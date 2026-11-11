// QR Attendance - the app and the attendance file live only on this computer.
// Students reach it either over the classroom Wi-Fi ("local" mode)
// or over the internet through a Cloudflare tunnel ("online" mode).
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const { execFile, exec, spawn } = require('child_process');
const QRCode = require('qrcode');

let PORT = Number(process.env.PORT) || 5080;
const FIRST_PORT = PORT;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const DB_FILE = path.join(DATA_DIR, 'attendance.json');
const PUBLIC = path.join(__dirname, 'public');
const CLOUDFLARED = path.join(__dirname, 'bin', 'cloudflared.exe');
const TUNNEL_CONFIG = path.join(__dirname, 'bin', 'tunnel-config.yml');

const ROTATE_MS = 15 * 1000;              // online mode: the QR code changes this often
const TICKET_LOCAL_MS = 15 * 60 * 1000;   // time to type the name after scanning (local mode)
const TICKET_ONLINE_MS = 3 * 60 * 1000;   // same, online mode
const FAR_METRES = 300;                   // online mode: further than this from the class is flagged
const MAX_ACCURACY = 1500;                // a location less precise than this cannot be checked
// Online mode: requests per minute from one address. A whole class on one mobile carrier can
// share an address, so this must stay well above 80 students x 3 requests.
const RATE_LIMIT = 400;

// ---------- storage ----------
let db = {
  secret: crypto.randomBytes(32).toString('hex'),
  subjects: [],   // {id, name}
  sessions: [],   // {id, subjectId, subjectName, mode, startedAt, endedAt}
  records: [],    // {id, sessionId, name, time, via, ip, mac, did, fp, loc, source}
  blocked: [],    // {sessionId, time, name, reason, ownerName}
  settings: { mode: 'local', lanIp: '', wifiSsid: '', wifiPass: '', deviceLock: true },
};

function loadDb() {
  fs.mkdirSync(DATA_DIR, { recursive: true });
  if (fs.existsSync(DB_FILE)) {
    const saved = JSON.parse(fs.readFileSync(DB_FILE, 'utf8'));
    db = { ...db, ...saved, settings: { ...db.settings, ...(saved.settings || {}) } };
  }
  saveDb();
}

function saveDb() {
  const tmp = DB_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, DB_FILE);
}

// Wi-Fi mode: students can register only while the QR window is open on screen.
// That window reports in every 2 seconds; when it is closed, registration pauses.
// Two things must both be true: the teacher opened the QR from the dashboard (qrOpen),
// and the QR window is really still on screen (it reported in during the last 8 seconds).
let qrOpen = false;
let displaySeen = 0;
const displayOpen = () => qrOpen && Date.now() - displaySeen < 8000;
const registrationOpen = (session) => isOnline(session) || displayOpen();
const closeQr = () => { qrOpen = false; displaySeen = 0; };

const newId = () => crypto.randomBytes(6).toString('hex');
const activeSession = () => db.sessions.find((s) => !s.endedAt) || null;
const isOnline = (session) => !!session && session.mode === 'online';

// ---------- network ----------
function lanInterfaces() {
  const out = [];
  for (const [name, addrs] of Object.entries(os.networkInterfaces())) {
    for (const a of addrs || []) {
      if (a.family === 'IPv4' && !a.internal && !a.address.startsWith('169.254.')) {
        out.push({ name, address: a.address, cidr: a.cidr });
      }
    }
  }
  return out;
}

function currentLanIp() {
  const list = lanInterfaces();
  if (list.some((i) => i.address === db.settings.lanIp)) return db.settings.lanIp;
  // 192.168.137.1 is the address Windows gives this PC when Mobile Hotspot is on
  const hotspot = list.find((i) => i.address === '192.168.137.1');
  return (hotspot || list[0] || { address: 'localhost' }).address;
}

// Name of the Wi-Fi this computer is on, so the dashboard can say which one students must join.
let wifiName = '';
function refreshWifiName() {
  execFile('netsh', ['wlan', 'show', 'interfaces'], { timeout: 3000, windowsHide: true }, (err, out) => {
    const m = !err && String(out).match(/^\s*SSID\s*:\s*(.+)$/m);
    wifiName = m ? m[1].trim() : '';
  });
}
refreshWifiName();
setInterval(refreshWifiName, 15000).unref();

// Plain-language note about the network in Wi-Fi mode. The QR link is a private address:
// it opens only on phones joined to the same network as this computer.
function networkAdvice() {
  const ip = currentLanIp();
  if (ip === 'localhost') {
    return { warn: true, text: 'This computer is not connected to any network, so phones cannot reach it. Connect to a Wi-Fi, or switch "How students connect" to Internet.' };
  }
  const iface = lanInterfaces().find((i) => i.address === ip);
  const prefix = iface && iface.cidr ? Number(iface.cidr.split('/')[1]) : 24;
  const room = Math.max(0, 2 ** (32 - prefix) - 4); // phones the network has addresses for
  const named = wifiName ? ` "${wifiName}"` : '';
  if (ip.startsWith('172.20.10.')) {
    return { warn: true, text: `This computer is on an iPhone hotspot${named}. The QR link opens only on phones joined to that hotspot, and it accepts just a few devices. Phones on mobile data cannot open it. For a class, switch "How students connect" to Internet.` };
  }
  if (ip === '192.168.137.1') {
    return { warn: true, text: 'This computer is sharing its own Windows hotspot, which accepts 8 devices at most. The QR link opens only on phones joined to it.' };
  }
  if (room < 60) {
    return { warn: true, text: `The network${named} has room for only about ${room} phones. The QR link opens only on phones joined to it.` };
  }
  return { warn: false, text: `Students must first join the Wi-Fi${named || ' this computer is on'}. Phones on mobile data or another Wi-Fi cannot open the QR link.` };
}

const cleanIp = (req) => (req.socket.remoteAddress || '').replace(/^::ffff:/, '');

// The teacher pages only work from this computer itself, opened by its own address.
function isTeacher(req) {
  const own = ['127.0.0.1', '::1', ...lanInterfaces().map((i) => i.address)];
  if (!own.includes(cleanIp(req))) return false;
  const host = String(req.headers.host || '').replace(/:\d+$/, '').replace(/^\[|\]$/g, '');
  if (host !== 'localhost' && !own.includes(host)) return false;
  // refuse requests that another website, open in the teacher's browser, tries to send here
  const origin = req.headers.origin;
  if (origin && origin !== `http://${req.headers.host}`) return false;
  if (req.headers['sec-fetch-site'] === 'cross-site') return false;
  return true;
}

// Hardware (MAC) address of a phone on the local network, from Windows' ARP table.
function macFor(ip) {
  return new Promise((resolve) => {
    if (!/^\d+\.\d+\.\d+\.\d+$/.test(ip) || ip.startsWith('127.')) return resolve(null);
    execFile('arp', ['-a', ip], { timeout: 2000, windowsHide: true }, (err, out) => {
      if (err) return resolve(null);
      const m = String(out).match(/([0-9a-f]{2}[-:]){5}[0-9a-f]{2}/i);
      resolve(m ? m[0].toLowerCase().replace(/:/g, '-') : null);
    });
  });
}

// ---------- internet tunnel (online mode) ----------
// Students never reach the main server through the internet. The tunnel points at a
// second, student-only server that has no teacher pages at all.
let publicPort = 0;
let tunnelProc = null;
let tunnel = { status: 'off', url: '', error: '' };

function startTunnel() {
  if (tunnelProc) return;
  if (!fs.existsSync(CLOUDFLARED)) {
    tunnel = { status: 'error', url: '', error: 'bin\\cloudflared.exe is missing.' };
    return;
  }
  tunnel = { status: 'starting', url: '', error: '' };
  const proc = spawn(
    CLOUDFLARED,
    // the empty config keeps this separate from any other Cloudflare tunnel set up on this computer
    ['tunnel', '--config', TUNNEL_CONFIG, '--no-autoupdate', '--url', `http://127.0.0.1:${publicPort}`],
    { windowsHide: true, stdio: ['ignore', 'pipe', 'pipe'] }
  );
  tunnelProc = proc;
  let log = '';
  const onData = (chunk) => {
    if (tunnel.url || tunnelProc !== proc) return;
    log += chunk;
    const m = log.match(/https:\/\/[a-z0-9]+(?:-[a-z0-9]+)+\.trycloudflare\.com/);
    if (m) {
      tunnel.url = m[0];
      waitUntilReachable(proc, m[0]);
    }
  };
  proc.stdout.on('data', onData);
  proc.stderr.on('data', onData);
  proc.on('error', () => {});
  proc.on('exit', () => {
    if (tunnelProc !== proc) return; // stopped on purpose
    tunnelProc = null;
    tunnel = { status: 'error', url: '', error: 'No internet connection. Trying again…' };
    setTimeout(() => { if (isOnline(activeSession())) startTunnel(); }, 5000);
  });
}

// The public address needs a few seconds before phones can open it.
async function waitUntilReachable(proc, url) {
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  await sleep(4000);
  for (let i = 0; i < 8 && tunnelProc === proc; i++) {
    try {
      const res = await fetch(url + '/api/ping', { signal: AbortSignal.timeout(4000) });
      if (res.ok) break;
    } catch { /* not ready yet */ }
    await sleep(2000);
  }
  if (tunnelProc === proc) tunnel.status = 'on';
}

function stopTunnel() {
  const proc = tunnelProc;
  tunnelProc = null;
  tunnel = { status: 'off', url: '', error: '' };
  if (proc) proc.kill();
}

function syncTunnel() {
  if (isOnline(activeSession())) startTunnel();
  else stopTunnel();
}

const hits = new Map(); // address -> {count, resetAt}
function rateLimited(ip) {
  const now = Date.now();
  if (hits.size > 5000) hits.clear();
  const h = hits.get(ip);
  if (!h || now > h.resetAt) {
    hits.set(ip, { count: 1, resetAt: now + 60000 });
    return false;
  }
  return ++h.count > RATE_LIMIT;
}

// ---------- QR token + form ticket ----------
const sign = (text) =>
  crypto.createHmac('sha256', db.secret).update(text).digest('base64url');

// Local mode: one code per session. Online mode: the code changes every 15 seconds,
// because nothing else proves the student can see the screen.
function tokenFor(session, step = 0) {
  if (!isOnline(session)) return sign(`qr:${session.id}`).slice(0, 10);
  return sign(`qr:${session.id}:${Math.floor(Date.now() / ROTATE_MS) - step}`).slice(0, 10);
}

const tokenValid = (session, token) =>
  token === tokenFor(session) || (isOnline(session) && token === tokenFor(session, 1));

// The ticket is tied to the phone that scanned, so a forwarded page is useless elsewhere.
function makeTicket(session, did) {
  const exp = Date.now() + (isOnline(session) ? TICKET_ONLINE_MS : TICKET_LOCAL_MS);
  return `${session.id}.${exp}.${sign(`ticket:${session.id}:${exp}:${did}`).slice(0, 22)}`;
}

function ticketSession(ticket, did) {
  const [sessionId, exp, sig] = String(ticket || '').split('.');
  if (!sessionId || !exp || !sig) return null;
  if (sig !== sign(`ticket:${sessionId}:${exp}:${did}`).slice(0, 22)) return null;
  if (Date.now() > Number(exp)) return null;
  return sessionId;
}

// ---------- names ----------
const tidyName = (name) => String(name || '').normalize('NFKC').replace(/\s+/g, ' ').trim();

// Used to spot the same name typed slightly differently (also for Arabic spelling variants).
function nameKey(name) {
  return tidyName(name)
    .toLowerCase()
    .replace(/[ً-ٰٟـ]/g, '') // Arabic diacritics and tatweel
    .replace(/[أإآٱ]/g, 'ا')
    .replace(/ى/g, 'ي')
    .replace(/ة/g, 'ه')
    .replace(/[^\p{L} ]/gu, '');
}

function nameProblem(name) {
  if (name.length > 80) return 'The name is too long.';
  if (!/^[\p{L}\p{M}'’.\- ]+$/u.test(name)) return 'Please use letters only.';
  if (name.split(' ').filter((w) => w.length > 1).length < 2) {
    return 'Please enter your full name (first name and family name).';
  }
  return null;
}

// ---------- http helpers ----------
const SAFE_HEADERS = {
  'Cache-Control': 'no-store',
  'X-Content-Type-Options': 'nosniff',
  'X-Frame-Options': 'DENY',
  'Referrer-Policy': 'no-referrer',
};

function sendJson(res, code, obj, headers = {}) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', ...SAFE_HEADERS, ...headers });
  res.end(JSON.stringify(obj));
}

function sendPage(res, file) {
  fs.readFile(path.join(PUBLIC, file), (err, buf) => {
    if (err) {
      res.writeHead(500);
      return res.end('Missing page');
    }
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', ...SAFE_HEADERS });
    res.end(buf);
  });
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let data = '';
    req.on('data', (chunk) => {
      data += chunk;
      if (data.length > 10000) {
        reject(new Error('too large'));
        req.destroy();
      }
    });
    req.on('end', () => {
      try {
        resolve(data ? JSON.parse(data) : {});
      } catch (e) {
        reject(e);
      }
    });
    req.on('error', reject);
  });
}

function cookie(req, name) {
  const m = (req.headers.cookie || '').match(new RegExp(`(?:^|; )${name}=([^;]+)`));
  return m ? m[1] : null;
}

// ---------- student side ----------
// Which earlier record, if any, came from this same phone.
// On the classroom Wi-Fi the network and hardware addresses identify a phone as well as the
// cookie does. Over the internet many phones share one address, so only the cookie can block.
function deviceOwner(sessionId, did, lan) {
  if (!db.settings.deviceLock) return null;
  return (
    db.records.find(
      (r) =>
        r.sessionId === sessionId &&
        r.source === 'scan' &&
        ((did && r.did === did) ||
          (lan && r.via === 'lan' && ((lan.ip && r.ip === lan.ip) || (lan.mac && r.mac === lan.mac))))
    ) || null
  );
}

function noteBlocked(sessionId, name, reason, ownerName) {
  db.blocked.push({ sessionId, time: new Date().toISOString(), name, reason, ownerName });
  saveDb();
}

function handleTicket(req, res, url, viaTunnel) {
  const session = activeSession();
  if (!session) return sendJson(res, 403, { error: 'closed' });
  if (!registrationOpen(session)) return sendJson(res, 403, { error: 'paused' });
  if (!tokenValid(session, url.searchParams.get('t') || '')) {
    return sendJson(res, 403, { error: 'expired' });
  }
  let did = cookie(req, 'did');
  const headers = {};
  if (!did || !/^[0-9a-f]{32}$/.test(did)) {
    did = crypto.randomBytes(16).toString('hex');
    headers['Set-Cookie'] =
      `did=${did}; Path=/; Max-Age=31536000; HttpOnly; SameSite=Lax${viaTunnel ? '; Secure' : ''}`;
  }
  const owner = deviceOwner(session.id, did, viaTunnel ? null : { ip: cleanIp(req) });
  if (owner) {
    return sendJson(res, 200, { already: true, name: owner.name, subject: session.subjectName }, headers);
  }
  sendJson(res, 200, {
    ticket: makeTicket(session, did),
    subject: session.subjectName,
    askLocation: viaTunnel,
  }, headers);
}

function cleanLocation(loc) {
  if (!loc || typeof loc !== 'object') return null;
  const { lat, lon, acc } = loc;
  if (![lat, lon, acc].every(Number.isFinite)) return null;
  if (Math.abs(lat) > 90 || Math.abs(lon) > 180 || acc < 0) return null;
  return { lat, lon, acc: Math.round(acc) };
}

async function handleAttend(req, res, viaTunnel, clientIp) {
  const body = await readBody(req);
  const session = activeSession();
  if (!session) return sendJson(res, 403, { error: 'closed' });
  if (!registrationOpen(session)) return sendJson(res, 403, { error: 'paused' });
  const did = cookie(req, 'did');
  if (!did || ticketSession(body.ticket, did) !== session.id) {
    return sendJson(res, 403, { error: 'expired' });
  }

  const name = tidyName(body.name);
  const problem = nameProblem(name);
  if (problem) return sendJson(res, 400, { error: 'name', message: problem });

  const mac = viaTunnel ? null : await macFor(clientIp);

  // everything below runs without interruption, so two requests cannot slip past each other
  const owner = deviceOwner(session.id, did, viaTunnel ? null : { ip: clientIp, mac });
  if (owner) {
    if (nameKey(owner.name) !== nameKey(name)) noteBlocked(session.id, name, 'device', owner.name);
    return sendJson(res, 409, { error: 'device', name: owner.name });
  }
  const key = nameKey(name);
  if (db.records.some((r) => r.sessionId === session.id && nameKey(r.name) === key)) {
    noteBlocked(session.id, name, 'duplicate', null);
    return sendJson(res, 409, { error: 'duplicate' });
  }

  const record = {
    id: newId(), sessionId: session.id, name,
    time: new Date().toISOString(),
    via: viaTunnel ? 'tunnel' : 'lan',
    ip: clientIp, mac, did, source: 'scan',
  };
  if (viaTunnel) {
    // a description of the phone (model, screen, language): used only to warn the teacher
    const about = `${req.headers['user-agent'] || ''}|${String(body.fp || '').slice(0, 300)}`;
    record.fp = crypto.createHash('sha256').update(about).digest('hex').slice(0, 16);
    record.loc = cleanLocation(body.loc);
  }
  db.records.push(record);
  saveDb();
  sendJson(res, 200, { ok: true, name, subject: session.subjectName, time: record.time });
}

// ---------- warnings for the teacher (online mode) ----------
function median(values) {
  const v = [...values].sort((a, b) => a - b);
  const mid = Math.floor(v.length / 2);
  return v.length % 2 ? v[mid] : (v[mid - 1] + v[mid]) / 2;
}

function metresBetween(a, b) {
  const rad = (d) => (d * Math.PI) / 180;
  const dLat = rad(b.lat - a.lat);
  const dLon = rad(b.lon - a.lon);
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(rad(a.lat)) * Math.cos(rad(b.lat)) * Math.sin(dLon / 2) ** 2;
  return 6371000 * 2 * Math.asin(Math.sqrt(h));
}

// The classroom is taken to be where most students are: the middle point of everyone's location.
function warningsFor(sessionId) {
  const recs = db.records.filter((r) => r.sessionId === sessionId);
  const located = recs.filter((r) => r.loc && r.loc.acc <= MAX_ACCURACY);
  const centre = located.length >= 5
    ? { lat: median(located.map((r) => r.loc.lat)), lon: median(located.map((r) => r.loc.lon)) }
    : null;
  const out = new Map();
  for (const r of recs) {
    const list = [];
    if (r.via === 'tunnel') {
      const twin = recs.find((o) => o !== r && o.via === 'tunnel' && o.fp && o.fp === r.fp && o.ip === r.ip);
      if (twin) list.push(`Possibly the same phone as "${twin.name}"`);
      if (!r.loc) list.push('Location not shared');
      else if (r.loc.acc > MAX_ACCURACY) list.push('Location too imprecise to check');
      else if (centre) {
        const d = metresBetween(r.loc, centre);
        if (d > FAR_METRES + r.loc.acc) {
          list.push(`About ${d < 1000 ? Math.round(d / 10) * 10 + ' m' : (d / 1000).toFixed(1) + ' km'} from the class`);
        }
      }
    }
    out.set(r.id, list);
  }
  return out;
}

function recordsFor(sessionId) {
  const warnings = warningsFor(sessionId);
  return db.records
    .filter((r) => r.sessionId === sessionId)
    .map((r) => ({ id: r.id, name: r.name, time: r.time, source: r.source, warnings: warnings.get(r.id) }));
}

// ---------- teacher side ----------
const qrSvg = (text) => QRCode.toString(text, { type: 'svg', margin: 2, errorCorrectionLevel: 'M' });

const wifiEscape = (s) => String(s).replace(/([\\;,:"])/g, '\\$1');

function stateFor() {
  const session = activeSession();
  return {
    subjects: db.subjects,
    active: session,
    records: session ? recordsFor(session.id) : [],
    blocked: session ? db.blocked.filter((b) => b.sessionId === session.id) : [],
    settings: db.settings,
    interfaces: lanInterfaces(),
    lanIp: currentLanIp(),
    port: PORT,
    networkAdvice: networkAdvice(),
    paused: !!session && !registrationOpen(session),
    tunnel,
    onlineAvailable: fs.existsSync(CLOUDFLARED),
  };
}

async function handleQr(res, url) {
  if (url.searchParams.get('display') && qrOpen) displaySeen = Date.now(); // the QR window reporting in
  const session = activeSession();
  if (!session) return sendJson(res, 200, { active: false });
  const out = {
    active: true,
    mode: session.mode || 'local',
    subject: session.subjectName,
    count: db.records.filter((r) => r.sessionId === session.id).length,
  };
  if (isOnline(session)) {
    if (tunnel.status !== 'on') {
      out.waiting = tunnel.status === 'error' ? tunnel.error : 'Connecting to the internet…';
      return sendJson(res, 200, out);
    }
    out.svg = await qrSvg(`${tunnel.url}/a?t=${tokenFor(session)}`);
    return sendJson(res, 200, out);
  }
  if (!displayOpen()) {
    out.paused = true; // no code is shown anywhere while the QR window is closed
    return sendJson(res, 200, out);
  }
  out.svg = await qrSvg(`http://${currentLanIp()}:${PORT}/a?t=${tokenFor(session)}`);
  const { wifiSsid, wifiPass } = db.settings;
  if (wifiSsid) {
    const wifi = wifiPass
      ? `WIFI:T:WPA;S:${wifiEscape(wifiSsid)};P:${wifiEscape(wifiPass)};;`
      : `WIFI:T:nopass;S:${wifiEscape(wifiSsid)};;`;
    out.wifiSvg = await qrSvg(wifi);
    out.wifiSsid = wifiSsid;
  }
  sendJson(res, 200, out);
}

const pad = (n) => String(n).padStart(2, '0');
const localDate = (d) => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
const localTime = (d) => `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;

function handleExport(res, url) {
  const sessionId = url.searchParams.get('session');
  const subjectId = url.searchParams.get('subject');
  let sessions = db.sessions;
  let label = 'all';
  if (sessionId) {
    sessions = sessions.filter((s) => s.id === sessionId);
    if (sessions[0]) label = `${sessions[0].subjectName}-${localDate(new Date(sessions[0].startedAt))}`;
  } else if (subjectId) {
    sessions = sessions.filter((s) => s.subjectId === subjectId);
    if (sessions[0]) label = sessions[0].subjectName;
  }
  const cell = (v) => `"${String(v).replace(/"/g, '""')}"`;
  const rows = [['Subject', 'Date', 'Time', 'Full name', 'Entered by', 'Warnings'].map(cell).join(',')];
  for (const s of sessions) {
    const warnings = warningsFor(s.id);
    for (const r of db.records.filter((x) => x.sessionId === s.id)) {
      const d = new Date(r.time);
      rows.push(
        [
          s.subjectName, localDate(d), localTime(d), r.name,
          r.source === 'scan' ? 'Student (QR)' : 'Teacher',
          (warnings.get(r.id) || []).join('; '),
        ].map(cell).join(',')
      );
    }
  }
  const filename = `attendance-${label}.csv`.replace(/[\\/:*?"<>|]/g, '_');
  res.writeHead(200, {
    'Content-Type': 'text/csv; charset=utf-8',
    'Content-Disposition': `attachment; filename="attendance.csv"; filename*=UTF-8''${encodeURIComponent(filename)}`,
    'Cache-Control': 'no-store',
  });
  res.end('﻿' + rows.join('\r\n') + '\r\n'); // BOM so Excel shows Arabic correctly
}

async function handleTeacherApi(req, res, url) {
  const p = url.pathname;
  const m = req.method;

  if (p === '/api/state' && m === 'GET') return sendJson(res, 200, stateFor());
  if (p === '/api/qr' && m === 'GET') return handleQr(res, url);
  if (p === '/api/display/open' && m === 'POST') {
    qrOpen = true;
    displaySeen = Date.now(); // a few seconds for the QR window to appear and report in
    return sendJson(res, 200, { ok: true });
  }
  if (p === '/api/display/closed' && m === 'POST') {
    closeQr(); // the QR was closed: pause at once
    return sendJson(res, 200, { ok: true });
  }
  if (p === '/api/shutdown' && m === 'POST') {
    // a newer copy of the app is starting and takes over
    sendJson(res, 200, { ok: true });
    return setTimeout(shutDown, 100);
  }
  if (p === '/api/export' && m === 'GET') return handleExport(res, url);

  if (p === '/api/subjects' && m === 'POST') {
    const name = tidyName((await readBody(req)).name).slice(0, 80);
    if (!name) return sendJson(res, 400, { message: 'Enter a subject name.' });
    if (db.subjects.some((s) => s.name.toLowerCase() === name.toLowerCase())) {
      return sendJson(res, 409, { message: 'That subject already exists.' });
    }
    db.subjects.push({ id: newId(), name });
    saveDb();
    return sendJson(res, 200, { ok: true });
  }

  let match = p.match(/^\/api\/subjects\/(\w+)$/);
  if (match && m === 'DELETE') {
    // past attendance for the subject is kept in the history
    db.subjects = db.subjects.filter((s) => s.id !== match[1]);
    saveDb();
    return sendJson(res, 200, { ok: true });
  }

  if (p === '/api/session/start' && m === 'POST') {
    const { subjectId } = await readBody(req);
    const subject = db.subjects.find((s) => s.id === subjectId);
    if (!subject) return sendJson(res, 400, { message: 'Choose a subject first.' });
    const mode = db.settings.mode === 'online' ? 'online' : 'local';
    if (mode === 'online' && !fs.existsSync(CLOUDFLARED)) {
      return sendJson(res, 400, { message: 'Internet mode needs bin\\cloudflared.exe, which is missing.' });
    }
    const now = new Date().toISOString();
    for (const s of db.sessions) if (!s.endedAt) s.endedAt = now;
    db.sessions.push({
      id: newId(), subjectId: subject.id, subjectName: subject.name, mode, startedAt: now, endedAt: null,
    });
    closeQr();
    saveDb();
    syncTunnel();
    return sendJson(res, 200, { ok: true });
  }

  if (p === '/api/session/end' && m === 'POST') {
    const session = activeSession();
    if (session) session.endedAt = new Date().toISOString();
    closeQr();
    saveDb();
    syncTunnel();
    return sendJson(res, 200, { ok: true });
  }

  if (p === '/api/sessions' && m === 'GET') {
    const list = db.sessions
      .map((s) => ({ ...s, count: db.records.filter((r) => r.sessionId === s.id).length }))
      .reverse();
    return sendJson(res, 200, { sessions: list });
  }

  match = p.match(/^\/api\/sessions\/(\w+)$/);
  if (match && m === 'GET') {
    const session = db.sessions.find((s) => s.id === match[1]);
    if (!session) return sendJson(res, 404, { message: 'Not found.' });
    return sendJson(res, 200, { session, records: recordsFor(session.id) });
  }
  if (match && m === 'DELETE') {
    db.sessions = db.sessions.filter((s) => s.id !== match[1]);
    db.records = db.records.filter((r) => r.sessionId !== match[1]);
    db.blocked = db.blocked.filter((b) => b.sessionId !== match[1]);
    saveDb();
    syncTunnel();
    return sendJson(res, 200, { ok: true });
  }

  if (p === '/api/records' && m === 'POST') {
    // teacher adds a student by hand (for example a student without a phone)
    const session = activeSession();
    if (!session) return sendJson(res, 400, { message: 'Start a session first.' });
    const name = tidyName((await readBody(req)).name).slice(0, 80);
    if (!name) return sendJson(res, 400, { message: 'Enter a name.' });
    if (db.records.some((r) => r.sessionId === session.id && nameKey(r.name) === nameKey(name))) {
      return sendJson(res, 409, { message: 'That name is already on the list.' });
    }
    db.records.push({
      id: newId(), sessionId: session.id, name,
      time: new Date().toISOString(), ip: null, mac: null, did: null, source: 'manual',
    });
    saveDb();
    return sendJson(res, 200, { ok: true });
  }

  match = p.match(/^\/api\/records\/(\w+)$/);
  if (match && m === 'DELETE') {
    db.records = db.records.filter((r) => r.id !== match[1]);
    saveDb();
    return sendJson(res, 200, { ok: true });
  }

  if (p === '/api/settings' && m === 'POST') {
    const body = await readBody(req);
    if (body.mode === 'local' || body.mode === 'online') db.settings.mode = body.mode;
    if (typeof body.lanIp === 'string') db.settings.lanIp = body.lanIp;
    if (typeof body.wifiSsid === 'string') db.settings.wifiSsid = body.wifiSsid.trim().slice(0, 64);
    if (typeof body.wifiPass === 'string') db.settings.wifiPass = body.wifiPass.slice(0, 64);
    if (typeof body.deviceLock === 'boolean') db.settings.deviceLock = body.deviceLock;
    saveDb();
    return sendJson(res, 200, { ok: true });
  }

  sendJson(res, 404, { message: 'Not found.' });
}

// ---------- routers ----------
// Returns true when the request was one of the three things a student may do.
async function studentRoute(req, res, url, viaTunnel, clientIp) {
  const p = url.pathname;
  if (p === '/a' && req.method === 'GET') return sendPage(res, 'attend.html'), true;
  if (p === '/api/ping' && req.method === 'GET') return sendJson(res, 200, { ok: true, app: 'qr-attendance' }), true;
  if (p === '/api/open' && req.method === 'GET') {
    // the name form asks this every few seconds, and hides itself when registration stops
    const session = activeSession();
    const state = !session ? 'closed' : registrationOpen(session) ? 'open' : 'paused';
    return sendJson(res, 200, { state }), true;
  }
  if (p === '/api/ticket' && req.method === 'GET') return handleTicket(req, res, url, viaTunnel), true;
  if (p === '/api/attend' && req.method === 'POST') return await handleAttend(req, res, viaTunnel, clientIp), true;
  return false;
}

const fail = (res, err) => {
  console.error(err);
  if (!res.headersSent) sendJson(res, 500, { message: 'Something went wrong.' });
};

// Main server: this computer (teacher) and the classroom Wi-Fi (students).
const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url, 'http://localhost');
    const p = url.pathname;
    if (await studentRoute(req, res, url, false, cleanIp(req))) return;

    if (!isTeacher(req)) {
      res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('Please scan the QR code shown in class.');
    }
    if (p === '/' && req.method === 'GET') return sendPage(res, 'admin.html');
    if (p === '/display' && req.method === 'GET') return sendPage(res, 'display.html');
    if (p.startsWith('/api/')) return await handleTeacherApi(req, res, url);

    res.writeHead(404, { 'Content-Type': 'text/plain' });
    res.end('Not found');
  } catch (err) {
    fail(res, err);
  }
});

// Internet server: reachable only through the tunnel, and only for the student check-in.
const publicServer = http.createServer(async (req, res) => {
  try {
    const clientIp = String(req.headers['cf-connecting-ip'] || 'unknown').slice(0, 60);
    if (!isOnline(activeSession())) {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      return res.end('Not found');
    }
    if (rateLimited(clientIp)) {
      res.writeHead(429, { 'Content-Type': 'text/plain' });
      return res.end('Too many requests. Wait a minute and try again.');
    }
    const url = new URL(req.url, 'http://localhost');
    if (await studentRoute(req, res, url, true, clientIp)) return;
    res.writeHead(404, { 'Content-Type': 'text/plain' });
    res.end('Not found');
  } catch (err) {
    fail(res, err);
  }
});

// ---------- start ----------

server.on('error', (err) => {
  // if another program already uses the port, try the next few
  if (err.code === 'EADDRINUSE' && PORT < FIRST_PORT + 10) {
    PORT += 1;
    return server.listen(PORT, '0.0.0.0');
  }
  console.error(err.message);
  process.exit(1);
});

server.on('listening', () => {
  console.log('');
  console.log('  QR Attendance is running.');
  console.log(`  Teacher dashboard (this computer only):  http://localhost:${PORT}`);
  console.log(`  Students on the classroom Wi-Fi use:     http://${currentLanIp()}:${PORT}`);
  console.log(`  Attendance is saved in:                  ${DB_FILE}`);
  console.log('');
  console.log('  Keep this window open during class. Close it to stop.');
  syncTunnel();
  if (process.argv.includes('--open')) exec(`start "" http://localhost:${PORT}`);
});

// Two copies running at once would overwrite each other's attendance file.
// So a copy that is starting first asks any older copy to stop, and takes over.
async function stopOlderCopies() {
  let stopped = false;
  for (let port = FIRST_PORT; port <= FIRST_PORT + 10; port++) {
    try {
      const base = `http://127.0.0.1:${port}`;
      const ping = await (await fetch(base + '/api/ping', { signal: AbortSignal.timeout(700) })).json();
      if (ping.app !== 'qr-attendance') continue;
      await fetch(base + '/api/shutdown', { method: 'POST', signal: AbortSignal.timeout(700) });
      stopped = true;
    } catch { /* nothing of ours on this port */ }
  }
  if (stopped) await new Promise((r) => setTimeout(r, 1200));
}

// the student-only server listens on this computer alone; the tunnel program connects to it
stopOlderCopies().then(() => {
  loadDb();
  publicServer.listen(0, '127.0.0.1', () => {
    publicPort = publicServer.address().port;
    server.listen(PORT, '0.0.0.0');
  });
});

function shutDown() { stopTunnel(); process.exit(0); }
process.on('SIGINT', shutDown);
process.on('SIGTERM', shutDown);
process.on('SIGHUP', shutDown);
process.on('exit', () => { if (tunnelProc) tunnelProc.kill(); });
