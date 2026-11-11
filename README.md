# QR Attendance

Local QR code attendance for classrooms. The teacher runs a small Node.js server on their own computer, shows a rotating QR code, and students scan it to mark themselves present.

## Run

Requires [Node.js](https://nodejs.org).

```bash
npm install
```

```bash
npm start
```

On Windows you can just double-click `start.bat`.

## Internet mode (optional)

By default students must be on the same network as the teacher's computer. To let them attend over the internet, download `cloudflared.exe` from the [Cloudflare releases page](https://github.com/cloudflare/cloudflared/releases) and place it at `bin/cloudflared.exe`.

## Data

Attendance records are stored locally in `data/attendance.json`. That folder is git-ignored and is never uploaded.
