@echo off
title QR Attendance
cd /d "%~dp0"
if not exist node_modules (
  echo Installing, one time only...
  call npm install
)
node server.js --open
pause
