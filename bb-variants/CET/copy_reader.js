const fs = require('fs');
const src = fs.readFileSync('c:/Users/Rowan/Documents/catch em/read_remote_log.py', 'utf8');
fs.writeFileSync('\\\\wsl$\\Ubuntu\\tmp\\read_remote_log.py', src);
