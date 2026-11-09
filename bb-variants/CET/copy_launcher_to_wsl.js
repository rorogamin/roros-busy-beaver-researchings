const fs = require('fs');
const src = fs.readFileSync('c:/Users/Rowan/Documents/catch em/remote_launcher.py', 'utf8');
fs.writeFileSync('\\\\wsl$\\Ubuntu\\tmp\\remote_launcher.py', src);
console.log('Successfully written remote_launcher.py into WSL /tmp!');
