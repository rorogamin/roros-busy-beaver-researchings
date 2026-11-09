const fs = require('fs');
const code = "import subprocess\nprint(subprocess.check_output(['nvidia-smi']).decode())\n";
fs.writeFileSync('\\\\wsl$\\Ubuntu\\tmp\\check_gpu.py', code);
console.log('Written to WSL /tmp/check_gpu.py');
