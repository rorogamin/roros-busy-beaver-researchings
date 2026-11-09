const fs = require('fs');
const src = fs.readFileSync('c:/Users/Rowan/Documents/catch em/colab_triple_expedition.c', 'utf8');
fs.writeFileSync('\\\\wsl$\\Ubuntu\\tmp\\colab_triple_expedition.c', src);
console.log('Successfully written colab_triple_expedition.c into WSL /tmp!');
