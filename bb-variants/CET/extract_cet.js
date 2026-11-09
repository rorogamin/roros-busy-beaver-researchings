// Extract lines from TNF.txt starting from line 2
const fs = require('fs');
const lines = fs.readFileSync('C:/Users/Rowan/Downloads/TNF.txt', 'utf8').split('\n');
// First line is %%writefile cet.cpp
const cleanCode = lines.slice(1).join('\n');
fs.writeFileSync('cet.cpp', cleanCode);
console.log('Saved cet.cpp, length:', cleanCode.length, 'lines:', cleanCode.split('\n').length);
