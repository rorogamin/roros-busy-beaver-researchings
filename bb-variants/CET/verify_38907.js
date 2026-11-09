// Let's independently simulate Agent 1: 0RA_0RB_1LA_0LA, Agent 2: 1RB_0RA_1LA_0RA
function parseAgent(str) {
  const parts = str.split('_');
  const tr = [];
  for (let s = 0; s < 2; s++) {
    tr[s] = [];
    for (let r = 0; r < 2; r++) {
      const tok = parts[s * 2 + r];
      tr[s][r] = {
        w: parseInt(tok[0]),
        mv: tok[1] === 'R' ? 1 : -1,
        ns: tok[2] === 'B' ? 1 : 0
      };
    }
  }
  return tr;
}

const ag1 = parseAgent('0RA_0RB_1LA_0LA');
const ag2 = parseAgent('1RB_0RA_1LA_0RA');

const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;

let lastCol = 0;
let cols = 0;

for (let step = 1; step <= 40000; step++) {
  const r1 = tape.get(p1) || 0;
  const r2 = tape.get(p2) || 0;

  const t1 = ag1[s1][r1];
  const t2 = ag2[s2][r2];

  tape.set(p2, t2.w);
  tape.set(p1, t1.w);

  p1 += t1.mv; s1 = t1.ns;
  p2 += t2.mv; s2 = t2.ns;

  if (p1 === p2) {
    cols++;
    lastCol = step;
  }
}

console.log('Simulated 40000 steps.');
console.log('Total collisions:', cols);
console.log('Last collision step:', lastCol);
console.log('Positions at step 40000:', p1, p2);

// Check if they collide between 40000 and 60000
for (let step = 40001; step <= 60000; step++) {
  const r1 = tape.get(p1) || 0;
  const r2 = tape.get(p2) || 0;

  const t1 = ag1[s1][r1];
  const t2 = ag2[s2][r2];

  tape.set(p2, t2.w);
  tape.set(p1, t1.w);

  p1 += t1.mv; s1 = t1.ns;
  p2 += t2.mv; s2 = t2.ns;

  if (p1 === p2) {
    cols++;
    lastCol = step;
    console.log('Another collision at step:', step);
  }
}
console.log('After 60000 steps: Total collisions:', cols, 'Last collision step:', lastCol);
