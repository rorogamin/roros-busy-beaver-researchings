// Verify 2880 step candidate:
// Agent 1: 1RA1LB_0RA0LA
// Agent 2: 1RB0RA_1LB0LA
function parseAgent(str) {
  const states = str.split('_');
  const tr = [];
  for (let s = 0; s < states.length; s++) {
    tr[s] = [];
    for (let r = 0; r < 2; r++) {
      const tok = states[s].substring(r * 3, r * 3 + 3);
      tr[s][r] = {
        w: parseInt(tok[0]),
        mv: tok[1] === 'R' ? 1 : -1,
        ns: tok[2].charCodeAt(0) - 65
      };
    }
  }
  return tr;
}

const bb = "1RA1LB_0RA0LA|1RB0RA_1LB0LA";
const [ag1, ag2] = bb.split('|').map(parseAgent);
const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;
let cols = 0;
let lastCol = 0;

for (let step = 1; step <= 3500; step++) {
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

console.log("Candidate:", bb);
console.log("Total collisions in 3500 steps:", cols);
console.log("Last collision step:", lastCol);
console.log("Positions at step 3500: p1 =", p1, "p2 =", p2);

// Check if they ever collide between 3500 and 10000
for (let step = 3501; step <= 10000; step++) {
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
    console.log("Collision at step:", step);
  }
}
console.log("Total collisions in 10000 steps:", cols, "Last collision:", lastCol);
