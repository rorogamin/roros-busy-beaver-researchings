function parseAgent(str) {
  const states = str.split('_');
  const tr = {};
  states.forEach((stStr, sIdx) => {
    tr[sIdx] = {};
    for (let r = 0; r < 2; r++) {
      const chunk = stStr.substring(r * 3, r * 3 + 3);
      tr[sIdx][r] = {
        write: parseInt(chunk[0]),
        move: chunk[1] === 'R' ? 1 : -1,
        nextState: chunk[2].charCodeAt(0) - 65
      };
    }
  });
  return tr;
}

const bb = '1RB0LA_1LB0RA|1LA1LB_0RB0RA';
const [ag1, ag2] = bb.split('|').map(parseAgent);
const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;
let lastCol = 0, cols = 0;

for (let step = 1; step <= 3000; step++) {
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
console.log('Candidate:', bb);
console.log('Total Collisions:', cols, 'Last Collision Step:', lastCol);
console.log('Positions at step 3000: p1 =', p1, 'p2 =', p2);
