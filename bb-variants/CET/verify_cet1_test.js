// Verify Nath76's definition of CET_1(2) on the example:
// Agent 1: 0RB_1LB_1LA_1RB
// Agent 2: 0RB_1RB_0LB_0RA
// Collisions: 6, Last collision: 15, Steps: 20, Cycle: 4

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

const ag1 = parseAgent('0RB_1LB_1LA_1RB');
const ag2 = parseAgent('0RB_1RB_0LB_0RA');

const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;
let collisions = 0;
let lastColStep = 0;

for (let step = 1; step <= 30; step++) {
  const r1 = tape.get(p1) || 0;
  const r2 = tape.get(p2) || 0;

  const t1 = ag1[s1][r1];
  const t2 = ag2[s2][r2];

  // Write priority: agent 1 wins tie if on same cell before write
  tape.set(p2, t2.w);
  tape.set(p1, t1.w);

  p1 += t1.mv;
  s1 = t1.ns;
  p2 += t2.mv;
  s2 = t2.ns;

  const isCol = (p1 === p2);
  if (isCol) {
    collisions++;
    lastColStep = step;
  }
  console.log(`Step ${step}: p1=${p1} (s1=${s1}), p2=${p2} (s2=${s2}) | ${isCol ? 'COLLISION! (col #' + collisions + ')' : ''}`);
}
console.log('Total collisions in 30 steps:', collisions, 'Last collision step:', lastColStep);
