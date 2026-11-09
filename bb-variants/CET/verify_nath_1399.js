// Step-by-step verification of Nath76's candidate:
// Agent 1: 1RA1RB_1LA0LB
// Agent 2: 1LA0RB_0LA1RB

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

const bb = "1RA1RB_1LA0LB|1LA0RB_0LA1RB";
const [ag1, ag2] = bb.split('|').map(parseAgent);
const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;
let cols = 0;
let lastCol = 0;

console.log("=== VERIFYING NATH76 1399 CANDIDATE ===");
console.log("bbchallenge:", bb);

const seen = new Map();

for (let step = 1; step <= 3000; step++) {
  const r1 = tape.get(p1) || 0;
  const r2 = tape.get(p2) || 0;

  const t1 = ag1[s1][r1];
  const t2 = ag2[s2][r2];

  tape.set(p2, t2.w);
  tape.set(p1, t1.w);

  p1 += t1.mv; s1 = t1.ns;
  p2 += t2.mv; s2 = t2.ns;

  const isCol = (p1 === p2);
  if (isCol) {
    cols++;
    lastCol = step;
  }

  // Tape signature around heads
  if (lastCol > 0 && step > lastCol) {
    let minX = Infinity, maxX = -Infinity;
    for (const [k, v] of tape.entries()) {
      if (v !== 0) {
        if (k < minX) minX = k;
        if (k > maxX) maxX = k;
      }
    }
    const arr = [];
    for (let x = minX; x <= maxX; x++) arr.push(tape.get(x) || 0);
    const tapeStr = `${minX - p1}:${arr.join('')}`;
    const key = `${p2 - p1}_${s1}_${s2}_${tapeStr}`;

    if (seen.has(key)) {
      const past = seen.get(key);
      const dp1 = p1 - past.p1;
      const dp2 = p2 - past.p2;
      const period = step - past.step;
      if (dp1 === dp2 && past.cols === cols) {
        console.log(`\n🎉 100% PROVEN QUASI-HALT!`);
        console.log(`Last Collision Step: ${lastCol} (Total Collisions: ${cols})`);
        console.log(`Cycle closed at step ${step} with Period: ${period}, Drift: ${dp1} cells/cycle`);
        process.exit(0);
      }
    }
    seen.set(key, { step, p1, p2, cols });
  }

  if (isCol && (step <= 10 || step % 100 === 0 || step >= 1390)) {
    console.log(`Step ${step.toString().padStart(4)}: p1=${p1.toString().padStart(4)}, p2=${p2.toString().padStart(4)} | Collision #${cols}`);
  }
}

console.log(`\nEnd of simulation (3000 steps). Last collision observed: ${lastCol}, total collisions: ${cols}`);
