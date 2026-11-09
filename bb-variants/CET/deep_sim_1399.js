// Deep simulation of Nath76's 1399 machine to verify the shift overflow counter behavior
function parseAgent(str) {
  const states = str.split('_');
  const tr = [];
  for (let s = 0; s < states.length; s++) {
    tr[s] = [];
    for (let r = 0; r < 2; r++) {
      const tok = states[s].substring(r * 3, r * 3 + 3);
      tr[s][r] = { w: parseInt(tok[0]), mv: tok[1] === 'R' ? 1 : -1, ns: tok[2].charCodeAt(0) - 65 };
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

console.log("=== SIMULATING NATH76 1399 MACHINE DEEP TO 2,000,000 STEPS ===");

for (let step = 1; step <= 2000000; step++) {
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
    console.log(`💥 COLLISION #${cols} at step ${step} on cell ${p1}!`);
  }

  // Periodic status check
  if (step === 10000 || step === 50000 || step === 100000 || step === 500000 || step === 1000000 || step === 2000000) {
    console.log(`Step ${step.toString().padStart(7)}: p1 = ${p1.toString().padStart(6)}, p2 = ${p2.toString().padStart(4)} | Dist = ${p2 - p1} | Collisions so far: ${cols}`);
  }
}

console.log(`\nSimulation to 2,000,000 steps finished.`);
console.log(`Final collision count: ${cols}, Last collision step: ${lastCol}`);
