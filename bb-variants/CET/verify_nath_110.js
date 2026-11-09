// Simulate Nath76's new CET_1(2) candidate:
// Agent 1: 1LB_1RA_1RA_1LB  (in std: 1LB1RA_1RA1LB)
// Agent 2: 0RB_0RA_1LA_0LB  (in std: 0RB0RA_1LA0LB)

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

const bb = "1LB1RA_1RA1LB|0RB0RA_1LA0LB";
const [ag1, ag2] = bb.split('|').map(parseAgent);
const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;
let cols = 0;
let lastCol = 0;

console.log("=== SIMULATING NATH76 110 CANDIDATE ===");
console.log("bbchallenge:", bb);

const seen = new Map();

for (let step = 1; step <= 300; step++) {
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

  // Get active tape string
  let minX = Infinity, maxX = -Infinity;
  for (const [k, v] of tape.entries()) {
    if (v !== 0) {
      if (k < minX) minX = k;
      if (k > maxX) maxX = k;
    }
  }

  // State signature: (p1, p2, s1, s2, tape signature)
  // Or translated signature: (p2 - p1, s1, s2, tape shifted by p1)
  let tapeStr = "";
  if (minX <= maxX) {
    const arr = [];
    for (let x = minX; x <= maxX; x++) arr.push(tape.get(x) || 0);
    tapeStr = `${minX - p1}:${arr.join('')}`;
  }
  const key = `${p2 - p1}_${s1}_${s2}_${tapeStr}`;

  if (isCol || step >= 105) {
    console.log(`Step ${step.toString().padStart(3)}: p1=${p1.toString().padStart(3)} (s1=${s1}), p2=${p2.toString().padStart(3)} (s2=${s2}) | ${isCol ? '💥 COLLISION #' + cols : ''}`);
  }

  if (seen.has(key)) {
    const past = seen.get(key);
    console.log(`\n🔁 CYCLE DETECTED! Current step ${step}, past step ${past.step}`);
    console.log(`Cycle period: ${step - past.step}, delta_p1: ${p1 - past.p1}, delta_p2: ${p2 - past.p2}`);
    console.log(`Collisions in past: ${past.cols}, collisions now: ${cols}`);
    if (past.cols === cols) {
      console.log(`✅ ZERO COLLISIONS IN CYCLE! QUASI-HALTS AT STEP ${lastCol}!`);
    } else {
      console.log(`⚠️ Collisions occurred inside the cycle!`);
    }
    break;
  }
  seen.set(key, { step, p1, p2, cols });
}

console.log(`\nFinal: Last collision step = ${lastCol}, total collisions = ${cols}`);
