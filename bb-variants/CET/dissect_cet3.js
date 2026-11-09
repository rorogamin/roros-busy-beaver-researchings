// Deep Behavioral Dissection of CET(3) Champion (3,746,207 Steps)
// Machine: 1LC1LA_1LA0LC_1RC0LB | 0LB0RA_1RA1LB_0RA0LB
const fs = require('fs');

const bb = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";
function parse(bb) {
  const [h1, h2] = bb.split("|");
  function parseH(h) {
    return h.split("_").map(s => {
      const t0 = { w: +s[0], d: s[1] === "R" ? 1 : -1, ns: s.charCodeAt(2) - 65 };
      const t1 = { w: +s[3], d: s[4] === "R" ? 1 : -1, ns: s.charCodeAt(5) - 65 };
      return [t0, t1];
    });
  }
  return [parseH(h1), parseH(h2)];
}

const [a1, a2] = parse(bb);

// We will track:
// 1. Agent 2 trajectory and visited positions
// 2. Agent 1 sweeps (turns where p1 changes direction or visits left frontier)
// 3. Tape modifications and boundaries

const TAPE_SIZE = 10000000;
const OFFSET = 5000000;
const tape = new Int8Array(TAPE_SIZE);

let p1 = OFFSET, p2 = OFFSET + 2, s1 = 0, s2 = 0;
let minP1 = p1, maxP1 = p1, minP2 = p2, maxP2 = p2;

let a2Positions = new Map();
let a1Sweeps = [];
let prevMinP1 = 0;
let lastTurnStep = 0;

console.log("Analyzing first 10,000 steps to understand startup & initial phase locks...");

let interactionCount = 0;
let lastInteractionStep = 0;

for (let step = 1; step <= 3746207; step++) {
  const r1 = tape[p1];
  const r2 = tape[p2];

  const t1 = a1[s1][r1];
  const t2 = a2[s2][r2];

  tape[p2] = t2.w;
  tape[p1] = t1.w;

  p1 += t1.d;
  p2 += t2.d;
  s1 = t1.ns;
  s2 = t2.ns;

  let pos2 = p2 - OFFSET;
  a2Positions.set(pos2, (a2Positions.get(pos2) || 0) + 1);

  if (p1 < minP1) {
    minP1 = p1;
    let dist = minP1 - OFFSET;
    if (dist % 200 === 0 || dist > -20) {
      a1Sweeps.push({ step, minX: dist, p2: p2 - OFFSET, s1, s2 });
    }
  }

  if (p1 === p2) {
    console.log(`\nCollision at step ${step} at cell ${p1 - OFFSET}!`);
    break;
  }
}

console.log("\n--- AGENT 2 POSITION DISTRIBUTION ---");
console.log(Array.from(a2Positions.entries()).sort((a,b) => a[0] - b[0]));

console.log("\n--- AGENT 1 EXPANSION SWEEPS (Sample of Frontier Growth) ---");
console.log(a1Sweeps.slice(0, 20));
console.log("...\nFinal sweeps before collision:");
console.log(a1Sweeps.slice(-10));
