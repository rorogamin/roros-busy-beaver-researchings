// Examine the shuttle mechanism of CET(3) Champion
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
const TAPE_SIZE = 10000000;
const OFFSET = 5000000;
const tape = new Int8Array(TAPE_SIZE);

let p1 = OFFSET, p2 = OFFSET + 2, s1 = 0, s2 = 0;
let minP1 = p1;

// Track when Agent 1 enters [-10, 2] and when it leaves [-10, 2]
let visitsToA2Zone = [];
let inZone = true;
let enterStep = 1;

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

  if (p1 < minP1) minP1 = p1;

  let x1 = p1 - OFFSET;
  if (!inZone && x1 >= -10) {
    // Agent 1 returned to Agent 2 territory
    inZone = true;
    visitsToA2Zone.push({
      round: visitsToA2Zone.length + 1,
      stepReturn: step,
      awayDuration: step - enterStep,
      furthestLeft: minP1 - OFFSET,
      p2AtReturn: p2 - OFFSET,
      s1AtReturn: s1,
      s2AtReturn: s2
    });
  } else if (inZone && x1 < -10) {
    inZone = false;
    enterStep = step;
  }

  if (p1 === p2) {
    console.log(`Collision at step ${step} at cell ${p1 - OFFSET}! Final Round: ${visitsToA2Zone.length + 1}`);
    break;
  }
}

console.log("Total shuttle rounds where Agent 1 visited the left frontier and returned:", visitsToA2Zone.length);
console.log("\nFirst 10 rounds:");
console.table(visitsToA2Zone.slice(0, 10));
console.log("\nLast 10 rounds before collision:");
console.table(visitsToA2Zone.slice(-10));
