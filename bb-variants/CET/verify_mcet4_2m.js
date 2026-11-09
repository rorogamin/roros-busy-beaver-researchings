// Verify 4,239,504 step MCET(3) Champion
const bb = "1LC1LA_1RA1RB_0RB0RA|1LC1LB_1RB0RA_0LC0RA|0LA1RB_0RC1RB_0RA1RC";

function parseMCET3(bb) {
  return bb.split("|").map(agStr => {
    return agStr.split("_").map(stStr => {
      const t0 = { w: +stStr[0], d: stStr[1] === "R" ? 1 : -1, ns: stStr.charCodeAt(2) - 65 };
      const t1 = { w: +stStr[3], d: stStr[4] === "R" ? 1 : -1, ns: stStr.charCodeAt(5) - 65 };
      return [t0, t1];
    });
  });
}

const agents = parseMCET3(bb);
const tape = new Int8Array(10000000);
const OFFSET = 5000000;
let p1 = OFFSET + 0, p2 = OFFSET + 2, p3 = OFFSET + 4;
let s1 = 0, s2 = 0, s3 = 0;
let minP = OFFSET, maxP = OFFSET + 4;

console.log("Simulating and verifying 4.23M all-agent MCET(3) machine...");
for (let step = 1; step <= 5000000; step++) {
  const r1 = tape[p1];
  const r2 = tape[p2];
  const r3 = tape[p3];

  const tr1 = agents[0][s1][r1];
  const tr2 = agents[1][s2][r2];
  const tr3 = agents[2][s3][r3];

  // Writing priority: Agent 3, Agent 2, Agent 1
  tape[p3] = tr3.w;
  tape[p2] = tr2.w;
  tape[p1] = tr1.w;

  p1 += tr1.d;
  p2 += tr2.d;
  p3 += tr3.d;

  s1 = tr1.ns;
  s2 = tr2.ns;
  s3 = tr3.ns;

  if (p1 < minP) minP = p1; if (p1 > maxP) maxP = p1;
  if (p2 < minP) minP = p2; if (p2 > maxP) maxP = p2;
  if (p3 < minP) minP = p3; if (p3 > maxP) maxP = p3;

  if (p1 === p2 && p2 === p3) {
    console.log(`✅ VERIFIED ALL-AGENT SIMULTANEOUS COLLISION!`);
    console.log(`Step: ${step}`);
    console.log(`Collision Cell: ${p1 - OFFSET}`);
    console.log(`Tape range: [${minP - OFFSET}, ${maxP - OFFSET}] (width ${maxP - minP + 1})`);
    
    let ones = 0;
    for (let i = minP; i <= maxP; i++) {
      if (tape[i] === 1) ones++;
    }
    console.log(`Ones on tape: ${ones}`);
    break;
  }
}
