// Verify MCET(3) Champion 1,300,013 steps
const bb = "1RA0LA_1LC1LB_1LC1LB|1RB1LA_1RC1LB_0LA0RB|0RC1RB_0LA0LC_1RB0LC";

function parseMCET3(bb) {
  const agents = bb.split("|").map(agStr => {
    return agStr.split("_").map(stStr => {
      // 2 symbols: stStr is 6 chars e.g. "1RA0LA"
      const t0 = { w: +stStr[0], d: stStr[1] === "R" ? 1 : -1, ns: stStr.charCodeAt(2) - 65 };
      const t1 = { w: +stStr[3], d: stStr[4] === "R" ? 1 : -1, ns: stStr.charCodeAt(5) - 65 };
      return [t0, t1];
    });
  });
  return agents;
}

const agents = parseMCET3(bb);
const tape = new Int8Array(4000000);
const OFFSET = 2000000;
let p1 = OFFSET + 0, p2 = OFFSET + 2, p3 = OFFSET + 4;
let s1 = 0, s2 = 0, s3 = 0;
let minP = OFFSET, maxP = OFFSET + 4;

console.log("Simulating MCET(3) 1.3M machine...");
for (let step = 1; step <= 2000000; step++) {
  const r1 = tape[p1];
  const r2 = tape[p2];
  const r3 = tape[p3];

  const tr1 = agents[0][s1][r1];
  const tr2 = agents[1][s2][r2];
  const tr3 = agents[2][s3][r3];

  // Writing priority: Agent 3, then Agent 2, then Agent 1
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
    console.log(`✅ VERIFIED ALL-AGENT COLLISION!`);
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
