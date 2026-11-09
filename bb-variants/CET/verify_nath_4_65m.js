function parseAgent(tokensStr) {
  const parts = tokensStr.split("_"); // 6 tokens: s0r0, s0r1, s1r0, s1r1, s2r0, s2r1
  return [
    [
      { w: +parts[0][0], d: parts[0][1] === "R" ? 1 : -1, ns: parts[0].charCodeAt(2) - 65 },
      { w: +parts[1][0], d: parts[1][1] === "R" ? 1 : -1, ns: parts[1].charCodeAt(2) - 65 }
    ],
    [
      { w: +parts[2][0], d: parts[2][1] === "R" ? 1 : -1, ns: parts[2].charCodeAt(2) - 65 },
      { w: +parts[3][0], d: parts[3][1] === "R" ? 1 : -1, ns: parts[3].charCodeAt(2) - 65 }
    ],
    [
      { w: +parts[4][0], d: parts[4][1] === "R" ? 1 : -1, ns: parts[4].charCodeAt(2) - 65 },
      { w: +parts[5][0], d: parts[5][1] === "R" ? 1 : -1, ns: parts[5].charCodeAt(2) - 65 }
    ]
  ];
}

const a1 = parseAgent("0LB_0LB_0RC_1LA_1LB_1RC");
const a2 = parseAgent("0RB_1RC_1RC_0RA_1LC_0LB");

console.log("Parsed Agent 1:", JSON.stringify(a1));
console.log("Parsed Agent 2:", JSON.stringify(a2));

const TAPE_SIZE = 10000000;
const OFFSET = 5000000;
const tape = new Int8Array(TAPE_SIZE);

let p1 = OFFSET + 0;
let p2 = OFFSET + 2;
let s1 = 0, s2 = 0;
let minP1 = p1, maxP1 = p1, minP2 = p2, maxP2 = p2;

console.log("\nSimulating Nath76's machine up to 5,000,000 steps...");

for (let step = 1; step <= 5000000; step++) {
  const r1 = tape[p1];
  const r2 = tape[p2];

  const t1 = a1[s1][r1];
  const t2 = a2[s2][r2];

  if (p1 === p2) {
    tape[p1] = t1.w; // LOW priority: Agent 0 writes
  } else {
    tape[p2] = t2.w;
    tape[p1] = t1.w;
  }

  p1 += t1.d;
  p2 += t2.d;
  s1 = t1.ns;
  s2 = t2.ns;

  if (p1 < minP1) minP1 = p1; if (p1 > maxP1) maxP1 = p1;
  if (p2 < minP2) minP2 = p2; if (p2 > maxP2) maxP2 = p2;

  if (p1 === p2) {
    console.log(`\n🎉🎉🎉 CONFIRMED COLLISION! 🎉🎉🎉`);
    console.log(`Exact step: ${step}`);
    console.log(`Collision cell: x = ${p1 - OFFSET}`);
    console.log(`Agent 1 bounds: [${minP1 - OFFSET}, ${maxP1 - OFFSET}]`);
    console.log(`Agent 2 bounds: [${minP2 - OFFSET}, ${maxP2 - OFFSET}]`);
    let ones = 0;
    let minP = Math.min(minP1, minP2), maxP = Math.max(maxP1, maxP2);
    for (let i = minP; i <= maxP; i++) {
      if (tape[i] === 1) ones++;
    }
    console.log(`Ones on tape: ${ones} across ${maxP - minP + 1} cells`);
    break;
  }
}
