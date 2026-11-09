const m = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";
function parse(m) {
  const [p1, p2] = m.split("|");
  function parseHalf(h) {
    const tr = [];
    for (const s of h.split("_")) {
      const t0 = {w: +s[0], m: s[1]==="R"?1:-1, ns: s.charCodeAt(2)-65};
      const t1 = {w: +s[3], m: s[4]==="R"?1:-1, ns: s.charCodeAt(5)-65};
      tr.push([t0, t1]);
    }
    return tr;
  }
  return [parseHalf(p1), parseHalf(p2)];
}

const [a1, a2] = parse(m);
const tape = new Int8Array(10000000);
const OFFSET = 5000000;
let p1 = OFFSET, p2 = OFFSET + 2, s1 = 0, s2 = 0;
let minP1 = p1, maxP1 = p1, minP2 = p2, maxP2 = p2;

for (let step = 1; step <= 3746210; step++) {
  const r1 = tape[p1];
  const r2 = tape[p2];
  const t1 = a1[s1][r1];
  const t2 = a2[s2][r2];
  tape[p2] = t2.w;
  tape[p1] = t1.w;
  p1 += t1.m;
  p2 += t2.m;
  s1 = t1.ns;
  s2 = t2.ns;

  if (p1 < minP1) minP1 = p1; if (p1 > maxP1) maxP1 = p1;
  if (p2 < minP2) minP2 = p2; if (p2 > maxP2) maxP2 = p2;

  if (p1 === p2) {
    console.log(`Collided at step ${step} at cell ${p1 - OFFSET}`);
    console.log(`Agent 1 bounds: [${minP1 - OFFSET}, ${maxP1 - OFFSET}] (width ${maxP1 - minP1})`);
    console.log(`Agent 2 bounds: [${minP2 - OFFSET}, ${maxP2 - OFFSET}] (width ${maxP2 - minP2})`);
    break;
  }
}
