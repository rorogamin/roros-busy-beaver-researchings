const m = "1LC1LA_1LA0LC_1RC0LB|0LB0RA_1RA1LB_0RA0LB";
function parse(m) {
  let [p1, p2] = m.split("|");
  function parseHalf(h) {
    let tr = [];
    for (let s of h.split("_")) {
      let t0 = {w: +s[0], m: s[1]==="R"?1:-1, ns: s.charCodeAt(2)-65};
      let t1 = {w: +s[3], m: s[4]==="R"?1:-1, ns: s.charCodeAt(5)-65};
      tr.push([t0, t1]);
    }
    return tr;
  }
  return [parseHalf(p1), parseHalf(p2)];
}
let [a1, a2] = parse(m);
let c1 = [[0,0],[0,0],[0,0]], c2 = [[0,0],[0,0],[0,0]];
let tape = new Int8Array(10000000);
let OFFSET = 5000000;
let p1 = OFFSET, p2 = OFFSET + 2, s1 = 0, s2 = 0;
for (let step = 1; step <= 3746207; step++) {
  let r1 = tape[p1], r2 = tape[p2];
  c1[s1][r1]++; c2[s2][r2]++;
  let t1 = a1[s1][r1], t2 = a2[s2][r2];
  tape[p2] = t2.w; tape[p1] = t1.w;
  p1 += t1.m; p2 += t2.m;
  s1 = t1.ns; s2 = t2.ns;
}
console.log("Agent 1 transitions used:");
console.log("State A: [0]->", c1[0][0], "[1]->", c1[0][1]);
console.log("State B: [0]->", c1[1][0], "[1]->", c1[1][1]);
console.log("State C: [0]->", c1[2][0], "[1]->", c1[2][1]);
console.log("\nAgent 2 transitions used:");
console.log("State A: [0]->", c2[0][0], "[1]->", c2[0][1]);
console.log("State B: [0]->", c2[1][0], "[1]->", c2[1][1]);
console.log("State C: [0]->", c2[2][0], "[1]->", c2[2][1]);
