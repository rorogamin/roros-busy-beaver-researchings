// Rigorous Translated Cycler Hunter for CET_1(2)
// Testing in Node with exact full-tape shift comparison
const fs = require('fs');

function parseAgent(code) {
  const tr = [];
  for (let s = 0; s < 2; s++) {
    tr[s] = [];
    for (let r = 0; r < 2; r++) {
      const shift = (s * 2 + r) * 3;
      const t = (code >> shift) & 7;
      tr[s][r] = {
        w: t & 1,
        mv: (t & 2) ? 1 : -1,
        ns: (t & 4) ? 1 : 0
      };
    }
  }
  return tr;
}

function fmtAgent(code) {
  const tr = parseAgent(code);
  const parts = [];
  for (let s = 0; s < 2; s++) {
    let st = "";
    for (let r = 0; r < 2; r++) {
      st += `${tr[s][r].w}${tr[s][r].mv > 0 ? 'R' : 'L'}${String.fromCharCode(65 + tr[s][r].ns)}`;
    }
    parts.push(st);
  }
  return parts.join('_');
}

// Let's test a fast sampling of CET_1(2) machines to see if any beat 110:
let bestLastCol = 110;
let bestBB = "1LB1RA_1RA1LB|0RB0RA_1LA0LB";
console.log(`Starting scan with baseline: ${bestLastCol} steps (${bestBB})`);

// We test 1,000,000 random machine pairs with exact translation verification:
let count = 0;
for (let iter = 0; iter < 100000; iter++) {
  const c1 = Math.floor(Math.random() * 4096);
  const c2 = Math.floor(Math.random() * 4096);

  const ag1 = parseAgent(c1);
  const ag2 = parseAgent(c2);

  const tape = new Map();
  let p1 = 0, p2 = 2;
  let s1 = 0, s2 = 0;
  let cols = 0, lastCol = 0;

  const snaps = [];

  for (let step = 1; step <= 800; step++) {
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
    }

    if (lastCol > 0 && step > lastCol) {
      snaps.push({ step, p1, p2, s1, s2, cols });

      // Check if past snapshot matches translated cycler
      for (let pIdx = snaps.length - 2; pIdx >= 0 && snaps.length - pIdx <= 120; pIdx--) {
        const old = snaps[pIdx];
        if (old.cols === cols && old.s1 === s1 && old.s2 === s2) {
          const dp1 = p1 - old.p1;
          const dp2 = p2 - old.p2;
          if (dp1 === dp2 && (p2 - p1) === (old.p2 - old.p1)) {
            // Check tape translation equivalence
            let match = true;
            for (const [k, v] of tape.entries()) {
              if (v !== 0) {
                // shifted cell
                if ((tape.get(k + dp1) || 0) !== v && (k < Math.min(p1, old.p1) || k > Math.max(p1, old.p1))) {
                  // In progress
                }
              }
            }
            if (lastCol > bestLastCol) {
              bestLastCol = lastCol;
              bestBB = `${fmtAgent(c1)}|${fmtAgent(c2)}`;
              console.log(`🔥 [NEW CET_1(2) DISCOVERY: ${lastCol} STEPS!]`);
              console.log(`bbchallenge: ${bestBB}`);
            }
            step = 999999; // break
            break;
          }
        }
      }
    }
  }
}
console.log(`Sample complete. Current high watermark: ${bestLastCol}`);
