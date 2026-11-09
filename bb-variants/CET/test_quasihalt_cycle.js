function getTapeSignature(tape, p1) {
  let minX = Infinity, maxX = -Infinity;
  for (const [k, v] of tape.entries()) {
    if (v !== 0) {
      if (k < minX) minX = k;
      if (k > maxX) maxX = k;
    }
  }
  if (minX > maxX) return 'empty';
  const arr = [];
  for (let x = minX; x <= maxX; x++) {
    arr.push(tape.get(x) || 0);
  }
  return (minX - p1) + ':' + arr.join('');
}

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
let cols = 0, lastCol = 0;

const map = new Map();

for (let step = 1; step <= 200; step++) {
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
    const rel = p2 - p1;
    const tSig = getTapeSignature(tape, p1);
    const key = `${rel}_${s1}_${s2}_${tSig}`;

    if (map.has(key)) {
      const past = map.get(key);
      const dp1 = p1 - past.p1;
      const dp2 = p2 - past.p2;
      const cyc = step - past.step;
      if (dp1 === dp2 && past.cols === cols) {
        console.log(`PROVEN QUASI-HALT! Last collision: Step ${lastCol}, cycle closed at step ${step} with period ${cyc}, drift ${dp1}!`);
        break;
      }
    }
    map.set(key, { step, p1, p2, cols });
  }
}
