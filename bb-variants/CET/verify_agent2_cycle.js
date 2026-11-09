function parseAgent(str) {
  const states = str.split('_');
  const tr = [];
  for (let s = 0; s < states.length; s++) {
    tr[s] = [];
    for (let r = 0; r < 2; r++) {
      const tok = states[s].substring(r * 3, r * 3 + 3);
      tr[s][r] = { w: parseInt(tok[0]), mv: tok[1] === 'R' ? 1 : -1, ns: tok[2].charCodeAt(0) - 65 };
    }
  }
  return tr;
}
const bb = '1RA1RB_1LA0LB|1LA0RB_0LA1RB';
const [ag1, ag2] = bb.split('|').map(parseAgent);
const tape = new Map();
let p1 = 0, p2 = 2;
let s1 = 0, s2 = 0;

for (let step = 1; step <= 2000; step++) {
  const r1 = tape.get(p1) || 0;
  const r2 = tape.get(p2) || 0;
  const t1 = ag1[s1][r1];
  const t2 = ag2[s2][r2];
  tape.set(p2, t2.w);
  tape.set(p1, t1.w);
  p1 += t1.mv; s1 = t1.ns;
  p2 += t2.mv; s2 = t2.ns;
}

const seen2 = new Map();
for (let step = 2001; step <= 5000; step++) {
  const r2 = tape.get(p2) || 0;
  const t2 = ag2[s2][r2];
  tape.set(p2, t2.w);
  p2 += t2.mv; s2 = t2.ns;
  const tapeSlice = [0,1,2,3,4].map(x => tape.get(x) || 0).join('');
  const key = p2 + '_' + s2 + '_' + tapeSlice;
  if (seen2.has(key)) {
    console.log('Agent 2 in-place cycle confirmed at step', step, 'with period:', step - seen2.get(key));
    break;
  }
  seen2.set(key, step);
}
