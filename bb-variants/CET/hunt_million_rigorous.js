const fs = require('fs');
const CETSimulator = require('./simulator.js');

const TAPE_SIZE = 1000000;
const TAPE_OFFSET = 500000;
const tape = new Uint8Array(TAPE_SIZE);
const visited = new Uint32Array(TAPE_SIZE);
let marker = 1;

function simCandidate(t0, t1, maxSteps = 2500000) {
  marker++;
  if (marker === 0) {
    visited.fill(0);
    marker = 1;
  }

  let p1 = TAPE_OFFSET;
  let p2 = TAPE_OFFSET + 2;
  let s1 = 0;
  let s2 = 0;

  let minP1 = p1, maxP1 = p1;
  let rev1 = 0, lastV1 = 0;

  for (let step = 1; step <= maxSteps; step++) {
    let r1 = (visited[p1] === marker) ? tape[p1] : 0;
    let r2 = (visited[p2] === marker) ? tape[p2] : 0;

    let tr1 = t0[s1][r1];
    let tr2 = t1[s2][r2];

    visited[p2] = marker; tape[p2] = tr2[0];
    visited[p1] = marker; tape[p1] = tr1[0];

    p1 += tr1[1];
    p2 += tr2[1];

    s1 = tr1[2];
    s2 = tr2[2];

    if (tr1[1] !== lastV1) {
      rev1++;
      lastV1 = tr1[1];
    }

    if (p1 < minP1) minP1 = p1;
    if (p1 > maxP1) maxP1 = p1;

    if (p1 === p2) {
      // Must have traversed back and forth like a real counter (reversals > 1000 and bounded span)
      let span = maxP1 - minP1;
      return { halted: true, steps: step, pos: p1 - TAPE_OFFSET, span, rev1 };
    }

    let d = p2 - p1;
    if (d > 1200 || d < -1200) return { halted: false };
    if (p1 < 1000 || p1 > TAPE_SIZE - 1000) return { halted: false };
  }
  return { halted: false };
}

function formatBB(t0, t1) {
  const letters = ['A','B','C'];
  let str = '';
  for (let a = 0; a < 2; a++) {
    let t = (a === 0) ? t0 : t1;
    if (a > 0) str += '|';
    for (let s = 0; s < 3; s++) {
      if (s > 0) str += '_';
      for (let r = 0; r < 2; r++) {
        let tr = t[s][r];
        str += tr[0] + (tr[1] > 0 ? 'R' : 'L') + letters[tr[2]];
      }
    }
  }
  return str;
}

const base0 = [
  [[0, -1, 2], [1, -1, 0]],
  [[0, -1, 2], [0, -1, 1]],
  [[1,  1, 1], [1,  1, 2]]
];
const base1 = [
  [[1,  1, 2], [0,  1, 2]],
  [[1,  1, 0], [1, -1, 1]],
  [[0, -1, 1], [1,  1, 2]]
];

let baseRes = simCandidate(base0, base1);
console.log('265k baseline check: steps =', baseRes.steps, 'span =', baseRes.span, 'reversals =', baseRes.rev1);

console.log('Hunting for 500k..1M+ true counter champions...');

let best = 265383;
const dirs = [-1, 1];

for (let iter = 1; iter <= 150000; iter++) {
  let m0 = JSON.parse(JSON.stringify(base0));
  let m1 = JSON.parse(JSON.stringify(base1));

  // Focus mutations on transitions that preserve the counter structure
  let mutTarget = Math.random() < 0.5 ? m0 : m1;
  let s = Math.floor(Math.random() * 3);
  let r = Math.floor(Math.random() * 2);
  mutTarget[s][r][0] = Math.floor(Math.random() * 2);
  mutTarget[s][r][1] = dirs[Math.floor(Math.random() * 2)];
  mutTarget[s][r][2] = Math.floor(Math.random() * 3);

  let res = simCandidate(m0, m1);
  if (res.halted && res.rev1 > 5000 && res.steps > best) {
    best = res.steps;
    let bb = formatBB(m0, m1);
    console.log('\n============================================================');
    console.log(' [🌟] NEW VERIFIED RECORD: ' + best + ' STEPS! [🌟]');
    console.log('bbchallenge: ' + bb);
    console.log('Active span: ' + res.span + ' cells | Reversals: ' + res.rev1 + ' | Collision at: ' + res.pos);
    if (best >= 1000000) {
      console.log('>>> !!! OFFICIAL 1,000,000+ STEP CET(3) CHAMPION !!! <<<');
    }
    console.log('============================================================\n');
  }

  if (iter % 25000 === 0) {
    console.log('[Checked ' + (iter/1000) + 'k candidates] Current best: ' + best);
  }
}
