const fs = require('fs');

const TAPE_SIZE = 2000000;
const TAPE_OFFSET = 1000000;
const tape = new Uint8Array(TAPE_SIZE);
const visited = new Uint32Array(TAPE_SIZE);
let marker = 1;

function sim(t0, t1, maxSteps = 5000000) {
  marker++;
  if (marker === 0) {
    visited.fill(0);
    marker = 1;
  }

  let p1 = TAPE_OFFSET;
  let p2 = TAPE_OFFSET + 2;
  let s1 = 0;
  let s2 = 0;
  let revs = 0, lastV1 = 0;

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

    if (tr1[1] !== lastV1) { revs++; lastV1 = tr1[1]; }

    if (p1 === p2) return { halted: true, steps: step, pos: p1 - TAPE_OFFSET, revs };

    let d = p2 - p1;
    if (d > 2000 || d < -2000) return { halted: false };
    if (p1 < 500 || p1 > TAPE_SIZE - 500) return { halted: false };
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

// 717,751 record base: 0LB1LA_0LC0LB_1RB1RC|1LC0RC_1RA1LB_0LB1RC
const base0 = [
  [[0, -1, 1], [1, -1, 0]],
  [[0, -1, 2], [0, -1, 1]],
  [[1,  1, 1], [1,  1, 2]]
];
const base1 = [
  [[1, -1, 2], [0,  1, 2]],
  [[1,  1, 0], [1, -1, 1]],
  [[0, -1, 1], [1,  1, 2]]
];

const dirs = [-1, 1];
console.log('Exploring 717,751 base neighborhood for >= 1,000,000 steps...');

let best = 717751;
let tested = 0;

for (let iter = 1; iter <= 250000; iter++) {
  let m0 = JSON.parse(JSON.stringify(base0));
  let m1 = JSON.parse(JSON.stringify(base1));

  let slots = 1 + Math.floor(Math.random() * 2);
  for (let k = 0; k < slots; k++) {
    let t = Math.random() < 0.5 ? m0 : m1;
    let s = Math.floor(Math.random() * 3);
    let r = Math.floor(Math.random() * 2);
    t[s][r][0] = Math.floor(Math.random() * 2);
    t[s][r][1] = dirs[Math.floor(Math.random() * 2)];
    t[s][r][2] = Math.floor(Math.random() * 3);
  }

  if (m0[0][0][1] === 1 && m1[0][0][1] === -1) continue;

  let res = sim(m0, m1, 4500000);
  tested++;

  if (res.halted && res.revs > 20000 && res.steps > best) {
    best = res.steps;
    let bb = formatBB(m0, m1);
    console.log('\n============================================================');
    console.log(' [🏆] NEW WORLD RECORD HALT: ' + best + ' STEPS! [🏆]');
    console.log('bbchallenge: ' + bb);
    console.log('Collision at cell ' + res.pos + ' after ' + res.revs + ' reversals');
    if (best >= 1000000) {
      console.log('>>> !!! OFFICIAL 1,000,000+ STEP CET(3) CHAMPION !!! <<<');
    }
    console.log('============================================================\n');
  }

  if (iter % 25000 === 0) {
    console.log('[Checked ' + (iter/1000) + 'k] Current peak: ' + best);
  }
}
