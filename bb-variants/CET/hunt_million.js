const fs = require('fs');

// Fast flat array simulator for hunting CET(3)
const TAPE_SIZE = 1000000;
const TAPE_OFFSET = 500000;
const tape = new Uint8Array(TAPE_SIZE);
const visited = new Uint32Array(TAPE_SIZE);
let marker = 1;

function simMachine(t0, t1, maxSteps = 3000000) {
  marker++;
  if (marker === 0) {
    visited.fill(0);
    marker = 1;
  }

  let p1 = TAPE_OFFSET;
  let p2 = TAPE_OFFSET + 2;
  let s1 = 0;
  let s2 = 0;

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

    if (p1 === p2) return step;
    let d = p2 - p1;
    // The 265k machine reaches distance 612! So cut off only if > 1500
    if (d > 1500 || d < -1500) return -1;
  }
  return -2; // Survives maxSteps
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

// 265,383 base
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

let baseSteps = simMachine(base0, base1);
console.log('Verified base champion steps:', baseSteps);

console.log('Beginning multi-threaded / deep genetic mutation search for 1M+ steps...');

let best = 265383;
let tested = 0;
const dirs = [-1, 1];

// Random + genetic hill-climb loop
for (let iter = 1; iter <= 200000; iter++) {
  let m0 = JSON.parse(JSON.stringify(base0));
  let m1 = JSON.parse(JSON.stringify(base1));

  // Mutate 1 to 3 transitions
  let numMut = 1 + Math.floor(Math.random() * 3);
  for (let m = 0; m < numMut; m++) {
    let target = Math.random() < 0.5 ? m0 : m1;
    let s = Math.floor(Math.random() * 3);
    let r = Math.floor(Math.random() * 2);
    target[s][r][0] = Math.floor(Math.random() * 2);
    target[s][r][1] = dirs[Math.floor(Math.random() * 2)];
    target[s][r][2] = Math.floor(Math.random() * 3);
  }

  // Quick reject step 1 collision
  if (m0[0][0][1] === 1 && m1[0][0][1] === -1) continue;

  let st = simMachine(m0, m1, 3000000);
  tested++;

  if (st > best) {
    best = st;
    let bb = formatBB(m0, m1);
    console.log('\n============================================================');
    console.log(' [🚨] NEW RECORD DISCOVERY: ' + best + ' STEPS! [🚨]');
    console.log('bbchallenge: ' + bb);
    if (best >= 1000000) {
      console.log('>>> !!! SURPASSED 1,000,000 STEPS IN CET(3) !!! <<<');
    }
    console.log('============================================================\n');
  }

  if (iter % 25000 === 0) {
    console.log('[Progress] Checked ' + (iter/1000) + 'k candidates | Best: ' + best);
  }
}

console.log('Finished search. Best:', best);
