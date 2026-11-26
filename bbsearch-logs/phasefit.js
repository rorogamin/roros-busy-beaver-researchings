// Phase analysis of the outer loop: delta between successive new-leftmost cells.
const fs = require('fs');
const lines = fs.readFileSync(process.argv[2] || 'phase.log', 'utf8').split(/\r?\n/);
const ev = [];
for (const l of lines) {
  const m = l.match(/^MINLINE (\d+) (\d+) (-?\d+) (\d+) (\d+)$/);
  if (m) ev.push({ i: +m[1], steps: +m[2], pos: +m[3], span: +m[4], cells: +m[5] });
}
const d = [];
for (let i = 1; i < ev.length; i++) d.push(ev[i].steps - ev[i - 1].steps);

// phase boundary: a large relative drop
const phases = [];
let start = 0, peak = d[0], peakAt = 1;
for (let i = 1; i < d.length; i++) {
  if (d[i] < peak / 2) {
    phases.push({ from: start + 1, to: i, len: i - start, peak, peakAt });
    start = i; peak = d[i]; peakAt = i + 1;
  } else if (d[i] > peak) { peak = d[i]; peakAt = i + 1; }
}
phases.push({ from: start + 1, to: d.length, len: d.length - start, peak, peakAt });

console.log('events', ev.length, 'last step', ev[ev.length - 1].steps, 'last pos', ev[ev.length - 1].pos);
console.log('phases', phases.length);
for (const p of phases.slice(0, 12)) console.log('  phase', p.from + '..' + p.to, 'len', p.len, 'peakDelta', p.peak, 'peakAt', p.peakAt);
console.log('  ...');
for (const p of phases.slice(-4)) console.log('  phase', p.from + '..' + p.to, 'len', p.len, 'peakDelta', p.peak, 'peakAt', p.peakAt);

// slope of delta within the last few phases (per iteration)
for (const p of phases.slice(-3)) {
  const a = p.from, b = p.to;
  if (b - a < 50) continue;
  const n = b - a;
  let sx = 0, sy = 0, sxx = 0, sxy = 0;
  for (let i = a; i < b; i++) { const x = i - a; const y = d[i - 1]; sx += x; sy += y; sxx += x * x; sxy += x * y; }
  const slope = (n * sxy - sx * sy) / (n * sxx - sx * sx);
  console.log('  fit phase ' + a + '..' + b + ': slope ' + slope.toFixed(3) + ' steps/iteration, resid-free check done');
}
// global: how many resets in the last 100k steps, and cells vs steps exponent
const last = ev[ev.length - 1];
const ref = ev.find(e => e.steps >= 1e6);
console.log('cells', ref.cells, '->', last.cells, 'over steps', ref.steps, '->', last.steps,
  'exponent', (Math.log(last.cells / ref.cells) / Math.log(last.steps / ref.steps)).toFixed(3));
