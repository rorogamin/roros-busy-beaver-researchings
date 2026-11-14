import { appendFileSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import ModuleFactory from './vendor/cczsite/TM/LongAcc/longacc.js';

const spec = process.argv[2];
const tracePath = process.argv[3];
const effort = Number(process.argv[4] ?? 2);
const iterations = Number(process.argv[5] ?? 1_000_000);
const maxSeconds = Number(process.argv[6] ?? 240);

if (!spec || !tracePath) {
  console.error('usage: node longacc_trace.mjs <machine> <trace.jsonl> [effort] [iterationsPerRow] [maxSeconds]');
  process.exit(2);
}

mkdirSync(dirname(tracePath), { recursive: true });
writeFileSync(tracePath, '');

const wasmBinary = readFileSync(new URL('./vendor/cczsite/TM/LongAcc/longacc.wasm', import.meta.url));
const Module = await ModuleFactory({ wasmBinary });
const api = {
  create: Module.cwrap('longacc_create', 'number', []),
  destroy: Module.cwrap('longacc_destroy', null, ['number']),
  load: Module.cwrap('longacc_load', 'number', ['number', 'string']),
  setEffort: Module.cwrap('longacc_set_effort', null, ['number', 'number']),
  stepUntilRow: Module.cwrap('longacc_step_until_row', 'number', ['number', 'number']),
  config: Module.cwrap('longacc_config', 'string', ['number']),
  error: Module.cwrap('longacc_error', 'string', ['number']),
  head: Module.cwrap('longacc_head', 'number', ['number']),
  state: Module.cwrap('longacc_state', 'number', ['number']),
  direction: Module.cwrap('longacc_direction', 'number', ['number']),
  width: Module.cwrap('longacc_width', 'number', ['number']),
  height: Module.cwrap('longacc_height', 'number', ['number']),
  halted: Module.cwrap('longacc_halted', 'number', ['number']),
  done: Module.cwrap('longacc_done', 'number', ['number']),
};

const session = api.create();
api.setEffort(session, Math.max(0, effort));
if (!api.load(session, spec)) {
  const out = { spec, loaded: false, error: api.error(session) || 'load failed' };
  appendFileSync(tracePath, JSON.stringify(out) + '\n');
  console.log(JSON.stringify(out));
  process.exit(1);
}

const started = Date.now();
const deadline = started + maxSeconds * 1000;
let rows = 0;
let status = 0;
let timeout = false;

function snapshot(row, kind, statusValue) {
  return {
    spec,
    row,
    kind,
    status: statusValue,
    elapsedMs: Date.now() - started,
    halted: Boolean(api.halted(session)),
    done: Boolean(api.done(session)),
    state: api.state(session),
    head: api.head(session),
    direction: api.direction(session),
    width: api.width(session),
    height: api.height(session),
    config: api.config(session) || null,
  };
}

appendFileSync(tracePath, JSON.stringify(snapshot(0, 'initial', null)) + '\n');

while (true) {
  status = api.stepUntilRow(session, Math.max(1, iterations));
  if (status < 0) {
    appendFileSync(tracePath, JSON.stringify(snapshot(rows, 'error', status)) + '\n');
    break;
  }
  if (status > 0) {
    rows++;
    appendFileSync(tracePath, JSON.stringify(snapshot(rows, 'row', status)) + '\n');
  }
  if (status === 2 || api.done(session)) {
    appendFileSync(tracePath, JSON.stringify(snapshot(rows, 'done', status)) + '\n');
    break;
  }
  if (Date.now() >= deadline) {
    timeout = true;
    appendFileSync(tracePath, JSON.stringify(snapshot(rows, 'timeout', status)) + '\n');
    break;
  }
}

const out = {
  spec,
  effort,
  iterationsPerRow: iterations,
  rows,
  status,
  timeout,
  halted: Boolean(api.halted(session)),
  done: Boolean(api.done(session)),
  state: api.state(session),
  head: api.head(session),
  direction: api.direction(session),
  width: api.width(session),
  height: api.height(session),
  error: api.error(session) || null,
  config: api.config(session) || null,
  elapsedMs: Date.now() - started,
  tracePath,
};
console.log(JSON.stringify(out, null, 2));
api.destroy(session);
