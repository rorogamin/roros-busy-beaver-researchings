import { readFileSync } from 'node:fs';
import ModuleFactory from './vendor/cczsite/TM/LongAcc/longacc.js';

const spec = process.argv[2];
const effort = Number(process.argv[3] ?? 2);
const iterations = Number(process.argv[4] ?? 1_000_000);
const maxSeconds = Number(process.argv[5] ?? 60);

if (!spec) {
  console.error('usage: node longacc_run.mjs <machine> [effort] [iterationsPerRow] [maxSeconds]');
  process.exit(2);
}

const wasmBinary = readFileSync(new URL('./vendor/cczsite/TM/LongAcc/longacc.wasm', import.meta.url));
const Module = await ModuleFactory({ wasmBinary });
const api = {
  create: Module.cwrap('longacc_create', 'number', []),
  destroy: Module.cwrap('longacc_destroy', null, ['number']),
  load: Module.cwrap('longacc_load', 'number', ['number', 'string']),
  setEffort: Module.cwrap('longacc_set_effort', null, ['number', 'number']),
  reset: Module.cwrap('longacc_reset', null, ['number']),
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
  console.log(JSON.stringify({ spec, loaded: false, error: api.error(session) || 'load failed' }));
  process.exit(1);
}

const started = Date.now();
const deadline = started + maxSeconds * 1000;
let rows = 0;
let status = 0;
let timeout = false;
while (true) {
  status = api.stepUntilRow(session, Math.max(1, iterations));
  if (status < 0) break;
  if (status > 0) rows++;
  if (status === 2 || api.done(session)) break;
  if (Date.now() >= deadline) {
    timeout = true;
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
};
console.log(JSON.stringify(out, null, 2));
api.destroy(session);
