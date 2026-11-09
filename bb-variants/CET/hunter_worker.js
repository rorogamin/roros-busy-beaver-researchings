/**
 * Busy Beaver Hunter Web Worker
 * Runs continuous background searches for high-step colliding CET(n) / MCET machines.
 */

// Import or define simulation logic in worker scope
function createRandomTable(nStates, nSymbols = 2) {
  const table = [];
  for (let s = 0; s < nStates; s++) {
    const row = [];
    for (let sym = 0; sym < nSymbols; sym++) {
      row.push({
        write: Math.random() < 0.5 ? 1 : 0,
        dir: Math.random() < 0.5 ? 1 : -1,
        nextState: Math.floor(Math.random() * nStates)
      });
    }
    table.push(row);
  }
  return table;
}

function mutateTable(table, nStates) {
  const newTbl = JSON.parse(JSON.stringify(table));
  const s = Math.floor(Math.random() * nStates);
  const sym = Math.floor(Math.random() * 2);
  const choice = Math.floor(Math.random() * 3);
  if (choice === 0) {
    newTbl[s][sym].write = 1 - newTbl[s][sym].write;
  } else if (choice === 1) {
    newTbl[s][sym].dir = -newTbl[s][sym].dir;
  } else {
    newTbl[s][sym].nextState = Math.floor(Math.random() * nStates);
  }
  return newTbl;
}

function simulateFast(tables, agentCount, initialPositions, maxSteps) {
  const TAPE_OFFSET = 32768;
  const TAPE_SIZE = 65536;
  const tape = new Uint8Array(TAPE_SIZE);
  const visited = new Int32Array(TAPE_SIZE);
  const marker = Math.floor(Math.random() * 100000000) + 1;

  const positions = new Int32Array(agentCount);
  const states = new Uint8Array(agentCount);

  for (let i = 0; i < agentCount; i++) {
    positions[i] = (initialPositions[i] !== undefined ? initialPositions[i] : i * 2) + TAPE_OFFSET;
    states[i] = 0;
  }

  // Pre-flatten tables for fast array lookup
  // flatTable[agent][state * 2 + sym] => { w, d, ns }
  const flatW = new Uint8Array(agentCount * 16 * 2);
  const flatD = new Int8Array(agentCount * 16 * 2);
  const flatNS = new Uint8Array(agentCount * 16 * 2);

  for (let a = 0; a < agentCount; a++) {
    const tbl = tables[a];
    const nS = tbl.length;
    for (let s = 0; s < nS; s++) {
      for (let sym = 0; sym < 2; sym++) {
        const idx = (a * 16 + s) * 2 + sym;
        const entry = tbl[s][sym];
        flatW[idx] = entry.write;
        flatD[idx] = entry.dir;
        flatNS[idx] = entry.nextState;
      }
    }
  }

  for (let step = 0; step < maxSteps; step++) {
    // Check pairwise collision
    for (let i = 0; i < agentCount; i++) {
      for (let j = i + 1; j < agentCount; j++) {
        if (positions[i] === positions[j]) {
          return { collided: true, step: step, pos: positions[i] - TAPE_OFFSET };
        }
      }
    }

    // Distance prune for 2 agents
    if (agentCount === 2) {
      const dist = Math.abs(positions[0] - positions[1]);
      if (dist > 2 * (maxSteps - step)) {
        return { collided: false, step: maxSteps };
      }
    }

    // Read symbols
    const reads = new Uint8Array(agentCount);
    for (let a = 0; a < agentCount; a++) {
      const p = positions[a];
      if (p < 50 || p >= TAPE_SIZE - 50) return { collided: false, step: maxSteps };
      reads[a] = (visited[p] === marker) ? tape[p] : 0;
    }

    // Write & Move
    for (let a = 0; a < agentCount; a++) {
      const p = positions[a];
      const s = states[a];
      const sym = reads[a];
      const idx = (a * 16 + s) * 2 + sym;

      const w = flatW[idx];
      const d = flatD[idx];
      const ns = flatNS[idx];

      visited[p] = marker;
      tape[p] = w;

      positions[a] += d;
      states[a] = ns;
    }
  }

  // Final check at maxSteps
  for (let i = 0; i < agentCount; i++) {
    for (let j = i + 1; j < agentCount; j++) {
      if (positions[i] === positions[j]) {
        return { collided: true, step: maxSteps, pos: positions[i] - TAPE_OFFSET };
      }
    }
  }

  return { collided: false, step: maxSteps };
}

let isSearching = false;
let config = {
  nStates: 2,
  agentCount: 2,
  initialPositions: [0, 2],
  maxSteps: 5000,
  mode: 'random' // 'random' | 'hill_climb'
};

let currentBest = null;
let topMachines = [];

self.onmessage = function (e) {
  const { command, params } = e.data;
  if (command === 'start') {
    Object.assign(config, params);
    isSearching = true;
    runSearchLoop();
  } else if (command === 'stop') {
    isSearching = false;
  } else if (command === 'updateConfig') {
    Object.assign(config, params);
  }
};

function runSearchLoop() {
  if (!isSearching) return;

  const BATCH_SIZE = 500;
  let batchChecked = 0;
  let newRecords = [];

  for (let b = 0; b < BATCH_SIZE; b++) {
    let candidateTables;
    if (config.mode === 'hill_climb' && currentBest) {
      candidateTables = currentBest.tables.map(t => mutateTable(t, config.nStates));
    } else {
      candidateTables = [];
      for (let a = 0; a < config.agentCount; a++) {
        candidateTables.push(createRandomTable(config.nStates));
      }
    }

    const res = simulateFast(candidateTables, config.agentCount, config.initialPositions, config.maxSteps);
    batchChecked++;

    if (res.collided && res.step > 0) {
      if (!currentBest || res.step > currentBest.step) {
        currentBest = {
          step: res.step,
          pos: res.pos,
          tables: candidateTables,
          nStates: config.nStates,
          agentCount: config.agentCount
        };
        newRecords.push(currentBest);
      }
    }
  }

  self.postMessage({
    type: 'progress',
    checked: batchChecked,
    currentBestStep: currentBest ? currentBest.step : 0,
    newRecords: newRecords
  });

  if (isSearching) {
    setTimeout(runSearchLoop, 0);
  }
}
