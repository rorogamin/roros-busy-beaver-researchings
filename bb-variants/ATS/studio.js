/* UI controller for the Absorbing Tag System simulator and space-time studio. */
(function () {
  'use strict';

  const { ATSSimulator, parseTape, formatTape, formatToken, tokenCategory } = window.ATSCore;

  const PRESETS = [
    {
      id: 'grove',
      label: 'Grove — length 32, cryptid candidate',
      tape: '[fn(010), fn(011), fn(00011000), fn(111), fn(1111111), fn(10), fn(10), fn(0001)]',
      note: 'All-function candidate. Its core grows for at least 10M steps; not a halting proof.',
    },
    {
      id: 'loom',
      label: 'Loom — length 9, certified BMO non-halter',
      tape: '[1, fn(1), 0, 1, fn(1), fn(01), 1, 0]',
      note: 'Certified non-halting via the finite type-set invariant. Decidable, not a cryptid.',
    },
    {
      id: 'probe8',
      label: 'Length-8 probe — fixed-core rotor',
      tape: '[1, 1, 1, 0, fn(1), fn(1), fn(1), fn(0)]',
      note: 'The requested length-8 extension; enters a fixed 74-token core after step 884.',
    },
    {
      id: 'rattle',
      label: 'Rattle — length 14, cryptid candidate',
      tape: '[fn(11111), fn(1), fn(0011), fn(1), fn(01), fn(0)]',
      note: 'Small all-function candidate with a slowly changing core; no fixed-core collapse observed.',
    },
    {
      id: 'n6',
      label: 'Length-6 halter — 108 steps',
      tape: '[1, 1, 1, 0, fn(1), fn(0)]',
      note: 'Verified length-6 halter; useful for watching a clean endgame.',
    },
    {
      id: 'n7',
      label: 'Length-7 halter — 253 steps',
      tape: '[1, 1, 1, 0, fn(1), fn(1), fn(0)]',
      note: 'Verified length-7 halter; compare the endgame with the length-8 probe.',
    },
    {
      id: 'n8best',
      label: 'Length-8 best halter — 307 steps',
      tape: '[fn(11), 1, 1, 0, 1, 1, 0]',
      note: 'Best length-8 halter found in the local 100k-step sweep (lower bound for the class).',
    },
  ];

  const $ = (id) => document.getElementById(id);
  const canvas = $('spacetimeCanvas');
  const readout = $('spacetimeReadout');
  const diagram = new window.ATSSpaceTime(canvas, readout);

  let sim = null;
  let running = false;
  let rafId = null;
  let lastFrame = 0;
  let accumulator = 0;
  let currentPreset = PRESETS[0];

  function presetById(id) {
    return PRESETS.find((p) => p.id === id) || null;
  }

  function setStatus(text, kind) {
    const badge = $('statusBadge');
    badge.className = 'status-badge' + (kind ? ` status-${kind}` : '');
    badge.textContent = text;
  }

  function pause() {
    running = false;
    $('btnRunPause').textContent = 'Run';
    $('btnRunPause').classList.remove('btn-rose');
    $('btnRunPause').classList.add('btn-green');
    if (rafId !== null) cancelAnimationFrame(rafId);
    rafId = null;
  }

  function refreshMetrics() {
    $('metricStep').textContent = sim.steps.toLocaleString();
    $('metricTokens').textContent = sim.tokens().toLocaleString();
    $('metricLength').textContent = sim.length.toLocaleString();
    $('metricZeros').textContent = sim.zeros.toLocaleString();
    $('metricCore').textContent = sim.nonFn1.toLocaleString();
    $('metricTypes').textContent = sim.types.size.toLocaleString();
    $('metricMax').textContent = sim.maxTokens.toLocaleString();
    $('metricDecreases').textContent = sim.decreases.toLocaleString();

    const types = Array.from(sim.types).map(formatToken);
    $('typeList').textContent = types.length
      ? types.slice(0, 28).join(', ') + (types.length > 28 ? `, … (${types.length} total)` : '')
      : '—';

    if (sim.halted) {
      setStatus(`HALTED — tape became empty at step ${sim.steps.toLocaleString()}.`, 'halted');
    } else if (sim.proof === 'zero-free') {
      setStatus(`PROVED NON-HALTING — zero-free decider at step ${sim.steps.toLocaleString()}.`, 'cycle');
    } else if (running) {
      setStatus(`Running at step ${sim.steps.toLocaleString()} — ${sim.tokens().toLocaleString()} tokens.`, 'running');
    } else if (sim.steps === 0) {
      setStatus('Ready — press Run, Step, or +100. This view is unclassified.', '');
    } else {
      setStatus(`Paused at step ${sim.steps.toLocaleString()} — no halting or cycle proof yet.`, '');
    }

    $('tapeShape').textContent =
      `${sim.tokens().toLocaleString()} tokens · ${sim.length.toLocaleString()} ATS length · ` +
      `${sim.zeros.toLocaleString()} zeros · ${sim.nonFn1.toLocaleString()} non-fn(1)`;
    $('rowsLabel').textContent = `${diagram.visibleRows.toLocaleString()} rows`;
    $('rowsRange').value = String(diagram.visibleRows);
  }

  function renderRibbon() {
    const ribbon = $('tapeRibbon');
    ribbon.innerHTML = '';
    const n = sim.tokens();
    if (n === 0) {
      const empty = document.createElement('div');
      empty.className = 'empty-tape';
      empty.textContent = 'Empty tape — halt.';
      ribbon.appendChild(empty);
      return;
    }

    const limit = 120;
    const firstCount = n <= limit ? n : 60;
    const lastCount = n <= limit ? 0 : 60;

    function addCell(index, token, isHead) {
      const cell = document.createElement('div');
      const category = tokenCategory(token);
      cell.className = `token-chip cat-${category}` + (isHead ? ' head-token' : '');
      cell.title = `${formatToken(token)} · index ${index.toLocaleString()} · ${category}`;
      const idx = document.createElement('span');
      idx.className = 'chip-index';
      idx.textContent = `#${index.toLocaleString()}`;
      const val = document.createElement('span');
      val.className = 'chip-value';
      val.textContent = formatToken(token);
      cell.appendChild(idx);
      cell.appendChild(val);
      ribbon.appendChild(cell);
    }

    for (let i = 0; i < firstCount; i++) addCell(i, sim.tokenAt(i), i === 0);
    if (lastCount > 0) {
      const gap = document.createElement('div');
      gap.className = 'tape-gap';
      gap.textContent = `… ${(n - firstCount - lastCount).toLocaleString()} more tokens …`;
      ribbon.appendChild(gap);
      for (let i = n - lastCount; i < n; i++) addCell(i, sim.tokenAt(i), false);
    }
  }

  function refresh() {
    refreshMetrics();
    renderRibbon();
    diagram.render();
  }

  function loadTape(tokens, preset, label) {
    pause();
    currentPreset = preset || { id: 'custom', label: label || 'Custom tape', note: 'Custom tape loaded from the editor.' };
    sim = new ATSSimulator(tokens);
    diagram.setSimulator(sim);
    $('tapeInput').value = formatTape(tokens);
    $('presetNote').textContent = currentPreset.note || '';
    $('presetSelect').value = currentPreset.id === 'custom' ? '' : currentPreset.id;
    $('tapeError').textContent = '';
    refresh();
  }

  function loadPreset(id) {
    const preset = presetById(id);
    if (!preset) return;
    try {
      loadTape(parseTape(preset.tape), preset);
    } catch (err) {
      setStatus(`Preset error: ${err.message}`, 'halted');
    }
  }

  function applyEditor() {
    try {
      const tokens = parseTape($('tapeInput').value);
      loadTape(tokens, null, 'Custom tape');
    } catch (err) {
      $('tapeError').textContent = err.message;
      setStatus(`Tape parse error: ${err.message}`, 'halted');
    }
  }

  function stepOnce() {
    if (!sim) return;
    pause();
    if (sim.halted) {
      setStatus(`HALTED at step ${sim.steps.toLocaleString()} — reset to run again.`, 'halted');
      return;
    }
    sim.step();
    refresh();
  }

  function advanceBy(count) {
    if (!sim) return;
    pause();
    if (sim.halted) {
      setStatus(`HALTED at step ${sim.steps.toLocaleString()} — reset to run again.`, 'halted');
      return;
    }
    sim.advance(count);
    refresh();
  }

  function resetTape() {
    if (!sim) return;
    pause();
    const tokens = sim.initialTokens.slice();
    sim = new ATSSimulator(tokens);
    diagram.setSimulator(sim);
    $('tapeError').textContent = '';
    refresh();
  }

  function play() {
    if (!sim) return;
    if (sim.halted) {
      resetTape();
    }
    if (sim.proof === 'zero-free') {
      setStatus('This tape is already proved non-halting by the zero-free decider.', 'cycle');
      return;
    }
    running = true;
    $('btnRunPause').textContent = 'Pause';
    $('btnRunPause').classList.remove('btn-green');
    $('btnRunPause').classList.add('btn-rose');
    lastFrame = 0;
    accumulator = 0;
    setStatus('Running — the queue is being sampled into the space-time diagram.', 'running');
    rafId = requestAnimationFrame(loop);
  }

  function loop(ts) {
    if (!running || !sim) return;
    if (!lastFrame) lastFrame = ts;
    const dt = Math.min(0.12, (ts - lastFrame) / 1000);
    lastFrame = ts;
    const speed = Number($('speedSelect').value) || 1000;
    accumulator += dt * speed;
    let todo = Math.floor(accumulator);
    accumulator -= todo;
    if (todo > 0) {
      todo = Math.min(todo, 20000);
      sim.advance(todo);
      refresh();
      if (sim.halted || sim.proof === 'zero-free') {
        pause();
        refresh();
        return;
      }
    }
    if (running) rafId = requestAnimationFrame(loop);
  }

  function loadInitialDefaults() {
    const select = $('presetSelect');
    for (const preset of PRESETS) {
      const option = document.createElement('option');
      option.value = preset.id;
      option.textContent = preset.label;
      select.appendChild(option);
    }
    loadPreset('grove');
  }

  // Playback controls.
  $('btnRunPause').addEventListener('click', () => (running ? (pause(), refresh()) : play()));
  $('btnStep').addEventListener('click', stepOnce);
  $('btnStep100').addEventListener('click', () => advanceBy(100));
  $('btnStep10k').addEventListener('click', () => advanceBy(10000));
  $('btnReset').addEventListener('click', resetTape);
  $('btnApply').addEventListener('click', applyEditor);
  $('btnLoadPreset').addEventListener('click', () => loadPreset($('presetSelect').value));
  $('presetSelect').addEventListener('change', () => loadPreset($('presetSelect').value));
  $('viewMode').addEventListener('change', (event) => {
    diagram.setMode(event.target.value);
    refreshMetrics();
  });
  $('btnZoomIn').addEventListener('click', () => { diagram.zoomIn(); refreshMetrics(); });
  $('btnZoomOut').addEventListener('click', () => { diagram.zoomOut(); refreshMetrics(); });
  $('btnFit').addEventListener('click', () => { diagram.fitAll(); refreshMetrics(); });
  $('btnExport').addEventListener('click', () => {
    const a = document.createElement('a');
    a.download = `ats_grove_${sim ? sim.steps : 0}steps.png`;
    a.href = diagram.exportPNG();
    a.click();
  });
  $('rowsRange').addEventListener('input', (event) => {
    diagram.setVisibleRows(Number(event.target.value));
    refreshMetrics();
  });

  window.addEventListener('keydown', (event) => {
    if (document.activeElement && ['INPUT', 'SELECT', 'TEXTAREA', 'BUTTON'].includes(document.activeElement.tagName)) {
      if (document.activeElement.id === 'tapeInput' || document.activeElement.tagName === 'SELECT') return;
    }
    if (event.code === 'Space') {
      event.preventDefault();
      if (running) { pause(); refresh(); } else play();
    } else if (event.key === '.') {
      event.preventDefault();
      stepOnce();
    }
  });

  loadInitialDefaults();
})();
