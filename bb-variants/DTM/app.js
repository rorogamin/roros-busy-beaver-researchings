/* UI Controller for Double Turing Machine (DTM) Studio */
(function () {
  'use strict';

  const {
    parseRuleString,
    parseRuleOrder,
    formatRuleOrder,
    parseDTMSpec,
    formatDTMSpec,
    dtmSignature,
    toEquivalentStandardTM,
    DTMSimulator,
  } = window.DTMCore;

  const DEFAULT_PRESETS = [
    { id: 'dtm12', label: 'DTM(1,2) Exact (6 steps, Σ=4)', spec: '1RA1LA|1LA1RZ' },
    { id: 'dtm22', label: 'DTM(2,2) Exact (40 steps, Σ=5)', spec: '1RA0LA_1LA0RB|1LA1LB_1RZ1RB' },
    { id: 'dtm32', label: 'DTM(3,2) Champion (≥16,244 steps, Σ=73)', spec: '1RB1RA_1LC1RC_0RA0LB|1RZ1RB_1LB0RA_1LC0RB' },
    { id: 'dtm23', label: 'DTM(2,3) Champion (≥65,794 steps, Σ=355)', spec: '1RA0RA2LB_2RA0LB0LA|1LA2LB1RB_2RB1LA1RZ' },
    { id: 'dtm13', label: 'DTM(1,3) Exact (12 steps, Σ=6)', spec: '1RA2LA1RA|1LA2RA1RZ' },
    { id: 'dtm123', label: 'DTM(1,2,3) 3-Rule Exact (18 steps, Σ=5)', spec: '1RA0LA|0RA1RA|1LA1RZ' },
    { id: 'dtm223', label: 'DTM(2,2,3) 3-Rule Champion (≥26,336 steps, Σ=132)', spec: '0RB0RA_1LB1RB|0LB1RZ_1RB0LA|1RA1LB_1RB0RA' },
    { id: 'dtm2232_asym', label: 'DTM(2,2,3,2) Asymmetric (27 steps, State-OOB Halt)', spec: '1RA0LA_1LA1RB|1LA1RB_0RC0RA_1RC1RZ' },
  ];

  const sim = new DTMSimulator(DEFAULT_PRESETS[0].spec);
  const stCanvas = new window.DTMSpaceTimeCanvas(document.getElementById('spacetimeCanvas'));

  let mode = 'dtm'; // 'dtm' | 'multi' | 'asym'
  let running = false;
  let rafId = null;
  let lastFrameTs = 0;
  let stepAccumulator = 0;
  let lastServerDiscovery = '';
  let lastServerHoldout = '';

  const el = (id) => document.getElementById(id);

  function populatePresets(list) {
    const sel = el('presetSelect');
    sel.innerHTML = '';
    for (const item of list) {
      const opt = document.createElement('option');
      opt.value = item.spec;
      opt.textContent = item.label;
      sel.appendChild(opt);
    }
  }

  function updateModeControls() {
    document.querySelectorAll('.mode-tab-btn').forEach((btn) => {
      btn.classList.toggle('active', btn.dataset.mode === mode);
    });
    el('groupA').style.display = (mode === 'multi' || mode === 'order') ? 'flex' : 'none';
    el('groupOrder').style.display = mode === 'order' ? 'flex' : 'none';
    el('groupAsymA').style.display = mode === 'asym' ? 'flex' : 'none';
    el('groupAsymB').style.display = mode === 'asym' ? 'flex' : 'none';
  }

  function syncInputsFromSim() {
    el('specInput').value = sim.getSpec();
    const r0 = sim.rules[0];
    el('dimN').value = r0.states;
    el('dimM').value = r0.symbols;
    el('dimRules').value = sim.rules.length;
    if (sim.rules.order && sim.rules.order.length) {
      el('dimOrder').value = formatRuleOrder(sim.rules.order);
    }
    if (sim.rules.length === 2) {
      el('dimA2').value = sim.rules[1].states;
      el('dimB2').value = sim.rules[1].symbols;
    }
  }

  function renderRuleTables() {
    const container = el('ruleTablesContainer');
    container.innerHTML = '';
    const activeRule = sim.halted ? -1 : sim.activeRuleIndex();
    const curSym = sim.halted ? -1 : sim.readCell(sim.head);
    const curSt = sim.halted ? -1 : sim.state;

    sim.rules.forEach((rule, rIdx) => {
      const card = document.createElement('div');
      card.className = 'rule-table-card' + (rIdx === activeRule ? ' active-rule' : '');

      const title = document.createElement('div');
      title.className = 'rule-table-title';
      const tag = (sim.rules.order && sim.rules.order.length)
        ? `scheduled in {${formatRuleOrder(sim.rules.order)}}`
        : `t mod ${sim.rules.length} == ${rIdx}`;
      title.innerHTML = `<span>Rule ${rIdx + 1} (${tag})</span>` +
        `<span style="color:var(--text-dim)">${rule.states} states &times; ${rule.symbols} sym</span>`;
      card.appendChild(title);

      const tbl = document.createElement('table');
      tbl.className = 'trans-table';
      const thead = document.createElement('thead');
      let hrow = '<tr><th>State</th>';
      for (let y = 0; y < rule.symbols; y++) hrow += `<th>Sym ${y}</th>`;
      hrow += '</tr>';
      thead.innerHTML = hrow;
      tbl.appendChild(thead);

      const tbody = document.createElement('tbody');
      for (let s = 0; s < rule.states; s++) {
        const trEl = document.createElement('tr');
        const th = document.createElement('th');
        th.textContent = String.fromCharCode(65 + s);
        trEl.appendChild(th);
        for (let y = 0; y < rule.symbols; y++) {
          const td = document.createElement('td');
          if (rIdx === activeRule && s === curSt && y === curSym) {
            td.classList.add('trans-cell-active');
          }
          const inp = document.createElement('input');
          inp.className = 'trans-input';
          const tr = rule.table[s][y];
          inp.value = !tr ? '---' : `${tr.write}${tr.dir > 0 ? 'R' : 'L'}${tr.nextState < 0 ? 'Z' : String.fromCharCode(65 + tr.nextState)}`;
          inp.maxLength = 3;
          inp.addEventListener('change', () => {
            const val = inp.value.trim().toUpperCase();
            try {
              const parsed = window.DTMCore.parseRuleString(val.length === 3 ? val : '---');
              if (val === '---') {
                sim.rules[rIdx].table[s][y] = null;
              } else {
                const w = parseInt(val[0], 10);
                const d = val[1] === 'R' ? 1 : (val[1] === 'L' ? -1 : 0);
                const nx = (val[2] === 'Z' || val[2] === 'H') ? -1 : (val.charCodeAt(2) - 65);
                if (Number.isNaN(w) || !d || nx < -1) throw new Error('Bad token');
                sim.rules[rIdx].table[s][y] = { write: w, dir: d, nextState: nx };
              }
              pause();
              sim.reset();
              stCanvas.reset();
              syncInputsFromSim();
              refreshAll();
            } catch (_e) {
              renderRuleTables();
            }
          });
          td.appendChild(inp);
          trEl.appendChild(td);
        }
        tbody.appendChild(trEl);
      }
      tbl.appendChild(tbody);
      card.appendChild(tbl);
      container.appendChild(card);
    });
  }

  function renderTapeRibbon() {
    const ribbon = el('tapeRibbon');
    ribbon.innerHTML = '';
    const radius = 14;
    for (let pos = sim.head - radius; pos <= sim.head + radius; pos++) {
      const cell = document.createElement('div');
      cell.className = 'tape-cell' + (pos === sim.head ? ' head' : '');
      const val = sim.readCell(pos);
      cell.innerHTML = `<div class="idx">${pos}</div><div class="val" style="color:${val ? '#00f0ff' : '#475569'}">${val}</div>`;
      ribbon.appendChild(cell);
    }
    el('tapeSpanLabel').textContent = `head = ${sim.head} | span = [${sim.minPos}, ${sim.maxPos}]`;
  }

  function refreshAll() {
    const k = sim.rules.length;
    const ar = sim.activeRuleIndex();
    el('metricStepCount').textContent = sim.steps.toLocaleString();
    el('metricActiveRule').textContent = sim.halted
      ? 'HALTED'
      : (sim.rules.order && sim.rules.order.length
        ? `Rule ${ar + 1} (ord[${sim.activeScheduleIndex()}]=r${ar + 1})`
        : `Rule ${ar + 1} (t%${k}=${ar})`);
    el('metricState').textContent = sim.halted ? 'Z' : String.fromCharCode(65 + sim.state);
    el('metricScore').textContent = sim.nonZeros.toLocaleString();
    el('metricSpan').textContent = `${sim.head} [${sim.minPos}..${sim.maxPos}]`;
    el('metricSignature').textContent = sim.getSignature();

    const badge = el('statusBadge');
    if (sim.halted) {
      badge.className = 'status-badge status-halted';
      badge.textContent = `${sim.haltReason} (Total: ${sim.steps.toLocaleString()} steps, Score: ${sim.nonZeros})`;
    } else if (running) {
      badge.className = 'status-badge status-running';
      badge.textContent = `Running step ${sim.steps.toLocaleString()} — Rule ${sim.activeRuleIndex() + 1}, State ${String.fromCharCode(65 + sim.state)}`;
    } else {
      badge.className = 'status-badge';
      badge.textContent = sim.steps === 0 ? 'Ready — press Run, Step, or Server Sim' : `Paused at step ${sim.steps.toLocaleString()}`;
    }

    const eq = toEquivalentStandardTM(sim.rules);
    if (eq) {
      el('equivCard').style.display = 'block';
      el('equivBox').textContent = eq;
    } else {
      el('equivCard').style.display = 'none';
    }

    renderTapeRibbon();
    renderRuleTables();
    stCanvas.render(sim);
  }

  function loop(ts) {
    if (!running) return;
    if (!lastFrameTs) lastFrameTs = ts;
    const dt = Math.min(0.1, (ts - lastFrameTs) / 1000);
    lastFrameTs = ts;
    const speed = parseInt(el('speedSelect').value, 10) || 200;
    stepAccumulator += dt * speed;
    const todo = Math.floor(stepAccumulator);
    if (todo > 0) {
      stepAccumulator -= todo;
      sim.runSteps(Math.min(todo, 5000), true);
      if (sim.halted) pause();
      refreshAll();
    }
    if (running) rafId = requestAnimationFrame(loop);
  }

  function play() {
    if (sim.halted) {
      sim.reset();
      stCanvas.reset();
    }
    running = true;
    el('btnRunPause').textContent = 'Pause';
    lastFrameTs = 0;
    stepAccumulator = 0;
    rafId = requestAnimationFrame(loop);
  }

  function pause() {
    running = false;
    el('btnRunPause').textContent = 'Run';
    if (rafId) cancelAnimationFrame(rafId);
    rafId = null;
  }

  function loadMachineSpec(spec) {
    try {
      pause();
      sim.loadSpec(spec);
      stCanvas.reset();
      const k = sim.rules.length;
      if (sim.rules.order && sim.rules.order.length) mode = 'order';
      else if (k !== 2) mode = 'multi';
      else if (sim.rules[0].states !== sim.rules[1].states || sim.rules[0].symbols !== sim.rules[1].symbols) mode = 'asym';
      else mode = 'dtm';
      updateModeControls();
      syncInputsFromSim();
      refreshAll();
    } catch (err) {
      el('statusBadge').className = 'status-badge status-halted';
      el('statusBadge').textContent = `Spec Error: ${err.message}`;
    }
  }

  function makeRandomSpec() {
    const n = Math.max(1, Math.min(8, parseInt(el('dimN').value, 10) || 2));
    const m = Math.max(2, Math.min(6, parseInt(el('dimM').value, 10) || 2));
    let rules = (mode === 'multi' || mode === 'order') ? Math.max(1, Math.min(10, parseInt(el('dimRules').value, 10) || 3)) : 2;
    let ord = null;
    if (mode === 'order') {
      try {
        ord = parseRuleOrder(el('dimOrder').value || 'r1r2r3r2r1r2r2');
        const maxR = Math.max(...ord) + 1;
        if (maxR > rules) rules = maxR;
      } catch (_e) {
        ord = [0, 1, 2, 1, 0, 1, 1];
        if (rules < 3) rules = 3;
      }
    }
    const a2 = mode === 'asym' ? Math.max(1, Math.min(8, parseInt(el('dimA2').value, 10) || n)) : n;
    const b2 = mode === 'asym' ? Math.max(2, Math.min(6, parseInt(el('dimB2').value, 10) || m)) : m;

    const parts = [];
    for (let r = 0; r < rules; r++) {
      const rs = r === 1 && mode === 'asym' ? a2 : n;
      const rm = r === 1 && mode === 'asym' ? b2 : m;
      const blks = [];
      for (let s = 0; s < rs; s++) {
        let blk = '';
        for (let y = 0; y < rm; y++) {
          const w = Math.floor(Math.random() * rm);
          const d = (r === 0 && s === 0 && y === 0) ? 'R' : (Math.random() < 0.5 ? 'L' : 'R');
          const nx = String.fromCharCode(65 + Math.floor(Math.random() * rs));
          blk += `${w}${d}${nx}`;
        }
        blks.push(blk);
      }
      parts.push(blks.join('_'));
    }
    const hr = Math.floor(Math.random() * rules);
    const rs = hr === 1 && mode === 'asym' ? a2 : n;
    const rm = hr === 1 && mode === 'asym' ? b2 : m;
    const hs = Math.floor(Math.random() * rs);
    const hy = Math.floor(Math.random() * rm);
    const blks = parts[hr].split('_');
    const b = blks[hs];
    blks[hs] = b.slice(0, 3 * hy) + '1RZ' + b.slice(3 * hy + 3);
    parts[hr] = blks.join('_');
    const base = parts.join('|');
    return ord ? `${base}{${formatRuleOrder(ord)}}` : base;
  }

  async function checkServerHealth() {
    try {
      const resp = await fetch('/api/health');
      const data = await resp.json();
      el('serverBadge').textContent = data.native_c
        ? `Server online (Native C + ${data.cpu_count} CPUs)`
        : `Server online (Python fallback)`;
      el('serverBadge').style.color = '#39ff14';
    } catch (_e) {
      el('serverBadge').textContent = 'Offline static mode';
      el('serverBadge').style.color = '#ffb703';
    }
    try {
      const resp = await fetch('/api/champions');
      if (resp.ok) {
        const data = await resp.json();
        if (Array.isArray(data.presets) && data.presets.length) {
          populatePresets(data.presets);
          loadMachineSpec(data.presets[0].spec);
        }
      }
    } catch (_e) {
      // Keep default presets in static offline mode
    }
  }

  function parseStepCap(raw, fallback = 10000000) {
    const s = String(raw || '').trim().replace(/[,\s_]+/g, '').toLowerCase();
    if (!s) return fallback;
    const m = s.match(/^(\d+(?:\.\d+)?(?:e[+-]?\d+)?)(k|m|b)?$/);
    if (!m) return null;
    let val = Number(m[1]);
    if (!Number.isFinite(val)) return null;
    if (m[2] === 'k') val *= 1e3;
    else if (m[2] === 'm') val *= 1e6;
    else if (m[2] === 'b') val *= 1e9;
    const n = Math.floor(val);
    return (n >= 1 && n <= 10000000000) ? n : null;
  }

  async function runServerSim() {
    const cap = parseStepCap(el('fastSimCap') ? el('fastSimCap').value : '10M');
    if (!cap) {
      el('serverOutput').textContent = 'Invalid Fast Sim Cap (enter e.g. 50000, 10M, 100M, 1B, up to 10B).';
      return;
    }
    el('serverOutput').textContent = `Running native C server simulation (${cap.toLocaleString()} step cap)...`;
    try {
      const resp = await fetch('/api/simulate', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ spec: sim.getSpec(), cap, slice_rad: 30 }),
      });
      const data = await resp.json();
      if (data.error) throw new Error(data.error);
      el('serverOutput').textContent =
        `[${data.engine}] ${data.signature}\n` +
        `Result: ${data.halted ? 'HALTED' : (data.cycle_type ? 'PROVEN NON-HALTING CYCLE' : 'HOLDOUT (step limit)')}\n` +
        `Reason: ${data.halt_reason}\n` +
        `Steps: ${Number(data.steps).toLocaleString()} | Score: ${data.score} | Span: [${data.min_pos}, ${data.max_pos}] | Time: ${data.elapsed_ms} ms`;
    } catch (err) {
      el('serverOutput').textContent = `Server error: ${err.message}`;
    }
  }

  async function runServerHunt(useMutate) {
    const n = parseInt(el('dimN').value, 10) || 2;
    const m = parseInt(el('dimM').value, 10) || 2;
    const rules = (mode === 'multi' || mode === 'order') ? (parseInt(el('dimRules').value, 10) || 3) : 2;
    const order = mode === 'order'
      ? (el('dimOrder').value || '').trim()
      : (sim.rules.order ? formatRuleOrder(sim.rules.order) : '');
    const a = mode === 'asym' ? (parseInt(el('dimA2').value, 10) || 0) : 0;
    const b = mode === 'asym' ? (parseInt(el('dimB2').value, 10) || 0) : 0;

    el('serverOutput').textContent = useMutate
      ? 'Running 1.5s server mutation hunt from current machine...'
      : `Running 1.5s server random search in ${sim.getSignature()}...`;
    try {
      const resp = await fetch('/api/search', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          n, m, rules, order, a, b,
          cap: 500000,
          budget_ms: 1500,
          mutate_spec: useMutate ? sim.getSpec() : '',
        }),
      });
      const data = await resp.json();
      if (data.error) throw new Error(data.error);
      lastServerDiscovery = data.best_spec || '';
      lastServerHoldout = data.holdout_spec || '';
      el('loadBestRow').style.display = (lastServerDiscovery || lastServerHoldout) ? 'flex' : 'none';
      el('btnLoadBest').style.display = lastServerDiscovery ? 'inline-block' : 'none';
      el('btnLoadHoldout').style.display = lastServerHoldout ? 'inline-block' : 'none';
      el('serverOutput').textContent =
        `[${data.engine}] Tested: ${Number(data.tested).toLocaleString()} | Halted: ${Number(data.halted).toLocaleString()} | Holdouts: ${Number(data.holdouts).toLocaleString()} (${data.elapsed_ms} ms)\n` +
        `Best Halted: ${Number(data.best_steps).toLocaleString()} steps (score=${data.best_score})\n${data.best_spec || '(none)'}` +
        (lastServerHoldout ? `\nTop Holdout: ${lastServerHoldout}` : '');
    } catch (err) {
      el('serverOutput').textContent = `Server error: ${err.message}`;
    }
  }

  // Wire events
  populatePresets(DEFAULT_PRESETS);
  document.querySelectorAll('.mode-tab-btn').forEach((btn) => {
    btn.addEventListener('click', () => {
      mode = btn.dataset.mode;
      updateModeControls();
    });
  });
  el('presetSelect').addEventListener('change', (e) => loadMachineSpec(e.target.value));
  el('btnRunPause').addEventListener('click', () => (running ? pause() : play()));
  el('btnStep').addEventListener('click', () => { pause(); sim.step(true); refreshAll(); });
  el('btnStep100').addEventListener('click', () => { pause(); sim.runSteps(100, true); refreshAll(); });
  el('btnReset').addEventListener('click', () => { pause(); sim.reset(); stCanvas.reset(); refreshAll(); });
  el('btnApplySpec').addEventListener('click', () => loadMachineSpec(el('specInput').value));
  el('btnRandomize').addEventListener('click', () => loadMachineSpec(makeRandomSpec()));
  el('btnMutate').addEventListener('click', () => {
    const r = Math.floor(Math.random() * sim.rules.length);
    const rl = sim.rules[r];
    const s = Math.floor(Math.random() * rl.states);
    const y = Math.floor(Math.random() * rl.symbols);
    rl.table[s][y] = Math.random() < 0.1
      ? { write: 1, dir: 1, nextState: -1 }
      : { write: Math.floor(Math.random() * rl.symbols), dir: Math.random() < 0.5 ? -1 : 1, nextState: Math.floor(Math.random() * rl.states) };
    pause(); sim.reset(); stCanvas.reset(); syncInputsFromSim(); refreshAll();
  });
  el('btnResize').addEventListener('click', () => loadMachineSpec(makeRandomSpec()));
  el('btnZoomIn').addEventListener('click', () => stCanvas.zoomIn());
  el('btnZoomOut').addEventListener('click', () => stCanvas.zoomOut());
  el('btnFitAll').addEventListener('click', () => stCanvas.fitAll());
  el('btnFitCenter').addEventListener('click', () => stCanvas.fitCenter(sim.head, sim.history.length));
  el('btnExportPng').addEventListener('click', () => {
    const a = document.createElement('a');
    a.download = `dtm_${sim.steps}steps.png`;
    a.href = stCanvas.exportPNG();
    a.click();
  });
  el('btnServerSim').addEventListener('click', runServerSim);
  el('btnServerMutate').addEventListener('click', () => runServerHunt(true));
  el('btnServerSearch').addEventListener('click', () => runServerHunt(false));
  el('btnLoadBest').addEventListener('click', () => { if (lastServerDiscovery) loadMachineSpec(lastServerDiscovery); });
  el('btnLoadHoldout').addEventListener('click', () => { if (lastServerHoldout) loadMachineSpec(lastServerHoldout); });

  window.addEventListener('keydown', (e) => {
    if (document.activeElement && ['INPUT', 'SELECT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;
    if (e.code === 'Space') { e.preventDefault(); running ? pause() : play(); }
    else if (e.key === '.') { pause(); sim.step(true); refreshAll(); }
    else if (e.key === 'r' || e.key === 'R') { loadMachineSpec(makeRandomSpec()); }
  });

  updateModeControls();
  syncInputsFromSim();
  refreshAll();
  checkServerHealth();
})();
