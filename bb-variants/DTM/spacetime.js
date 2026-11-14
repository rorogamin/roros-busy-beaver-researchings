/**
 * Interactive Space-Time Diagram Visualizer for Double Turing Machines (DTM).
 * Renders tape symbols (0..m-1), rule parity stripe along left gutter (t mod k),
 * head trajectory worldline, and halting marker with deep zoom/pan/fit/PNG export.
 */

(function (global) {
  'use strict';

  const SYMBOL_COLORS = [
    '#0b101b',
    '#00f0ff',
    '#ff5c5c',
    '#39ff14',
    '#ffb703',
    '#bf55ec',
    '#f472b6',
    '#38bdf8',
  ];

  const RULE_COLORS = [
    '#00f0ff', // Rule 1 (t % k == 0)
    '#bf55ec', // Rule 2 (t % k == 1)
    '#ffb703', // Rule 3 (t % k == 2)
    '#39ff14', // Rule 4
    '#ff5c5c', // Rule 5
  ];

  const BASE_CELL_W = 8;
  const BASE_CELL_H = 5;
  const MIN_SCALE = 0.002; // 0.016px x 0.010px -> fits 50,000+ steps vertically
  const MAX_SCALE = 6.0;   // 48px x 30px

  class DTMSpaceTimeCanvas {
    constructor(canvas) {
      this.canvas = canvas;
      this.ctx = canvas.getContext('2d');
      this.scale = 1.0;
      this.cellW = BASE_CELL_W;
      this.cellH = BASE_CELL_H;
      this.offsetX = 0;
      this.offsetY = 0;
      this.autoFollow = true;
      this.dragging = false;
      this.dragStartX = 0;
      this.dragStartY = 0;
      this.history = [];
      this.lastSim = null;
      this.initTapeGrid();
      this._bindEvents();
    }

    initTapeGrid() {
      this.rows = [];
      this.builtUpTo = -1;
    }

    reset() {
      this.history = [];
      this.lastSim = null;
      this.rows = [];
      this.builtUpTo = -1;
      this.offsetX = 0;
      this.offsetY = 0;
      this.autoFollow = true;
    }

    _setScale(nextScale) {
      this.scale = Math.max(MIN_SCALE, Math.min(MAX_SCALE, nextScale));
      this.cellW = BASE_CELL_W * this.scale;
      this.cellH = BASE_CELL_H * this.scale;
    }

    _zoomBy(factor, anchorX, anchorY) {
      const oldCw = this.cellW;
      const oldCh = this.cellH;
      this._setScale(this.scale * factor);
      if (!this.autoFollow) {
        const ax = anchorX !== undefined ? anchorX : this.canvas.width / 2;
        const ay = anchorY !== undefined ? anchorY : this.canvas.height / 2;
        this.offsetX = ax - (ax - this.offsetX) * (this.cellW / oldCw);
        this.offsetY = ay - (ay - this.offsetY) * (this.cellH / oldCh);
      }
      this.render();
    }

    syncHistory(history) {
      if (history.length < this.builtUpTo + 1) {
        this.rows = [];
        this.builtUpTo = -1;
      }
      this.history = history;
      let curTape = this.builtUpTo >= 0 ? new Map(this.rows[this.builtUpTo]) : new Map();
      for (let i = this.builtUpTo + 1; i < history.length; i++) {
        const h = history[i];
        if (!h.halted || h.write !== undefined) {
          if (h.write === 0) curTape.delete(h.pos);
          else curTape.set(h.pos, h.write);
        }
        this.rows.push(new Map(curTape));
        this.builtUpTo = i;
      }
    }

    _bindEvents() {
      this.canvas.addEventListener('mousedown', (e) => {
        if (e.button === 0) {
          this.dragging = true;
          this.autoFollow = false;
          const dpr = window.devicePixelRatio || 1;
          this.dragStartX = e.clientX * dpr - this.offsetX;
          this.dragStartY = e.clientY * dpr - this.offsetY;
        }
      });
      window.addEventListener('mousemove', (e) => {
        if (!this.dragging) return;
        const dpr = window.devicePixelRatio || 1;
        this.offsetX = e.clientX * dpr - this.dragStartX;
        this.offsetY = e.clientY * dpr - this.dragStartY;
        this.render();
      });
      window.addEventListener('mouseup', () => {
        this.dragging = false;
      });
      this.canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const rect = this.canvas.getBoundingClientRect();
        const dpr = window.devicePixelRatio || 1;
        const ax = (e.clientX - rect.left) * dpr;
        const ay = (e.clientY - rect.top) * dpr;
        const factor = e.deltaY < 0 ? 1.18 : 0.85;
        this._zoomBy(factor, ax, ay);
      }, { passive: false });
    }

    zoomIn() {
      this._zoomBy(1.33);
    }

    zoomOut() {
      this._zoomBy(0.72);
    }

    fitCenter(headPos, stepCount) {
      this.autoFollow = true;
      const w = this.canvas.width;
      const h = this.canvas.height;
      this.offsetX = w / 2 - headPos * this.cellW;
      const totalH = stepCount * this.cellH;
      this.offsetY = totalH > h - 30 ? (h - 24 - totalH) : 12;
      this.render();
    }

    fitAll() {
      const nSteps = this.history.length;
      if (nSteps === 0) {
        this._setScale(1.0);
        this.fitCenter(0, 0);
        return;
      }
      this.autoFollow = false;
      let minP = 0;
      let maxP = 0;
      for (let t = 0; t < nSteps; t++) {
        const p = this.history[t].pos;
        const np = this.history[t].nextPos;
        if (p < minP) minP = p;
        if (p > maxP) maxP = p;
        if (np < minP) minP = np;
        if (np > maxP) maxP = np;
      }
      const dpr = window.devicePixelRatio || 1;
      const W = this.canvas.width;
      const H = this.canvas.height;
      const gutterW = 14 * dpr;
      const pad = 16 * dpr;
      const spanX = Math.max(1, maxP - minP + 2);
      const scaleX = (W - gutterW - pad) / (spanX * BASE_CELL_W);
      const scaleY = (H - pad) / (nSteps * BASE_CELL_H);
      this._setScale(Math.min(scaleX, scaleY, 2.0));

      const midX = (minP + maxP + 1) / 2;
      this.offsetX = gutterW + (W - gutterW) / 2 - midX * this.cellW;
      this.offsetY = Math.max(8 * dpr, (H - nSteps * this.cellH) / 2);
      this.render();
    }

    render(sim) {
      if (sim) {
        this.lastSim = sim;
        this.syncHistory(sim.history);
      }
      const activeSim = sim || this.lastSim;
      const canvas = this.canvas;
      const rect = canvas.getBoundingClientRect();
      const dpr = window.devicePixelRatio || 1;
      if (canvas.width !== Math.floor(rect.width * dpr) || canvas.height !== Math.floor(rect.height * dpr)) {
        canvas.width = Math.max(300, Math.floor(rect.width * dpr));
        canvas.height = Math.max(200, Math.floor(rect.height * dpr));
      }
      const ctx = this.ctx;
      const W = canvas.width;
      const H = canvas.height;
      ctx.fillStyle = '#070a12';
      ctx.fillRect(0, 0, W, H);

      const nSteps = this.history.length;
      if (nSteps === 0) {
        ctx.fillStyle = '#64748b';
        ctx.font = `${13 * dpr}px Inter, sans-serif`;
        ctx.textAlign = 'center';
        ctx.fillText('Press Run or Step to visualize DTM Space-Time Diagram', W / 2, H / 2);
        return;
      }

      if (this.autoFollow && activeSim) {
        this.offsetX = W / 2 - activeSim.head * this.cellW;
        const totalH = nSteps * this.cellH;
        this.offsetY = totalH > H - 24 * dpr ? (H - 20 * dpr - totalH) : 12 * dpr;
      }

      const cw = this.cellW;
      const ch = this.cellH;
      const gutterW = 10 * dpr;

      const tStart = Math.max(0, Math.floor(-this.offsetY / ch) - 1);
      const tEnd = Math.min(nSteps - 1, Math.ceil((H - this.offsetY) / ch) + 1);
      const tStep = ch < 0.75 ? Math.max(1, Math.floor(0.75 / ch)) : 1;
      const drawW = cw >= 2.0 ? (cw - 0.5) : Math.max(1, cw);
      const drawH = tStep > 1 ? Math.max(1, ch * tStep) : (ch >= 1.5 ? ch - 0.3 : Math.max(1, ch));

      // Draw rows (cells + rule parity gutter)
      for (let t = tStart; t <= tEnd; t += tStep) {
        const y = this.offsetY + t * ch;
        const h = this.history[t];
        const rowMap = this.rows[t];
        if (rowMap) {
          for (const [pos, val] of rowMap.entries()) {
            const x = this.offsetX + pos * cw;
            if (x + drawW < gutterW || x > W) continue;
            ctx.fillStyle = SYMBOL_COLORS[val % SYMBOL_COLORS.length];
            ctx.fillRect(x, y, drawW, drawH);
          }
        }
        ctx.fillStyle = RULE_COLORS[h.ruleIdx % RULE_COLORS.length];
        ctx.fillRect(2 * dpr, y, gutterW - 3 * dpr, drawH);
      }

      // Origin x = 0 faint guide
      const zeroX = this.offsetX;
      if (zeroX > gutterW && zeroX < W) {
        ctx.strokeStyle = 'rgba(255,255,255,0.08)';
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(zeroX, 0);
        ctx.lineTo(zeroX, H);
        ctx.stroke();
      }

      // Head worldline overlay (fade smoothly when zoomed far out so colored tape stays visible)
      if (cw >= 0.3) {
        const alpha = Math.min(0.78, Math.max(0.12, cw * 0.42));
        ctx.lineWidth = Math.max(1.0, Math.min(1.5 * dpr, cw * 0.45));
        ctx.beginPath();
        let started = false;
        for (let t = tStart; t <= tEnd; t += tStep) {
          const h = this.history[t];
          const x = this.offsetX + (h.pos + 0.5) * cw;
          const y = this.offsetY + (t + 0.5) * ch;
          if (!started) { ctx.moveTo(x, y); started = true; }
          else ctx.lineTo(x, y);
        }
        if (tEnd >= tStart) {
          const hLast = this.history[tEnd];
          ctx.lineTo(this.offsetX + (hLast.pos + 0.5) * cw, this.offsetY + (tEnd + 0.5) * ch);
        }
        ctx.strokeStyle = `rgba(255, 255, 255, ${alpha.toFixed(2)})`;
        ctx.stroke();
      }

      // Halting marker or current head dot
      const last = this.history[nSteps - 1];
      const lx = this.offsetX + (last.nextPos + 0.5) * cw;
      const ly = this.offsetY + (nSteps - 0.5) * ch;
      ctx.beginPath();
      ctx.arc(lx, ly, Math.max(3, Math.min(4.5 * dpr, Math.max(2.5, cw * 1.2))), 0, Math.PI * 2);
      ctx.fillStyle = last.halted ? '#ff5c5c' : '#39ff14';
      ctx.fill();
    }

    exportPNG() {
      return this.canvas.toDataURL('image/png');
    }
  }

  global.DTMSpaceTimeCanvas = DTMSpaceTimeCanvas;
})(typeof window !== 'undefined' ? window : globalThis);
