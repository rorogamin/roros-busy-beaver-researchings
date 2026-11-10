/**
 * Interactive Space-Time Diagram Visualizer for Double Turing Machines (DTM).
 * Renders tape symbols (0..m-1), rule parity stripe along left gutter (t mod k),
 * head trajectory worldline, and halting marker with pan/zoom/PNG export.
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

  class DTMSpaceTimeCanvas {
    constructor(canvas) {
      this.canvas = canvas;
      this.ctx = canvas.getContext('2d');
      this.cellW = 8;
      this.cellH = 5;
      this.offsetX = 0;
      this.offsetY = 0;
      this.autoFollow = true;
      this.dragging = false;
      this.dragStartX = 0;
      this.dragStartY = 0;
      this.history = [];
      this.initTapeGrid();
      this._bindEvents();
    }

    initTapeGrid() {
      // Sparse row cache: step t -> Map(pos -> val) built lazily from history
      this.rows = [];
      this.builtUpTo = -1;
    }

    reset() {
      this.history = [];
      this.rows = [];
      this.builtUpTo = -1;
      this.offsetX = 0;
      this.offsetY = 0;
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
          this.dragStartX = e.clientX - this.offsetX;
          this.dragStartY = e.clientY - this.offsetY;
        }
      });
      window.addEventListener('mousemove', (e) => {
        if (!this.dragging) return;
        this.offsetX = e.clientX - this.dragStartX;
        this.offsetY = e.clientY - this.dragStartY;
        this.render();
      });
      window.addEventListener('mouseup', () => {
        this.dragging = false;
      });
      this.canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const factor = e.deltaY < 0 ? 1.15 : 0.87;
        this.cellW = Math.max(2, Math.min(28, this.cellW * factor));
        this.cellH = Math.max(1.5, Math.min(20, this.cellH * factor));
        this.render();
      }, { passive: false });
    }

    zoomIn() {
      this.cellW = Math.min(28, this.cellW * 1.25);
      this.cellH = Math.min(20, this.cellH * 1.25);
      this.render();
    }

    zoomOut() {
      this.cellW = Math.max(2, this.cellW * 0.8);
      this.cellH = Math.max(1.5, this.cellH * 0.8);
      this.render();
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

    render(sim) {
      if (sim) {
        this.syncHistory(sim.history);
      }
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

      if (this.autoFollow && sim) {
        this.offsetX = W / 2 - sim.head * this.cellW;
        const totalH = nSteps * this.cellH;
        this.offsetY = totalH > H - 24 * dpr ? (H - 20 * dpr - totalH) : 12 * dpr;
      }

      const cw = this.cellW;
      const ch = this.cellH;
      const gutterW = 10 * dpr;

      const tStart = Math.max(0, Math.floor(-this.offsetY / ch) - 1);
      const tEnd = Math.min(nSteps - 1, Math.ceil((H - this.offsetY) / ch) + 1);

      // Draw rows (cells + rule parity gutter)
      for (let t = tStart; t <= tEnd; t++) {
        const y = this.offsetY + t * ch;
        const h = this.history[t];
        const rowMap = this.rows[t];
        if (rowMap) {
          for (const [pos, val] of rowMap.entries()) {
            const x = this.offsetX + pos * cw;
            if (x + cw < gutterW || x > W) continue;
            ctx.fillStyle = SYMBOL_COLORS[val % SYMBOL_COLORS.length];
            ctx.fillRect(x, y, Math.max(1, cw - 0.5), Math.max(1, ch - 0.3));
          }
        }
        // Left gutter shows which rule activated at step t
        ctx.fillStyle = RULE_COLORS[h.ruleIdx % RULE_COLORS.length];
        ctx.fillRect(2 * dpr, y, gutterW - 3 * dpr, Math.max(1, ch - 0.3));
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

      // Head worldline overlay
      ctx.lineWidth = Math.max(1.2, 1.5 * dpr);
      ctx.beginPath();
      let started = false;
      for (let t = tStart; t <= tEnd; t++) {
        const h = this.history[t];
        const x = this.offsetX + (h.pos + 0.5) * cw;
        const y = this.offsetY + (t + 0.5) * ch;
        if (!started) { ctx.moveTo(x, y); started = true; }
        else ctx.lineTo(x, y);
      }
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.78)';
      ctx.stroke();

      // Halting marker or current head dot
      const last = this.history[nSteps - 1];
      const lx = this.offsetX + (last.nextPos + 0.5) * cw;
      const ly = this.offsetY + (nSteps - 0.5) * ch;
      ctx.beginPath();
      ctx.arc(lx, ly, Math.max(4, 4.5 * dpr), 0, Math.PI * 2);
      ctx.fillStyle = last.halted ? '#ff5c5c' : '#39ff14';
      ctx.fill();
    }

    exportPNG() {
      return this.canvas.toDataURL('image/png');
    }
  }

  global.DTMSpaceTimeCanvas = DTMSpaceTimeCanvas;
})(typeof window !== 'undefined' ? window : globalThis);
