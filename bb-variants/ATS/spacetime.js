/* Canvas space-time diagram for the Absorbing Tag System web studio. */
(function (global) {
  'use strict';

  const COLORS = {
    prim1: '#22c55e',
    prim0: '#64748b',
    fn1: 'rgba(56, 189, 248, 0.52)',
    fnzero: '#f59e0b',
    fnmix: '#f472b6',
    fnone: '#a78bfa',
  };

  const PRIORITY = {
    fnmix: 6,
    fnzero: 5,
    prim0: 4,
    prim1: 3,
    fnone: 2,
    fn1: 1,
  };

  const MODE_LABELS = {
    overview: 'whole tape (sampled)',
    head: 'head window',
    tail: 'tail window',
  };

  class ATSSpaceTime {
    constructor(canvas, readout) {
      this.canvas = canvas;
      this.ctx = canvas.getContext('2d');
      this.readout = readout;
      this.sim = null;
      this.mode = 'overview';
      this.visibleRows = 240;
      this.hoverRow = null;
      this._resizeObserver = null;
      this._bindEvents();
      if (global.ResizeObserver) {
        this._resizeObserver = new ResizeObserver(() => this.render());
        this._resizeObserver.observe(canvas.parentElement);
      }
    }

    setSimulator(sim) {
      this.sim = sim;
      this.hoverRow = null;
      this.render();
    }

    reset() {
      this.sim = null;
      this.hoverRow = null;
      this.render();
    }

    setMode(mode) {
      this.mode = MODE_LABELS[mode] ? mode : 'overview';
      this.render();
    }

    setVisibleRows(count) {
      this.visibleRows = Math.max(30, Math.min(1000, Math.floor(count)));
      this.render();
    }

    zoomIn() {
      this.setVisibleRows(Math.round(this.visibleRows * 0.7));
    }

    zoomOut() {
      this.setVisibleRows(Math.round(this.visibleRows * 1.4));
    }

    fitAll() {
      const n = this.sim && this.sim.history ? this.sim.history.length : 0;
      this.setVisibleRows(Math.max(30, n));
    }

    exportPNG() {
      this.render();
      return this.canvas.toDataURL('image/png');
    }

    _bindEvents() {
      this.canvas.addEventListener('mousemove', (event) => {
        const rect = this.canvas.getBoundingClientRect();
        const x = event.clientX - rect.left;
        const y = event.clientY - rect.top;
        const rows = this._visibleRows();
        const top = 18;
        const bottom = 24;
        const plotH = rect.height - top - bottom;
        if (!rows.length || x < 48 || x > rect.width - 8 || y < top || y > top + plotH) {
          this._setReadout(null);
          return;
        }
        const index = Math.min(rows.length - 1, Math.max(0, Math.floor(((y - top) / plotH) * rows.length)));
        this.hoverRow = rows[index];
        this._setReadout(this.hoverRow);
      });
      this.canvas.addEventListener('mouseleave', () => {
        this.hoverRow = null;
        this._setReadout(null);
      });
    }

    _visibleRows() {
      if (!this.sim || !this.sim.history) return [];
      const history = this.sim.history;
      const n = Math.min(this.visibleRows, history.length);
      return history.slice(Math.max(0, history.length - n));
    }

    _setReadout(row) {
      if (!this.readout) return;
      if (!row) {
        this.readout.classList.remove('visible');
        return;
      }
      this.readout.classList.add('visible');
      this.readout.textContent =
        `step ${row.step.toLocaleString()} · ${row.count.toLocaleString()} tokens · ` +
        `${row.length.toLocaleString()} length · ${row.zeros.toLocaleString()} zeros · ` +
        `${row.nonFn1.toLocaleString()} non-fn(1)`;
    }

    _category(source, isCategorySource) {
      return isCategorySource ? source : global.ATSCore.tokenCategory(source);
    }

    _sample(source, columns, isCategorySource) {
      if (!source || !source.length || columns <= 0) return [];
      const cells = [];
      if (source.length <= columns) {
        for (let i = 0; i < columns; i++) {
          cells.push(i < source.length ? this._category(source[i], isCategorySource) : null);
        }
        return cells;
      }
      for (let i = 0; i < columns; i++) {
        const from = Math.floor((i * source.length) / columns);
        const to = Math.max(from + 1, Math.floor(((i + 1) * source.length) / columns));
        let best = null;
        let bestPriority = -1;
        for (let j = from; j < to && j < source.length; j++) {
          const cat = this._category(source[j], isCategorySource);
          const priority = PRIORITY[cat] || 0;
          if (priority > bestPriority) {
            bestPriority = priority;
            best = cat;
          }
        }
        cells.push(best);
      }
      return cells;
    }

    _rowCells(row) {
      const maxColumns = Math.max(20, Math.min(360, Math.floor(this.canvas.clientWidth / 2.2)));
      if (this.mode === 'head') {
        const source = row.full ? row.full.slice(0, global.ATSCore.WINDOW) : row.head;
        const columns = Math.min(maxColumns, global.ATSCore.WINDOW);
        return { cells: this._sample(source, columns, false), columns };
      }
      if (this.mode === 'tail') {
        const source = row.full ? row.full.slice(-global.ATSCore.WINDOW) : row.tail;
        const columns = Math.min(maxColumns, global.ATSCore.WINDOW);
        return { cells: this._sample(source, columns, false), columns };
      }
      const source = row.overview || row.full || row.head || [];
      const columns = Math.min(maxColumns, source === row.overview ? global.ATSCore.OVERVIEW_SAMPLES : 512);
      return { cells: this._sample(source, columns, source === row.overview), columns };
    }

    render() {
      const canvas = this.canvas;
      if (!canvas) return;
      const rect = canvas.getBoundingClientRect();
      const dpr = global.devicePixelRatio || 1;
      const width = Math.max(320, Math.floor(rect.width));
      const height = Math.max(220, Math.floor(rect.height));
      canvas.width = Math.floor(width * dpr);
      canvas.height = Math.floor(height * dpr);
      const ctx = this.ctx;
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      ctx.fillStyle = '#060a12';
      ctx.fillRect(0, 0, width, height);

      const left = 52;
      const right = 10;
      const top = 18;
      const bottom = 24;
      const plotW = width - left - right;
      const plotH = height - top - bottom;
      const rows = this._visibleRows();

      ctx.fillStyle = 'rgba(148, 163, 184, 0.75)';
      ctx.font = '10px "JetBrains Mono", "Cascadia Code", monospace';
      ctx.textAlign = 'left';
      ctx.fillText('time ↓', 8, 12);

      if (!rows.length) {
        ctx.fillStyle = '#64748b';
        ctx.font = '13px Inter, "Segoe UI", sans-serif';
        ctx.textAlign = 'center';
        ctx.fillText('Load a tape, then Step or Run to draw its space-time diagram.', width / 2, height / 2);
        return;
      }

      const rowH = plotH / rows.length;
      const drawH = Math.max(1, rowH - 0.35);
      const maxColumns = Math.max(20, Math.min(360, Math.floor(plotW / 2.2)));
      const columnWidth = Math.min(plotW / maxColumns, 8);

      // Subtle time grid: every roughly 1/5 of the visible interval.
      ctx.strokeStyle = 'rgba(148, 163, 184, 0.10)';
      ctx.lineWidth = 1;
      const tickCount = 4;
      for (let i = 0; i <= tickCount; i++) {
        const rowIndex = Math.floor((i * (rows.length - 1)) / tickCount);
        const y = top + rowIndex * rowH;
        ctx.beginPath();
        ctx.moveTo(left, y);
        ctx.lineTo(width - right, y);
        ctx.stroke();
        ctx.fillStyle = 'rgba(148, 163, 184, 0.82)';
        ctx.font = '10px "JetBrains Mono", "Cascadia Code", monospace';
        ctx.textAlign = 'right';
        ctx.fillText(rows[rowIndex].step.toLocaleString(), left - 8, y + 3);
      }

      // Queue rows. Each row is sampled to a fixed number of columns so the
      // whole tape remains visible even when it grows to hundreds of thousands
      // of tokens.
      for (let i = 0; i < rows.length; i++) {
        const row = rows[i];
        const { cells, columns } = this._rowCells(row);
        const y = top + i * rowH;
        const cellW = plotW / columns;
        const drawW = Math.max(0.8, cellW - 0.12);
        for (let c = 0; c < cells.length; c++) {
          const color = COLORS[cells[c]];
          if (!color) continue;
          ctx.fillStyle = color;
          ctx.fillRect(left + c * cellW, y, drawW, drawH);
        }
        if (i === rows.length - 1) {
          ctx.strokeStyle = 'rgba(241, 245, 249, 0.7)';
          ctx.lineWidth = 1;
          ctx.strokeRect(left, y, plotW, Math.max(1, drawH));
        }
      }

      // Head is the first queue token. A small cyan tick makes the active end
      // of the queue visible without pretending ATS has a tape-cell head.
      if (this.mode !== 'tail') {
        ctx.fillStyle = 'rgba(0, 240, 255, 0.9)';
        ctx.fillRect(left - 2, top, 2, plotH);
      } else {
        ctx.fillStyle = 'rgba(244, 114, 182, 0.8)';
        ctx.fillRect(left + plotW - 1, top, 2, plotH);
      }

      ctx.fillStyle = 'rgba(148, 163, 184, 0.78)';
      ctx.font = '10px "JetBrains Mono", "Cascadia Code", monospace';
      ctx.textAlign = 'left';
      ctx.fillText(MODE_LABELS[this.mode] || this.mode, left, height - 7);
      ctx.textAlign = 'right';
      ctx.fillText(`latest: step ${rows[rows.length - 1].step.toLocaleString()}`, width - right, height - 7);
    }
  }

  global.ATSSpaceTime = ATSSpaceTime;
  global.ATS_COLORS = COLORS;
})(window);
