/**
 * SpaceTimeDiagram - High Performance 2D Interactive Space-Time Canvas Visualizer
 *
 * Visualizes the 2D evolution of Catch-Em-Turing machines:
 * - X Axis: Tape Coordinate (Space)
 * - Y Axis: Time Step (Time, flowing downward or upward)
 * - Tape cell states (0 = background, 1 = energized cell)
 * - Agent Worldlines (continuous trajectory paths with glowing heads)
 * - Halting Collision Explosion Marker
 * - Smooth 60fps pan and zoom
 * - Scrubbing and hover inspection
 */

/**
 * Spacetime Block Grid Engine
 * Organizes spacetime (pos, t) into 64x64 blocks.
 * Enables frustum culling, instant incremental updates,
 * and Level-of-Detail (LOD) macro-block rendering when zoomed out.
 */
class SpacetimeBlockGrid {
  constructor(blockW = 64, blockH = 64) {
    this.blockW = blockW;
    this.blockH = blockH;
    this.blocks = new Map();
    this.processedStep = -1;
  }

  clear() {
    this.blocks.clear();
    this.processedStep = -1;
  }

  // Incrementally process new history steps
  updateFromHistory(history, maxT) {
    if (!history || history.length === 0) return;
    const startT = Math.max(0, this.processedStep + 1);
    if (startT > maxT) return;

    for (let t = startT; t <= maxT; t++) {
      const snap = history[t];
      if (snap && snap.writtenCells) {
        for (const wc of snap.writtenCells) {
          this.setCell(wc.pos, t, wc.val);
        }
      }
    }
    this.processedStep = maxT;
  }

  setCell(x, t, val) {
    const bx = Math.floor(x / this.blockW);
    const bt = Math.floor(t / this.blockH);
    const key = bx + ',' + bt;
    let blk = this.blocks.get(key);
    if (!blk) {
      blk = {
        bx,
        bt,
        count: 0,
        data: new Uint8Array(this.blockW * this.blockH),
        canvas: null,
        ctx: null,
        dirty: false
      };
      this.blocks.set(key, blk);
    }

    const lx = ((x % this.blockW) + this.blockW) % this.blockW;
    const lt = ((t % this.blockH) + this.blockH) % this.blockH;
    const idx = lt * this.blockW + lx;
    const oldVal = blk.data[idx];
    if (oldVal !== val) {
      blk.data[idx] = val;
      blk.count += (val === 1 ? 1 : -1);
      blk.dirty = true;
    }
  }

  getOrCreateBlockCanvas(blk, cellColor) {
    if (!blk.canvas && typeof document !== 'undefined') {
      blk.canvas = document.createElement('canvas');
      blk.canvas.width = this.blockW;
      blk.canvas.height = this.blockH;
      blk.ctx = blk.canvas.getContext('2d');
      blk.dirty = true;
    }

    if (blk.dirty && blk.ctx) {
      const imgData = blk.ctx.createImageData(this.blockW, this.blockH);
      const data = imgData.data;
      for (let i = 0; i < blk.data.length; i++) {
        if (blk.data[i] === 1) {
          const idx = i * 4;
          data[idx] = cellColor[0];
          data[idx + 1] = cellColor[1];
          data[idx + 2] = cellColor[2];
          data[idx + 3] = 240;
        }
      }
      blk.ctx.putImageData(imgData, 0, 0);
      blk.dirty = false;
    }
    return blk.canvas;
  }
}

class SpaceTimeDiagram {
  constructor(canvas, simulator, options = {}) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.sim = simulator;

    this.options = Object.assign({
      cellSize: 14,             // Base size of cell in pixels
      timeDirection: 'down',    // 'down' or 'up'
      showGrid: true,
      showWorldlines: true,
      showTapeCells: true,
      showAgentLabels: true,
      showCollisionEffect: true,
      autoCenterRunning: true,  // Automatically zoom out and center as agents run
      theme: 'cyberpunk'
    }, options);

    // Viewport transform
    this.scale = 1.0;
    this.scaleXMultiplier = 1.0; // Horizontal aspect stretch factor
    this.panX = 0;
    this.panY = 0;

    // Current scrubbed step in timeline (null means latest)
    this.scrubStep = null;

    // Interaction state
    this.isDragging = false;
    this.isRightDragging = false;
    this.dragStartX = 0;
    this.dragStartY = 0;
    this.hoverPos = null; // { x, t, canvasX, canvasY }

    // Block-based Spacetime Grid Engine (organizes cells into 64x64 blocks)
    this.blockGrid = new SpacetimeBlockGrid(64, 64);

    this.colorPalettes = {
      cyberpunk: {
        bg: '#0a0d14',
        grid: 'rgba(255, 255, 255, 0.04)',
        axis: 'rgba(255, 255, 255, 0.2)',
        cell0: '#0d111a',
        cell1: '#1b3a5c',
        cell1Glow: '#22d3ee',
        text: '#94a3b8',
        agents: [
          { main: '#00f0ff', glow: 'rgba(0, 240, 255, 0.4)', text: '#00f0ff' }, // Cyan
          { main: '#ff5c5c', glow: 'rgba(255, 92, 92, 0.4)', text: '#ff5c5c' }, // Coral
          { main: '#39ff14', glow: 'rgba(57, 255, 20, 0.4)', text: '#39ff14' }, // Neon Green
          { main: '#bf55ec', glow: 'rgba(191, 85, 236, 0.4)', text: '#bf55ec' },// Purple
          { main: '#ffb703', glow: 'rgba(255, 183, 3, 0.4)', text: '#ffb703' }, // Amber
          { main: '#ff007f', glow: 'rgba(255, 0, 127, 0.4)', text: '#ff007f' }  // Hot Pink
        ],
        collision: '#f59e0b',
        collisionGlow: 'rgba(245, 158, 11, 0.6)'
      },
      matrix: {
        bg: '#050c05',
        grid: 'rgba(0, 255, 70, 0.05)',
        axis: 'rgba(0, 255, 70, 0.25)',
        cell0: '#061309',
        cell1: '#0d381e',
        cell1Glow: '#00ff66',
        text: '#55b376',
        agents: [
          { main: '#00ff66', glow: 'rgba(0, 255, 102, 0.5)', text: '#00ff66' },
          { main: '#a8ff60', glow: 'rgba(168, 255, 96, 0.5)', text: '#a8ff60' },
          { main: '#ffff66', glow: 'rgba(255, 255, 102, 0.5)', text: '#ffff66' },
          { main: '#00e5ff', glow: 'rgba(0, 229, 255, 0.5)', text: '#00e5ff' }
        ],
        collision: '#ffff00',
        collisionGlow: 'rgba(255, 255, 0, 0.7)'
      },
      blueprint: {
        bg: '#0c1b33',
        grid: 'rgba(74, 144, 226, 0.12)',
        axis: 'rgba(74, 144, 226, 0.4)',
        cell0: '#102242',
        cell1: '#1e488f',
        cell1Glow: '#64b5f6',
        text: '#90caf9',
        agents: [
          { main: '#ffffff', glow: 'rgba(255, 255, 255, 0.5)', text: '#ffffff' },
          { main: '#ffd166', glow: 'rgba(255, 209, 102, 0.5)', text: '#ffd166' },
          { main: '#ef476f', glow: 'rgba(239, 71, 111, 0.5)', text: '#ef476f' },
          { main: '#06d6a0', glow: 'rgba(6, 214, 160, 0.5)', text: '#06d6a0' }
        ],
        collision: '#ff5252',
        collisionGlow: 'rgba(255, 82, 82, 0.6)'
      }
    };

    this.setupListeners();
    this.resize();
  }

  get colors() {
    return this.colorPalettes[this.options.theme] || this.colorPalettes.cyberpunk;
  }

  resize() {
    const dpr = window.devicePixelRatio || 1;
    const rect = this.canvas.getBoundingClientRect();
    this.width = rect.width;
    this.height = rect.height;

    this.canvas.width = Math.floor(rect.width * dpr);
    this.canvas.height = Math.floor(rect.height * dpr);
    this.ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    this.draw();
  }

  setupListeners() {
    window.addEventListener('resize', () => this.resize());

    // Disable default browser context menu on canvas so right click can be used to set time
    this.canvas.addEventListener('contextmenu', (e) => {
      e.preventDefault();
    });

    // Mouse down: Left click (0) = Pan, Right click (2) = Set Current Time
    this.canvas.addEventListener('mousedown', (e) => {
      if (e.button === 0) {
        this.isDragging = true;
        this.dragStartX = e.clientX - this.panX;
        this.dragStartY = e.clientY - this.panY;
        this.canvas.style.cursor = 'grabbing';
      } else if (e.button === 2) {
        e.preventDefault();
        this.isRightDragging = true;
        this.handleRightClickScrub(e);
      }
    });

    // Mouse move: handles left-click pan, right-click time scrub, and hover
    window.addEventListener('mousemove', (e) => {
      if (this.isDragging) {
        this.panX = e.clientX - this.dragStartX;
        this.panY = e.clientY - this.dragStartY;
        this.draw();
      } else if (this.isRightDragging) {
        this.handleRightClickScrub(e);
      } else {
        const rect = this.canvas.getBoundingClientRect();
        if (e.clientX >= rect.left && e.clientX <= rect.right &&
            e.clientY >= rect.top && e.clientY <= rect.bottom) {
          const mouseX = e.clientX - rect.left;
          const mouseY = e.clientY - rect.top;
          const spaceTimeCoord = this.canvasToSpaceTime(mouseX, mouseY);
          this.hoverPos = {
            canvasX: mouseX,
            canvasY: mouseY,
            x: spaceTimeCoord.x,
            t: spaceTimeCoord.t
          };

          if (this.onHover) {
            this.onHover(this.hoverPos);
          }
          this.draw();
        }
      }
    });

    // Mouse up: release pan or time scrub
    window.addEventListener('mouseup', (e) => {
      if (e.button === 0 && this.isDragging) {
        this.isDragging = false;
        this.canvas.style.cursor = 'grab';
      } else if (e.button === 2) {
        this.isRightDragging = false;
      }
    });

    this.canvas.addEventListener('mouseleave', () => {
      if (!this.isDragging && !this.isRightDragging) {
        this.hoverPos = null;
        if (this.onHover) this.onHover(null);
        this.draw();
      }
    });

    // Wheel for zooming centered exactly on mouse cursor
    this.canvas.addEventListener('wheel', (e) => {
      e.preventDefault();
      const rect = this.canvas.getBoundingClientRect();
      const mouseX = e.clientX - rect.left;
      const mouseY = e.clientY - rect.top;

      const zoomFactor = e.deltaY < 0 ? 1.15 : 0.87;
      this.zoomAroundPoint(mouseX, mouseY, zoomFactor);
    }, { passive: false });
  }

  handleRightClickScrub(e) {
    const rect = this.canvas.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;
    const st = this.canvasToSpaceTime(mouseX, mouseY);
    const clampedT = Math.max(0, Math.min(this.sim.stepCount, st.t));
    if (this.onScrub) {
      this.onScrub(clampedT);
    }
  }

  // Zoom centered around a specific canvas point (cx, cy) without lateral drift
  zoomAroundPoint(cx, cy, factor) {
    // Virtually unlimited zoom out (down to 1e-6) so massive runs are fully viewable
    const newScale = Math.min(Math.max(this.scale * factor, 1e-14), 100.0);
    const scaleRatio = newScale / this.scale;

    // Origin offsets matching spaceTimeToCanvas
    const ox = this.width / 2;
    const oy = this.options.timeDirection === 'down' ? 40 : (this.height - 40);

    // Keep the world point under (cx, cy) perfectly fixed
    this.panX = (cx - ox) - (cx - ox - this.panX) * scaleRatio;
    this.panY = (cy - oy) - (cy - oy - this.panY) * scaleRatio;
    this.scale = newScale;

    this.draw();
  }

  // Convert (tapePos x, step t) to Canvas (px, py)
  spaceTimeToCanvas(x, t) {
    const csT = this.options.cellSize * this.scale;
    const csX = csT * (this.scaleXMultiplier || 1.0);
    const px = this.width / 2 + this.panX + x * csX;
    let py;
    if (this.options.timeDirection === 'down') {
      py = 40 + this.panY + t * csT;
    } else {
      py = this.height - 40 + this.panY - t * csT;
    }
    return { px, py };
  }

  // Convert Canvas (px, py) to (tapePos x, step t)
  canvasToSpaceTime(px, py) {
    const csT = this.options.cellSize * this.scale;
    const csX = csT * (this.scaleXMultiplier || 1.0);
    const x = Math.round((px - (this.width / 2 + this.panX)) / csX);
    let t;
    if (this.options.timeDirection === 'down') {
      t = Math.round((py - (40 + this.panY)) / csT);
    } else {
      t = Math.round(((this.height - 40 + this.panY) - py) / csT);
    }
    return { x, t };
  }

  // Automatically fit diagram into current canvas bounds without arbitrary lower clamp
  fitToView() {
    const history = this.sim.history;
    if (!history || history.length === 0) return;

    let minX = 0, maxX = 0;
    const maxT = Math.max(1, this.sim.stepCount);

    for (let i = 0; i < history.length; i++) {
      const snap = history[i];
      if (!snap) continue;
      for (const ag of snap.agentStates) {
        if (ag.pos < minX) minX = ag.pos;
        if (ag.pos > maxX) maxX = ag.pos;
      }
      if (snap.intervals) {
        for (let k = 0; k < snap.intervals.length; k++) {
          const [s, e] = snap.intervals[k];
          if (s < minX) minX = s;
          if (e > maxX) maxX = e;
        }
      }
    }
    const tapeMetrics = this.sim.getTapeMetrics();
    if (tapeMetrics.onesCount > 0) {
      if (tapeMetrics.minPos < minX) minX = tapeMetrics.minPos;
      if (tapeMetrics.maxPos > maxX) maxX = tapeMetrics.maxPos;
    }

    // Add padding
    minX -= 3;
    maxX += 3;
    const spanX = Math.max(1, maxX - minX + 1);
    const spanT = Math.max(1, maxT + 4);

    const availW = this.width * 0.85;
    const availH = this.height * 0.85;

    // Target diagram width: auto-adjust scaleXMultiplier so space dimension occupies ~50% (half) of the canvas viewport
    const targetDiagramWidth = this.width * 0.50;
    const baseCell = this.options.cellSize;
    const scaleT = availH / (spanT * baseCell);

    // If slider is at default or user hasn't locked a custom width, adapt scaleXMultiplier to span ~50% width
    if (this.autoHalfWidth !== false) {
      const neededMultiplier = targetDiagramWidth / (spanX * baseCell * Math.max(scaleT, 1e-14));
      this.scaleXMultiplier = Math.max(1.0, neededMultiplier);
      const sliderWidthScale = document.getElementById('sliderWidthScale');
      const inputWidthScale = document.getElementById('inputWidthScale');
      if (sliderWidthScale) sliderWidthScale.value = Math.min(1000, this.scaleXMultiplier);
      if (inputWidthScale) inputWidthScale.value = `${Math.round(this.scaleXMultiplier * 10) / 10}x`;
    }

    const scaleX = availW / (spanX * baseCell * (this.scaleXMultiplier || 1.0));
    // Uncapped zoom-out limit so any step count (even 10,000+) fits cleanly
    this.scale = Math.min(Math.max(Math.min(scaleX, scaleT), 1e-14), 3.0);

    const csX = baseCell * this.scale * (this.scaleXMultiplier || 1.0);
    const midX = (minX + maxX) / 2;
    this.panX = -midX * csX;

    if (this.options.timeDirection === 'down') {
      this.panY = 20;
    } else {
      this.panY = -20;
    }

    this.draw();
  }

  // Automatically zooms out and centers the view on the agents as execution progresses
  autoCenterOnProgress() {
    if (!this.options.autoCenterRunning) return;
    const history = this.sim.history;
    const maxT = Math.max(1, this.sim.stepCount);
    if (!history || history.length === 0) return;

    let minX = 0, maxX = 2;
    for (const ag of this.sim.agents) {
      if (ag.pos < minX) minX = ag.pos;
      if (ag.pos > maxX) maxX = ag.pos;
    }
    if (this.cacheMinX < minX) minX = this.cacheMinX;
    if (this.cacheMaxX > maxX) maxX = this.cacheMaxX;

    minX -= 4;
    maxX += 4;
    const spanX = Math.max(1, maxX - minX + 1);
    const spanT = Math.max(1, maxT + 4);

    const availW = this.width * 0.85;
    const availH = this.height * 0.85;

    // Maintain diagram space dimension at approximately half the canvas window
    const targetDiagramWidth = this.width * 0.50;
    const baseCell = this.options.cellSize;
    const reqScaleT = availH / (spanT * baseCell);

    if (this.autoHalfWidth !== false) {
      const neededMultiplier = targetDiagramWidth / (spanX * baseCell * Math.max(reqScaleT, 1e-14));
      this.scaleXMultiplier = Math.max(1.0, neededMultiplier);
      const sliderWidthScale = document.getElementById('sliderWidthScale');
      const inputWidthScale = document.getElementById('inputWidthScale');
      if (sliderWidthScale) sliderWidthScale.value = Math.min(1000, this.scaleXMultiplier);
      if (inputWidthScale) inputWidthScale.value = `${Math.round(this.scaleXMultiplier * 10) / 10}x`;
    }

    const reqScaleX = availW / (spanX * baseCell * (this.scaleXMultiplier || 1.0));
    const targetScale = Math.min(reqScaleX, reqScaleT);

    // Zoom out dynamically if the run is exceeding the viewport
    if (targetScale < this.scale) {
      this.scale = targetScale;
    }

    const csX = baseCell * this.scale * (this.scaleXMultiplier || 1.0);
    const midX = (minX + maxX) / 2;
    this.panX = -midX * csX;

    if (this.options.timeDirection === 'down') {
      this.panY = 20;
    } else {
      this.panY = -20;
    }
  }

  invalidateTapeCache() {
    this.blockGrid.clear();
  }

  draw() {
    if (!this.ctx || !this.width || !this.height) return;
    const ctx = this.ctx;
    const palette = this.colors;
    const csT = this.options.cellSize * this.scale;
    const csX = csT * (this.scaleXMultiplier || 1.0);
    const cs = csT;

    // 1. Clear background
    ctx.fillStyle = palette.bg;
    ctx.fillRect(0, 0, this.width, this.height);

    const history = this.sim.history;
    const maxT = this.sim.stepCount;
    if (!history || history.length === 0) return;

    // Viewport visible bounds in space-time coordinates
    const topLeft = this.canvasToSpaceTime(0, 0);
    const bottomRight = this.canvasToSpaceTime(this.width, this.height);

    const visibleMinX = Math.min(topLeft.x, bottomRight.x) - 2;
    const visibleMaxX = Math.max(topLeft.x, bottomRight.x) + 2;
    const visibleMinT = Math.max(0, Math.min(topLeft.t, bottomRight.t) - 2);
    const visibleMaxT = Math.min(maxT, Math.max(topLeft.t, bottomRight.t) + 2);

    // 2. Draw Space Grid: only when cells are large enough to avoid clutter & lag
    if (this.options.showGrid && cs >= 6) {
      ctx.strokeStyle = palette.grid;
      ctx.lineWidth = 1;

      ctx.beginPath();
      for (let x = visibleMinX; x <= visibleMaxX; x++) {
        const { px } = this.spaceTimeToCanvas(x, 0);
        ctx.moveTo(px - cs / 2, 0);
        ctx.lineTo(px - cs / 2, this.height);
      }
      for (let t = visibleMinT; t <= visibleMaxT; t++) {
        const { py } = this.spaceTimeToCanvas(0, t);
        ctx.moveTo(0, py - cs / 2);
        ctx.lineTo(this.width, py - cs / 2);
      }
      ctx.stroke();
    }

    // 3. Draw Axis: T=0 and X=0 lines
    const axisX = this.spaceTimeToCanvas(0, 0).px - csX / 2;
    ctx.strokeStyle = palette.axis;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.moveTo(axisX, 0);
    ctx.lineTo(axisX, this.height);
    ctx.stroke();

    // 4. Render Tape Evolution as Continuous Horizontal Intervals/Bars
    if (this.options.showTapeCells) {
      const symGlowPalette = [
        '#94a3b8',           // 0: Slate
        palette.cell1Glow || '#22d3ee', // 1: Cyan
        '#e879f9',           // 2: Magenta
        '#fbbf24',           // 3: Amber
        '#34d399',           // 4: Emerald
        '#f472b6',           // 5: Pink
        '#facc15',           // 6: Yellow
        '#818cf8',           // 7: Indigo
        '#2dd4bf',           // 8: Teal
        '#fb7185'            // 9: Rose
      ];
      const symSolidPalette = [
        '#1e293b',
        palette.cell1 || '#1b3a5c',
        '#581c87',
        '#78350f',
        '#064e3b',
        '#831843',
        '#713f12',
        '#312e81',
        '#134e4a',
        '#881337'
      ];

      // Level of Detail (LOD) subsampling when zoomed out:
      // When zoomed out, multiple time steps project to the exact same vertical pixel row.
      // Skipping redundant sub-pixel rows dramatically speeds up rendering (10x-50x faster)
      // and creates an authentic smooth macro density look.
      const pixelTimeStep = Math.max(1, Math.floor(1 / Math.max(cs, 0.001)));
      const baseStride = this.sim.sampleStride || 1;
      const historyStepStride = Math.max(1, Math.floor(pixelTimeStep / baseStride));

      // Iterate over history snapshots intersecting visible time with dynamic LOD stride
      for (let i = 0; i < history.length; i += historyStepStride) {
        const snap = history[i];
        if (!snap || snap.step < visibleMinT) continue;
        if (snap.step > visibleMaxT) break;
        if (!snap.intervals || snap.intervals.length === 0) continue;

        const py = this.spaceTimeToCanvas(0, snap.step).py - cs / 2;
        const barHeight = Math.max(1, cs * baseStride * historyStepStride);

        // When zoomed out (csX < 2), merge adjacent sub-pixel intervals to cap fillRect calls
        const mergeSubpixels = csX < 2;
        let lastPx = -999999;
        let lastRight = -999999;
        let lastCol = null;

        for (let j = 0; j < snap.intervals.length; j++) {
          const [startPos, endPos, symVal = 1] = snap.intervals[j];
          if (endPos < visibleMinX || startPos > visibleMaxX) continue;

          const pIdx = Math.min(Math.max(symVal, 0), symGlowPalette.length - 1);
          const glowCol = symGlowPalette[pIdx];

          const px = this.spaceTimeToCanvas(startPos, snap.step).px - csX / 2;
          const numOnes = endPos - startPos + 1;
          const barWidth = Math.max(1, numOnes * csX);

          if (mergeSubpixels) {
            if (glowCol === lastCol && px <= lastRight + 1) {
              // Expand previous merged bar
              lastRight = Math.max(lastRight, px + barWidth);
              continue;
            } else {
              if (lastCol !== null) {
                ctx.fillStyle = lastCol;
                ctx.fillRect(lastPx, py, Math.max(1, lastRight - lastPx), barHeight);
              }
              lastPx = px;
              lastRight = px + barWidth;
              lastCol = glowCol;
            }
          } else {
            ctx.fillStyle = glowCol;
            ctx.fillRect(px, py, barWidth, barHeight);

            if (csX >= 8 && csT >= 8) {
              const solidCol = symSolidPalette[pIdx];
              ctx.fillStyle = solidCol;
              const drawStart = Math.max(startPos, visibleMinX);
              const drawEnd = Math.min(endPos, visibleMaxX);
              for (let x = drawStart; x <= drawEnd; x++) {
                const cellPx = this.spaceTimeToCanvas(x, snap.step).px - csX / 2;
                ctx.fillRect(cellPx + 1, py + 1, Math.max(1, csX - 2), Math.max(1, csT - 2));
              }
            }
          }
        }
        if (mergeSubpixels && lastCol !== null) {
          ctx.fillStyle = lastCol;
          ctx.fillRect(lastPx, py, Math.max(1, lastRight - lastPx), barHeight);
        }
      }
    }

    // 5. Draw Agent Worldlines (Trajectories)
    if (this.options.showWorldlines) {
      const numAgents = this.sim.agentCount;

      for (let a = 0; a < numAgents; a++) {
        const agentPalette = palette.agents[a % palette.agents.length];
        ctx.strokeStyle = agentPalette.main;
        ctx.lineWidth = Math.min(Math.max(cs * 0.35, 1.5), 6);
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';

        if (cs >= 4) {
          ctx.shadowColor = agentPalette.glow;
          ctx.shadowBlur = 6;
        } else {
          ctx.shadowBlur = 0;
        }

        ctx.beginPath();
        let started = false;

        // Adaptive trajectory point stride based on zoom:
        // More zoomed out = fewer polyline segments (faster, smoother), zoomed in = pixel-perfect detail
        const baseStride = this.sim.sampleStride || 1;
        const pixelTimeStep = Math.max(1, Math.floor(1 / Math.max(cs, 0.001)));
        const targetStepStride = Math.max(1, Math.floor(history.length / 4000));
        const trajStride = Math.max(1, Math.max(targetStepStride, Math.floor(pixelTimeStep / baseStride)));
        for (let i = 0; i < history.length; i += trajStride) {
          const snap = history[i];
          if (!snap) continue;
          const ag = snap.agentStates[a];
          if (!ag || !ag.active) continue;

          const { px, py } = this.spaceTimeToCanvas(ag.pos, snap.step);
          if (!started) {
            ctx.moveTo(px, py);
            started = true;
          } else {
            ctx.lineTo(px, py);
          }
        }
        ctx.stroke();
        ctx.shadowBlur = 0;
      }
    }

    // 6. Draw Collision Marker if halted
    if (this.sim.collisionEvent && this.options.showCollisionEffect) {
      const col = this.sim.collisionEvent;
      const { px, py } = this.spaceTimeToCanvas(col.pos, col.step);

      // Starburst animation effect
      const radius = Math.max(cs * 1.5, 12);
      const gradient = ctx.createRadialGradient(px, py, 2, px, py, radius * 2);
      gradient.addColorStop(0, '#ffffff');
      gradient.addColorStop(0.3, palette.collision);
      gradient.addColorStop(0.7, palette.collisionGlow);
      gradient.addColorStop(1, 'rgba(255, 165, 0, 0)');

      ctx.fillStyle = gradient;
      ctx.beginPath();
      ctx.arc(px, py, radius * 2, 0, Math.PI * 2);
      ctx.fill();

      // Sharp collision beacon
      ctx.fillStyle = '#ffffff';
      ctx.beginPath();
      ctx.arc(px, py, 4, 0, Math.PI * 2);
      ctx.fill();

      // Outer target ring
      ctx.strokeStyle = palette.collision;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(px, py, radius, 0, Math.PI * 2);
      ctx.stroke();

      // Collision badge text
      ctx.fillStyle = '#ffffff';
      ctx.font = 'bold 12px monospace';
      ctx.textAlign = 'left';
      ctx.textBaseline = 'middle';
      const labelText = `💥 COLLISION (t=${col.step}, x=${col.pos})`;
      ctx.fillText(labelText, px + radius + 8, py);
    }

    // 7. Active / Scrubbed Heads Marker
    const targetStep = this.scrubStep !== null ? this.scrubStep : maxT;
    const snap = this.sim.getSnapshotAtStep ? this.sim.getSnapshotAtStep(targetStep) : history[targetStep];
    if (snap) {
      // Draw scrub horizon line
      const { py } = this.spaceTimeToCanvas(0, targetStep);
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.35)';
      ctx.setLineDash([4, 4]);
      ctx.beginPath();
      ctx.moveTo(0, py);
      ctx.lineTo(this.width, py);
      ctx.stroke();
      ctx.setLineDash([]);

      // Draw agent heads at targetStep
      for (let a = 0; a < snap.agentStates.length; a++) {
        const ag = snap.agentStates[a];
        if (!ag.active) continue;
        const agentPalette = palette.agents[a % palette.agents.length];
        const { px, py } = this.spaceTimeToCanvas(ag.pos, targetStep);

        // Head beacon glow
        ctx.fillStyle = agentPalette.main;
        ctx.beginPath();
        ctx.arc(px, py, Math.max(cs * 0.45, 6), 0, Math.PI * 2);
        ctx.fill();

        ctx.strokeStyle = '#ffffff';
        ctx.lineWidth = 2;
        ctx.stroke();

        // Label agent head
        if (this.options.showAgentLabels) {
          ctx.font = 'bold 11px sans-serif';
          ctx.fillStyle = '#ffffff';
          ctx.textAlign = 'center';
          ctx.textBaseline = 'bottom';
          const stateLabel = String.fromCharCode(65 + ag.state);
          ctx.fillText(`A${ag.id}:${stateLabel}`, px, py - 8);
        }
      }
    }

    // 8. Hover Crosshair & Tooltip
    if (this.hoverPos) {
      const hp = this.hoverPos;
      if (hp.t >= 0 && hp.t <= maxT) {
        const { px, py } = this.spaceTimeToCanvas(hp.x, hp.t);

        // Crosshair highlight
        ctx.strokeStyle = 'rgba(255, 255, 255, 0.4)';
        ctx.lineWidth = 1;
        ctx.strokeRect(px - cs / 2, py - cs / 2, cs, cs);
      }
    }
  }

  // Export current diagram to PNG image data URL
  exportImageURL() {
    return this.canvas.toDataURL('image/png');
  }
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = SpaceTimeDiagram;
}
