/**
 * 1D Tape Visualizer (Tape Ribbon)
 * Renders the physical tape cells with moving agent heads,
 * read/write indicator badges, and center-on-agent navigation.
 */

class Tape1DVisualizer {
  constructor(container, simulator) {
    this.container = container;
    this.sim = simulator;
    this.centerPos = 1; // Default center between 0 and 2
    this.cellWidth = 44;
    this.renderRange = 15; // Cells to show on each side

    this.agentColors = [
      '#00f0ff', // Agent 1: Cyan
      '#ff5c5c', // Agent 2: Coral
      '#39ff14', // Agent 3: Neon Green
      '#bf55ec', // Agent 4: Purple
      '#ffb703', // Agent 5: Amber
      '#ff007f'  // Agent 6: Pink
    ];

    this.initDOM();
  }

  initDOM() {
    this.container.innerHTML = `
      <div class="tape-controls-bar">
        <div class="tape-nav-btn" id="btnTapeLeft" title="Scroll Tape Left">◀</div>
        <div class="tape-nav-btn" id="btnCenterAgents" title="Center Tape on Agents">🎯 Center</div>
        <div class="tape-nav-btn" id="btnTapeRight" title="Scroll Tape Right">▶</div>
      </div>
      <div class="tape-track-wrapper">
        <div class="tape-track" id="tapeTrack"></div>
      </div>
    `;

    this.trackEl = this.container.querySelector('#tapeTrack');

    this.container.querySelector('#btnTapeLeft').addEventListener('click', () => {
      this.centerPos -= 4;
      this.render();
    });
    this.container.querySelector('#btnTapeRight').addEventListener('click', () => {
      this.centerPos += 4;
      this.render();
    });
    this.container.querySelector('#btnCenterAgents').addEventListener('click', () => {
      this.autoCenter();
    });
  }

  autoCenter() {
    const active = this.sim.agents.filter(a => a.active);
    if (active.length > 0) {
      const sum = active.reduce((acc, a) => acc + a.pos, 0);
      this.centerPos = Math.round(sum / active.length);
      this.render();
    }
  }

  render(currentStepSnap = null) {
    if (!this.trackEl) return;

    // Use current snapshot if scrubbing, else simulator's current state
    let agentPositions = [];
    if (currentStepSnap) {
      agentPositions = currentStepSnap.agentStates;
    } else {
      agentPositions = this.sim.agents.map(a => ({ id: a.id, pos: a.pos, state: a.state, active: a.active }));
    }

    const minPos = this.centerPos - this.renderRange;
    const maxPos = this.centerPos + this.renderRange;

    // Build agent map by pos
    const agentMap = new Map();
    for (const ag of agentPositions) {
      if (!ag.active) continue;
      if (!agentMap.has(ag.pos)) agentMap.set(ag.pos, []);
      agentMap.get(ag.pos).push(ag);
    }

    let html = '';
    for (let pos = minPos; pos <= maxPos; pos++) {
      let val = 0;
      if (currentStepSnap && currentStepSnap.intervals) {
        val = currentStepSnap.intervals.some(([s, e]) => pos >= s && pos <= e) ? 1 : 0;
      } else {
        val = this.sim.tape.get(pos) || 0;
      }
      const agentsHere = agentMap.get(pos) || [];
      const isZeroPos = pos === 0;

      let headsHtml = '';
      if (agentsHere.length > 0) {
        headsHtml = '<div class="tape-heads-container">';
        for (const ag of agentsHere) {
          const color = this.agentColors[(ag.id - 1) % this.agentColors.length];
          const stateChar = String.fromCharCode(65 + ag.state);
          headsHtml += `
            <div class="tape-agent-head" style="border-color: ${color}; color: ${color};" title="Agent ${ag.id} | State ${stateChar}">
              <span class="head-agent-tag">A${ag.id}</span>
              <span class="head-state-tag">${stateChar}</span>
            </div>
          `;
        }
        headsHtml += '</div>';
      }

      let cellClass = 'cell-zero';
      if (val === 1) cellClass = 'cell-one';
      else if (val > 1) cellClass = `cell-sym-${Math.min(val, 9)}`;

      html += `
        <div class="tape-cell ${cellClass} ${isZeroPos ? 'cell-origin' : ''}" data-pos="${pos}">
          <div class="tape-cell-pos">${pos}</div>
          <div class="tape-cell-val">${val}</div>
          ${headsHtml}
        </div>
      `;
    }

    this.trackEl.innerHTML = html;
  }
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = Tape1DVisualizer;
}
