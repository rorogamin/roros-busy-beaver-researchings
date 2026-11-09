/**
 * Interactive SVG State Transition Graph Visualizer
 * Renders the state machine graph for an agent:
 * - States as circular nodes
 * - Directed transition edges with read/write/direction labels
 * - Active state glowing during simulation playback
 */

class StateGraphVisualizer {
  constructor(container) {
    this.container = container;
  }

  render(agentTable, agentId = 1, currentState = 0) {
    if (!this.container || !agentTable) return;

    const nStates = agentTable.length;
    const width = 320;
    const height = 240;
    const centerX = width / 2;
    const centerY = height / 2;
    const radius = Math.min(width, height) * 0.35;

    // Calculate node coordinates around circle
    const nodeCoords = [];
    for (let s = 0; s < nStates; s++) {
      const angle = (2 * Math.PI * s) / nStates - Math.PI / 2;
      const x = centerX + radius * Math.cos(angle);
      const y = centerY + radius * Math.sin(angle);
      nodeCoords.push({ x, y, angle });
    }

    let svg = `<svg viewBox="0 0 ${width} ${height}" class="state-machine-svg">
      <defs>
        <marker id="arrow" viewBox="0 0 10 10" refX="22" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#38bdf8" />
        </marker>
        <marker id="arrow-alt" viewBox="0 0 10 10" refX="22" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#f472b6" />
        </marker>
        <filter id="node-glow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feComposite in="SourceGraphic" in2="blur" operator="over" />
        </filter>
      </defs>`;

    // Render transition edges
    for (let s = 0; s < nStates; s++) {
      for (let sym = 0; sym < 2; sym++) {
        const trans = agentTable[s][sym];
        const targetState = trans.nextState;
        const from = nodeCoords[s];
        const to = nodeCoords[targetState];
        const isSelfLoop = s === targetState;
        const color = sym === 0 ? '#38bdf8' : '#f472b6';
        const marker = sym === 0 ? 'url(#arrow)' : 'url(#arrow-alt)';
        const dirChar = trans.dir === 1 ? 'R' : 'L';
        const labelText = `${sym}:${trans.write},${dirChar}`;

        if (isSelfLoop) {
          // Self loop arc
          const loopRadius = 24;
          const arcAngle = from.angle;
          const loopX = from.x + Math.cos(arcAngle) * loopRadius * 1.5;
          const loopY = from.y + Math.sin(arcAngle) * loopRadius * 1.5;
          const dx = loopX - from.x;
          const dy = loopY - from.y;

          svg += `
            <path d="M ${from.x} ${from.y} C ${from.x + dx - dy} ${from.y + dy + dx}, ${from.x + dx + dy} ${from.y + dy - dx}, ${from.x} ${from.y}"
                  fill="none" stroke="${color}" stroke-width="1.8" stroke-dasharray="${sym === 1 ? '4,3' : 'none'}" />
            <text x="${loopX}" y="${loopY}" fill="${color}" font-size="10" font-family="monospace" text-anchor="middle" dominant-baseline="middle" font-weight="bold">${labelText}</text>
          `;
        } else {
          // Directed curved edge between states
          // Curved to separate symmetric edges
          const midX = (from.x + to.x) / 2;
          const midY = (from.y + to.y) / 2;
          const dx = to.x - from.x;
          const dy = to.y - from.y;
          const normalX = -dy * 0.15 * (sym === 0 ? 1 : -1);
          const normalY = dx * 0.15 * (sym === 0 ? 1 : -1);
          const ctrlX = midX + normalX;
          const ctrlY = midY + normalY;

          svg += `
            <path d="M ${from.x} ${from.y} Q ${ctrlX} ${ctrlY} ${to.x} ${to.y}"
                  fill="none" stroke="${color}" stroke-width="1.8" marker-end="${marker}"
                  stroke-dasharray="${sym === 1 ? '4,3' : 'none'}" />
            <text x="${ctrlX}" y="${ctrlY}" fill="${color}" font-size="10" font-family="monospace" text-anchor="middle" dominant-baseline="middle" font-weight="bold">${labelText}</text>
          `;
        }
      }
    }

    // Render State Nodes
    for (let s = 0; s < nStates; s++) {
      const node = nodeCoords[s];
      const isCurrent = s === currentState;
      const stateChar = String.fromCharCode(65 + s);

      svg += `
        <g class="state-node" transform="translate(${node.x}, ${node.y})">
          <circle r="${isCurrent ? 20 : 18}"
                  fill="${isCurrent ? '#0284c7' : '#1e293b'}"
                  stroke="${isCurrent ? '#38bdf8' : '#475569'}"
                  stroke-width="${isCurrent ? 3 : 2}"
                  ${isCurrent ? 'filter="url(#node-glow)"' : ''} />
          <text text-anchor="middle" dominant-baseline="middle"
                fill="#ffffff" font-size="12" font-family="sans-serif" font-weight="bold">
            ${stateChar}
          </text>
        </g>
      `;
    }

    svg += `</svg>`;
    this.container.innerHTML = svg;
  }
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = StateGraphVisualizer;
}
