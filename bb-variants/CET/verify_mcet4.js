// Verify MCET(4) 4-agent simultaneous collision champion
const fs = require('fs');

function parseAgent(str) {
  // Format: 1RA0LB_1RA0LB -> state 0: [sym0, sym1], state 1: [sym0, sym1]
  const states = str.split('_');
  const tr = {};
  states.forEach((stStr, sIdx) => {
    tr[sIdx] = {};
    for (let r = 0; r < 2; r++) {
      const chunk = stStr.substring(r * 3, r * 3 + 3);
      tr[sIdx][r] = {
        write: parseInt(chunk[0]),
        move: chunk[1] === 'R' ? 1 : -1,
        nextState: chunk[2].charCodeAt(0) - 65
      };
    }
  });
  return tr;
}

const bbchallenge = "1RA0LB_1RA0LB|1RA1LB_1RA1LA|1LB1RA_0RA0LB|1LA0RA_1RB0LA";
const agents = bbchallenge.split('|').map(parseAgent);

const tape = new Map();
let pos = [0, 2, 4, 6];
let states = [0, 0, 0, 0];

let step = 0;
const limit = 2000000;

console.log("Simulating MCET(4) candidate:", bbchallenge);

while (step < limit) {
  step++;
  
  // Read
  const r = pos.map(p => tape.get(p) || 0);
  const actions = agents.map((ag, i) => ag[states[i]][r[i]]);

  // Write with priority Agent 0 > Agent 1 > Agent 2 > Agent 3
  for (let i = 3; i >= 0; i--) {
    tape.set(pos[i], actions[i].write);
  }

  // Move & transition
  for (let i = 0; i < 4; i++) {
    pos[i] += actions[i].move;
    states[i] = actions[i].nextState;
  }

  // Check 4-way collision
  if (pos[0] === pos[1] && pos[1] === pos[2] && pos[2] === pos[3]) {
    console.log(`\n💥 ALL 4 AGENTS SIMULTANEOUSLY COLLIDED at step ${step} on cell ${pos[0]}!`);
    console.log(`Agent states at collision: [${states.join(', ')}]`);
    
    // Tape stats
    let ones = 0;
    let minX = Infinity, maxX = -Infinity;
    for (const [k, v] of tape.entries()) {
      if (v === 1) ones++;
      if (k < minX) minX = k;
      if (k > maxX) maxX = k;
    }
    console.log(`Active tape span: [${minX}, ${maxX}] (${maxX - minX + 1} cells), 1s painted: ${ones}`);
    process.exit(0);
  }
}

console.log(`Reached limit ${limit} without 4-way collision.`);
