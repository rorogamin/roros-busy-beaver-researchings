/**
 * Catch-Em-Turing (CET) & Multi Catch-Em-Turing (MCET) Core Simulator Engine
 *
 * Rules:
 * - Tape is infinite in both directions, initially all 0s.
 * - CET(n): 2 agents, n states. Agent 1 starts at pos 0, Agent 2 at pos 2.
 * - MCET(n): M agents, n states. Arbitrary initial positions.
 * - At each step, agents simultaneously:
 *     1. Read current cell symbol.
 *     2. Write symbol to current cell.
 *     3. Move left (-1) or right (+1).
 *     4. Change state according to transition table.
 * - Writing conflict resolution: Lowest index has priority.
 * - Halting: agents collide on the same cell at the same time.
 */

/**
 * Block-based Infinite Tape Storage with Ultra-Fast Contiguous Fast-Path
 * Uses a flat 2M-cell Uint8Array around origin [-1048576, +1048575] for zero-overhead O(1) array indexing,
 * falling back to 512-cell chunks only if positions exceed +/- 1,048,576!
 */
const FAST_TAPE_HALF = 1048576; // 2^20
const FAST_TAPE_SIZE = 2097152; // 2^21

class BlockTape {
  constructor(chunkSize = 512) {
    this.chunkSize = chunkSize;
    this.chunkShift = 9; // 2^9 = 512
    this.chunkMask = 511;
    this.chunks = new Map();
    this.fastData = new Uint8Array(FAST_TAPE_SIZE);
    this.fastMinIdx = FAST_TAPE_HALF;
    this.fastMaxIdx = FAST_TAPE_HALF;
    this.minPos = 0;
    this.maxPos = 0;
    this.onesCount = 0;
  }

  reset() {
    if (this.onesCount > 0 || this.fastMinIdx <= this.fastMaxIdx) {
      const lo = Math.max(0, this.fastMinIdx - 2);
      const hi = Math.min(FAST_TAPE_SIZE, this.fastMaxIdx + 3);
      this.fastData.fill(0, lo, hi);
    }
    this.fastMinIdx = FAST_TAPE_HALF;
    this.fastMaxIdx = FAST_TAPE_HALF;
    this.chunks.clear();
    this.minPos = 0;
    this.maxPos = 0;
    this.onesCount = 0;
  }

  get(pos) {
    const idx = (pos + FAST_TAPE_HALF) | 0;
    if (idx >= 0 && idx < FAST_TAPE_SIZE) {
      return this.fastData[idx];
    }
    const cid = pos >> this.chunkShift;
    const chunk = this.chunks.get(cid);
    return chunk ? chunk.data[pos & this.chunkMask] : 0;
  }

  set(pos, val) {
    const idx = (pos + FAST_TAPE_HALF) | 0;
    if (idx >= 0 && idx < FAST_TAPE_SIZE) {
      const oldVal = this.fastData[idx];
      if (oldVal === val) return;
      this.fastData[idx] = val;
      if (idx < this.fastMinIdx) this.fastMinIdx = idx;
      if (idx > this.fastMaxIdx) this.fastMaxIdx = idx;

      if (val !== 0 && oldVal === 0) {
        this.onesCount++;
        if (this.onesCount === 1) {
          this.minPos = pos;
          this.maxPos = pos;
        } else {
          if (pos < this.minPos) this.minPos = pos;
          if (pos > this.maxPos) this.maxPos = pos;
        }
      } else if (val === 0 && oldVal !== 0) {
        this.onesCount--;
      }
      return;
    }

    const cid = pos >> this.chunkShift;
    let chunk = this.chunks.get(cid);
    const offset = pos & this.chunkMask;
    const oldVal = chunk ? chunk.data[offset] : 0;
    if (oldVal === val) return;

    if (!chunk) {
      chunk = { data: new Uint8Array(this.chunkSize), count: 0 };
      this.chunks.set(cid, chunk);
    }

    chunk.data[offset] = val;
    if (val !== 0 && oldVal === 0) {
      chunk.count++;
      this.onesCount++;
      if (this.onesCount === 1) {
        this.minPos = pos;
        this.maxPos = pos;
      } else {
        if (pos < this.minPos) this.minPos = pos;
        if (pos > this.maxPos) this.maxPos = pos;
      }
    } else if (val === 0 && oldVal !== 0) {
      chunk.count--;
      this.onesCount--;
    }
  }

  // Extract contiguous non-zero intervals [startPos, endPos, val] on-demand for snapshot recording!
  // Eliminates O(I) interval array cloning/sorting on every non-sampled simulation step!
  extractIntervals() {
    const intervals = [];
    if (this.onesCount === 0) return intervals;

    if (this.chunks.size === 0) {
      const start = Math.max(0, (this.minPos + FAST_TAPE_HALF) | 0);
      const end = Math.min(FAST_TAPE_SIZE - 1, (this.maxPos + FAST_TAPE_HALF) | 0);
      const data = this.fastData;
      let inRun = false;
      let runStart = 0;
      let runVal = 0;

      for (let i = start; i <= end; i++) {
        const v = data[i];
        if (v !== 0) {
          if (!inRun) {
            inRun = true;
            runStart = i - FAST_TAPE_HALF;
            runVal = v;
          } else if (v !== runVal) {
            intervals.push([runStart, i - 1 - FAST_TAPE_HALF, runVal]);
            runStart = i - FAST_TAPE_HALF;
            runVal = v;
          }
        } else if (inRun) {
          intervals.push([runStart, i - 1 - FAST_TAPE_HALF, runVal]);
          inRun = false;
        }
      }
      if (inRun) {
        intervals.push([runStart, end - FAST_TAPE_HALF, runVal]);
      }
      return intervals;
    }

    // Fallback if chunks are also used
    let inRun = false;
    let runStart = 0;
    let runVal = 0;
    for (let p = this.minPos; p <= this.maxPos; p++) {
      const v = this.get(p);
      if (v !== 0) {
        if (!inRun) {
          inRun = true;
          runStart = p;
          runVal = v;
        } else if (v !== runVal) {
          intervals.push([runStart, p - 1, runVal]);
          runStart = p;
          runVal = v;
        }
      } else if (inRun) {
        intervals.push([runStart, p - 1, runVal]);
        inRun = false;
      }
    }
    if (inRun) {
      intervals.push([runStart, this.maxPos, runVal]);
    }
    return intervals;
  }

  getMetrics() {
    return {
      minPos: this.minPos,
      maxPos: this.maxPos,
      span: this.onesCount > 0 ? (this.maxPos - this.minPos + 1) : 0,
      onesCount: this.onesCount,
      totalBlocks: this.chunks.size + 1
    };
  }
}

/**
 * TapeIntervals: Fast Disjoint Interval Tracker for Tape 1s
 * Maintains sorted contiguous intervals [startPos, endPos] of 1s on the tape.
 * Enables O(1) interval drawing (continuous horizontal lines) for space-time diagrams.
 */
class TapeIntervals {
  constructor() {
    this.intervals = [];
  }

  reset() {
    this.intervals = [];
  }

  clone() {
    const len = this.intervals.length;
    const arr = new Array(len);
    for (let i = 0; i < len; i++) {
      arr[i] = [this.intervals[i][0], this.intervals[i][1], this.intervals[i][2] || 1];
    }
    return arr;
  }

  set(pos, val) {
    if (val > 0) {
      this.add(pos, val);
    } else {
      this.remove(pos);
    }
  }

  add(pos, val = 1) {
    let newStart = pos;
    let newEnd = pos;
    const next = [];
    let inserted = false;
    for (let i = 0; i < this.intervals.length; i++) {
      const [s, e, v = 1] = this.intervals[i];
      // Only merge if contiguous AND same symbol value
      if (e < pos - 1) {
        next.push([s, e, v]);
      } else if (s > pos + 1) {
        if (!inserted) {
          next.push([newStart, newEnd, val]);
          inserted = true;
        }
        next.push([s, e, v]);
      } else {
        if (v === val) {
          if (s < newStart) newStart = s;
          if (e > newEnd) newEnd = e;
        } else {
          // Different symbol on adjacent or overlapping cell: split
          if (pos >= s && pos <= e) {
            if (s < pos) next.push([s, pos - 1, v]);
            if (pos < e) next.push([pos + 1, e, v]);
          } else {
            next.push([s, e, v]);
          }
        }
      }
    }
    if (!inserted) {
      next.push([newStart, newEnd, val]);
    }
    // Sort intervals by start pos
    next.sort((a, b) => a[0] - b[0]);
    this.intervals = next;
  }

  remove(pos) {
    const next = [];
    for (let i = 0; i < this.intervals.length; i++) {
      const [s, e, v = 1] = this.intervals[i];
      if (pos < s || pos > e) {
        next.push([s, e, v]);
      } else {
        if (s < pos) next.push([s, pos - 1, v]);
        if (pos < e) next.push([pos + 1, e, v]);
      }
    }
    this.intervals = next;
  }

  has(pos) {
    for (let i = 0; i < this.intervals.length; i++) {
      const [s, e] = this.intervals[i];
      if (pos >= s && pos <= e) return true;
      if (pos < s) return false;
    }
    return false;
  }

  getIntervals() {
    return this.intervals;
  }
}

class CETSimulator {
  constructor(options = {}) {
    this.nStates = options.nStates || 2;
    this.nSymbols = options.nSymbols || 2; // Default binary alphabet {0, 1}
    this.agentCount = options.agentCount || 2;
    this.initialPositions = options.initialPositions || [0, 2];
    this.haltRule = options.haltRule || 'first_pair'; // 'first_pair' | 'all' | 'elimination'
    this.haltCondition = options.haltCondition || 'normal'; // 'normal' (CET_0) | 'quasihalt' (CET_1)
    this.maxSteps = options.maxSteps || Infinity; // Unlimited steps (halts ONLY on collision)

    // Dynamic History Decimation to prevent browser freezing / OOM on multi-million steps
    this.maxSnapshots = 20000;
    this.sampleStride = 1;

    // Quasihalting tracking
    this.collisionCount = 0;
    this.lastCollisionStep = 0;
    this.lastCollisionPos = 0;
    this.quasihaltEvent = null; // { lastColStep, cycleLen, drift, totalCols }
    this.stateHistoryMap = new Map(); // signature -> { step, p1, p2, cols }

    // Transition tables: array of agent tables.
    // Each table is indexed by [state][symbol] => { write: 0|1, dir: -1|+1, nextState: 0..n-1 }
    this.tables = [];
    if (options.tables) {
      this.tables = JSON.parse(JSON.stringify(options.tables));
    } else {
      this.initDefaultTables();
    }

    this.reset();
  }

  initDefaultTables() {
    this.tables = [];
    for (let a = 0; a < this.agentCount; a++) {
      const agentTable = [];
      for (let s = 0; s < this.nStates; s++) {
        const stateRows = [];
        for (let sym = 0; sym < this.nSymbols; sym++) {
          // Default: write sym, move right for even agent, left for odd, stay in state
          stateRows.push({
            write: sym,
            dir: a % 2 === 0 ? 1 : -1,
            nextState: (s + 1) % this.nStates
          });
        }
        agentTable.push(stateRows);
      }
      this.tables.push(agentTable);
    }
  }

  // Load standard CET(2) record champion (Nath76 97-step)
  loadCET2Champion() {
    this.nStates = 2;
    this.agentCount = 2;
    this.initialPositions = [0, 2];
    this.tables = [
      // Agent 1: (1, LEFT, 1), (0, LEFT, 1), (1, RIGHT, 1), (0, LEFT, 0)
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: (1, RIGHT, 1), (1, LEFT, 0), (1, LEFT, 0), (1, RIGHT, 1)
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ];
    this.reset();
  }

  // Load CET(1) champion (1-step)
  loadCET1() {
    this.nStates = 1;
    this.agentCount = 2;
    this.initialPositions = [0, 2];
    this.tables = [
      // Agent 1: (0, RIGHT, 0), (0, LEFT, 0)
      [
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: (0, LEFT, 0), (0, LEFT, 0)
      [
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ]
    ];
    this.reset();
  }

  reset() {
    this.stepCount = 0;
    this.halted = false;
    this.haltReason = null;
    this.collisionEvent = null; // { step, pos, agents: [id1, id2] }
    this.collisionCount = 0;
    this.lastCollisionStep = 0;
    this.lastCollisionPos = 0;
    this.quasihaltEvent = null;
    this.stateHistoryMap = new Map();

    // Dynamic decimation for space-time diagram snapshots
    this.sampleStride = 1;

    // High performance block-based infinite tape
    this.tape = new BlockTape(512);

    // Continuous interval tracker for space-time diagram
    this.tapeIntervals = new TapeIntervals();

    // Active agents: array of { id, pos, state, active }
    this.agents = [];
    for (let i = 0; i < this.agentCount; i++) {
      const pos = this.initialPositions[i] !== undefined ? this.initialPositions[i] : i * 2;
      this.agents.push({
        id: i + 1,
        index: i,
        pos: pos,
        state: 0,
        active: true
      });
    }

    // Full run trajectory cache for space-time diagram
    this.history = [];
    this.recordInitialState();
  }

  recordInitialState() {
    this.history = [{
      step: 0,
      agentStates: this.agents.map(a => ({ id: a.id, pos: a.pos, state: a.state, active: a.active })),
      writtenCells: [],
      intervals: this.tape.extractIntervals(),
      collision: null
    }];

    // Check if initial positions have collision
    this.checkCollision(0);
  }

  checkCollision(step) {
    if (this.haltCondition === 'none') return false;
    const activeAgents = this.agents.filter(a => a.active);
    const posMap = new Map();

    for (const ag of activeAgents) {
      if (!posMap.has(ag.pos)) {
        posMap.set(ag.pos, []);
      }
      posMap.get(ag.pos).push(ag);
    }

    let collidedGroups = [];
    for (const [pos, ags] of posMap.entries()) {
      if (ags.length > 1) {
        collidedGroups.push({ pos, agents: ags.map(a => a.id) });
      }
    }

    if (collidedGroups.length > 0) {
      if (this.haltRule === 'first_pair') {
        this.halted = true;
        this.collisionEvent = {
          step: step,
          pos: collidedGroups[0].pos,
          agents: collidedGroups[0].agents
        };
        this.haltReason = `Collision at cell ${this.collisionEvent.pos} between Agent(s) ${this.collisionEvent.agents.join(', ')}`;
        return true;
      } else if (this.haltRule === 'all') {
        const largest = Math.max(...collidedGroups.map(g => g.agents.length));
        if (largest >= activeAgents.length && activeAgents.length > 1) {
          this.halted = true;
          this.collisionEvent = {
            step: step,
            pos: collidedGroups[0].pos,
            agents: collidedGroups[0].agents
          };
          this.haltReason = `All agents converged at cell ${this.collisionEvent.pos}!`;
          return true;
        }
      } else if (this.haltRule === 'elimination') {
        // Eliminate all but lowest id agent at each collided position
        for (const grp of collidedGroups) {
          const sorted = [...grp.agents].sort((a, b) => a - b);
          const survivor = sorted[0];
          for (let i = 1; i < sorted.length; i++) {
            const agToElim = this.agents.find(a => a.id === sorted[i]);
            if (agToElim) agToElim.active = false;
          }
        }
        const remaining = this.agents.filter(a => a.active);
        if (remaining.length <= 1) {
          this.halted = true;
          this.collisionEvent = {
            step: step,
            pos: collidedGroups[0].pos,
            agents: collidedGroups[0].agents
          };
          this.haltReason = `Elimination ended: Agent ${remaining[0]?.id || 'None'} sole survivor at step ${step}`;
          return true;
        }
      }
    }
    return false;
  }

  // Execute a single simulation step
  step() {
    if (this.halted) return false;
    if (this.stepCount >= this.maxSteps) {
      this.halted = true;
      this.haltReason = `Reached maximum step limit (${this.maxSteps})`;
      return false;
    }

    // Fast-path optimized 2-agent execution: eliminates Map/Array GC churn
    if (this.agentCount === 2 && this.agents[0].active && this.agents[1].active) {
      const ag1 = this.agents[0];
      const ag2 = this.agents[1];

      // 1. Read
      const sym1 = this.tape.get(ag1.pos) || 0;
      const sym2 = this.tape.get(ag2.pos) || 0;

      const t1 = this.tables[0][ag1.state][sym1];
      const t2 = this.tables[1][ag2.state][sym2];

      // 2. Write with Agent 1 priority on same cell
      this.tape.set(ag1.pos, t1.write);

      if (ag2.pos !== ag1.pos) {
        this.tape.set(ag2.pos, t2.write);
      }

      // 3. Move & State
      ag1.pos += t1.dir;
      ag1.state = t1.nextState;

      ag2.pos += t2.dir;
      ag2.state = t2.nextState;

      this.stepCount++;

      // 4. Halting collision check
      const hasCollided = (ag1.pos === ag2.pos);
      if (hasCollided) {
        this.collisionCount++;
        this.lastCollisionStep = this.stepCount;
        this.lastCollisionPos = ag1.pos;

        if (this.haltCondition !== 'quasihalt' && this.haltCondition !== 'none') {
          this.halted = true;
          this.collisionEvent = { step: this.stepCount, pos: ag1.pos, agents: [1, 2] };
          this.haltReason = `Collision at cell ${ag1.pos} between Agent(s) 1, 2`;
        }
      }

      // Check Quasihalting Cycle in post-collision phase
      if (this.haltCondition === 'quasihalt' && this.lastCollisionStep > 0 && this.stepCount > this.lastCollisionStep) {
        // Build relative local signature including local tape context
        const rel = ag2.pos - ag1.pos;
        
        // Sample local tape window around heads [-16 .. +16]
        let tapeSig = '';
        const base = Math.min(ag1.pos, ag2.pos) - 4;
        const maxPos = Math.max(ag1.pos, ag2.pos) + 4;
        for (let x = base; x <= maxPos; x++) {
          tapeSig += (this.tape.get(x) || 0);
        }

        const key = `${rel}_${ag1.state}_${ag2.state}_${tapeSig}`;
        const past = this.stateHistoryMap.get(key);

        if (past && past.step > this.lastCollisionStep) {
          const cyc = this.stepCount - past.step;
          const dp1 = ag1.pos - past.p1;
          const dp2 = ag2.pos - past.p2;

          if (dp1 === dp2 && past.cols === this.collisionCount) {
            // PROVEN QUASI-HALT!
            if (!this.quasihaltEvent) {
              this.quasihaltEvent = {
                lastColStep: this.lastCollisionStep,
                cycleLen: cyc,
                drift: dp1,
                totalCols: this.collisionCount,
                pos: this.lastCollisionPos
              };
              this.collisionEvent = { step: this.lastCollisionStep, pos: this.lastCollisionPos, agents: [1, 2] };
              this.haltReason = `Quasi-halted! Last collision at step ${this.lastCollisionStep} (${this.collisionCount} collisions). Cycle period ${cyc}, drift ${dp1}.`;
              this.halted = true; // Pause at certified quasi-halt
            }
          }
        }

        this.stateHistoryMap.set(key, {
          step: this.stepCount,
          p1: ag1.pos,
          p2: ag2.pos,
          cols: this.collisionCount
        });
      }

      // 5. Dynamic History Decimation (prevents OOM browser crash at millions of steps)
      const recordCollision = (hasCollided && this.haltCondition !== 'none');
      if (recordCollision || (this.stepCount % this.sampleStride === 0)) {
        this.history.push({
          step: this.stepCount,
          agentStates: [
            { id: 1, pos: ag1.pos, state: ag1.state, active: true },
            { id: 2, pos: ag2.pos, state: ag2.state, active: true }
          ],
          intervals: this.tape.extractIntervals(),
          collision: recordCollision ? this.collisionEvent : null
        });

        if (this.history.length > this.maxSnapshots) {
          // Decimate history by 2 to keep RAM constant (~10-20MB total)
          const newHist = [];
          for (let i = 0; i < this.history.length; i += 2) {
            newHist.push(this.history[i]);
          }
          this.history = newHist;
          this.sampleStride *= 2;
        }
      }

      return !this.halted;
    }

    // Generalized M-Agent path
    const activeAgents = this.agents.filter(a => a.active);
    if (activeAgents.length === 0) {
      this.halted = true;
      this.haltReason = 'No active agents';
      return false;
    }

    const actions = [];
    for (const ag of activeAgents) {
      const sym = this.tape.get(ag.pos) || 0;
      const trans = this.tables[ag.index][ag.state][sym];
      actions.push({
        agent: ag,
        readPos: ag.pos,
        readSym: sym,
        write: trans.write,
        dir: trans.dir,
        nextState: trans.nextState
      });
    }

    const writesByPos = new Map();
    for (const act of actions) {
      if (!writesByPos.has(act.readPos)) writesByPos.set(act.readPos, []);
      writesByPos.get(act.readPos).push(act);
    }

    for (const [pos, acts] of writesByPos.entries()) {
      acts.sort((a, b) => a.agent.index - b.agent.index);
      const chosenWrite = acts[0].write;
      this.tape.set(pos, chosenWrite);
    }

    for (const act of actions) {
      act.agent.pos += act.dir;
      act.agent.state = act.nextState;
    }

    this.stepCount++;
    const hasCollided = this.checkCollision(this.stepCount);

    if (hasCollided || (this.stepCount % this.sampleStride === 0)) {
      this.history.push({
        step: this.stepCount,
        agentStates: this.agents.map(a => ({ id: a.id, pos: a.pos, state: a.state, active: a.active })),
        intervals: this.tape.extractIntervals(),
        collision: hasCollided ? this.collisionEvent : null
      });

      if (this.history.length > this.maxSnapshots) {
        const newHist = [];
        for (let i = 0; i < this.history.length; i += 2) {
          newHist.push(this.history[i]);
        }
        this.history = newHist;
        this.sampleStride *= 2;
      }
    }

    return !this.halted;
  }

  // Ultra-fast JIT-inlined batch stepping for 2-agent standard CET execution (50M-100M+ steps/sec)
  stepBatch(batchSize) {
    if (this.halted) return 0;
    if (this.agentCount !== 2 || !this.agents[0].active || !this.agents[1].active || this.haltCondition === 'quasihalt') {
      let count = 0;
      while (count < batchSize && !this.halted && this.stepCount < this.maxSteps) {
        this.step();
        count++;
      }
      return count;
    }

    const ag1 = this.agents[0];
    const ag2 = this.agents[1];
    let p1 = ag1.pos | 0;
    let s1 = ag1.state | 0;
    let p2 = ag2.pos | 0;
    let s2 = ag2.state | 0;

    const tab0 = this.tables[0];
    const tab1 = this.tables[1];
    const tape = this.tape;
    const fastData = tape.fastData;
    let fastMinIdx = tape.fastMinIdx | 0;
    let fastMaxIdx = tape.fastMaxIdx | 0;
    let minPos = tape.minPos | 0;
    let maxPos = tape.maxPos | 0;
    let onesCount = tape.onesCount | 0;

    let stepCount = this.stepCount;
    const maxSteps = Math.min(this.maxSteps, stepCount + batchSize);
    let sampleStride = this.sampleStride | 0;
    let strideMask = (sampleStride - 1) | 0;
    let nextSampleStep = (Math.floor(stepCount / sampleStride) + 1) * sampleStride;

    let executed = 0;
    while (stepCount < maxSteps) {
      const idx1 = (p1 + FAST_TAPE_HALF) | 0;
      const idx2 = (p2 + FAST_TAPE_HALF) | 0;

      // Fast path when both heads are within [-1048576, +1048575]
      if (idx1 >= 0 && idx1 < FAST_TAPE_SIZE && idx2 >= 0 && idx2 < FAST_TAPE_SIZE) {
        const sym1 = fastData[idx1];
        const sym2 = fastData[idx2];
        const t1 = tab0[s1][sym1];
        const t2 = tab1[s2][sym2];

        const w1 = t1.write;
        if (sym1 !== w1) {
          fastData[idx1] = w1;
          if (idx1 < fastMinIdx) fastMinIdx = idx1;
          if (idx1 > fastMaxIdx) fastMaxIdx = idx1;
          if (w1 !== 0 && sym1 === 0) {
            onesCount++;
            if (onesCount === 1) {
              minPos = p1;
              maxPos = p1;
            } else {
              if (p1 < minPos) minPos = p1;
              if (p1 > maxPos) maxPos = p1;
            }
          } else if (w1 === 0 && sym1 !== 0) {
            onesCount--;
          }
        }

        if (p2 !== p1) {
          const w2 = t2.write;
          if (sym2 !== w2) {
            fastData[idx2] = w2;
            if (idx2 < fastMinIdx) fastMinIdx = idx2;
            if (idx2 > fastMaxIdx) fastMaxIdx = idx2;
            if (w2 !== 0 && sym2 === 0) {
              onesCount++;
              if (onesCount === 1) {
                minPos = p2;
                maxPos = p2;
              } else {
                if (p2 < minPos) minPos = p2;
                if (p2 > maxPos) maxPos = p2;
              }
            } else if (w2 === 0 && sym2 !== 0) {
              onesCount--;
            }
          }
        }

        p1 = (p1 + t1.dir) | 0;
        s1 = t1.nextState | 0;
        p2 = (p2 + t2.dir) | 0;
        s2 = t2.nextState | 0;
      } else {
        // Sync back scalar metrics and step via general tape fallback
        tape.fastMinIdx = fastMinIdx;
        tape.fastMaxIdx = fastMaxIdx;
        tape.minPos = minPos;
        tape.maxPos = maxPos;
        tape.onesCount = onesCount;

        const sym1 = tape.get(p1) || 0;
        const sym2 = tape.get(p2) || 0;
        const t1 = tab0[s1][sym1];
        const t2 = tab1[s2][sym2];
        tape.set(p1, t1.write);
        if (p2 !== p1) tape.set(p2, t2.write);
        p1 = (p1 + t1.dir) | 0;
        s1 = t1.nextState | 0;
        p2 = (p2 + t2.dir) | 0;
        s2 = t2.nextState | 0;

        fastMinIdx = tape.fastMinIdx;
        fastMaxIdx = tape.fastMaxIdx;
        minPos = tape.minPos;
        maxPos = tape.maxPos;
        onesCount = tape.onesCount;
      }

      stepCount++;
      executed++;

      if (p1 === p2) {
        tape.fastMinIdx = fastMinIdx;
        tape.fastMaxIdx = fastMaxIdx;
        tape.minPos = minPos;
        tape.maxPos = maxPos;
        tape.onesCount = onesCount;
        ag1.pos = p1;
        ag1.state = s1;
        ag2.pos = p2;
        ag2.state = s2;
        this.stepCount = stepCount;
        this.collisionCount++;
        this.lastCollisionStep = stepCount;
        this.lastCollisionPos = p1;

        if (this.haltCondition !== 'none') {
          this.halted = true;
          this.collisionEvent = { step: stepCount, pos: p1, agents: [1, 2] };
          this.haltReason = `Collision at cell ${p1} between Agent(s) 1, 2`;

          this.history.push({
            step: stepCount,
            agentStates: [
              { id: 1, pos: p1, state: s1, active: true },
              { id: 2, pos: p2, state: s2, active: true }
            ],
            intervals: tape.extractIntervals(),
            collision: this.collisionEvent
          });
          return executed;
        }
      }

      if (stepCount === nextSampleStep) {
        tape.fastMinIdx = fastMinIdx;
        tape.fastMaxIdx = fastMaxIdx;
        tape.minPos = minPos;
        tape.maxPos = maxPos;
        tape.onesCount = onesCount;

        this.history.push({
          step: stepCount,
          agentStates: [
            { id: 1, pos: p1, state: s1, active: true },
            { id: 2, pos: p2, state: s2, active: true }
          ],
          intervals: tape.extractIntervals(),
          collision: null
        });

        if (this.history.length > this.maxSnapshots) {
          const newHist = [];
          for (let i = 0; i < this.history.length; i += 2) {
            newHist.push(this.history[i]);
          }
          this.history = newHist;
          sampleStride *= 2;
          this.sampleStride = sampleStride;
        }
        nextSampleStep = stepCount + sampleStride;
      }
    }

    tape.fastMinIdx = fastMinIdx;
    tape.fastMaxIdx = fastMaxIdx;
    tape.minPos = minPos;
    tape.maxPos = maxPos;
    tape.onesCount = onesCount;
    ag1.pos = p1;
    ag1.state = s1;
    ag2.pos = p2;
    ag2.state = s2;
    this.stepCount = stepCount;

    if (this.stepCount >= this.maxSteps && !this.halted) {
      this.halted = true;
      this.haltReason = `Reached maximum step limit (${this.maxSteps})`;
    }
    return executed;
  }

  // Load a native-precomputed space-time trace (see trace_export.cpp) so multi-billion-step
  // machines can be viewed instantly: history snapshots + final collision state are restored.
  loadTrace(arrayBuffer) {
    const dv = new DataView(arrayBuffer);
    if (dv.getUint32(0, true) !== 0x43455431) throw new Error('Bad trace file');
    const ns = dv.getUint32(4, true);
    const finalStep = dv.getFloat64(16, true);
    const colPos = dv.getInt32(24, true);
    let off = 28;
    const history = [];
    for (let i = 0; i < ns; i++) {
      const step = dv.getFloat64(off, true); off += 8;
      const p0 = dv.getInt32(off, true), q0 = dv.getInt32(off + 4, true);
      const p1 = dv.getInt32(off + 8, true), q1 = dv.getInt32(off + 12, true);
      const cnt = dv.getInt32(off + 16, true); off += 20;
      const intervals = new Array(cnt);
      for (let k = 0; k < cnt; k++) {
        intervals[k] = [dv.getInt32(off, true), dv.getInt32(off + 4, true), dv.getInt32(off + 8, true)];
        off += 12;
      }
      history.push({
        step,
        agentStates: [
          { id: 1, pos: p0, state: q0, active: true },
          { id: 2, pos: p1, state: q1, active: true }
        ],
        writtenCells: [],
        intervals,
        collision: null
      });
    }
    this.history = history;
    this.stepCount = finalStep;
    this.sampleStride = Math.max(1, Math.floor(finalStep / Math.max(1, ns - 2)));
    this.collisionCount = 1;
    this.lastCollisionStep = finalStep;
    this.lastCollisionPos = colPos;
    this.collisionEvent = { step: finalStep, pos: colPos, agents: [1, 2] };
    history[history.length - 1].collision = this.collisionEvent;
    this.halted = true;
    this.haltReason = `Collision at cell ${colPos} between Agent(s) 1, 2 (native trace)`;
    const last = history[history.length - 1];
    this.agents[0].pos = last.agentStates[0].pos; this.agents[0].state = last.agentStates[0].state;
    this.agents[1].pos = last.agentStates[1].pos; this.agents[1].state = last.agentStates[1].state;
    // Restore final tape into BlockTape so metrics/tape view work
    this.tape.reset();
    for (const [s, e, v] of last.intervals) {
      for (let x = s; x <= e; x++) this.tape.set(x, v);
    }
    return { halted: true, stepCount: finalStep, collision: this.collisionEvent, reason: this.haltReason };
  }

  // Get nearest snapshot in history for a specific step (O(log K))
  getSnapshotAtStep(targetStep) {
    if (!this.history || this.history.length === 0) return null;
    let low = 0, high = this.history.length - 1;
    let best = 0;
    while (low <= high) {
      const mid = (low + high) >> 1;
      if (this.history[mid].step <= targetStep) {
        best = mid;
        low = mid + 1;
      } else {
        high = mid - 1;
      }
    }
    return this.history[best];
  }

  // Fast-forward run from start until halt or step limit
  runToCompletion(maxSteps = this.maxSteps, shouldReset = true) {
    if (shouldReset) {
      this.reset();
    }
    // If no halting condition, limit run to a safe chunk (e.g. 100,000 steps) so browser doesn't freeze forever
    const effectiveLimit = (this.haltCondition === 'none' && maxSteps === Infinity) ? 100000 : maxSteps;
    this.maxSteps = effectiveLimit;
    while (!this.halted && this.stepCount < this.maxSteps) {
      this.stepBatch(this.maxSteps - this.stepCount);
    }
    return {
      halted: this.halted,
      stepCount: this.stepCount,
      collision: this.collisionEvent,
      reason: this.haltReason
    };
  }

  // Get active tape boundaries and metrics (O(1) using BlockTape metrics)
  getTapeMetrics() {
    const tm = this.tape.getMetrics();
    let minPos = tm.minPos;
    let maxPos = tm.maxPos;

    for (const ag of this.agents) {
      if (ag.active) {
        if (ag.pos < minPos) minPos = ag.pos;
        if (ag.pos > maxPos) maxPos = ag.pos;
      }
    }

    return {
      minPos,
      maxPos,
      span: maxPos - minPos + 1,
      onesCount: tm.onesCount,
      totalBlocks: tm.totalBlocks
    };
  }

  // Get distance between Agent 1 and Agent 2 (for CET)
  getAgentDistance(a1Idx = 0, a2Idx = 1) {
    if (this.agents[a1Idx] && this.agents[a2Idx]) {
      return Math.abs(this.agents[a1Idx].pos - this.agents[a2Idx].pos);
    }
    return 0;
  }

  // Convert an agent's transition table to a canonical tuple string:
  // e.g. "(1, LEFT, 1), (0, LEFT, 1), (1, RIGHT, 1), (0, LEFT, 0)"
  agentToTuplesString(agIndex = 0) {
    if (!this.tables[agIndex]) return '';
    const tbl = this.tables[agIndex];
    const parts = [];
    for (let s = 0; s < this.nStates; s++) {
      for (let sym = 0; sym < this.nSymbols; sym++) {
        const t = tbl[s] ? tbl[s][sym] : null;
        if (t) {
          const dirStr = t.dir === 1 ? 'RIGHT' : 'LEFT';
          parts.push(`(${t.write}, ${dirStr}, ${t.nextState})`);
        }
      }
    }
    return parts.join(', ');
  }

  // Export single agent table in bbchallenge standard format:
  // e.g. "1LB0LB_1RB0LA" (for 2-sym) or "2LB1LA2LA_2RB0LA0LB" (for 3-sym)
  agentToBBChallenge(agIndex = 0) {
    if (!this.tables[agIndex]) return '';
    const tbl = this.tables[agIndex];
    const stateParts = [];
    for (let s = 0; s < this.nStates; s++) {
      let sStr = '';
      for (let sym = 0; sym < this.nSymbols; sym++) {
        const t = tbl[s] ? tbl[s][sym] : null;
        if (t) {
          const w = t.write;
          const d = t.dir === 1 ? 'R' : 'L';
          const ns = String.fromCharCode(65 + t.nextState);
          sStr += `${w}${d}${ns}`;
        } else {
          sStr += '---';
        }
      }
      stateParts.push(sStr);
    }
    return stateParts.join('_');
  }

  // Export full machine in piped bbchallenge standard format:
  // e.g. "1LB0LB_1RB0LA|1RB1LA_1LA1RB"
  toBBChallengeFormat() {
    const agentStrs = [];
    for (let a = 0; a < this.agentCount; a++) {
      agentStrs.push(this.agentToBBChallenge(a));
    }
    return agentStrs.join('|');
  }

  // Set an agent's table directly from a tuple string or bbchallenge format string
  setAgentFromTuples(agIndex, tupleInput) {
    let tuples = [];
    if (typeof tupleInput === 'string') {
      tuples = CETSimulator.parseTuplesOrBB(tupleInput);
    } else if (Array.isArray(tupleInput)) {
      tuples = tupleInput;
    }
    if (!tuples || tuples.length === 0) return false;

    // Check if new states or symbols are needed
    let maxState = this.nStates;
    let maxWrite = this.nSymbols - 1;
    for (const t of tuples) {
      if (t.nextState + 1 > maxState) maxState = t.nextState + 1;
      if (t.write > maxWrite) maxWrite = t.write;
    }
    const computedSymbols = Math.max(this.nSymbols, maxWrite + 1);
    const nFromLen = Math.ceil(tuples.length / computedSymbols);
    if (nFromLen > maxState) maxState = nFromLen;

    // Expand nStates or nSymbols if necessary across all agents
    if (maxState > this.nStates || computedSymbols > this.nSymbols) {
      this.nStates = maxState;
      this.nSymbols = computedSymbols;
      for (let a = 0; a < this.agentCount; a++) {
        // First expand symbols in existing states
        for (let s = 0; s < this.tables[a].length; s++) {
          while (this.tables[a][s].length < this.nSymbols) {
            this.tables[a][s].push({ write: 0, dir: 1, nextState: 0 });
          }
        }
        // Then expand states
        while (this.tables[a].length < this.nStates) {
          const row = [];
          for (let sym = 0; sym < this.nSymbols; sym++) {
            row.push({ write: 0, dir: 1, nextState: 0 });
          }
          this.tables[a].push(row);
        }
      }
    }

    // Reconstruct this agent's table
    const tbl = [];
    let idx = 0;
    for (let s = 0; s < this.nStates; s++) {
      const row = [];
      for (let sym = 0; sym < this.nSymbols; sym++) {
        if (idx < tuples.length) {
          row.push(tuples[idx++]);
        } else {
          row.push({ write: 0, dir: 1, nextState: 0 });
        }
      }
      tbl.push(row);
    }

    this.tables[agIndex] = tbl;
    this.reset();
    return true;
  }

  // Export machine as canonical readable text format
  toTextFormat() {
    let out = `CET Machine (n=${this.nStates}, agents=${this.agentCount})\n`;
    for (let a = 0; a < this.agentCount; a++) {
      const parts = [];
      for (let s = 0; s < this.nStates; s++) {
        for (let sym = 0; sym < this.nSymbols; sym++) {
          const t = this.tables[a][s][sym];
          const dirStr = t.dir === 1 ? 'RIGHT' : 'LEFT';
          parts.push(`(${t.write}, ${dirStr}, ${t.nextState})`);
        }
      }
      out += `Agent ${a + 1}: ${parts.join(', ')}\n`;
    }
    return out.trim();
  }

  // Fast flexible tuple parser: supports (1, LEFT, 1), (1, L, B), [0, RIGHT, 2], etc.
  static parseTuples(str) {
    if (!str || typeof str !== 'string') return [];
    const tupleRegex = /[\(\[]\s*([0-9])\s*[,;\s]\s*(LEFT|RIGHT|L|R|<|>|-?1|\+1)\s*[,;\s]\s*([0-9]|[A-Za-z])\s*[\)\]]/gi;
    const tuples = [];
    let m;
    while ((m = tupleRegex.exec(str)) !== null) {
      const write = parseInt(m[1], 10);
      const dStr = m[2].toUpperCase();
      const dir = (dStr === 'RIGHT' || dStr === 'R' || dStr === '1' || dStr === '+1' || dStr === '>') ? 1 : -1;
      let nextState;
      if (/[0-9]/.test(m[3])) {
        nextState = parseInt(m[3], 10);
      } else {
        nextState = m[3].toUpperCase().charCodeAt(0) - 65; // A=0, B=1, ...
      }
      tuples.push({ write, dir, nextState });
    }
    return tuples;
  }

  // Parse bbchallenge standard format transitions: e.g. "1RB0LD1LC..." or "1RB1LB_1LA1RH"
  static parseBBChallengeString(str) {
    if (!str || typeof str !== 'string') return [];
    const cleaned = str.trim().toUpperCase();
    const transitions = [];
    const transRegex = /([0-9])([RL])([A-Z0-9])|---/g;
    let m;
    while ((m = transRegex.exec(cleaned)) !== null) {
      if (m[0] === '---') {
        transitions.push({ write: 0, dir: 1, nextState: 0 });
      } else {
        const write = parseInt(m[1], 10);
        const dir = m[2] === 'R' ? 1 : -1;
        let nextState;
        if (/[0-9]/.test(m[3])) {
          nextState = parseInt(m[3], 10);
        } else {
          nextState = m[3].charCodeAt(0) - 65; // A=0, B=1, ...
        }
        transitions.push({ write, dir, nextState });
      }
    }
    return transitions;
  }

  // Universal single-agent parser: tries tuples first, then bbchallenge standard format
  static parseTuplesOrBB(str) {
    if (!str || typeof str !== 'string') return [];
    const tuples = CETSimulator.parseTuples(str);
    if (tuples.length > 0) return tuples;
    return CETSimulator.parseBBChallengeString(str);
  }

  // Import from full text format (supports "agent1|agent2" bbchallenge format, "Agent X:" notation, or tuple lines)
  static fromText(text, fallbackN = 2, fallbackSymbols = 2) {
    if (!text || typeof text !== 'string') return null;
    const trimmed = text.trim();

    // 1. Check for bbchallenge pipe format: "agent1|agent2" or "a1|a2|a3..."
    if (trimmed.includes('|')) {
      const parts = trimmed.split('|').map(p => p.trim()).filter(p => p.length > 0);
      if (parts.length >= 2) {
        const agentTuplesList = [];
        for (const part of parts) {
          const tuples = CETSimulator.parseTuplesOrBB(part);
          if (tuples.length > 0) {
            agentTuplesList.push(tuples);
          }
        }
        if (agentTuplesList.length >= 2) {
          return CETSimulator.buildFromTuplesList(agentTuplesList, fallbackN, fallbackSymbols);
        }
      }
    }

    const lines = text.split('\n').map(l => l.trim()).filter(l => l.length > 0);
    const agentTuplesList = [];

    // 2. Try matching explicit "Agent X:" headers
    for (const line of lines) {
      const match = line.match(/Agent\s*(\d+)\s*:\s*(.*)/i);
      if (match) {
        const tuples = CETSimulator.parseTuplesOrBB(match[2]);
        if (tuples.length > 0) {
          const agIdx = parseInt(match[1], 10) - 1;
          agentTuplesList[agIdx] = tuples;
        }
      }
    }

    // 3. If no "Agent X:" headers found, treat each non-empty line with tuples/bbchallenge as an agent
    if (agentTuplesList.length === 0) {
      for (const line of lines) {
        const tuples = CETSimulator.parseTuplesOrBB(line);
        if (tuples.length > 0) {
          agentTuplesList.push(tuples);
        }
      }
    }

    const validAgents = agentTuplesList.filter(t => t && t.length > 0);
    if (validAgents.length === 0) return null;

    return CETSimulator.buildFromTuplesList(validAgents, fallbackN, fallbackSymbols);
  }

  // Helper to build CETSimulator from a list of tuple arrays
  static buildFromTuplesList(validAgents, fallbackN = 2, fallbackSymbols = 2) {
    let maxState = 0;
    let maxWrite = 0;
    for (const tuples of validAgents) {
      for (const t of tuples) {
        if (t.nextState + 1 > maxState) maxState = t.nextState + 1;
        if (t.write > maxWrite) maxWrite = t.write;
      }
    }
    const computedSymbols = Math.max(fallbackSymbols, maxWrite + 1);
    for (const tuples of validAgents) {
      const nFromLength = Math.ceil(tuples.length / computedSymbols);
      if (nFromLength > maxState) maxState = nFromLength;
    }
    const computedN = Math.max(fallbackN, maxState);

    const tables = [];
    for (const tuples of validAgents) {
      const tbl = [];
      let idx = 0;
      for (let s = 0; s < computedN; s++) {
        const row = [];
        for (let sym = 0; sym < computedSymbols; sym++) {
          if (idx < tuples.length) {
            row.push(tuples[idx++]);
          } else {
            row.push({ write: 0, dir: 1, nextState: 0 });
          }
        }
        tbl.push(row);
      }
      tables.push(tbl);
    }

    return new CETSimulator({
      nStates: computedN,
      nSymbols: computedSymbols,
      agentCount: validAgents.length,
      tables: tables
    });
  }
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = CETSimulator;
}
