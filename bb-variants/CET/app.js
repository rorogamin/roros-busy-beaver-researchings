/**
 * Catch-Em-Turing Studio - Main Application Controller
 */

// Presets Collection
const PRESETS = {
  'cet1_2_counter_8540': {
    name: 'CET_1(2) Shift Counter (Col #18 @ 8540, Overflow Engine 🌌)',
    badge: 'CET_1(2) Counter 8540 🌌',
    description: 'Fascinating shift overflow counter! Agent 1 acts as a shift boundary anchor around x in [-13, 2], while Agent 2 acts as an active counter traversing the written track down to x = -122 and back. After Collision #18 at step 8,540 (cell x = -42), the counter continues running through huge multi-million step periods without true quasi-halting.',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB1LA_0LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 0LB1RA_1RA1LB
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }]
      ]
    ]
  },
  'cet1_2_champion_402': {
    name: 'CET_1(2) Glider Escape Champion (402 Steps - Speed-1 Glider ⚡)',
    badge: 'CET_1(2) Escape 402 ⚡',
    description: 'Astonishing clean glider escape! The two agents collide 25 times over 402 steps, culminating at cell x = -4. Following this final collision, Agent 2 enters an uninterrupted speed-1 leftward sprint into virgin tape (v2 = -1, p2(t) = 400 - t), while Agent 1 is trapped indefinitely in the bounded interval [-11, 3], guaranteeing zero collisions forever!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB1LA_0LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 1RB0RB_0LB1LA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2_champion_356': {
    name: 'CET_1(2) Glider Pair Record (356 Steps - Dual Drift +1 🚀)',
    badge: 'CET_1(2) Glider 356 🚀',
    description: 'Spectacular translated cycler record! 2 agents undergo 10 collisions over 356 steps, culminating at x = 154. At step 357, both agents synchronize into parallel rightward gliders moving at speed v = +1, permanently separated by exactly 2 cells (p1 - p2 = 2) drifting through virgin tape forever!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB0RB_1RA0LB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 0RB0RA_1LA1RB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet1_2_quad_shuttle': {
    name: 'CET_1(2) Quadratic Shuttle Cruiser (Col #6 @ 808k, Double Exp Recurrence 🚀)',
    badge: 'CET_1(2) Shuttle 808k 🚀',
    description: 'Profound infinite dynamic machine! Agent 2 cruises right at v = +1/2 while Agent 1 engages in an expanding triangular shuttle whose half-width expands by 2 cells per bounce. When the shuttle boundary hits the left wall, Agent 1 sprints right at v = 1 and catches Agent 2! Collisions occur at quadratic intervals: Col #4 at step 54 (cell 28), Col #5 at step 1,366 (cell 684), Col #6 at step 808,262 (cell 404,132), Col #7 at ~2.8×10^11 steps, Col #8 at ~6.9×10^22 steps! It collides infinitely many times at doubly-exponential intervals and never quasi-halts!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB0RB_1RA0LB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB0RB_1LA1RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2_nath_1399': {
    name: 'CET_1(2) Nath76 1399 (Col #9 @ 1399, Col #10 @ 6×10^105 🌌⚡)',
    badge: 'CET_1(2) Counter 1399 🌌',
    description: 'A mind-bending shift overflow counter! After colliding 9 times up to step 1,399 at x = -347, Agent 1 drifts left into virgin tape at v = -1/4. Meanwhile, Agent 2 executes an exact 351-bit binary counter on the line of 1s with recurrence T(N) = 2^(N+2) - N - 3. Around step 2^351 (~4.5×10^105), the counter will overflow, and Agent 2 will sprint left at speed 1, catching Agent 1 at step ~6.0×10^105 for Collision #10! It then bounces and expands to a ~10^105 bit counter, repeating ad infinitum without ever quasi-halting!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RA1RB_1LA0LB
      [
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1LA0RB_0LA1RB
      [
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet1_2x3_champion_1586': {
    name: 'CET_1(2,3) A100 Super Champion (1,586 Steps 🌈🔥)',
    badge: 'CET_1(2,3) WR 1,586 👑',
    description: 'Phenomenal NVIDIA A100 world record! 2 agents with 3 symbols weave through 46 collisions across 1,586 steps before locking into an infinite escape cycler with zero subsequent collisions forever!',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 2LB2RA2LB_2RA0LA1LB
      [
        [{ write: 2, dir: -1, nextState: 1 }, { write: 2, dir: 1, nextState: 0 }, { write: 2, dir: -1, nextState: 1 }],
        [{ write: 2, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 0RB0RA1RB_1LB0RA1RA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2_champion_188': {
    name: 'CET_1(2) A100 World Record (188 Steps - 79 Collisions 👑⚡)',
    badge: 'CET_1(2) WR 188 👑',
    description: 'New all-time world record! Shatters both Nath76\'s 110-step record and our earlier 156-step mark. 2 agents clash 79 times across 188 steps before locking into a period-3 translated cycler (+1 cell/cycle) drifting forever into blank tape!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB1LA_0LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 0RB0RB_0LB1RA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2x3_champion_1324': {
    name: 'CET_1(2,3) A100 Super Champion (1,324 Steps - 1320 Collisions 🌈🔥)',
    badge: 'CET_1(2,3) WR 1,324 👑',
    description: 'Astronomical Colab A100 discovery! 2 agents with 3 symbols weave through 1,320 collisions until step 1,324, then lock into an exact period-2 translated cycler drifting right (+2 cells/cycle) into virgin blank tape with 0 subsequent collisions forever!',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1LB2RA2RA_2RA2LB1RB
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 2, dir: 1, nextState: 0 }, { write: 2, dir: 1, nextState: 0 }],
        [{ write: 2, dir: 1, nextState: 0 }, { write: 2, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 1RB1LB1RA_2LA0LA0RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 2, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2_champion_156': {
    name: 'CET_1(2) A100 World Record (156 Steps - 34 Collisions 👑⚡)',
    badge: 'CET_1(2) WR 156 👑',
    description: 'New world record found on NVIDIA A100! Shatters Nath76\'s 110-step record. Agents experience 34 collisions across 156 steps before escaping into an infinite translated cycler drifting through virgin tape with 0 subsequent collisions!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LB1RA_1RA1LB
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 0LA1RB_1LA0RA
      [
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2_nath_110': {
    name: 'CET_1(2) Nath76 World Record (110 Steps - Translated Cycler 👑⚡)',
    badge: 'CET_1(2) 110 WR 👑',
    description: 'Phenomenal discovery by Nath76! Both agents engage in 6 collisions until step 110, then enter an exact translated cycler of period 23 drifting left by 1 cell every period (delta = -1). Because the heads drift into virgin zero tape 2 cells apart, they are mathematically proven by induction to never collide again!',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1LB1RA_1RA1LB
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 0RB0RA_1LA0LB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ]
    ]
  },
  'cet1_2_stationary_26': {
    name: 'CET_1(2) In-Place Cycle Champion (26 Steps - Quasi-Halts 🛡️)',
    badge: 'Stationary WR 26 🛡️',
    description: 'Absolute mathematical champion among all stationary cycles in CET_1(2)! 10 collisions occur, with the final collision at step 26 before locking into an exact period-4 stationary cycle at step 31 with zero subsequent collisions.',
    nStates: 2,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB0LB_0RA0LA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1LB0RB_1RA1LA
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet1_2x3_champion': {
    name: 'CET_1(2,3) World Champion (61 Steps - Quasi-Halts 🌈👑)',
    badge: 'CET_1(2,3) WR 61 👑',
    description: 'First ever world record in 2-state 3-symbol quasi-halting! Simulates 61 steps with 21 collisions across an active tape before colliding for the final time at step 61, locking into an exact period-2 collision-free cycle at step 64.',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LB1LA0RA_0RB1RA0LA
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 0RB1LB1LA_1LA2RB2LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }, { write: 2, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet4_holdout_counter': {
    name: 'CET(4) Genuine Holdout (Sublinear Counter L ~ sqrt(t) 🔥)',
    badge: 'CET(4) Holdout 🔥',
    description: 'A genuine unresolved holdout! Agent 1 acts as a reflective wall at cell 0 while Agent 2 performs complex ping-pong sweeps across a slowly expanding buffer of 1s (L ~ sqrt(t)), with 0 collisions and zero periodicity across 500k+ steps.',
    nStates: 4,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1LC1LC_1LC0LA_0RC1LC_0RA1LA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1RD0LB_0RD1LB_1LA1RC_1RC1RC
      [
        [{ write: 1, dir: 1, nextState: 3 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 3 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet4_champion_4_62b': {
    name: 'CET(4) 4.62B World Record (4,622,083,548 Steps 👑🔥🌌)',
    badge: 'CET(4) 4.62B 👑',
    trace: 'traces/cet4_4_62b.bin',
    description: 'Phenomenal all-time CET(4) world record! Shatters the previous 65.5M record by 70.5x! Runs for 4,622,083,548 steps before colliding at cell x = -19,208.',
    nStates: 4,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 1LC0LC_1LA1RB_0RB1LC_0RA0RA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1RC0RA_1RA1RB_1LC0RD_0RA0RC
      [
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 3 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet23_champion_1_52b': {
    name: 'CET(2,3) 1.52B World Record (1,528,952,999 Steps - 3 Symbols 👑🌈🔥)',
    badge: 'CET(2,3) 1.52B 👑',
    trace: 'traces/cet23_1_52b.bin',
    description: 'All-time 2-state 3-symbol world record! Shatters the previous 20,350-step record by 75,132x! Runs for 1,528,952,999 steps before colliding at cell x = 1,723.',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 1RB0RA2LB_2LA2RB1LB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }, { write: 2, dir: -1, nextState: 1 }],
        [{ write: 2, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 2RB0RA2RB_2LB1RA0RB
      [
        [{ write: 2, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }],
        [{ write: 2, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet4_champion_65m': {
    name: 'CET(4) Super Champion (65,579,412 Steps 🔥)',
    badge: 'BB(4) 65.5M 🏆',
    description: 'New all-time record! Beats the 49.18M mark by over 16.3 million steps. Agent 2 computes a 32.78M-step odometer before breaking out at unit speed to chase Agent 1, colliding at x = -32,789,706 on step 65,579,412.',
    nStates: 4,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LC0RA_0LD0RA_0LB0RA_0RA0RA
      [
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 3 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1RB1LD_1RC1RB_1LC1LA_0RC0RD
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 3 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 3 }]
      ]
    ]
  },
  'cet4_champion_49m': {
    name: 'CET(4) Mega Champion (49,184,559 Steps)',
    badge: 'BB(4) 49.1M 👑',
    description: 'Phenomenal 49.1M step discovery! Simulates 49,184,559 steps and creates 16,405,081 ones across a 16.4M cell tape before colliding at x = -16394853.',
    nStates: 4,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LB0LC_0LD0RA_0RA0RA_0RA0RA
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 3 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1RB1LD_1RC1RB_1LC1LA_0RC0RD
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 3 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 3 }]
      ]
    ]
  },
  'cet4_champion': {
    name: 'CET(4) 213k Discovery (213,393 Steps)',
    badge: '213k Steps',
    description: 'Found by 16-thread C hunter! Runs for 213,393 steps and creates 53,385 ones across a 53,386-cell tape before colliding at x = -53345.',
    nStates: 4,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: (1, RIGHT, 3), (0, RIGHT, 3), (1, LEFT, 3), (1, RIGHT, 0), (1, LEFT, 1), (0, LEFT, 1), (1, LEFT, 0), (0, RIGHT, 2)
      [
        [{ write: 1, dir: 1, nextState: 3 }, { write: 0, dir: 1, nextState: 3 }],
        [{ write: 1, dir: -1, nextState: 3 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 2 }]
      ],
      // Agent 2: (0, RIGHT, 1), (0, RIGHT, 3), (1, LEFT, 2), (0, RIGHT, 0), (0, RIGHT, 0), (1, LEFT, 2), (1, LEFT, 3), (0, RIGHT, 1)
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 3 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 3 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet1_bb': {
    name: 'CET(1) Champion (1 Step)',
    badge: 'BB(1) Record',
    description: 'Agent 1 starts at 0, Agent 2 starts at 2. They immediately collide at cell 1 on step 1.',
    nStates: 1,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      [[{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]],
      [[{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]]
    ]
  },
  'cet2_4sym_behemoth': {
    name: 'CET(2,4) Proven Behemoth (≥ 4.11 × 10²³ Steps)',
    badge: '≥ 411 Sextillion 🌌👑',
    description: 'Astronomical theoretical champion! Agent 2 computes the BBB(2,4) record for 205.7 sextillion steps before turning into a -1 cell/step translated cycler that chases down Agent 1 (-0.5 cells/step), proving a collision lower bound of ≥ 411,540,152,866,088,484,495,722 steps.',
    nStates: 2,
    nSymbols: 4,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LB0LB0RA0RA_1RA0LA0RA0RA (-0.5 cells/step glider)
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1RB2LA1RA1LB_0LB2RB3RB1LA (BBB(2,4) translated cycler)
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 2, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 2, dir: 1, nextState: 1 }, { write: 3, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet2_4sym_champion': {
    name: 'CET(2,4) Crazy Champion (14,068 Steps - 4 Symbols)',
    badge: 'BB(2,4) 14k 🌌',
    description: 'Found by multi-stage genetic annealing explorer! Simulates 14,068 steps and creates an intricate 4-symbol weave across 284 cells before colliding at cell -10.',
    nStates: 2,
    nSymbols: 4,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 3LB3RA3LA0LA_1RA1LA2LA2RB
      [
        [{ write: 3, dir: -1, nextState: 1 }, { write: 3, dir: 1, nextState: 0 }, { write: 3, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }, { write: 2, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 2RB1LB2LA1RB_1LB0RB1RB2RA
      [
        [{ write: 2, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }, { write: 2, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 1 }, { write: 2, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet2_3sym_champion_20k': {
    name: 'CET(2,3) World Champion (20,350 Steps - 3 Symbols 🌈🏆)',
    badge: 'BB(2,3) 20.3k 🌈',
    description: 'All-time 2-state 3-symbol record! Smashes the 8.7k record to 20,350 steps. Both agents paint symbols {0, 1, 2} across 394 cells [-226, 167] before colliding on cell x = -78.',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 2LB1LA2LA_2RB2LA0LB
      [
        [{ write: 2, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }, { write: 2, dir: -1, nextState: 0 }],
        [{ write: 2, dir: 1, nextState: 1 }, { write: 2, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB0LB1RB_2LA2LA1RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 2, dir: -1, nextState: 0 }, { write: 2, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet2_3sym_champion': {
    name: 'CET(2,3) Champion (8,786 Steps - 3 Symbols)',
    badge: 'BB(2,3) 8.7k 🌈',
    description: 'Phenomenal 2-state 3-symbol record discovered by parallel C hunter! Weaves 8,786 steps and paints symbols {0, 1, 2} across 325 cells before colliding at cell -192.',
    nStates: 2,
    nSymbols: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 2LB1LA2LA_2RB0LA0LB
      [
        [{ write: 2, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }, { write: 2, dir: -1, nextState: 0 }],
        [{ write: 2, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB0LB1LB_2LA2LA1RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 2, dir: -1, nextState: 0 }, { write: 2, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet2_champion': {
    name: 'CET(2) Champion (97 Steps)',
    badge: 'BB(2) Proven Maximum',
    description: 'Nath76 record: Verified by exhaustive search of all 16.7M machines. Collides at cell -1 after 97 steps.',
    nStates: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
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
    ]
  },
  'cet3_holdout_bouncer': {
    name: 'CET(3) Bouncer Holdout (Period 32,766 Non-Halter)',
    badge: 'CET(3) Bouncer 🛡️',
    description: 'Genuine non-translating bouncer holdout! Tightly confined within a 16-cell tape window [0..16], both agents bounce continuously without colliding for 32,766 steps per exact cycle.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0RC0LB_1LC1LA_1RB1LA
      [
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 0RC1RA_1LC1RB_0RB0LC
      [
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }]
      ]
    ]
  },
  'cet3_holdout_queue': {
    name: 'CET(3) Genuine Holdout (Active Hunt Queue Candidate 🔥)',
    badge: 'CET(3) Holdout 🔥',
    description: 'A genuine non-halting holdout from the active CET(3) hunt queue! Agent 1 oscillates between x = -1 and x = 0 while Agent 2 drifts rightward at a sub-luminal speed of v = 1/3 (steps: 3, 4, 3, 4, 5, 4, 5, 6...). Because v < 1, the speed-of-light escape decider correctly did NOT prune it, running for millions of steps without collision!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0LB0RA_0RA0RA_0RA0RA
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 0RB0RA_0RC0RA_0LA0RA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_3_09b': {
    name: 'CET(3) 3.09 BILLION World Record (3,092,745,703 Steps 👑🔥🌌)',
    badge: 'CET(3) 3.09B WR 👑',
    description: 'Brand new all-time CET(3) world record discovered by our parallel hunter! 3,092,745,703 steps (+336.8M over previous WR) before colliding at cell x = 9,857. Fully verified with instant native binary trace scrubbing.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    trace: 'traces/cet3_3_09b.bin',
    tables: [
      // Agent 1: 0LB0LC_1RB1LA_1RC0LA
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1LB0RC_1RA1LB_0LB1RC
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet3_champion_2_75b': {
    name: 'CET(3) 2.75 BILLION Mutation Champion (2,755,868,107 Steps 👑🔥🌌)',
    badge: 'CET(3) 2.75B WR 👑',
    description: 'All-time CET(3) record found by seeded 3-transition mutation search (independently verified): 2,755,868,107 steps, collides at x = -12115, tape span [-12776, 24895] with 37,670 ones. Run to End takes ~2 minutes in the browser.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    trace: 'traces/cet3_2_75b.bin',
    tables: [
      // Agent 1: 1RB0LC_1LA1RB_0RB1LC
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }]
      ],
      // Agent 2: 1RB0RB_1LB0LC_1RB0RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_26_1m': {
    name: 'CET(3) 26.1M Supreme World Record (26,121,565 Steps 👑🔥🌌)',
    badge: 'CET(3) 26.1M WR 👑',
    description: 'All-time CET(3) Supreme World Record (> 2.61 × 10^7 steps)! Discovered by our 16-thread Joint TNF Ultra Search, shattering Nath76\'s 9.44M mark by 2.76x! Simulates 26,121,565 steps across a 7,275-cell active tape [-593, 6681], painting 7,273 ones before colliding at cell x = -567!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LC_1LC1RB_1RC1LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1RB1LB_0RC0RA_1LC0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_24_9m': {
    name: 'CET(3) 24.9M Ultra World Record (24,979,202 Steps 👑🔥)',
    badge: 'CET(3) 24.9M WR 👑',
    description: '24,979,202-step CET(3) monster discovered by our Joint TNF Ultra Search! Collides at cell x = 816 after 24,979,202 steps.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0LB0LA_1RA1RC_0LC1RB
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 1RB1LA_1RC0RC_0LA1RC
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet3_champion_24_1m': {
    name: 'CET(3) 24.1M Omega World Record (24,120,601 Steps 👑🔥🌌)',
    badge: 'CET(3) 24.1M WR 👑',
    description: 'All-time CET(3) World Record (> 2.41 × 10^7 steps)! Discovered by our 16-thread Joint TNF Ultra Search, shattering Nath76\'s 9.44M mark by 2.55x! Simulates 24,120,601 steps across a 9,026-cell active tape [-399, 8626], painting 9,025 ones before colliding at cell x = 201!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LA_1RB0LC_0LB1LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1RB1RA_0RC1LB_1LA1RA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_14_8m': {
    name: 'CET(3) 14.8M TNF Discovery (14,836,405 Steps ⚡)',
    badge: 'CET(3) 14.8M ⚡',
    description: 'Compact high-density 14.83M-step CET(3) discovery! Simulates 14,836,405 steps across a 3,084-cell active tape [-222, 2861], painting 3,082 ones before colliding at cell x = 225!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LA_1RB0LC_0LA1LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 1RB1LC_0RC0RA_1LB1RC
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet3_champion_12_0m': {
    name: 'CET(3) 12.0M TNF Discovery (12,095,922 Steps ⚡)',
    badge: 'CET(3) 12.0M ⚡',
    description: 'Massive 12.09M-step CET(3) discovery! Simulates 12,095,922 steps across an 8,203-cell active tape [0, 8202], painting 8,201 ones before colliding at cell x = 5,254!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB1RC_1RC0LA_1LB1RC
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ],
      // Agent 2: 0RB1RB_0RC0RB_1LC1RA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_23_5m': {
    name: 'CET(3) 23.5M Super Runner-Up (23,528,345 Steps 🏆🔥)',
    badge: 'CET(3) 23.5M 🏆',
    description: 'Phenomenal 23.52M-step CET(3) odometer! Discovered by Joint TNF Ultra Search. Simulates 23,528,345 steps across a 7,372-cell active tape [-6487, 884], painting 7,370 ones before colliding at cell x = 859!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0RA_1LC0LC_1RC0LB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB1LA_0LC1RC_1LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_22_4m': {
    name: 'CET(3) 22.4M Mega World Record (22,428,251 Steps 👑🔥🌌)',
    badge: 'CET(3) 22.4M WR 👑',
    description: 'All-time CET(3) World Record (> 2.24 × 10^7 steps)! Discovered by our 16-thread Joint TNF Ultra Search, shattering Nath76\'s 9.44M mark by 2.37x! Simulates 22,428,251 steps across an 8,767-cell active tape [-2068, 6698], painting 8,766 ones before colliding at cell x = 3,349!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LA_0LC1LA_1RB1RC
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ],
      // Agent 2: 1RB0LB_1RC0RB_1LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_16_7m': {
    name: 'CET(3) 16.7M Super Champion (16,714,775 Steps 🏆🔥)',
    badge: 'CET(3) 16.7M 🏆',
    description: 'First CET(3) machine to break the 10^7 barrier! Discovered by Joint TNF Ultra Search. Simulates 16,714,775 steps across a 6,180-cell active tape [-704, 5475], painting 6,179 ones before colliding at cell x = -681!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LC_1LC1RB_1RC1LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 0RB0RA_1RC0RC_1LC0RB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_16_5m': {
    name: 'CET(3) 16.5M Super Runner-Up (16,511,187 Steps 🌟)',
    badge: 'CET(3) 16.5M 🌟',
    description: 'Massive 16.51M-step CET(3) odometer! Simulates 16,511,187 steps across a 7,532-cell active tape [-599, 6932], painting 7,531 ones before colliding at cell x = -575!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB1LC_1LA1RB_0LA0LA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 0RB0RC_1LA1RC_1LC0RA
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_9_4m': {
    name: 'CET(3) Nath76 Former Record (9,448,838 Steps 👑)',
    badge: 'CET(3) 9.44M 👑',
    description: 'Phenomenal all-time world record discovered by Nath76 via Joint Tree Normal Form (TNF) search! Simulates 9,448,838 steps across a 7,416-cell active tape [-5224, 2191], painting 6,840 ones before colliding at cell x = -4,074!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0RB0LC_0LC1RA_1LA0LB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB1LC_0LC0RC_1RA1LA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion_4_6m': {
    name: 'CET(3) Nath76 Runner-Up (4,657,368 Steps 🏆)',
    badge: 'CET(3) 4.65M 👑',
    description: 'Phenomenal new all-time world record! Discovered by Nath76 using Tree Normal Form (TNF) branch-and-bound search. Simulates 4,657,368 steps across a 2,115-cell active tape, painting 2,114 ones before colliding at cell x = -224!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    haltRule: 'collision',
    tables: [
      // Agent 1: 0LB0LB_0RC1LA_1LB1RC
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ],
      // Agent 2: 0RB1RC_1RC0RA_1LC0LB
      [
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_3_7m': {
    name: 'CET(3) Mega Champion (3,746,207 Steps 👑🔥)',
    badge: 'CET(3) 3.74M 👑',
    description: 'Phenomenal 3.74M all-time world record! Discovered by fresh-space parallel hunter across 55M machines. Runs 3,746,207 steps, creating 3,373 ones across a 3,372-cell tape before colliding at cell x = -9!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1LC1LA_1LA0LC_1RC0LB
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 0LB0RA_1RA1LB_0RA0LB
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_2m': {
    name: 'CET(3) 2.03M Discovery (2,033,240 Steps 🌟)',
    badge: 'CET(3) 2.03M 🌟',
    description: 'Fresh Monte-Carlo discovery! Executes 2,033,240 steps with over 1.07 million direction reversals. Both agents dynamically use all 3 states across a 1,315-cell active tape [-469, 845] before colliding at x = -374.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LC1LC_1RB0LA_0RB0LC
      [
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }]
      ],
      // Agent 2: 1LC1RA_1RC1LA_1RA0RB
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet3_champion_717k': {
    name: 'CET(3) World Record Discovery (717,751 Steps 👑)',
    badge: 'CET(3) 717k 👑',
    description: 'Phenomenal new all-time breakthrough! Simulates 717,751 steps across 1,014 cells with 359,342 reversals before finally colliding at cell x = 155, nearly tripling the 265k record!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LB1LA_0LC0LB_1RB1RC
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ],
      // Agent 2: 1LC0RC_1RA1LB_0LB1RC
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet3_champion_265k': {
    name: 'CET(3) World Record Champion (265,383 Steps 👑)',
    badge: 'CET(3) 265k 👑',
    description: 'Phenomenal Nath76 all-time breakthrough! Simulates 265,383 steps across 626 tape cells before colliding at cell x = 89, shattering the previous 9,137 record by 29x!',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 0LC1LA_0LC0LB_1RB1RC
      [
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ],
      // Agent 2: 1RC0RC_1RA1LB_0LB1RC
      [
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'cet3_champion_9k': {
    name: 'CET(3) Champion (9,137 Steps ★)',
    badge: 'BB(3) 9.1k Record ★',
    description: 'Phenomenal new discovery! Shatters the previous 6,065 record, simulating 9,137 steps across 325 cells before colliding at cell -233.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: 1RB0LC_1RA0LB_0RB1LC
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }]
      ],
      // Agent 2: 1RB1LA_1RC1RB_0LA0LA
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ]
    ]
  },
  'cet3_champion': {
    name: 'CET(3) Champion (6,065 Steps)',
    badge: 'BB(3) Champion ★',
    description: 'Discovered by parallel genetic search! Simulates 6,065 steps and paints 2,605 cells before colliding at x = -2591.',
    nStates: 3,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      // Agent 1: (1, LEFT, 2), (1, RIGHT, 1), (1, LEFT, 0), (0, LEFT, 1), (1, RIGHT, 0), (1, RIGHT, 0)
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 0 }]
      ],
      // Agent 2: (1, RIGHT, 2), (1, LEFT, 0), (1, LEFT, 1), (0, RIGHT, 1), (0, RIGHT, 1), (0, LEFT, 2)
      [
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }]
      ]
    ]
  },
  'cet2_77': {
    name: 'CET(2) Runner-Up (77 Steps)',
    badge: '77 Steps',
    description: 'Long-running dual weaver with broad tape expansion before converging to collide at cell 1.',
    nStates: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'cet2_49': {
    name: 'CET(2) Oscillating Weaver (49 Steps)',
    badge: '49 Steps',
    description: 'Agents oscillate back and forth exchanging tape marks across a 12-cell span before colliding at cell -1.',
    nStates: 2,
    agentCount: 2,
    initialPositions: [0, 2],
    tables: [
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'mcet33_champion_34k': {
    name: 'MCET(3,3) All-Agent Champion (34,399 Steps 👑)',
    badge: 'MCET(3,3) 34.3k 👑',
    description: 'Nath76 milestone! 3 agents, 3 states, 3 symbols: sim runs 34,399 steps with haltRule="all", traversing across 11,493 tape cells before all 3 agents collide simultaneously at cell x = 11,469.',
    nStates: 3,
    nSymbols: 3,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 2RB2RC1LA_0LA2RA2RB_0LA2RA0LA
      [
        [{ write: 2, dir: 1, nextState: 1 }, { write: 2, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      // Agent 2: 2LC2RC1RA_1LA0RA0LA_1LA1LA2RB
      [
        [{ write: 2, dir: -1, nextState: 2 }, { write: 2, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 1 }]
      ],
      // Agent 3: 2RB1LC2RC_0RC1RC1RA_1LA2RA2RC
      [
        [{ write: 2, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 2 }, { write: 2, dir: 1, nextState: 2 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 2, dir: 1, nextState: 0 }, { write: 2, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'mcet3_champion_211m': {
    name: 'MCET(3) 211M World Record (211,190,346 Steps 👑🔥🌌)',
    badge: 'MCET(3) 211M 👑',
    description: 'Phenomenal all-time MCET(3) world record discovered by our parallel hunter, shattering the previous 4.23M record by 49.8x! 3 agents coordinate across thousands of tape cells for 211,190,346 steps before ALL 3 agents simultaneously collide on cell x = 13,350.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1LC1LA_1RA1RB_0RB0RA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1LC1LB_1RC1RB_0LC0RA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 3: 0LA1RB_0RC1RB_0RA1RC
      [
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'mcet3_champion_4_2m': {
    name: 'MCET(3) 4.2M Super Champion (4,239,504 Steps 🏆👑)',
    badge: 'MCET(3) 4.2M 👑',
    description: 'Astronomical milestone! Smashes all previous records to 4,239,504 steps (surpassing even CET(3) 2-agent)! 3 agents execute 4.23 million steps of multi-agent resonance across 2,158 tape cells before ALL 3 simultaneously collide on cell x = 1490.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1LC1LA_1RA1RB_0RB0RA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 2: 1LC1LB_1RB0RA_0LC0RA
      [
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      // Agent 3: 0LA1RB_0RC1RB_0RA1RC
      [
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }]
      ]
    ]
  },
  'mcet3_champion_1_3m': {
    name: 'MCET(3) 1.3M World Champion (1,300,013 Steps 🏆👑)',
    badge: 'MCET(3) 1.3M 👑',
    description: 'Astronomical milestone! Smashes the 14.4k record by over 90x! 3 agents weave through complex multi-agent tape state for 1,300,013 steps before ALL 3 agents simultaneously collide on cell x = -709 across a 1,643-cell active tape.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1RA0LA_1LC1LB_1LC1LB
      [
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }]
      ],
      // Agent 2: 1RB1LA_1RC1LB_0LA0RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 3: 0RC1RB_0LA0LC_1RB0LC
      [
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 2 }]
      ]
    ]
  },
  'mcet3_champion_14k': {
    name: 'MCET(3) Champion (14,417 Steps - All Agents 🏆)',
    badge: 'MCET(3) 14.4k 👑',
    description: 'All-time MCET(3) record! 3 agents coordinate across 7,214 cells for 14,417 steps before ALL 3 agents simultaneously collide on cell x = -7205.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1RC0RB_1RB1LA_1LA0LC
      [
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 2 }]
      ],
      // Agent 2: 0RA0RC_0LC1LA_1LB0RB
      [
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 3: 1LA1RC_0LB1LA_0LB1RA
      [
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'mcet3_champion_12k': {
    name: 'MCET(3) Nath76 Champion (12,733 Steps)',
    badge: 'MCET(3) 12.7k 👑',
    description: 'Found by Nath76! 3 agents weave and sweep across 6,370 cells for 12,733 steps before ALL 3 simultaneously collide on cell x = -6363.',
    nStates: 3,
    nSymbols: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1RC0RB_1RC1LB_1LA0LC
      [
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 1, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: -1, nextState: 2 }]
      ],
      // Agent 2: 0RA0RC_0LC1LA_1LB0RB
      [
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 2 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      // Agent 3: 1LA0RC_1LB1LA_0LA1RB
      [
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ]
    ]
  },
  'mcet3_champion': {
    name: 'MCET(3) All-Agent Champion (8,899 Steps)',
    badge: 'MCET(3) Champion 🏆',
    description: 'Discovered by C multi-core hunter! Simulates 8,899 steps until ALL 3 agents simultaneously collide on cell x = 1781 (haltRule: all).',
    nStates: 3,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    haltRule: 'all',
    tables: [
      // Agent 1: 1RB0RB_1RC0LC_1LA1RB
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 2 }, { write: 0, dir: -1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }]
      ],
      // Agent 2: 0RC1RC_1LA1RC_0LB1RA
      [
        [{ write: 0, dir: 1, nextState: 2 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 2 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ],
      // Agent 3: 0LC0RB_1LB0RB_0RA0RA
      [
        [{ write: 0, dir: -1, nextState: 2 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: 1, nextState: 0 }, { write: 0, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'mcet3_cascade': {
    name: 'MCET(3) 3-Agent Cascade (36 Steps)',
    badge: 'MCET: 3 Agents',
    description: '3 agents (positions 0, 2, 4) navigating simultaneous read/writes with writing priority.',
    nStates: 2,
    agentCount: 3,
    initialPositions: [0, 2, 4],
    tables: [
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }]
      ],
      [
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      [
        [{ write: 1, dir: -1, nextState: 0 }, { write: 0, dir: 1, nextState: 1 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ]
    ]
  },
  'mcet4_squeeze': {
    name: 'MCET(4) 4-Agent Squeeze (52 Steps)',
    badge: 'MCET: 4 Agents',
    description: '4 agents starting at [-4, -2, 2, 4] moving inwards and weaving through each other until collision.',
    nStates: 2,
    agentCount: 4,
    initialPositions: [-4, -2, 2, 4],
    tables: [
      [
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }],
        [{ write: 0, dir: -1, nextState: 1 }, { write: 1, dir: 1, nextState: 0 }]
      ],
      [
        [{ write: 1, dir: 1, nextState: 0 }, { write: 0, dir: -1, nextState: 1 }],
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: 1, nextState: 0 }]
      ],
      [
        [{ write: 0, dir: -1, nextState: 0 }, { write: 1, dir: 1, nextState: 1 }],
        [{ write: 1, dir: 1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }]
      ],
      [
        [{ write: 1, dir: -1, nextState: 1 }, { write: 0, dir: -1, nextState: 0 }],
        [{ write: 0, dir: 1, nextState: 1 }, { write: 1, dir: -1, nextState: 0 }]
      ]
    ]
  }
};

class AppController {
  constructor() {
    this.sim = new CETSimulator();
    this.audio = new CETAudio();

    this.activeAgentTab = 0;
    this.isPlaying = false;
    this.playSpeed = 10; // steps per frame or delay
    this.animFrameId = null;
    this.lastFrameTime = 0;

    // Web Worker for Hunter
    this.hunterWorker = null;
    this.hunterRunning = false;
    this.hunterStats = { scanned: 0, rate: 0, bestStep: 0 };
    this.leaderboard = [];

    this.init();
  }

  init() {
    // Canvas & Diagram
    const canvas = document.getElementById('spacetimeCanvas');
    this.diagram = new SpaceTimeDiagram(canvas, this.sim);

    // 1D Tape Visualizer
    const tapeContainer = document.getElementById('tape1dContainer');
    this.tape1d = new Tape1DVisualizer(tapeContainer, this.sim);

    // State Graph
    const graphContainer = document.getElementById('stateGraphContainer');
    this.stateGraph = new StateGraphVisualizer(graphContainer);

    // Diagram Callbacks
    this.diagram.onScrub = (step) => {
      this.scrubTo(step);
    };

    this.diagram.onHover = (info) => {
      this.updateHoverInfo(info);
    };

    // Load default preset (matching the first option in preset dropdown)
    const presetSelect = document.getElementById('presetSelect');
    const defaultPreset = presetSelect ? presetSelect.value : 'cet4_champion_49m';
    this.loadPreset(defaultPreset);

    this.setupUIListeners();
    this.setupWorker();
    this.setupKeyboardShortcuts();

    // Initial render
    this.updateAllViews();
  }

  setupUIListeners() {
    // Mode Switcher (CET vs MCET)
    document.querySelectorAll('.mode-tab-btn').forEach(btn => {
      btn.addEventListener('click', (e) => {
        document.querySelectorAll('.mode-tab-btn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        const mode = btn.dataset.mode;
        if (mode === 'cet') {
          this.setModeCET();
        } else {
          this.setModeMCET();
        }
      });
    });

    // Presets Dropdown
    const presetSelect = document.getElementById('presetSelect');
    if (presetSelect) {
      presetSelect.addEventListener('change', (e) => {
        if (e.target.value) {
          this.loadPreset(e.target.value);
        }
      });
    }

    // Halting Condition Dropdown (CET_0 Normal vs CET_1 Quasi-Halting)
    const selectHaltCondition = document.getElementById('selectHaltCondition');
    if (selectHaltCondition) {
      selectHaltCondition.addEventListener('change', (e) => {
        this.sim.haltCondition = e.target.value;
        const qCard = document.getElementById('metricQuasihaltCard');
        if (qCard) qCard.style.display = (e.target.value === 'quasihalt') ? 'flex' : 'none';
        this.sim.reset();
        this.updateAllViews();
        this.diagram.fitToView();
      });
    }

    // Playback buttons
    document.getElementById('btnPlayPause').addEventListener('click', () => this.togglePlay());
    document.getElementById('btnStepFwd').addEventListener('click', () => this.stepForward());
    document.getElementById('btnStepBack').addEventListener('click', () => this.stepBackward());
    document.getElementById('btnReset').addEventListener('click', () => this.resetSimulation());
    document.getElementById('btnJumpEnd').addEventListener('click', () => this.jumpToEnd());

    const btnContinueQuasihalt = document.getElementById('btnContinuePostQuasihalt');
    if (btnContinueQuasihalt) {
      btnContinueQuasihalt.addEventListener('click', () => {
        this.continuePostQuasihalt(500);
      });
    }

    // Timeline Slider
    const timelineSlider = document.getElementById('timelineSlider');
    timelineSlider.addEventListener('input', (e) => {
      this.scrubTo(parseInt(e.target.value, 10));
    });

    // Speed Controls: Textbox, Logarithmic Slider & Max Button
    const speedInput = document.getElementById('speedInput');
    const speedSlider = document.getElementById('speedSlider');
    const btnSpeedMax = document.getElementById('btnSpeedMax');

    if (speedSlider) {
      speedSlider.addEventListener('input', (e) => {
        const val = parseInt(e.target.value, 10);
        // Map 0..800 logarithmically to 1..100,000,000 (100000k/s)
        const speed = Math.round(Math.pow(10, val / 100));
        this.setPlaySpeed(speed, true, false);
      });
    }

    if (speedInput) {
      const applyInput = () => {
        const parsed = this.parseSpeedText(speedInput.value);
        this.setPlaySpeed(parsed, true, true);
      };
      speedInput.addEventListener('change', applyInput);
      speedInput.addEventListener('blur', applyInput);
      speedInput.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
          e.preventDefault();
          applyInput();
          speedInput.blur();
        }
      });
    }

    if (btnSpeedMax) {
      btnSpeedMax.addEventListener('click', () => {
        this.setPlaySpeed(100000000, true, true); // 100,000k/s
      });
    }

    // Set initial speed
    this.setPlaySpeed(20, true, true);

    // Randomize Button & Options
    document.getElementById('btnRandomize').addEventListener('click', () => this.randomizeCurrent());
    document.getElementById('btnMutate').addEventListener('click', () => this.mutateCurrent());

    // N States Setter
    document.getElementById('btnNMinus').addEventListener('click', () => this.changeN(-1));
    document.getElementById('btnNPlus').addEventListener('click', () => this.changeN(1));

    // Symbols Setter
    document.getElementById('btnSymMinus').addEventListener('click', () => this.changeSymbols(-1));
    document.getElementById('btnSymPlus').addEventListener('click', () => this.changeSymbols(1));

    // Agent Count Setter (MCET)
    document.getElementById('btnAgentMinus').addEventListener('click', () => this.changeAgentCount(-1));
    document.getElementById('btnAgentPlus').addEventListener('click', () => this.changeAgentCount(1));

    // Fit View & Zoom Buttons
    document.getElementById('btnZoomIn').addEventListener('click', () => {
      this.diagram.zoomAroundPoint(this.diagram.width / 2, this.diagram.height / 2, 1.25);
    });
    document.getElementById('btnZoomOut').addEventListener('click', () => {
      this.diagram.zoomAroundPoint(this.diagram.width / 2, this.diagram.height / 2, 0.8);
    });
    document.getElementById('btnFitView').addEventListener('click', () => {
      this.diagram.fitToView();
    });

    // Diagram Options
    const checkAutoFollow = document.getElementById('checkAutoFollow');
    if (checkAutoFollow) {
      checkAutoFollow.addEventListener('change', (e) => {
        this.diagram.options.autoCenterRunning = e.target.checked;
      });
    }

    document.getElementById('selectTheme').addEventListener('change', (e) => {
      this.diagram.options.theme = e.target.value;
      this.diagram.draw();
    });

    document.getElementById('selectOrientation').addEventListener('change', (e) => {
      this.diagram.options.timeDirection = e.target.value;
      this.diagram.draw();
    });

    document.getElementById('checkWorldlines').addEventListener('change', (e) => {
      this.diagram.options.showWorldlines = e.target.checked;
      this.diagram.draw();
    });

    document.getElementById('checkTapeCells').addEventListener('change', (e) => {
      this.diagram.options.showTapeCells = e.target.checked;
      this.diagram.draw();
    });

    // Space-Time Width Aspect Ratio Slider & Textbox (unlimited)
    const sliderWidthScale = document.getElementById('sliderWidthScale');
    const inputWidthScale = document.getElementById('inputWidthScale');

    const applyWidthMultiplier = (val, fromInput = false) => {
      if (typeof val === 'string' && (val.toLowerCase() === 'auto' || val.trim() === '')) {
        this.diagram.autoHalfWidth = true;
        this.diagram.fitToView();
        if (inputWidthScale) inputWidthScale.value = 'Auto';
        return;
      }
      const factor = Math.max(0.01, parseFloat(val) || 1.0);
      this.diagram.scaleXMultiplier = factor;
      this.diagram.autoHalfWidth = false; // User manually set a width
      if (sliderWidthScale && !fromInput) {
        sliderWidthScale.value = Math.min(1000, factor);
      }
      if (inputWidthScale && !fromInput) {
        inputWidthScale.value = `${Math.round(factor * 10) / 10}x`;
      }
      this.diagram.draw();
    };

    if (sliderWidthScale) {
      sliderWidthScale.addEventListener('input', (e) => {
        applyWidthMultiplier(e.target.value, false);
      });
    }

    if (inputWidthScale) {
      inputWidthScale.addEventListener('change', (e) => {
        const raw = e.target.value.replace(/x/i, '').trim();
        applyWidthMultiplier(raw, true);
        if (raw.toLowerCase() !== 'auto') {
          e.target.value = `${this.diagram.scaleXMultiplier}x`;
        }
      });
      inputWidthScale.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
          inputWidthScale.blur();
        }
      });
    }

    // Export PNG
    document.getElementById('btnExportPng').addEventListener('click', () => this.exportDiagramPNG());

    // Audio Toggle
    const btnAudio = document.getElementById('btnAudioToggle');
    btnAudio.addEventListener('click', () => {
      const on = this.audio.toggle();
      btnAudio.textContent = on ? '🔊 Audio ON' : '🔇 Audio OFF';
      btnAudio.classList.toggle('active', on);
    });

    // Active Agent Format Input & Copy
    const agentFormatInput = document.getElementById('agentFormatInput');
    const btnApplyAgentFormat = document.getElementById('btnApplyAgentFormat');
    const btnCopyAgentFormat = document.getElementById('btnCopyAgentFormat');
    const agentFeedback = document.getElementById('agentFormatFeedback');

    const showAgentFeedback = (msg, isSuccess = true) => {
      if (!agentFeedback) return;
      agentFeedback.textContent = msg;
      agentFeedback.className = `agent-format-feedback ${isSuccess ? 'success' : 'error'}`;
      clearTimeout(this._agentFbTimeout);
      this._agentFbTimeout = setTimeout(() => {
        agentFeedback.textContent = '';
      }, 3000);
    };

    if (btnApplyAgentFormat && agentFormatInput) {
      const applyAgentFormat = () => {
        const val = agentFormatInput.value.trim();
        const ok = this.sim.setAgentFromTuples(this.activeAgentTab, val);
        if (ok) {
          showAgentFeedback(`✓ Agent ${this.activeAgentTab + 1} updated`, true);
          this.onTableModified(true);
        } else {
          showAgentFeedback('✖ Invalid format: expected (w, dir, s)...', false);
        }
      };

      btnApplyAgentFormat.addEventListener('click', applyAgentFormat);
      agentFormatInput.addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
          e.preventDefault();
          applyAgentFormat();
        }
      });
    }

    if (btnCopyAgentFormat && agentFormatInput) {
      btnCopyAgentFormat.addEventListener('click', () => {
        navigator.clipboard.writeText(agentFormatInput.value).then(() => {
          showAgentFeedback('✓ Copied!', true);
        }).catch(() => {
          showAgentFeedback('✖ Copy failed', false);
        });
      });
    }

    // Full Machine Notation Apply & Copy
    const rawTextInput = document.getElementById('rawTextInput');
    const btnApplyRawText = document.getElementById('btnApplyRawText');
    const btnCopyRawText = document.getElementById('btnCopyRawText');
    const fullFeedback = document.getElementById('fullNotationFeedback');

    const showFullFeedback = (msg, isSuccess = true) => {
      if (!fullFeedback) return;
      fullFeedback.textContent = msg;
      fullFeedback.className = `agent-format-feedback ${isSuccess ? 'success' : 'error'}`;
      clearTimeout(this._fullFbTimeout);
      this._fullFbTimeout = setTimeout(() => {
        fullFeedback.textContent = '';
      }, 3000);
    };

    if (btnApplyRawText && rawTextInput) {
      btnApplyRawText.addEventListener('click', () => {
        const txt = rawTextInput.value.trim();
        const parsed = CETSimulator.fromText(txt, this.sim.nStates);
        if (parsed) {
          this.sim = parsed;
          if (parsed.agentCount > 2) {
            this.sim.haltRule = 'all';
          }
          this.diagram.sim = this.sim;
          this.tape1d.sim = this.sim;
          this.sim.reset();
          this.diagram.scrubStep = 0;
          this.updateAllViews();
          this.diagram.fitToView();
          showFullFeedback(`✓ Loaded ${parsed.agentCount} agents (n=${parsed.nStates})`, true);
        } else {
          showFullFeedback('✖ Could not parse notation', false);
        }
      });
    }

    if (btnCopyRawText && rawTextInput) {
      btnCopyRawText.addEventListener('click', () => {
        navigator.clipboard.writeText(rawTextInput.value).then(() => {
          showFullFeedback('✓ Copied all!', true);
        }).catch(() => {
          showFullFeedback('✖ Copy failed', false);
        });
      });
    }

    const btnCopyBBChallenge = document.getElementById('btnCopyBBChallenge');
    if (btnCopyBBChallenge) {
      btnCopyBBChallenge.addEventListener('click', () => {
        const bbStr = this.sim.toBBChallengeFormat();
        navigator.clipboard.writeText(bbStr).then(() => {
          showFullFeedback('✓ Copied bbchallenge pipe format!', true);
        }).catch(() => {
          showFullFeedback('✖ Copy failed', false);
        });
      });
    }

    // Hunter UI
    document.getElementById('btnToggleHunter').addEventListener('click', () => this.toggleHunter());
    document.getElementById('hunterStrategy').addEventListener('change', (e) => {
      if (this.hunterWorker) {
        this.hunterWorker.postMessage({
          command: 'updateConfig',
          params: { mode: e.target.value }
        });
      }
    });
  }

  setupKeyboardShortcuts() {
    window.addEventListener('keydown', (e) => {
      if (['INPUT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;
      if (e.code === 'Space') {
        e.preventDefault();
        this.togglePlay();
      } else if (e.code === 'ArrowRight') {
        e.preventDefault();
        this.stepForward();
      } else if (e.code === 'ArrowLeft') {
        e.preventDefault();
        this.stepBackward();
      } else if (e.code === 'Home') {
        e.preventDefault();
        this.resetSimulation();
      } else if (e.code === 'End') {
        e.preventDefault();
        this.jumpToEnd();
      } else if (e.key === 'r' || e.key === 'R') {
        this.randomizeCurrent();
      } else if (e.key === 'm' || e.key === 'M') {
        const btn = document.getElementById('btnAudioToggle');
        btn.click();
      }
    });
  }

  setupWorker() {
    try {
      this.hunterWorker = new Worker('hunter_worker.js');
      this.hunterWorker.onmessage = (e) => {
        const data = e.data;
        if (data.type === 'progress') {
          this.hunterStats.scanned += data.checked;
          this.hunterStats.bestStep = Math.max(this.hunterStats.bestStep, data.currentBestStep);
          this.updateHunterUI();

          if (data.newRecords && data.newRecords.length > 0) {
            for (const rec of data.newRecords) {
              this.addLeaderboardEntry(rec);
            }
          }
        }
      };
    } catch (e) {
      console.warn('Web Worker not supported in this environment, hunter runs in fallback mode.', e);
    }
  }

  toggleHunter() {
    this.hunterRunning = !this.hunterRunning;
    const btn = document.getElementById('btnToggleHunter');
    const status = document.getElementById('hunterStatusText');

    if (this.hunterRunning) {
      btn.textContent = '⏹ Stop Hunter';
      btn.classList.add('btn-danger');
      status.textContent = 'Hunting in background...';

      if (this.hunterWorker) {
        this.hunterWorker.postMessage({
          command: 'start',
          params: {
            nStates: this.sim.nStates,
            agentCount: this.sim.agentCount,
            initialPositions: this.sim.initialPositions,
            maxSteps: 10000,
            mode: document.getElementById('hunterStrategy').value
          }
        });
      }
    } else {
      btn.textContent = '▶ Start Auto-Hunter';
      btn.classList.remove('btn-danger');
      status.textContent = 'Idle';

      if (this.hunterWorker) {
        this.hunterWorker.postMessage({ command: 'stop' });
      }
    }
  }

  updateHunterUI() {
    const elScanned = document.getElementById('hunterScannedCount');
    const elBest = document.getElementById('hunterBestStep');
    if (elScanned) elScanned.textContent = this.hunterStats.scanned.toLocaleString();
    if (elBest) elBest.textContent = this.hunterStats.bestStep;
  }

  addLeaderboardEntry(record) {
    this.leaderboard.unshift(record);
    if (this.leaderboard.length > 20) this.leaderboard.pop();

    const tbody = document.getElementById('leaderboardTbody');
    if (!tbody) return;

    let html = '';
    this.leaderboard.forEach((rec, idx) => {
      html += `
        <tr>
          <td><span class="rank-badge">#${idx + 1}</span></td>
          <td><strong>${rec.step}</strong> steps</td>
          <td>n=${rec.nStates}, ${rec.agentCount} ag</td>
          <td>pos ${rec.pos}</td>
          <td><button class="btn btn-xs btn-primary btn-load-record" data-idx="${idx}">Load</button></td>
        </tr>
      `;
    });
    tbody.innerHTML = html;

    tbody.querySelectorAll('.btn-load-record').forEach(b => {
      b.addEventListener('click', (e) => {
        const idx = parseInt(e.target.dataset.idx, 10);
        this.loadRecord(this.leaderboard[idx]);
      });
    });
  }

  loadRecord(record) {
    this.sim.nStates = record.nStates;
    this.sim.nSymbols = record.nSymbols || 2;
    this.sim.agentCount = record.agentCount;
    this.sim.initialPositions = record.agentCount === 2 ? [0, 2] : record.initialPositions;
    this.sim.tables = JSON.parse(JSON.stringify(record.tables));
    this.sim.haltRule = record.agentCount > 2 ? 'all' : 'first_pair';
    // Reset to Step 0: do not automatically run or draw diagram until user clicks Play / Step / Run
    this.sim.reset();
    this.diagram.scrubStep = 0;

    this.activeAgentTab = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  loadPreset(key) {
    const preset = PRESETS[key];
    if (!preset) return;

    this.sim.nStates = preset.nStates;
    this.sim.nSymbols = preset.nSymbols || 2;
    this.sim.agentCount = preset.agentCount;
    this.sim.initialPositions = [...preset.initialPositions];
    this.sim.tables = JSON.parse(JSON.stringify(preset.tables));
    this.sim.haltRule = preset.haltRule || (preset.agentCount > 2 ? 'all' : 'first_pair');

    // Auto-detect quasihalt presets
    const isQuasihaltPreset = key.startsWith('cet1_');
    this.sim.haltCondition = isQuasihaltPreset ? 'quasihalt' : 'normal';
    const selectHaltCondition = document.getElementById('selectHaltCondition');
    if (selectHaltCondition) selectHaltCondition.value = this.sim.haltCondition;
    const qCard = document.getElementById('metricQuasihaltCard');
    if (qCard) qCard.style.display = isQuasihaltPreset ? 'flex' : 'none';

    // Reset to Step 0: do not automatically run or draw diagram until user clicks Play / Step / Run
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.activeAgentTab = 0;

    // Ensure preset dropdown syncs with loaded preset
    const presetSelect = document.getElementById('presetSelect');
    if (presetSelect && presetSelect.value !== key) {
      presetSelect.value = key;
    }

    // Update preset description
    const descEl = document.getElementById('presetDescription');
    if (descEl) {
      descEl.innerHTML = `<strong>${preset.name}</strong> <span class="badge badge-accent">${preset.badge}</span><br><small>${preset.description}</small>`;
    }

    this.currentPresetKey = key;
    this.updateAllViews();
    this.diagram.fitToView();
    if (preset.trace) this.loadNativeTrace(preset.trace);
  }

  // Fetch a natively precomputed trace (traces/*.bin made by trace_export.exe) and show it instantly
  async loadNativeTrace(url) {
    const descEl = document.getElementById('presetDescription');
    try {
      const resp = await fetch(url);
      if (!resp.ok) throw new Error('HTTP ' + resp.status);
      const buf = await resp.arrayBuffer();
      if (this.isPlaying) this.togglePlay();
      this.sim.loadTrace(buf);
      this.diagram.scrubStep = this.sim.stepCount;
      this.updateAllViews();
      this.diagram.fitToView();
      if (descEl) descEl.innerHTML += `<br><small>⚡ Native trace loaded (${this.sim.history.length} snapshots) — scrub the timeline freely.</small>`;
      return true;
    } catch (err) {
      console.warn('Native trace load failed:', err);
      if (descEl) descEl.innerHTML += `<br><small>⚠ Native trace unavailable (${err.message}); run in-browser instead.</small>`;
      return false;
    }
  }

  setModeCET() {
    this.sim.agentCount = 2;
    this.sim.initialPositions = [0, 2];
    this.sim.haltRule = 'first_pair';
    document.getElementById('mcetControlsGroup').style.display = 'none';
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  setModeMCET() {
    document.getElementById('mcetControlsGroup').style.display = 'flex';
    this.sim.haltRule = 'all';
    if (this.sim.agentCount < 3) {
      this.sim.agentCount = 3;
      this.sim.initialPositions = [0, 2, 4];
      this.sim.initDefaultTables();
    }
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  changeN(delta) {
    const newN = Math.max(1, Math.min(10, this.sim.nStates + delta));
    if (newN === this.sim.nStates) return;

    this.sim.nStates = newN;
    this.sim.initDefaultTables();
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  changeSymbols(delta) {
    const newSym = Math.max(2, Math.min(10, this.sim.nSymbols + delta));
    if (newSym === this.sim.nSymbols) return;

    this.sim.nSymbols = newSym;
    this.sim.initDefaultTables();
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  changeAgentCount(delta) {
    const newCount = Math.max(2, Math.min(10, this.sim.agentCount + delta));
    if (newCount === this.sim.agentCount) return;

    this.sim.agentCount = newCount;
    this.sim.initialPositions = [];
    for (let i = 0; i < newCount; i++) {
      this.sim.initialPositions.push(i * 2);
    }
    this.sim.initDefaultTables();
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  randomizeCurrent() {
    for (let a = 0; a < this.sim.agentCount; a++) {
      for (let s = 0; s < this.sim.nStates; s++) {
        for (let sym = 0; sym < this.sim.nSymbols; sym++) {
          this.sim.tables[a][s][sym] = {
            write: Math.floor(Math.random() * this.sim.nSymbols),
            dir: Math.random() < 0.5 ? 1 : -1,
            nextState: Math.floor(Math.random() * this.sim.nStates)
          };
        }
      }
    }
    this.onTableModified(true);
  }

  mutateCurrent() {
    const a = Math.floor(Math.random() * this.sim.agentCount);
    const s = Math.floor(Math.random() * this.sim.nStates);
    const sym = Math.floor(Math.random() * this.sim.nSymbols);
    const choice = Math.floor(Math.random() * 3);

    if (choice === 0) {
      this.sim.tables[a][s][sym].write = (this.sim.tables[a][s][sym].write + 1) % this.sim.nSymbols;
    } else if (choice === 1) {
      this.sim.tables[a][s][sym].dir = -this.sim.tables[a][s][sym].dir;
    } else {
      this.sim.tables[a][s][sym].nextState = Math.floor(Math.random() * this.sim.nStates);
    }

    this.onTableModified(true);
  }

  togglePlay() {
    this.isPlaying = !this.isPlaying;
    const btn = document.getElementById('btnPlayPause');
    btn.innerHTML = this.isPlaying ? '⏸ Pause' : '▶ Play';

    if (this.isPlaying) {
      // If halted due to quasi-halt, allow user to press Play to keep simulating the cycle indefinitely!
      if (this.sim.halted && this.sim.quasihaltEvent) {
        this.sim.halted = false; // Un-halt to let user watch the post-quasihalt infinite trajectory
      } else if (this.sim.halted && this.diagram.scrubStep === this.sim.stepCount) {
        // Normal collision halting: reset to step 0 to replay cleanly
        this.sim.reset();
        this.diagram.scrubStep = 0;
        this.updateAllViews();
      }
      this.lastFrameTime = performance.now();
      this.playLoop();
    } else {
      if (this.animFrameId) {
        cancelAnimationFrame(this.animFrameId);
        this.animFrameId = null;
      }
    }
  }

  setPlaySpeed(speed, updateInput = true, updateSlider = true) {
    // Clamp speed between 1 and 100,000,000 steps/sec (100M/s)
    speed = Math.max(1, Math.min(100000000, Math.round(speed)));
    this.playSpeed = speed;

    const formatted = this.formatSpeed(speed);

    const speedDisplay = document.getElementById('speedDisplay');
    if (speedDisplay) {
      speedDisplay.textContent = formatted;
    }

    const speedInput = document.getElementById('speedInput');
    if (speedInput && updateInput) {
      speedInput.value = formatted;
    }

    const speedSlider = document.getElementById('speedSlider');
    if (speedSlider && updateSlider) {
      // Map speed (1 .. 100,000,000) to log slider (0 .. 800)
      const logVal = Math.log10(speed);
      const sliderVal = Math.round(logVal * 100);
      speedSlider.value = Math.max(0, Math.min(800, sliderVal));
    }
  }

  formatSpeed(speed) {
    if (speed >= 100000000) {
      return '100M/s';
    }
    if (speed >= 1000000) {
      const m = speed / 1000000;
      return `${m % 1 === 0 ? m : m.toFixed(1)}M/s`;
    }
    if (speed >= 1000) {
      const k = speed / 1000;
      return `${k % 1 === 0 ? k : k.toFixed(1)}k/s`;
    }
    return `${speed}/s`;
  }

  parseSpeedText(str) {
    if (!str) return 20;
    let s = String(str).trim().toLowerCase().replace('/s', '').replace('steps', '').replace(/,/g, '');
    if (s.endsWith('m')) {
      const num = parseFloat(s.slice(0, -1));
      return isNaN(num) ? 20 : num * 1000000;
    }
    if (s.endsWith('k')) {
      const num = parseFloat(s.slice(0, -1));
      return isNaN(num) ? 20 : num * 1000;
    }
    const num = parseFloat(s);
    return isNaN(num) ? 20 : num;
  }

  playLoop() {
    if (!this.isPlaying) return;

    const current = this.diagram.scrubStep !== null ? this.diagram.scrubStep : 0;
    
    // If user scrubbed back into history, scrub forward along recorded history first
    if (current < this.sim.stepCount) {
      const stepDelta = Math.max(1, Math.min(this.sim.stepCount - current, Math.floor(this.playSpeed / 60)));
      const next = Math.min(this.sim.stepCount, current + stepDelta);
      this.scrubTo(next);
      if (this.playSpeed <= 120) {
        this.audio.playStep(this.sim.getAgentDistance());
      }
      this.animFrameId = requestAnimationFrame(() => this.playLoop());
      return;
    }

    // At execution frontier: if halted, stop playing
    if (this.sim.halted) {
      this.isPlaying = false;
      document.getElementById('btnPlayPause').innerHTML = '▶ Play';
      if (this.sim.collisionEvent) {
        this.audio.playCollision();
      }
      return;
    }

    // Ultra-high speed dynamic simulation: target steps calculated from playSpeed (up to 100M/s)
    const targetSteps = Math.max(1, Math.round(this.playSpeed / 60));
    const frameStart = performance.now();
    // Allow up to 35ms per animation frame for turbo execution
    const maxFrameBudgetMs = this.playSpeed >= 1000000 ? 35 : 20;

    let executed = 0;
    const chunkSize = Math.min(targetSteps, 65536);
    while (executed < targetSteps && !this.sim.halted) {
      const batch = Math.min(chunkSize, targetSteps - executed);
      executed += this.sim.stepBatch(batch);
      if (performance.now() - frameStart > maxFrameBudgetMs) {
        break;
      }
    }

    this.diagram.scrubStep = this.sim.stepCount;
    if (this.diagram.options.autoCenterRunning) {
      this.diagram.autoCenterOnProgress();
      this.tape1d.autoCenter();
    }
    this.updateAllViews({ isPlayback: true });
    if (this.playSpeed <= 120) {
      this.audio.playStep(this.sim.getAgentDistance());
    }

    if (this.sim.halted) {
      this.isPlaying = false;
      document.getElementById('btnPlayPause').innerHTML = '▶ Play';
      if (this.sim.collisionEvent) {
        this.audio.playCollision();
      }
      return;
    }

    this.animFrameId = requestAnimationFrame(() => this.playLoop());
  }

  stepForward() {
    const current = this.diagram.scrubStep !== null ? this.diagram.scrubStep : this.sim.stepCount;
    if (current < this.sim.stepCount) {
      this.scrubTo(current + 1);
      this.audio.playStep(this.sim.getAgentDistance());
      return;
    }

    // At frontier: simulate the next step on demand!
    if (this.sim.halted && this.sim.quasihaltEvent) {
      this.sim.halted = false; // Allow stepping past quasihalt
    }

    if (!this.sim.halted) {
      this.sim.step();
      this.diagram.scrubStep = this.sim.stepCount;
      if (this.diagram.options.autoCenterRunning) {
        this.diagram.autoCenterOnProgress();
        this.tape1d.autoCenter();
      }
      this.updateAllViews();
      this.audio.playStep(this.sim.getAgentDistance());

      if (this.sim.collisionEvent) {
        this.audio.playCollision();
      }
    }
  }

  stepBackward() {
    const current = this.diagram.scrubStep !== null ? this.diagram.scrubStep : this.sim.stepCount;
    if (current > 0) {
      this.scrubTo(current - 1);
      this.audio.playStep(this.sim.getAgentDistance());
    }
  }

  resetSimulation() {
    if (this.isPlaying) {
      this.togglePlay();
    }
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  jumpToEnd() {
    if (this.isPlaying) {
      this.togglePlay();
    }
    // Run remaining steps to completion without resetting
    const tp = PRESETS[this.currentPresetKey];
    if (tp && tp.trace && this.sim.stepCount === 0) {
      this.loadNativeTrace(tp.trace).then(ok => { if (ok && this.sim.collisionEvent) this.audio.playCollision(); });
      return;
    }
    this.sim.runToCompletion(undefined, false);
    this.diagram.scrubStep = this.sim.stepCount;
    this.updateAllViews();
    this.diagram.fitToView();
    if (this.sim.collisionEvent) {
      this.audio.playCollision();
    }
  }

  continuePostQuasihalt(extraSteps = 500) {
    if (this.isPlaying) {
      this.togglePlay();
    }
    // Temporarily unhalt simulator and disable quasihalt check for extraSteps
    this.sim.halted = false;
    const oldCondition = this.sim.haltCondition;
    this.sim.haltCondition = 'normal'; // run steps without cycle halting

    const target = this.sim.stepCount + extraSteps;
    while (this.sim.stepCount < target && !this.sim.halted) {
      this.sim.step();
    }
    this.sim.haltCondition = oldCondition;

    this.diagram.scrubStep = this.sim.stepCount;
    this.updateAllViews();
    this.diagram.fitToView();
  }

  scrubTo(step) {
    this.diagram.scrubStep = step;
    document.getElementById('timelineSlider').value = step;
    document.getElementById('timelineStepDisplay').textContent = `${step} / ${this.sim.stepCount}`;

    const snap = this.sim.getSnapshotAtStep ? this.sim.getSnapshotAtStep(step) : this.sim.history[step];
    this.tape1d.render(snap);
    this.diagram.draw();

    // Update state graph for active agent tab
    if (snap && snap.agentStates[this.activeAgentTab]) {
      const activeState = snap.agentStates[this.activeAgentTab].state;
      this.stateGraph.render(this.sim.tables[this.activeAgentTab], this.activeAgentTab + 1, activeState);
    }
  }

  updateAllViews(options = {}) {
    // 1. Update N, Symbols, and Agent counters
    document.getElementById('displayNValue').textContent = this.sim.nStates;
    const dispSym = document.getElementById('displaySymValue');
    if (dispSym) dispSym.textContent = this.sim.nSymbols;
    document.getElementById('displayAgentCount').textContent = this.sim.agentCount;

    // 2. Timeline slider bounds
    const timeline = document.getElementById('timelineSlider');
    timeline.max = Math.max(1, this.sim.stepCount);
    const targetStep = this.diagram.scrubStep !== null ? this.diagram.scrubStep : this.sim.stepCount;
    timeline.value = targetStep;
    document.getElementById('timelineStepDisplay').textContent = `${targetStep} / ${this.sim.stepCount}`;

    // 3. Status Badge & Metrics
    const statusEl = document.getElementById('statusBadge');
    const btnContinueQuasihalt = document.getElementById('btnContinuePostQuasihalt');
    if (btnContinueQuasihalt) {
      btnContinueQuasihalt.style.display = (this.sim.haltCondition === 'quasihalt' && this.sim.quasihaltEvent) ? 'inline-flex' : 'none';
    }

    if (this.sim.quasihaltEvent) {
      statusEl.className = 'status-badge status-halted';
      statusEl.innerHTML = `🔮 QUASI-HALTED: Final collision at step <strong>${this.sim.quasihaltEvent.lastColStep}</strong>! Verified Cycle (Period <strong>${this.sim.quasihaltEvent.cycleLen}</strong>, Drift <strong>${this.sim.quasihaltEvent.drift}</strong>). 0 collisions forever after.`;
    } else if (this.sim.collisionEvent) {
      statusEl.className = 'status-badge status-halted';
      statusEl.innerHTML = `💥 HALTED: Collision at cell <strong>${this.sim.collisionEvent.pos}</strong> on step <strong>${this.sim.collisionEvent.step}</strong> (Agent ${this.sim.collisionEvent.agents.join(' & ')})`;
    } else if (this.sim.stepCount === 0) {
      statusEl.className = 'status-badge status-running';
      statusEl.innerHTML = `⏸ READY (Step 0) — Click <strong>▶ Play</strong> or <strong>Step ▶</strong> to run, or <strong>⏭ Run to End</strong>`;
    } else if (this.sim.halted) {
      statusEl.className = 'status-badge status-running';
      statusEl.innerHTML = `⚠️ NO COLLISION: ${this.sim.haltReason || 'Stopped'}`;
    } else {
      statusEl.className = 'status-badge status-running';
      statusEl.innerHTML = `🟡 RUNNING — Step ${this.sim.stepCount}`;
    }

    const metrics = this.sim.getTapeMetrics();
    document.getElementById('metricStepCount').textContent = this.sim.stepCount;
    document.getElementById('metricOnesCount').textContent = metrics.onesCount;
    document.getElementById('metricTapeSpan').textContent = `[${metrics.minPos}, ${metrics.maxPos}] (${metrics.span} cells)`;
    document.getElementById('metricAgentDist').textContent = `${this.sim.getAgentDistance()} cells`;
    const haltRuleEl = document.getElementById('metricHaltRule');
    if (haltRuleEl) {
      if (this.sim.haltCondition === 'quasihalt') {
        haltRuleEl.textContent = 'Quasi-Halting (CET_1)';
        haltRuleEl.style.color = '#e879f9';
      } else if (this.sim.haltRule === 'all') {
        haltRuleEl.textContent = `All Agents (${this.sim.agentCount})`;
        haltRuleEl.style.color = '#a855f7';
      } else if (this.sim.haltRule === 'elimination') {
        haltRuleEl.textContent = 'Elimination';
        haltRuleEl.style.color = '#f59e0b';
      } else {
        haltRuleEl.textContent = 'Pairwise Collision';
        haltRuleEl.style.color = '#38bdf8';
      }
    }

    const qCard = document.getElementById('metricQuasihaltCard');
    const qState = document.getElementById('metricQuasihaltState');
    if (qCard && qState) {
      if (this.sim.haltCondition === 'quasihalt') {
        qCard.style.display = 'flex';
        if (this.sim.quasihaltEvent) {
          qState.textContent = `Quasi-halted at step ${this.sim.quasihaltEvent.lastColStep} (Period ${this.sim.quasihaltEvent.cycleLen})`;
          qState.style.color = '#4ade80';
        } else if (this.sim.collisionCount > 0) {
          qState.textContent = `${this.sim.collisionCount} collisions (last at ${this.sim.lastCollisionStep})`;
          qState.style.color = '#facc15';
        } else {
          qState.textContent = '0 collisions observed';
          qState.style.color = '#94a3b8';
        }
      } else {
        qCard.style.display = 'none';
      }
    }

    // 4. Raw text output & tables only when idle or explicitly requested (prevents heavy DOM lag at 60fps)
    if (!options.isPlayback) {
      document.getElementById('rawTextInput').value = this.sim.toTextFormat();
      this.renderAgentTabs();
      this.renderTransitionTable();
    }

    // 5. Visualizers
    this.tape1d.render();
    this.diagram.draw();

    if (!options.isPlayback) {
      const currState = this.sim.agents[this.activeAgentTab]?.state || 0;
      this.stateGraph.render(this.sim.tables[this.activeAgentTab], this.activeAgentTab + 1, currState);
    }
  }

  renderAgentTabs() {
    const tabsContainer = document.getElementById('agentTabsContainer');
    if (!tabsContainer) return;

    let html = '';
    for (let a = 0; a < this.sim.agentCount; a++) {
      const color = this.tape1d.agentColors[a % this.tape1d.agentColors.length];
      const isActive = a === this.activeAgentTab;
      html += `
        <button class="agent-tab-btn ${isActive ? 'active' : ''}" data-agent="${a}" style="--agent-color: ${color}">
          <span class="agent-dot" style="background: ${color}"></span>
          Agent ${a + 1}
        </button>
      `;
    }
    tabsContainer.innerHTML = html;

    tabsContainer.querySelectorAll('.agent-tab-btn').forEach(btn => {
      btn.addEventListener('click', (e) => {
        const agIdx = parseInt(btn.dataset.agent, 10);
        this.activeAgentTab = agIdx;
        this.renderAgentTabs();
        this.renderTransitionTable();
        const currState = this.sim.agents[this.activeAgentTab]?.state || 0;
        this.stateGraph.render(this.sim.tables[this.activeAgentTab], this.activeAgentTab + 1, currState);
      });
    });
  }

  renderTransitionTable() {
    const tbody = document.getElementById('transitionTableTbody');
    if (!tbody) return;

    // Update active agent format text box and active agent label
    const agentFormatInput = document.getElementById('agentFormatInput');
    if (agentFormatInput) {
      agentFormatInput.value = this.sim.agentToTuplesString(this.activeAgentTab);
    }
    const lblActiveAgentNum = document.getElementById('lblActiveAgentNum');
    if (lblActiveAgentNum) {
      lblActiveAgentNum.textContent = this.activeAgentTab + 1;
    }

    const table = this.sim.tables[this.activeAgentTab];
    let html = '';

    for (let s = 0; s < this.sim.nStates; s++) {
      const stateChar = String.fromCharCode(65 + s);
      for (let sym = 0; sym < this.sim.nSymbols; sym++) {
        const trans = table[s][sym];
        let symClass = 'sym-0';
        if (sym === 1) symClass = 'sym-1';
        else if (sym === 2) symClass = 'sym-2';
        else if (sym >= 3) symClass = 'sym-3';

        html += `
          <tr data-state="${s}" data-sym="${sym}">
            <td><span class="badge badge-state">${stateChar} (${s})</span></td>
            <td><span class="sym-badge ${symClass}">${sym}</span></td>
            <td>
              <button class="btn-toggle-prop btn-write ${trans.write > 0 ? 'active' : ''}" data-prop="write">
                ${trans.write}
              </button>
            </td>
            <td>
              <button class="btn-toggle-prop btn-dir ${trans.dir === 1 ? 'btn-dir-right' : 'btn-dir-left'}" data-prop="dir">
                ${trans.dir === 1 ? '▶ R' : '◀ L'}
              </button>
            </td>
            <td>
              <select class="select-next-state" data-prop="nextState">
                ${Array.from({ length: this.sim.nStates }, (_, ns) => `
                  <option value="${ns}" ${ns === trans.nextState ? 'selected' : ''}>
                    ${String.fromCharCode(65 + ns)} (${ns})
                  </option>
                `).join('')}
              </select>
            </td>
          </tr>
        `;
      }
    }
    tbody.innerHTML = html;

    // Attach row events
    tbody.querySelectorAll('.btn-write').forEach(btn => {
      btn.addEventListener('click', (e) => {
        const tr = btn.closest('tr');
        const s = parseInt(tr.dataset.state, 10);
        const sym = parseInt(tr.dataset.sym, 10);
        const cur = this.sim.tables[this.activeAgentTab][s][sym].write;
        this.sim.tables[this.activeAgentTab][s][sym].write = (cur + 1) % this.sim.nSymbols;
        this.onTableModified();
      });
    });

    tbody.querySelectorAll('.btn-dir').forEach(btn => {
      btn.addEventListener('click', (e) => {
        const tr = btn.closest('tr');
        const s = parseInt(tr.dataset.state, 10);
        const sym = parseInt(tr.dataset.sym, 10);
        const cur = this.sim.tables[this.activeAgentTab][s][sym].dir;
        this.sim.tables[this.activeAgentTab][s][sym].dir = -cur;
        this.onTableModified();
      });
    });

    tbody.querySelectorAll('.select-next-state').forEach(sel => {
      sel.addEventListener('change', (e) => {
        const tr = sel.closest('tr');
        const s = parseInt(tr.dataset.state, 10);
        const sym = parseInt(tr.dataset.sym, 10);
        this.sim.tables[this.activeAgentTab][s][sym].nextState = parseInt(sel.value, 10);
        this.onTableModified();
      });
    });
  }

  onTableModified(shouldFit = true) {
    if (this.isPlaying) {
      this.togglePlay();
    }
    // Do NOT run the agents when the transition table is modified!
    // Simply reset the simulation state to Step 0 with the new transition table.
    this.sim.reset();
    this.diagram.scrubStep = 0;
    this.updateAllViews();
    if (shouldFit) {
      this.diagram.fitToView();
    }
  }

  updateHoverInfo(info) {
    const tip = document.getElementById('spaceTimeTooltip');
    if (!tip) return;
    if (!info || info.t < 0 || info.t > this.sim.stepCount) {
      tip.style.display = 'none';
      return;
    }

    const snap = this.sim.getSnapshotAtStep(info.t);
    let agentsAtPos = [];
    let isCellOne = false;
    if (snap) {
      agentsAtPos = snap.agentStates.filter(a => a.active && a.pos === info.x);
      if (snap.intervals) {
        isCellOne = snap.intervals.some(([s, e]) => info.x >= s && info.x <= e);
      }
    }

    tip.style.display = 'block';
    tip.style.left = `${info.canvasX + 16}px`;
    tip.style.top = `${info.canvasY + 16}px`;

    let agentsText = 'None';
    if (agentsAtPos.length > 0) {
      agentsText = agentsAtPos.map(a => `<span style="color:${this.tape1d.agentColors[(a.id-1)%this.tape1d.agentColors.length]}">Agent ${a.id} (State ${String.fromCharCode(65+a.state)})</span>`).join(', ');
    }

    tip.innerHTML = `
      <div><strong>Step (t):</strong> ${info.t}</div>
      <div><strong>Tape Pos (x):</strong> ${info.x}</div>
      <div><strong>Symbol:</strong> <span class="sym-badge ${isCellOne ? 'sym-1' : 'sym-0'}">${isCellOne ? '1' : '0'}</span></div>
      <div><strong>Agents:</strong> ${agentsText}</div>
    `;
  }

  exportDiagramPNG() {
    const dataUrl = this.diagram.exportImageURL();
    const link = document.createElement('a');
    link.download = `CET_n${this.sim.nStates}_steps${this.sim.stepCount}.png`;
    link.href = dataUrl;
    link.click();
  }
}

// Bootstrap on DOM loaded
window.addEventListener('DOMContentLoaded', () => {
  window.app = new AppController();
});
