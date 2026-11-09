# Catch-Em-Turing (CET & MCET) Studio

An ultra-fast simulator, interactive space-time diagrammer, Busy Beaver search engine, and exploration studio for **Catch-Em-Turing (CET(n))** and **Multi Catch-Em-Turing (MCET(n))** computational systems.

---

## 🌟 Mathematical Discoveries & Exact Results

The Catch-Em-Turing Busy Beaver function measures the maximum steps two $n$-state agents on an infinite tape can execute before colliding on the same cell:
$$\text{CET}(n) = \max \{ \text{steps before collision} \}$$

| Model | Value (Steps) | Status | Collision Cell | Discovered By / Verification | Champion Spec (Agent 1 \| Agent 2 \| ...) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **CET(1)** | **1** | **Proven Exact** | Cell `1` | Nath76 | `0RA0RA\|0LA0LA` |
| **CET(2)** | **97** | **Proven Exact** | Cell `-1` | Nath76 / Antigravity (Exhaustive search of 16.7M) | `1LB0LB_1RB0LA\|1RB1LA_1LA1RB` |
| **CET(3)** | **3,092,745,703** | **Current Champion** | Cell `9,857` | Antigravity (Deep multi-seed search) | `0LB0LC_1RB1LA_1RC0LA\|1LB0RC_1RA1LB_0LB1RC` |
| **CET(4)** | **4,622,083,548** | **Current Champion** | Cell `-19,208` | Antigravity (Billion-odometer / GA search) | `1LC0LC_1LA1RB_0RB1LC_0RA0RA\|1RC0RA_1RA1RB_1LC0RD_0RA0RC` |
| **CET(2, 3 sym)** | **1,528,952,999** | **Current Champion** | Cell `1,723` | Antigravity (3-symbol search) | `1RB0RA2LB_2LA2RB1LB\|2RB0RA2RB_2LB1RA0RB` |
| **MCET(3)** (3 agents) | **211,190,346** | **Current Champion** | Cell `13,350` | Antigravity (3-agent search) | `1LC1LA_1RA1RB_0RB0RA\|1LC1LB_1RC1RB_0LC0RA\|0LA1RB_0RC1RB_0RA1RC` |

> **Note on Parity Invariance:**
> Agent 1 starts at position 0, and Agent 2 starts at position 2. Because both agents move $\pm 1$ at every discrete step, the spatial difference $\Delta x = x_2 - x_1$ always preserves parity ($\Delta x \pmod 2 = 0$). Thus, agents can never pass through each other in continuous space without landing on the exact same discrete cell at the same time!

---

## 📜 Formal Verification in Rocq 9.1

The CET variant includes machine-checked certificates in Rocq 9.1:

* **`NonQuasiHalting_CET1.v`**: Formal certificate proving that target machine `1RB0RB_1RA0LB | 1RB0RB_1LA1RA` exhibits **Non-Quasi-Halting** via an infinite collision recurrence witness theorem (`witness_implies_non_quasihalting`). Compiles with zero unverified axioms (`[propext, Classical.choice, Quot.sound]`).
* **`cert_proto.v`**: Executable step definitions and formal collision predicates over zipper/functional configurations.

---

## 🚀 Quick Start

### 1. Web Studio (Interactive GUI)
Open `index.html` directly in any web browser, or launch the built-in local server:
```bash
python cet_cli.py serve
```
Then navigate to: **`http://localhost:8000`**

### 2. Terminal CLI & ASCII Space-Time Visualizer
Run the 97-step CET(2) champion or CET(1) directly in your terminal:
```bash
python cet_cli.py run --preset cet2
python cet_cli.py run --preset cet1
```

---

## 🎮 Web Studio Features

1. **Interactive 2D Space-Time Diagram Canvas**:
   - **X Axis**: Tape space coordinates (relative to origin).
   - **Y Axis**: Time steps (flowing downwards or upwards).
   - Visualizes the tape cell states (0 = dark space, 1 = energized cells).
   - Neon glowing worldlines for each agent trajectory.
   - Pulsing collision starburst at $(x_{\text{halt}}, t_{\text{halt}})$.
   - **Pan & Zoom**: Click-and-drag to pan, mouse wheel to zoom around cursor.
   - **Timeline Scrubbing**: Click anywhere on the diagram or scrub the timeline slider to inspect any historical step.
   - **Themes**: Cyberpunk Neon, Matrix Terminal, and Blueprint Cobalt.
   - **PNG Export**: One-click high-resolution diagram export.

2. **1D Ribbon Tape Visualizer**:
   - Realistic tape view with active agent heads showing current state, movement directions, and simultaneous read/writes.
   - Center-on-agents button and navigation arrows.

3. **Multi Catch-Em-Turing (MCET) Support**:
   - Toggle between **CET(n)** (2 agents) and **MCET(n, m)** ($m$ agents).
   - Configurable initial positions and agent counts (2 to 8).
   - Writing conflict resolution: lowest index agent has priority.

4. **Interactive Transition Table Editor**:
   - Tabs for each agent.
   - Interactive toggle chips for write (`0` / `1`), direction (`◀ L` / `R ▶`), and next state.
   - Edits take effect immediately with instant re-simulation.
   - Direct text notation input (paste strings like `Agent 1: (1, LEFT, 1), (0, LEFT, 1)...`).

5. **Randomizer & Mutator**:
   - 🎲 **Randomize**: Generates completely new valid transition tables.
   - 🧬 **Mutate**: Flips a single action to explore nearby topological behaviors.

6. **State Transition Graph**:
   - Real-time SVG state diagram for the active agent with glowing indicators during execution.

7. **Background Busy Beaver Auto-Hunter**:
   - Multi-threaded Web Worker that scans machines in the background without UI lag.
   - Random and Genetic / Hill Climbing search strategies.
   - Live leaderboard of high-score discoveries with one-click machine loading.

8. **Audio Sonification Engine (Web Audio API)**:
   - Ambient soundscape: stereo-panned tape clicks, pitch-modulated head ticks, and a major chord chime upon collision.

---

## 🛠️ High-Performance Search Toolchain

The directory contains an extensive suite of native C, C++, and CUDA engines for gigastep exploration:

* **Champion Ledgers**:
  * `cet3_all_champions.txt`: Milestones up to 3,092,745,703 steps.
  * `cet4_all_champions.txt`: Milestones up to 4,622,083,548 steps.
  * `cet23_all_champions.txt`: 2-state 3-symbol records up to 1,528,952,999 steps.
  * `mcet3_all_champions.txt`: 3-agent records up to 211,190,346 steps.
* **Native C / C++ Searchers**:
  * `fast_bb_hunter.c`, `fast_search.c`: Core multi-threaded random and DFS searchers.
  * `hunt_cet3_world_champ.c`: Deep optimization pipeline for CET(3).
  * `hunt_cet4_billion_odometer.c`: Odometer exploration reaching multi-billion-step domains.
  * `bench_mega_speed.cpp`: Performance benchmarking for simultaneous simulation.
* **GPU / CUDA Kernels**:
  * `cuda_cet_kernel.cu`: Massively parallel evaluation on NVIDIA GPUs.
  * `a100_search.cu`, `a100_hyper_v2.cu`: Scaled cluster searchers for cloud A100 nodes.

---

## 📁 Project Structure

```
├── index.html                       # Main web application entry point
├── style.css                        # Cyberpunk dark sci-fi responsive UI stylesheet
├── simulator.js                     # Simultaneous multi-agent Turing simulation engine
├── spacetime.js                     # Canvas 2D space-time diagram visualizer
├── tape1d.js                        # 1D interactive tape ribbon visualizer
├── state_graph.js                   # SVG state transition graph generator
├── audio.js                         # Web Audio API sonification engine
├── hunter_worker.js                 # Background Web Worker for Busy Beaver hunting
├── app.js                           # Main application controller & preset manager
├── cet_cli.py                       # Python CLI & ASCII space-time diagrammer
├── fast_bb_hunter.c                 # Ultra-fast native C search engine
├── NonQuasiHalting_CET1.v           # Rocq 9.1 proof of non-quasi-halting
├── cet3_all_champions.txt           # CET(3) champions up to 3.09B steps
├── cet4_all_champions.txt           # CET(4) champions up to 4.62B steps
├── cet23_all_champions.txt          # CET(2, 3) champions up to 1.52B steps
├── mcet3_all_champions.txt          # MCET(3) champions up to 211M steps
└── README.md                        # Documentation and mathematical results
```
