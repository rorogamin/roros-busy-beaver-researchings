# Catch-Em-Turing (CET & MCET) Studio

An ultra-fast simulator, interactive space-time diagrammer, Busy Beaver search engine, and exploration studio for **Catch-Em-Turing (CET(n))** and **Multi Catch-Em-Turing (MCET(n))** computational systems.

---

## 🌟 Mathematical Discoveries & Exact Results

The Catch-Em-Turing Busy Beaver function measures the maximum steps two $n$-state agents on an infinite tape can execute before colliding on the same cell:
$$\text{CET}(n) = \max \{ \text{steps before collision} \}$$

| Model | Value | Status | Collision Cell | Discovered By / Verification |
| :--- | :--- | :--- | :--- | :--- |
| **CET(1)** | **1** | **Proven Exact** | Cell `1` | Nath76 |
| **CET(2)** | **97** | **Proven Exact** | Cell `-1` | Nath76 (Machine) / Antigravity (Exhaustive search of all 16,777,216 machines) |
| **CET(3)** | **&ge; 6,065** | **Current Champion** | Cell `-2591` | Antigravity (Multi-threaded genetic search over $8.9 \times 10^{12}$ space) |

> **Note on Parity Invariance:**
> Agent 1 starts at position 0, and Agent 2 starts at position 2. Because both agents move $\pm 1$ at every discrete step, the spatial difference $\Delta x = x_2 - x_1$ always preserves parity ($\Delta x \pmod 2 = 0$). Thus, agents can never pass through each other in continuous space without landing on the exact same discrete cell at the same time!

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
   - Pulsing collision starburst at $(x_{halt}, t_{halt})$.
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

## 📁 Project Structure

```
├── index.html           # Main web application entry point
├── style.css            # Cyberpunk dark sci-fi responsive UI stylesheet
├── simulator.js         # Simultaneous multi-agent Turing simulation engine
├── spacetime.js         # Canvas 2D space-time diagram visualizer
├── tape1d.js            # 1D interactive tape ribbon visualizer
├── state_graph.js       # SVG state transition graph generator
├── audio.js             # Web Audio API sonification engine
├── hunter_worker.js     # Background Web Worker for Busy Beaver hunting
├── app.js               # Main application controller & preset manager
├── cet_cli.py           # Python CLI & ASCII space-time diagrammer
├── fast_bb_hunter.c     # Ultra-fast native C search engine
└── README.md            # Documentation and mathematical results
```
