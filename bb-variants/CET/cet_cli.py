#!/usr/bin/env python3
"""
Catch-Em-Turing (CET & MCET) Command Line Interface & Terminal Space-Time Visualizer
"""

import sys
import os
import time
import argparse
import http.server
import socketserver
import webbrowser

PRESETS = {
    "cet1": {
        "name": "CET(1) = 1 (Busy Beaver Champion)",
        "n": 1,
        "a1": [(0, 1, 0), (0, -1, 0)],
        "a2": [(0, -1, 0), (0, -1, 0)],
    },
    "cet2": {
        "name": "CET(2) = 97 (Busy Beaver Champion - Nath76 / Verified Maximum)",
        "n": 2,
        "a1": [(1, -1, 1), (0, -1, 1), (1, 1, 1), (0, -1, 0)],
        "a2": [(1, 1, 1), (1, -1, 0), (1, -1, 0), (1, 1, 1)],
    },
    "cet2_77": {
        "name": "CET(2) Dual Weaver (77 Steps)",
        "n": 2,
        "a1": [(0, -1, 1), (1, 1, 1), (1, 1, 1), (0, -1, 0)],
        "a2": [(1, -1, 1), (1, 1, 0), (0, 1, 0), (1, 1, 1)],
    },
    "cet3": {
        "name": "CET(3) = 6065 (Busy Beaver Champion)",
        "n": 3,
        "a1": [(1, -1, 2), (1, 1, 1), (1, -1, 0), (0, -1, 1), (1, 1, 0), (1, 1, 0)],
        "a2": [(1, 1, 2), (1, -1, 0), (1, -1, 1), (0, 1, 1), (0, 1, 1), (0, -1, 2)],
    },
    "cet4": {
        "name": "CET(4) = 213393 (Busy Beaver Champion - 16-Thread C Hunter)",
        "n": 4,
        "a1": [(1, 1, 3), (0, 1, 3), (1, -1, 3), (1, 1, 0), (1, -1, 1), (0, -1, 1), (1, -1, 0), (0, 1, 2)],
        "a2": [(0, 1, 1), (0, 1, 3), (1, -1, 2), (0, 1, 0), (0, 1, 0), (1, -1, 2), (1, -1, 3), (0, 1, 1)],
    }
}

class CETRunner:
    def __init__(self, t1, t2, n_states=2, max_steps=1000):
        self.t1 = t1 # list of (w, d, ns) for (s0,0), (s0,1), (s1,0), (s1,1)...
        self.t2 = t2
        self.n_states = n_states
        self.max_steps = max_steps

    def simulate(self):
        tape = {}
        pos1, pos2 = 0, 2
        s1, s2 = 0, 0
        history = [(0, pos1, s1, pos2, s2, dict(tape))]

        for step in range(1, self.max_steps + 1):
            if pos1 == pos2:
                return {
                    "halted": True,
                    "steps": step - 1,
                    "collision_pos": pos1,
                    "history": history,
                    "tape": tape
                }

            sym1 = tape.get(pos1, 0)
            sym2 = tape.get(pos2, 0)

            idx1 = s1 * 2 + sym1
            idx2 = s2 * 2 + sym2

            w1, d1, ns1 = self.t1[idx1]
            w2, d2, ns2 = self.t2[idx2]

            tape[pos1] = w1
            tape[pos2] = w2

            pos1 += d1
            pos2 += d2
            s1 = ns1
            s2 = ns2

            history.append((step, pos1, s1, pos2, s2, dict(tape)))

            if pos1 == pos2:
                return {
                    "halted": True,
                    "steps": step,
                    "collision_pos": pos1,
                    "history": history,
                    "tape": tape
                }

        return {
            "halted": False,
            "steps": self.max_steps,
            "collision_pos": None,
            "history": history,
            "tape": tape
        }

    def print_ascii_spacetime(self, result):
        history = result["history"]
        min_x = min(min(h[1], h[3]) for h in history) - 2
        max_x = max(max(h[1], h[3]) for h in history) + 2

        print("\n" + "=" * 65)
        print("🌌 TERMINAL SPACE-TIME DIAGRAM (T: Step, X: Space)")
        print("   Legend: \033[96m1\033[0m: Agent 1, \033[91m2\033[0m: Agent 2, \033[93m#\033[0m: Tape 1, \033[90m.\033[0m: Tape 0, \033[93m💥\033[0m: Collision")
        print("=" * 65)

        # Header with positions
        hdr = " t  | "
        for x in range(min_x, max_x + 1):
            if x == 0:
                hdr += "|"
            elif x % 5 == 0:
                hdr += "'"
            else:
                hdr += " "
        print(hdr)

        for step, p1, st1, p2, st2, tape_snap in history:
            row = f"{step:3d} | "
            for x in range(min_x, max_x + 1):
                if p1 == x and p2 == x:
                    row += "\033[93m💥\033[0m"
                elif p1 == x:
                    row += "\033[96m1\033[0m"
                elif p2 == x:
                    row += "\033[91m2\033[0m"
                elif tape_snap.get(x, 0) == 1:
                    row += "\033[33m#\033[0m"
                else:
                    row += "\033[90m.\033[0m"
            print(row)

        print("-" * 65)
        if result["halted"]:
            print(f"\033[92m✔ HALTED by collision at cell {result['collision_pos']} on step {result['steps']}!\033[0m")
        else:
            print(f"\033[91m✖ DID NOT COLLIDE within {self.max_steps} steps\033[0m")
        print("=" * 65 + "\n")

def main():
    parser = argparse.ArgumentParser(description="Catch-Em-Turing (CET) Simulator & Tooling")
    parser.add_argument("--port", "-p", type=int, default=8000, help="Port to listen on when serving")
    parser.add_argument("--no-browser", action="store_true", help="Do not automatically open browser")
    
    subparsers = parser.add_subparsers(dest="command")

    # Command: run
    run_parser = subparsers.add_parser("run", help="Run a CET preset or custom machine")
    run_parser.add_argument("--preset", choices=list(PRESETS.keys()), default="cet2", help="Preset to run")
    run_parser.add_argument("--steps", type=int, default=200, help="Max step limit")

    # Command: serve
    serve_parser = subparsers.add_parser("serve", help="Launch local web server for GUI visualizer")
    serve_parser.add_argument("--port", "-p", type=int, default=8000, help="Port to listen on")
    serve_parser.add_argument("--no-browser", action="store_true", help="Do not automatically open browser")

    args = parser.parse_args()

    if args.command == "serve" or args.command is None:
        port = args.port
        os.chdir(os.path.dirname(os.path.abspath(__file__)))
        handler = http.server.SimpleHTTPRequestHandler
        print(f"\n🚀 Catch-Em-Turing Studio Web App ready at http://localhost:{port}")
        print("Press Ctrl+C to stop.\n")
        if not args.no_browser:
            webbrowser.open(f"http://localhost:{port}")
        with socketserver.TCPServer(("", port), handler) as httpd:
            try:
                httpd.serve_forever()
            except KeyboardInterrupt:
                print("\nServer stopped.")
    elif args.command == "run":
        preset = PRESETS[args.preset]
        print(f"Loading {preset['name']}...")
        runner = CETRunner(preset["a1"], preset["a2"], n_states=preset["n"], max_steps=args.steps)
        res = runner.simulate()
        runner.print_ascii_spacetime(res)

if __name__ == "__main__":
    main()
