#!/usr/bin/env python3
"""One-machine backtracking proof attempt.

Run with cwd=vendor/busy-beaver/Code so the local decider modules resolve.
"""

import json
import sys
from pathlib import Path

CODE = Path(__file__).resolve().parent / "vendor" / "busy-beaver" / "Code"
sys.path.insert(0, str(CODE))

import Backtracking_Filter  # noqa: E402
import IO  # noqa: E402


def main() -> int:
    if len(sys.argv) != 4:
        print(json.dumps({"error": "usage: backtrack_one.py <machine> <steps> <max_width>"}))
        return 2
    machine, steps_s, width_s = sys.argv[1:]
    steps = int(steps_s)
    max_width = int(width_s)
    tm = IO.parse_tm(machine)
    result = Backtracking_Filter.backtrack(tm, steps, max_width)
    print(json.dumps({
        "machine": machine,
        "steps": steps,
        "max_width": max_width,
        "success": bool(result.success),
        "halted": bool(result.halted),
        "stopped_at_steps": int(result.max_steps),
        "observed_width": int(result.max_width),
        "num_nodes": int(result.num_nodes),
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
