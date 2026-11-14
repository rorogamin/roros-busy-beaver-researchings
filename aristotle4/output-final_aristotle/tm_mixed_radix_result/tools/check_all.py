#!/usr/bin/env python3
"""Reproduce the independent and literal comparisons. Requires g++ and Boost."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIELDS = ("t", "p", "q", "lo", "hi", "tape")


def run_json(argv: list[str]) -> dict:
    result = subprocess.run(argv, check=True, text=True, capture_output=True)
    return json.loads(result.stdout.strip().splitlines()[-1])


def same(a: dict, b: dict) -> None:
    assert a["status"] == b["status"] == "REACHED_TARGET"
    for field in FIELDS:
        assert a[field] == b[field], f"mismatch in {field}"


def main() -> None:
    from mixed_radix import selftest
    print(json.dumps(selftest()), flush=True)
    with tempfile.TemporaryDirectory() as directory:
        binary = str(Path(directory) / "verify")
        subprocess.run(["g++", "-std=c++17", "-O3", str(ROOT / "tools/verify.cpp"), "-o", binary], check=True)
        fast8 = run_json([binary, "8"])
        literal8 = run_json([binary, "8", "slow"])
        same(fast8, literal8)
        print("PASS: full configuration comparison, C++ accelerated vs literal, 10^8", flush=True)
        cpp100 = run_json([binary, "100"])
        python100 = run_json([sys.executable, str(ROOT / "tools/mixed_radix.py"), "--power", "100"])
        same(cpp100, python100)
        assert int(cpp100["t"]) == 10**100
        stored = json.loads((ROOT / "checkpoints/checkpoint_1e100_cpp.json").read_text())
        same(cpp100, stored)
        print("PASS: full configuration comparison, C++ vs Python vs saved checkpoint, 10^100", flush=True)
        print("New Lean source has NOT been compiled; these are executable tests, not a Lean certificate.")


if __name__ == "__main__":
    main()
