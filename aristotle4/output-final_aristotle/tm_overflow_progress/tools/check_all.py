#!/usr/bin/env python3
"""Reproduce local tests and independent checkpoint comparisons.

Default: test the saved Python prefix against an independent C++ run from
blank, then resume Python to 10^1000. --full-python additionally runs Python
from blank without the checkpoint. Requires a C++17 compiler and Boost headers.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from event_machine import selftest
ROOT = Path(__file__).resolve().parents[1]
FIELDS = ('t', 'p', 'q', 'lo', 'hi', 'tape')


def run_json(args):
    result = subprocess.run(args, check=True, text=True, capture_output=True)
    return json.loads(result.stdout)


def same(a, b):
    for key in FIELDS:
        if a[key] != b[key]:
            raise AssertionError(f'configuration mismatch in {key}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-python', action='store_true')
    args = parser.parse_args()
    for script in ('test_laws.py', 'test_productive.py'):
        result = run_json([sys.executable, str(ROOT/'tools'/script)])
        assert result['status'] == 'PASS'
        print(f'PASS: {script}', flush=True)
    print(json.dumps(selftest()), flush=True)
    with tempfile.TemporaryDirectory() as directory:
        binary = str(Path(directory)/'verify_events')
        subprocess.run(['g++', '-O3', '-std=c++17', str(ROOT/'tools/verify_events.cpp'),
                        '-o', binary], check=True)
        literal = run_json([binary, '8', 'slow'])
        fast = run_json([binary, '8'])
        same(literal, fast)
        print('PASS: C++ event evaluator vs literal, exactly 10^8', flush=True)
        cpp = run_json([binary, '1000'])
        assert cpp['status'] == 'REACHED_TARGET' and int(cpp['t']) == 10**1000
        same(cpp, json.loads((ROOT/'checkpoints/1e1000_cpp.json').read_text()))
        prefix = json.loads((ROOT/'checkpoints/python_prefix.json').read_text())
        independent_prefix = run_json([binary, '1000', '--steps', prefix['t']])
        same(prefix, independent_prefix)
        print('PASS: saved Python prefix independently reproduced from blank in C++', flush=True)
        python = run_json([sys.executable, str(ROOT/'tools/event_machine.py'),
                           '--power', '1000', '--resume', str(ROOT/'checkpoints/python_prefix.json')])
        same(cpp, python)
        same(cpp, json.loads((ROOT/'checkpoints/1e1000_python.json').read_text()))
        print('PASS: complete Python/C++ configuration at exactly 10^1000', flush=True)
        if args.full_python:
            full = run_json([sys.executable, str(ROOT/'tools/event_machine.py'), '--power', '1000'])
            same(cpp, full)
            print('PASS: uninterrupted Python run from blank', flush=True)
    print('Lean draft was NOT compiled. No blank-tape nonhalting theorem is claimed.')

if __name__ == '__main__':
    main()
