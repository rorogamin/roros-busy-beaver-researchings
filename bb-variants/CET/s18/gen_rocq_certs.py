"""Generate Rocq certificate verification files from s18 decider outputs."""
import sys
from pathlib import Path

def parse_agent_rocq(name: str, spec: str) -> str:
    rows = spec.split('_')
    states = ['StA', 'StB', 'StC']
    arms = []
    for st_idx, row in enumerate(rows):
        for sym_idx, sym_name in enumerate(['false', 'true']):
            tok = row[3*sym_idx : 3*sym_idx+3]
            if tok == '---':
                arms.append(f"  | {states[st_idx]}, {sym_name} => None")
            else:
                w = 'true' if tok[0] == '1' else 'false'
                d = 'MoveL' if tok[1] == 'L' else 'MoveR'
                ns = {'A': 'StA', 'B': 'StB', 'C': 'StC'}[tok[2]]
                arms.append(f"  | {states[st_idx]}, {sym_name} => Some {{| write_sym := {w}; move_dir := {d}; next_state := {ns} |}}")
    body = "\n".join(arms)
    return f"Definition {name} (s : State) (b : bool) : option Transition :=\n  match s, b with\n{body}\n  end."

if __name__ == '__main__':
    print("Helper loaded.")
