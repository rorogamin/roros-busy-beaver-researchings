#!/usr/bin/env python3
"""Finite reset automaton for machine 14's A/2> block system.

The table is interpreted as a rightmost-active-control rewrite system.

Language candidate
------------------
A configuration is described by the last reset token R in {2>, 214}, the suffix s
after R, and the token g immediately before R.  The observed 200,000-step run has
only 11 guarded states, and every observed reset suffix has length <= 3.

The automaton is not fully closed.  Closure produces the state

    (g, R, s) = ('2>', '214', ('21$',))

which is not observed; the 2> then consumes the 214 and loses the reset.  The
script reports that exact transition instead of assuming the state away.

Run: py -3.14 machine14_reset_automaton.py
"""

from __future__ import annotations

import json
from collections import deque
from pathlib import Path

RA = {
    "22": ["22", "A", "A"],
    "14": ["24"],
    "24": ["21"],
    "21": ["14", "A"],
    "214": ["14", "2>", "A"],
    "224": ["22", "A", "2>", "A"],
    "221": ["22", "A", "2>"],
    "21$": ["14", "21$"],
}
RB = {
    "22": ["22", "2>"],
    "14": ["214"],
    "24": ["224"],
    "21": ["221"],
    "214": ["22", "14"],
    "224": ["22", "24"],
    "221": ["22", "21"],
    "21$": None,
}

# States observed in the first 200,000 macro steps.  A state is
# (token left of reset, reset token, suffix after reset).
OBSERVED = {
    ("214", "214", ("21$",)),
    ("14", "214", ("21$",)),
    ("A", "214", ("21$",)),
    ("14", "2>", ("A", "21$")),
    ("14", "2>", ("14", "21$")),
    ("24", "214", ("21$",)),
    ("224", "214", ("21$",)),
    ("21", "214", ("21$",)),
    ("A", "2>", ("22", "14", "21$")),
    ("22", "2>", ("14", "21$")),
    ("22", "214", ("21$",)),
}


def closure() -> tuple[set, list, tuple | None]:
    states = set(OBSERVED)
    queue = deque(states)
    transitions: list[tuple] = []
    failure: tuple | None = None

    def add(state: tuple) -> None:
        if state not in states:
            states.add(state)
            queue.append(state)

    while queue and failure is None:
        g, reset, suffix = queue.popleft()

        # A control inside the suffix acts before anything to its left.
        if suffix and suffix[0] == "A":
            block = suffix[1]
            out = RA.get(block, "MISS")
            if out == "MISS":
                failure = ("MISSING", g, reset, suffix, "A", block)
                break
            new_suffix = tuple(out) + suffix[2:]
            transitions.append((g, reset, suffix, "inner", "A", block, out,
                                (g, reset, new_suffix)))
            add((g, reset, new_suffix))
            continue

        # A reset 2> is itself the active control.
        if reset == "2>":
            block = suffix[0]
            out = RB.get(block, "MISS")
            if out is None:
                failure = ("HALT", g, reset, suffix, "2>", block)
                break
            if out == "MISS":
                failure = ("MISSING", g, reset, suffix, "2>", block)
                break
            resets = [i for i, x in enumerate(out) if x in ("2>", "214")]
            if not resets:
                failure = ("LOST_RESET_2>", g, reset, suffix, "2>", block, out)
                break
            k = max(resets)
            new_reset = out[k]
            new_g = g if k == 0 else out[k - 1]
            new_suffix = tuple(out[k + 1:]) + suffix[1:]
            transitions.append((g, reset, suffix, "reset2", "2>", block, out,
                                (new_g, new_reset, new_suffix)))
            add((new_g, new_reset, new_suffix))
            continue

        # reset is 214.  If the immediate left token is a control, it acts.
        if g in ("A", "2>"):
            out = (RA if g == "A" else RB).get("214", "MISS")
            resets = [i for i, x in enumerate(out) if x in ("2>", "214")]
            if not resets:
                failure = ("LOST_RESET_GUARD", g, reset, suffix, g, "214", out)
                break
            k = max(resets)
            new_reset = out[k]
            new_g = out[k - 1] if k > 0 else g
            new_suffix = tuple(out[k + 1:]) + suffix
            transitions.append((g, reset, suffix, "guardhead", g, "214", out,
                                (new_g, new_reset, new_suffix)))
            add((new_g, new_reset, new_suffix))
            continue

        # g is a block: a control farther left acts on it.  Only its last output
        # token is adjacent to the reset, so that token becomes the new guard.
        for h in ("A", "2>"):
            out = (RA if h == "A" else RB).get(g, "MISS")
            if out == "MISS" or out is None:
                continue
            new_g = out[-1]
            transitions.append((g, reset, suffix, "guardblock", h, g, out,
                                (new_g, reset, suffix)))
            add((new_g, reset, suffix))

    return states, transitions, failure


def main() -> None:
    states, transitions, failure = closure()
    print(f"observed states: {len(OBSERVED)}")
    print(f"closure states:  {len(states)}")
    print(f"transitions:     {len(transitions)}")
    print(f"closed:          {failure is None}")
    if failure:
        print(f"failure:         {failure}")

    payload = {
        "observed_states": sorted(map(list, OBSERVED)),
        "closure_states": sorted([list(g), r, list(s)] for g, r, s in states),
        "transitions": [list(t) for t in transitions],
        "failure": list(failure) if failure else None,
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"wrote {out.name}")


if __name__ == "__main__":
    main()
