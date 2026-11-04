"""gem48x_instrumented_tracer.py: the instrumented sync-frame walk."""
import sys
sys.path.insert(0, 'tools')

import importlib.machinery, importlib.util

# load _gem48x_cycle WITHOUT running the battery (its __main__ guards away)
spec = importlib.util.spec_from_file_location('cycle', 'tools/_gem48x_cycle.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def本案等():
    pass

# build one case and run with instrumentation
(Es, Q) = m.build_case()
T = m.T

def run():
    out = []
    for (i, (w, d, nx, ph)) in enumerate(frame_sync_monotone()):
        actual_names = Es.monotone_bases(i, ph)
        out.append((i, ph, actual_names))
    return out

if __name__ == '__main__':
    rng = (0, 1, 0, 1)
    cellser(ltcSI, rng)
    print(str(run()))
