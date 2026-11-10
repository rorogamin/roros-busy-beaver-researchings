"""Local HTTP server + C-accelerated API for Double Turing Machines (DTM) Studio.

Run with:
    py -3.14 server.py [--port 8765] [--no-open]
"""

from __future__ import annotations

import argparse
import functools
import http.server
import json
import os
import random
import subprocess
import sys
import time
import urllib.parse
import webbrowser
from typing import Any

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from dtm import DTM  # noqa: E402

FAST_EXE = os.path.join(HERE, "dtm_fast.exe" if os.name == "nt" else "dtm_fast")
CHAMPIONS_FILE = os.path.join(HERE, "champions.json")


def load_champions() -> dict[str, Any]:
    if os.path.exists(CHAMPIONS_FILE):
        with open(CHAMPIONS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"champions": [], "presets": []}


def run_fast_sim(spec: str, cap: int, slice_rad: int = 48) -> dict[str, Any]:
    dtm = DTM.parse(spec)
    norm_spec = dtm.spec()
    if os.path.exists(FAST_EXE):
        proc = subprocess.run(
            [FAST_EXE, "--sim", norm_spec, "--cap", str(cap), "--slice-rad", str(slice_rad)],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            data = json.loads(proc.stdout.strip().splitlines()[-1])
            data["engine"] = "native_c"
            data["signature"] = dtm.signature()
            data["equivalent_tm"] = dtm.to_equivalent_standard_tm()
            return data

    t0 = time.perf_counter()
    res = dtm.run(max_steps=min(cap, 1_000_000))
    dt = (time.perf_counter() - t0) * 1000.0
    slo = res.head - slice_rad
    shi = res.head + slice_rad
    return {
        "engine": "python",
        "spec": norm_spec,
        "signature": dtm.signature(),
        "equivalent_tm": dtm.to_equivalent_standard_tm(),
        "steps": res.steps,
        "halted": res.halted,
        "cycle_type": 0,
        "halt_reason": res.halt_reason,
        "score": res.score,
        "ones": res.nonzeros,
        "head": res.head,
        "state": res.state,
        "rule_idx": res.rule_idx,
        "min_pos": res.min_pos,
        "max_pos": res.max_pos,
        "elapsed_ms": round(dt, 2),
        "slice_start": slo,
        "slice": [res.tape.get(p, 0) for p in range(slo, shi + 1)],
    }


def run_fast_search(payload: dict[str, Any]) -> dict[str, Any]:
    n = int(payload.get("n", 2))
    m = int(payload.get("m", 2))
    rules = int(payload.get("rules", 2))
    a = int(payload.get("a", 0))
    b = int(payload.get("b", 0))
    cap = min(int(payload.get("cap", 100000)), 10_000_000)
    budget_ms = max(100, min(int(payload.get("budget_ms", 1200)), 10_000))
    mutate_spec = payload.get("mutate_spec", "").strip()
    seed = int(payload.get("seed", random.randint(1, 2**31 - 1)))

    if os.path.exists(FAST_EXE):
        cmd = [
            FAST_EXE,
            "--n", str(n),
            "--m", str(m),
            "--rules", str(rules),
            "--a", str(a),
            "--b", str(b),
            "--cap", str(cap),
            "--budget-ms", str(budget_ms),
            "--seed", str(seed),
        ]
        if mutate_spec:
            cmd.extend(["--mutate", DTM.parse(mutate_spec).spec()])
        else:
            cmd.append("--search")
        proc = subprocess.run(
            cmd,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=20,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            data = json.loads(proc.stdout.strip().splitlines()[-1])
            data["engine"] = "native_c"
            return data

    # Fallback pure-Python search
    t0 = time.perf_counter()
    rng = random.Random(seed)
    best_steps = 0
    best_score = 0
    best_spec = ""
    tested = 0
    halted = 0
    deadline = t0 + budget_ms / 1000.0
    while time.perf_counter() < deadline:
        parts = []
        for r in range(rules):
            rs = a if (r == 1 and a > 0) else n
            rm = b if (r == 1 and b > 0) else m
            blocks = []
            for _s in range(rs):
                toks = []
                for _y in range(rm):
                    w = rng.randrange(rm)
                    d = rng.choice("LR")
                    nx = rng.randrange(rs)
                    toks.append(f"{w}{d}{chr(ord('A') + nx)}")
                blocks.append("".join(toks))
            parts.append("_".join(blocks))
        # Inject one halt
        hr = rng.randrange(rules)
        spec_list = [list(p.split("_")) for p in parts]
        hs = rng.randrange(len(spec_list[hr]))
        rm = b if (hr == 1 and b > 0) else m
        hy = rng.randrange(rm)
        blk = spec_list[hr][hs]
        spec_list[hr][hs] = blk[: 3 * hy] + "1RZ" + blk[3 * hy + 3 :]
        cand_spec = "|".join("_".join(b) for b in spec_list)
        res = DTM.parse(cand_spec).run(max_steps=min(cap, 20000))
        tested += 1
        if res.halted:
            halted += 1
            if res.steps > best_steps or (res.steps == best_steps and res.score > best_score):
                best_steps = res.steps
                best_score = res.score
                best_spec = cand_spec
    return {
        "engine": "python",
        "tested": tested,
        "halted": halted,
        "holdouts": 0,
        "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 2),
        "best_steps": best_steps,
        "best_score": best_score,
        "best_spec": best_spec,
        "holdout_spec": "",
    }


class DTMHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self) -> None:
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def _send_json(self, code: int, data: Any) -> None:
        body = json.dumps(data).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> dict[str, Any]:
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length) if length > 0 else b"{}"
        return json.loads(raw.decode("utf-8"))

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path == "/api/health":
            self._send_json(200, {
                "ok": True,
                "native_c": os.path.exists(FAST_EXE),
                "cpu_count": os.cpu_count() or 1,
                "variant": "DTM",
            })
            return
        if parsed.path == "/api/champions":
            self._send_json(200, load_champions())
            return
        if parsed.path == "/":
            self.path = "/index.html"
        super().do_GET()

    def do_POST(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        try:
            payload = self._read_json()
            if parsed.path == "/api/parse":
                dtm = DTM.parse(payload["spec"])
                self._send_json(200, {
                    "spec": dtm.spec(),
                    "signature": dtm.signature(),
                    "equivalent_tm": dtm.to_equivalent_standard_tm(),
                    "num_rules": len(dtm.rules),
                    "rules": [{"states": r.states, "symbols": r.symbols} for r in dtm.rules],
                })
                return
            if parsed.path == "/api/simulate":
                res = run_fast_sim(
                    payload["spec"],
                    cap=int(payload.get("cap", 1_000_000)),
                    slice_rad=int(payload.get("slice_rad", 48)),
                )
                self._send_json(200, res)
                return
            if parsed.path == "/api/search":
                res = run_fast_search(payload)
                self._send_json(200, res)
                return
            self._send_json(404, {"error": f"Unknown endpoint {parsed.path}"})
        except Exception as exc:
            self._send_json(400, {"error": str(exc)})


def main() -> None:
    parser = argparse.ArgumentParser(description="Double Turing Machines (DTM) Studio Server")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--no-open", action="store_true")
    args = parser.parse_args()

    handler = functools.partial(DTMHandler, directory=HERE)
    server = http.server.ThreadingHTTPServer((args.host, args.port), handler)
    url = f"http://{args.host}:{args.port}/"
    print(f"DTM Studio Server listening at {url} (native_c={os.path.exists(FAST_EXE)})")
    if not args.no_open:
        try:
            webbrowser.open(url)
        except Exception:
            pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down DTM server.")
        server.server_close()


if __name__ == "__main__":
    main()
