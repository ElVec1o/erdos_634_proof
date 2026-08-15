#!/usr/bin/env python3
"""Re-certification campaign for the patch engine after the exact-π flat fix.

The pre-fix engine branched over straight-gap fillers whose flat list was
anchored to already-placed points only — not exhaustive, so a KILLED reached
through such a branch was not sound.  The fixed engine (swap_patch_search.py)
enumerates flats exhaustively whenever the line's contact origin is pinned and
defers otherwise, so every KILLED it reports is sound.  This driver reruns
the full slot campaign (f ≤ 9, both chord disciplines, open + all rN modes)
and writes a fresh verdict table; nothing from the old table is trusted.

Usage: rerun_patch_campaign.py [fmax] [time_cap] > table.txt
"""
from math import gcd
import subprocess, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))


def members(fmax):
    for f in range(3, fmax + 1):
        for e in range(2, f):
            if gcd(e, f) == 1:
                yield e, f


def run_one(e, f, M, mode, chord, tcap):
    cmd = [sys.executable, os.path.join(HERE, "swap_patch_search.py"),
           "--only", f"{e},{f},{M}", "--mode", mode, "--chord", chord,
           "--fmax", "12", "--time-cap", str(tcap)]
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=tcap + 60)
    for line in out.stdout.splitlines():
        if line.startswith(f"({e},{f}) M={M}:"):
            verdict = line.split(":", 1)[1].strip().split()[0]
            return verdict, line.strip()
    return "NORUN", out.stdout.strip()[-200:]


def main():
    fmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    tcap = float(sys.argv[2]) if len(sys.argv) > 2 else 90.0
    print(f"# fixed-engine re-certification: fmax={fmax} time_cap={tcap}")
    print("# semantics: open-KILLED = all k >= M+2; rN-KILLED = k = M+N;")
    print("# OPEN = no verdict (defer or caps).  Every KILLED is sound.")
    t00 = time.time()
    for chord in ("free", "swap"):
        print(f"\n== chord={chord} ==")
        for e, f in members(fmax):
            Mlo, Mhi = f // e + 2, f - 2
            if Mlo > Mhi:
                continue
            for M in range(Mlo, Mhi + 1):
                cells = []
                v, line = run_one(e, f, M, "open", chord, tcap)
                cells.append(f"open:{v}")
                open_killed = (v == "KILLED")
                for r in range(2, f - M + 1):
                    v, line = run_one(e, f, M, f"r{r}", chord, tcap)
                    cells.append(f"r{r}:{v}")
                print(f"({e},{f}) M={M}: " + "  ".join(cells) +
                      ("   [all k by open]" if open_killed else ""))
                sys.stdout.flush()
    print(f"\n# total {time.time() - t00:.0f}s")


if __name__ == "__main__":
    main()
