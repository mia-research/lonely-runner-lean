#!/usr/bin/env python3
"""As escape_direct_v1.py, but the control verifies a certificate for EVERY covered tuple,
not only the newly-covered ones.  The certificate is checked against all n-1 = 7 speeds of
T, i.e. it verifies LRC(8) for that tuple outright.  Exact arithmetic; no float anywhere."""
import sys
from fractions import Fraction as F
from math import gcd, lcm
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import norm, largest_prime, escape_ii, witness_ii
from escape_coverage_v2 import good_idx, band_B, witness11
from escape_direct_v1 import config
n = 8; CAP = 10**6

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    stat = {}
    for T in combinations(range(1, B + 1), 7):
        if gcd(*T) != 1: continue
        c = config(T)
        if c is None: continue
        arm, Gsp, L_G, Asp, L_A, p = c
        if L_G > CAP or n * L_A > 4 * CAP:
            stat.setdefault(arm, {}).setdefault("cap", 0); stat[arm]["cap"] += 1; continue
        d = stat.setdefault(arm, {})
        for k in ("tot","pig","inter","ii","new","wok","wfail","resid"):
            d.setdefault(k, [] if k == "resid" else 0)
        d["tot"] += 1
        Bn, seen = band_B(Gsp, L_G, Asp, L_A, p)
        IA = [b for b in range(n * L_A) if good_idx(b, Asp, L_A)]
        pig = (Bn + len(IA) > n * L_A)
        inter = any(seen[b] for b in IA)
        e2 = escape_ii(T)
        d["pig"] += pig; d["inter"] += inter; d["ii"] += e2; d["new"] += (e2 or inter)
        if not (e2 or inter): d["resid"].append(T); continue
        # CONTROL on EVERY covered tuple: build a certificate and verify all 7 speeds.
        t = witness_ii(T) if e2 else witness11(T, (Gsp, L_G, Asp, L_A, p, seen, set(IA)))
        if t is not None and all(norm(t * v) >= F(1, n) for v in T): d["wok"] += 1
        else: d["wfail"] += 1
    print(f"n=8, speeds <= {B}, gcd=1, hard case.  Exact; ratios as Fractions.")
    for arm in ("10.1", "11.1"):
        if arm not in stat: continue
        d = stat[arm]; t = d["tot"]
        print(f"\n  THEOREM {arm}   arm {t}   compute-capped {d.get('cap',0)}")
        print(f"    (ii) 5.2-D {d['ii']}   (iii) count {d['pig']}   (iii') intersection {d['inter']}")
        print(f"    coverage (ii or intersection) : {d['new']}/{t} = {F(d['new'],t)}")
        print(f"    RESIDUAL : {t - d['new']}")
        print(f"    CERTIFICATES verified (all 7 speeds, exact) : {d['wok']}")
        print(f"    certificate FAILURES (must be 0)            : {d['wfail']}")
        for X in d["resid"][:20]: print("      residual", list(X))
