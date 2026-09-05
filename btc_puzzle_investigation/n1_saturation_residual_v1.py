#!/usr/bin/env python3
"""
n1_saturation_residual_v1.py -- EXPLORATORY.  Targets N1, the record's ONE measured
anomaly with no account (POSITIVE_FINDINGS_MASTER_v4.md M3/N1, OPEN, "twice attempted,
twice not closed").

THE ANOMALY AS RECORDED.  Saturation = max_a |V(a)| / (dim * sqrt p) with dim = 4:
chi2(y) gives 0.470 [0.432-0.500] over 6 primes "converging to 1/2", while the SAME
DIMENSION additive readout bx+cy gives 0.876 -- a 1.86x gap at identical dimension.

TWO SEPARATE QUESTIONS, kept separate here:
  Q1 WHY 1/2 AND NOT 0.876?  Mechanism, already on file (ANALYSIS_n1_cap_anew_channel_
     kronecker_route_v1.md, 2026-07-26, POSTDATING MASTER_v4's "no account"): the 120
     degree lock alpha_2/alpha_1 = zeta_3 makes |1 + zeta_3| = 1 exactly, so only 2 of
     the 4 eigenvalues carry independent weight => ceiling 2 sqrt p = 1/2 of 4 sqrt p.
     Not re-tested here; noted because MASTER_v4's OPEN status is stale.
  Q2 IS THE SUB-1/2 DEFICIT A REAL RESIDUAL?  ***THIS IS THE TEST.***  If the 120 lock
     is exact, max|u| (u = V/(2i sqrt p), |u| <= 1) is the maximum of L = (n-1)/6 draws
     from the semicircle marginal, and
             1/2 - saturation = (1 - max|u|)/2  ~  c * L^(-2/3)     [finite size]
     because the semicircle density vanishes like sqrt(1-u) at the edge.  A residual
     that does NOT follow the null's own deficit is a subleading term in the
     cancellation -- which is the only place the interference picture leaves for
     information (a uniform exact suppression has no complementary bright fringe).

DECISIVE COMPARISON: data deficit vs the SAME-L iid-semicircle null deficit, at every p.
Ratio -> 1 across a decade of p  =>  fully finite-size, no residual, N1's numeric half
accounted.  Ratio bounded away from 1  =>  a real subleading term.

Exact int signal path; float only in the max statistic, compared to null draws.
"""
import argparse, json, sys
import numpy as np
from sympy import isprime
from twist_orbit_spectrum_run_v1 import signal
from semicircle_null_v1 import free_reps, u_free, semicircle


def collect(pmin, pmax, want):
    out, p = [], pmin - 1
    while len(out) < want and p < pmax:
        p += 1
        if not isprime(p) or p % 4 != 3:
            continue
        s = signal(p, 7)
        if s is None:
            continue
        out.append((p, s))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmin", type=int, default=100)
    ap.add_argument("--pmax", type=int, default=9000)
    ap.add_argument("--want", type=int, default=34)
    ap.add_argument("-R", type=int, default=300)
    ap.add_argument("--seed", type=int, default=20260801)
    ap.add_argument("--out", default="n1_saturation_residual_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)

    rows = []
    print(f"{'p':>6} {'n':>6} {'L':>6}  {'sat_data':>9} {'sat_null':>9} "
          f"{'def_data':>9} {'def_null':>9} {'ratio':>7}")
    for p, s in collect(a.pmin, a.pmax, a.want):
        n, c, X, Y = s
        reps, L = free_reps(n)
        u = u_free(p, n, c, reps)
        mx = float(np.max(np.abs(u)))                              # noqa: float
        sat = mx / 2.0
        nulls = np.array([np.max(np.abs(semicircle(L, rng))) for _ in range(a.R)])
        satn = float(nulls.mean()) / 2.0                            # noqa: float
        dd, dn = 0.5 - sat, 0.5 - satn
        ratio = dd / dn if dn > 0 else float("nan")                 # noqa: float
        rows.append({"p": p, "n": int(n), "L": int(L), "max_u": mx,
                     "sat_data": sat, "sat_null": satn,
                     "def_data": dd, "def_null": dn, "ratio": ratio,
                     "z": float((mx - nulls.mean()) / nulls.std())})  # noqa: float
        print(f"{p:6d} {n:6d} {L:6d}  {sat:9.5f} {satn:9.5f} "
              f"{dd:9.5f} {dn:9.5f} {ratio:7.3f}")
        sys.stdout.flush()

    P = np.array([r["p"] for r in rows], float)                     # noqa: float
    DD = np.array([r["def_data"] for r in rows])
    DN = np.array([r["def_null"] for r in rows])
    RT = np.array([r["ratio"] for r in rows])
    ZS = np.array([r["z"] for r in rows])
    ok = DD > 0
    sd = np.polyfit(np.log(P[ok]), np.log(DD[ok]), 1)[0]            # noqa: float
    sn = np.polyfit(np.log(P), np.log(DN), 1)[0]                    # noqa: float
    print(f"\nN = {len(rows)} primes, p in [{int(P.min())}, {int(P.max())}]")
    print(f"  log-log slope of DATA deficit vs p : {sd:+.3f}")
    print(f"  log-log slope of NULL deficit vs p : {sn:+.3f}   "
          f"(finite-size prediction -2/3 = -0.667)")
    print(f"  ratio def_data/def_null : mean {RT.mean():.3f}  median "
          f"{np.median(RT):.3f}  sd {RT.std():.3f}")
    print(f"  per-prime z of max|u| vs null : mean {ZS.mean():+.3f}  "
          f"pooled {ZS.mean()*np.sqrt(len(ZS)):+.2f}  "
          f"signs {int((ZS>0).sum())}/{len(ZS)} positive")
    # split by size: is the ratio drifting?
    h = len(rows) // 2
    print(f"  ratio, small-p half : {RT[:h].mean():.3f}   large-p half : "
          f"{RT[h:].mean():.3f}")
    json.dump(rows, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
