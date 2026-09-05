#!/usr/bin/env python3
"""
coherent_pool_p0prime_stageC_nullnull_v1.py -- the NULL-vs-NULL gate on the
HELD-OUT stratum S (closes the gate battery on S before the pool is read).

Same logic as coherent_pool_p0prime_nullnull_v1.py but using the frozen S
freq-list and the S curve params: replace the real char by a MN-mu6 replicate,
recompute q'_p over B pseudo-chars, require ~50/50 sign split.  If it fires, the
all-positive held-out pattern would be a pool construction bias -> VOID.
"""
import argparse
import numpy as np
from row_budget_run_v1 import mu6_orbits, Permuter, nlow_batch
from row_budget_core_v1 import curve_orbit
from coherent_pool_p0prime_stageC_run_v1 import load_S


def nullnull(p, n, lam, F, R, B, rng):
    X, Y, nn = curve_orbit(p); assert nn == n
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)                # noqa: float (carve-out)
    pc = [0] * B; nul = [0] * R
    for (b, c) in F:
        e = (b * X + c * Y) % p                                # exact integer exponent
        s = tab[e]; s[0] = 0.0                                 # noqa: float (carve-out)
        rows = [s[P6.draw(rng)] for _ in range(B + R)]
        NL, _, _ = nlow_batch(np.array(rows), n)
        for i in range(B): pc[i] += int(NL[i])
        for j in range(R): nul[j] += int(NL[B + j])
    nsum = sum(nul)
    qs = [R * pc[i] - nsum for i in range(B)]
    return sum(1 for q in qs if q > 0), sum(1 for q in qs if q < 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--freqs", default="coherent_pool_p0prime_stageC_S_FREQS.txt")
    ap.add_argument("--primes", default="823,907")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--B", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20260827)
    a = ap.parse_args()
    params, freqs, sha = load_S(a.freqs)
    print(f"NULL-vs-NULL on held-out S  SHA {sha[:16]}...  R={a.R} B={a.B}")
    rng = np.random.default_rng(a.seed)
    tp = tt = 0
    for p in [int(t) for t in a.primes.split(",")]:
        n, beta, lam = params[p]
        pos, neg = nullnull(p, n, lam, freqs[p], a.R, a.B, rng)
        tp += pos; tt += pos + neg
        print(f"  p={p:>5} n={n:>5}  pseudo-char q'>0: {pos}/{a.B}  (<0: {neg})")
    lo, hi = tt * 40 // 100, tt * 60 // 100
    print(f"\n  pooled {tp}/{tt} positive; within [40%,60%]=[{lo},{hi}]? "
          f"{'YES -> gate PASSES on S' if lo <= tp <= hi else 'NO -> VOID'}")


if __name__ == "__main__":
    main()
