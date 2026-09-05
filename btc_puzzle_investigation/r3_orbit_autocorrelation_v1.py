#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
r3_orbit_autocorrelation_v1.py -- executes frozen PREREG_r3_orbit_autocorrelation_v1.md

Lag-d autocorrelation A(d)=|Sum_s omega^{c(s)-c(s+d)}|^2 of the cubic-class sequence
c(s)=chi3(x([s]G)) along a consecutive orbit.  Ranks A(d) against the CODE-SHUFFLE null
(permute the orbit's own codes: same marginal, no order) -- gate-cleared as immune to the
multiplicity and pool-imbalance defects (index pairing held fixed, actual code multiset used).
Two-sided 99th screen; candidate = same tail on 5/5 fresh orbit locations.

Exactness: chi3 via pure-int modexp; the shuffle null uses numpy on the 0/1/2 CLASS LABELS
only (integer permutation + bincount, no float, no precision loss) -- not float ops on keys.

Usage: python3 r3_orbit_autocorrelation_v1.py [L] [Rsh] [noos] [seed]
"""
import sys
import time
import bisect
import random
import numpy as np

from shortscalar_sum_stageA_v1 import scalar_mult, point_add, chi3_class, G, N_ORDER, EXP3, P_FIELD

LAGS = [1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 24, 32, 64, 128, 256]
MAXLAG = max(LAGS)


def orbit_cubic(s0, length):
    """cubic class c(s)=chi3(x([s]G)) for s0, s0+1, ..., s0+length-1 (1 modexp/point)."""
    P = scalar_mult(s0 % N_ORDER, G)
    out = np.empty(length, dtype=np.int64)
    for i in range(length):
        out[i] = chi3_class(P[0])
        P = point_add(P, G)
    return out


def A_of(cs, d, L):
    """A(d) = |Sum omega^{c(s)-c(s+d)}|^2 over s in [0,L), exact integer."""
    delta = (cs[:L] - cs[d:d + L]) % 3            # integer array, values in {0,1,2}
    m = np.bincount(delta, minlength=3)
    m0, m1, m2 = int(m[0]), int(m[1]), int(m[2])
    return m0 * m0 + m1 * m1 + m2 * m2 - m0 * m1 - m1 * m2 - m2 * m0


def shuffle_null(cs, L, R_sh, gen):
    """A(d) under random code-permutation is d-independent -> one null for all lags (d=1)."""
    n = len(cs)
    vals = [A_of(cs[gen.permutation(n)], 1, L) for _ in range(R_sh)]
    vals.sort()
    return vals


def p_upper(nullv, A):
    return (len(nullv) - bisect.bisect_left(nullv, A)) / len(nullv)   # #null >= A / R


def tail(p):
    return "HI" if p <= 0.005 else ("LO" if p >= 0.995 else ".")


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    R_sh = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    noos = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 20260802
    rng = random.Random(seed)
    gen = np.random.default_rng(seed)

    print("=" * 84)
    print(f"R3 ORBIT AUTOCORRELATION  L={L} Rsh={R_sh} noos={noos} seed={seed}")
    print(f"  lags={LAGS}")
    print(f"  BIG-O: {noos} orbits x {L+MAXLAG} chi3-modexp = {noos*(L+MAXLAG):,} modexp"
          f" + {noos*R_sh} integer shuffles")
    print("  screen: A(d) two-sided vs code-shuffle null; candidate = same tail 5/5 OOS")
    print("=" * 84)
    t0 = time.perf_counter()
    tb = time.perf_counter(); a = 3
    for _ in range(1000): a = pow((a + 7) % P_FIELD or 3, EXP3, P_FIELD)
    print(f"[bench] chi3 pow ~ {(time.perf_counter()-tb)/1000*1e6:.1f} us/modexp (full (p-1)/3 exponent)")

    # OOS locations frozen at seed, before any screen; non-overlapping by construction (~2L/n).
    s0s = [rng.randrange(1 << 200, N_ORDER) for _ in range(noos)]

    # per orbit: A(d) real, p_upper vs its own shuffle null
    perlag_p = {d: [] for d in LAGS}
    perlag_A = {d: [] for d in LAGS}
    plant_line = None
    for oi, s0 in enumerate(s0s):
        to = time.perf_counter()
        cs = orbit_cubic(s0, L + MAXLAG)
        nullv = shuffle_null(cs, L, R_sh, gen)
        for d in LAGS:
            A = A_of(cs, d, L)
            perlag_A[d].append(A)
            perlag_p[d].append(p_upper(nullv, A))
        # C-PLANT on the first orbit: inject lag-d* correlation, must fire
        if oi == 0:
            dstar = 5
            n99 = nullv[(99 * len(nullv)) // 100]
            fires = []
            for f in (0.0, 0.02, 0.05, 0.10):
                cp = cs.copy()
                idx = np.where(gen.random(L) < f)[0]
                cp[idx + dstar] = cp[idx]           # force c(s+d*)=c(s) on fraction f
                Ap = A_of(cp, dstar, L)
                fires.append((f, Ap, Ap > n99))
            plant_line = (dstar, n99, fires)
        print(f"[orbit {oi}] s0~2^{s0.bit_length()-1}  ({time.perf_counter()-to:.0f}s)"
              f"  shuffle-null median={nullv[len(nullv)//2]} 99th={nullv[(99*len(nullv))//100]}")

    # ---- controls ----
    print("-" * 84)
    ds, n99, fires = plant_line
    print(f"[C-PLANT] inject lag-{ds} correlation (null 99th={n99}); A({ds}) vs 99th:")
    for f, Ap, fired in fires:
        print(f"    f={f:4.2f}: A={Ap:>12}  {'FIRES' if fired else '--'}")
    print(f"    -> plant {'FIRES with injected correlation (instrument live)' if fires[-1][2] else 'DEAD'}"
          f"; void at f=0: {'ok' if not fires[0][2] else 'FALSE-FIRE'}")

    print("-" * 84)
    print("[forced-value] median A(d) across orbits vs null 99th (a forced lag would sit >> 99th):")
    # use last orbit's null 99th as reference scale
    ref99 = nullv[(99 * len(nullv)) // 100]
    forced = []
    for d in LAGS:
        medA = sorted(perlag_A[d])[len(perlag_A[d]) // 2]
        flag = "FORCED?" if medA > ref99 else "generic"
        if medA > ref99:
            forced.append(d)
        print(f"    d={d:>3}: median A={medA:>12}  (null99~{ref99})  [{flag}]")
    if forced:
        print(f"    -> lags flagged forced (drop per gate note 3): {forced}")

    # ---- verdict ----
    print("=" * 84)
    print(f"PER-LAG two-sided p across {noos} OOS orbits (candidate = same tail {noos}/{noos}):")
    candidates = []
    for d in LAGS:
        ps = perlag_p[d]
        tags = "".join(tail(p) for p in ps)
        hi = all(p <= 0.005 for p in ps)
        lo = all(p >= 0.995 for p in ps)
        mark = " <=CANDIDATE" if (hi or lo) else ""
        if hi or lo:
            candidates.append((d, "HI" if hi else "LO"))
        print(f"    d={d:>3}: [{tags}]  p=[{', '.join(f'{p:.3f}' for p in ps)}]{mark}")
    print("=" * 84)
    if candidates:
        print(f"CANDIDATE lags (same tail {noos}/{noos}): {candidates}")
        print("  -> real short-range chi structure the histogram missed; characterize (do NOT name mechanism).")
        print("  -> A(d) is a group-law-difference correlation -> directly seeds C2.")
    else:
        print(f"No lag screened same-tail {noos}/{noos}. MIXING CONFIRMED at these lags/power.")
        print("  -> bound (Rule 5): no lag-d chi3 correlation above the shuffle floor; finer structure")
        print("     absent to this power. Strengthens the earned artifact verdict; proceed to C2.")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
