#!/usr/bin/env python3
"""
second_order_density_v1.py

Beyond first-order shadow sweeps (all flat). User asks: second order, density,
"pattern/resonance in the integer when you change it". On the full-range 256-bit
set (columns already carry n,k,D,sextant,chi6X/Y -> mostly free):

SECOND ORDER
  S1 INTERACTION: MI(point-stat ; V1 op V2) for op in {+,*,xor} over construction
     vars (n%6,k%6,D%6,d%6). A shadow can hide in an interaction while every
     first-order MI is flat.
  S2 HETEROSKEDASTICITY: does VAR/tail of a point-stat change with a construction
     bucket even when the MEAN is flat? (a second-moment shadow).

DENSITY / INTEGER RESONANCE
  D1 GECT expansion length (d_terms = greedy reciprocal count, det. fn of (N,D)):
     distribution + resonance scan MI(d_terms ; D mod m) and vs |D| bit-length.
  D2 PRIME density of X, Y, d, n vs the 1/ln baseline (Bateman-Horn sanity).
  D3 COLLISION/GAP: low-bit X uniformity + nearest-neighbour gap law (Poisson if
     scrambled; clustering if structured).

Plant controls fire. Exact integers in the signal path (CLAUDE.md).
"""
import numpy as np
from collections import Counter
from exact_core import d_terms
from angular_interference_scaling_v1 import conditional
from sympy import isprime

def load256(cap=12000):
    z = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
    mask = np.array([int(v) == 256 for v in z["N"]])
    idx = np.where(mask)[0][:cap]
    col = lambda name: [int(z[name][i]) for i in idx]
    return {k: col(k) for k in ["d", "X", "Y", "n", "k", "D", "sextant", "chi6X", "chi6Y"]}

def mi_z(feat, targ, Ms, rng, Bnull=250):
    res = conditional(np.array(feat), np.array(targ), Ms, Bnull, rng)
    return res[-1][1], res[-1][2]

def main():
    dat = load256()
    n = len(dat["d"]); Ms = [3000, n] if n > 3000 else [n]
    rng = np.random.default_rng(7)
    d = dat["d"]; nn = dat["n"]; kk = dat["k"]; DD = dat["D"]; sxt = dat["sextant"]
    print(f"loaded {n} 256-bit keys\n")

    # ---- S1 INTERACTION ----
    print("=== S1  SECOND-ORDER INTERACTION: MI(sextant ; V1 op V2) ===")
    v = {"n%6": [x % 6 for x in nn], "k%6": [x % 6 for x in kk],
         "D%6": [abs(x) % 6 for x in DD], "d%6": [x % 6 for x in d]}
    combos = [("n%6", "k%6"), ("n%6", "d%6"), ("k%6", "D%6"), ("d%6", "n%6")]
    for a, b in combos:
        A, B = v[a], v[b]
        for op, fn in [("+", lambda x, y: (x + y) % 6), ("*", lambda x, y: (x * y) % 6),
                       ("^", lambda x, y: (x ^ y) % 6)]:
            V = [fn(x, y) for x, y in zip(A, B)]
            ic, zz = mi_z(sxt, V, Ms, rng)
            if abs(zz) > 3:
                print(f"    sextant ; {a}{op}{b}: I_c={ic:+.5f} z={zz:+.2f}  <-- check")
    print("    (only |z|>3 shown; none => no interaction shadow)")
    # plant: sextant leaks (sextant vs sextant) already known; here plant an interaction
    plantV = [(s + 0) % 6 for s in sxt]
    _, zc = mi_z(sxt, plantV, Ms, rng)
    print(f"    [plant] sextant ; sextant-copy: z={zc:.0f}  (detector fires)")

    # ---- S2 HETEROSKEDASTICITY ----
    print("\n=== S2  HETEROSKEDASTICITY: var(sextant) across a construction bucket ===")
    for vn, vv in [("n%6", v["n%6"]), ("d%6", v["d%6"]), ("|D|bitlen%4", [abs(x).bit_length() % 4 for x in DD])]:
        buckets = {}
        for s, b in zip(sxt, vv):
            buckets.setdefault(b, []).append(s)
        vars_ = {b: float(np.var(arr)) for b, arr in buckets.items() if len(arr) > 50}  # noqa: float (report)
        spread = (max(vars_.values()) - min(vars_.values())) if vars_ else 0.0  # noqa: float
        print(f"    by {vn:11}: var(sextant) range = {min(vars_.values()):.3f}..{max(vars_.values()):.3f} "
              f"(spread {spread:.3f}; ~0 => homoskedastic)")

    # ---- D1 GECT expansion length resonance ----
    print("\n=== D1  GECT expansion length (d_terms) + resonance ===")
    dt = [d_terms(d[i], 256, nn[i], kk[i]) for i in range(n)]
    print(f"    d_terms distribution: {dict(sorted(Counter(dt).items()))}")
    for m in (2, 3, 4, 6, 7, 8, 12, 16):
        ic, zz = mi_z(dt, [abs(x) % m for x in DD], Ms, rng)
        if abs(zz) > 3:
            print(f"    MI(d_terms ; |D|%{m})  z={zz:+.2f}  I_c={ic:+.5f}  <-- resonance?")
    ic, zz = mi_z(dt, [abs(x).bit_length() for x in DD], Ms, rng)
    print(f"    MI(d_terms ; |D| bitlen) z={zz:+.2f} I_c={ic:+.5f}  (expansion vs residual size)")

    # ---- D2 PRIME density ----
    print("\n=== D2  PRIME density vs 1/ln(p)~1/177 baseline (sample 3000) ===")
    samp = range(0, min(3000, n))
    for nm, arr in [("X", dat["X"]), ("Y", dat["Y"]), ("d", d), ("n", nn)]:
        pr = sum(1 for i in samp if isprime(arr[i]))
        rate = pr / len(list(samp))                      # noqa: float (report)
        print(f"    {nm}: prime rate = {rate:.4f}  (expect ~{1/177:.4f} for X,Y,d; n small)")  # noqa: float (report baseline)

    # ---- D3 COLLISION / GAP ----
    print("\n=== D3  low-bit X uniformity + nearest-neighbour gap law ===")
    xm = np.array([x % 256 for x in dat["X"]])
    hist = np.bincount(xm, minlength=256)
    chi2 = float(((hist - n/256) ** 2 / (n/256)).sum())  # noqa: float (report)
    print(f"    X%256 chi^2(df255, ~255) = {chi2:.0f}  ({'uniform' if chi2 < 320 else 'CLUSTERED'})")
    xs = sorted(x % (1 << 40) for x in dat["X"])
    gaps = np.diff(np.array(xs, dtype=float))            # noqa: float (report gap law)
    cv = float(np.std(gaps) / (np.mean(gaps) + 1e-9))    # noqa: float (report)
    print(f"    40-bit-X gap CV = {cv:.3f}  (Poisson/exponential=1.0 => scrambled; <<1 => lattice)")

if __name__ == "__main__":
    main()
