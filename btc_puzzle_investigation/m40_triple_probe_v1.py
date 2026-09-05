#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
m40_triple_probe_v1.py — the 3-sign coupling probe on M40's forced mu6-invariant subspace.

The (g) pairwise result: MI(f(d1+d2); (f1,f2)) is entirely the forced anti-diagonal. This is the
exact 3-point analogue, TOTAL enumeration over the cube (d1,d2,d3) in [1,n)^3:

  MI3        = I( f(s); (f1,f2,f3) ),  s = d1+d2+d3 mod n
  gain3      = I( f(s); f3 | f1,f2 ) = MI3 - I(f(s); (f1,f2))   [both from the SAME cube joint]
               -- the N15 question: does a third point's sign ADD anything beyond two?
  MI3_rest   = the same MI off ALL forced vanishing loci (d_i+d_j != 0 and s != 0)
               -- any residual here is genuine 3-coupling, not degeneracy.

Scales for context: a forced-vanishing locus has cube mass ~ 4/n; Weil-type noise ~ n^{-1/2}
on rates; 1/n and 1/n^2 printed for calibration. Exact integers; floats only for MI display.
"""
import math, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m40_n15_exact_accounting_v1 import curve_walk

def mi_from_joint(cj, cA, cB, N):
    mi = 0.0
    for (a, b), c in cj.items():
        if c and cA[a] and cB[b]:
            mi += (c / N) * math.log2((c * N) / (cA[a] * cB[b]))
    return mi

print("=" * 108)
print(" M40 TRIPLE PROBE — 3-sign couplings of f(d)=chi2(y_[d]G), TOTAL enumeration of the cube")
print("=" * 108)
print(f" {'p':>4} {'n':>4} | {'MI3':>10} {'gain3':>10} {'MI3_rest':>10} {'excl':>7} | "
      f"{'1/n':>8} {'1/n^2':>8}  verdict")
for p in (43, 79, 127, 163, 211, 61):
    n, h, xs = curve_walk(p)
    leg = 1 if p % 4 == 1 else -1
    lam = next(g for g in range(2, n) if pow(g, 3, n) == 1 and g != 1)
    assert all(h[(lam * d) % n] == h[d] for d in range(n))
    assert all(h[(-d) % n] == leg * h[d] for d in range(n))

    N3 = (n - 1) ** 3
    cj3 = Counter()          # (fs, (f1,f2,f3))
    cj2 = Counter()          # (fs, (f1,f2))     [same cube, f3 marginalized]
    cS = Counter()           # fs
    cT3 = Counter()          # (f1,f2,f3)
    cT2 = Counter()          # (f1,f2)
    # restricted (off all forced vanishing loci)
    cj3r = Counter(); cSr = Counter(); cT3r = Counter(); Nr = 0
    for d1 in range(1, n):
        f1 = h[d1]
        neg1 = (n - d1) % n
        for d2 in range(1, n):
            f2 = h[d2]
            s12 = (d1 + d2) % n
            if s12 == 0:
                # full column still contributes to the unrestricted counts
                for d3 in range(1, n):
                    f3 = h[d3]
                    s = d3
                    fs = h[s]
                    cj3[(fs, (f1, f2, f3))] += 1
                    cj2[(fs, (f1, f2))] += 1
                    cS[fs] += 1; cT3[(f1, f2, f3)] += 1; cT2[(f1, f2)] += 1
                continue
            neg2 = (n - d2) % n
            negs = (n - s12) % n
            excl = {e for e in (neg1, neg2, negs) if e != 0}
            for d3 in range(1, n):
                f3 = h[d3]
                s = (s12 + d3) % n
                fs = h[s]
                cj3[(fs, (f1, f2, f3))] += 1
                cj2[(fs, (f1, f2))] += 1
                cS[fs] += 1; cT3[(f1, f2, f3)] += 1; cT2[(f1, f2)] += 1
                if d3 not in excl:
                    cj3r[(fs, (f1, f2, f3))] += 1; cSr[fs] += 1
                    cT3r[(f1, f2, f3)] += 1; Nr += 1
    MI3 = mi_from_joint(cj3, cS, cT3, N3)
    MI2_cube = mi_from_joint(cj2, cS, cT2, N3)
    gain3 = MI3 - MI2_cube
    MI3r = mi_from_joint(cj3r, cSr, cT3r, Nr)
    flat3 = MI3r < 2.0 / n
    print(f" {p:>4} {n:>4} | {MI3:10.6f} {gain3:10.6f} {MI3r:10.6f} {1 - Nr/N3:7.4f} | "
          f"{1/n:8.6f} {1/n**2:8.2e}  {'FLAT off forced loci' if flat3 else 'RESIDUAL — investigate'}",
          flush=True)
print("-" * 108)
print(" reading: MI3's bulk is the forced s=0 locus (cube mass ~1/n, deterministic fs=0 there);")
print(" gain3 > 0 would be a genuine third-point synergy; MI3_rest < 2/n means no genuine 3-coupling.")
print("=" * 108)
