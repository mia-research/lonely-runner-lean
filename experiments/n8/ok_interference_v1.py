#!/usr/bin/env python3
"""INTERFERENCE: do the resonance terms REINFORCE or CANCEL?

|G| = sum_{k.e=0} prod_j fhat(k_j),  fhat(k) = -sin(pi k/4)/(pi k).
The SIGN of a term depends only on k mod 8 (negative for |k| = 1,2,3 mod 8, positive for
5,6,7, zero for 0,4), and k.e = 0 forces k.(e mod 8) = 0 mod 8.  So the sign structure is
governed by the RESIDUES e mod 8 -- the same data as the block/Klein structure -- while the
magnitudes are governed by the actual integers.

COHERENCE = |signed sum| / unsigned sum  over the short vectors.  Near 1 = constructive
(terms reinforce); near 0 = destructive (they cancel).

|G| is exact Fraction.  The truncated Fourier sums are FLOAT and are a diagnostic only --
they are never the source of a claim.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, sin, pi
from functools import reduce
import sys

def gmeas(E):
    iv = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: iv.append((lo, hi))
    iv.sort(); mg = []
    for lo, hi in iv:
        if mg and lo <= mg[-1][1]: mg[-1][1] = max(mg[-1][1], hi)
        else: mg.append([lo, hi])
    cur = tot = F(0)
    for lo, hi in mg:
        if cur < lo: tot += lo - cur
        cur = max(cur, hi)
    return tot + (1 - cur if cur < 1 else 0)

def fh(k): return -sin(pi * k / 4) / (pi * k)

def interference(T, K=4, maxsupp=4):
    """signed and unsigned truncated sums over resonances with |k_j| <= K, support <= maxsupp."""
    n = len(T); signed = unsigned = 0.0; cnt = 0
    for r in range(2, maxsupp + 1):
        for S in combinations(range(n), r):
            for ks in product([j for j in range(-K, K + 1) if j != 0], repeat=r):
                if sum(ks[i] * T[S[i]] for i in range(r)) != 0: continue
                if reduce(gcd, [abs(x) for x in ks]) != 1: continue    # primitive only
                p = (0.75) ** (n - r)
                for i in range(r): p *= fh(ks[i])
                signed += p; unsigned += abs(p); cnt += 1
    return signed, unsigned, cnt

def report(T, label=""):
    g = gmeas(list(T)); s, u, c = interference(list(T))
    coh = abs(s) / u if u else 0.0
    print(f"  {str(tuple(T)):<28} |G|={float(g):.6f}  terms={c:>4}  "
          f"signed={s:+.5f}  unsigned={u:.5f}  coherence={coh:.4f}  {label}")
    return g, s, u, coh

print("Extremum, its neighbours on the same grid, and easy tuples")
print("  (main term (3/4)^7 = 0.133484)\n")
for T, lab in (([2,6,7,8,10,13,14], "<- E*, the extremum"),
               ([2,6,8,10,11,14,17], "same grid, next-smallest |G|"),
               ([2,6,8,10,14,11,22], "same grid"),
               ([2,6,8,10,14,3,32],  "same grid, both added speeds FREE"),
               ([1,3,5,7,13,15,24],  "an easy tuple"),
               ([3,10,14,15,16,19,21], "an easy tuple")):
    report(sorted(T), lab)

print("\nCorrelation over a Case-2 sample")
tuples = [T for T in combinations(range(1, 17), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
tuples = tuples[::max(1, len(tuples) // 120)]
rows = []
for T in tuples:
    g = gmeas(list(T)); s, u, c = interference(list(T))
    if u > 0: rows.append((float(g), abs(s) / u, s, u))
rows.sort()
n = len(rows)
lo = rows[:n // 5]; hi = rows[-n // 5:]
import statistics as st
print(f"  {n} tuples.  bottom fifth by |G| vs top fifth:")
print(f"    coherence   : {st.mean(x[1] for x in lo):.4f}  vs  {st.mean(x[1] for x in hi):.4f}")
print(f"    signed sum  : {st.mean(x[2] for x in lo):+.5f}  vs  {st.mean(x[2] for x in hi):+.5f}")
print(f"    unsigned sum: {st.mean(x[3] for x in lo):.5f}  vs  {st.mean(x[3] for x in hi):.5f}")
ra = sorted(range(n), key=lambda i: rows[i][0]); rb = sorted(range(n), key=lambda i: rows[i][2])
r1 = {v: i for i, v in enumerate(ra)}; r2 = {v: i for i, v in enumerate(rb)}
d2 = sum((r1[i] - r2[i]) ** 2 for i in range(n))
print(f"    Spearman(|G|, signed truncated sum) = {1 - 6*d2/(n*(n*n-1)):.4f}")
ra2 = sorted(range(n), key=lambda i: rows[i][1])
r3 = {v: i for i, v in enumerate(ra2)}
d3 = sum((r1[i] - r3[i]) ** 2 for i in range(n))
print(f"    Spearman(|G|, coherence)            = {1 - 6*d3/(n*(n*n-1)):.4f}")

# ---------------------------------------------------------------- support parity
def by_support(T, K=4, maxsupp=5):
    n = len(T); m = {r: 0.0 for r in range(2, maxsupp + 1)}
    for r in range(2, maxsupp + 1):
        for S in combinations(range(n), r):
            for ks in product([j for j in range(-K, K + 1) if j != 0], repeat=r):
                if sum(ks[i] * T[S[i]] for i in range(r)) != 0: continue
                if reduce(gcd, [abs(x) for x in ks]) != 1: continue
                p = (0.75) ** (n - r)
                for i in range(r): p *= fh(ks[i])
                m[r] += p
    return m

def parity_report():
    print("\n\nMASS BY SUPPORT SIZE  (sign = (-1)^support for short vectors)")
    print("  tuple                        |G|        r=2       r=3       r=4       r=5"
          "     even-odd")
    for T, lab in (([2,6,7,8,10,13,14], "E*"),
                   ([2,6,8,10,11,14,17], ""),
                   ([2,3,6,8,10,14,32], "free adds"),
                   ([1,3,5,7,13,15,24], "easy"),
                   ([3,10,14,15,16,19,21], "easy")):
        T = sorted(T); g = gmeas(T); m = by_support(T)
        ev = m[2] + m[4]; od = m[3] + m[5]
        print(f"  {str(tuple(T)):<28} {float(g):.6f} "
              + " ".join(f"{m[r]:+.5f}" for r in (2,3,4,5))
              + f"   {ev+od:+.5f}  {lab}")
    tuples = [T for T in combinations(range(1, 17), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//90)]
    rows = []
    for T in tuples:
        g = gmeas(list(T)); m = by_support(list(T))
        rows.append((float(g), m[2] + m[4], m[3] + m[5], m))
    rows.sort(); n = len(rows)
    import statistics as st
    lo, hi = rows[:n//4], rows[-n//4:]
    print(f"\n  {n} tuples, bottom quarter by |G| vs top quarter:")
    print(f"    EVEN support mass (r=2,4), constructive : "
          f"{st.mean(x[1] for x in lo):+.5f}  vs  {st.mean(x[1] for x in hi):+.5f}")
    print(f"    ODD  support mass (r=3,5), destructive  : "
          f"{st.mean(x[2] for x in lo):+.5f}  vs  {st.mean(x[2] for x in hi):+.5f}")
    print(f"    net                                     : "
          f"{st.mean(x[1]+x[2] for x in lo):+.5f}  vs  {st.mean(x[1]+x[2] for x in hi):+.5f}")
    ra = sorted(range(n), key=lambda i: rows[i][0])
    for name, key in (("even mass", lambda i: rows[i][1]),
                      ("odd mass ", lambda i: rows[i][2]),
                      ("net      ", lambda i: rows[i][1] + rows[i][2])):
        rb = sorted(range(n), key=key)
        r1 = {v: i for i, v in enumerate(ra)}; r2 = {v: i for i, v in enumerate(rb)}
        d2 = sum((r1[i] - r2[i])**2 for i in range(n))
        print(f"    Spearman(|G|, {name}) = {1 - 6*d2/(n*(n*n-1)):+.4f}")

parity_report()
