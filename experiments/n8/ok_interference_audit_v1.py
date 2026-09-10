#!/usr/bin/env python3
"""SELF-AUDIT of INTERFERENCE_v1.  Three claims put under test.

 Q1  Is "net" a new predictor, or is it just the signed truncated sum?
     (net = m2+m3+m4+m5 = the signed sum.  So compare LIKE FOR LIKE across maxsupp.)
 Q2  Is the unsigned sum really constant across tuples, or is that a cutoff artefact?
     The absolute series DIVERGES (AB_SPLIT_v1 A2), so its value is set by where I cut.
     Test: vary K and maxsupp and see whether the spread and the ordering survive.
 Q3  Does the parity SPLIT add predictive power over the raw signed sum?  (If net is the
     signed sum, it cannot -- state that plainly rather than implying otherwise.)
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, sin, pi
from functools import reduce
import statistics as st

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

def sums(T, K, maxsupp):
    """solve for the LAST coordinate instead of enumerating it: (2K)^(r-1), not (2K)^r."""
    n = len(T); signed = unsigned = 0.0; ev = od = 0.0
    rng = [j for j in range(-K, K+1) if j != 0]
    for r in range(2, maxsupp + 1):
        for S in combinations(range(n), r):
            last = T[S[-1]]
            for ks in product(rng, repeat=r-1):
                tot = sum(ks[i]*T[S[i]] for i in range(r-1))
                if tot % last: continue
                kl = -tot // last
                if kl == 0 or abs(kl) > K: continue
                full = ks + (kl,)
                if reduce(gcd, [abs(x) for x in full]) != 1: continue
                p = 0.75 ** (n - r)
                for x in full: p *= fh(x)
                signed += p; unsigned += abs(p)
                if r % 2 == 0: ev += p
                else: od += p
    return signed, unsigned, ev, od

def spear(vals, ref):
    n = len(ref)
    ra = sorted(range(n), key=lambda i: ref[i]); rb = sorted(range(n), key=lambda i: vals[i])
    r1 = {v: i for i, v in enumerate(ra)}; r2 = {v: i for i, v in enumerate(rb)}
    return 1 - 6*sum((r1[i]-r2[i])**2 for i in range(n))/(n*(n*n-1))

tuples = [T for T in combinations(range(1, 17), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
tuples = tuples[::max(1, len(tuples)//60)]
G = [float(gmeas(list(T))) for T in tuples]
n = len(tuples)
print(f"{n} Case-2 tuples from [1..16]\n")

print("Q1 -- LIKE FOR LIKE: Spearman(|G|, signed sum) as the truncation grows")
print("     K  maxsupp   Spearman(signed)   Spearman(net)   identical?")
for K, ms in ((3,3),(4,3),(4,4),(4,5),(5,5)):
    S = [sums(list(T), K, ms) for T in tuples]
    sg = [x[0] for x in S]; nt = [x[2]+x[3] for x in S]
    print(f"    {K:>2}   {ms:>4}      {spear(sg,G):+.4f}          {spear(nt,G):+.4f}"
          f"        {'YES -- net IS the signed sum' if max(abs(a-b) for a,b in zip(sg,nt)) < 1e-12 else 'no'}")

print("\nQ2 -- is the unsigned sum constant, or a cutoff artefact?")
print("     K  maxsupp     mean    stdev    CV     min      max   max/min")
for K, ms in ((3,3),(4,4),(4,5),(5,5)):
    U = [sums(list(T), K, ms)[1] for T in tuples]
    cv = st.pstdev(U)/st.mean(U)
    print(f"    {K:>2}   {ms:>4}   {st.mean(U):.5f}  {st.pstdev(U):.5f}  {cv:.3f} "
          f"{min(U):.5f}  {max(U):.5f}   {max(U)/min(U):.2f}")

print("\nQ3 -- does the parity SPLIT add anything over the raw signed sum?")
S = [sums(list(T), 4, 5) for T in tuples]
ev = [x[2] for x in S]; od = [x[3] for x in S]; sg = [x[0] for x in S]
print(f"     Spearman(|G|, even mass alone) = {spear(ev,G):+.4f}")
print(f"     Spearman(|G|, odd  mass alone) = {spear(od,G):+.4f}")
print(f"     Spearman(|G|, signed = net   ) = {spear(sg,G):+.4f}")
print(f"     best single half                = {max(spear(ev,G), spear(od,G)):+.4f}")
print("     -> the split EXPLAINS the sign law; it is not an independent predictor.")
