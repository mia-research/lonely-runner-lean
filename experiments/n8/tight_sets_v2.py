"""
n=8 tight-set enumeration -- v2.  Exact rational arithmetic (Fraction), no floats
in any decision.  Supersedes tight_sets_v1.py, which enumerated crossings globally
and was too slow; v2 decides tightness by exact interval coverage instead.

M(T) := max_t min_{v in T} ||v t||,  T = 7 distinct positive integers, gcd = 1.
LRC(8) (Rosenfeld 2025) gives M(T) >= 1/8.   TIGHT  <=>  M(T) = 1/8 exactly.

Tightness test (exact, and the reason v2 is fast):
  M(T) > 1/8  <=>  the open bad set  U = union over v,k of ( k/v - 1/(8v), k/v + 1/(8v) )
  leaves a POSITIVE-LENGTH gap in [0,1].   A zero-length gap (two intervals meeting
  at a point) is the tight case.  So: sort the O(sum v) interval endpoints and sweep.

M(T) inside a gap: min_v ||v t|| is piecewise linear there, so its max sits at a
gap endpoint or at a crossing t = k/(2v), k/(v_i+v_j), k/(v_i-v_j) inside the gap.

Prefilter (PROVED -- the witness ladder, docs/n8/N11_TRANSLATION_v1.md sec 3):
q in {2..7} dividing no element of T forces M(T) >= 1/q > 1/8.  So a tight T holds
a multiple of 4, of 5, of 6 and of 7.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def frac_norm(x):
    r = x - (x.numerator // x.denominator)
    return r if r <= F(1,2) else 1 - r

def gaps_of(T):
    """Maximal positive-length gaps of [0,1] \\ U(T), exact."""
    iv = []
    for v in T:
        w = F(1, 8*v)
        for k in range(0, v+1):
            lo, hi = F(k,v) - w, F(k,v) + w
            if hi <= 0 or lo >= 1: continue
            iv.append((max(lo, F(0)), min(hi, F(1))))
    iv.sort()
    out, cur = [], F(0)
    for lo, hi in iv:
        if lo > cur: out.append((cur, lo))
        if hi > cur: cur = hi
    if cur < 1: out.append((cur, F(1)))
    return out

def M_in_gaps(T, gs):
    dens = set(2*v for v in T)
    for a, b in combinations(T, 2):
        dens.add(a+b); dens.add(abs(a-b))
    dens.discard(0)
    best = F(1,8)
    for glo, ghi in gs:
        cands = {glo, ghi}
        for d in dens:
            k0 = int(glo*d)
            for k in range(k0, k0+3):
                t = F(k, d)
                if glo <= t <= ghi: cands.add(t)
        for t in cands:
            m = min(frac_norm(v*t) for v in T)
            if m > best: best = m
    return best

def has_ladder(T):
    return all(any(v % q == 0 for v in T) for q in (4,5,6,7))

def main(V):
    tight, near, ncand = [], [], 0
    for T in combinations(range(1, V+1), 7):
        if not has_ladder(T): continue
        g = 0
        for v in T: g = gcd(g, v)
        if g != 1: continue
        ncand += 1
        gs = gaps_of(T)
        if not gs:
            tight.append(T)
        else:
            m = M_in_gaps(T, gs)
            if m < F(9,64): near.append((m, T))
    print(f"V={V}: {ncand} candidates past ladder+gcd filter")
    print(f"TIGHT (M = 1/8 exactly): {len(tight)}")
    for T in tight: print("   ", T)
    near.sort()
    print(f"NEAR-TIGHT (1/8 < M < 9/64): {len(near)} (20 closest)")
    for m, T in near[:20]:
        print(f"    {str(m):>12} ~{float(m):.6f}  {T}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 24)
