"""
n=8 tight-set enumeration.  Exact rational arithmetic throughout (Fraction).

M(T) := max_t min_{v in T} ||v t||   for T a set of 7 distinct positive integers.
LRC(8) (Rosenfeld 2025) says M(T) >= 1/8 always.  TIGHT means M(T) = 1/8 exactly.

Exactness: ||v t|| is piecewise linear in t with breakpoints at t = k/(2v).
min over T is piecewise linear; its local maxima sit at a breakpoint k/(2v_i)
or at a crossing of two opposite-slope pieces, t = k/(v_i+v_j), or of two
same-slope pieces, t = k/(v_i-v_j).  Evaluating min_i ||v_i t|| on that finite
exact candidate set attains the global max.  No floating point anywhere.

Prefilter (PROVED, the "witness ladder" of docs/n8/N11_TRANSLATION_v1.md sec 3):
if q in {2..7} divides no element of T, then t = 1/q gives ||v t|| >= 1/q > 1/8
for every v, so M(T) > 1/8 and T is not tight.  Hence a tight T must contain a
multiple of 4, of 5, of 6 and of 7 (2 and 3 follow).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def frac_norm(x):
    """||x|| = distance from x to nearest integer, exact."""
    r = x - int(x)          # int() truncates toward 0
    if r < 0: r += 1
    return r if r <= F(1,2) else 1 - r

def M(T):
    """max_t min_v ||v t||, exact."""
    dens = set()
    for v in T:
        dens.add(2*v)
    for a, b in combinations(T, 2):
        dens.add(a+b)
        if a != b: dens.add(abs(a-b))
    best = F(0)
    for d in dens:
        if d == 0: continue
        for k in range(1, d):          # t in (0,1); symmetric so this suffices
            t = F(k, d)
            m = min(frac_norm(v*t) for v in T)
            if m > best:
                best = m
                if best > F(1,4): pass
    return best

def has_ladder(T):
    for q in (4,5,6,7):
        if not any(v % q == 0 for v in T):
            return False
    return True

def main(V):
    thresh = F(1,8)
    tight, near = [], []
    n_cand = 0
    for T in combinations(range(1, V+1), 7):
        if not has_ladder(T): continue
        g = 0
        for v in T: g = gcd(g, v)
        if g != 1: continue
        n_cand += 1
        m = M(T)
        if m == thresh:
            tight.append(T)
        elif m < F(9,64):          # 1/8 < m < 9/64 = 0.140625
            near.append((m, T))
    print(f"V = {V}: {n_cand} candidate 7-sets passed ladder+gcd filter")
    print(f"TIGHT (M = 1/8 exactly): {len(tight)}")
    for T in tight: print("   ", T)
    near.sort()
    print(f"NEAR-TIGHT (1/8 < M < 9/64): {len(near)}  (showing 20 closest)")
    for m, T in near[:20]:
        print(f"    {str(m):>10}  ~{float(m):.6f}   {T}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 24)
