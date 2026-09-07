#!/usr/bin/env python3
"""Exact LR-property check for integer speeds -- NO floating point anywhere.

Replaces the float grid scan used on 2026-09-07 to claim that the p=41 witness
T = {1,4,12,13,14,16,20} "has the LR property (max_t min_i ||t v_i|| = 0.14284 > 1/8)".
That number came from t = a/200000 in IEEE-754 doubles and was reported as evidence.
Everything below is Fraction arithmetic; no float is constructed.

COMPLETENESS OF THE CANDIDATE SET.  f(t) = min_i ||v_i t|| is continuous and
piecewise linear on [0,1], with each ||v_i t|| linear between consecutive points of
{ m/(2 v_i) }.  A local maximum of the lower envelope f occurs either at a peak of
whichever ||v_i t|| is active -- t = (2m+1)/(2 v_i) -- or where two of them cross.
Crossings solve  v_i t - a = +-(v_j t - b)  with a,b integers, giving
t = (a -+ b)/(v_i -+ v_j).  So every local maximum of f lies in

    { m/(2 v_i) } u { m/(v_i + v_j) } u { m/|v_i - v_j| }   (m integer, t in [0,1])

which is the candidate set enumerated here.  By the symmetry ||v(1-t)|| = ||v t||
it suffices to scan [0, 1/2].
"""
from fractions import Fraction as F
from itertools import combinations

def norm(x):
    """||x|| = distance to nearest integer, exact."""
    r = x - (x.numerator // x.denominator)      # fractional part in [0,1)
    return min(r, 1 - r)

def max_min_norm(speeds):
    dens = set()
    for v in speeds:
        dens.add(2 * v)
    for a, b in combinations(speeds, 2):
        dens.add(a + b)
        if a != b:
            dens.add(abs(a - b))
    dens.discard(0)
    best, arg = F(0), None
    for d in sorted(dens):
        for m in range(0, d // 2 + 1):
            t = F(m, d)
            if t > F(1, 2):
                break
            val = min(norm(t * v) for v in speeds)
            if val > best:
                best, arg = val, t
    return best, arg

if __name__ == "__main__":
    cases = [
        ("p=41 bad cover (k=7)", [1, 4, 12, 13, 14, 16, 20], F(1, 8)),
        ("k=6 obstruction",      [1, 6, 7, 8, 9, 15],        F(1, 7)),
        ("n=4 example {1,2,3}",  [1, 2, 3],                  F(1, 4)),
        ("n=3 {1,2}",            [1, 2],                     F(1, 3)),
    ]
    for name, T, thr in cases:
        m, t = max_min_norm(T)
        print(f"{name}")
        print(f"   speeds {T}")
        print(f"   max_t min_i ||t v_i|| = {m}  attained at t = {t}")
        print(f"   threshold {thr};  LR property at that bound: {m >= thr}"
              f"   (exact comparison {m.numerator}*{thr.denominator} "
              f"{'>=' if m >= thr else '<'} {thr.numerator}*{m.denominator})")
        print(f"   per-speed at t: {[str(norm(t*v)) for v in T]}")
        print()
