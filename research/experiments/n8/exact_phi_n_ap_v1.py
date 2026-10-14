#!/usr/bin/env python3
"""The phi(n) AP isolation law, verified in EXACT rational arithmetic.

The published verification (lrc_ap_phi_n_law_v1) is IEEE-754 with ulp-aware
tolerances.  That is not a precision quibble here: Proposition 4.1 of that same
paper says exact grid formation is a measure-zero affine set with ZERO stability
radius, so a float experiment cannot distinguish "the law failed" from "the input
was not exactly on the variety".  Its own section 6 "n = 8 anomaly" is that
confusion.  Everything below is Fraction; no float is constructed, and no
tolerance is used or needed.

METHOD.  This is the paper's OWN Boundary Set Method (section 2.2, Lemmas 2.1-2.2,
Algorithm 2.1), which is exact by construction and was devised to be exact -- isolation
status changes only at the boundary times t = (k +- 1/n)/v, and between consecutive
boundary times the predicate is constant, so the evaluation is event-complete.  Running
that method in floats discards the property it was built to have.  Nothing below is new
method; it is the stated method executed over Fraction.

OBJECT.  For a speed tuple T and bound 1/n, the LONELY SET is
    L(T,n) = { t in [0,1) : ||v t|| >= 1/n for every v in T }.
For each v, { t : ||v t|| >= 1/n } is a union of closed intervals whose endpoints
are exactly the crossings t = (m +- 1/n)/v.  So the predicate is constant between
consecutive crossings, and L is computed exactly by evaluating at every crossing
AND at every midpoint between consecutive crossings -- the midpoints find the
positive-length components, the crossings themselves find the ISOLATED points,
which is what the AP case consists of.
"""
from fractions import Fraction as F
from math import gcd
from itertools import combinations

def norm(x):
    r = x - (x.numerator // x.denominator)
    return min(r, 1 - r)

def lonely_set(T, n):
    """Exact L(T,n) as (isolated_points, positive_length_intervals)."""
    b = F(1, n)
    cuts = {F(0), F(1)}
    for v in T:
        m = 0
        while F(m - 1, v) <= 1:
            for e in (F(m) - b, F(m) + b):
                t = e / v
                if 0 <= t <= 1:
                    cuts.add(t)
            m += 1
    cuts = sorted(cuts)
    ok = lambda t: all(norm(t * v) >= b for v in T)
    pts, ivs = [], []
    for a, c in zip(cuts, cuts[1:]):
        if ok((a + c) / 2):
            ivs.append((a, c))
    covered = lambda t: any(a <= t <= c for a, c in ivs)
    for t in cuts:
        if t < 1 and ok(t) and not covered(t):
            pts.append(t)
    return pts, ivs

def phi(n):
    return sum(1 for a in range(1, n + 1) if gcd(a, n) == 1)

print("PART 1 — Theorem 3.1(a),(b),(d) for AP relative speeds (delta, 2delta, ..., (n-1)delta)")
print("         exact lonely set at bound 1/n; delta scales t, so delta = 1 is general")
print(f"{'n':>3} {'phi(n)':>7} {'isolated pts':>13} {'intervals':>10} {'points':>34} {'law holds':>10}")
allok = True
for n in range(3, 13):
    T = list(range(1, n))
    pts, ivs = lonely_set(T, n)
    want = [F(r, n) for r in range(1, n) if gcd(r, n) == 1]
    ok = (sorted(pts) == want) and not ivs
    allok &= ok
    print(f"{n:>3} {phi(n):>7} {len(pts):>13} {len(ivs):>10} "
          f"{str([str(x) for x in sorted(pts)]):>34} {str(ok):>10}")
print(f"  all n: exactly phi(n) isolated lonely points at r/n with gcd(r,n)=1, "
      f"zero positive-length components -> {allok}")

print()
print("PART 2 — n = 8 specifically (the paper's section 6 anomaly case)")
pts, ivs = lonely_set([1, 2, 3, 4, 5, 6, 7], 8)
print("  isolated lonely times:", [str(x) for x in sorted(pts)],
      " = {1,3,5,7}/8 :", sorted(pts) == [F(1,8), F(3,8), F(5,8), F(7,8)])
print("  positive-length components:", len(ivs), " -> zero stability radius, exactly")
for t in sorted(pts):
    print(f"    t = {t}:  ||j t|| = {[str(norm(t*j)) for j in range(1,8)]}   min = {min(norm(t*j) for j in range(1,8))}")

print()
print("PART 3 — Theorem 3.1(c): positions are a translate of the uniform n-grid")
print("         exact check for APs with common start, v_i = v0 + (i-1)*delta")
bad = 0
for n in range(3, 11):
    for v0 in range(1, 6):
        for d in range(1, 6):
            for r in range(1, n):
                if gcd(r, n) != 1: continue
                t = F(r, n * d)
                pos = sorted({F((v0 + i * d) * t) - ((v0 + i * d) * t).numerator //
                              ((v0 + i * d) * t).denominator for i in range(n)})
                alpha = pos[0]
                grid = sorted({alpha + F(j, n) - (1 if alpha + F(j, n) >= 1 else 0)
                               for j in range(n)})
                if pos != grid: bad += 1
print(f"  translate-of-grid failures over all (n<=10, v0<=5, delta<=5, r coprime): {bad}")

print()
print("PART 4 — non-AP control, exact.  Does a non-AP tuple show the phi(n) signature")
print("         (exactly phi(n) isolated lonely points and no interval)?")
print(f"{'n':>3} {'tuples tested':>14} {'phi(n) signature':>17} {'has interval':>13} {'empty L':>8}")
for n in range(4, 9):
    tested = sig = withiv = empty = 0
    for T in combinations(range(1, 4 * n), n - 1):
        T = list(T)
        d = {T[i+1] - T[i] for i in range(len(T) - 1)}
        if len(d) == 1 and T[0] == list(d)[0]:
            continue                      # skip the AP family itself
        tested += 1
        pts, ivs = lonely_set(T, n)
        if ivs: withiv += 1
        if not pts and not ivs: empty += 1
        if len(pts) == phi(n) and not ivs: sig += 1
        if tested >= 400: break
    print(f"{n:>3} {tested:>14} {sig:>17} {withiv:>13} {empty:>8}")
