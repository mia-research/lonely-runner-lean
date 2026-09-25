"""Shift openings by level, on SixResidual and EightResidual.

At a flank e, fix a level h dividing e and put f = e/h.  The opening numerator a = 1 + k*f is an
opening (a = n*j + 1) exactly when n | k*f, and only k mod n*h matters.  Writing
p = d // f and r = d % f,

    d*a mod n*e  =  f * ((k*d + p) mod n*h)  +  r,

so d is clear (Theorem 10: reading in [e, (n-1)e]) exactly when c = (k*d + p) mod n*h satisfies
h <= c < (n-1)*h, or c = (n-1)*h with r = 0.  Each reading moves affinely in k with slope d.

Level 1 is the free-flank shift a = k*e + 1; it has gcd(e, n) openings, so at even n every even
flank has at least two, while at prime n a non-multiple flank has only a = 1.  The case list
(OrderSixN, OrderEightCasesN) tries level 1 only at multiples of n.

The residuals are rebuilt field by field: SixResidual from OrderSixN's docstring,
EightResidual from eight_residual_count_v1.py.  The formula is checked against Theorem 10
directly on every opening it is used for in the first 300 sets of each residual.
"""
import itertools, time
from math import gcd
from collections import Counter

# ---------- order six: SixResidual ----------
def free_flank(n, S, e):
    for d in S:
        if d != e and d % n == 0:
            if not (e <= d % (n * e) <= (n - 1) * e): return False
    return any(all((d * k + d // e) % n not in (0, n - 1) for d in S if d % n) for k in range(n))

def six_residual(S):
    if not all(any(d % q == 0 for d in S) for q in (4, 5, 6)): return False
    if not max(S) > 5 * min(S): return False
    if sum(max(2, gcd(d, 6)) for d in S if d % 6) < 6: return False
    if any(free_flank(6, S, e) for e in S if e % 6 == 0): return False
    s = sorted(S)
    return not s[-1] > 5 * s[-2]

def bhk(S):
    v1, v2, v3, v4, v5 = sorted(S); D = v3 - v2
    if v3 <= 3 * v1: return "S8 v3<=3v1"
    if v1 % D == 0: return "S5 D|v1"
    if v3 % D == 0: return "S6 D|v3"
    return "S7 generic"

# ---------- order eight: EightResidual (as eight_residual_count_v1.py) ----------
def shifted(S):
    e = max(S)
    if e % 8: return False
    if any(d % 8 == 0 for d in S if d != e): return False
    return sum(1 for d in S if d != e and d % 2) <= 3

def first_lap(S):
    for e in S:
        others = [d for d in S if d != e]
        lo, hi = min(others), max(others)
        A = 1
        while hi * A <= 7 * e:
            if lo * A >= e: return True
            A += 8
    return False

def minus_seven(S):
    return any(all(e <= (-7 * d) % (8 * e) <= 7 * e for d in S) for e in S)

def eight_residual(S):
    if not any(d % 2 for d in S): return False
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): return False
    if not max(S) > 7 * min(S): return False
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return False
    if any(free_flank(8, S, e) for e in S if e % 8 == 0): return False
    if shifted(S): return False
    s = sorted(S)
    if s[-1] > 7 * s[-2]: return False
    return not (first_lap(S) or minus_seven(S))

# ---------- the level family ----------
def band(n, S, e, a):
    return all(e <= (d * a) % (n * e) <= (n - 1) * e for d in S)

def level_ks(n, S, e, h, check=False):
    f = e // h
    out = []
    for k in range(n * h):
        if (k * f) % n: continue
        ok = True
        for d in S:
            c = (k * d + d // f) % (n * h)
            if not (h <= c < (n - 1) * h or (c == (n - 1) * h and d % f == 0)):
                ok = False; break
        if check: assert ok == band(n, S, e, 1 + k * f), (n, S, e, h, k)
        if ok: out.append(k)
    return out

def min_level(n, S, check=False):
    best = None
    for e in S:
        for h in range(1, e + 1):
            if e % h: continue
            if best is not None and h >= best: break
            if level_ks(n, S, e, h, check): best = h; break
    return best

def level1_classes(n, S):
    return tuple(sorted({gcd(e, n) for e in S if level_ks(n, S, e, 1)}))

def run(n, R, label, split):
    print(f"== order {n}: {label}: {len(R)} sets")
    for S in R[:300]: min_level(n, S, check=True)
    L = [min_level(n, S) for S in R]
    assert all(h is not None for h in L)          # level e is Theorem 10 itself
    c = Counter(L); tot = 0
    print("  least level h at which some flank has a working opening:")
    for h in sorted(c):
        tot += c[h]; print(f"    h = {h:2d}: {c[h]:6d}   cumulative {tot:6d}")
    cls = Counter(level1_classes(n, S) for S, h in zip(R, L) if h == 1)
    print("  level 1, by the classes gcd(e, n) of the flanks carrying it:", dict(cls.most_common()))
    print(f"  level 1 at multiples of {n} only (what the case list tries): "
          f"{sum(1 for S in R if any(e % n == 0 and level_ks(n, S, e, 1) for e in S))}")
    by = {}
    for S, h in zip(R, L):
        b = split(S); by.setdefault(b, Counter())[h] += 1
    print("  least level, by", "BHK case:" if n == 6 else "shape (multiples of 8, others):")
    for b in sorted(by):
        print(f"    {b}: {dict(sorted(by[b].items()))}")

t0 = time.time()
R6 = [S for S in itertools.combinations(range(1, 41), 5) if six_residual(S)]
run(6, R6, "SixResidual, 5-subsets of [1,40]", bhk)
R8 = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
run(8, R8, "EightResidual, 7-subsets of [1,30]",
    lambda S: (sum(d % 8 == 0 for d in S), sum(d % 8 != 0 for d in S)))
print(f"{time.time() - t0:.0f}s")
