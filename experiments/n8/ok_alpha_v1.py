#!/usr/bin/env python3
"""WHAT READS THE DEFICIT.  Exact Fraction, no float on any decision path.

|G(grid u {x,y})| = |G(grid)| * (1 - a_x - a_y + a_xy),  a_x = |A_x n G(grid)| / |G(grid)|,
generic a = 1/4.  Is the deficit ONE-BODY (each a_x inflated) or TWO-BODY (the overlap)?
Test: compare the actual survival against the one-body prediction (1-a_x)(1-a_y).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

def ivs(E):
    out = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: out.append((lo, hi))
    return out

def merge(iv):
    iv = sorted(iv); m = []
    for lo, hi in iv:
        if m and lo <= m[-1][1]: m[-1][1] = max(m[-1][1], hi)
        else: m.append([lo, hi])
    return m

def complement(m):
    g, cur = [], F(0)
    for lo, hi in m:
        if cur < lo: g.append((cur, lo))
        cur = max(cur, hi)
    if cur < 1: g.append((cur, F(1)))
    return g

def meas(iv): return sum(hi - lo for lo, hi in iv)

def inter(a, b):
    out, i, j = [], 0, 0
    while i < len(a) and j < len(b):
        lo, hi = max(a[i][0], b[j][0]), min(a[i][1], b[j][1])
        if lo < hi: out.append((lo, hi))
        if a[i][1] < b[j][1]: i += 1
        else: j += 1
    return out

GRID = [2, 6, 8, 10, 14]
G = complement(merge(ivs(GRID)))
MG = meas(G)
print(f"grid {GRID}:  |G(grid)| = {MG}\n")

def alpha(x):
    return meas(inter(merge(ivs([x])), G)) / MG

def survival(x, y):
    bad = merge(ivs([x]) + ivs([y]))
    return meas(inter(complement(bad), G)) / MG

print("E* = grid + {7,13}")
a7, a13 = alpha(7), alpha(13)
s = survival(7, 13)
print(f"  a_7  = {a7} = {float(a7):.4f}      (generic 1/4)")
print(f"  a_13 = {a13} = {float(a13):.4f}")
print(f"  actual survival        = {s} = {float(s):.6f}")
print(f"  one-body (1-a7)(1-a13) = {(1-a7)*(1-a13)} = {float((1-a7)*(1-a13)):.6f}")
print(f"  generic (3/4)^2        = {F(9,16)} = {float(F(9,16)):.6f}")
print(f"  -> one-body explains {float(((1-a7)*(1-a13) - F(9,16))/(s - F(9,16))):.1%}"
      f" of the deficit\n")

rows = []
for x, y in combinations(range(1, 41), 2):
    if x in GRID or y in GRID: continue
    T = sorted(GRID + [x, y])
    if reduce(gcd, T) != 1 or not any(e % 8 == 0 for e in T): continue
    ax, ay, sv = alpha(x), alpha(y), survival(x, y)
    ob = (1 - ax) * (1 - ay)
    rows.append((sv, x, y, ax, ay, ob))
rows.sort()
print(f"{len(rows)} pairs.  Ten smallest survival:")
print("    x   y     a_x      a_y    actual    one-body   one-body/actual")
for sv, x, y, ax, ay, ob in rows[:10]:
    mark = "  <- E*" if (x, y) == (7, 13) else ""
    print(f"   {x:>2}  {y:>2}   {float(ax):.4f}  {float(ay):.4f}  {float(sv):.6f}  "
          f"{float(ob):.6f}    {float(ob/sv):.3f}{mark}")

err = [abs(float(ob - sv)) for sv, x, y, ax, ay, ob in rows]
rel = [abs(float((ob - sv) / sv)) for sv, x, y, ax, ay, ob in rows]
print(f"\none-body predictor across all {len(rows)} pairs:")
print(f"  mean |absolute error| = {sum(err)/len(err):.6f}")
print(f"  mean |relative error| = {sum(rel)/len(rel):.4f}")
print(f"  max  |relative error| = {max(rel):.4f}")
# rank agreement
import statistics
by_actual = sorted(range(len(rows)), key=lambda i: rows[i][0])
by_ob     = sorted(range(len(rows)), key=lambda i: rows[i][5])
ra = {v: r for r, v in enumerate(by_actual)}; rb = {v: r for r, v in enumerate(by_ob)}
n = len(rows)
d2 = sum((ra[i] - rb[i]) ** 2 for i in range(n))
print(f"  Spearman rank correlation actual vs one-body = "
      f"{1 - 6*d2/(n*(n*n-1)):.4f}")
print(f"\n  a_x over all candidate single speeds (generic 1/4 = 0.25):")
al = sorted(((alpha(x), x) for x in range(1, 41) if x not in GRID), reverse=True)
print("   largest: " + ", ".join(f"x={x}:{float(a):.3f}" for a, x in al[:8]))
print("   smallest: " + ", ".join(f"x={x}:{float(a):.3f}" for a, x in al[-6:]))

# ---------------------------------------------------------------- the two-body term
def part_two():
    print("\n\nTWO-BODY: the overlap a_xy = |A_x n A_y n G(grid)| / |G(grid)|.")
    print("Generic (independent) overlap is a_x * a_y.  DISJOINT means a_xy = 0.\n")
    rows = []
    for x, y in combinations(range(1, 41), 2):
        if x in GRID or y in GRID: continue
        T = sorted(GRID + [x, y])
        if reduce(gcd, T) != 1 or not any(e % 8 == 0 for e in T): continue
        ax, ay = alpha(x), alpha(y)
        axy = meas(inter(inter(merge(ivs([x])), merge(ivs([y]))), G)) / MG
        sv = 1 - ax - ay + axy
        rows.append((sv, x, y, ax, ay, axy))
    rows.sort()
    nz = [r for r in rows if r[5] == 0]
    print(f"  {len(rows)} pairs; EXACTLY DISJOINT (a_xy = 0): {len(nz)} "
          f"({100*len(nz)//len(rows)}%)")
    print(f"  of the 10 smallest survival, disjoint: "
          f"{sum(1 for r in rows[:10] if r[5]==0)} / 10")
    print(f"  of the 10 largest  survival, disjoint: "
          f"{sum(1 for r in rows[-10:] if r[5]==0)} / 10")
    print("\n    x   y     a_x     a_y    a_xy   a_x*a_y   survival")
    for sv, x, y, ax, ay, axy in rows[:8]:
        mark = "  <- E*" if (x, y) == (7, 13) else ""
        print(f"   {x:>2}  {y:>2}  {float(ax):.4f}  {float(ay):.4f}  {float(axy):.4f}"
              f"   {float(ax*ay):.4f}   {float(sv):.6f}{mark}")
    # is a_x + a_y (the disjoint model) a better predictor than one-body?
    import math
    def spear(key):
        idx = sorted(range(len(rows)), key=key)
        r = {v: i for i, v in enumerate(idx)}
        ia = sorted(range(len(rows)), key=lambda i: rows[i][0])
        ra = {v: i for i, v in enumerate(ia)}
        n = len(rows); d2 = sum((ra[i]-r[i])**2 for i in range(n))
        return 1 - 6*d2/(n*(n*n-1))
    s_one = spear(lambda i: (1-rows[i][3])*(1-rows[i][4]))
    s_dis = spear(lambda i: 1-rows[i][3]-rows[i][4])
    s_sum = spear(lambda i: -(rows[i][3]+rows[i][4]))
    print(f"\n  Spearman vs actual survival:")
    print(f"    one-body independent  (1-a_x)(1-a_y) : {s_one:.4f}")
    print(f"    disjoint model        1 - a_x - a_y  : {s_dis:.4f}")
    print(f"    pure concentration    -(a_x + a_y)   : {s_sum:.4f}")
    ex = [r for r in rows if (r[1], r[2]) == (7, 13)][0]
    print(f"\n  at E*: disjoint model gives {float(1-ex[3]-ex[4])} = "
          f"{float(1-ex[3]-ex[4]):.6f}, actual {float(ex[0]):.6f}  "
          f"{'EXACT' if 1-ex[3]-ex[4] == ex[0] else 'differs'}")

part_two()
