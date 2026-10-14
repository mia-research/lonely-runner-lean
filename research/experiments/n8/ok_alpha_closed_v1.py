#!/usr/bin/env python3
"""CLOSED FORM FOR alpha.  Exact Fraction; no float on any decision path.

phi(Y) = |{y in [0,Y] : ||y|| < 1/8}| satisfies phi(Y) = floor(Y)/4 + phi({Y}), and
|A_x n [0,s]| = phi(x s)/x = s/4 + psi({x s})/x  where  psi(t) = phi(t) - t/4:

    psi(t) =  3t/4          on [0, 1/8]
              1/8 - t/4     on [1/8, 7/8]
              3(t-1)/4      on [7/8, 1]          range exactly [-3/32, 3/32].

Summing over the components (u_i, v_i) of G = G(grid):

    |A_x n G| = |G|/4 + S_x / x ,     S_x = sum_i [ psi({x v_i}) - psi({x u_i}) ]

    >>>  alpha_x = 1/4 + S_x / (x |G|)  <<<        exact, elementary, endpoint-only.

Consequences, both immediate:
  * |S_x| <= (3/16) N  (N = number of components of G), so
        |alpha_x - 1/4| <= 3N / (16 x |G|)  --  alpha_x -> 1/4 at rate O(N/x);
  * the bound is DILATION INVARIANT (N scales with lambda, x with lambda).
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

def psi(t):
    t = t - int(t)
    if t < 0: t += 1
    if t <= F(1, 8):  return 3 * t / 4
    if t <= F(7, 8):  return F(1, 8) - t / 4
    return 3 * (t - 1) / 4

def alpha_closed(x, G, MG):
    S = sum(psi(F(x) * v) - psi(F(x) * u) for u, v in G)
    return F(1, 4) + S / (x * MG), S

def alpha_direct(x, G, MG):
    return meas(inter(merge(ivs([x])), G)) / MG

GRID = [2, 6, 8, 10, 14]
G = complement(merge(ivs(GRID))); MG = meas(G); N = len(G)
print(f"grid {GRID}:  |G| = {MG},  components N = {N}\n")

print("VERIFY the closed form against direct interval computation, x = 1..200")
bad = 0; worst = None
for x in range(1, 201):
    a1, S = alpha_closed(x, G, MG)
    a2 = alpha_direct(x, G, MG)
    if a1 != a2:
        bad += 1
        if worst is None: worst = (x, a1, a2)
print(f"  mismatches: {bad} / 200" + (f"   first {worst}" if worst else "   (exact)"))

print(f"\nThe named values, from the closed form:")
for x in (7, 13, 4, 22, 3, 16, 20, 28, 32):
    a, S = alpha_closed(x, G, MG)
    print(f"  x={x:>3}:  S_x = {str(S):>10}   alpha = {str(a):>12} = {float(a):.6f}")

C = F(3 * N, 16) / MG
print(f"\nBOUND  |alpha_x - 1/4| <= 3N/(16 x |G|) = {C}/x = {float(C):.4f}/x")
viol = sum(1 for x in range(1, 501)
           if abs(alpha_closed(x, G, MG)[0] - F(1, 4)) > C / x)
print(f"  violations over x = 1..500: {viol}")
mx = max(range(1, 501), key=lambda x: abs(alpha_closed(x, G, MG)[0] - F(1, 4)) * x)
a, _ = alpha_closed(mx, G, MG)
print(f"  worst ratio to the bound: x={mx}, |alpha-1/4|*x = "
      f"{float(abs(a - F(1,4)) * mx):.4f} vs C = {float(C):.4f}")

print(f"\nCONSEQUENCE -- survival = 1 - a_x - a_y + a_xy >= 1/2 - C(1/x + 1/y).")
for s in (F(1,4), F(1,5), F(1,10)):
    thr = (F(1,2) - s) / C
    print(f"  survival < {s}  requires  1/x + 1/y > {thr} = {float(thr):.5f}, "
          f"hence min(x,y) < {float(2/thr):.1f}")
print(f"  E* has x,y = 7,13:  1/7 + 1/13 = {F(1,7)+F(1,13)} = "
      f"{float(F(1,7)+F(1,13)):.5f}   (survival {float(F(93,1066)):.4f})")

# ---------------------------------------------------------------- the alpha criterion
def alpha_crit(T):
    """exists H subset with  |O|/4 + C_H * sum_{v in O} 1/v  <  1  ?   (C_H = 3N/(16|G_H|))
    Then sum of alpha_v < 1, so |G(T)| >= |G_H|(1 - sum alpha_v) > 0: a witness exists.
    Uses the TRUE alpha where available -- the bound is only the certificate."""
    from itertools import combinations as CB
    n = len(T)
    for r in (1, 2, 3):
        for O in CB(range(n), r):
            H = [T[i] for i in range(n) if i not in O]
            Ov = [T[i] for i in O]
            g = complement(merge(ivs(H)))
            mg = meas(g)
            if mg == 0: continue
            C = F(3 * len(g), 16) / mg
            if F(r, 4) + C * sum(F(1, v) for v in Ov) < 1:
                return ("bound", H, Ov)
            # CIRCULARITY WARNING -- do NOT count this as a criterion.
            # For r = 1, "sum of true alpha_v < 1" says A_v fails to cover G(H), which IS
            # |G(T)| > 0.  It recomputes the conclusion under another name and returns 100%
            # for any true theorem.  Kept only to demonstrate the tautology, never scored.
            s = sum(alpha_direct(v, g, mg) for v in Ov)
            if s < 1:
                return ("CIRCULAR-do-not-count", H, Ov)
    return None

def run(box=18, cap=500):
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    step = max(1, len(tuples) // cap); tuples = tuples[::step]
    nb = ne = 0
    resid = []
    for T in tuples:
        r = alpha_crit(list(T))
        if r is None: resid.append(T)
        elif r[0] == "bound": nb += 1
        else: ne += 1
    n = len(tuples)
    print(f"\nALPHA CRITERION over {n} Case-2 tuples from [1..{box}]")
    print(f"  settled by the a-priori BOUND  r/4 + C*sum(1/v) < 1 : {nb}  ({100*nb//n}%)")
    print(f"  settled by the exact sum(alpha_v) < 1               : {ne}  ({100*ne//n}%)")
    print(f"  the only NON-circular figure is the bound row: {nb} / {n} = "
          f"{100*nb//n}%")
    return resid

resid = run()

print("\nthe seven tuples that survived the earlier three criteria, plus E*:")
prev = [(1,2,3,6,8,10,12),(1,2,5,7,9,16,17),(1,2,6,10,16,17,18),(1,4,7,8,15,19,20),
        (1,7,8,12,17,19,20),(2,5,6,8,10,13,14),(2,5,8,10,14,15,18),(2,6,7,8,10,13,14)]
for T in prev:
    r = alpha_crit(list(T))
    tag = "NOT settled" if r is None else f"settled ({r[0]}, |O|={len(r[2])} off={r[2]})"
    print(f"  {str(T):<30} {tag}")
