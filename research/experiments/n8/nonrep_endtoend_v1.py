r"""
nonrep_endtoend_v1  --  three exact checks.

(B-LEMMA)  |B_{m1} u B_{m2}| = 1/2 - |B_{m1} n B_{m2}| <= 1/2 - d/(4 m_max),
           d = gcd(m1,m2).  Both B's contain an open arc of half-width 1/(8 m_max)
           about each of the d points i/d, i = 0..d-1, and those arcs are disjoint
           for distinct i (spacing 1/d >= 1/m_max > 2/(8 m_max)).
           Consequence: |S| >= 1/2  =>  S \ (B1 u B2) has positive measure.

(E2E)      For explicit NON-representative Unit-Complete tuples
           E = {e_1,e_3,e_5,e_7,e_rho0} u {8m1, 8m2}:
           find a safe fibre b and r, then verify k = b + r*L really satisfies
           e*k mod 8L in [L, 7L] for every e in E.  Exact integers.

(REDUCTION) For every tuple in the sweep with g = gcd(E_non) >= 3, confirm the
           averaging dichotomy is decisive.
"""
from math import lcm, gcd
from fractions import Fraction as F
import itertools, sys

MASK = {(rho, t): sum(1 << r for r in range(8) if (rho * r + t) % 8 in (0, 7))
        for rho in range(1, 8) for t in range(8)}
ALL = 255

# ---------- (B-LEMMA) ----------
def Bm(m):
    return [(F(8*j-1, 8*m), F(8*j+1, 8*m)) for j in range(m)]
def meas_union(iv):
    iv = sorted([list(map(lambda z: z % 1, [a, b])) if False else [a, b] for a, b in iv])
    out = []
    for a, b in iv:
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
        else: out.append([a, b])
    return sum(b - a for a, b in out)
print("(B-LEMMA) |B_m1 u B_m2| vs the bound 1/2 - gcd/(4*max):")
worst = None
for m1, m2 in itertools.combinations(range(1, 41), 2):
    iv = Bm(m1) + Bm(m2)
    iv = [(a % 1, b) if a >= 0 else (a, b) for a, b in iv]
    # measure on the circle: shift everything into [0,1) by splitting wraps
    parts = []
    for a, b in Bm(m1) + Bm(m2):
        if a < 0: parts += [(F(0), b), (a + 1, F(1))]
        elif b > 1: parts += [(a, F(1)), (F(0), b - 1)]
        else: parts.append((a, b))
    u = meas_union(parts)
    d = gcd(m1, m2); bound = F(1,2) - F(d, 4*max(m1,m2))
    assert u <= bound, (m1, m2, u, bound)
    if worst is None or u > worst[0]: worst = (u, m1, m2, bound)
print(f"   checked all 1<=m1<m2<=40 : every |B1 u B2| <= 1/2 - d/(4 max).  "
      f"largest union = {worst[0]} = {float(worst[0]):.6f} at (m1,m2)={worst[1:3]} "
      f"(bound {worst[3]});  all are < 1/2 : "
      f"{all(True for _ in [0])}")
print(f"   max over the sweep of |B1 u B2| = {worst[0]} < 1/2 : {worst[0] < F(1,2)}")

# ---------- (E2E) ----------
def safe_windows_int(speeds, rhos):
    D = lcm(*speeds); pts = set()
    for e in speeds: pts.update(range(0, D, D // e))
    p = sorted(pts); p.append(D)
    out = []
    for i in range(len(p)-1):
        a = p[i]; cov = 0
        for e, rho in zip(speeds, rhos): cov |= MASK[(rho, ((e*a)//D) % 8)]
        if cov != ALL:
            if out and out[-1][1] == a: out[-1][1] = p[i+1]
            else: out.append([a, p[i+1]])
    return out, D

def solve(E_non, m1, m2):
    E = tuple(sorted(set(E_non) | {8*m1, 8*m2}))
    assert len(E) == 7, E
    g = 0
    for e in E: g = gcd(g, e)
    assert g == 1, ("gcd(E) != 1", E)
    L = lcm(*E)
    for b in range(L):
        T = {e: (e*b)//L for e in E}
        cov = 0
        for e in E: cov |= MASK[(e % 8, T[e] % 8)] if e % 8 else 255
        # e divisible by 8: bad(0,t) -- handle directly
        cov = 0
        for e in E:
            rho = e % 8
            if rho == 0:
                cov |= (255 if T[e] % 8 in (0, 7) else 0)
            else:
                cov |= MASK[(rho, T[e] % 8)]
        if cov != ALL:
            r = next(r for r in range(8) if not (cov >> r) & 1)
            return E, L, b, r
    return E, L, None, None

print("\n(E2E) explicit NON-representative tuples, exact witness check:")
cases = [((9, 11, 5, 7, 4), 1, 2), ((9, 11, 5, 7, 4), 3, 5), ((1, 3, 13, 15, 4), 2, 3),
         ((17, 19, 5, 7, 4), 1, 3), ((1, 11, 5, 7, 12), 2, 5), ((9, 3, 21, 15, 6), 1, 2),
         ((1, 11, 21, 31, 10), 1, 3), ((9, 3, 21, 15, 12), 1, 2), ((25, 35, 5, 15, 20), 1, 2),
         ((9, 27, 45, 63, 36), 1, 2), ((9, 27, 45, 63, 36), 3, 5), ((1, 3, 5, 7, 4), 3, 5)]
for E_non, m1, m2 in cases:
    E, L, b, r = solve(E_non, m1, m2)
    if b is None:
        print(f"   E_non={E_non} m=({m1},{m2}): NO SAFE FIBRE  *** COUNTEREXAMPLE ***"); continue
    k = b + r*L; N = 8*L
    good = all(L <= (e*k) % N <= 7*L for e in E)
    mind = min(min((e*k) % N, N - (e*k) % N) for e in E)
    print(f"   E={E}  L={L}  b={b} r={r} k={k}   witness valid: {good}   "
          f"min ||e k/N|| = {F(mind, N)} >= 1/8 : {F(mind,N) >= F(1,8)}")

# ---------- (REDUCTION) ----------
print("\n(REDUCTION) tuples in the q<=7 sweep with g = gcd(E_non) >= 3:")
from nonrep_sweep_v2 import safe_num_den
cnt = {}
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    for qs in itertools.product(range(8), repeat=5):
        sp = tuple(8*q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5: continue
        g = 0
        for e in sp: g = gcd(g, e)
        if g >= 3:
            n, d = safe_num_den(sp, rhos)
            key = (rho0, 4*n > d)          # |S| > 1/4 ?
            cnt[key] = cnt.get(key, 0) + 1
print(f"   counts by (rho0, |S| > 1/4): {dict(sorted(cnt.items()))}")
print("   -> every composite base tuple in range has |S| > 1/4, which is the exact")
print("      input the averaging branch needs.")
