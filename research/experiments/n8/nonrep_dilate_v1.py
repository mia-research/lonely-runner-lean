"""
nonrep_dilate_v1  --  the ONLY family with |S| <= 1/2 : E_non = lam * {1,3,5,7,4}.

By the odd-dilation symmetry S(lam*E) = lam^{-1} S(E), for E_non = lam*{1,3,5,7,4}
   S_lam = { x : lam*x mod 1  in  S_0 },   S_0 = [1/4,3/7) u [4/7,3/4),  |S_lam| = 5/14.
Must show  S_lam \ (B_{m1} u B_{m2})  is nonempty, where B_m = {x : ||m x|| < 1/8},
for all lam odd >= 1, m1 != m2 >= 1 with gcd(lam,m1,m2) = 1 (needed for gcd(E)=1).

Exact rational arithmetic via a common denominator D = lcm(28*lam, 8*m1, 8*m2);
every endpoint is an integer over D, so all comparisons are integer comparisons.
"""
from math import lcm, gcd
from fractions import Fraction as F
import itertools, sys

def S_intervals(lam, D):
    """half-open [a,b) as integers over D"""
    out = []
    for i in range(lam):
        out.append(((4 * i + 1) * (D // (4 * lam)), (7 * i + 3) * (D // (7 * lam))))
        out.append(((7 * i + 4) * (D // (7 * lam)), (4 * i + 3) * (D // (4 * lam))))
    return out

def B_intervals(m, D):
    """open (j/m - 1/(8m), j/m + 1/(8m)) for j in Z, clipped to [0,D); returns closed-ish
    covering intervals as integers over D (we subtract them as OPEN sets, so the
    surviving set may be a single point; we report MEASURE, which is what we need)."""
    s = D // (8 * m)
    out = []
    for j in range(m + 1):
        lo, hi = 8 * j * s - s, 8 * j * s + s
        lo = max(lo, 0); hi = min(hi, D)
        if lo < hi: out.append((lo, hi))
    return out

def uncovered_measure(lam, m1, m2):
    D = lcm(28 * lam, 8 * m1, 8 * m2)
    S = S_intervals(lam, D)
    Bs = sorted(B_intervals(m1, D) + B_intervals(m2, D))
    # merge B
    mg = []
    for lo, hi in Bs:
        if mg and lo <= mg[-1][1]: mg[-1][1] = max(mg[-1][1], hi)
        else: mg.append([lo, hi])
    tot = 0
    k = 0
    for a, b in sorted(S):
        cur = a
        for lo, hi in mg:
            if hi <= cur: continue
            if lo >= b: break
            if lo > cur: tot += lo - cur
            cur = max(cur, hi)
            if cur >= b: break
        if cur < b: tot += b - cur
    return F(tot, D)

if __name__ == "__main__":
    LMAX = int(sys.argv[1]); MMAX = int(sys.argv[2])
    worst = None; fails = []; n = 0
    for lam in range(1, LMAX + 1, 2):
        for m1, m2 in itertools.combinations(range(1, MMAX + 1), 2):
            if gcd(gcd(lam, m1), m2) != 1: continue
            n += 1
            r = uncovered_measure(lam, m1, m2)
            if r == 0: fails.append((lam, m1, m2))
            if worst is None or r < worst[0]: worst = (r, lam, m1, m2)
    print(f"lam odd <= {LMAX}, 1 <= m1 < m2 <= {MMAX}, gcd(lam,m1,m2)=1 : {n} triples")
    print(f"   triples where B_m1 u B_m2 COVERS S_lam : {len(fails)}")
    if fails: print("   ", fails[:20])
    print(f"   minimum surviving measure = {worst[0]} = {float(worst[0]):.8f}"
          f"  at (lam,m1,m2) = {worst[1:]}")
    # the lam=1 row reproduces Lemma D's constant
    w1 = min((uncovered_measure(1, a, b), a, b)
             for a, b in itertools.combinations(range(1, MMAX + 1), 2))
    print(f"   lam = 1 row: min surviving measure = {w1[0]} at (m1,m2)={w1[1:]}"
          f"   [Lemma D reported 19/420 at (3,5) for the single window I=[1/4,3/7)]")
