# E638: whole-number sets that satisfy the simple fields of EightResidual (card 7, an odd member, gcd 1, multiples of 5, 6, 7, 8, spread 7a < b, cost >= 8, not_fast, no first-lap flank),
# and how many of them are covered by the real chain class (ChainNested2 / NativeClusters, slow cluster at its native gate) or by one of the 368 fixed instants R = 8a/b (b <= 12, a <= 8b).
# Superset of EightResidual (other fields not tested).  Exact integer arithmetic; chain class on Fractions only for the survivors.  usage: N
import sys, math, itertools, collections
from fractions import Fraction as F
N = int(sys.argv[1])
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
Rs = sorted({(a, b) for b in range(1, 13) for a in range(1, 8 * b + 1)})
def fixedR(S):
    m = S[0]
    for a, b in Rs:
        q = b * m; ok = True
        for d in S:
            rem = (a * d) % q
            if 8 * rem < q or 8 * rem > 7 * q: ok = False; break
        if ok: return True
    return False
def chain2(r):
    n = len(r)
    for m in range(0, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if m == 0: return True
            M = r[m - 1]; gam = F(1, m + 1)
            if gaps[0] * M <= 2 * (gam - E): return True
    return False
def simple_fields(S):
    if len(S) != 7: return False
    g = 0
    for d in S: g = math.gcd(g, d)
    if g != 1: return False
    if all(d % 2 == 0 for d in S): return False
    for q in (5, 6, 7, 8):
        if not any(d % q == 0 for d in S): return False
    if not any(7 * a < b for a in S for b in S): return False
    if sum(max(2, math.gcd(e, 8)) for e in S if e % 8) < 8: return False
    for V in S:
        if not any(s != V and V <= 7 * s for s in S): return False
    for e in S:
        for k in range(0, 7 * e // 8 + 1):
            if all(e <= d * (8 * k + 1) <= 7 * e for d in S if d != e): return False
    return True
cand = 0; cov_chain = 0; cov_fixed = 0; cov_any = 0; left = []
for S in itertools.combinations(range(1, N + 1), 7):
    if not simple_fields(S): continue
    cand += 1
    r = [F(d, S[0]) for d in S]
    c1 = fixedR(S); c2 = chain2(r) if not c1 else True
    if c1: cov_fixed += 1
    if c2 and not c1: cov_chain += 1
    if not (c1 or c2): left.append(S)
print('N', N, 'candidates (simple EightResidual fields)', cand, 'fixed-instant', cov_fixed, 'chain only', cov_chain, 'neither', len(left))
print('examples', left[:6])
