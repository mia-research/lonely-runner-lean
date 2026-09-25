"""Anatomy of EightResidual on 7-subsets of [1,N]: which flanks certify each set (Theorem 10),
and the least denominator q of a lonely rational instant a/q (a coprime to q)."""
import itertools, collections, sys
from math import gcd
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open(__import__("os").path.join(__import__("os").path.dirname(__file__) or ".", "eight_residual_count_v1.py")).read().split("t0 = time.time()")[0])
def certs(S):
    out = []
    for e in S:
        for j in range(e):
            A = 8*j+1
            if all(e <= (d*A) % (8*e) <= 7*e for d in S): out.append((e, j)); break
    return out
def least_q(S, qmax=200):
    for q in range(2, qmax):
        for a in range(1, q//2+1):
            if gcd(a, q) == 1 and all(min((d*a) % q, q-(d*a) % q)*8 >= q for d in S): return q, a
    return None
stat = collections.Counter(); qs = collections.Counter(); ex = {}
for S in itertools.combinations(range(1, N+1), 7):
    if not any(d%2 for d in S): continue
    if not all(any(d%q==0 for d in S) for q in (5,6,7,8)): continue
    if not max(S) > 7*min(S): continue
    if sum(4 if d%8==4 else 2 for d in S if d%8) < 8: continue
    if any(free_flank8(S,e) for e in S if e%8==0): continue
    if shifted(S): continue
    s = sorted(S)
    if s[-1] > 7*s[-2]: continue
    if first_lap(S) or minus_seven(S): continue
    M = [d for d in S if d%8==0]
    if len(M) != 1: continue
    e8 = M[0]; E = [d for d in S if d%8]
    C = certs(S); fl = {e for e,_ in C}
    stat['sets'] += 1
    stat['cert at the multiple of 8'] += e8 in fl
    stat['cert at an odd flank'] += any(e%2 for e in fl)
    stat['cert at the least disparity'] += s[0] in fl
    stat['cert at the largest non-multiple'] += max(E) in fl
    stat['cert at the least odd disparity'] += min(d for d in S if d%2) in fl
    stat['cert only at the multiple of 8'] += fl == {e8}
    q = least_q(S); qs[q[0] if q else None] += 1
    if q and q[0] not in ex: ex[q[0]] = (S, q)
print(dict(stat)); print("least lonely denominator q:", sorted(qs.items(), key=lambda x: (x[0] is None, x[0])))
for q in sorted(ex)[-4:]: print("  q =", q, ex[q])
