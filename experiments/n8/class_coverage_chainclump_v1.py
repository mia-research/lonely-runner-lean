# Coverage with a chain of singleton rungs ending in a CLUMP terminal (ChainNested2 + ClumpGap, cap T = gap2 of the chain from alpha0 = 0): exact; steering only.
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_chain2_v1.py').read().split("cnt = collections.Counter(); byc")[0])
def chain_clump(r):
    n = len(r)
    for c in range(2, n + 1):
        rungs = r[:n - c]; C = r[n - c:]; x = C[0]; eps = C[-1] / x - 1
        LT = F(1, 2) / x
        gaps = [LT]
        for y in reversed(rungs): gaps.append(F(1, 4) / y + 2 * gaps[-1])
        gaps.reverse()
        if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
        T = gaps[0]
        if eps * (x * T + 2) <= F(1, 8): return c
    return None
cnt = collections.Counter(); byc = collections.Counter()
for rec in S:
    r = sorted(rec[1])
    o = unblocked(r) or ratio(r) or firstlap(r); c2 = chain2(r) is not None; cc = chain_clump(r)
    cnt['total'] += 1
    if cc: cnt['chain_clump'] += 1; byc[cc] += 1
    if cc and not (o or c2): cnt['adds'] += 1
    if o or c2 or cc: cnt['union'] += 1
print(dict(cnt), sorted(byc.items()))
