# Coverage with ClusterChainClass (NativeClusters / ChainNested2): slow cluster of size m (gate 1/(m+1), native), singleton rungs with the full-window condition gap2(rest) <= 3/(4x),
# terminal single (LT = 1/(4x)) or arbitrary pair (LT = 1/(2a)).  m = 0: chain alone.  Exact; the survey is sampler output (no measure).
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_v1.py').read().split("cnt = collections.Counter()")[0])
def chain2(r):
    n = len(r); hits = []
    for m in range(0, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()  # gaps[i] = gap2 of rungs[i:] ; gaps[len(rungs)] = LT
            ok = all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs)))
            if not ok: continue
            if m == 0: return (m, k)
            M = r[m - 1]; gam = F(1, m + 1)
            if gaps[0] * M <= 2 * (gam - E): return (m, k)
    return None
cnt = collections.Counter(); byc = collections.Counter(); exs = {}
for rec in S:
    r = sorted(rec[1])
    old = unblocked(r) or ratio(r) or firstlap(r)
    ch = chain2(r); ch1 = cluster_ladder(r) > 0 or ladder(r)
    cnt['total'] += 1
    if old: cnt['old3'] += 1
    if ch: cnt['chain2'] += 1; byc[ch] += 1
    if ch and not old: cnt['chain2_adds_to_old3'] += 1; exs.setdefault(ch, [str(x) for x in r])
    if old or ch: cnt['union'] += 1
print(dict(cnt)); print(sorted(byc.items())); print(exs)
