# The remainder after all proved types plus the fixed-instant list FixedRList (R = 8a/b, b <= 12, a <= 8b) on the 52,000-arrangement survey.  Exact; the remainder is listed with its cascade outcome label and move count.
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_chain2_v1.py').read().split("cnt = collections.Counter(); byc")[0])
Rs = sorted({F(8 * a, b) for b in range(1, 13) for a in range(1, 8 * b + 1)})
def fixedR(r): return any(all(dist(d * R / 8) >= E for d in r) for R in Rs)
def casc(r):
    t = F(1, 8 * min(r)); mv = 0
    while True:
        way = [d for d in r if dist(d * t) < E]
        if not way: return t, mv
        t = max((F(round(d * t)) + E) / d for d in way); mv += 1
rem = []; cnt = collections.Counter()
for rec in S:
    r = sorted(rec[1]); cnt['total'] += 1
    if unblocked(r) or ratio(r) or firstlap(r) or chain2(r) or fixedR(r): continue
    rem.append((rec[0], rec[2], r))
print('candidates', len(Rs), 'total', cnt['total'], 'remainder', len(rem))
labs = collections.Counter(x[1] for x in rem); gens = collections.Counter(x[0] for x in rem)
print('by label', dict(labs)); print('by generator', dict(gens))
for gen, lab, r in rem[:12]:
    t, mv = casc(r); print(gen, lab, 'moves', mv, 'R*', t * 8 * min(r), [str(x) for x in r])
