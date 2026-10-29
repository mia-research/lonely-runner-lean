# Greedy cover of the 52,000-arrangement survey by FIXED rational instants R = 8 a / b (R = 8 d_min t, b in 2..12, R <= 60): an arrangement is covered by R when every reading rho has dist(rho R/8) >= 1/8.
# Exact Fractions.  The question: how short is a list of fixed R that covers most of the survey?  (Sampler output, not a measure; steering only.)
import pickle, math, collections
from fractions import Fraction as F
S = pickle.load(open('../../LonelyRunner/experiments/nN/redo/taxo_sample_v1.pkl', 'rb'))
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
arrs = [sorted(rec[1]) for rec in S]
cands = sorted({F(8 * a, b) for b in range(2, 13) for a in range(1, 8 * 60 * b // 8 + 1) if F(8 * a, b) <= 60})
print('candidates', len(cands))
cov = {}
for R in cands:
    s = set()
    for i, r in enumerate(arrs):
        if all(dist(d * R / 8) >= E for d in r): s.add(i)
    cov[R] = s
left = set(range(len(arrs))); order = []
for step in range(40):
    best = max(cands, key=lambda R: len(cov[R] & left))
    gain = len(cov[best] & left)
    if gain == 0: break
    left -= cov[best]; order.append((str(best), gain, len(arrs) - len(left)))
    print(step + 1, 'R =', best, 'gain', gain, 'covered', len(arrs) - len(left))
