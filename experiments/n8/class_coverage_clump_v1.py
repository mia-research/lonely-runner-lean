# Coverage by SlowOneClumpClass and APSlowClumpClass (ClumpClasses) on the 52,000-arrangement survey.  Exact; steering only (sampler output).
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_chain2_v1.py').read().split("cnt = collections.Counter(); byc")[0])
def slow_one_clump(r):
    s = r[0]
    for j in range(1, 7):  # clump = r[j:], x = r[j]
        pass
    x = r[1]; eps = r[-1] / x - 1
    return eps * (x / (2 * s) + 2) <= F(1, 8) and 2 * s <= 3 * x
def ap_slow_clump(r):
    n = len(r)
    for rr in range(1, 7):
        slow = r[:rr]; C = r[rr:]
        if not C: continue
        x = C[0]; eps = C[-1] / x - 1
        # best g: least squares-ish search over g = slow[i]/(i+1)
        for g in {slow[i] / (i + 1) for i in range(rr)}:
            eta = max(abs(slow[i] - (i + 1) * g) for i in range(rr))
            sig = F(1) / ((rr + 1) * g)
            if not (eta * sig < F(1, rr + 1) - F(1, 8)): continue
            if not ((rr * g + eta) / (2 * x) <= 2 * (F(1, rr + 1) - eta * sig - F(1, 8))): continue
            if eps * (x * sig + 2) <= F(1, 8): return True
    return False
cnt = collections.Counter()
for rec in S:
    r = sorted(rec[1])
    o = unblocked(r) or ratio(r) or firstlap(r); c = chain2(r) is not None
    a = slow_one_clump(r); b = ap_slow_clump(r)
    cnt['total'] += 1
    if a: cnt['slow_one_clump'] += 1
    if b: cnt['ap_slow_clump'] += 1
    if a and not (o or c): cnt['one_adds'] += 1
    if b and not (o or c): cnt['ap_adds'] += 1
    if o or c or a or b: cnt['union'] += 1
print(dict(cnt))
