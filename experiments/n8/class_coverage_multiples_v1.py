# Coverage by NearMultiplesClass (AP indices 1..r, r <= 6, tolerance g (1 - (r+1)/8)) on the 52,000-arrangement survey.  Exact; steering only.
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_chain2_v1.py').read().split("cnt = collections.Counter(); byc")[0])
def near_multiples(r):
    for rr in range(1, 7):
        tol = 1 - F(rr + 1, 8)
        cands = {d / n for d in r for n in range(1, rr + 1)}
        for g in cands:
            eta = max(min(abs(d - n * g) for n in range(1, rr + 1)) for d in r)
            if eta <= g * tol: return rr
    return 0
cnt = collections.Counter(); byr = collections.Counter(); bylab = collections.Counter()
for rec in S:
    r = sorted(rec[1])
    o = unblocked(r) or ratio(r) or firstlap(r); c = chain2(r) is not None
    m = near_multiples(r)
    cnt['total'] += 1
    if m: cnt['near_multiples'] += 1; byr[m] += 1; bylab[rec[2]] += 1
    if m and not (o or c): cnt['adds'] += 1
    if o or c or m: cnt['union'] += 1
print(dict(cnt), sorted(byr.items())); print(dict(bylab))
