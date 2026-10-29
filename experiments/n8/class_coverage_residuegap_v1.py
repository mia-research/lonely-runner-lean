# Coverage by the residue-gap class: unit g, q in 2..7, every disparity within eta of n g with q not dividing n, eta <= g (1 - q/8); isolation at t = 1/(q g).  Exact; steering only.
import pickle, math, collections
from fractions import Fraction as F
exec(open('class_coverage_chain2_v1.py').read().split("cnt = collections.Counter(); byc")[0])
def residue_gap(r, nmax=24):
    best = None
    for q in range(2, 8):
        tol = 1 - F(q, 8)
        cands = {d / n for d in r[:3] for n in range(1, 13)}
        for g in cands:
            ok = True
            for d in r:
                e = min(abs(d - n * g) for n in range(1, nmax + 1) if n % q)
                if e > g * tol: ok = False; break
            if ok: return (q, g)
    return None
cnt = collections.Counter(); byq = collections.Counter(); bylab = collections.Counter(); ex = {}
for rec in S:
    r = sorted(rec[1])
    o = unblocked(r) or ratio(r) or firstlap(r); c = chain2(r) is not None
    m = residue_gap(r)
    cnt['total'] += 1
    if m: cnt['residue_gap'] += 1; byq[m[0]] += 1
    if m and not (o or c): cnt['adds'] += 1; bylab[rec[2]] += 1; ex.setdefault(m[0], ([str(x) for x in r], str(m[1])))
    if o or c or m: cnt['union'] += 1
print(dict(cnt), sorted(byq.items())); print('adds by label', dict(bylab)); print(ex)
