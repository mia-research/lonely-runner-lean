"""E656 jitter (rule 12): the 890 quarter-lap landings of E655. Shift the gap G by +1/997 and by -1/997 (off the
sample lattice) and rerun the unchanged cascade: does the landing keep frac(s t*) in {1/4, 3/4}, and does the setter
stay the same reading and lap? Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def frac(x): return x - math.floor(x)
def dist(x):
    f = frac(x); return min(f, 1 - f)
def cascade(r):
    t = F(1, 8 * r[0]); last = None
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, last
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; last = (i, M)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
res = Counter(); n = 0
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0 or op[0] != 'set': continue
    v = sp(p, G + p - 1, b); ownb = list(range(p)) if k < p else list(range(p, 8))
    if op[1] in ownb: continue
    s = b if k < p else F(1)
    if frac(s * t) not in (F(1, 4), F(3, 4)): continue
    n += 1
    for e in (F(1, 997), F(-1, 997)):
        w = sp(p, G + e + p - 1, b)
        rd = sorted((abs(x - w[k]), i) for i, x in enumerate(w) if i != k)
        rr = [d for d, _ in rd]; who = [i for _, i in rd]
        t2, last = cascade(rr)
        same = last is not None and who[last[0]] == op[1] and last[1] == M
        q = frac(s * t2) in (F(1, 4), F(3, 4))
        res[('shift %s' % ('+' if e > 0 else '-'), 'quarter kept' if q else 'quarter lost', 'same setter and lap' if same else 'setter changed')] += 1
print("quarter-lap landings:", n)
for kk, vv in sorted(res.items()): print(vv, kk)
