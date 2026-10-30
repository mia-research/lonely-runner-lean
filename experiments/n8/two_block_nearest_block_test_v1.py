"""E648 place test, all 388,712 records. Place: let N be the block holding the subject's nearest reading (own block on
a tie). From the subject, N's readings have an exact clear set; let C1 be its first component. The landing is the first
t in C1 at which the other block's readings are clear. Pass: equality with the cascade's landing; misses by kind,
and for misses the index of the component of N's clear set holding the landing. Exact."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
def comps(ds, T):
    zones = sorted(((m - E) / d, (m + E) / d) for d in ds for m in range(0, int(d * T) + 2))
    out = []; cur = F(0)
    for a, b in zones:
        if a > cur: out.append((cur, a))
        cur = max(cur, b)
    return out
res = Counter(); missidx = Counter(); ex = []
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    A = G + (p - 1); v = sp(p, A, b)
    own = [i for i in (range(p) if k < p else range(p, 8)) if i != k]
    oth = [i for i in range(8) if i != k and i not in own]
    do = [abs(v[i] - v[k]) for i in own]; dx = [abs(v[i] - v[k]) for i in oth]
    N, O = (do, dx) if min(do) <= min(dx) else (dx, do)
    which = 'N=own' if N is do else 'N=other'
    T = t + 2
    cs = comps(N, T)
    c1 = cs[0] if cs else None
    place = None
    if c1:
        lo, hi = c1
        cands = sorted({lo} | {(F(m) + E) / d for d in O for m in range(0, int(d * hi) + 1)})
        for c in cands:
            if lo <= c <= hi and all(dist(d * c) >= E for d in O): place = c; break
    reg = 'interleaved' if G <= 0 else 'gap'
    if place == t: res[(reg, which, 'hit')] += 1
    else:
        idx = next((i + 1 for i, (a, bb) in enumerate(cs) if a <= t <= bb), None)
        res[(reg, which, 'miss')] += 1; missidx[(reg, which, idx)] += 1
        if len(ex) < 10: ex.append((p, b, G, k, t, idx))
for kk, vv in sorted(res.items()): print(vv, kk)
print("misses by component of N's clear set holding the landing:")
for kk, vv in sorted(missidx.items(), key=lambda x: -x[1])[:25]: print("  ", vv, kk)
print("examples (p, b, G, subject, landing, component):"); [print("  ", e) for e in ex]
