"""The three events after the first cycle (arrangement_types_v1): which runners carry the delay, and do
two of them share a slot?  Exact.  Shift one speed at a time by +/-1..3 (arrangement kept distinct and
positive) and recompute the subject's event; runners whose shift collapses the delay (u* <= 1) are critical.
Then read every pair of runners at the subject's own AP scale d_min and at the cascade's final scale D*:
two runners share a slot at scale D when their mutual difference reads within 1 of a multiple of 8,
i.e. |(v_j - v_l)/D - 8M| < 1 (they occupy the same eighth at the spine instants of that scale)."""
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd

def cascade_trace(ds):
    t = F(1, 8 * min(ds)); scales = [min(ds)]; setters = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, scales, setters
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); t = cand[d]; setters.append(d); scales.append(1 / (8 * t))

def d8(x):
    r = x % 8; return min(r, 8 - r)

cases = [([27,70,107,137,159,188,344,393], 393), ([1,31,75,97,128,160,176,225], 1),
         ([1,1975,5265,6910,8737,9589,11845,15135], 1)]
for V, s in cases:
    k = V.index(s); ds = readings(V, k); t, scales, setters = cascade_trace(ds); dmin = min(ds)
    print(f"\n=== V={V}, subject {s}: u*={dmin*t}, moves={len(setters)}, D* = {1/(8*t)}")
    crit = []
    for j in range(8):
        if j == k: continue
        res = []
        for sh in (-3, -2, -1, 1, 2, 3):
            W = V[:]; W[j] += sh
            if len(set(W)) < 8 or min(W) <= 0: continue
            dsW = readings(W, k); tW, sc, st = cascade_trace(dsW)
            res.append((sh, min(dsW) * tW, len(st)))
        collapses = [r for r in res if r[1] <= 1]
        print(f"  shift runner {V[j]:>6}: " + "; ".join(f"{sh:+d}: u*={float(u):.3f} ({m} mv)" for sh, u, m in res)
              + ("   <- CRITICAL" if collapses else ""))
        if collapses: crit.append(j)
    print("  critical runners:", [V[j] for j in crit])
    setter_runner = {}
    for d in setters:
        for j in range(8):
            if j != k and abs(V[j] - s) == d: setter_runner[d] = V[j]
    from collections import Counter
    print("  setters (runner: times):", dict(Counter(setter_runner[d] for d in setters)))
    for D, name in ((F(dmin), 'd_min'), (1 / (8 * t), 'D*')):
        pairs = []
        for a in range(8):
            for b in range(a + 1, 8):
                x = F(abs(V[a] - V[b])) / D
                if d8(x) < 1: pairs.append((V[a], V[b], d8(x)))
        print(f"  pairs sharing a slot at {name}: " + ", ".join(f"({p},{q}) off {float(e):.3f}" for p, q, e in pairs))
