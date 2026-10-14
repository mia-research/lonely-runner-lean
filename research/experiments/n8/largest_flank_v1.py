"""Data suggests: clear flanks are the LARGE differences, shadowed ones the SMALL.
CLAIM to test: for every subject, the flank at its LARGEST |difference| is clear.
If true, Existence follows immediately."""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)

def flank_status(ds, e, kmax=3000):
    ae = abs(e); ratios = [F(d, ae) for d in ds]
    if any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios): return 'dead'
    movers = [r for r in ratios if r.denominator != 1]
    for k in range(kmax):
        ok = True
        for r in movers:
            x = k*frac(r) + r/8
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return k
    return 'shadowed'

rng = random.Random(20260919)
res = Counter(); fails = []; tot = 0
rank_clear = Counter()
for _ in range(6000):
    v = sorted(rng.sample(range(0, 400), 8))
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        tot += 1
        e = max(ds, key=abs)
        st = flank_status(ds, e)
        res[st if isinstance(st, str) else 'clear'] += 1
        if st == 'shadowed' and len(fails) < 5: fails.append((v, i, e))
        # also: by rank of |e| among the differences, is it clear?
        order = sorted(ds, key=lambda x: -abs(x))
        for rnk, ee in enumerate(order):
            s = flank_status(ds, ee)
            if s not in ('dead','shadowed'): rank_clear[rnk] += 1
print(f"subjects tested: {tot:,}")
print(f"  status of the LARGEST-|e| flank: {dict(res)}")
if fails:
    print(f"\n  counterexamples (largest flank shadowed):")
    for v,i,e in fails: print(f"     v={v} subject {i} e={e}")
else:
    print(f"\n  no counterexample: the largest flank was never shadowed.")
print(f"\n  clear-rate by rank of |e| (0 = largest):")
for r in sorted(rank_clear): print(f"     rank {r}: clear in {100*rank_clear[r]/tot:6.2f}% of subjects")
