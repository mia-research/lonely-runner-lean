"""Can `no_return_after_few_faster` be strengthened into a general bound on returns?

Three questions, in order, each measured rather than argued:

 1. is `2g+2 <= n` tight?                      -> no_return_tightness_v1.py: TIGHT P-uniformly (3 at n=8),
                                                  loose per-P (7 at P=0, 4 at P=1)
 2. does raising g buy anything?               -> depends on the OTHER hypothesis, `hlap`
 3. for the returns hlap does cover, is there
    headroom in the growth estimate at all?    -> this script

The theorem contradicts a return by bounding growth above (worst case `F^m`) and below (`return_growth`).
Replacing the worst case by the EXACT per-step factors `prod (Q_j + h)/(Q_j - h)` is the strongest form
this proof structure can take. If the exact product still exceeds the return threshold, no sharpening of
the growth estimate excludes that return -- the conclusion is simply false there, and the lemma cannot be
extended to it at any g.

Sampled over arrangements that actually move (ratio in (n-1, n], the non-trivial stratum: at ratio
<= n-1 the subject is lonely at the opening instant and there are no returns at all).
"""
import sys, random
from fractions import Fraction as F
from collections import Counter

n = 8; h = F(1, n); INV_N = h
def fract(x):   return x - (x.numerator // x.denominator)
def cd(x):      return min(fract(x), 1 - fract(x))
def inWay(d,t): return cd(d * t) < INV_N
def ceil_(x):   return -((-x.numerator) // x.denominator)
def nxt(d,t):   return (F(ceil_(d * t - INV_N)) + INV_N) / d
def move(ds,t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nxt(d, t)
            if o > acc: acc = o
    return acc
def trace(dsi, maxsteps=2000):
    ds = sorted(F(d) for d in dsi); m = min(ds); t = F(1) / (n * m); out = []
    for _ in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t: return out
        s = next(d for d in ds if inWay(d, t) and nxt(d, t) == t2)
        out.append((s, ceil_(s * t - INV_N))); t = t2
    return None

def hlap_returns(tr):
    pos = {}
    for i, (s, P) in enumerate(tr): pos.setdefault(s, []).append((i, P))
    out = []
    for s, lst in pos.items():
        for (i, P), (j, _) in zip(lst, lst[1:]):
            inter = tr[i+1:j]
            if not inter or not all(Q >= P + 1 for _, Q in inter): continue
            exact = F(1)
            for _, Q in inter: exact *= (F(Q) + h) / (F(Q) - h)
            need = (F(P) + 1 - h) / (F(P) + h)
            out.append((j - i - 1, P, exact, need))
    return out

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 40000
VMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 300
random.seed(20260917)

print(f"n = {n}; sampling the stratum that moves: ratio in ({n-1}, {n}], entries <= {VMAX}")
print(f"{NS} arrangements\n")
rets = []; moved = 0; tot_returns = 0
for _ in range(NS):
    while True:
        dsi = random.sample(range(1, VMAX + 1), 7); m = min(dsi)
        if (n - 1) * m < max(dsi) <= n * m: break
    tr = trace(dsi)
    if not tr: continue
    moved += 1
    pos = {}
    for i, (s, P) in enumerate(tr): pos.setdefault(s, []).append(i)
    tot_returns += sum(len(v) - 1 for v in pos.values())
    rets += hlap_returns(tr)

print(f"  arrangements that moved: {moved}/{NS}")
print(f"  returns observed: {tot_returns}")
print(f"  returns satisfying hlap: {len(rets)}  ({100*len(rets)/tot_returns if tot_returns else 0:.1f}%)")
if rets:
    excl = [r for r in rets if r[2] <= r[3]]
    print(f"\n  of the hlap returns, how many would the EXACT-growth form exclude: {len(excl)}")
    print(f"    (it must be 0 -- these returns happened; a nonzero count is a bug)")
    gaps = Counter(r[0] for r in rets)
    print(f"\n  gap histogram (hlap returns): {dict(sorted(gaps.items()))}")
    print(f"  gaps <= 3 (already covered by the shipped theorem): {sum(v for k,v in gaps.items() if k<=3)}")
    marg = sorted(float(r[2] / r[3]) for r in rets)
    print(f"\n  margin = exact growth / return threshold, over hlap returns:")
    print(f"    min {marg[0]:.4f}   median {marg[len(marg)//2]:.4f}   max {marg[-1]:.4f}")
    print(f"    fraction within 5% of the threshold (margin < 1.05): "
          f"{sum(1 for m in marg if m < 1.05)}/{len(marg)}")
    print(f"\n  reading: every margin > 1 means the exact-growth bound does NOT contradict that return.")
    print(f"  The shipped theorem is consistent because those returns all have gap > 3.")
