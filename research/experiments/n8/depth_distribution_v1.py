"""The setter depths delta_j -- the quantity every current bound charges at its worst case.

ORDER5_GROWTH_v2 section 2: a move's contribution to R is (2 - n*delta_j)/s_j, where
delta_j = x_j*t_j - Q_j + 1/n  in (0, 2/n)  is how far into its zone the setter had gone when caught.

Every bound in the tree charges delta_j = 0 (the worst case, contribution 2/s_j):
  * the counting/potential route -> n > 2k, wanting n > 14 at k = 7;
  * section 6.7's move bound (7/8)*S*R + 7;
  * ORDER5_GROWTH_v2 section 5's charging argument.

So the gap between the bounds and reality is exactly the gap between delta = 0 and the delta that occurs.
This measures it.
"""
import sys, random
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(x): return x - (x.numerator // x.denominator)
def cd(x):    return min(fract(x), 1 - fract(x))
def inWay(d,t): return cd(d * t) < INV
def ceil_(x): return -((-x.numerator) // x.denominator)
def nxt(d,t): return (F(ceil_(d * t - INV)) + INV) / d
def move(ds,t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nxt(d, t)
            if o > acc: acc = o
    return acc

def depths(dsi, maxsteps=2000):
    ds = sorted(F(d) for d in dsi); m = min(ds); t = F(1) / (n * m); out = []
    for _ in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t: return out
        x = next(d for d in ds if inWay(d, t) and nxt(d, t) == t2)
        Q = ceil_(x * t - INV)
        out.append((x * t - Q + INV, x, Q))      # delta in (0, 2/n)
        t = t2
    return None

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
random.seed(20260917)
MAXD = F(2, n)

print(f"order {n}: setter depths.  delta in (0, {MAXD}); worst case charged by every bound is delta = 0.")
print(f"a move's contribution to R is (2 - {n}*delta)/s, so delta = {MAXD} contributes nothing.\n")

for name, dsi in [("section 6.7 climb", [49,205,234,256,286,323,366]),
                  ("section 6.9 row",   [30,74,96,127,159,175,224])]:
    ds = depths(dsi)
    dl = sorted(d for d, _, _ in ds)
    print(f"  {name}: {len(ds)} moves")
    print(f"     delta/({MAXD}): min {float(dl[0]/MAXD):.4f}  median {float(dl[len(dl)//2]/MAXD):.4f}"
          f"  max {float(dl[-1]/MAXD):.4f}")
    print(f"     moves with delta below 10% of the zone (near worst case): "
          f"{sum(1 for d in dl if d < MAXD/10)}/{len(dl)}")

alld = []
for _ in range(NS):
    while True:
        dsi = random.sample(range(1, 301), 7); m = min(dsi)
        if 7 * m < max(dsi) <= 8 * m: break
    ds = depths(dsi)
    if ds: alld += [d for d, _, _ in ds]
alld.sort()
print(f"\n  pooled over {NS} moving arrangements: {len(alld)} moves")
q = lambda p: float(alld[int(p * (len(alld) - 1))] / MAXD)
print(f"     delta as a fraction of the zone width {MAXD}:")
print(f"       min {q(0):.4f}   10% {q(.1):.4f}   median {q(.5):.4f}   90% {q(.9):.4f}   max {q(1):.4f}")
print(f"     mean {float(sum(alld)/len(alld)/MAXD):.4f}")
print(f"     moves below 10% of the zone: {sum(1 for d in alld if d < MAXD/10)}/{len(alld)}"
      f"  ({100*sum(1 for d in alld if d < MAXD/10)/len(alld):.1f}%)")
print(f"\n  a bound charging delta = 0 overpays each move by the factor 2/(2 - {n}*delta);")
print(f"  at the median depth that factor is {float(2/(2 - n*alld[len(alld)//2])):.3f}")
