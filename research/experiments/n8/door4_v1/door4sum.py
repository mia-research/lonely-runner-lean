# max_b N(b) >= 1 and sum_b N(b) >= 1 are EQUIVALENT, but the sum has a clean main term:
#     sum_b N(b)  ~  (3/4)^6 * sum_b b
# and averaging over flanks may be far more robust than any single flank (whose worst ratio
# was 0.324).  Measure the summed ratio, including on the tight sets.
from math import gcd
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
def tot(ds): return sum(N(ds,b) for b in ds)
def pred(ds): return (0.75**6)*sum(ds)
print("the three tight sets:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    t=tot(ds); p=pred(ds)
    print(f"   {str(ds):24s} total {t:3d}  predicted {p:6.2f}  ratio {t/p:.3f}")
print()
rng=random.Random(404); rs=[]; zeros=0; worst=None
for _ in range(8000):
    ds=sorted(rng.sample(range(1,70),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    t=tot(ds); p=pred(ds)
    if t==0: zeros+=1
    r=t/p; rs.append(r)
    if worst is None or r<worst[0]: worst=(r,ds,t,p)
rs.sort()
print(f"{len(rs)} primitive sets, SUMMED over all seven flanks:")
print(f"   ratio total/predicted : min {rs[0]:.3f}  1% {rs[len(rs)//100]:.3f}  median {rs[len(rs)//2]:.3f}  max {rs[-1]:.3f}")
print(f"   sets with total ZERO  : {zeros}")
print(f"   worst: ds={worst[1]} total {worst[2]} vs predicted {worst[3]:.2f} (ratio {worst[0]:.3f})")
print()
print("compare: the worst SINGLE-flank ratio measured earlier was 0.324 (b = max ds).")
print(f"   summed worst here is {rs[0]:.3f}, 1st percentile {rs[len(rs)//100]:.3f}")
print()
# does the summed main term ever fall BELOW 1?  that is when the first moment cannot conclude.
small=[p for p in (pred(tuple(x//max(1,gcd(*ds)) for x in ds)) for ds in []) ]
rng2=random.Random(77); lows=0; tot2=0
for _ in range(8000):
    ds=sorted(rng2.sample(range(1,70),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    tot2+=1
    if pred(ds) < 1.0: lows+=1
print(f"sets where the predicted total is BELOW 1 (first moment cannot conclude): {lows}/{tot2}")
print(f"   smallest possible sum(ds) for a primitive 7-set is 1+2+..+7 = 28 -> predicted {pred((1,2,3,4,5,6,7)):.2f}")
