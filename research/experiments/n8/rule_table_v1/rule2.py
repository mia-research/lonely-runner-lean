# NATIVE rule, generalising the k=0 collapse:
#   at flank b, opening k, the nearest runner m reads m(8k+1)/(8b).
#   If m(8k+1) < b then that is < 1/8, so m is IN THE WAY and (b,k) is not lonely.
# Contrapositive: lonely at (b,k)  =>  b <= m(8k+1),  i.e.  k >= (b/m - 1)/8.
from math import gcd, ceil
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def lonely(ds,b,k): return all(clear(a,b,k) for a in ds)
rng=random.Random(5)
viol=0; tot=0; pruned=0; kept=0
for _ in range(3000):
    ds=sorted(rng.sample(range(1,120),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    m=min(ds)
    for b in ds:
        kmin = max(0, ceil((b/m - 1)/8))
        for k in range(b):
            tot+=1
            if k < kmin: pruned+=1
            else: kept+=1
            if lonely(ds,b,k) and k < kmin: viol+=1
print(f"openings examined {tot}")
print(f"  RULE: lonely at (b,k) requires k >= ceil((b/m - 1)/8)")
print(f"  violations (a lonely opening below the bound): {viol}")
print(f"  openings pruned by the rule: {pruned} ({pruned/tot:.3f});  kept {kept} ({kept/tot:.3f})")
print()
# how much does it prune the whole door-4 search?
rng2=random.Random(11); before=0; after=0
for _ in range(3000):
    ds=sorted(rng2.sample(range(1,120),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    m=min(ds)
    for b in ds:
        before += b
        kmin = max(0, ceil((b/m - 1)/8))
        after += max(0, b - kmin)
print(f"total openings to check, before the rule {before}, after {after}  ({after/before:.3f} of the original)")
print()
# sanity: the k=0 case of the rule is exactly the theorem already proved
print("k=0 case: the rule says lonely at (b,0) requires b <= m, i.e. b = m -- matches")
print("          Flanks.eq_min_of_lonely_first_opening, already proved.")
