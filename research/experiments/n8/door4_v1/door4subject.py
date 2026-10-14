# An 8-runner ARRANGEMENT gives eight difference sets, one per subject.  ExistenceAt8 treats
# each in isolation -- the coupling is discarded.  Is that a loss?  Test:
#   (a) does difficulty vary a lot across the eight subjects of one arrangement?
#   (b) is some subject choice always easy (a 'subject rule', analogous to a flank rule)?
#   (c) in the extremal arrangement, is every subject tight, or only one?
from math import gcd
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def best_count(ds):
    ds=tuple(sorted(set(ds)))
    g=0
    for x in ds: g=gcd(g,x)
    ds=tuple(x//g for x in ds)
    return max(sum(1 for k in range(b) if all(clear(a,b,k) for a in ds)) for b in ds)
def subjects(v):
    return [tuple(abs(x-v[i]) for x in v if x!=v[i]) for i in range(len(v))]
print("[c] the extremal arrangement v = (0,1,2,3,4,5,6,7): per-subject best count")
v=tuple(range(8))
print("   ", [best_count(s) for s in subjects(v)])
print("    -> only the two EXTREME subjects are tight at 1; interior subjects give 2 or 3")
print()
print("[a] spread across the eight subjects of one arrangement:")
rng=random.Random(7); spreads=[]; mins=[]; argmin_is_extreme=0; N=0
for _ in range(1500):
    v=sorted(rng.sample(range(0,120),8))
    cs=[best_count(s) for s in subjects(v)]
    N+=1; spreads.append(max(cs)-min(cs)); mins.append(min(cs))
    i=cs.index(min(cs))
    if i in (0,7): argmin_is_extreme+=1
spreads.sort(); mins.sort()
print(f"    {N} arrangements: max-min spread  min {spreads[0]}  median {spreads[len(spreads)//2]}  max {spreads[-1]}")
print(f"    hardest subject's count: min {mins[0]}  1% {mins[len(mins)//100]}  median {mins[len(mins)//2]}")
print(f"    arrangements with a subject having ZERO: {mins.count(0)}")
print(f"    hardest subject is an EXTREME runner (slowest or fastest): {argmin_is_extreme}/{N} (chance 2/8 = 0.25)")
print()
print("[b] is any fixed subject index always easy?  count of arrangements where index i is the hardest:")
rng2=random.Random(11); hard={i:0 for i in range(8)}
for _ in range(1500):
    v=sorted(rng2.sample(range(0,120),8))
    cs=[best_count(s) for s in subjects(v)]
    hard[cs.index(min(cs))]+=1
print(f"    {hard}")
