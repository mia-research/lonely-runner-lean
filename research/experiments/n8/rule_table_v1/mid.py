# If slow runners block long runs and fast ones only punch scattered holes, the lonely opening
# should sit INSIDE a long clear stretch of the slowest runner -- and plausibly near its middle.
# That would be a NAMING rule, not a count.  Test it.
from math import gcd
import random, statistics
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def clear_runs(a,b):
    """maximal runs of consecutive k where runner a is CLEAR, as (start,len) on the cycle."""
    cl=[k for k in range(b) if clear(a,b,k)]
    if not cl: return []
    cs=set(cl); runs=[]
    for k in cl:
        if (k-1)%b not in cs:
            L=0; j=k
            while j%b in cs and L<b: L+=1; j+=1
            runs.append((k,L))
    return runs
rng=random.Random(8)
pos=[]; inlongest=0; tot=0; relrank=[]
for _ in range(1500):
    ds=sorted(rng.sample(range(1,200),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds); m=min(ds)
    if b<40: continue
    R=clear_runs(m,b)
    if not R: continue
    Rs=sorted(R,key=lambda r:-r[1])
    longest=Rs[0]
    for k in range(b):
        if not all(clear(a,b,k) for a in ds): continue
        tot+=1
        # which clear-run of the slowest runner does k fall in, and where in it?
        for (st,L) in R:
            off=(k-st)%b
            if off<L:
                pos.append(off/max(1,L-1) if L>1 else 0.5)
                relrank.append(sorted([l for _,l in R],reverse=True).index(L))
                if (st,L)==longest: inlongest+=1
                break
print(f"lonely openings examined: {tot}")
if tot:
    print(f"  fraction inside the slowest runner's LONGEST clear run: {inlongest/tot:.3f}")
    print(f"  (a run holds ~1/#runs of the clear set; #runs median ~9, so chance ~0.11-0.2)")
    pos.sort()
    print(f"  position within its clear run (0=start, 1=end): min {pos[0]:.2f} "
          f"25% {pos[len(pos)//4]:.2f} median {pos[len(pos)//2]:.2f} 75% {pos[3*len(pos)//4]:.2f}")
    import collections
    c=collections.Counter(relrank)
    print(f"  rank of the containing run by length (0 = longest): {dict(sorted(c.items())[:6])}")
