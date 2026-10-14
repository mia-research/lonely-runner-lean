# Owner's suggestion: loneliness constrains only the subject's TWO adjacent gaps; the other six
# are free.  So is the exclusion at a flank concentrated in two runners, with the rest rarely
# binding?  If so the effective condition count is 2, not 6, and the error has a different source.
from math import gcd
from fractions import Fraction as F
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def dist(a,b,k):   # circle distance of runner a at flank b's k-th opening, as a Fraction
    x=F(a*(8*k+1), 8*b); f=x-(x.numerator//x.denominator); return min(f,1-f)
rng=random.Random(9)
conc=[]; nb=[]; solo=[]
for _ in range(1500):
    ds=sorted(rng.sample(range(1,90),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds); others=[a for a in ds if a!=b]
    if b<10: continue
    # per-runner: how many k does it block, and how many does it block ALONE?
    blocks={a: 0 for a in others}; alone={a: 0 for a in others}
    for k in range(b):
        bad=[a for a in others if not clear(a,b,k)]
        for a in bad: blocks[a]+=1
        if len(bad)==1: alone[bad[0]]+=1
    tot=sum(blocks.values())
    if tot==0: continue
    sb=sorted(blocks.values(), reverse=True)
    conc.append((sb[0]+sb[1])/tot)            # share of blocking done by the top TWO runners
    sa=sorted(alone.values(), reverse=True); ta=sum(sa)
    if ta>0: solo.append((sa[0]+sa[1])/ta)
conc.sort(); solo.sort()
print(f"[1] share of all blocking done by the TOP TWO runners, {len(conc)} flanks")
print(f"    min {conc[0]:.3f}  median {conc[len(conc)//2]:.3f}  max {conc[-1]:.3f}")
print(f"    (6 equal runners would give 2/6 = {2/6:.3f})")
print(f"[2] share of SOLE-blocking done by the top two, {len(solo)} flanks")
print(f"    min {solo[0]:.3f}  median {solo[len(solo)//2]:.3f}  max {solo[-1]:.3f}")
print()
print("[3] at a LONELY opening, how many runners sit within 1/8 + 1/100 of the subject?")
cnt={}
for _ in range(1500):
    ds=sorted(rng.sample(range(1,90),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds)
    if b<10: continue
    for k in range(b):
        if all(clear(a,b,k) for a in ds):
            near=sum(1 for a in ds if dist(a,b,k) <= F(1,8)+F(1,100))
            cnt[near]=cnt.get(near,0)+1
print(f"    distribution over lonely openings: {dict(sorted(cnt.items()))}")
print()
print("[4] the three tight sets at their unique lonely opening (b=1, k=0, t=1/8):")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    ds2=sorted(ds); b=1; k=0
    dd=[(a, dist(a,b,k)) for a in ds2]
    at18=[a for a,d in dd if d==F(1,8)]
    print(f"    {ds}: distances {[str(d) for _,d in dd]}   runners exactly at 1/8: {at18}")
