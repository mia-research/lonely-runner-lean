# The cushion (M-1)/error has fallen 1.127 -> 1.084 as the search widened.  If it goes BELOW 1
# the first-moment argument fails.  Hunt for the minimum by hill-climbing rather than sampling.
from math import gcd
import random
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def exact_main(ds):
    t=0.0
    for b in ds:
        x=float(b)
        for a in ds:
            if a!=b: x *= win(a,b)/b
        t+=x
    return t
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def T(ds): return sum(sum(1 for k in range(b) if all(clear(a,b,k) for a in ds)) for b in ds)
def cushion(ds):
    M=exact_main(ds); t=T(ds)
    if M<=t: return 9e9, t, M
    return (M-1)/(M-t), t, M
def norm(ds):
    ds=tuple(sorted(set(ds)))
    if len(ds)!=7 or ds[0]<1: return None
    g=0
    for x in ds: g=gcd(g,x)
    return tuple(x//g for x in ds)
rng=random.Random(1234)
best=None
for restart in range(400):
    cur=norm(rng.sample(range(1,120),7))
    while cur is None: cur=norm(rng.sample(range(1,120),7))
    cc,_,_=cushion(cur)
    for step in range(300):
        i=rng.randrange(7)
        delta=rng.choice([-8,-4,-3,-2,-1,1,2,3,4,8])
        cand=list(cur); cand[i]=cand[i]+delta
        if cand[i]<1 or cand[i]>400: continue
        nd=norm(cand)
        if nd is None: continue
        nc,t,M=cushion(nd)
        if nc<cc:
            cur, cc = nd, nc
    if best is None or cc<best[0]:
        c2,t2,M2=cushion(cur)
        best=(c2,cur,t2,M2)
print(f"hill-climb, 400 restarts x 300 steps")
print(f"  minimum cushion found: {best[0]:.4f}x")
print(f"     ds={best[1]}  T={best[2]}  M={best[3]:.3f}  error={best[3]-best[2]:.3f}")
print(f"     error/M = {(best[3]-best[2])/best[3]:.4f}   requirement < {1-1/best[3]:.4f}")
print()
print(f"  first-moment argument {'STILL HOLDS' if best[0]>1 else 'FAILS'} at the minimum found")
if best[0]>1:
    print(f"  margin remaining: T = {best[2]} against the 1 needed")
