# A reformulation that strips the 8b modulus down to b.
# a(8k+1) = 8ak + a = 8(ak + q) + s   with  a = 8q + s,  s = a mod 8.
# So  a(8k+1) mod 8b = 8c + s  with  c = (a*k + q) mod b.
# CLEAR  iff  b <= 8c+s <= 7b  iff  (b-s)/8 <= c <= (7b-s)/8
# -- an interval of length exactly 3b/4, i.e. the middle three quarters of [0,b).
from math import gcd
import random
def clear_direct(a,b,k):
    return b <= (a*(8*k+1)) % (8*b) <= 7*b
def clear_reform(a,b,k):
    s = a % 8; q = a // 8
    c = (a*k + q) % b
    return (b - s) <= 8*c <= (7*b - s)
bad=0; tot=0
rng=random.Random(3)
for _ in range(200000):
    b=rng.randrange(1,120); a=rng.randrange(1,400); k=rng.randrange(0,b)
    tot+=1
    if clear_direct(a,b,k)!=clear_reform(a,b,k): bad+=1
print(f"[1] reformulation vs direct: {tot} cases, disagreements {bad}")
# the flank itself sits exactly on the LEFT edge of its own window
edge=0; tot2=0
for _ in range(20000):
    b=rng.randrange(1,200); k=rng.randrange(0,b); tot2+=1
    s=b%8; q=b//8; c=(b*k+q)%b
    if 8*c == b - s: edge+=1
print(f"[2] flank a=b sits exactly on its window's left edge: {edge}/{tot2}")
# so 6 non-trivial conditions of density 3/4 each; heuristic (3/4)^6 = {:.3f}
print(f"[3] heuristic density of lonely openings at a flank: (3/4)^6 = {(0.75)**6:.4f}")
obs=[]
rng2=random.Random(5)
for _ in range(3000):
    ds=sorted(rng2.sample(range(1,90),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    b=max(ds)
    cnt=sum(1 for k in range(b) if all(clear_reform(a,b,k) for a in ds))
    obs.append(cnt/b)
obs.sort()
print(f"    observed at flank b=max(ds): median {obs[len(obs)//2]:.4f}  10th {obs[int(.1*len(obs))]:.4f}  min {obs[0]:.4f}")
print(f"    flanks b=max with ZERO lonely openings: {sum(1 for x in obs if x==0)}/{len(obs)}")
