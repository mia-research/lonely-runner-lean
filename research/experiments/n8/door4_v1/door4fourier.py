# N(b) = sum_k prod_i 1[c_i(k) in I_i].  Expanding over Z/b, the h=0 term is b*prod(|I_i|/b)
# and every error term needs a RELATION  sum h_i a_i = 0 (mod b).  Verify the main term, then
# ask what the error is made of: is it a few small relations?
from math import gcd
from itertools import product
import random
def window(a,b):
    s=a%8
    lo=-(-(b-s)//8)          # ceil((b-s)/8)
    hi=(7*b-s)//8            # floor((7b-s)/8)
    return lo,hi
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
def main_term(ds,b):
    t=b
    for a in ds:
        if a==b: continue           # the flank contributes its whole window
        lo,hi=window(a,b); t *= (hi-lo+1)/b
    return t
rng=random.Random(202); rows=[]
for _ in range(4000):
    ds=sorted(rng.sample(range(1,90),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    b=max(ds)
    if b<8: continue
    n=N(ds,b); m=main_term(ds,b)
    rows.append((n/m if m>0 else 0, n, m, ds, b))
r=sorted(x[0] for x in rows)
print(f"{len(rows)} flanks b=max(ds):  actual / main term")
print(f"   min {r[0]:.3f}  1% {r[len(r)//100]:.3f}  median {r[len(r)//2]:.3f}  max {r[-1]:.3f}")
print(f"   flanks where the error EXCEEDS the main term (ratio <= 0): {sum(1 for x in r if x<=0)}")
print()
# the worst flanks: is there a SMALL relation sum h_i a_i = 0 mod b ?
print("worst flanks, and their smallest non-trivial relation among the six non-flank runners:")
for ratio,n,m,ds,b in sorted(rows,key=lambda x:x[0])[:4]:
    others=[a for a in ds if a!=b]
    best=None
    for h in product(range(-3,4), repeat=len(others)):
        if all(x==0 for x in h): continue
        if sum(hi*ai for hi,ai in zip(h,others)) % b == 0:
            w=sum(abs(x) for x in h)
            if best is None or w<best[0]: best=(w,h)
    print(f"   ds={ds} b={b}: actual {n} vs main {m:.2f} (ratio {ratio:.3f})")
    print(f"      smallest relation (L1 weight {best[0]}): h={best[1]}   gcds={[gcd(a,b) for a in others]}" if best else "      no relation with |h_i|<=3")
print()
print("control - a TYPICAL flank, for comparison:")
for ratio,n,m,ds,b in sorted(rows,key=lambda x:abs(x[0]-1.0))[:2]:
    others=[a for a in ds if a!=b]
    best=None
    for h in product(range(-3,4), repeat=len(others)):
        if all(x==0 for x in h): continue
        if sum(hi*ai for hi,ai in zip(h,others)) % b == 0:
            w=sum(abs(x) for x in h)
            if best is None or w<best[0]: best=(w,h)
    print(f"   ds={ds} b={b}: ratio {ratio:.3f}, smallest relation L1 weight {best[0] if best else '>18'}")
