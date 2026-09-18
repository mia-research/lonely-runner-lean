# Robustness of the SUMMED first moment across speed ranges, with the EXACT main term
#   M(ds) = sum_b [ b * prod_{a != b} |I_a(b)| / b ]
# Target: sum_b N(b) >= 1.  Needed: error/main <= 1 - 1/M.  Observed error/main = 1 - ratio.
from math import gcd
import random
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
def exact_main(ds):
    tot=0.0
    for b in ds:
        t=float(b)
        for a in ds:
            if a==b: continue
            t *= win(a,b)/b
        tot+=t
    return tot
print(f"{'range':>12} {'sets':>6} {'min ratio':>10} {'1%':>8} {'median':>8} {'min main':>9} {'worst err/main':>15} {'needed':>8}")
for V in (30, 70, 150, 400, 1000):
    rng=random.Random(V); rs=[]; mains=[]; zeros=0
    trials = 4000 if V<=150 else 1200
    for _ in range(trials):
        ds=sorted(rng.sample(range(1,V),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
        M=exact_main(ds); T=sum(N(ds,b) for b in ds)
        if T==0: zeros+=1
        rs.append(T/M); mains.append(M)
    rs.sort(); mains.sort()
    need = 1 - 1/mains[0]
    print(f"{'[1,'+str(V)+')':>12} {len(rs):>6} {rs[0]:>10.3f} {rs[len(rs)//100]:>8.3f} {rs[len(rs)//2]:>8.3f} {mains[0]:>9.2f} {1-rs[0]:>15.3f} {need:>8.3f}   zeros {zeros}")
print()
print("the three tight sets, exact main term:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    M=exact_main(ds); T=sum(N(ds,b) for b in ds)
    print(f"   {str(ds):24s} total {T}  exact main {M:.3f}  ratio {T/M:.3f}  err/main {1-T/M:.3f}  needed <= {1-1/M:.3f}")
