# The closed dyadic route used denominators 2^kappa (numerator odd).  My named instant is
# (8k+1)/(8c) -- that is the dyadic case only when c is a power of 2.  Does GENERAL c beat it?
from math import gcd, log2
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=4000, pow2_only=False):
    c=1
    while c<=cmax:
        for k in range(c):
            if ok(ds,c,k): return c
        c = c*2 if pow2_only else c+1
    return None
print(f"{'V':>6} {'n':>6} {'max general c':>15} {'max pow2 c':>12} {'ratio':>7}")
for V in (50, 100, 200, 400, 800):
    rng=random.Random(V); g_mx=0; p_mx=0; N=0; gnone=pnone=0
    for _ in range(1200):
        ds=sorted(rng.sample(range(1,V+1),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
        N+=1
        cg=smallest_c(ds); cp=smallest_c(ds, pow2_only=True)
        if cg is None: gnone+=1
        else: g_mx=max(g_mx,cg)
        if cp is None: pnone+=1
        else: p_mx=max(p_mx,cp)
    print(f"{V:>6} {N:>6} {g_mx:>15} {p_mx:>12} {p_mx/max(1,g_mx):>7.1f}x"
          + (f"   (general none {gnone}, pow2 none {pnone})" if gnone or pnone else ""))
print()
print("  the closed dyadic route reported max kappa = 7,8,8,9,10 for V = 50..800,")
print("  i.e. denominator 2^kappa = 8c, so c = 2^(kappa-3) = 16,32,32,64,128.")
