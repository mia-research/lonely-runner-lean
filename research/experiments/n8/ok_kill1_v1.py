r"""
ok_kill1_v1 -- the phihat(1) = 0 lever.

The arc [1/8,7/8] spans 270 degrees, so 0 lies in the convex hull of { e(-t) : t in arc }:
put weights at t = 1/8, 1/2, 7/8, whose phases are -45, 180, +45 degrees.  Solving
   2w cos(45) = w3,  2w + w3 = 1   gives   w = 1/(2+sqrt2) ~ 0.2929,  w3 ~ 0.4142,
so a nonnegative phi on the arc with phihat(1) = 0 EXISTS.  Point masses have no decay, so
spread each into a narrow bump and optimise.  Measured: does killing low coefficients beat
the indicator's tail ratio of 2.66?
"""
import numpy as np
from itertools import combinations
from math import gcd, sqrt

N=1<<14; t=np.arange(N)/N
lo,hi=1/8,7/8
E=(2,6,7,8,10,13,14); K=60

def bump(center,width):
    x=(t-center)/width
    v=np.zeros(N); m=np.abs(x)<1
    v[m]=np.exp(-1.0/(1-x[m]**2))
    return v

def tail_ratio(phi,K=K,report=False):
    F=np.fft.fft(phi)/N
    def ch(k): return F[k%N]
    c0=ch(0).real
    if c0<=0: return np.inf,0,0
    main=c0**7; tail=0.0
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g; m=1
        while m*max(a,b)<=K:
            tail+=2*abs(ch(m*b)*ch(-m*a))*c0**5; m+=1
    for i,j,l in combinations(range(7),3):
        A,B,C=E[i],E[j],E[l]
        for ka in range(-K,K+1):
            if ka==0: continue
            for kb in range(-K,K+1):
                if kb==0: continue
                r=-(ka*A+kb*B)
                if r%C: continue
                kc=r//C
                if kc==0 or abs(kc)>K: continue
                tail+=abs(ch(ka)*ch(kb)*ch(kc))*c0**4
    return tail/main, c0, abs(ch(1))/c0

w=1/(2+sqrt(2)); w3=1-2*w
print(f"three-bump weights: w(1/8)=w(7/8)={w:.6f}, w(1/2)={w3:.6f}")
print(f"\n{'construction':34} {'phihat(0)':>10} {'|ph(1)|/ph(0)':>14} {'tail/main':>10}")
# baseline
phi=np.zeros(N); phi[(t>=lo)&(t<=hi)]=1.0
r,c0,r1=tail_ratio(phi); print(f"{'indicator on [1/8,7/8]':34} {c0:10.6f} {r1:14.6f} {r:10.2f}")
best=None
for width in (0.02,0.04,0.06,0.08,0.10):
    phi=w*bump(lo+width,width)+w*bump(hi-width,width)+w3*bump(0.5,width)
    phi=np.maximum(phi,0)
    r,c0,r1=tail_ratio(phi)
    print(f"{'3 bumps, width '+str(width):34} {c0:10.6f} {r1:14.6f} {r:10.2f}")
    if best is None or r<best[0]: best=(r,width)
# mixture: indicator plus the three-bump corrector, scanning the mix
print()
for lam in (0.0,0.2,0.4,0.6,0.8,1.0):
    base=np.zeros(N); base[(t>=lo)&(t<=hi)]=1.0
    corr=w*bump(lo+0.06,0.06)+w*bump(hi-0.06,0.06)+w3*bump(0.5,0.06)
    corr=corr/corr.sum()*base.sum()
    phi=(1-lam)*base+lam*corr
    r,c0,r1=tail_ratio(phi)
    print(f"{'mix lambda='+str(lam):34} {c0:10.6f} {r1:14.6f} {r:10.2f}")
print("\nratio < 1 would prove this tuple.  Lowest achieved above:", f"{best[0]:.2f}")
