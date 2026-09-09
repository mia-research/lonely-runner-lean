r"""
ok_positivity_v1 -- can the proof be pure positivity?  And if not, how close can we get?

THE DREAM.  If phi >= 0 with supp(phi) contained in [1/8,7/8] and phihat(k) >= 0 for ALL k,
then  int prod_j phi(e_j t) dt = sum_{k.e=0} prod_j phihat(k_j) >= phihat(0)^7 > 0,
every term being nonnegative -- and positivity of the integral forces some t with every
e_j t in [1/8,7/8], i.e. ||e_j t|| >= 1/8.  That is LRC(8) in three lines.

THE OBSTRUCTION (proved, elementary).  phihat >= 0 and phi >= 0 give
        phi(0) = sum_k phihat(k) >= |sum_k phihat(k) e(kt)| = |phi(t)|   for every t,
so phi(0) = max phi > 0 whenever phi is not identically 0.  But 0 is NOT in [1/8,7/8], so
supp(phi) in [1/8,7/8] forces phi(0) = 0.  Contradiction.  NO SUCH phi EXISTS.

So the ray series MUST carry negative terms: the negativity is structural, not an artefact
of choosing f = indicator.  What remains is to pick phi minimising the damage.  Measured
below: over a family of nonnegative phi supported in [1/8,7/8], the ratio
        (absolute ray tail) / phihat(0)^7
at the extremal tuple.  Ratio < 1 for some phi would BE a proof for that tuple.
"""
import numpy as np
from itertools import combinations
from math import gcd

N = 1<<14
t = np.arange(N)/N
lo, hi = 1/8, 7/8
inside = (t>=lo)&(t<=hi)

def coeffs(phi, K):
    """phihat(k) for |k| <= K via FFT"""
    F = np.fft.fft(phi)/N
    return np.array([F[k % N] for k in range(-K,K+1)])

def make(kind, p=1.0):
    phi = np.zeros(N)
    x = (t[inside]-lo)/(hi-lo)          # 0..1 across the arc
    if kind=="ind":   phi[inside] = 1.0
    elif kind=="sin": phi[inside] = np.sin(np.pi*x)**p
    elif kind=="bump":phi[inside] = np.exp(-1.0/np.maximum(x*(1-x),1e-12))**p
    return phi

E = (2,6,7,8,10,13,14)
K = 60
print(f"extremal tuple {E};   main term = phihat(0)^7,  tail = sum |prod phihat| over")
print(f"supports 2 and 3 with |k| <= {K}  (a LOWER bound on the true tail)\n")
print(f"{'phi':16} {'phihat(0)':>10} {'main':>12} {'|ph(1)|/ph(0)':>14} {'tail(2+3)':>12} {'ratio':>9}")
for kind,p in [("ind",1),("sin",1),("sin",2),("sin",4),("sin",8),("bump",1),("bump",0.3)]:
    phi = make(kind,p)
    c = coeffs(phi,K); c0 = c[K].real
    def ch(k): return c[k+K]
    main = c0**7
    tail = 0.0
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
        m=1
        while m*max(a,b)<=K:
            tail += 2*abs(ch(m*b)*ch(-m*a))*c0**5
            m+=1
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
                tail += abs(ch(ka)*ch(kb)*ch(kc))*c0**4
    print(f"{kind+'^'+str(p):16} {c0:10.6f} {main:12.3e} {abs(ch(1))/c0:14.4f} "
          f"{tail:12.3e} {tail/main:9.2f}")
print("\nratio < 1 would prove the tuple; every row above is the ABSOLUTE tail, truncated.")
