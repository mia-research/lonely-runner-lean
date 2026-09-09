r"""
ok_fourier_v2 -- the support-3 tail, and whether the ABSOLUTE Fourier bound can close (A).

|G| = sum over k with k.e = 0 of prod fhat(k_j),  fhat(0)=3/4, fhat(k) = -sin(pi k/4)/(pi k),
fhat(k) = 0 iff 4|k.  A valid lower bound needs the FULL absolute tail:

    |G|  >=  (3/4)^7  -  T2  -  T3  -  T4  - ...        T_s = absolute tail at support s.

v1 computed only T2 and I must not read (3/4)^7 - T2 > 0 as settling anything.
Here T3 is enumerated exactly (per triple, a rank-2 lattice, cut at height H), and T4 by the
same method on 4-subsets, so the partial bound (3/4)^7 - T2 - T3 - T4 is honest as far as it
goes -- still an OVERestimate of |G| because supports 5,6,7 are omitted.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, sin, pi

def fhat(k):
    if k == 0: return 0.75
    if k % 4 == 0: return 0.0
    return -sin(pi*k/4)/(pi*k)

def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))

MAIN=0.75**7
def T2(E,M=600):
    tot=0.0
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
        s=sum(abs(fhat(m*b)*fhat(m*a)) for m in range(1,M+1))
        tot+=2*s*(0.75**5)
    return tot
def Ts(E,size,H):
    """absolute tail at support exactly `size`, heights |k| <= H"""
    tot=0.0
    for idx in combinations(range(7),size):
        sub=[E[i] for i in idx]
        w=0.75**(7-size)
        if size==3:
            a,b,c=sub
            for ka in range(-H,H+1):
                if ka==0 or ka%4==0: continue
                fa=fhat(ka)
                for kb in range(-H,H+1):
                    if kb==0 or kb%4==0: continue
                    r=-(ka*a+kb*b)
                    if r % c: continue
                    kc=r//c
                    if kc==0 or kc%4==0: continue
                    tot+=abs(fa*fhat(kb)*fhat(kc))*w
        else:
            a,b,c,d=sub
            for ka in range(-H,H+1):
                if ka==0 or ka%4==0: continue
                for kb in range(-H,H+1):
                    if kb==0 or kb%4==0: continue
                    for kc in range(-H,H+1):
                        if kc==0 or kc%4==0: continue
                        r=-(ka*a+kb*b+kc*c)
                        if r % d: continue
                        kd=r//d
                        if kd==0 or kd%4==0: continue
                        tot+=abs(fhat(ka)*fhat(kb)*fhat(kc)*fhat(kd))*w
    return tot

tests=[(2,6,7,8,10,13,14),(1,3,4,5,7,11,24),(1,3,5,7,13,15,24),
       (2,12,13,14,16,19,20),(3,10,14,15,16,19,21)]
print(f"main (3/4)^7 = {MAIN:.6f}\n")
print(f"{'E':28} {'|G|':>9} {'T2':>9} {'T3(H=30)':>10} {'T4(H=14)':>10} {'main-T2-T3-T4':>15}")
for E in tests:
    g=float(G_measure(list(E))); t2=T2(list(E)); t3=Ts(list(E),3,30); t4=Ts(list(E),4,14)
    print(f"{str(E):28} {g:9.6f} {t2:9.6f} {t3:10.6f} {t4:10.6f} {MAIN-t2-t3-t4:15.6f}")
print("\nT3/T4 are truncated at the stated heights, so they UNDERSTATE the true tails;")
print("supports 5,6,7 are omitted entirely.  Any negative column is already fatal.")
