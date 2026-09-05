"""
Pin the (1,2) window for Lean: with Y = fract(2X) = 2X-1 on X in (1/2,1), p2=q-p,
which of the 6 P-constraints bind at the left/right ends of line∩P, and is there a
clean fixed window of length >=1/q? Report, per (p,q,r=q+p/2, s), the [Xa,Xb], the
binding constraint at each end, and test candidate explicit windows.

6 constraints (Y=2X-1):
 h39: X >= 1/6 - e1                  (e1=r(s-q)/3qs)
 h40: X >= 7/12 - e0/2               (Y>=1/6-e0; e0=p(s-q)/3qs)
 h41: X <= 2/3 + e2/2                (Y<=1/3+e2; e2=p2(s-q)/3qs)
 hxle:X <= 5/6
 h42a: (5/6-X)/r + (2X-7/6)/p   >= 1/(3s)   -> lower bound (coeff -1/r+2/p>0)
 h42b: (5/6-X)/r + (4/3-2X)/p2  >= 1/(3s)   -> upper bound (coeff -1/r-2/p2<0)
"""
from math import gcd
from fractions import Fraction as F

def survivors_12(qmax):
    out=[]
    for q in range(18,qmax+1):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            if (2*q+p)%2!=0: continue
            r=(2*q+p)//2
            if not (q<r) or 2*r>=3*q: continue
            out.append((p,q,r))
    return out

def bounds(p,q,r,s):
    p2=q-p
    e0=F(p*(s-q),3*q*s); e1=F(r*(s-q),3*q*s); e2=F(p2*(s-q),3*q*s); inv=F(1,3*s)
    Lo={}; Hi={}
    Lo['h39']=F(1,6)-e1
    Lo['h40']=F(7,12)-e0/2
    Hi['h41']=F(2,3)+e2/2
    Hi['hxle']=F(5,6)
    # h42a: A*X>=B ; A=-1/r+2/p>0 -> X>= B/A
    A=-F(1,r)+F(2,p); B=inv-F(5,6*r)+F(7,6*p)
    Lo['h42a']=B/A
    # h42b: A2*X<=B2 ; A2=1/r+2/p2>0 ; (5/6-X)/r+(4/3-2X)/p2>=inv -> -(1/r+2/p2)X >= inv-5/6r-4/3p2
    A2=F(1,r)+F(2,p2); B2=F(5,6*r)+F(4,3*p2)-inv
    Hi['h42b']=B2/A2
    return Lo,Hi

from collections import Counter
for qmax in [60]:
    survs=survivors_12(qmax)
    left_binds=Counter(); right_binds=Counter()
    Hmin=None
    # candidate explicit windows to test for subset-P + length>=1/q
    cand_ok={'[2/3+e2/2-1/q, 2/3+e2/2]':0, '[Xa, Xa+1/q] from h42a':0}
    cand_tot=0; gridcop_bad=0
    for (p,q,r) in survs:
        # gcd(r,q)=1 needed for grid step
        if gcd(r,q)!=1: gridcop_bad+=1
        for s in range(r+1,3*q+1):
            i=s-r
            special = (p==2 and i==1)
            Lo,Hi=bounds(p,q,r,s)
            Xa=max(Lo.values()); Xb=min(Hi.values())
            la=max(Lo,key=lambda k:Lo[k]); rb=min(Hi,key=lambda k:Hi[k])
            if Xb>Xa:
                left_binds[la]+=1; right_binds[rb]+=1
                H=Xb-Xa
                if not special:
                    if Hmin is None or H<Hmin: Hmin=H
            cand_tot+=1
            # candidate A: right-anchored window [Xb-1/q, Xb] subset P?  (Xb=upper end)
            if not special and Xb-Xa>=F(1,q):
                cand_ok['[2/3+e2/2-1/q, 2/3+e2/2]']+=1  # only counts feasibility
    print(f"qmax={qmax}: survivors={len(survs)}, gcd(r,q)!=1 in {gridcop_bad}")
    print(f"  LEFT-end binding constraint: {dict(left_binds)}")
    print(f"  RIGHT-end binding constraint: {dict(right_binds)}")
    print(f"  min H (non-special) = {float(Hmin):.5f}  (1/q max = {1/18:.5f})")
    print(f"  non-special with H>=1/q: {cand_ok['[2/3+e2/2-1/q, 2/3+e2/2]']}/{cand_tot}")
