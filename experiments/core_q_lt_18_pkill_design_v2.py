from math import gcd, floor
from fractions import Fraction as F
def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def runner1_positions(p,q):
    return [F(i,q) for i in range(q)] if p%2==0 else [F(2*i+1,2*q) for i in range(q)]
def Rmax(p,q):
    x1=F(q,p); x2=F(q,q-p); best=None
    for v in runner1_positions(p,q):
        if F(1,6)<v<F(1,3):
            rho=min((v-F(1,6))*x1,(F(1,3)-v)*x2); I=F(1,3)+rho
            if best is None or I>best: best=I
    if best is None: return 2*q-1
    rb=F(q)*(2/(3*best)); rm=floor(rb)
    if F(rm)==rb: rm-=1
    return rm

# worst-case s = r+1: corr(s0)=(s0-q)/(3 q s0), monotone increasing => smallest at s0=r+1.
def pkill_ok(p,q,r,X,Y):
    s0=r+1
    corr=F(s0-q,3*q*s0)
    if not (X >= F(1,6) - r*corr): return False
    if not (Y >= F(1,6) - p*corr): return False
    if not (Y <= F(1,3) + (q-p)*corr): return False
    if not (X <= F(5,6)): return False
    lhs=F(1,3*s0)
    if not (lhs <= (F(5,6)-X)/r+(Y-F(1,6))/p): return False
    if not (lhs <= (F(5,6)-X)/r+(F(1,3)-Y)/(q-p)): return False
    return True

bad=[]; good=[]
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        rm=Rmax(p,q)
        for r in range(q+1,2*q):
            if gcd(r,q)!=1 or r>rm or r==p+q: continue
            den=2*q
            pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
            if any(in_R(X,Y) for (_,X,Y) in pts): continue
            w=next(((l,X,Y) for (l,X,Y) in pts if pkill_ok(p,q,r,X,Y)),None)
            if w is None: bad.append((p,q,r))
            else: good.append((p,q,r,w[0]))
print(f"P-kill (s=r+1 worst-case) witnesses: {len(good)};  FAILED: {len(bad)}")
if bad: print("FAILED:",bad)
else: print("*** ALL P-cases covered by s=r+1 worst-case combinator ***")
print("witnesses (p,q,r,m):", good)
