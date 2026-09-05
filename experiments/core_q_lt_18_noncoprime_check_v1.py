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
def pkill_ok(p,q,r,X,Y):
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))

# ALL r in (q,2q), INCLUDING gcd(r,q)>1 (no coprimality filter)
counts={'R':0,'P':0,'DIAG':0,'EXCL':0,'HARD':0}; hard=[]
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        rm=Rmax(p,q)
        for r in range(q+1,2*q):
            if r>rm: counts['EXCL']+=1; continue
            if r==p+q: counts['DIAG']+=1; continue
            den=2*q
            pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
            if any(in_R(X,Y) for (_,X,Y) in pts): counts['R']+=1; continue
            if any(pkill_ok(p,q,r,X,Y) for (_,X,Y) in pts): counts['P']+=1; continue
            counts['HARD']+=1; hard.append((p,q,r,gcd(r,q)))
print("ALL r in (q,2q) (incl. non-coprime):", counts)
if hard: print("HARD:",hard)
else: print("*** still 0 HARD — dispatch needs NO gcd(r,q)=1 ***")
