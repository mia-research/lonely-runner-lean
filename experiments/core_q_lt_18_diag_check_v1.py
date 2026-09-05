from math import gcd
from fractions import Fraction as F
def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def pkill_ok(p,q,r,X,Y):  # worst-case s=r+1
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
diag=[]
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        r=p+q  # diagonal
        if not (q<r<2*q): continue
        den=2*q
        pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
        hitsR=any(in_R(X,Y) for (_,X,Y) in pts)
        hitsP=next(((l,X,Y) for (l,X,Y) in pts if pkill_ok(p,q,r,X,Y)),None)
        diag.append((p,q,r,hitsR,hitsP))
print("Diagonal triples (p,q,r,hitsR,Pwitness):")
nfail=0
for p,q,r,hR,hP in diag:
    tag = "R" if hR else ("P:m=%d"%hP[0] if hP else "FAIL")
    if not hR and not hP: nfail+=1
    print(f"  ({p},{q},{r}) -> {tag}")
print(f"\nFAIL (neither R nor P): {nfail} of {len(diag)}")
