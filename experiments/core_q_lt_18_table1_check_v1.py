from math import gcd, floor
from fractions import Fraction as F

# BHK Lemma 18 / Table 1: longest 0123-gap |I| = 1/3 + rho_max,
#   rho_max = max over runner-1 positions v in (1/6,1/3) of min((v-1/6)*x1,(1/3-v)*x2)
#   x1=q/p (=1/v1), x2=q/(q-p) (=1/v2).
# Runner-1 positions at l+1/2: {i/q} if p even, {(2i+1)/(2q)} if p odd.
# Lemma 4: v4 < 2/(3|I|). v4=r/q so r < q*2/(3|I|). R_max = ceil(that)-1.
def runner1_positions(p,q):
    if p%2==0:
        return [F(i,q) for i in range(q)]
    else:
        return [F(2*i+1,2*q) for i in range(q)]

def Rmax(p,q):
    x1=F(q,p); x2=F(q,q-p)
    best=None
    for v in runner1_positions(p,q):
        if F(1,6) < v < F(1,3):
            rho=min((v-F(1,6))*x1, (F(1,3)-v)*x2)
            I=F(1,3)+rho
            if best is None or I>best: best=I
    if best is None:
        # no runner-1 position strictly in (1/6,1/3): fall back to v4<2 (Cor16) => r<2q
        return 2*q-1
    vbound = 2/(3*best)        # v4 < vbound
    rbound = F(q)*vbound       # r < rbound
    # largest integer r strictly less than rbound
    rm = floor(rbound)
    if F(rm)==rbound: rm-=1
    return rm

# Now redo classification, EXCLUDING r > Rmax(p,q), and verify no HARD remains.
def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def in_P(X,Y,p,q,r,s):
    ca=F(r*(s-q),3*q*s); cb=F(p*(s-q),3*q*s); cc=F((q-p)*(s-q),3*q*s)
    return (F(1,6)-ca<=X and F(1,6)-cb<=Y and Y<=F(1,3)+cc and X<=F(5,6)
            and F(1,3*s)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
def slist(q,r,cap=500):
    out=[];s=r+1
    while s<=cap and len(out)<80:
        if gcd(s,q)==1: out.append(s)
        s+=1
    return out

from collections import Counter
counts=Counter(); hard=[]; excluded=0
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        rm=Rmax(p,q)
        for r in range(q+1,2*q):
            if gcd(r,q)!=1: continue
            if r>rm:
                excluded+=1; continue   # eliminated by Table 1 / Lemma 18
            diag=(r==p+q)
            den=2*q
            pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
            hitsR=any(in_R(X,Y) for (_,X,Y) in pts)
            sl=slist(q,r)
            killP=any(all(in_P(X,Y,p,q,r,s) for s in sl) for (_,X,Y) in pts)
            if hitsR: st="R"
            elif diag: st="DIAG"
            elif killP: st="P"
            else: st="HARD"; hard.append((q,p,r,rm))
            counts[st]+=1
print("After Table1 exclusion: counts=",dict(counts)," excluded(r>Rmax)=",excluded)
print("Rmax table:")
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        print(f"  ({p},{q}): Rmax={Rmax(p,q)}  v4<= {F(Rmax(p,q),q)}")
if hard:
    print("REMAINING HARD:",hard)
else:
    print("\n*** 0 HARD remaining — route fully closes ***")
