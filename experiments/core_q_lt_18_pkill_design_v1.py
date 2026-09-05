from math import gcd, floor
from fractions import Fraction as F

def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)

# Rmax (Lemma18 bound) to restrict to kept triples
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

# P-kill design check: witness m with X in (1/2,5/6], Y in [1/6,1/3], and the
# s-reduced slant conditions 1/(3(r+1)) <= (5/6-X)/r+(Y-1/6)/p  and <= (5/6-X)/r+(1/3-Y)/(q-p)
def pkill_ok(p,q,r,X,Y):
    if not (F(1,2)<X<=F(5,6)): return False
    if not (F(1,6)<=Y<=F(1,3)): return False
    lhs=F(1,3*(r+1))
    a=(F(5,6)-X)/r+(Y-F(1,6))/p
    b=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p)
    return lhs<=a and lhs<=b

bad=[]; good=[]
for q in range(5,18):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        rm=Rmax(p,q)
        for r in range(q+1,2*q):
            if gcd(r,q)!=1 or r>rm: continue
            if r==p+q: continue  # diagonal -> part6
            den=2*q
            pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
            if any(in_R(X,Y) for (_,X,Y) in pts): continue  # R-kill
            # needs P: find a witness m satisfying clean pkill
            w=None
            for (l,X,Y) in pts:
                if pkill_ok(p,q,r,X,Y): w=(l,X,Y); break
            if w is None: bad.append((p,q,r))
            else: good.append((p,q,r,w[0],w[1],w[2]))

print(f"clean P-kill witnesses found: {len(good)};  FAILED: {len(bad)}")
if bad: print("FAILED triples:",bad)
print("\nSample P witnesses (p,q,r,m,X,Y):")
for g in good[:12]: print("  ",g)
