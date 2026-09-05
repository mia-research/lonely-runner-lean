from math import gcd
from fractions import Fraction as F
def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
# exc_open configs for q in [18,30): gcd(p,q)=1, 3p<q, q<r<3q/2 (2r<3q), r != p+q (hndiag),
# and exclude (1,2)/(1,-2) which are peeled: 2r=2q+p or 2r+p=3q.
fails=[]; total=0; need_check=0
for q in range(18,30):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        for r in range(q+1, (3*q+1)//2 + 1):
            if 2*r>=3*q: continue   # hr32: 2r<3q
            if r==p+q: continue     # hndiag
            # peel (1,2): 2r=2q+p ; (1,-2): 2r+p=3q  (only relevant when p could be the i=1 readout, but exclude these r)
            if 2*r==2*q+p: continue
            if 2*r+p==3*q: continue
            total+=1
            den=2*q
            pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
            if not any(in_R(X,Y) for (_,X,Y) in pts):
                fails.append((p,q,r))
print(f"q in [18,30): total configs {total}, NOT-hitting-R: {len(fails)}")
for f in fails: print("  ",f, "v1=p/q=",f[0],"/",f[1])

print("\n=== Can the 49 R-avoiders be P-killed (worst-case s=r+1)? ===")
def pkill_ok(p,q,r,X,Y):
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
pf=[]
for (p,q,r) in fails:
    den=2*q
    pts=[(l,fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)]
    if not any(pkill_ok(p,q,r,X,Y) for (_,X,Y) in pts):
        pf.append((p,q,r))
print(f"of {len(fails)} R-avoiders, P-kill FAILS for: {len(pf)}")
for f in pf: print("   ",f,"v1>1/6:",6*f[0]>f[1])
