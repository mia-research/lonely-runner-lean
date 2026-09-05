from math import gcd
from fractions import Fraction as F
def Cpoint(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def pkill_ok(p,q,r,X,Y):
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
L=[]; nR=0; nP=0; fail=0
for q in range(18,30):
    bound=(q-1)//3
    L.append(f"  · -- q = {q}")
    L.append(f"    have hpb : p ≤ {bound} := by omega")
    L.append(f"    interval_cases p")
    for p in range(1,bound+1):
        if gcd(p,q)!=1:
            L.append(f"    · exact absurd hcop (by decide)")
            continue
        # r in (q, 3q/2): 2r<3q -> r <= (3q-1)//2
        rmax=(3*q-1)//2
        L.append(f"    · -- p = {p}")
        L.append(f"      have hru : r ≤ {rmax} := by omega")
        L.append(f"      interval_cases r")
        for r in range(q+1, rmax+1):
            if r==p+q:
                L.append(f"      · omega  -- r={r}=p+q (diagonal, excluded by hndiag)")
                continue
            pts=[(m,Cpoint(r,q,m),Cpoint(p,q,m)) for m in range(2*q)]
            mR=next((m for (m,X,Y) in pts if in_R(X,Y)),None)
            if mR is not None:
                nR+=1
                L.append(f"      · exact bhk_prop11_exc_Rkill {p} {q} {r} {mR} (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])")
                continue
            mP=next((m for (m,X,Y) in pts if pkill_ok(p,q,r,X,Y)),None)
            if mP is not None:
                nP+=1
                L.append(f"      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall hcover g {p} {q} {r} s {mP} hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
                continue
            fail+=1
            L.append(f"      · sorry -- FAIL ({p},{q},{r})")
open("/tmp/q1830_body.txt","w").write("\n".join(L))
print(f"R={nR} P={nP} FAIL={fail}  total lines={len(L)}")
