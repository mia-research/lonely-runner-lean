from math import gcd
from fractions import Fraction as F
def Cpoint(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def pkill_ok(p,q,r,X,Y):
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
L=[]
nexp=0
for q in range(5,18):
    bound=(q-1)//3
    L.append(f"    · -- q = {q}")
    L.append(f"      have hpb : p ≤ {bound} := by omega")
    L.append(f"      interval_cases p")
    for p in range(1,bound+1):
        if gcd(p,q)!=1:
            L.append(f"      · exact absurd hcop (by decide)")
            continue
        L.append(f"      · -- p = {p}")
        L.append(f"        interval_cases r")
        for r in range(q+1,2*q):
            if r!=p+q:
                L.append(f"        · omega  -- r={r} non-diagonal, excluded by hdiag")
                continue
            # diagonal handler
            if p>=2 and r>=12:
                L.append(f"        · exact bhk_prop11_part6_ge12 w hpos hcover hsum hsmall hdiagw hw34 g {p} {q} {r} s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12")
            elif p==1 and q>=16:
                L.append(f"        · exact bhk_prop11_part6_p1 w hpos hcover hsum hdiagw hw24 g {q} s hg_pos (by norm_num) (by omega) hgq hgs  -- diag part6_p1")
            else:
                # try Pkill
                mP=next((m for m in range(2*q) if pkill_ok(p,q,r,Cpoint(r,q,m),Cpoint(p,q,m))),None)
                if mP is not None:
                    L.append(f"        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall hcover g {p} {q} {r} s {mP} hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- diag P")
                else:
                    nexp+=1
                    L.append(f"        · sorry  -- diag EXPLICIT (BHK 5.2.12.x): ({p},{q},{r})")
print("\n".join(L))
print(f"\n-- explicit sorries: {nexp}")
