from math import gcd, floor
from fractions import Fraction as F
def fract(num,den): return F(num%den,den)
def Cpoint(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def runner1_positions(p,q):
    return [F(i,q) for i in range(q)] if p%2==0 else [F(2*i+1,2*q) for i in range(q)]
def rho_and_Rmax(p,q):
    x1=F(q,p); x2=F(q,q-p); best=None; bestv=None
    for v in runner1_positions(p,q):
        if F(1,6)<v<F(1,3):
            rho=min((v-F(1,6))*x1,(F(1,3)-v)*x2); I=F(1,3)+rho
            if best is None or I>best: best=I; bestv=v; bestrho=rho
    if best is None: return None,2*q-1
    rb=F(q)*(2/(3*best)); rm=floor(rb)
    if F(rm)==rb: rm-=1
    return bestrho,rm
def pkill_ok(p,q,r,X,Y):
    s0=r+1; corr=F(s0-q,3*q*s0)
    return (X>=F(1,6)-r*corr and Y>=F(1,6)-p*corr and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*s0)<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*s0)<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p))
def find_m_for_v(p,q,vtarget):
    for m in range(2*q):
        if Cpoint(p,q,m)==vtarget: return m
    return None

L=[]
ind="      "
for q in range(5,18):
    bound=(q-1)//3
    L.append(f"    · -- q = {q}")
    L.append(f"      have hpb : p ≤ {bound} := by omega")
    L.append(f"      interval_cases p")
    for p in range(1,bound+1):
        if gcd(p,q)!=1:
            L.append(f"      · exact absurd hcop (by decide)  -- p={p}, gcd>1")
            continue
        rho,rmax=rho_and_Rmax(p,q)
        L.append(f"      · -- p = {p}")
        L.append(f"        interval_cases r")
        for r in range(q+1,2*q):
            if r==p+q:
                L.append(f"        · omega  -- r={r}=p+q diagonal")
                continue
            # classify
            pts=[(m,Cpoint(r,q,m),Cpoint(p,q,m)) for m in range(2*q)]
            mR=next((m for (m,X,Y) in pts if in_R(X,Y)),None)
            if mR is not None:
                L.append(f"        · exact bhk_prop11_exc_Rkill {p} {q} {r} {mR} (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r={r} R")
                continue
            mP=next((m for (m,X,Y) in pts if pkill_ok(p,q,r,X,Y)),None)
            if mP is not None:
                L.append(f"        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall hcover g {p} {q} {r} s {mP} hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r={r} P")
                continue
            # v4 exclusion: need r>rmax and hrb: 2q<=(1+3rho)r
            assert rho is not None and r>rmax, f"unexpected {p,q,r} rmax={rmax}"
            assert 2*q <= (1+3*rho)*r, f"hrb fails {p,q,r} rho={rho}"
            mv=find_m_for_v(p,q, [v for v in runner1_positions(p,q) if F(1,6)<v<F(1,3) and min((v-F(1,6))*F(q,p),(F(1,3)-v)*F(q,q-p))==rho][0])
            L.append(f"        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall hcover g {p} {q} {r} {mv} ({rho.numerator}/{rho.denominator} : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r={r} v4 excl")
print("\n".join(L))
print(f"\n-- lines: {len(L)}")
