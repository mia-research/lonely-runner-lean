"""Generate the full core2_q_lt_18 finite dispatch (both branches).
Space: p in {1,2}, q in [7,17], gcd(p,q)=1, 6p<q, q<r<2q.
Non-diagonal: exc_Rkill (abstract) / exc_Pkill2 (windowed pentagon + (43) cut) /
exc_v4kill2. Diagonal r=p+q: exc_diag2_1_{7,9,10,12} / part6_p1_wit_w (grid) /
part6_ge12_w (p>=2) / exc_Pkill2 (1,8,9)."""
from math import gcd, floor
from fractions import Fraction as F
def Cpoint(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
def runner1_positions(p,q):
    return [F(i,q) for i in range(q)] if p%2==0 else [F(2*i+1,2*q) for i in range(q)]
def rho_and_Rmax(p,q):
    x1=F(q,p); x2=F(q,q-p); best=None
    for v in runner1_positions(p,q):
        if F(1,6)<v<F(1,3):
            rho=min((v-F(1,6))*x1,(F(1,3)-v)*x2); I=F(1,3)+rho
            if best is None or I>best: best=I; bestrho=rho; bestv=v
    if best is None: return None,2*q-1,None
    rb=F(q)*(2/(3*best)); rm=floor(rb)
    if F(rm)==rb: rm-=1
    return bestrho,rm,bestv
def pkill2_ok(p,q,r,X,Y):
    corr=F(r+1-q,3*q*(r+1))
    return (F(1,6)-r*corr<=X and F(1,6)-p*corr<=Y and Y<=F(1,3)+(q-p)*corr
            and X<=F(5,6) and F(1,3*(r+1))<=(F(5,6)-X)/r+(Y-F(1,6))/p
            and F(1,3*(r+1))<=(F(5,6)-X)/r+(F(1,3)-Y)/(q-p)
            and Y<=F(5,12)-F(p,3*q))
def find_m_for_v(p,q,v):
    for m in range(2*q):
        if Cpoint(p,q,m)==v: return m
    return None

# diagonal routing
DIAG_EXPLICIT={7,9,10,12}   # exc_diag2_1_{q}
DIAG_PKILL={8:1}            # (1,8,9) exc_Pkill2 m=1
DIAG_P1WIT={11:4,13:5,14:5,15:6,16:6,17:6}  # part6_p1_wit_w grid m

def nondiag_leaf(p,q,r):
    if (p,q,r)==(1,9,11):
        return ("exact bhk_prop11_exc_special_1_9_11 w hpos hcov6 hsum g s hg_pos (by omega) "
                "(by omega) hgq hgr hgs  -- special (43-cut fallthrough)")
    mR=next((m for m in range(2*q) if in_R(Cpoint(r,q,m),Cpoint(p,q,m))),None)
    if mR is not None:
        return (f"exact bhk_prop11_exc_Rkill {p} {q} {r} {mR} (by norm_num) h_nogood "
                f"(by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R")
    mP=next((m for m in range(2*q) if pkill2_ok(p,q,r,Cpoint(r,q,m),Cpoint(p,q,m))),None)
    if mP is not None:
        return (f"exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 hcov6 g {p} {q} {r} s {mP} "
                f"hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 "
                f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) "
                f"(by norm_num) (by norm_num)  -- P")
    rho,rmax,bv=rho_and_Rmax(p,q)
    assert rho is not None and r>rmax and 2*q<=(1+3*rho)*r, f"v4 fail {(p,q,r)} rmax={rmax}"
    mv=find_m_for_v(p,q,bv)
    return (f"exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 hcov6 g {p} {q} {r} {mv} "
            f"({rho.numerator}/{rho.denominator} : ℝ) hg_pos (by norm_num) c0 c2 c3 "
            f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4")

def diag_leaf(p,q,r):
    if p==1 and q in DIAG_EXPLICIT:
        return [f"exact bhk_prop11_exc_diag2_1_{q} w hpos hcov6 hsum g s hg_pos (by omega) "
                f"(by omega) hgq hgr hgs  -- explicit"]
    if p==1 and q in DIAG_PKILL:
        m=DIAG_PKILL[q]
        return [f"exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 hcov6 g 1 {q} {r} s {m} "
                f"hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 "
                f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) "
                f"(by norm_num) (by norm_num)  -- diag P"]
    if p==1 and q in DIAG_P1WIT:
        m=DIAG_P1WIT[q]
        return [f"refine bhk_prop11_part6_p1_wit_w w hpos hcov6 hsum hdiagw hw24 g {q} s hg_pos "
                f"(by norm_num) (by omega) hgq hgs (({m} : ℝ) / (w ⟨2, by omega⟩ : ℝ)) {m} ?_ ?_ ?_",
                f"· have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity",
                f"  field_simp; norm_num",
                f"· have hwt : (w ⟨0, by omega⟩ : ℝ) * (({m} : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = ({m} : ℝ) / {q} := by",
                f"    rw [c0, c2]; field_simp; ring",
                f"  rw [hwt]; norm_num",
                f"· have hwt : (w ⟨0, by omega⟩ : ℝ) * (({m} : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = ({m} : ℝ) / {q} := by",
                f"    rw [c0, c2]; field_simp; ring",
                f"  rw [hwt]; norm_num"]
    # p>=2, r>=12
    return [f"exact bhk_prop11_part6_ge12_w w hpos hcov6 hsum hsmall hsmall6 hdiagw hw34 g {p} {q} "
            f"{r} s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- part6_ge12_w"]

def emit_tree(diagonal):
    L=[]
    L.append("    interval_cases q")
    for q in range(7,18):
        bound=(q-1)//6
        L.append(f"    · -- q = {q}")
        L.append(f"      have hpb : p ≤ {bound} := by omega")
        L.append(f"      interval_cases p")
        for p in range(1,bound+1):
            if gcd(p,q)!=1:
                L.append(f"      · exact absurd hcop (by decide)  -- p={p} gcd>1")
                continue
            L.append(f"      · -- p = {p}")
            L.append(f"        interval_cases r")
            for r in range(q+1,2*q):
                isdiag = (r==p+q)
                if diagonal:
                    if isdiag:
                        body=diag_leaf(p,q,r)
                        L.append("        · "+body[0])
                        for ln in body[1:]:
                            L.append("          "+ln)
                    else:
                        L.append(f"        · omega  -- r={r} non-diag")
                else:
                    if isdiag:
                        L.append(f"        · omega  -- r={r}=p+q diagonal")
                    else:
                        L.append("        · "+nondiag_leaf(p,q,r))
    return L

out=[]
out.append("  by_cases hdiag : r = p + q")
out.append("  · -- DIAGONAL")
out.append("    have hdiagw : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩ := by")
out.append("      rw [hgr, hgp, hgq, hdiag]; ring")
out.append("    have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by")
out.append("      exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))")
out.append("    have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by")
out.append("      have h23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by")
out.append("        exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))")
out.append("      linarith")
out.append("    have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg_pos.ne'")
out += emit_tree(diagonal=True)
out.append("  · -- NON-DIAGONAL")
out += emit_tree(diagonal=False)
print("\n".join(out))
