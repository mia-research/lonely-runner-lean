"""Generate the 4 explicit 6-runner diagonal lemmas for core2_q_lt_18:
(1,7,8),(1,9,10),(1,10,11),(1,12,13). Emits Lean using bhk_diag_sbound2 (gap +
fictional band via bhk_away_band_v) and bhk_lonely6 (per surviving s)."""
from fractions import Fraction as F
def frac(x): return x - (x.numerator//x.denominator)
def Kf(n,theta):
    x=n*theta; k=x.numerator//x.denominator; return k, x-k

# per-case data: q, a(num,den as N/(D*g)), b, smax, (b-a)=BA, contradiction id num/den factor
CASES = {
 7:  dict(a=(7,36),  b=(11,48), smax=9,  ba=(5,144),  hid=("15 * s - 144","432 * g * s","15*s>=150>144 for s>=10","10")),
 9:  dict(a=(1,6),   b=(11,60), smax=20, ba=(1,60),   hid=("s - 20","60 * g * s","s-20>=1 for s>=21","21")),
 10: dict(a=(13,54), b=(17,66), smax=19, ba=(5,297),  hid=("15 * s - 297","891 * g * s","15*s>=300>297 for s>=20","20")),
 12: dict(a=(13,66), b=(17,78), smax=15, ba=(3,143),  hid=("9 * s - 143","429 * g * s","9*s>=144>143 for s>=16","16")),
}
def fr(t): return f"{t.numerator} / {t.denominator}" if t.denominator!=1 else f"{t.numerator}"
def fic(p,q): return 2*p  # speed of fictional = 2*w0 = 2*g (p=1)

out=[]
for q,d in CASES.items():
    p=1; r=p+q; n=[p,q-p,q,r]
    an,ad=d['a']; bn,bd=d['b']
    a=F(an,ad); b=F(bn,bd); ba=F(*d['ba']); smax=d['smax']
    w1=q-p
    # bands
    bands=[]
    for i,ni in enumerate(n):
        Ka,fa=Kf(ni,a); Kb,fb=Kf(ni,b)
        assert Ka==Kb
        bands.append((i,ni,Ka,fa,fb))
    # fictional band (speed 2)
    Kfa,ffa=Kf(2*p,a); Kfb,ffb=Kf(2*p,b); assert Kfa==Kfb
    # witnesses
    wits=[]
    for s in range(r+1,smax+1):
        ns=[p,q-p,q,r,s]; th=None
        for dd in range(2,80):
            for aa in range(1,dd):
                t=F(aa,dd)
                if all(frac(nn*t)>=F(1,6) and frac(nn*t)<=F(5,6) for nn in ns) and \
                   frac(2*p*t)>=F(1,6) and frac(2*p*t)<=F(5,6):
                    th=t; break
            if th: break
        assert th is not None,(q,s)
        Ks=[]; fs=[]
        for nn in ns:
            k,f=Kf(nn,th); Ks.append(k); fs.append(f)
        k2,f2=Kf(2*p,th)
        wits.append((s,th,Ks,fs,k2,f2))
    L=out
    L.append(f"set_option maxHeartbeats 1600000 in")
    L.append(f"/-- **core2 diagonal `(1,{q},{r})`** (explicit, six-runner). -/")
    L.append(f"lemma bhk_prop11_exc_diag2_1_{q} (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)")
    L.append(f"    (hcov6 : ∀ t : ℝ, (∃ i, circDist ((w i : ℝ) * t) < 1 / 6) ∨")
    L.append(f"        circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * t)) < 1 / 6)")
    L.append(f"    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)")
    L.append(f"    (g s : ℕ) (hg : 0 < g) (hs : {r} < s)")
    L.append(f"    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * {q})")
    L.append(f"    (hw3 : w ⟨3, by omega⟩ = g * {r}) (hw4 : w ⟨4, by omega⟩ = g * s) : False := by")
    L.append(f"  have hgR : (0 : ℝ) < g := by exact_mod_cast hg")
    L.append(f"  have hgne : (g : ℝ) ≠ 0 := hgR.ne'")
    L.append(f"  have hw1 : w ⟨1, by omega⟩ = g * {w1} := by omega")
    L.append(f"  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0")
    L.append(f"  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * {w1} := by exact_mod_cast hw1")
    L.append(f"  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * {q} := by exact_mod_cast hw2")
    L.append(f"  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * {r} := by exact_mod_cast hw3")
    L.append(f"  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4")
    L.append(f"  set a : ℝ := ({an} : ℝ) / ({ad} * (g : ℝ)) with ha")
    L.append(f"  set b : ℝ := ({bn} : ℝ) / ({bd} * (g : ℝ)) with hb")
    L.append(f"  have hab : a ≤ b := by")
    L.append(f"    rw [ha, hb, ← sub_nonneg]")
    L.append(f"    have hid : ({bn} : ℝ) / ({bd} * g) - {an} / ({ad} * g) = {ba.numerator} / ({ba.denominator} * g) := by field_simp <;> ring")
    L.append(f"    rw [hid]; positivity")
    cmap={0:'c0',1:'c1',2:'c2',3:'c3'}
    L.append(f"  have hbnd := bhk_diag_sbound2 w hpos hcov6 a b hab")
    for (i,ni,K,fa,fb) in bands:
        L.append(f"    (bhk_away_band w ⟨{i}, by omega⟩ a b hab {K} ({fr(fa)}) ({fr(fb)})")
        L.append(f"      (by rw [{cmap[i]}, ha]; push_cast; field_simp <;> ring)")
        L.append(f"      (by rw [{cmap[i]}, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))")
    # fictional band
    L.append(f"    (fun τ hτ => by")
    L.append(f"      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b hab {Kfa} ({fr(ffa)}) ({fr(ffb)})")
    L.append(f"        (by rw [c0, ha]; push_cast; field_simp <;> ring)")
    L.append(f"        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ")
    L.append(f"      rwa [mul_assoc] at h)")
    num,den,_,sthr=d['hid']
    L.append(f"  have hsb : s ≤ {smax} := by")
    L.append(f"    by_contra hcon")
    L.append(f"    have hsT : ({sthr} : ℝ) ≤ s := by exact_mod_cast (by omega : {sthr} ≤ s)")
    L.append(f"    have hsR : (0 : ℝ) < s := by linarith")
    L.append(f"    have hsne : (s : ℝ) ≠ 0 := hsR.ne'")
    L.append(f"    rw [c4] at hbnd")
    L.append(f"    have hba : b - a = {ba.numerator} / ({ba.denominator} * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring")
    L.append(f"    rw [hba] at hbnd")
    L.append(f"    have hid : ({ba.numerator} : ℝ) / ({ba.denominator} * g) - 1 / (3 * (g * s)) = ({num}) / ({den}) := by field_simp <;> ring")
    L.append(f"    have hd : (0 : ℝ) < {ba.numerator} / ({ba.denominator} * g) - 1 / (3 * (g * s)) := by")
    L.append(f"      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)")
    L.append(f"    linarith")
    L.append(f"  interval_cases s")
    for (s,th,Ks,fs,k2,f2) in wits:
        thn,thd=th.numerator,th.denominator
        fstr=" ".join(f"({fr(x)})" for x in fs)
        Kstr=" ".join(str(k) for k in Ks)
        es=[]
        for i in range(5):
            es.append(f"(by rw [{ ['c0','c1','c2','c3','c4'][i] }]; push_cast; field_simp <;> ring)")
        ems=" ".join(f"(by norm_num [Set.mem_Icc])" for _ in range(5))
        L.append(f"  · exact bhk_lonely6 w hcov6 ({thn} / ({thd} * (g : ℝ))) {fstr} {Kstr}")
        L.append(f"      {es[0]} {es[1]} {es[2]} {es[3]} {es[4]}")
        L.append(f"      {ems}")
        L.append(f"      ({fr(f2)}) {k2} (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])")
    L.append("")
print("\n".join(out))
