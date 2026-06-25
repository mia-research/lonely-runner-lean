"""Generate the 9 third-slope read-off lemmas (5 clean q>=30, 4 half-window q>=36)
for (2,3),(2,-3),(4,3),(4,-3). Templated on exc_5_3_c2 (incr) / exc_5_neg3_c4 (decr).
Params per lemma: iota,gamma,rho,kappa,e,betaN,sh ; A-window [Alo,Ahi] ; q-threshold."""
from fractions import Fraction as F

def fr(x):  # Lean fraction literal
    x = F(x)
    return f"{x.numerator}" if x.denominator == 1 else f"{x.numerator} / {x.denominator}"

def lit(n):  # signed int literal with parens if negative
    return f"({n})" if n < 0 else f"{n}"

# name, iota, gamma, rho, kappa, e, betaN, sh, Alo, Ahi, thr(30/36)
SPECS = [
    # clean (q>=30), A in [1/6,3/10]
    ("2_3_c3",    2, 3, 1, -3, -1, 1, 1, F(1,6), F(3,10), 30),
    ("2_neg3_c5",-2, 5, 2, -2,  3, 3,-1, F(1,6), F(3,10), 30),
    ("4_3_c2",    4, 2, 2, -2, -2, 0, 3, F(1,6), F(3,10), 30),
    ("4_3_c4",    4, 4, 1, -1,  0, 0, 2, F(1,6), F(3,10), 30),
    ("4_neg3_c4",-4, 4, 0, -2,  4, 4, 0, F(1,6), F(3,10), 30),
    # half (q>=36): incr -> A in [1/6,1/4], decr -> A in [1/4,1/3]
    ("2_3_c4_hi",  2, 4, 1, -2,  0, 2, 1, F(1,6), F(1,4), 36),
    ("2_neg3_c4_hi",-2,4, 0, -1,  2, 4, 0, F(1,4), F(1,3), 36),
    ("4_3_c3_hi",  4, 3, 2, -3, -3, 1, 3, F(1,6), F(1,4), 36),
    ("4_neg3_c5_hi",-4,5, 0, -1,  3, 5, 0, F(1,4), F(1,3), 36),
]

def gen(name, iota, gamma, rho, kappa, e, betaN, sh, Alo, Ahi, thr):
    assert iota*kappa+gamma == 3*e, name
    assert 2*iota*rho+gamma == 6*sh+betaN, name
    mult = -kappa                       # 3w' = p + mult*q
    coeff = -kappa                      # 3G = pt + coeff*l
    glo = (Alo + rho) / 3
    wlen = (Ahi - Alo) / 3
    ghi = glo + wlen
    assert wlen >= F(1, thr), (name, wlen, thr)
    incr = iota > 0
    # relation
    if iota > 0:
        rel = f"3 * r = {iota} * p + {gamma} * q"
        relR = (f"    have h : (3 : ℝ) * r = {iota} * p + {gamma} * q := by exact_mod_cast hr3\n"
                f"    push_cast; linarith")
    else:
        rel = f"3 * r + {-iota} * p = {gamma} * q"
        relR = (f"    have h : (3 : ℝ) * r + {-iota} * p = {gamma} * q := by exact_mod_cast hr3\n"
                f"    push_cast; linarith")
    qthr = f"hq{thr} : {thr} ≤ q"
    # grid window feasibility proof
    if thr == 30:
        feas = (f"(by have h30 : (30 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq30\n"
                f"        exact le_trans (one_div_le_one_div_of_le (by norm_num) h30) (by norm_num))")
    else:
        feas = (f"(by have h36 : (36 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq36\n"
                f"        exact one_div_le_one_div_of_le (by norm_num) h36)")
    # A-membership args
    Amem_lo = "hA0" if Alo == F(1,6) else "by linarith [hA0]"
    Amem_hi = "hA1" if Ahi == F(1,3) else "by linarith [hA1]"
    # X-bound linarith hints
    xlo_hint, xhi_hint = ("hA0", "hA1") if incr else ("hA1", "hA0")
    L = []
    L.append(f"/-- **`{name}` third-slope read-off.** `X = ({iota}/3)A + {fr(F(betaN,6))}`, "
             f"`A ∈ [{fr(Alo)},{fr(Ahi)}]`. -/")
    L.append(f"lemma bhk_prop11_exc_{name} (p q r : ℕ) ({qthr}) (hcop : Nat.Coprime p q)")
    L.append(f"    (hp : 0 < p) (h3p : 3 * p < q) (hr3 : {rel})")
    L.append(f"    (h_nogood : ∀ l : ℤ,")
    L.append(f"      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧")
    L.append(f"         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) :")
    L.append(f"    False := by")
    L.append(f"  have hq0 : 0 < q := by omega")
    L.append(f"  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0")
    L.append(f"  have hrR : (3 : ℝ) * r = (({iota} : ℤ) : ℝ) * p + (({gamma} : ℤ) : ℝ) * q := by")
    L.append(relR)
    L.append(f"  set w' : ℕ := (p + {mult} * q) / 3 with hw'def")
    L.append(f"  have h4w : p + {mult} * q = 3 * w' := by omega")
    L.append(f"  have hcopw : Nat.Coprime w' q := by")
    L.append(f"    have h2 : Nat.gcd w' q ∣ q := Nat.gcd_dvd_right _ _")
    L.append(f"    have hd : Nat.gcd w' q ∣ p := by")
    L.append(f"      have hb : Nat.gcd w' q ∣ {mult} * q := h2.mul_left {mult}")
    L.append(f"      have ha : Nat.gcd w' q ∣ {mult} * q + p := by")
    L.append(f"        rw [show {mult} * q + p = 3 * w' from by omega]; exact (Nat.gcd_dvd_left _ _).mul_left 3")
    L.append(f"      exact (Nat.dvd_add_right hb).mp ha")
    L.append(f"    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd h2)")
    L.append(f"  obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq0 w' hcopw")
    L.append(f"    ((p : ℝ) / (6 * q)) ({fr(glo)}) ({fr(wlen)})")
    L.append(f"    {feas} (by norm_num) (by norm_num)")
    L.append(f"  set G : ℝ := (p : ℝ) / (6 * q) + (l : ℝ) * (w' : ℝ) / (q : ℝ) with hGdef")
    L.append(f"  rw [Set.mem_Icc] at hl")
    L.append(f"  have hGfr0 : {fr(glo)} ≤ Int.fract G := hl.1")
    L.append(f"  have hGfr1 : Int.fract G ≤ {fr(ghi)} := by linarith [hl.2]")
    L.append(f"  have hw3R : 3 * (w' : ℝ) = (p : ℝ) + {mult} * q := by exact_mod_cast h4w.symm")
    L.append(f"  have h3G : 3 * G = (p : ℝ) / q * ((l : ℝ) + 1 / 2) + {coeff} * (l : ℝ) := by")
    L.append(f"    rw [hGdef, show (w' : ℝ) = ((p : ℝ) + {mult} * q) / 3 from by linarith [hw3R]]; field_simp; ring")
    L.append(f"  obtain ⟨hfl, hfr⟩ := bhk_prop11_third_window G {rho}")
    L.append(f"    (by push_cast; linarith [hGfr0]) (by push_cast; linarith [hGfr1])")
    L.append(f"  have hflr : ⌊3 * G⌋ = ⌊(p : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ + {coeff} * l := by")
    L.append(f"    rw [h3G, show (p : ℝ) / q * ((l : ℝ) + 1 / 2) + {coeff} * (l : ℝ)")
    L.append(f"      = (p : ℝ) / q * ((l : ℝ) + 1 / 2) + (({coeff} * l : ℤ) : ℝ) from by push_cast; ring, Int.floor_add_intCast]")
    L.append(f"  have hD : ⌊(p : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ = 3 * ⌊G⌋ + {rho} + {lit(kappa)} * l := by omega")
    L.append(f"  have hAval : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) = 3 * Int.fract G - {rho} := by")
    L.append(f"    have heq : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) = Int.fract (3 * G) := by")
    L.append(f"      rw [h3G, show (p : ℝ) / q * ((l : ℝ) + 1 / 2) + {coeff} * (l : ℝ)")
    L.append(f"        = (p : ℝ) / q * ((l : ℝ) + 1 / 2) + (({coeff} * l : ℤ) : ℝ) from by push_cast; ring, Int.fract_add_intCast]")
    L.append(f"    rw [heq, hfr]; push_cast; ring")
    L.append(f"  have hA0 : {fr(Alo)} ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) := by rw [hAval]; linarith [hGfr0]")
    L.append(f"  have hA1 : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ {fr(Ahi)} := by rw [hAval]; linarith [hGfr1]")
    L.append(f"  have hX := bhk_prop11_readoff_third_gen p q r {lit(iota)} {gamma} {rho} {lit(kappa)} {lit(e)} {betaN} {lit(sh)} l ⌊G⌋ hq0 hrR")
    L.append(f"    (by norm_num) (by norm_num) hD (by push_cast; linarith [hA0, hA1]) (by push_cast; linarith [hA0, hA1])")
    L.append(f"  refine h_nogood l ⟨Set.mem_Icc.mpr ⟨?_, ?_⟩, Set.mem_Icc.mpr ⟨{Amem_lo}, {Amem_hi}⟩⟩")
    L.append(f"  · rw [hX]; push_cast; linarith [{xlo_hint}]")
    L.append(f"  · rw [hX]; push_cast; linarith [{xhi_hint}]")
    return "\n".join(L)

print("\n\n".join(gen(*s) for s in SPECS))
