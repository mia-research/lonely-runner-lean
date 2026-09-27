"""Generate LonelyRunner/LRC/Spec/DoubledNbhdN.lean.  Every band is checked here in exact arithmetic against the
worst-case error the Lean proof uses, before emission."""
from fractions import Fraction as F
from math import floor, gcd
def band_N(lo, hi):
    N = floor(lo - F(1, 8))
    assert N + F(1, 8) <= lo and hi <= N + F(7, 8), (lo, hi)
    return N
def R(x): return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"
END = {1: (2, 0), 2: (7, 3), 3: (7, 2), 4: (5, 1), 5: (6, 1), 6: (7, 1)}   # cc -> (d, N0)
FARFL = {1: (0, 1), 2: (1, 1), 3: (2, 1), 4: (3, 1), 5: (1, 2), 6: (1, 3), 7: (6, 0)}
out = []
# ---------- end cases ----------
for s in (0, 7):
    for r in range(1, 7):
        cc = r if s == 0 else 7 - r
        d, N0 = END[cc]; P = 8 * N0 + 1; c0 = F(P, 8 * d)
        dd = d // gcd(P, d)                        # the partner reads a whole number of laps at c0 iff dd | m
        Kc = P // gcd(P, d)                        # shifted lap L = Kc * q  (m = dd * q)
        x0 = d if s == 0 else 7 - d
        DX = x0 - s                                 # +d or -d
        emax_u = F(1, 512)                          # unshifted: eta <= 1/512
        emax_s = F(1, 256 * (dd + 1))               # shifted: m >= dd
        dmax = F(1, 64 * dd)
        # unshifted AP readings
        lines_u = []; lines_s = []
        for j in range(8):
            if j in (s, r, x0): continue
            a = j - s
            err = c0 * (2 * emax_u + 2 * emax_u * 4)
            N = band_N(a * c0 - err, a * c0 + err)
            lines_u.append((j, a, N))
        for j in range(8):
            if j in (s, r): continue
            a = j - s
            err = (c0 + dmax) * (2 * emax_s + 2 * emax_s * 1)
            lo = min(a * c0, a * (c0 + dmax)) - err; hi = max(a * c0, a * (c0 + dmax)) + err
            N = band_N(lo, hi)
            lines_s.append((j, a, N))
        # partner, unshifted: circDist(c0 * 8m) >= 1/dd (dd >= 2), error <= c0 (2/512 + 16/(256 d))
        mu = F(1, dd) - F(1, 8)
        errp = c0 * (F(2, 512) + F(16, 256 * d))
        assert errp <= mu, (s, r)
        name = f"end_{s}_{r}"
        sfin = f"⟨{s}, by norm_num⟩"
        body = [f"""theorem {name} {{δ : Fin 8 → ℝ}} {{m : ℕ}} (hm : 1 ≤ m) {{η : ℝ}} (hη0 : 0 ≤ η)
    (hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1)
    (hδ : ∀ j, |δ j - ((dsZ {s} {r} m j - dsZ {s} {r} m {sfin} : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ {sfin} → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hη1 : η ≤ 1 / 512 := by nlinarith
  have hηm' : η * m ≤ 1 / 256 := by nlinarith
  have hD : ∀ j : Fin 8, ((dsZ {s} {r} m j - dsZ {s} {r} m {sfin} : ℤ) : ℝ)
      = if (j : ℕ) = {r} then 8 * (m : ℝ) + {s} - {s} else ((j : ℕ) : ℝ) - {s} := by
    intro j; unfold dsZ; split_ifs <;> push_cast <;> ring
  by_cases hdv : {dd} ∣ m
  · -- shifted: the partner's opening
    obtain ⟨q, rfl⟩ := hdv
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hmq : (({dd} * q : ℕ) : ℝ) = {dd} * (q : ℝ) := by push_cast; ring
    have hη2 : η ≤ {R(emax_s)} := by
      have : η * (256 * ((({dd} * q : ℕ) : ℝ) + 1)) ≤ 1 := hηm
      rw [hmq] at this; nlinarith
    set X : Fin 8 := ⟨{r}, by norm_num⟩
    have hDX : ((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ) = 8 * ({dd} * (q : ℝ)) := by
      rw [hD]; simp [X]; rw [hmq]; ring
    have hDX1 : 1 ≤ |((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ)| := by
      rw [hDX, abs_of_pos (by positivity)]; nlinarith
    have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
    set t0 : ℝ := (8 * ({Kc} * (q : ℝ)) + 1) / (64 * ({dd} * (q : ℝ))) with ht0def
    have ht0pos : 0 < t0 := by rw [ht0def]; positivity
    have ht0c : t0 = {R(c0)} + 1 / (64 * ({dd} * (q : ℝ))) := by rw [ht0def]; field_simp; ring
    have hδ' : 0 ≤ 1 / (64 * ({dd} * (q : ℝ))) ∧ 1 / (64 * ({dd} * (q : ℝ))) ≤ {R(dmax)} := by
      constructor
      · positivity
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have ht0η : t0 * η ≤ {R(c0 + dmax)} * {R(emax_s)} := by
      apply mul_le_mul (by rw [ht0c]; linarith [hδ'.2]) hη2 hη0 (by norm_num)
    refine ⟨t0 * ((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ) / δ X, ?_, ?_⟩
    · exact LRC.DoubledNbhd.pos_reloc ht0pos (by linarith) (hδ X) hDX1
    intro j hj
    fin_cases j
    · exact absurd rfl hj""" if s == 0 else f"""theorem {name} {{δ : Fin 8 → ℝ}} {{m : ℕ}} (hm : 1 ≤ m) {{η : ℝ}} (hη0 : 0 ≤ η)
    (hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1)
    (hδ : ∀ j, |δ j - ((dsZ {s} {r} m j - dsZ {s} {r} m {sfin} : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ {sfin} → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hη1 : η ≤ 1 / 512 := by nlinarith
  have hηm' : η * m ≤ 1 / 256 := by nlinarith
  have hD : ∀ j : Fin 8, ((dsZ {s} {r} m j - dsZ {s} {r} m {sfin} : ℤ) : ℝ)
      = if (j : ℕ) = {r} then 8 * (m : ℝ) + {s} - {s} else ((j : ℕ) : ℝ) - {s} := by
    intro j; unfold dsZ; split_ifs <;> push_cast <;> ring
  by_cases hdv : {dd} ∣ m
  · obtain ⟨q, rfl⟩ := hdv
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hmq : (({dd} * q : ℕ) : ℝ) = {dd} * (q : ℝ) := by push_cast; ring
    have hη2 : η ≤ {R(emax_s)} := by
      have : η * (256 * ((({dd} * q : ℕ) : ℝ) + 1)) ≤ 1 := hηm
      rw [hmq] at this; nlinarith
    set X : Fin 8 := ⟨{r}, by norm_num⟩
    have hDX : ((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ) = 8 * ({dd} * (q : ℝ)) := by
      rw [hD]; simp [X]; rw [hmq]; ring
    have hDX1 : 1 ≤ |((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ)| := by
      rw [hDX, abs_of_pos (by positivity)]; nlinarith
    have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
    set t0 : ℝ := (8 * ({Kc} * (q : ℝ)) + 1) / (64 * ({dd} * (q : ℝ))) with ht0def
    have ht0pos : 0 < t0 := by rw [ht0def]; positivity
    have ht0c : t0 = {R(c0)} + 1 / (64 * ({dd} * (q : ℝ))) := by rw [ht0def]; field_simp; ring
    have hδ' : 0 ≤ 1 / (64 * ({dd} * (q : ℝ))) ∧ 1 / (64 * ({dd} * (q : ℝ))) ≤ {R(dmax)} := by
      constructor
      · positivity
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have ht0η : t0 * η ≤ {R(c0 + dmax)} * {R(emax_s)} := by
      apply mul_le_mul (by rw [ht0c]; linarith [hδ'.2]) hη2 hη0 (by norm_num)
    refine ⟨t0 * ((dsZ {s} {r} ({dd} * q) X - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ) / δ X, ?_, ?_⟩
    · exact LRC.DoubledNbhd.pos_reloc ht0pos (by linarith) (hδ X) hDX1
    intro j hj
    fin_cases j"""]
        # shifted branch: per j in order 0..7
        for j in range(8):
            if j == s:
                if s == 7: body.append("    · exact absurd rfl hj")
                continue
            if j == r:
                body.append(f"""    · -- the partner, exactly on its opening
      refine LRC.DoubledNbhd.flank_exact (L := (({Kc} * q : ℕ) : ℤ)) hδX0 (Or.inl ?_)
      rw [hDX, ht0def]; push_cast; field_simp; ring""")
                continue
            a = j - s; N = [x for x in lines_s if x[0] == j][0][2]
            body.append(f"""    · have hj' := hδ ⟨{j}, by norm_num⟩
      have hDj : ((dsZ {s} {r} ({dd} * q) ⟨{j}, by norm_num⟩ - dsZ {s} {r} ({dd} * q) {sfin} : ℤ) : ℝ) = {a} := by
        rw [hD]; norm_num
      apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 1) ht0pos.le hη0 (by linarith) (hδ X) hDX1 hj'
        (by norm_num)
      · rw [hDj, hDX, abs_of_pos (show (0 : ℝ) < 8 * ({dd} * (q : ℝ)) by positivity)]; norm_num; nlinarith
      · rw [hDj, ht0c]; nlinarith [hδ'.1, hδ'.2, ht0η]
      · rw [hDj, ht0c]; nlinarith [hδ'.1, hδ'.2, ht0η]""")
        # unshifted branch
        xfin = f"⟨{x0}, by norm_num⟩"
        body.append(f"""  · -- the far end of the progression, at lap {N0}
    set X : Fin 8 := {xfin}
    have hDX : ((dsZ {s} {r} m X - dsZ {s} {r} m {sfin} : ℤ) : ℝ) = {DX} := by rw [hD]; norm_num [X]
    have hDX1 : 1 ≤ |((dsZ {s} {r} m X - dsZ {s} {r} m {sfin} : ℤ) : ℝ)| := by rw [hDX]; norm_num
    have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
    set t0 : ℝ := {R(c0)} with ht0def
    refine ⟨t0 * ((dsZ {s} {r} m X - dsZ {s} {r} m {sfin} : ℤ) : ℝ) / δ X, ?_, ?_⟩
    · exact LRC.DoubledNbhd.pos_reloc (by norm_num) (by linarith) (hδ X) hDX1
    intro j hj
    fin_cases j""")
        for j in range(8):
            if j == s:
                body.append("    · exact absurd rfl hj"); continue
            if j == x0:
                sign = "Or.inl" if DX > 0 else "Or.inr"
                body.append(f"""    · refine LRC.DoubledNbhd.flank_exact (L := {N0}) hδX0 ({sign} ?_)
      rw [hDX, ht0def]; norm_num""")
                continue
            if j == r:
                body.append(f"""    · -- the partner: a fraction of denominator {dd} at t0, moved at most {errp}
      have hj' := hδ ⟨{r}, by norm_num⟩
      have hDj : ((dsZ {s} {r} m ⟨{r}, by norm_num⟩ - dsZ {s} {r} m {sfin} : ℤ) : ℝ) = 8 * (m : ℝ) := by
        rw [hD]; norm_num
      exact LRC.DoubledNbhd.partner_lip (dd := {dd}) (P := {P}) (d := {d}) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hdv hm hη0 hη1 hηm' hDX hDX1 (hδ X) hj' hDj""")
                continue
            a = j - s; N = [x for x in lines_u if x[0] == j][0][2]
            body.append(f"""    · have hj' := hδ ⟨{j}, by norm_num⟩
      have hDj : ((dsZ {s} {r} m ⟨{j}, by norm_num⟩ - dsZ {s} {r} m {sfin} : ℤ) : ℝ) = {a} := by rw [hD]; norm_num
      apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 4) (by norm_num) hη0 (by linarith) (hδ X) hDX1 hj'
        (by norm_num)
      · rw [hDj, hDX]; norm_num
      · rw [hDj, ht0def]; linarith
      · rw [hDj, ht0def]; linarith""")
        out.append("\n".join(body) + "\n")
# ---------- far exceptions: s = 0, m = 1 ----------
for r, (j0, L) in FARFL.items():
    DX = j0 - 8; t0 = F(8 * L + 1, 8 * abs(DX))
    name = f"farx_{r}"; rfin = f"⟨{r}, by norm_num⟩"
    body = [f"""theorem {name} {{δ : Fin 8 → ℝ}} {{η : ℝ}} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 512)
    (hδ : ∀ j, |δ j - ((dsZ 0 {r} 1 j - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ {rfin} → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  have hD : ∀ j : Fin 8, ((dsZ 0 {r} 1 j - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ)
      = if (j : ℕ) = {r} then 0 else ((j : ℕ) : ℝ) - 8 := by
    intro j; unfold dsZ; split_ifs <;> push_cast <;> simp_all
  set X : Fin 8 := ⟨{j0}, by norm_num⟩
  have hDX : ((dsZ 0 {r} 1 X - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ) = {DX} := by rw [hD]; norm_num [X]
  have hDX1 : 1 ≤ |((dsZ 0 {r} 1 X - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ)| := by rw [hDX]; norm_num
  have hδX0 := LRC.DoubledNbhd.nz_of (by linarith) (hδ X) hDX1
  set t0 : ℝ := {R(t0)} with ht0def
  refine ⟨t0 * ((dsZ 0 {r} 1 X - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ) / δ X, ?_, ?_⟩
  · exact LRC.DoubledNbhd.pos_reloc (by norm_num) (by linarith) (hδ X) hDX1
  intro j hj
  fin_cases j"""]
    for j in range(8):
        if j == r:
            body.append("  · exact absurd rfl hj"); continue
        if j == j0:
            body.append(f"""  · refine LRC.DoubledNbhd.flank_exact (L := {L}) hδX0 (Or.inr ?_)
    rw [hDX, ht0def]; norm_num"""); continue
        a = j - 8; err = t0 * (2 * F(1, 512) + 2 * F(1, 512) * 8)
        N = band_N(a * t0 - err, a * t0 + err)
        body.append(f"""  · have hj' := hδ ⟨{j}, by norm_num⟩
    have hDj : ((dsZ 0 {r} 1 ⟨{j}, by norm_num⟩ - dsZ 0 {r} 1 {rfin} : ℤ) : ℝ) = {a} := by rw [hD]; norm_num
    apply LRC.DoubledNbhd.reloc_clear (N := {N}) (K := 8) (by norm_num) hη0 (by linarith) (hδ X) hDX1 hj'
      (by norm_num)
    · rw [hDj, hDX]; norm_num
    · rw [hDj, ht0def]; linarith
    · rw [hDj, ht0def]; linarith""")
    out.append("\n".join(body) + "\n")
open("gen_doubled_nbhd_cases.lean.txt", "w").write("\n".join(out))
print(len(out), "generated case lemmas; all bands checked")
