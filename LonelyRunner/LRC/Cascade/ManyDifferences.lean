import LonelyRunner.LRC.Cascade.FourDifferences

/-!
# `k` differences at every `n > 2k`

Part of the cascade artefact (`LRC/Cascade/`).  The cascade from the bound `1/(n·m)` stops whenever `2k < n`, `k` the
number of differences.

The argument is a potential.  For a runner `x` and an instant `t`, `lapsPassed n x t` counts the openings `(r + 1/n)/x`,
`r ≥ 1`, at or before `t`.  The potential `potential n ds t` multiplies, over the runners, the lap factors
`(r + 1/n)/(r − 1/n)` of the laps each has passed.

* `potential_step` — a move set by `x` at lap `Q` raises the potential by at least the factor of lap `Q`, because before
  the move `x` had passed at most `Q − 1` laps and after it `Q`.
* `time_le_potential` — the move itself multiplies the instant by less than that factor (`move_growth`), so
  `t_N · Ψ(t_0) ≤ t_0 · Ψ(t_N)` along the cascade.
* `lapProd_pow_le` — the product of the first `L` lap factors, raised to the `n`, is at most `C·(L + 1)²`
  (`lapFactor_pow_le`, from `bernoulli_upper`).
* `stops_when_twice_card_lt` — with `k` runners, `t_N^n ≤ B·t_N^{2k}`, so the instants are capped when `2k < n` and the
  cascade stops (`exists_fixed_of_capped`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ManyDifferences

open ConstructionN MomentIterationN TerminationFour ChainBounds FewDifferences FasterMoves

/-- The factor of lap `r`. -/
noncomputable def lapFactor (n r : ℕ) : ℝ := ((r : ℝ) + (n : ℝ)⁻¹) / ((r : ℝ) - (n : ℝ)⁻¹)

/-- The product of the factors of laps `1, …, L`. -/
noncomputable def lapProd (n L : ℕ) : ℝ := ∏ r ∈ Finset.range L, lapFactor n (r + 1)

/-- The number of laps `r ≥ 1` whose opening `(r + 1/n)/x` is at or before `t`. -/
noncomputable def lapsPassed (n : ℕ) (x t : ℝ) : ℕ := (⌊x * t - (n : ℝ)⁻¹⌋).toNat

/-- The potential: over the runners, the product of the factors of the laps each has passed. -/
noncomputable def potential (n : ℕ) (ds : Finset ℝ) (t : ℝ) : ℝ := ∏ x ∈ ds, lapProd n (lapsPassed n x t)

variable {n : ℕ} [Fact (2 ≤ n)]

theorem lapFactor_ge_one {r : ℕ} (hr : 1 ≤ r) : 1 ≤ lapFactor n r := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold lapFactor
  rw [le_div_iff₀ (by linarith)]; linarith

theorem lapProd_succ (L : ℕ) : lapProd n (L + 1) = lapProd n L * lapFactor n (L + 1) := by
  unfold lapProd; rw [Finset.prod_range_succ]

theorem lapProd_ge_one (L : ℕ) : 1 ≤ lapProd n L := by
  induction L with
  | zero => simp [lapProd]
  | succ L ih =>
    rw [lapProd_succ]
    have := lapFactor_ge_one (n := n) (Nat.succ_pos L)
    nlinarith

theorem lapProd_mono {L L' : ℕ} (h : L ≤ L') : lapProd n L ≤ lapProd n L' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rename_i m _
    rw [lapProd_succ]
    have h1 := lapFactor_ge_one (n := n) (Nat.succ_pos m)
    have h2 := lapProd_ge_one (n := n) m
    nlinarith

theorem lapsPassed_mono {x t t' : ℝ} (hx : 0 < x) (h : t ≤ t') : lapsPassed n x t ≤ lapsPassed n x t' := by
  unfold lapsPassed
  have : x * t - (n : ℝ)⁻¹ ≤ x * t' - (n : ℝ)⁻¹ := by nlinarith
  exact Int.toNat_le_toNat (Int.floor_mono this)

/-- Before a move set at lap `Q`, the setter has passed at most `Q − 1` laps. -/
theorem lapsPassed_before {x t : ℝ} {Q : ℤ} (hQ : 1 ≤ Q) (hk : |x * t - Q| < (n : ℝ)⁻¹) :
    lapsPassed n x t + 1 ≤ Q.toNat := by
  unfold lapsPassed
  have h1 : x * t - (n : ℝ)⁻¹ < Q := by have := (abs_lt.mp hk).2; linarith
  have h2 : ⌊x * t - (n : ℝ)⁻¹⌋ < Q := Int.floor_lt.mpr h1
  omega

/-- At its lap-`Q` opening, the setter has passed exactly `Q` laps. -/
theorem lapsPassed_at_opening {x : ℝ} (hx : 0 < x) {Q : ℤ} (hQ : 1 ≤ Q) :
    lapsPassed n x (((Q : ℝ) + (n : ℝ)⁻¹) / x) = Q.toNat := by
  unfold lapsPassed
  have e : x * (((Q : ℝ) + (n : ℝ)⁻¹) / x) - (n : ℝ)⁻¹ = (Q : ℝ) := by field_simp; ring
  rw [e, Int.floor_intCast]

theorem potential_ge_one (ds : Finset ℝ) (t : ℝ) : 1 ≤ potential n ds t := by
  unfold potential
  have : ∏ _x ∈ ds, (1 : ℝ) ≤ ∏ x ∈ ds, lapProd n (lapsPassed n x t) :=
    Finset.prod_le_prod (fun _ _ => zero_le_one) (fun x _ => lapProd_ge_one _)
  simpa using this

theorem potential_mono {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (h : t ≤ t') :
    potential n ds t ≤ potential n ds t' := by
  unfold potential
  exact Finset.prod_le_prod (fun x _ => le_trans zero_le_one (lapProd_ge_one _))
    (fun x hx => lapProd_mono (lapsPassed_mono (hpos x hx) h))

/-- **A move raises the potential by at least its lap factor.** -/
theorem potential_step {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {x t : ℝ} (hx : x ∈ ds) {Q : ℤ} (hQ : 1 ≤ Q)
    (hk : |x * t - Q| < (n : ℝ)⁻¹) (hle : t ≤ ((Q : ℝ) + (n : ℝ)⁻¹) / x) :
    lapFactor n Q.toNat * potential n ds t ≤ potential n ds (((Q : ℝ) + (n : ℝ)⁻¹) / x) := by
  classical
  have hx0 := hpos x hx
  set t' := ((Q : ℝ) + (n : ℝ)⁻¹) / x with ht'
  unfold potential
  rw [← Finset.mul_prod_erase ds _ hx, ← Finset.mul_prod_erase ds (fun y => lapProd n (lapsPassed n y t')) hx]
  have hrest : ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t) ≤ ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t') :=
    Finset.prod_le_prod (fun y _ => le_trans zero_le_one (lapProd_ge_one _))
      (fun y hy => lapProd_mono (lapsPassed_mono (hpos y (Finset.mem_of_mem_erase hy)) hle))
  have hrest0 : 0 ≤ ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t) :=
    Finset.prod_nonneg (fun y _ => le_trans zero_le_one (lapProd_ge_one _))
  have hq : 1 ≤ Q.toNat := by omega
  obtain ⟨p, hp⟩ : ∃ p, Q.toNat = p + 1 := ⟨Q.toNat - 1, by omega⟩
  have hbefore := lapsPassed_before (n := n) hQ hk
  have hsetter : lapFactor n Q.toNat * lapProd n (lapsPassed n x t) ≤ lapProd n (lapsPassed n x t') := by
    rw [ht', lapsPassed_at_opening hx0 hQ, hp, lapProd_succ]
    have hm : lapProd n (lapsPassed n x t) ≤ lapProd n p := lapProd_mono (by omega)
    have hf := lapFactor_ge_one (n := n) (Nat.succ_pos p)
    nlinarith [lapProd_ge_one (n := n) (lapsPassed n x t)]
  have hsetter0 : 0 ≤ lapProd n (lapsPassed n x t') := le_trans zero_le_one (lapProd_ge_one _)
  calc lapFactor n Q.toNat * (lapProd n (lapsPassed n x t) * ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t))
      = (lapFactor n Q.toNat * lapProd n (lapsPassed n x t)) * ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t) := by
        ring
    _ ≤ lapProd n (lapsPassed n x t') * ∏ y ∈ ds.erase x, lapProd n (lapsPassed n y t') :=
        mul_le_mul hsetter hrest hrest0 hsetter0

/-- **The instant grows no faster than the potential**, along the cascade from the bound. -/
theorem time_le_potential {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hmin : ∀ d ∈ ds, m ≤ d) (N : ℕ) :
    (move n ds)^[N] (1 / (n * m)) * potential n ds (1 / (n * m)) ≤
      1 / (n * m) * potential n ds ((move n ds)^[N] (1 / (n * m))) := by
  have hm0 := hpos m hm
  have hn0 : (0 : ℝ) < n := n_pos
  set b := 1 / (n * m) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hmb : m * b = (n : ℝ)⁻¹ := by rw [hb]; field_simp
  induction N with
  | zero => simp
  | succ N ih =>
    set tN := (move n ds)^[N] b with htN
    have htNb : b ≤ tN := iterate_ge ds b N
    have htN0 : 0 < tN := lt_of_lt_of_le hb0 htNb
    have hsucc : (move n ds)^[N + 1] b = move n ds tN := Function.iterate_succ_apply' _ _ _
    rw [hsucc]
    have hP0 : 0 ≤ potential n ds b := le_trans zero_le_one (potential_ge_one ds b)
    rcases step_cases (n := n) hpos tN with hfix | ⟨x, hx, k, hk, he⟩
    · rw [hfix]; exact ih
    · have hx0 := hpos x hx
      have hmt : (n : ℝ)⁻¹ ≤ m * tN := by rw [← hmb]; exact mul_le_mul_of_nonneg_left htNb hm0.le
      have hk1 : 1 ≤ k := lap_ge_one (hmin x hx) htN0.le hmt hk
      have hg := move_growth hx0 htN0 hk1 hk
      have hle : tN ≤ ((k : ℝ) + (n : ℝ)⁻¹) / x := by rw [← he]; exact le_move ds tN
      have hstep := potential_step (n := n) hpos hx hk1 hk hle
      have hF : lapFactor n k.toNat = ((k : ℝ) + (n : ℝ)⁻¹) / ((k : ℝ) - (n : ℝ)⁻¹) := by
        unfold lapFactor
        have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
          have h0 : (0 : ℤ) ≤ k := by omega
          exact_mod_cast Int.toNat_of_nonneg h0
        rw [this]
      rw [hF] at hstep
      set Fk := ((k : ℝ) + (n : ℝ)⁻¹) / ((k : ℝ) - (n : ℝ)⁻¹)
      rw [he]
      calc ((k : ℝ) + (n : ℝ)⁻¹) / x * potential n ds b ≤ Fk * tN * potential n ds b :=
            mul_le_mul_of_nonneg_right hg.le hP0
        _ = Fk * (tN * potential n ds b) := by ring
        _ ≤ Fk * (b * potential n ds tN) :=
            mul_le_mul_of_nonneg_left ih (le_trans zero_le_one (lapFactor_ge_one (n := n) (by omega) |>.trans_eq hF))
        _ = b * (Fk * potential n ds tN) := by ring
        _ ≤ b * potential n ds (((k : ℝ) + (n : ℝ)⁻¹) / x) := mul_le_mul_of_nonneg_left hstep hb0.le

/-- **One lap factor, raised to the `n`**: for `r ≥ 4`, `((r + 1/n)/(r − 1/n))^n ≤ ((r − 2)/(r − 3))²`. -/
theorem lapFactor_pow_le {r : ℕ} (hr : 4 ≤ r) :
    lapFactor n r ^ n ≤ (((r : ℝ) - 2) / ((r : ℝ) - 3)) ^ 2 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hn2 : (2 : ℝ) ≤ n := two_le_n
  have hr' : (4 : ℝ) ≤ r := by exact_mod_cast hr
  set A : ℝ := (n : ℝ) * r - 1 with hA
  have hA7 : 7 ≤ A := by nlinarith
  set y : ℝ := 2 / A with hy
  have hy0 : 0 ≤ y := by positivity
  have hF : lapFactor n r = 1 + y := by
    have hA0 : A ≠ 0 := by linarith
    have hden : (r : ℝ) - (n : ℝ)⁻¹ = A / n := by rw [hA]; field_simp
    have hnum : (r : ℝ) + (n : ℝ)⁻¹ = (A + 2) / n := by rw [hA]; field_simp; ring
    unfold lapFactor
    rw [hden, hnum, hy, div_div_div_cancel_right₀ hn0.ne', add_div, div_self hA0]
  have hny : (n : ℝ) * y < 1 := by
    rw [hy, mul_div_assoc', div_lt_one (by linarith)]; nlinarith
  have hb := bernoulli_upper hy0 n hny.le
  have hpos1 : 0 < 1 - (n : ℝ) * y := by linarith
  have h1 : (1 + y) ^ n ≤ 1 / (1 - (n : ℝ) * y) := by
    rw [le_div_iff₀ hpos1]; exact hb
  have hr3 : 0 < (r : ℝ) - 3 := by linarith
  have h2 : 1 / (1 - (n : ℝ) * y) ≤ (((r : ℝ) - 2) / ((r : ℝ) - 3)) ^ 2 := by
    have e : 1 - (n : ℝ) * y = (A - 2 * n) / A := by rw [hy]; field_simp
    have hA2n : 0 < A - 2 * n := by nlinarith
    rw [e, one_div_div, div_pow, div_le_div_iff₀ (by linarith) (by positivity)]
    have key : 0 ≤ (A - 2 * n) * ((r : ℝ) - 2) ^ 2 - A * ((r : ℝ) - 3) ^ 2 := by
      have e2 : (A - 2 * n) * ((r : ℝ) - 2) ^ 2 - A * ((r : ℝ) - 3) ^ 2 = (3 * n - 2) * r + 5 - 8 * n := by
        rw [hA]; ring
      rw [e2]; nlinarith
    nlinarith
  rw [hF]; exact h1.trans h2

/-- **The first `L` lap factors, raised to the `n`**, are at most `C·(L + 1)²` with `C = lapProd n 3 ^ n`. -/
theorem lapProd_pow_le (L : ℕ) : lapProd n L ^ n ≤ lapProd n 3 ^ n * ((L : ℝ) + 1) ^ 2 := by
  have hC : 1 ≤ lapProd n 3 ^ n := one_le_pow₀ (lapProd_ge_one 3)
  have hshift : ∀ j : ℕ, lapProd n (j + 3) ^ n ≤ lapProd n 3 ^ n * ((j : ℝ) + 1) ^ 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by ring, lapProd_succ, mul_pow]
      have hf := lapFactor_pow_le (n := n) (r := j + 3 + 1) (by omega)
      have e : (((j + 3 + 1 : ℕ) : ℝ) - 2) / (((j + 3 + 1 : ℕ) : ℝ) - 3) = ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
        push_cast; ring_nf
      rw [e] at hf
      have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hfac0 : 0 ≤ lapFactor n (j + 3 + 1) ^ n := pow_nonneg (le_trans zero_le_one (lapFactor_ge_one (by omega))) n
      calc lapProd n (j + 3) ^ n * lapFactor n (j + 3 + 1) ^ n
          ≤ (lapProd n 3 ^ n * ((j : ℝ) + 1) ^ 2) * (((j : ℝ) + 2) / ((j : ℝ) + 1)) ^ 2 :=
            mul_le_mul ih hf hfac0 (by positivity)
        _ = lapProd n 3 ^ n * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 := by
            push_cast; field_simp; ring
  by_cases hL : 3 ≤ L
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 3 := ⟨L - 3, by omega⟩
    refine (hshift j).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    push_cast
    nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  · have hle : lapProd n L ^ n ≤ lapProd n 3 ^ n :=
      pow_le_pow_left₀ (le_trans zero_le_one (lapProd_ge_one L)) (lapProd_mono (by omega)) n
    have : 1 ≤ ((L : ℝ) + 1) ^ 2 := one_le_pow₀ (by have := (L.cast_nonneg : (0 : ℝ) ≤ L); linarith)
    nlinarith

theorem lapsPassed_le {x t : ℝ} (hxt : 0 ≤ x * t) : (lapsPassed n x t : ℝ) ≤ x * t := by
  unfold lapsPassed
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr n_pos
  rcases le_or_gt 0 ⌊x * t - (n : ℝ)⁻¹⌋ with h | h
  · have e : ((⌊x * t - (n : ℝ)⁻¹⌋.toNat : ℕ) : ℝ) = (⌊x * t - (n : ℝ)⁻¹⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [e]; have := Int.floor_le (x * t - (n : ℝ)⁻¹); linarith
  · have : ⌊x * t - (n : ℝ)⁻¹⌋.toNat = 0 := by omega
    rw [this]; simpa using hxt

/-- **The potential is at most a power of the instant.** For `t ≥ t₀ > 0`,
`Ψ(t)^n ≤ C^k · (∏_x (x + 1/t₀))² · t^{2k}`. -/
theorem potential_pow_le {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    potential n ds t ^ n ≤
      (lapProd n 3 ^ n) ^ ds.card * (∏ x ∈ ds, (x + 1 / t₀)) ^ 2 * t ^ (2 * ds.card) := by
  have ht0 : 0 < t := lt_of_lt_of_le ht₀ ht
  unfold potential
  rw [← Finset.prod_pow]
  have hbound : ∀ x ∈ ds, lapProd n (lapsPassed n x t) ^ n ≤ lapProd n 3 ^ n * ((x + 1 / t₀) * t) ^ 2 := by
    intro x hx
    have hx0 := hpos x hx
    refine (lapProd_pow_le _).trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_trans zero_le_one (lapProd_ge_one 3)) n))
    have hl := lapsPassed_le (n := n) (mul_nonneg hx0.le ht0.le)
    have h1 : x * t + 1 ≤ (x + 1 / t₀) * t := by
      have : 1 ≤ t / t₀ := by rw [le_div_iff₀ ht₀]; linarith
      have e : (x + 1 / t₀) * t = x * t + t / t₀ := by field_simp
      linarith
    have h2 : 0 ≤ (lapsPassed n x t : ℝ) + 1 := by positivity
    exact pow_le_pow_left₀ h2 (by linarith) 2
  calc ∏ x ∈ ds, lapProd n (lapsPassed n x t) ^ n ≤ ∏ x ∈ ds, (lapProd n 3 ^ n * ((x + 1 / t₀) * t) ^ 2) :=
        Finset.prod_le_prod (fun x _ => pow_nonneg (le_trans zero_le_one (lapProd_ge_one _)) n) hbound
    _ = (lapProd n 3 ^ n) ^ ds.card * (∏ x ∈ ds, (x + 1 / t₀)) ^ 2 * t ^ (2 * ds.card) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, Finset.prod_mul_distrib,
          Finset.prod_const, mul_pow]
        ring

/-- **`k` differences at every `n > 2k`: the cascade from the bound stops.** -/
theorem stops_when_twice_card_lt {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hmin : ∀ d ∈ ds, m ≤ d) (hk : 2 * ds.card < n) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  have hm0 := hpos m hm
  have hn0 : (0 : ℝ) < n := n_pos
  set b := 1 / (n * m) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set B := b ^ n * ((lapProd n 3 ^ n) ^ ds.card * (∏ x ∈ ds, (x + 1 / b)) ^ 2) with hB
  refine exists_fixed_of_capped hpos hb0 (U := max 1 B) (fun N => ?_)
  set t := (move n ds)^[N] b with ht
  have htb : b ≤ t := iterate_ge ds b N
  have ht0 : 0 < t := lt_of_lt_of_le hb0 htb
  rcases le_or_gt t 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    -- `t ≤ b·Ψ(t)`
    have hinv := time_le_potential (n := n) hpos hm hmin N
    have hP0 := potential_ge_one (n := n) ds b
    have htP : t ≤ b * potential n ds t := by
      have : t ≤ t * potential n ds b := le_mul_of_one_le_right ht0.le hP0
      exact this.trans hinv
    have hpow : t ^ n ≤ b ^ n * potential n ds t ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ ht0.le htP n
    have hPp := potential_pow_le (n := n) hpos hb0 htb
    have hmain : t ^ n ≤ B * t ^ (2 * ds.card) := by
      calc t ^ n ≤ b ^ n * potential n ds t ^ n := hpow
        _ ≤ b ^ n * ((lapProd n 3 ^ n) ^ ds.card * (∏ x ∈ ds, (x + 1 / b)) ^ 2 * t ^ (2 * ds.card)) :=
            mul_le_mul_of_nonneg_left hPp (by positivity)
        _ = B * t ^ (2 * ds.card) := by rw [hB]; ring
    obtain ⟨e, he⟩ : ∃ e, n = 2 * ds.card + (e + 1) := ⟨n - 2 * ds.card - 1, by omega⟩
    rw [he, pow_add] at hmain
    have hk0 : 0 < t ^ (2 * ds.card) := by positivity
    have h2 : t ^ (e + 1) ≤ B := by
      have : t ^ (2 * ds.card) * t ^ (e + 1) ≤ t ^ (2 * ds.card) * B := by linarith
      exact le_of_mul_le_mul_left this hk0
    have h3 : t ≤ t ^ (e + 1) := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ (e + 1) := pow_le_pow_right₀ h1.le (by omega)
    exact h3.trans h2

/-- **Version B form.** With `k` differences and `2k < n`, some step of the cascade from the bound is lonely, and no
positive lonely instant precedes it. -/
theorem many_diffs {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hmin : ∀ d ∈ ds, m ≤ d) (hk : 2 * ds.card < n) :
    ∃ N : ℕ, Lonely n ds ((move n ds)^[N] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[N] (1 / (n * m)) ≤ s := by
  obtain ⟨N, hN⟩ := stops_when_twice_card_lt (n := n) hpos hm hmin hk
  exact ⟨N, first_isolation_of_fixed hpos hm N hN⟩

end ManyDifferences
