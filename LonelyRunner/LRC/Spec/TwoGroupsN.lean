import LonelyRunner.LRC.Spec.OrderFiveResidualN
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Order five, real speeds: two incommensurable groups

2026-09-24.  Let the disparities split into two groups, `u·A` and `w·B`, each a set of whole
multiples of its own unit, with `u/w` irrational, and each group of at most three.

* **Each group alone.**  At most three disparities are lonely at `1/4` (order four, inside the
  framework).  At `1/5` that leaves a margin: group `A` stays clear on `[τ_A − δ, τ_A + δ]`,
  `δ = 1/(20·max A)`, and the whole picture repeats with period `1/u`.  Group `B` is lonely at
  `τ_B + l/w` for every `l`.
* **Lining the two up.**  We need `l` with `τ_B + l/w` inside a repeat of group `A`'s cell, that
  is `(τ_B − τ_A)·u + l·(u/w)` within `δ·u` of an integer.  A pigeonhole (Dirichlet) gives
  `k₀` with `s = k₀·(u/w) − j` of size at most `δ·u`; `s ≠ 0` exactly because `u/w` is irrational.
  Stepping by `s` from `(τ_B − τ_A)·u` reaches within `|s|` of an integer (`exists_step_near_int`).

No density or equidistribution is used: one pigeonhole for a small step, then stepping.  This is
R7's mechanism — an off-lattice step cannot be blocked forever — made quantitative.  The
class structures `3 + 1` and `2 + 2` at order five are both instances.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN ConstructionN

/-- **Stepping to an integer.**  Steps of a nonzero size `s` with `|s| ≤ ε` from `c` come within
`ε` of an integer. -/
theorem exists_step_near_int (c s ε : ℝ) (hs : s ≠ 0) (hsε : |s| ≤ ε) :
    ∃ i : ℕ, ∃ K : ℤ, |c + i * s - K| ≤ ε := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hms : 0 < -s := by linarith
    set x := (c - ⌊c⌋) / (-s) with hx
    have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr (Int.floor_le c)) hms.le
    refine ⟨⌊x⌋₊, ⌊c⌋, ?_⟩
    have e1 : (⌊x⌋₊ : ℝ) * (-s) ≤ c - ⌊c⌋ := by
      have := Nat.floor_le hx0; rwa [hx, le_div_iff₀ hms] at this
    have e2 : c - ⌊c⌋ < ((⌊x⌋₊ : ℝ) + 1) * (-s) := by
      have := Nat.lt_floor_add_one x; rwa [hx, div_lt_iff₀ hms] at this
    have hab : |s| = -s := abs_of_neg hneg
    rw [abs_le]; constructor <;> nlinarith
  · set x := (⌈c⌉ - c) / s with hx
    have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr (Int.le_ceil c)) hpos.le
    refine ⟨⌊x⌋₊, ⌈c⌉, ?_⟩
    have e1 : (⌊x⌋₊ : ℝ) * s ≤ ⌈c⌉ - c := by
      have := Nat.floor_le hx0; rwa [hx, le_div_iff₀ hpos] at this
    have e2 : ⌈c⌉ - c < ((⌊x⌋₊ : ℝ) + 1) * s := by
      have := Nat.lt_floor_add_one x; rwa [hx, div_lt_iff₀ hpos] at this
    have hab : |s| = s := abs_of_pos hpos
    rw [abs_le]; constructor <;> nlinarith

/-- **Two incommensurable groups at order five.**  If the disparities are `u·A` and `w·B` with
`u/w` irrational and each group of at most three, the set is lonely at `1/5`. -/
theorem lonely_five_two_groups {A B : Finset ℕ} {u w : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hirr : Irrational (u / w)) (hA : ∀ m ∈ A, 0 < m) (hB : ∀ m ∈ B, 0 < m)
    (hcA : A.card ≤ 3) (hcB : B.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ (∀ m ∈ A, (5 : ℝ)⁻¹ ≤ circDist (u * m * t)) ∧
      ∀ m ∈ B, (5 : ℝ)⁻¹ ≤ circDist (w * m * t) := by
  classical
  -- each group alone, at the threshold of order four
  have group : ∀ (G : Finset ℕ) (v : ℝ), 0 < v → (∀ m ∈ G, 0 < m) → G.card ≤ 3 →
      ∃ τ : ℝ, 0 < τ ∧ ∀ m ∈ G, (4 : ℝ)⁻¹ ≤ circDist (v * m * τ) := by
    intro G v hv hG hcG
    obtain ⟨τ, hτ, hl⟩ := existenceAtN_four (G.image (fun m : ℕ => v * (m : ℝ)) : Finset ℝ)
      (by
        intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        have : (0 : ℝ) < m := by exact_mod_cast hG m hm
        positivity)
      (by
        have := le_trans (Finset.card_image_le (s := G) (f := fun m : ℕ => v * (m : ℝ))) hcG
        omega)
    exact ⟨τ, hτ, fun m hm => by simpa using hl _ (Finset.mem_image_of_mem _ hm)⟩
  obtain ⟨τA, hτA, hlA⟩ := group A u hu hA hcA
  obtain ⟨τB, hτB, hlB⟩ := group B w hw hB hcB
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨τB, hτB, by simp, fun m hm => le_trans (by norm_num) (hlB m hm)⟩
  obtain ⟨m0, hm0⟩ := hAne
  have hsup : ∀ m ∈ A, m ≤ A.sup id := fun m hm => Finset.le_sup (f := id) hm
  have hsup0 : (0 : ℝ) < ((A.sup id : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (hA m0 hm0) (hsup m0 hm0)
  set MA : ℝ := u * ((A.sup id : ℕ) : ℝ) with hMAdef
  have hMA : 0 < MA := by positivity
  have hle : ∀ m ∈ A, u * (m : ℝ) ≤ MA := fun m hm =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hsup m hm) hu.le
  set δ : ℝ := 1 / (20 * MA) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := δ * u with hε
  have hε0 : 0 < ε := by positivity
  -- a small step of the ratio of the two periods, by pigeonhole
  set n : ℕ := ⌈1 / ε⌉₊ + 1 with hn
  obtain ⟨j, k0, hk0, -, hdir⟩ := Real.exists_int_int_abs_mul_sub_le (u / w) (show 0 < n by omega)
  have hnε : 1 / ((n : ℝ) + 1) ≤ ε := by
    have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (n : ℝ) + 1 = (⌈1 / ε⌉₊ : ℝ) + 2 := by rw [hn]; push_cast; ring
    rw [h2, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε0] at h1
    nlinarith
  set s : ℝ := (k0 : ℝ) * (u / w) - j with hs
  have hs0 : s ≠ 0 := ((hirr.intCast_mul hk0.ne').sub_intCast j).ne_zero
  have hsε : |s| ≤ ε := le_trans hdir hnε
  -- stepping lines the two groups up
  obtain ⟨i, K, hiK⟩ := exists_step_near_int ((τB - τA) * u) s ε hs0 hsε
  set l : ℕ := i * k0.toNat with hl
  have hlr : (l : ℝ) = (i : ℝ) * (k0 : ℝ) := by
    rw [hl]; push_cast; rw [show ((k0.toNat : ℕ) : ℝ) = ((k0.toNat : ℤ) : ℝ) by rfl,
      Int.toNat_of_nonneg hk0.le]
  set t : ℝ := τB + l / w with ht
  refine ⟨t, by positivity, fun m hm => ?_, fun m hm => ?_⟩
  · -- group `A`: inside a repeat of its cell
    set r : ℝ := t - τA - ((K + i * j : ℤ) : ℝ) / u with hr
    have hru : r * u = (τB - τA) * u + i * s - K := by
      rw [hr, ht, hs, hlr]; push_cast; field_simp; ring
    have hrδ : |r| ≤ δ := by
      have habs : |r| * u = |(τB - τA) * u + i * s - K| := by
        rw [← hru, abs_mul, abs_of_pos hu]
      have : |r| * u ≤ δ * u := by rw [habs]; exact hiK
      exact le_of_mul_le_mul_right this hu
    have heq : u * m * t = (u * m * τA + u * m * r) + ((m * (K + i * j) : ℤ) : ℝ) := by
      rw [hr]; push_cast; field_simp; ring
    rw [heq, circDist_add_int]
    have hlip := circDist_lipschitz.dist_le_mul (u * m * τA + u * m * r) (u * m * τA)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hbound : |u * m * τA + u * m * r - u * m * τA| ≤ MA * δ := by
      rw [show u * m * τA + u * m * r - u * m * τA = (u * m) * r by ring, abs_mul,
        abs_of_nonneg (by positivity)]
      exact mul_le_mul (hle m hm) hrδ (abs_nonneg _) hMA.le
    have hMAδ : MA * δ = 1 / 20 := by rw [hδ]; field_simp
    have h1 := hlA m hm
    have := abs_sub_le_iff.mp hlip
    have h45 : (4 : ℝ)⁻¹ - 1 / 20 = (5 : ℝ)⁻¹ := by norm_num
    linarith [this.2]
  · -- group `B`: exactly on a repeat of its lonely moment
    have heq : w * m * t = w * m * τB + (((m * l : ℕ) : ℤ) : ℝ) := by
      rw [ht]; push_cast; field_simp
    rw [heq, circDist_add_int]
    exact le_trans (by norm_num) (hlB m hm)

/-! ## A group on its lattice, and two free runners -/

/-- **Two free runners, the slower leading.**  With steps `0 < σ₁ ≤ σ₂ ≤ 1/2` and `σ₁ ≤ 1/20`, the
walk `(β + m σ₁, γ + m σ₂)` puts both runners in the band at `1/5` for some `m`: the leader stays
in its band for about `1/(2σ₁)` steps, and in that stretch the follower crosses its blocked arc of
`2/5` and lands clear. -/
theorem exists_walk_clear_pos (β γ σ1 σ2 : ℝ) (h1 : 0 < σ1) (h12 : σ1 ≤ σ2) (h2 : σ2 ≤ 1 / 2)
    (hsmall : σ1 ≤ 1 / 20) :
    ∃ m : ℕ, (1 / 5 : ℝ) ≤ circDist (β + m * σ1) ∧ (1 / 5 : ℝ) ≤ circDist (γ + m * σ2) := by
  -- the leader enters its band near `K + 1/5`
  obtain ⟨i0, K, hK⟩ := exists_step_near_int (β - 1 / 5 - σ1) σ1 σ1 h1.ne' (by rw [abs_of_pos h1])
  have hb0 := abs_le.mp hK
  -- the follower, from where it stands at `i0`
  set γ0 := γ + i0 * σ2 with hγ0
  have hσ2 : 0 < σ2 := lt_of_lt_of_le h1 h12
  set M : ℕ := ⌊1 / (2 * σ1)⌋₊ with hM
  have hMσ : (M : ℝ) * σ1 ≤ 1 / 2 := by
    have := Nat.floor_le (show (0 : ℝ) ≤ 1 / (2 * σ1) by positivity)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hM1 : 1 / (2 * σ1) - 1 < M := Nat.sub_one_lt_floor _
  obtain ⟨i, hiM, hci⟩ : ∃ i : ℕ, i ≤ M ∧ (1 / 5 : ℝ) ≤ circDist (γ0 + i * σ2) := by
    obtain ⟨K', hK'⟩ := circDist_eq_abs_sub_some_int γ0
    by_cases hc0 : (1 / 5 : ℝ) ≤ circDist γ0
    · exact ⟨0, Nat.zero_le _, by simpa using hc0⟩
    · push Not at hc0
      rw [hK'] at hc0
      have hy := abs_lt.mp hc0
      have hx0 : 0 ≤ ((K' : ℝ) + 1 / 5 - γ0) / σ2 := div_nonneg (by linarith) hσ2.le
      refine ⟨⌈((K' : ℝ) + 1 / 5 - γ0) / σ2⌉₊, ?_, fifth_le_circDist_of_band K' ?_ ?_⟩
      · -- the follower lands within the leader's stretch
        have hc := Nat.ceil_lt_add_one hx0
        have hlt : ((K' : ℝ) + 1 / 5 - γ0) / σ2 < 2 / 5 / σ1 := by
          rw [div_lt_div_iff₀ hσ2 h1]; nlinarith
        have : (⌈((K' : ℝ) + 1 / 5 - γ0) / σ2⌉₊ : ℝ) ≤ M := by
          have h20 : 2 / 5 / σ1 + 1 ≤ 1 / (2 * σ1) - 1 := by
            rw [div_add_one h1.ne', div_sub_one (by positivity), div_le_div_iff₀ h1 (by positivity)]
            nlinarith
          linarith
        exact_mod_cast this
      · have := Nat.le_ceil (((K' : ℝ) + 1 / 5 - γ0) / σ2)
        rw [div_le_iff₀ hσ2] at this; linarith
      · have hc := Nat.ceil_lt_add_one hx0
        have h' : (⌈((K' : ℝ) + 1 / 5 - γ0) / σ2⌉₊ : ℝ) * σ2 < ((K' : ℝ) + 1 / 5 - γ0) + σ2 := by
          have := mul_lt_mul_of_pos_right hc hσ2
          rwa [add_mul, div_mul_cancel₀ _ hσ2.ne', one_mul] at this
        linarith
  refine ⟨i0 + i, ?_, ?_⟩
  · -- the leader is still in its band
    apply fifth_le_circDist_of_band K
    · push_cast; nlinarith [hb0.1]
    · push_cast
      have hi : (i : ℝ) * σ1 ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hiM) h1.le) hMσ
      nlinarith [hb0.2]
  · have heq : γ + ((i0 + i : ℕ) : ℝ) * σ2 = γ0 + i * σ2 := by rw [hγ0]; push_cast; ring
    rw [heq]; exact hci

/-- The walk with steps of either sign, the smaller of size at most `1/20`, both nonzero and at
most `1/2`. -/
theorem exists_walk_clear (β γ s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0) (hs2 : |s| ≤ 1 / 2)
    (ht2 : |t| ≤ 1 / 2) (hsmall : min |s| |t| ≤ 1 / 20) :
    ∃ m : ℕ, (1 / 5 : ℝ) ≤ circDist (β + m * s) ∧ (1 / 5 : ℝ) ≤ circDist (γ + m * t) := by
  -- signs: `circDist` is even
  have sign : ∀ (x σ : ℝ) (m : ℕ), circDist (x + m * σ) = circDist ((if 0 < σ then x else -x) +
      m * |σ|) := by
    intro x σ m
    split_ifs with h
    · rw [abs_of_pos h]
    · push Not at h
      rw [abs_of_nonpos h, ← circDist.symm_neg]; ring_nf
  have hs0 : 0 < |s| := abs_pos.mpr hs
  have ht0 : 0 < |t| := abs_pos.mpr ht
  rcases le_total |s| |t| with hst | hts
  · obtain ⟨m, h1, h2⟩ := exists_walk_clear_pos (if 0 < s then β else -β) (if 0 < t then γ else -γ)
      |s| |t| hs0 hst ht2 (by rwa [min_eq_left hst] at hsmall)
    exact ⟨m, by rw [sign]; exact h1, by rw [sign]; exact h2⟩
  · obtain ⟨m, h1, h2⟩ := exists_walk_clear_pos (if 0 < t then γ else -γ) (if 0 < s then β else -β)
      |t| |s| ht0 hts hs2 (by rwa [min_eq_right hts] at hsmall)
    exact ⟨m, by rw [sign]; exact h2, by rw [sign]; exact h1⟩

/-- **A group on its lattice, and two free runners.**  Let the group `u·A` be lonely at `1/5`
at `τ > 0`, and let `b, c > 0` with `b/u, c/u` irrational.  Along the group's lattice
`τ + k/u` the group stays lonely, and a Dirichlet step with the walk puts `b` and `c` clear
too. -/
theorem lonely_group_two_free {A : Finset ℕ} {u b c τ : ℝ} (hu : 0 < u) (hτ : 0 < τ)
    (hA : ∀ m ∈ A, (5 : ℝ)⁻¹ ≤ circDist (u * m * τ))
    (hb : Irrational (b / u)) (hc : Irrational (c / u)) :
    ∃ t : ℝ, 0 < t ∧ (∀ m ∈ A, (5 : ℝ)⁻¹ ≤ circDist (u * m * t)) ∧
      (5 : ℝ)⁻¹ ≤ circDist (b * t) ∧ (5 : ℝ)⁻¹ ≤ circDist (c * t) := by
  obtain ⟨j, k0, hk0, -, hdir⟩ := Real.exists_int_int_abs_mul_sub_le (b / u) (show 0 < 20 by norm_num)
  set sb : ℝ := (k0 : ℝ) * (b / u) - j with hsb
  set jc : ℤ := round ((k0 : ℝ) * (c / u)) with hjc
  set sc : ℝ := (k0 : ℝ) * (c / u) - jc with hsc
  have hsb0 : sb ≠ 0 := ((hb.intCast_mul hk0.ne').sub_intCast j).ne_zero
  have hsc0 : sc ≠ 0 := ((hc.intCast_mul hk0.ne').sub_intCast jc).ne_zero
  have hsb2 : |sb| ≤ 1 / 20 := by
    have : (1 : ℝ) / ((20 : ℕ) + 1) ≤ 1 / 20 := by norm_num
    exact le_trans hdir (by simpa using this)
  have hsc2 : |sc| ≤ 1 / 2 := abs_sub_round _
  obtain ⟨m, h1, h2⟩ := exists_walk_clear (b * τ) (c * τ) sb sc hsb0 hsc0
    (by linarith) hsc2 (le_trans (min_le_left _ _) hsb2)
  have hk : (0 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0.le
  set t : ℝ := τ + (m : ℝ) * (k0 : ℝ) / u with ht
  have h15 : (5 : ℝ)⁻¹ = 1 / 5 := by norm_num
  refine ⟨t, by positivity, fun a ha => ?_, ?_, ?_⟩
  · have heq : u * a * t = u * a * τ + (((a : ℤ) * (m * k0) : ℤ) : ℝ) := by
      rw [ht]; push_cast; field_simp
    rw [heq, circDist_add_int]; exact hA a ha
  · have heq : b * t = (b * τ + m * sb) + (((m : ℤ) * j : ℤ) : ℝ) := by
      rw [ht, hsb]; push_cast; field_simp; ring
    rw [heq, circDist_add_int, h15]; exact h1
  · have heq : c * t = (c * τ + m * sc) + (((m : ℤ) * jc : ℤ) : ℝ) := by
      rw [ht, hsc]; push_cast; field_simp; ring
    rw [heq, circDist_add_int, h15]; exact h2

end LRC.OrderFiveN
