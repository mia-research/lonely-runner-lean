import LonelyRunner.LRC.Cascade.Iteration
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# Flanks: every lonely instant is an opening of one runner, read by speed ratios

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/n`.

* `flankOpening n e k = (k + 1/n)/e` — the `k`-th opening of the runner at difference `e` (the flank).
* `exists_flank_of_lonely`, `lonely_iff_exists_flank` — the subject is lonely at some positive instant iff some flank has a
  lonely opening (from `reading_complete`).
* `position_at_flank` — at the flank's `k`-th opening, the runner at `d` sits at `(d/e)·(k + 1/n)` laps: only the ratio
  `d/e` enters.
* `integer_ratio_clear_iff` — a runner whose ratio to the flank is an integer `A` is clear at every opening unless `n ∣ A`,
  and in the way at every opening if `n ∣ A`.
* `fractional_ratio_circDist` — otherwise only the fractional part `f` of the ratio moves: the circle distance at opening `k`
  is that of `k·f + (d/e)/n`.
* `exists_clear_step` — for `n ≥ 4` and `0 < f < 1`, the points `k·f + c` cannot all stay within `1/n` of an integer.
* `lonely_opening_of_one_fractional` — a flank at which one runner has a non-integer ratio and every other ratio is an integer
  not divisible by `n` has a lonely opening; so the cascade from the bound stops (`stops_of_one_fractional`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Flanks

open ConstructionN MomentIterationN

/-- The `k`-th opening of the flank at difference `e`. -/
noncomputable def flankOpening (n : ℕ) (e : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + (n : ℝ)⁻¹) / e

variable {n : ℕ} [Fact (2 ≤ n)]

theorem flankOpening_pos {e : ℝ} (he : 0 < e) (k : ℕ) : 0 < flankOpening n e k := by
  unfold flankOpening
  have : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr n_pos
  positivity

/-- **Every lonely instant is matched by a lonely flank opening.** -/
theorem exists_flank_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {s : ℝ} (hs : 0 < s)
    (hl : Lonely n ds s) (hne : ds.Nonempty) :
    ∃ e ∈ ds, ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  have hn0 : 0 < n := by have := (Fact.out : 2 ≤ n); omega
  obtain ⟨e, he, -, hlo⟩ := reading_complete hn0 ds hne hpos hl
  have he0 := hpos e he
  have hfl : (0 : ℤ) ≤ ⌊e * s⌋ := Int.floor_nonneg.mpr (by positivity)
  refine ⟨e, he, ⌊e * s⌋.toNat, ?_⟩
  have hcast : ((⌊e * s⌋.toNat : ℕ) : ℝ) = ((⌊e * s⌋ : ℤ) : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hfl
  unfold flankOpening; rw [hcast]
  exact hlo

/-- **Loneliness is a flank statement.** -/
theorem lonely_iff_exists_flank {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) :
    (∃ s, 0 < s ∧ Lonely n ds s) ↔ ∃ e ∈ ds, ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  constructor
  · rintro ⟨s, hs, hl⟩; exact exists_flank_of_lonely hpos hs hl hne
  · rintro ⟨e, he, k, hl⟩; exact ⟨_, flankOpening_pos (hpos e he) k, hl⟩

/-- At the flank's `k`-th opening only the ratio `d/e` enters. -/
theorem position_at_flank {d e : ℝ} (he : 0 < e) (k : ℕ) :
    d * flankOpening n e k = (d / e) * ((k : ℝ) + (n : ℝ)⁻¹) := by
  unfold flankOpening; field_simp

/-- **Integer ratios.** A runner at ratio `A` (an integer) to the flank is clear at every opening iff `n ∤ A`. -/
theorem integer_ratio_clear_iff {d e : ℝ} (he : 0 < e) {A : ℤ} (hA : d = A * e) (k : ℕ) :
    (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e k) ↔ ¬ ((n : ℤ) ∣ A) := by
  have hn0 : 0 < n := by have := (Fact.out : 2 ≤ n); omega
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have e1 : d * flankOpening n e k = (((A * 1 : ℤ) : ℝ) / n) + ((A * k : ℤ) : ℝ) := by
    rw [position_at_flank he, hA]; push_cast; field_simp; ring
  rw [e1, circDist_add_int]
  exact spine_all_or_nothing hn0 isCoprime_one_right

/-- **Fractional ratios.** Only the fractional part `f` of the ratio moves from opening to opening. -/
theorem fractional_ratio_circDist {d e : ℝ} (he : 0 < e) (k : ℕ) :
    circDist (d * flankOpening n e k) = circDist ((k : ℝ) * Int.fract (d / e) + (d / e) / n) := by
  have e1 : d * flankOpening n e k =
      ((k : ℝ) * Int.fract (d / e) + (d / e) / n) + ((k * ⌊d / e⌋ : ℤ) : ℝ) := by
    rw [position_at_flank he]
    have hf : Int.fract (d / e) = d / e - ⌊d / e⌋ := rfl
    rw [hf]; push_cast; ring
  rw [e1, circDist_add_int]

/-- **One step cannot stay in the way.** For `n ≥ 4` and a step `0 < f < 1`, some `k·f + c` is at least `1/n` from every
integer. -/
theorem exists_clear_step (hn4 : 4 ≤ n) {f c : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    ∃ k : ℕ, (n : ℝ)⁻¹ ≤ circDist ((k : ℝ) * f + c) := by
  by_contra hcon
  push Not at hcon
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hq : 4 * (n : ℝ)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hn0]; linarith
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  choose m hm using fun k : ℕ => circDist_eq_abs_sub_some_int ((k : ℝ) * f + c)
  have hnear : ∀ k : ℕ, |(k : ℝ) * f + c - (m k : ℝ)| < (n : ℝ)⁻¹ := fun k => (hm k) ▸ hcon k
  -- consecutive nearest integers differ by δ with |f − δ| < 2/n
  have hstep : ∀ k : ℕ, f - ((m (k + 1) : ℝ) - (m k : ℝ)) < 2 * (n : ℝ)⁻¹ ∧
      -(2 * (n : ℝ)⁻¹) < f - ((m (k + 1) : ℝ) - (m k : ℝ)) := by
    intro k
    have h1 := abs_lt.mp (hnear k)
    have h2 := abs_lt.mp (hnear (k + 1))
    push_cast at h2
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  rcases lt_or_ge f (2 * (n : ℝ)⁻¹) with hsmall | hbig
  · -- the nearest integer never changes
    have hconst : ∀ k : ℕ, m k = m 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        obtain ⟨s1, s2⟩ := hstep k
        have hd0 : m (k + 1) - m k ≤ 0 := by
          by_contra h; push Not at h
          have : (1 : ℝ) ≤ (m (k + 1) : ℝ) - (m k : ℝ) := by exact_mod_cast h
          linarith
        have hd1 : 0 ≤ m (k + 1) - m k := by
          by_contra h; push Not at h
          have : (m (k + 1) : ℝ) - (m k : ℝ) ≤ -1 := by
            have : m (k + 1) - m k ≤ -1 := by omega
            exact_mod_cast this
          linarith
        omega
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / f)
    have hKf : 2 < (K : ℝ) * f := by rwa [div_lt_iff₀ hf0] at hK
    have h0 := abs_lt.mp (hnear 0)
    have hK' := abs_lt.mp (hnear K)
    rw [hconst K] at hK'
    push_cast at h0
    linarith [h0.1, h0.2, hK'.1, hK'.2]
  · rcases lt_or_ge (1 - 2 * (n : ℝ)⁻¹) f with hlarge | hmid
    · -- the nearest integer advances by one each step
      have hlin : ∀ k : ℕ, m k = m 0 + k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          obtain ⟨s1, s2⟩ := hstep k
          have hd1 : m (k + 1) - m k ≤ 1 := by
            by_contra h; push Not at h
            have : (2 : ℝ) ≤ (m (k + 1) : ℝ) - (m k : ℝ) := by
              have : 2 ≤ m (k + 1) - m k := by omega
              exact_mod_cast this
            linarith
          have hd2 : 1 ≤ m (k + 1) - m k := by
            by_contra h; push Not at h
            have : (m (k + 1) : ℝ) - (m k : ℝ) ≤ 0 := by
              have : m (k + 1) - m k ≤ 0 := by omega
              exact_mod_cast this
            linarith
          push_cast; omega
      obtain ⟨K, hK⟩ := exists_nat_gt (2 / (1 - f))
      have hpos1 : 0 < 1 - f := by linarith
      have hKf : 2 < (K : ℝ) * (1 - f) := by rwa [div_lt_iff₀ hpos1] at hK
      have h0 := abs_lt.mp (hnear 0)
      have hK' := abs_lt.mp (hnear K)
      rw [hlin K] at hK'
      push_cast at h0 hK'
      nlinarith [h0.1, h0.2, hK'.1, hK'.2]
    · -- a middle step cannot be followed at all
      obtain ⟨s1, s2⟩ := hstep 0
      rcases le_or_gt (m 1 - m 0) 0 with hd | hd
      · have : (m 1 : ℝ) - (m 0 : ℝ) ≤ 0 := by exact_mod_cast hd
        linarith
      · have : (1 : ℝ) ≤ (m 1 : ℝ) - (m 0 : ℝ) := by
          have : 1 ≤ m 1 - m 0 := by omega
          exact_mod_cast this
        linarith

/-- **Blocking a whole residue class of openings forces integrality.**  If the runner at difference `d` is in the
way at every opening `k ≡ r (mod P)` of the flank at `e`, then `P·(d/e)` is an integer.

This is what makes a killer set finite: only ratios with `P·(d/e) ∈ ℤ` can shadow an entire class of openings,
so the candidates form a lattice rather than a continuum.  Stated as the clear-step form (some opening in the
class is clear) with the integrality corollary below.

No density, equidistribution or rationality input: `exists_clear_step` covers rational and irrational `d/e`
alike, in one case. -/
theorem clear_in_class_of_not_int (hn4 : 4 ≤ n) {d e : ℝ} (he : 0 < e) (P r : ℕ)
    (hfr : Int.fract ((P : ℝ) * (d / e)) ≠ 0) :
    ∃ j : ℕ, (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e (r + j * P)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hf0 : 0 < Int.fract ((P : ℝ) * (d / e)) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfr)
  have hf1 : Int.fract ((P : ℝ) * (d / e)) < 1 := Int.fract_lt_one _
  obtain ⟨j, hj⟩ := exists_clear_step (n := n) hn4 hf0 hf1
    (c := (d / e) * (r : ℝ) + (d / e) * (n : ℝ)⁻¹)
  refine ⟨j, ?_⟩
  have hfr' : Int.fract ((P : ℝ) * (d / e)) = (P : ℝ) * (d / e) - (⌊(P : ℝ) * (d / e)⌋ : ℝ) := rfl
  have key : d * flankOpening n e (r + j * P)
      = ((j : ℝ) * Int.fract ((P : ℝ) * (d / e))
          + ((d / e) * (r : ℝ) + (d / e) * (n : ℝ)⁻¹))
        + ((j * ⌊(P : ℝ) * (d / e)⌋ : ℤ) : ℝ) := by
    unfold flankOpening
    rw [hfr']
    push_cast
    field_simp
    ring
  rw [key, circDist_add_int]
  exact hj

/-- **Integrality of a class killer.**  Contrapositive of `clear_in_class_of_not_int`: shadowing
every opening in a residue class mod `P` forces `P·(d/e) ∈ ℤ`. -/
theorem class_killer_int (hn4 : 4 ≤ n) {d e : ℝ} (he : 0 < e) (P r : ℕ)
    (hblock : ∀ j : ℕ, inWay n d (flankOpening n e (r + j * P))) :
    Int.fract ((P : ℝ) * (d / e)) = 0 := by
  by_contra hfr
  obtain ⟨j, hj⟩ := clear_in_class_of_not_int (n := n) hn4 he P r hfr
  exact absurd (hblock j) (not_lt.mpr hj)

/-- **A ratio on the lattice is periodic in the opening index.**  If `P·(d/e) ∈ ℤ` then the runner at
difference `d` has the same circle distance at openings `k` and `k + jP`: being in the way depends only
on `k` mod `P`.  This is what makes the uncovered set `U_e` a set of residues rather than of openings. -/
theorem circDist_periodic_of_lattice {d e : ℝ} (he : 0 < e) {P : ℕ}
    (hP : Int.fract ((P : ℝ) * (d / e)) = 0) (k j : ℕ) :
    circDist (d * flankOpening n e (k + j * P)) = circDist (d * flankOpening n e k) := by
  -- `P · fract (d/e)` is the integer `⌊P·(d/e)⌋ − P·⌊d/e⌋`
  have hPρ : (P : ℝ) * (d / e) = (⌊(P : ℝ) * (d / e)⌋ : ℝ) := by
    have h := Int.fract_add_floor ((P : ℝ) * (d / e))
    rw [hP] at h; linarith
  have hmr : ((⌊(P : ℝ) * (d / e)⌋ - (P : ℤ) * ⌊d / e⌋ : ℤ) : ℝ)
      = (P : ℝ) * Int.fract (d / e) := by
    have hfr : Int.fract (d / e) = d / e - (⌊d / e⌋ : ℝ) := rfl
    rw [hfr]; push_cast; rw [← hPρ]; ring
  rw [fractional_ratio_circDist he, fractional_ratio_circDist he]
  have key : ((k + j * P : ℕ) : ℝ) * Int.fract (d / e) + d / e / (n : ℝ)
      = ((k : ℝ) * Int.fract (d / e) + d / e / (n : ℝ))
        + ((j * (⌊(P : ℝ) * (d / e)⌋ - (P : ℤ) * ⌊d / e⌋) : ℤ) : ℝ) := by
    push_cast [hmr]; ring
  rw [key, circDist_add_int]

/-- **A free parameter off the lattice cannot shadow an uncovered class.**  Suppose every runner other
than `x` has its ratio to the flank on the lattice (`P·(d/e) ∈ ℤ`) and is clear at opening `r`, so the
whole class `r + jP` is clear of them.  If `x` is off the lattice then the flank has a lonely opening.

Together with `class_killer_int` this is the finiteness the killer set needs: a shadow of an uncovered
class must come from the lattice, so only lattice values of `x` can be checked, and every other value
leaves the flank free. -/
theorem lonely_opening_of_free_off_lattice (hn4 : 4 ≤ n) {ds : Finset ℝ} {e x : ℝ} (he0 : 0 < e)
    (P r : ℕ)
    (hlat : ∀ d ∈ ds, d ≠ x → Int.fract ((P : ℝ) * (d / e)) = 0)
    (hclear : ∀ d ∈ ds, d ≠ x → (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e r))
    (hoff : Int.fract ((P : ℝ) * (x / e)) ≠ 0) :
    ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  obtain ⟨j, hj⟩ := clear_in_class_of_not_int (n := n) hn4 he0 P r hoff
  refine ⟨r + j * P, fun d hd => ?_⟩
  by_cases hdx : d = x
  · subst hdx; exact hj
  · rw [circDist_periodic_of_lattice he0 (hlat d hd hdx) r j]
    exact hclear d hd hdx

/-- **A flank with one fractional ratio has a lonely opening** (`n ≥ 4`). Every other runner has an integer ratio to the flank
that `n` does not divide (the flank itself has ratio `1`). -/
theorem lonely_opening_of_one_fractional (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {e j : ℝ}
    (he : e ∈ ds) (hj : j ∈ ds) (hfrac : Int.fract (j / e) ≠ 0)
    (hint : ∀ d ∈ ds, d ≠ j → ∃ A : ℤ, d = A * e ∧ ¬ ((n : ℤ) ∣ A)) :
    ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  have he0 := hpos e he
  have hf0 : 0 < Int.fract (j / e) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfrac)
  obtain ⟨k, hk⟩ := exists_clear_step (n := n) hn4 (c := (j / e) / n) hf0 (Int.fract_lt_one _)
  refine ⟨k, fun d hd => ?_⟩
  by_cases hdj : d = j
  · subst hdj; rw [fractional_ratio_circDist he0]; exact hk
  · obtain ⟨A, hA, hnA⟩ := hint d hd hdj
    exact (integer_ratio_clear_iff he0 hA k).2 hnA

/-- **The cascade stops** for such an arrangement (`exists_fixed_of_lonely`). -/
theorem stops_of_one_fractional (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m e j : ℝ} (hm : m ∈ ds)
    (he : e ∈ ds) (hj : j ∈ ds) (hfrac : Int.fract (j / e) ≠ 0)
    (hint : ∀ d ∈ ds, d ≠ j → ∃ A : ℤ, d = A * e ∧ ¬ ((n : ℤ) ∣ A)) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  obtain ⟨k, hk⟩ := lonely_opening_of_one_fractional hn4 hpos he hj hfrac hint
  exact exists_fixed_of_lonely hpos hm (flankOpening_pos (hpos e he) k) hk

end Flanks
