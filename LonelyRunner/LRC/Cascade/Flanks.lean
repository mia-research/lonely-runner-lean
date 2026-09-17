import LonelyRunner.LRC.Cascade.Iteration
import LonelyRunner.LRC.ConstructionN.LemmaPass
import Mathlib.NumberTheory.Real.Irrational

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

/-- **Inside the band is clear.**  If `y` lies in `[1/n, 1 − 1/n]` then `y` plus any integer is at least
`1/n` from every integer.  The clearance facts of a concrete family all reduce to this. -/
theorem circDist_ge_of_band {y : ℝ} (c : ℤ) (h1 : (n : ℝ)⁻¹ ≤ y) (h2 : y ≤ 1 - (n : ℝ)⁻¹) :
    (n : ℝ)⁻¹ ≤ circDist (y + (c : ℝ)) := by
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr n_pos
  have hy0 : (0 : ℝ) ≤ y := le_trans hh0.le h1
  have hy1 : y < 1 := by linarith
  rw [circDist_add_int]
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨hy0, hy1⟩, le_min_iff]
  exact ⟨h1, by linarith⟩

/-- **The clearing test, as an integer comparison** (Proposition 2.1).  A runner at a whole-number
difference `m` is clear at the `k`-th opening of a whole-number flank `e` exactly when the residue
`m·(n·k+1) mod n·e` lies in the band `[e, (n−1)·e]`.

This is the framework's own decision procedure: at `t = a/(n·D)` a difference is clear iff
`D ≤ a·e mod n·D ≤ (n−1)·D`.  Nothing real-valued survives — the verdict is decidable arithmetic, so a
concrete arrangement discharges by `decide`. -/
theorem clear_of_residue_band {e k m : ℕ} (he : 0 < e)
    (h1 : e ≤ m * (n * k + 1) % (n * e)) (h2 : m * (n * k + 1) % (n * e) ≤ (n - 1) * e) :
    (n : ℝ)⁻¹ ≤ circDist ((m : ℝ) * flankOpening n e k) := by
  have hn2 : 2 ≤ n := Fact.out
  have hn0 : (0 : ℝ) < n := n_pos
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have hN0 : 0 < n * e := Nat.mul_pos (by omega) he
  have hNR : (0 : ℝ) < ((n * e : ℕ) : ℝ) := by exact_mod_cast hN0
  have step1 : (m : ℝ) * flankOpening n e k = ((m * (n * k + 1) : ℕ) : ℝ) / ((n * e : ℕ) : ℝ) := by
    unfold flankOpening; push_cast; field_simp
  have hdm : ((m * (n * k + 1) : ℕ) : ℝ)
      = ((n * e : ℕ) : ℝ) * ((m * (n * k + 1) / (n * e) : ℕ) : ℝ)
        + ((m * (n * k + 1) % (n * e) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (m * (n * k + 1)) (n * e)).symm
  have step2 : ((m * (n * k + 1) : ℕ) : ℝ) / ((n * e : ℕ) : ℝ)
      = ((m * (n * k + 1) % (n * e) : ℕ) : ℝ) / ((n * e : ℕ) : ℝ)
        + (((m * (n * k + 1) / (n * e) : ℕ) : ℤ) : ℝ) := by
    have hz : (((m * (n * k + 1) / (n * e) : ℕ) : ℤ) : ℝ)
        = ((m * (n * k + 1) / (n * e) : ℕ) : ℝ) := by norm_cast
    rw [hz, div_add' _ _ _ hNR.ne']
    congr 1
    linarith [hdm]
  rw [step1, step2]
  refine circDist_ge_of_band _ ?_ ?_
  · rw [le_div_iff₀ hNR]
    have he' : (e : ℝ) ≤ ((m * (n * k + 1) % (n * e) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast
    nlinarith [he', hinv, hn0, heR]
  · rw [div_le_iff₀ hNR]
    have hn1 : 1 ≤ n := by omega
    have hcast : (((n - 1) * e : ℕ) : ℝ) = ((n : ℝ) - 1) * (e : ℝ) := by
      push_cast [Nat.cast_sub hn1]; ring
    have h2' : ((m * (n * k + 1) % (n * e) : ℕ) : ℝ) ≤ ((n : ℝ) - 1) * (e : ℝ) := by
      rw [← hcast]; exact_mod_cast h2
    push_cast
    nlinarith [h2', hinv, hn0, heR]

/-- **A whole arrangement cleared by one integer check.**  If every difference in the list satisfies the
residue band at the `k`-th opening of the flank `e`, the subject is lonely there.  The hypothesis is
decidable arithmetic on small naturals, so a concrete arrangement closes by `decide`. -/
theorem lonely_of_band_list {L : List ℕ} {e k : ℕ} (he : 0 < e)
    (h : ∀ m ∈ L, e ≤ m * (n * k + 1) % (n * e) ∧ m * (n * k + 1) % (n * e) ≤ (n - 1) * e) :
    Lonely n ((L.map (Nat.cast : ℕ → ℝ)).toFinset) (flankOpening n e k) := by
  classical
  intro d hd
  simp only [List.mem_toFinset, List.mem_map] at hd
  obtain ⟨m, hmL, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h m hmL
  exact clear_of_residue_band he h1 h2

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

/-- **An unkillable flank is free for every value of the free parameter.**

The family form.  `U` is the flank's uncovered residue set: every runner but `x` is on the lattice
(`P·(d/e) ∈ ℤ`, so by `circDist_periodic_of_lattice` its verdict depends only on the residue) and is
clear at every residue in `U`.  The free runner `x` is unconstrained.  If, whenever `x` lands on the
lattice, it fails to shadow the whole class of some residue in `U`, then the flank has a lonely opening
— for **every** real `x`, not merely the ones checked.

The off-lattice values of `x` need no hypothesis at all: `class_killer_int` rules them out, so a family
is settled by a finite check over the lattice.  This is the machine's `K_e = ∅` verdict, as a theorem. -/
theorem lonely_of_flank_unkillable (hn4 : 4 ≤ n) {ds : Finset ℝ} {e x : ℝ} (he0 : 0 < e) (P : ℕ)
    (U : Finset ℕ) (hUne : U.Nonempty)
    (hlat : ∀ d ∈ ds, d ≠ x → Int.fract ((P : ℝ) * (d / e)) = 0)
    (hU : ∀ r ∈ U, ∀ d ∈ ds, d ≠ x → (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e r))
    (hkill : Int.fract ((P : ℝ) * (x / e)) = 0 →
      ∃ r ∈ U, ∃ j : ℕ, (n : ℝ)⁻¹ ≤ circDist (x * flankOpening n e (r + j * P))) :
    ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  by_cases hoff : Int.fract ((P : ℝ) * (x / e)) = 0
  · -- `x` is on the lattice: it fails on some uncovered residue, and the rest are clear there
    obtain ⟨r, hrU, j, hj⟩ := hkill hoff
    refine ⟨r + j * P, fun d hd => ?_⟩
    by_cases hdx : d = x
    · subst hdx; exact hj
    · rw [circDist_periodic_of_lattice he0 (hlat d hd hdx) r j]
      exact hU r hrU d hd hdx
  · -- `x` is off the lattice: `class_killer_int` rules it out with no further hypothesis
    obtain ⟨r, hrU⟩ := hUne
    exact lonely_opening_of_free_off_lattice hn4 he0 P r hlat (hU r hrU) hoff

/-- **Existence for the runner, from an unkillable flank.**  The cascade from the bound reaches a fixed
point (`lonely_iff_run_ends`), which is Existence read at this flank. -/
theorem stops_of_flank_unkillable (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m e x : ℝ}
    (hm : m ∈ ds) (he0 : 0 < e) (P : ℕ) (U : Finset ℕ) (hUne : U.Nonempty)
    (hlat : ∀ d ∈ ds, d ≠ x → Int.fract ((P : ℝ) * (d / e)) = 0)
    (hU : ∀ r ∈ U, ∀ d ∈ ds, d ≠ x → (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e r))
    (hkill : Int.fract ((P : ℝ) * (x / e)) = 0 →
      ∃ r ∈ U, ∃ j : ℕ, (n : ℝ)⁻¹ ≤ circDist (x * flankOpening n e (r + j * P))) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  obtain ⟨k, hk⟩ := lonely_of_flank_unkillable hn4 he0 P U hUne hlat hU hkill
  exact exists_fixed_of_lonely hpos hm (flankOpening_pos he0 k) hk

/-- **The empty-killer-intersection route.**  The flank that survives may depend on the free parameter.

Each flank `e ∈ E` carries its own period `P e` and uncovered residue set `U e`, with every runner but
`x` on that flank's lattice and clear at every residue in `U e`.  If **some** flank of `E` is one that
`x` fails to shadow, that flank has a lonely opening.

`hsome`'s body is exactly "`x` is not a killer of flank `e`": either `x` is off that flank's lattice, in
which case the implication is vacuous and `class_killer_int` does the work, or it is on the lattice and
fails on some uncovered residue.  So the hypothesis is the negation of "`x` kills every flank", which is
what an empty intersection of the killer sets gives — the machine's second settlement route.

The mathematical content is the finite check that the intersection is empty; this is the step that turns
that check into loneliness. -/
theorem lonely_of_some_flank_unkillable (hn4 : 4 ≤ n) {ds : Finset ℝ} {x : ℝ}
    (E : Finset ℝ) (P : ℝ → ℕ) (U : ℝ → Finset ℕ)
    (he0 : ∀ e ∈ E, 0 < e) (hUne : ∀ e ∈ E, (U e).Nonempty)
    (hlat : ∀ e ∈ E, ∀ d ∈ ds, d ≠ x → Int.fract ((P e : ℝ) * (d / e)) = 0)
    (hU : ∀ e ∈ E, ∀ r ∈ U e, ∀ d ∈ ds, d ≠ x →
      (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e r))
    (hsome : ∃ e ∈ E, Int.fract ((P e : ℝ) * (x / e)) = 0 →
      ∃ r ∈ U e, ∃ j : ℕ, (n : ℝ)⁻¹ ≤ circDist (x * flankOpening n e (r + j * P e))) :
    ∃ e ∈ E, ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  obtain ⟨e, heE, hfail⟩ := hsome
  exact ⟨e, heE, lonely_of_flank_unkillable hn4 (he0 e heE) (P e) (U e) (hUne e heE)
    (hlat e heE) (hU e heE) hfail⟩

/-- **Existence for the runner, from the empty-killer-intersection route.** -/
theorem stops_of_some_flank_unkillable (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {m x : ℝ} (hm : m ∈ ds) (E : Finset ℝ) (P : ℝ → ℕ) (U : ℝ → Finset ℕ)
    (he0 : ∀ e ∈ E, 0 < e) (hUne : ∀ e ∈ E, (U e).Nonempty)
    (hlat : ∀ e ∈ E, ∀ d ∈ ds, d ≠ x → Int.fract ((P e : ℝ) * (d / e)) = 0)
    (hU : ∀ e ∈ E, ∀ r ∈ U e, ∀ d ∈ ds, d ≠ x →
      (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e r))
    (hsome : ∃ e ∈ E, Int.fract ((P e : ℝ) * (x / e)) = 0 →
      ∃ r ∈ U e, ∃ j : ℕ, (n : ℝ)⁻¹ ≤ circDist (x * flankOpening n e (r + j * P e))) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  obtain ⟨e, heE, k, hk⟩ :=
    lonely_of_some_flank_unkillable hn4 E P U he0 hUne hlat hU hsome
  exact exists_fixed_of_lonely hpos hm (flankOpening_pos (he0 e heE) k) hk

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

/-! ### Proposition 6.10, the mixed pair

A rational and an irrational ratio never shadow a live flank together.  This needs no residue count
and no pigeonhole: the rational runner's verdict repeats with its own denominator `c`, so it is clear
on a whole residue class mod `c`, and `class_killer_int` (inside `lonely_opening_of_free_off_lattice`)
says that shadowing every opening of that class would force the irrational ratio onto the `c`-lattice.
Only the two lattice bridges below are new. -/

/-- **A ratio that is no ratio of integers is off every lattice.**  The hypothesis is irrationality
written out in the framework's own words, so this theorem needs no imported notion.  It is also
*stronger* than the irrational case: a rational ratio whose reduced denominator does not divide `P`
satisfies the conclusion too, and `shadowing_pair_cross_lattice` is where that matters. -/
theorem off_lattice_of_not_ratio {d e : ℝ}
    (h : ∀ a b : ℤ, b ≠ 0 → d / e ≠ (a : ℝ) / (b : ℝ)) {P : ℕ} (hP : 0 < P) :
    Int.fract ((P : ℝ) * (d / e)) ≠ 0 := by
  intro hf
  have hPz : (P : ℝ) * (d / e) = (⌊(P : ℝ) * (d / e)⌋ : ℝ) := by
    have := Int.fract_add_floor ((P : ℝ) * (d / e)); rw [hf] at this; linarith
  have hP0 : ((P : ℝ)) ≠ 0 := by positivity
  have hPne : ((P : ℤ)) ≠ 0 := by exact_mod_cast hP0
  refine h ⌊(P : ℝ) * (d / e)⌋ (P : ℤ) hPne ?_
  push_cast
  field_simp at hPz ⊢
  linarith [hPz]

/-- **Irrational ratios are covered, and are covered under that name.**

This corollary exists so that the coverage cannot be missed by a reader searching for the word.
`off_lattice_of_not_ratio` above is the real content and needs no import; this restates it for an
irrational ratio, which is the case a reader is most likely to come looking for.

**Irrational speeds are not an exception anywhere in this framework.**  The cascade and every
statement about it are real-valued throughout; `LRC/Cascade/Irrational.lean` carries worked cases —
`IrrationalDemo.all_lonely` for the speeds `1, 2, π, 4, …, 8`, whose `d_min = 4 − π` is irrational,
and `time_irrational`, which shows the isolation instant itself is irrational.  Manuscript §6.8
tabulates those alongside a `√2` cascade.  `Flanks.class_killer_int` covers rational and irrational
ratios in one case, with no rationality input at all. -/
theorem off_lattice_of_irrational_ratio {d e : ℝ} (hirr : Irrational (d / e)) {P : ℕ} (hP : 0 < P) :
    Int.fract ((P : ℝ) * (d / e)) ≠ 0 :=
  off_lattice_of_not_ratio ((irrational_iff_ne_rational _).mp hirr) hP

/-- **A runner whose ratio to the flank has denominator `c` is on the `c`-lattice.** -/
theorem on_lattice_of_ratio_den {d e : ℝ} {a : ℤ} {c : ℕ} (hc : 0 < c)
    (hrat : d / e = (a : ℝ) / (c : ℝ)) : Int.fract ((c : ℝ) * (d / e)) = 0 := by
  have hc0 : ((c : ℝ)) ≠ 0 := by positivity
  have : (c : ℝ) * (d / e) = ((a : ℤ) : ℝ) := by rw [hrat]; field_simp
  rw [this, Int.fract_intCast]

/-- **Proposition 6.10, the mixed pair.**  A live flank whose non-integer ratios are one rational (of
denominator `c`) and one off the `c`-lattice has a lonely opening, so the cascade stops.  Every other
runner has an integer ratio to the flank that `n` does not divide.  No count of residues is used. -/
theorem lonely_opening_of_lattice_and_free (hn4 : 4 ≤ n) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) {e y z : ℝ} (he : e ∈ ds) {a : ℤ} {c : ℕ} (hc : 0 < c)
    (hyrat : y / e = (a : ℝ) / (c : ℝ)) (hyfrac : Int.fract (y / e) ≠ 0)
    (hzoff : Int.fract ((c : ℝ) * (z / e)) ≠ 0)
    (hint : ∀ d ∈ ds, d ≠ y → d ≠ z → ∃ A : ℤ, d = A * e ∧ ¬ ((n : ℤ) ∣ A)) :
    ∃ k : ℕ, Lonely n ds (flankOpening n e k) := by
  have he0 := hpos e he
  -- the opening `r` at which the rational runner is clear
  have hf0 : 0 < Int.fract (y / e) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hyfrac)
  obtain ⟨r, hr⟩ := exists_clear_step (n := n) hn4 (c := (y / e) / n) hf0 (Int.fract_lt_one _)
  refine lonely_opening_of_free_off_lattice (n := n) (x := z) hn4 he0 c r ?_ ?_ hzoff
  · -- everything but `z` sits on the `c`-lattice
    intro d hd hdz
    by_cases hdy : d = y
    · subst hdy; exact on_lattice_of_ratio_den hc hyrat
    · obtain ⟨A, hA, -⟩ := hint d hd hdy hdz
      have : d / e = (A : ℝ) := by rw [hA]; field_simp
      rw [this, show (c : ℝ) * (A : ℝ) = (((c : ℤ) * A : ℤ) : ℝ) by push_cast; ring,
        Int.fract_intCast]
  · -- everything but `z` is clear at opening `r`
    intro d hd hdz
    by_cases hdy : d = y
    · subst hdy; rw [fractional_ratio_circDist he0]; exact hr
    · obtain ⟨A, hA, hnA⟩ := hint d hd hdy hdz
      exact (integer_ratio_clear_iff he0 hA r).2 hnA

/-- **The cascade stops** for such an arrangement. -/
theorem stops_of_lattice_and_free (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {m e y z : ℝ} (hm : m ∈ ds) (he : e ∈ ds) {a : ℤ} {c : ℕ} (hc : 0 < c)
    (hyrat : y / e = (a : ℝ) / (c : ℝ)) (hyfrac : Int.fract (y / e) ≠ 0)
    (hzoff : Int.fract ((c : ℝ) * (z / e)) ≠ 0)
    (hint : ∀ d ∈ ds, d ≠ y → d ≠ z → ∃ A : ℤ, d = A * e ∧ ¬ ((n : ℤ) ∣ A)) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  obtain ⟨k, hk⟩ :=
    lonely_opening_of_lattice_and_free hn4 hpos he hc hyrat hyfrac hzoff hint
  exact exists_fixed_of_lonely hpos hm (flankOpening_pos (hpos e he) k) hk

/-! ### Proposition 6.10, the rational pair: the denominators must agree

The manuscript proves this by a residue count over all denominators.  Most of it needs no
count.  If two runners shadow a live flank between them and each is on a lattice, then each
is forced onto the *other's* lattice, by `class_killer_int` alone: the first is clear on a
whole residue class mod `P`, so the second must shadow that entire class, which puts it on
the `P`-lattice.  For reduced denominators this says `c₂ ∣ c₁` and `c₁ ∣ c₂`, hence `c₁ = c₂`.
Only the last step -- that two runners of one common denominator `c` cover all `c` residues
only when `c = 2` -- is a count, and it is a count over a single denominator. -/

/-- **A shadowing pair lies on each other's lattice.**  No residue count is used. -/
theorem shadowing_pair_cross_lattice (hn4 : 4 ≤ n) {e y z : ℝ} (he0 : 0 < e) {P Q : ℕ}
    (hylat : Int.fract ((P : ℝ) * (y / e)) = 0)
    (hzlat : Int.fract ((Q : ℝ) * (z / e)) = 0)
    (hyclear : ∃ r : ℕ, (n : ℝ)⁻¹ ≤ circDist (y * flankOpening n e r))
    (hzclear : ∃ r : ℕ, (n : ℝ)⁻¹ ≤ circDist (z * flankOpening n e r))
    (hshadow : ∀ k : ℕ, inWay n y (flankOpening n e k) ∨ inWay n z (flankOpening n e k)) :
    Int.fract ((P : ℝ) * (z / e)) = 0 ∧ Int.fract ((Q : ℝ) * (y / e)) = 0 := by
  constructor
  · -- `y` is clear on the whole class `r + jP`, so `z` must shadow it
    obtain ⟨r, hr⟩ := hyclear
    refine class_killer_int (n := n) hn4 he0 P r (fun j => ?_)
    have hy : ¬ inWay n y (flankOpening n e (r + j * P)) := by
      rw [inWay, circDist_periodic_of_lattice he0 hylat r j]; exact not_lt.mpr hr
    exact (hshadow (r + j * P)).resolve_left hy
  · obtain ⟨r, hr⟩ := hzclear
    refine class_killer_int (n := n) hn4 he0 Q r (fun j => ?_)
    have hz : ¬ inWay n z (flankOpening n e (r + j * Q)) := by
      rw [inWay, circDist_periodic_of_lattice he0 hzlat r j]; exact not_lt.mpr hr
    exact (hshadow (r + j * Q)).resolve_right hz

/-! ### The band criterion at any opening — Theorem 4.8 carried past `k = 0`

Theorem 4.8 (`Construction8.ratio_condition`) decides a difference at the flank's **bound**,
`k = 0`.  The manuscript's mirror of it states the criterion at every opening: at flank `e`'s
`k`-th opening runner `d` is clear exactly when the ratio `d/e` lies in
`⋃_M [(nM+1)/(nk+1), (nM+n−1)/(nk+1)]`.  That is the same object at a different `k`, and it is
proved here once for all `k`, with `k = 0` recovering 4.8.

The point is coverage.  Measured on difference sets (`experiments/n8/small_k_theorem_v1`),
`k = 0` alone settles about 50% of random 7-sets; allowing `k ≤ 2` at any flank settles about
91%.  This does **not** prove Existence — the required `k` is unbounded
(`experiments/n8/bounded_k_attack_v1` reaches `k = 369`) — it widens what is decided. -/

/-- **A difference is clear at flank `e`'s `k`-th opening when its ratio sits in the band.**
`k = 0` is Theorem 4.8. -/
theorem clear_at_opening_of_band {e d : ℝ} (he : 0 < e) (k : ℕ) (M : ℤ)
    (h1 : (n : ℝ) * (M : ℝ) + 1 ≤ (d / e) * ((n : ℝ) * (k : ℝ) + 1))
    (h2 : (d / e) * ((n : ℝ) * (k : ℝ) + 1) ≤ (n : ℝ) * (M : ℝ) + (n : ℝ) - 1) :
    (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e k) := by
  have hn0 : (0 : ℝ) < n := n_pos
  set y : ℝ := (d / e) * ((n : ℝ) * (k : ℝ) + 1) / (n : ℝ) - (M : ℝ) with hy
  have hsplit : d * flankOpening n e k = y + (M : ℝ) := by
    rw [position_at_flank he, hy]; field_simp; ring
  have hninv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have key : (n : ℝ) * y = (d / e) * ((n : ℝ) * (k : ℝ) + 1) - (n : ℝ) * (M : ℝ) := by
    rw [hy]; field_simp
  -- `n·y ≥ 1 = n·(1/n)` and `n > 0`, so `y ≥ 1/n`; likewise at the top of the band
  have hy1 : (n : ℝ)⁻¹ ≤ y := by
    have hge : (1 : ℝ) ≤ (n : ℝ) * y := by rw [key]; linarith
    have := mul_le_mul_of_nonneg_left hge (le_of_lt (inv_pos.mpr hn0))
    rw [← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul, mul_one] at this
    linarith
  have hy2 : y ≤ 1 - (n : ℝ)⁻¹ := by
    have hle : (n : ℝ) * y ≤ (n : ℝ) - 1 := by rw [key]; linarith
    have := mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hn0))
    rw [← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul, mul_sub, mul_one,
      inv_mul_cancel₀ hn0.ne'] at this
    exact this
  rw [hsplit]
  exact circDist_ge_of_band M hy1 hy2

/-- **The converse: clear at an opening forces the ratio into a band.**  Together with
`clear_at_opening_of_band` this makes the band criterion an `iff`, which is how the manuscript
states it.  Taking `M = ⌊·⌋` of the scaled ratio, `circDist ≥ 1/n` says exactly that the scaled
ratio sits between `nM + 1` and `nM + n − 1`. -/
theorem band_of_clear_at_opening {e d : ℝ} (he : 0 < e) (k : ℕ)
    (hclear : (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e k)) :
    ∃ M : ℤ, (n : ℝ) * (M : ℝ) + 1 ≤ (d / e) * ((n : ℝ) * (k : ℝ) + 1) ∧
      (d / e) * ((n : ℝ) * (k : ℝ) + 1) ≤ (n : ℝ) * (M : ℝ) + (n : ℝ) - 1 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hninv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  set y : ℝ := d * flankOpening n e k with hy
  have hscale : (d / e) * ((n : ℝ) * (k : ℝ) + 1) = (n : ℝ) * y := by
    rw [hy, position_at_flank he]; field_simp
  have hfr : Int.fract y = y - (⌊y⌋ : ℝ) := rfl
  have h1 : (n : ℝ)⁻¹ ≤ Int.fract y := le_trans hclear (min_le_left _ _)
  have h2 : (n : ℝ)⁻¹ ≤ 1 - Int.fract y := le_trans hclear (min_le_right _ _)
  have hA : (1 : ℝ) ≤ (n : ℝ) * Int.fract y := by
    have := mul_le_mul_of_nonneg_left h1 hn0.le; rwa [hninv] at this
  have hB : (n : ℝ) * Int.fract y ≤ (n : ℝ) - 1 := by
    have := mul_le_mul_of_nonneg_left h2 hn0.le
    rw [mul_sub, mul_one, hninv] at this; linarith
  rw [hfr, mul_sub] at hA hB
  exact ⟨⌊y⌋, by linarith [hA, hscale], by linarith [hB, hscale]⟩

/-- **It recovers Theorem 4.8 at `k = 0`.**  Taking `M = 0` and `k = 0` the band condition reads
`e ≤ d ≤ (n−1)·e`, which at `n = 8` is `d_min ≤ d ≤ 7·d_min` — the hypothesis of
`Construction8.ratio_condition`.  Stated so the relationship is checkable rather than asserted. -/
theorem clear_at_bound_of_ratio {e d : ℝ} (he : 0 < e) (h1 : e ≤ d) (h7 : d ≤ ((n : ℝ) - 1) * e) :
    (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e 0) := by
  have hde1 : (1 : ℝ) ≤ d / e := (one_le_div he).mpr h1
  have hde7 : d / e ≤ (n : ℝ) - 1 := by rw [div_le_iff₀ he]; linarith
  refine clear_at_opening_of_band he 0 0 ?_ ?_ <;> push_cast <;> nlinarith [hde1, hde7]

/-- **The mirror, at the other end: `k = 1` at the largest flank.**  Theorem 4.8 is the band at
`(e = d_min, k = 0)` with `M = 0`, which reads `e ≤ d ≤ (n−1)·e`.  Its mirror is the SAME band at
`(e = d_max, k = 1)` with `M = 0`, which reads `e/(n+1) ≤ d ≤ (n−1)·e/(n+1)` — at `n = 8`,
`d_max/9 ≤ d ≤ 7·d_max/9`.  Stated so that what mirrors what is checkable, not asserted: the two
are one criterion at two `(flank, opening)` pairs, not two theorems. -/
theorem clear_at_first_opening_of_ratio {e d : ℝ} (he : 0 < e)
    (h1 : e ≤ ((n : ℝ) + 1) * d) (h7 : ((n : ℝ) + 1) * d ≤ ((n : ℝ) - 1) * e) :
    (n : ℝ)⁻¹ ≤ circDist (d * flankOpening n e 1) := by
  have hn0 : (0 : ℝ) < n := n_pos
  refine clear_at_opening_of_band he 1 0 ?_ ?_
  · push_cast
    rw [div_mul_eq_mul_div, le_div_iff₀ he]
    nlinarith [h1, he, hn0]
  · push_cast
    rw [div_mul_eq_mul_div, div_le_iff₀ he]
    nlinarith [h7, he, hn0]

/-- **The subject is lonely at flank `e`'s `k`-th opening when every difference's ratio sits in
some band.**  This is the form that decides a difference set. -/
theorem lonely_at_opening_of_bands {ds : Finset ℝ} {e : ℝ} (he : 0 < e) (k : ℕ)
    (h : ∀ d ∈ ds, ∃ M : ℤ, (n : ℝ) * (M : ℝ) + 1 ≤ (d / e) * ((n : ℝ) * (k : ℝ) + 1) ∧
      (d / e) * ((n : ℝ) * (k : ℝ) + 1) ≤ (n : ℝ) * (M : ℝ) + (n : ℝ) - 1) :
    Lonely n ds (flankOpening n e k) := by
  intro d hd
  obtain ⟨M, h1, h2⟩ := h d hd
  exact clear_at_opening_of_band he k M h1 h2

/-- **Existence for a difference set decided at a single opening.**  If some flank of `ds` has an
opening at which every ratio lies in a band, the subject has a lonely instant. -/
theorem exists_lonely_of_bands {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {e : ℝ} (he : e ∈ ds)
    (k : ℕ)
    (h : ∀ d ∈ ds, ∃ M : ℤ, (n : ℝ) * (M : ℝ) + 1 ≤ (d / e) * ((n : ℝ) * (k : ℝ) + 1) ∧
      (d / e) * ((n : ℝ) * (k : ℝ) + 1) ≤ (n : ℝ) * (M : ℝ) + (n : ℝ) - 1) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s :=
  ⟨flankOpening n e k, flankOpening_pos (hpos e he) k, lonely_at_opening_of_bands (hpos e he) k h⟩

/-! ### The census is one theorem, not four thousand

The artefact carries 4,413 census families, each a separate declaration.  They are **not**
4,413 facts.  Every one is the same statement — every difference lies in the band at some
`(e, k)` — instantiated at one of only 169 distinct `(flank, opening)` pairs, of which a
greedy cover needs 78 (`experiments/n8/census_unification_v1`).  The criterion is
`clear_at_opening_of_band` above; what follows bounds the search over `k`.

So the census's own split — 1,341 families "clear at the bound" against 3,072 "decided at a
later opening" — is a **false division**.  It is one criterion at different `k`, not two
phenomena. -/

/-- **At an integer flank the verdict repeats with period `e`.**  A corollary of
`circDist_periodic_of_lattice` at `P = e`, since `fract (e · (d/e)) = fract d = 0` when `d` is a
whole number.  Consequently a search over openings at an integer flank need never pass `k = e`:
the openings `0, …, e−1` already carry every verdict the flank can give. -/
theorem circDist_periodic_of_int_flank {a b : ℤ} (hb : 0 < b) (k j : ℕ) :
    circDist ((a : ℝ) * flankOpening n (b : ℝ) (k + j * b.toNat))
      = circDist ((a : ℝ) * flankOpening n (b : ℝ) k) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  refine circDist_periodic_of_lattice hb0 ?_ k j
  have hbn : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hb.le)
  rw [hbn]
  have : (b : ℝ) * ((a : ℝ) / (b : ℝ)) = ((a : ℤ) : ℝ) := by field_simp
  rw [this, Int.fract_intCast]

/-- **Loneliness at an integer flank is periodic in the opening, with period the flank.**  The
whole search collapses to `k < e`. -/
theorem lonely_periodic_of_int_flank {ds : Finset ℝ} {b : ℤ} (hb : 0 < b)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) (k j : ℕ) :
    Lonely n ds (flankOpening n (b : ℝ) (k + j * b.toNat))
      ↔ Lonely n ds (flankOpening n (b : ℝ) k) := by
  constructor <;> intro h d hd <;> obtain ⟨a, rfl⟩ := hint d hd
  · rw [← circDist_periodic_of_int_flank hb k j]; exact h _ hd
  · rw [circDist_periodic_of_int_flank hb k j]; exact h _ hd

/-- **Loneliness over whole-number differences is a FINITE search.**  `lonely_iff_exists_flank`
gives an unbounded `∃ k`; at an integer flank the verdict repeats with period `e`, so the search
collapses to `k < e`.  The subject is lonely somewhere **iff** it is lonely at one of the
`∑_{e ∈ ds} e` openings with `k < e`.

This is what the census was doing.  Its 4,413 declarations are this criterion evaluated on 4,413
particular difference sets; with the criterion stated, enumerating more of them adds nothing.
It does **not** prove `ExistenceAt8`, which quantifies over infinitely many `ds` — a decision
procedure decides each case, it does not discharge a universal. -/
theorem lonely_iff_bounded_search {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    (∃ s, 0 < s ∧ Lonely n ds s) ↔
      ∃ e ∈ ds, ∃ k : ℕ, (k : ℝ) < e ∧ Lonely n ds (flankOpening n e k) := by
  rw [lonely_iff_exists_flank hpos hne]
  constructor
  · rintro ⟨e, he, k, hk⟩
    obtain ⟨b, rfl⟩ := hint e he
    have hb0 : (0 : ℝ) < (b : ℝ) := hpos _ he
    have hbZ : 0 < b := by exact_mod_cast hb0
    have hbN : 0 < b.toNat := by omega
    refine ⟨(b : ℝ), he, k % b.toNat, ?_, ?_⟩
    · have : ((k % b.toNat : ℕ) : ℝ) < ((b.toNat : ℕ) : ℝ) := by
        exact_mod_cast Nat.mod_lt _ hbN
      rwa [show ((b.toNat : ℕ) : ℝ) = (b : ℝ) from
        (by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hbZ.le))] at this
    · have hsplit : k = k % b.toNat + (k / b.toNat) * b.toNat := (Nat.mod_add_div' k _).symm
      rw [hsplit] at hk
      exact (lonely_periodic_of_int_flank hbZ hint _ _).mp hk
  · rintro ⟨e, he, k, -, hk⟩; exact ⟨e, he, k, hk⟩

/-! ### The two symmetries the framework uses and had not stated

Both are elementary and both were relied on before being proved.  `circDist` is **even**, which
is what makes a difference's sign irrelevant — and so makes "the slowest runner" a labelling
convention rather than a fact about the arrangement.  And loneliness is **scale-free**: only the
ratios matter, which is what licenses reading every difference against `d_min`. -/

/-- **`circDist` is even.**  So a difference and its negation are interchangeable, and the order
of the speeds is a convention. -/
theorem circDist_neg (x : ℝ) : circDist (-x) = circDist x := by
  unfold circDist
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · rw [h, Int.fract_neg_eq_zero.mpr h]
  · rw [Int.fract_neg h, min_comm]
    congr 1 <;> ring

/-- **Loneliness is scale-free.**  Rescaling every difference by `c > 0` and the instant by `1/c`
leaves every reading, and so every verdict, unchanged.  This is what lets the framework normalise
by `d_min` and work with ratios. -/
theorem lonely_smul {ds : Finset ℝ} {c s : ℝ} (hc : 0 < c) :
    Lonely n (ds.image (fun d => c * d)) (s / c) ↔ Lonely n ds s := by
  constructor
  · intro h d hd
    have := h (c * d) (Finset.mem_image_of_mem _ hd)
    rwa [show c * d * (s / c) = d * s by field_simp] at this
  · intro h d' hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [show c * d * (s / c) = d * s by field_simp]
    exact h d hd

/-- **In the way is the complement of the band.**  The clear criterion decides both sides: a
difference is in the way at flank `e`'s `k`-th opening exactly when its scaled ratio is NOT in any
band, i.e. within `1` of a multiple of `n`. -/
theorem inWay_at_opening_iff_not_band {e d : ℝ} (he : 0 < e) (k : ℕ) :
    inWay n d (flankOpening n e k) ↔
      ¬ ∃ M : ℤ, (n : ℝ) * (M : ℝ) + 1 ≤ (d / e) * ((n : ℝ) * (k : ℝ) + 1) ∧
        (d / e) * ((n : ℝ) * (k : ℝ) + 1) ≤ (n : ℝ) * (M : ℝ) + (n : ℝ) - 1 := by
  unfold inWay
  constructor
  · intro hlt ⟨M, h1, h2⟩
    exact absurd (clear_at_opening_of_band he k M h1 h2) (not_le.mpr hlt)
  · intro hno
    by_contra hge
    exact hno (band_of_clear_at_opening he k (not_lt.mp hge))

/-- **Time reversal.**  Loneliness is symmetric about zero: the subject is lonely at `s` exactly
when it is lonely at `−s`.  Immediate from `circDist_neg`, and it says the lonely set of an
arrangement is a symmetric set — half of it lies at negative times and carries no new information. -/
theorem lonely_neg {ds : Finset ℝ} {s : ℝ} : Lonely n ds (-s) ↔ Lonely n ds s := by
  constructor <;> (intro h d hd; have := h d hd)
  · rwa [show d * -s = -(d * s) by ring, circDist_neg] at this
  · rwa [← circDist_neg (d * s), ← show d * -s = -(d * s) by ring] at this

/-- **A flank sits exactly on the boundary at its own openings.**  `circDist (e · flankOpening n e k)`
is exactly `1/n`, never more and never less.  This is why the zones are OPEN: the flank is clear at
its own opening by the `≤` in `Lonely`, and would not be under a strict inequality.  The boundary
discipline of §1.2 is load-bearing exactly here. -/
theorem circDist_flank_self {e : ℝ} (he : 0 < e) (k : ℕ) :
    circDist (e * flankOpening n e k) = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have h : e * flankOpening n e k = ((k : ℤ) : ℝ) + (n : ℝ)⁻¹ := by
    unfold flankOpening; field_simp; push_cast; ring
  rw [h, add_comm, circDist_add_int]
  unfold circDist
  have hh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have h1 : Int.fract ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ :=
    Int.fract_eq_self.mpr ⟨by positivity, by norm_num at hh ⊢; linarith⟩
  rw [h1]
  exact min_eq_left (by norm_num at hh ⊢; linarith)

/-! ### The depth of a runner at an opening is quantised

The cascade's instant is always some runner's opening, `(k + 1/n)/b`.  When the speeds are whole
numbers, a second runner's **depth** into its blocking zone at that instant — the quantity
`a·t − N + 1/n`, which is `0` at the near edge of the zone and `2/n` at the far edge — cannot take
an arbitrary value.  It is an integer multiple of `1/(n·b)`, so it is either exactly zero or at
least `1/(n·b)`.

This answers a candidate lemma from another session, which asked for a **universal** floor `c_* > 0`
on that depth.  There is no universal floor — over real speeds the depth reaches `6·10⁻¹³` and below
(`experiments/n8/long_return_depth_v1`).  Over whole-number speeds there is one, and this is it:
`1/(n·b)`, set by the **previous setter** `b`.  Bounded speeds give a floor; unbounded speeds do
not, and the real-speed counterexamples are the `b → ∞` limit.  Checked tight on 13,603 moves in
exact arithmetic (`experiments/n8/return_depth_floor_v1`), the bound being attained. -/

/-- **The depth is an integer over `n·b`.** -/
theorem depth_eq_int_div {a b : ℤ} (hb : 0 < b) (k : ℕ) (N : ℤ) :
    (a : ℝ) * flankOpening n (b : ℝ) k - (N : ℝ) + (n : ℝ)⁻¹
      = ((a * ((n : ℤ) * (k : ℤ) + 1) - N * (n : ℤ) * b + b : ℤ) : ℝ) / ((n : ℝ) * (b : ℝ)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  unfold flankOpening
  push_cast
  field_simp

/-- **So a positive depth is at least `1/(n·b)`.**  `b` is the speed of the runner whose opening the
cascade is currently at — the previous setter. -/
theorem depth_floor {a b : ℤ} (hb : 0 < b) (k : ℕ) (N : ℤ)
    (hpos : 0 < (a : ℝ) * flankOpening n (b : ℝ) k - (N : ℝ) + (n : ℝ)⁻¹) :
    ((n : ℝ) * (b : ℝ))⁻¹ ≤ (a : ℝ) * flankOpening n (b : ℝ) k - (N : ℝ) + (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hnb : (0 : ℝ) < (n : ℝ) * (b : ℝ) := mul_pos hn0 hb0
  set K : ℤ := a * ((n : ℤ) * (k : ℤ) + 1) - N * (n : ℤ) * b + b with hK
  rw [depth_eq_int_div hb k N] at hpos ⊢
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    by_contra h
    push Not at h
    exact absurd hpos (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg h hnb.le))
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have : (0 : ℤ) < K := by exact_mod_cast hKpos
    exact_mod_cast this
  rw [inv_eq_one_div]
  gcongr

end Flanks
