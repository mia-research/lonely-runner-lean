import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.SmallN.IntLRC_5_Bienia

/-!
# Bohman–Holzman–Kleitman 2001 — Foundations

Definitions and elementary bridge lemmas shared across the BHK formalisation.

* `BHK.bhkB`            — open unsafe set near integers `⋃_k (k-1/6, k+1/6)`
* `BHK.bhkBunion`       — `⋃_i x_i · B` (the conjecture asserts this `≠ ℝ⁺`)
* `BHK.unsafeOf i`      — set of times `t` with `v_i · t ∈ bhkB`
* `BHK.mem_bhkB_iff`    — bridge to `circDist x < 1/6`
* `BHK.mem_unsafeOf_iff`— bridge for `unsafeOf`
* `BHK.bhkRectangle`    — the standard 2-torus rectangle from BHK §3
-/

open MeasureTheory Set

namespace BHK

/-- BHK's `B`: the open unsafe set near integers,
    `B = {x : ℝ | ∃ k : ℤ, |x − k| < 1/6}`. -/
def bhkB : Set ℝ := { x : ℝ | ∃ k : ℤ, |x - (k : ℝ)| < 1 / 6 }

/-- BHK's union `𝓑 = ⋃_i x_i · B`. -/
noncomputable def bhkBunion (speeds : Fin 5 → ℕ) : Set ℝ :=
  ⋃ i, { t : ℝ | (speeds i : ℝ) * t ∈ bhkB }

/-- The set of times where runner `i` is "near the origin" (within `1/6`)
    on the circle. -/
def unsafeOf (speeds : Fin 5 → ℕ) (i : Fin 5) : Set ℝ :=
  { t : ℝ | (speeds i : ℝ) * t ∈ bhkB }

/-- Bridge between BHK's interval formulation and our `circDist` formulation:
    `x ∈ bhkB` iff `circDist x < 1/6`. -/
theorem mem_bhkB_iff (x : ℝ) : x ∈ bhkB ↔ circDist x < 1 / 6 := by
  constructor
  · rintro ⟨k, hk⟩
    have hmem : (k : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨k, rfl⟩
    rw [circDist_eq_infDist]
    calc Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))
        ≤ dist x (k : ℝ) := Metric.infDist_le_dist_of_mem hmem
      _ = |x - (k : ℝ)| := Real.dist_eq _ _
      _ < 1 / 6 := hk
  · intro hcd
    unfold circDist at hcd
    rcases min_lt_iff.mp hcd with hL | hR
    · refine ⟨⌊x⌋, ?_⟩
      have hfl_le : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      have hfract : x - (⌊x⌋ : ℝ) = Int.fract x := by
        unfold Int.fract; ring
      rw [abs_of_nonneg (by linarith), hfract]; exact hL
    · refine ⟨⌊x⌋ + 1, ?_⟩
      have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
      have hfract_lt_one : Int.fract x < 1 := Int.fract_lt_one x
      have hcast : ((⌊x⌋ + 1 : ℤ) : ℝ) = (⌊x⌋ : ℝ) + 1 := by push_cast; ring
      have hdiff : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract x) := by
        rw [hcast]; unfold Int.fract; ring
      rw [hdiff, abs_neg, abs_of_nonneg (by linarith)]; exact hR

/-- Translated bridge: `t ∈ unsafeOf speeds i` iff `circDist (v_i · t) < 1/6`. -/
theorem mem_unsafeOf_iff (speeds : Fin 5 → ℕ) (i : Fin 5) (t : ℝ) :
    t ∈ unsafeOf speeds i ↔ circDist ((speeds i : ℝ) * t) < 1 / 6 := by
  unfold unsafeOf; exact mem_bhkB_iff _

/-- The 2-dimensional torus rectangle `R = {(u,v) : 0 ≤ {u - x₁} ≤ α ∧ 0 ≤ {v - x₂} ≤ β}`
    from BHK §3, encoded as a subset of `ℝ × ℝ`. -/
def bhkRectangle (x₁ x₂ α β : ℝ) : Set (ℝ × ℝ) :=
  { p | 0 ≤ Int.fract (p.1 - x₁) ∧ Int.fract (p.1 - x₁) ≤ α ∧
        0 ≤ Int.fract (p.2 - x₂) ∧ Int.fract (p.2 - x₂) ≤ β }

/-! ## Structural facts about `bhkB` and `unsafeOf`

These characterise `bhkB` as a union of open intervals around integers and
give explicit length bounds — both used downstream in `bhk_lemma_4` and the
case branches of §§5–8. -/

/-- `bhkB` is the disjoint union of open intervals of length `1/3` centred at
    each integer: `bhkB = ⋃_k (k - 1/6, k + 1/6)`. -/
theorem bhkB_eq_iUnion_Ioo :
    bhkB = ⋃ k : ℤ, Ioo ((k : ℝ) - 1 / 6) ((k : ℝ) + 1 / 6) := by
  ext x
  simp only [bhkB, mem_iUnion, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · have := neg_lt_of_abs_lt hk; linarith
    · have := lt_of_abs_lt hk; linarith
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, ?_⟩
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩

/-- `unsafeOf i` rescaled: `t ∈ unsafeOf i` iff `(v_i · t) ∈ bhkB`. -/
theorem mem_unsafeOf_iff_bhkB (speeds : Fin 5 → ℕ) (i : Fin 5) (t : ℝ) :
    t ∈ unsafeOf speeds i ↔ (speeds i : ℝ) * t ∈ bhkB := Iff.rfl

end BHK
