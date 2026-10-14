import LonelyRunner.LRC.Spec.PinchReflectionN

/-!
# Partial reflection: reflect only the readings that share a period

2026-09-29.  Running record: `RUNNING_LOG_order8_v1.md` E181.

`PinchReflectionN.reflected_right_inequalities` reflects EVERY reading around a common period `(λ+1)·t`.  Its slope
reversal (`active_slope_reversal`) only ever uses the two active readings.  Here only the readings in `R ⊆ S` are
reflected, each whole at `(λ+1)·t` (for instance just the pinching pair, around its own period, which is typically much
shorter than the period of all seven).  Every other reading keeps a lap label of its own and needs only to be strictly
clear at the reflected instant `λ·t`.

`partial_reflected_right_inequalities`: then the reflected lap assignment satisfies every pairwise window inequality on a
right neighbourhood of the pinch.  The one new step: at the reflected instant a slack can be zero only if both of its
readings sit on band boundaries there, and the unreflected readings are strictly inside theirs, so every zero slack is
between two reflected readings, where `active_slope_reversal` applies.  The full reflection is the case `R = S`.

Local transport only: nothing here says the unreflected readings are clear at `λ·t`; that is a hypothesis, checked
against the cascade in `experiments/nN/redo/partial_reflection_v1.py`.  Everything here is proved; no `sorry`, no
`native_decide`.
-/

namespace LRC.PartialReflection

open LRC.PinchReflection

variable {ι : Type*}

/-- **Partial reflection.**  Reflect the readings in `R` (each whole at `(λ+1)·t`) around that period; give every other
reading its own label, strictly clear at `λ·t`.  If the old labels were feasible just before (`hleft`, on `R`), the new
labels satisfy every pairwise window inequality throughout a right neighbourhood. -/
theorem partial_reflected_right_inequalities (S R : Finset ι) (hS : S.Nonempty)
    (d v : ι → ℝ) (q P lab : ι → ℤ) {t lam delta : ℝ}
    (hd : ∀ i ∈ S, 0 < d i) (hlam : 0 < lam) (hdelta : 0 < delta)
    (hP : ∀ i ∈ R, (P i : ℝ) = (lam + 1) * d i * t)
    (hlab : ∀ i ∈ R, lab i = P i - q i - 1)
    (hband : ∀ i ∈ R, (q i : ℝ) + 1/8 ≤ d i * t ∧ d i * t ≤ q i + 7/8)
    (hleft : ∀ i ∈ R, ∀ j ∈ R,
      ((q i : ℝ) + 1/8) * (d j - delta * v j) ≤ ((q j : ℝ) + 7/8) * (d i - delta * v i))
    (hfree : ∀ i ∈ S, i ∉ R →
      (lab i : ℝ) + 1/8 < d i * (lam * t) ∧ d i * (lam * t) < lab i + 7/8) :
    ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e → ∀ i ∈ S, ∀ j ∈ S,
      ((lab i : ℝ) + 1/8) * (d j + h * v j) ≤ ((lab j : ℝ) + 7/8) * (d i + h * v i) := by
  classical
  -- every reading, reflected or not, is in its band at the reflected instant
  have hb : ∀ i ∈ S, (lab i : ℝ) + 1/8 ≤ d i * (lam * t) ∧ d i * (lam * t) ≤ lab i + 7/8 := by
    intro i hi
    by_cases hr : i ∈ R
    · rw [hlab i hr]
      exact reflected_band (hP i hr) (hband i hr).1 (hband i hr).2
    · exact ⟨(hfree i hi hr).1.le, (hfree i hi hr).2.le⟩
  let C := fun p : ι × ι => ((lab p.2 : ℝ) + 7/8) * d p.1 - ((lab p.1 : ℝ) + 1/8) * d p.2
  let B := fun p : ι × ι => ((lab p.2 : ℝ) + 7/8) * v p.1 - ((lab p.1 : ℝ) + 1/8) * v p.2
  have hC : ∀ p ∈ S ×ˢ S, 0 ≤ C p := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    have h1 := mul_le_mul_of_nonneg_left (hb j hj).2 (hd i hi).le
    have h2 := mul_le_mul_of_nonneg_left (hb i hi).1 (hd j hj).le
    dsimp [C]
    nlinarith
  have hB : ∀ p ∈ S ×ˢ S, C p = 0 → 0 ≤ B p := by
    rintro ⟨i, j⟩ hp hz
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    dsimp [C] at hz
    -- a zero slack puts both readings on boundaries, so both are reflected
    have hjR : j ∈ R := by
      by_contra hjR
      have h1 := mul_lt_mul_of_pos_left (hfree j hj hjR).2 (hd i hi)
      have h2 := mul_le_mul_of_nonneg_left (hb i hi).1 (hd j hj).le
      nlinarith
    have hiR : i ∈ R := by
      by_contra hiR
      have h1 := mul_lt_mul_of_pos_left (hfree i hi hiR).1 (hd j hj)
      have h2 := mul_le_mul_of_nonneg_left (hb j hj).2 (hd i hi).le
      nlinarith
    rw [hlab i hiR, hlab j hjR] at hz
    have he := reflected_slack (hP j hjR) (hP i hiR) (qi := q j) (qj := q i)
    have hold : ((q i : ℝ) + 7/8) * d j - ((q j : ℝ) + 1/8) * d i = 0 := by
      rwa [he] at hz
    obtain ⟨hl, hu⟩ := active_boundaries (hd j hj) (hd i hi)
      (hband j hjR).1 (hband i hiR).2 hold
    have hbv : ((q i : ℝ) + 7/8) * v j - ((q j : ℝ) + 1/8) * v i ≤ 0 := by
      apply active_slope_nonpos hdelta hold
      nlinarith [hleft j hjR i hiR]
    dsimp [B]
    rw [hlab i hiR, hlab j hjR, active_slope_reversal (hP j hjR) (hP i hiR) hl hu]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hlam.le) hbv
  obtain ⟨e, he, hw⟩ := affine_right (S ×ˢ S) (hS.product hS) C B hC hB
  refine ⟨e, he, ?_⟩
  intro h hh heh i hi j hj
  have hw' := hw h hh heh (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
  dsimp [C, B] at hw'
  nlinarith

end LRC.PartialReflection
