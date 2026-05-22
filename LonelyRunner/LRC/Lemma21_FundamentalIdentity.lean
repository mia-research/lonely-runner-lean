import LonelyRunner.LRC.Defs

/-!
# Lemma 2.1 — Fundamental Identity

Source: `lrc_proof_v11_draft.md` §2.4.

**Statement:** For any integers `a ≥ 1`, `b ≥ 1`, and any real `t`:
  `Int.fract (a * Int.fract (b * t)) = Int.fract (a * b * t)`

**Proof idea:** `Int.fract (b * t) = b * t - ⌊b * t⌋`, so
  `a * Int.fract (b * t) = a * b * t - a * ⌊b * t⌋`.
Since `a * ⌊b * t⌋ ∈ ℤ`, taking fractional parts gives the result.

This is the key algebraic engine used in Theorems 10.1 and 11.1.
-/


/-! ## §2.4  Fundamental Identity -/

/-- **Lemma 2.1** (Fundamental Identity).
    For natural numbers `a`, `b` and any real `t`:
    `{a · {b·t}} = {a·b·t}` where `{·}` denotes `Int.fract`. -/
theorem fundamental_identity (a b : ℕ) (t : ℝ) :
    Int.fract ((a : ℝ) * Int.fract ((b : ℝ) * t)) =
    Int.fract ((a : ℝ) * ((b : ℝ) * t)) := by
  -- Proof: a * {b*t} = a*b*t - a * ⌊b*t⌋, and a * ⌊b*t⌋ ∈ ℤ.
  conv_lhs =>
    rw [show (a : ℝ) * Int.fract ((b : ℝ) * t) =
          (a : ℝ) * ((b : ℝ) * t) - ↑((a : ℤ) * ⌊(b : ℝ) * t⌋) by
      simp only [Int.fract, Int.cast_mul, Int.cast_natCast, Int.cast_floor_eq]
      push_cast
      ring]
  -- Now apply Int.fract_sub_int or derive via Int.fract_add_int
  rw [sub_eq_add_neg, ← Int.cast_neg]
  -- BLOCKER: Need `Int.fract_add_int` or `Int.fract_int_add` for the final step.
  -- In Mathlib: Int.fract_add_int : Int.fract (a + ↑n) = Int.fract a
  -- The form we need: Int.fract (x + ↑(-m)) = Int.fract x  (m : ℤ)
  -- MATHLIB_SEARCH: `Int.fract_add_int`, `Int.fract_int_add`, `Int.fract_sub_int`
  -- STATUS: sorry — the tactic proof needs `Int.fract_add_int` applied correctly
  sorry

/-- Alternate form of Lemma 2.1 with `V = a*b` written directly. -/
theorem fundamental_identity' (p q : ℕ) (t : ℝ) :
    Int.fract ((q : ℝ) * Int.fract ((p : ℝ) * t)) =
    Int.fract ((p : ℝ) * ((q : ℝ) * t)) := by
  have := fundamental_identity q p t
  linarith [this]  -- just permuting multiplication
  -- BLOCKER: `linarith` won't work here; need `ring_nf` + the identity
  -- STATUS: sorry
  sorry

/-- **Corollary 2.2.** For integers `a, b ≥ 1` and real `t`:
    `circDist (a * Int.fract (b * t)) = circDist (a * b * t)`. -/
theorem circDist_fundamental (a b : ℕ) (t : ℝ) :
    circDist ((a : ℝ) * Int.fract ((b : ℝ) * t)) =
    circDist ((a : ℝ) * ((b : ℝ) * t)) := by
  -- `circDist` depends only on `Int.fract`, and Lemma 2.1 equates the fracts.
  unfold circDist
  congr 1
  · exact fundamental_identity a b t
  · congr 1; exact fundamental_identity a b t

/-- **Corollary 2.2 (norm form).**
    `‖V·t‖ ≥ 1/n` iff `‖q · {p·t}‖ ≥ 1/n`, where `V = p*q`. -/
theorem goodSet_rewrite_via_fract (p q n : ℕ) (t : ℝ) :
    t ∈ goodSet (p * q) n ↔
    circDist ((q : ℝ) * Int.fract ((p : ℝ) * t)) ≥ (1 : ℝ) / (n : ℝ) := by
  unfold goodSet
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h
  · rw [circDist_fundamental q p t]
    convert h using 2
    push_cast; ring
  · rw [circDist_fundamental q p t] at h
    convert h using 2
    push_cast; ring

/-- The set `A = {φ ∈ [0,1) | circDist (q * φ) ≥ 1/n}` appearing in Theorem 10.1. -/
noncomputable def setA (q n : ℕ) : Set ℝ :=
  { φ : ℝ | Int.fract φ = φ ∧ circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / (n : ℝ) }

/-- Measure of `setA q n` is `(n-2)/n` (when `n ≥ 2`).

    The set decomposes into `q` intervals per period `[0,1)`, each of width `(n-2)/(n*q)`.
    Total measure: `q * (n-2)/(n*q) = (n-2)/n`. -/
theorem setA_measure (q n : ℕ) (hn : 2 ≤ n) (hq : 0 < q) :
    MeasureTheory.volume (setA q n) = ENNReal.ofReal ((n - 2 : ℝ) / n) := by
  -- BLOCKER: Requires explicit measure computation for union of intervals.
  -- Each "bad arc" around integer multiples of 1/q has width 2/(n*q).
  -- Good arcs: q arcs each of width (n-2)/(n*q).
  -- MATHLIB_SEARCH: `MeasureTheory.volume_iUnion_disjoint`, `Real.volume_Ioo`
  -- STATUS: sorry
  sorry
