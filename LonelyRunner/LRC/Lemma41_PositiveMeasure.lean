import LonelyRunner.LRC.Defs

/-!
# Lemma 4.1 — Positive-Measure Lemma

Source: `lrc_proof_v11_draft.md` §4.

**Statement:** If LRC holds for `n-1` runners (i.e. `H(n-1)` holds), then the
simultaneous good set `G_s` for the `n-2` slow runners has positive Lebesgue measure.
Moreover, it contains a non-degenerate closed interval.

**Proof sketch:**
1. `H(n-1)` gives `t**` with `circDist(v_j * t**) ≥ 1/(n-1)` for all slow `j`.
2. Since `1/(n-1) > 1/n`, `t**` lies in the open interior of every `goodSet v_j n`.
3. By Lipschitz continuity of `t ↦ circDist(v_j * t)` (Lipschitz constant `v_j`),
   a neighbourhood `(t** - δ, t** + δ)` is contained in each `goodSet v_j n`.
4. Taking `δ = 1 / (n * (n-1) * v_{n-2})` yields the explicit bound.

This lemma converts the bare existence given by the inductive hypothesis into
the positive-measure input that Weyl equidistribution (Theorem 5.2) requires.
-/


open MeasureTheory Set

/-! ## §4  Positive-Measure Lemma -/

/-- Lipschitz bound: `|circDist(v*t) - circDist(v*s)| ≤ v * |t - s|`. -/
theorem circDist_lipschitz (v : ℕ) : LipschitzWith v circDist := by
  -- BLOCKER: `LipschitzWith` for `circDist` requires showing it is Lipschitz-v.
  -- Key chain: `circDist x = dist (Int.fract x) (round x)` or similar.
  -- `Int.fract` is 1-Lipschitz (piecewise linear), so `v ↦ v*t` composes.
  -- MATHLIB_SEARCH: `Int.fract_lipschitzWith`, `LipschitzWith.comp`
  -- STATUS: sorry
  sorry

/-- The neighbourhood radius from Lemma 4.1's explicit bound (★). -/
noncomputable def lemma41_delta (n : ℕ) (vmax : ℕ) : ℝ :=
  1 / (n * (n - 1) * vmax)

/-- **Lemma 4.1** (Positive-Measure Lemma).

    Given `H(n-1)` (LRC for n-1 runners), and slow runners `v₁ < ... < v_{n-2}`,
    the simultaneous good set `G_s = ⋂_j goodSet v_j n` has positive measure.
    Specifically, it contains the closed interval `[t** - δ, t** + δ]`
    where `δ = 1 / (n * (n-1) * v_{n-2})`. -/
theorem lemma41_positive_measure
    {k n : ℕ} (hn : 3 ≤ n) (hk : k = n - 2)
    (speeds : Fin k → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (hmono : StrictMono speeds)
    (Hn1 : H (n - 1)) :
    ∃ (t_star : ℝ) (δ : ℝ), 0 < δ ∧
      Icc (t_star - δ) (t_star + δ) ⊆ jointGoodSet speeds n ∧
      0 < MeasureTheory.volume (jointGoodSet speeds n) := by
  -- Step 1: Get t** from H(n-1), which gives LRC for k = n-2 runners.
  -- H(n-1) applies to (n-2) speeds (an (n-1)-runner problem).
  -- BLOCKER: Connecting H(n-1) (which talks about Fin(n-2) speeds) to our setup
  --          requires careful index management.
  -- MATHLIB_SEARCH: `Finset.univ`, `Fin.val_fin_lt`
  have Hn1_applied : ∃ t : ℝ, ∀ i : Fin k,
      circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    -- Apply H(n-1): LRC for k = n-2 runners with threshold 1/(n-1).
    -- STATUS: sorry — need to massage intLRC into this form
    sorry
  obtain ⟨t_star, ht_star⟩ := Hn1_applied
  -- Step 2: t** is in the strict interior of each goodSet speeds_i n.
  have h_strict : ∀ i : Fin k,
      circDist ((speeds i : ℝ) * t_star) > (1 : ℝ) / (n : ℝ) := by
    intro i
    have h1 : circDist ((speeds i : ℝ) * t_star) ≥ 1 / ((n - 1 : ℕ) : ℝ) := ht_star i
    have h2 : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) > 1 / (n : ℝ) := by
      -- BLOCKER: Requires careful handling of nat subtraction and division inequalities
      sorry
    linarith
  -- Step 3: Lipschitz → explicit neighbourhood.
  -- For each i: circDist(v_i * t) > 1/n for t in (t** - δ_i, t** + δ_i)
  -- where δ_i = (circDist(v_i * t**) - 1/n) / v_i ≥ (1/(n-1) - 1/n) / v_i
  --           = 1/(n(n-1)v_i).
  -- Taking minimum over i gives δ ≥ 1/(n(n-1) * v_{n-2}).
  let vmax : ℕ := if k = 0 then 1 else speeds ⟨k - 1, by omega⟩
  let δ := lemma41_delta n vmax
  refine ⟨t_star, δ, ?_, ?_, ?_⟩
  · -- δ > 0
    -- BLOCKER: Requires unfolding and positivity arguments for δ.
    sorry
  · -- [t** - δ, t** + δ] ⊆ jointGoodSet speeds n
    -- BLOCKER: Requires the Lipschitz continuity lemma.
    -- STATUS: sorry
    sorry
  · -- μ(jointGoodSet) > 0 (follows from the interval containment)
    -- BLOCKER: Depends on the two bullets above.
    -- STATUS: sorry
    sorry

/-- Quantitative form: the measure of `jointGoodSet` is at least `2 * δ`. -/
theorem lemma41_measure_lower_bound
    {k n : ℕ} (hn : 3 ≤ n) (hk : k = n - 2)
    (speeds : Fin k → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (hmono : StrictMono speeds)
    (Hn1 : H (n - 1)) :
    MeasureTheory.volume (jointGoodSet speeds n) ≥
      ENNReal.ofReal (2 * lemma41_delta n (speeds ⟨k - 1, by omega⟩)) := by
  -- BLOCKER: Follows from `lemma41_positive_measure` + measure of an interval.
  -- MATHLIB_SEARCH: `Real.volume_Icc`, `ENNReal.ofReal_le_ofReal`
  -- STATUS: sorry
  sorry
