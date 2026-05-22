import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Lemma41_PositiveMeasure

/-!
# Theorem 7.1 — Large Speed Ratio

Source: `lrc_proof_v11_draft.md` §7.

**Statement:** If `V > (n-1) * v_{n-2}` (where `v_{n-2}` is the second-largest speed),
then there exists `t` with `circDist(v_j * t) ≥ 1/n` for all `j`.

**Proof sketch:**
1. Get `t**` from `H(n-1)` with `circDist(v_j * t**) ≥ 1/(n-1)` for slow runners.
2. By Lemma 4.1, `I = [t** - δ, t** + δ] ⊆ G_s` with `δ = 1/(n(n-1)v_{n-2})`.
3. Each connected component of `B_V` (bad set for V) has width `2/(nV) < 2δ = |I|`.
4. No single bad component covers all of `I`, so `I ∩ G_V ≠ ∅`.

**Difficulty:** MODERATE — interval arithmetic, two sub-cases for the geometric argument.
-/


open MeasureTheory Set

/-! ## §7  Large Speed Ratio -/

/-- Width of a connected component of `badSet V n`: each component is an interval
    of length `2/(n*V)` centred at some integer multiple of `1/V`. -/
theorem badSet_component_width (V n : ℕ) (hV : 0 < V) (hn : 0 < n) :
    ∀ k : ℤ,
      (badSet V n) ∩ Set.Ioo ((k : ℝ) / V - 1 / (n * V)) ((k : ℝ) / V + 1 / (n * V)) =
      Set.Ioo ((k : ℝ) / V - 1 / (n * V)) ((k : ℝ) / V + 1 / (n * V)) := by
  -- BLOCKER: Requires showing that on the open interval
  --   (k/V - 1/(nV), k/V + 1/(nV)), we have circDist(V*t) < 1/n.
  -- Proof: on this interval, V*t ∈ (k - 1/n, k + 1/n),
  --   so Int.fract(V*t) < 1/n or > (n-1)/n, giving circDist < 1/n.
  -- MATHLIB_SEARCH: `Set.eq_of_subset_of_subset`, `Set.Ioo_subset_Ioo`
  -- STATUS: sorry
  sorry

/-- **Key geometric lemma:** If `|I| > 2/(nV)` and `I ⊆ G_s`, then `I ∩ G_V ≠ ∅`. -/
theorem interval_escapes_bad
    (I : Set ℝ) (a b : ℝ) (hI : I = Icc a b)
    (hlen : 2 / ((n : ℝ) * V) < b - a)
    (V n : ℕ) (hV : 0 < V) (hn : 0 < n) :
    (I ∩ goodSet V n).Nonempty := by
  -- Case split based on manuscript's two sub-cases:
  -- (i) I starts to the left of any bad component.
  -- (ii) I starts inside a bad component — then it must exit to the right.
  -- In both cases, I ∩ G_V ≠ ∅.
  -- BLOCKER: The bad set has period 1/V, and each component has width 2/(nV) < |I|.
  --          A standard covering argument shows I cannot be covered by one component.
  -- MATHLIB_SEARCH: `Set.Nonempty.mono`, `Set.Icc_inter_Icc`
  -- STATUS: sorry
  sorry

/-- **Theorem 7.1** (Large Speed Ratio).

    Suppose `V > (n-1) * v_{n-2}` (where `v_{n-2}` is the second-largest slow runner's speed).
    Then under `H(n-1)`, there exists `t₀ ∈ G_s ∩ G_V`. -/
theorem theorem71_LargeSR
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (V : ℕ)
    (hpos : ∀ i, 0 < slowSpeeds i)
    (hmono : StrictMono slowSpeeds)
    (hV_large : (n - 1) * slowSpeeds ⟨n - 3, by omega⟩ < V)
    (Hn1 : H (n - 1)) :
    ∃ t₀ : ℝ,
      (∀ i, circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- Step 1: Get t** from H(n-1) and the neighbourhood from Lemma 4.1.
  have hpm := @lemma41_positive_measure (n - 2) n hn rfl slowSpeeds hpos hmono Hn1
  obtain ⟨t_star, δ, hδ_pos, hI_sub, _⟩ := hpm
  -- Step 2: The neighbourhood I = [t** - δ, t** + δ] ⊆ G_s.
  -- Step 3: Width condition: 2/(nV) < 2δ follows from V > (n-1)*v_{n-2}.
  have hwidth : 2 / ((n : ℝ) * V) < 2 * δ := by
    unfold lemma41_delta at *
    -- δ ≥ 1/(n(n-1)v_{n-2}) and 2/(nV) = 2/(nV).
    -- Need: 2/(nV) < 2/(n(n-1)v_{n-2}) ↔ (n-1)v_{n-2} < V.
    have hV_cast : ((n - 1) * slowSpeeds ⟨n - 3, by omega⟩ : ℝ) < V := by
      exact_mod_cast hV_large
    -- BLOCKER: Connecting δ to lemma41_delta and doing the arithmetic.
    -- STATUS: sorry
    sorry
  -- Step 4: Apply interval_escapes_bad to get t₀ ∈ I ∩ G_V.
  have hG_s : Icc (t_star - δ) (t_star + δ) ⊆ jointGoodSet slowSpeeds n := hI_sub
  have hnonempty := @interval_escapes_bad
    (Icc (t_star - δ) (t_star + δ))
    (t_star - δ) (t_star + δ) rfl (by linarith) V n (by omega) (by omega)
  obtain ⟨t₀, ht₀_I, ht₀_V⟩ := hnonempty
  refine ⟨t₀, ?_, ?_⟩
  · -- Slow runners: t₀ ∈ I ⊆ G_s
    intro i
    have hmem : t₀ ∈ jointGoodSet slowSpeeds n := hG_s ht₀_I
    exact hmem i
  · -- Fast runner V: t₀ ∈ G_V
    exact ht₀_V

/-! ## §7  Boundary remark -/

/-- At the boundary `V = (n-1) * v_{n-2}`, the LR argument breaks (equal widths).
    This case falls into the hard case (§9) and is handled by Theorems 10.1 or 11.1.
    No separate proof is needed here. -/
-- (This is a remark, not a lemma.)
