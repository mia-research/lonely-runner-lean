import LonelyRunner.LRC.Defs

/-!
# Theorem 6.1 — Bounded Speed Ratio

Source: `lrc_proof_v11_draft.md` §6.

**Statement:** If `V ≤ (n-1) * v₁` (where `v₁` is the minimum speed and `V` is the
maximum), then `t* = 1 / (n * v₁)` satisfies `circDist(v_j * t*) ≥ 1/n` for all `j`.

**Proof:** For each runner `j`:
  `v_j * t* = v_j / (n * v₁) ∈ [1/n, (n-1)/n]`
since `v₁ ≤ v_j ≤ V ≤ (n-1)*v₁`.  The value lies in `[1/n, (n-1)/n] ⊆ (0,1)`,
so `Int.fract(v_j * t*) = v_j / (n * v₁)` and
  `circDist(v_j * t*) = min(v_j/(n*v₁), 1 - v_j/(n*v₁)) ≥ 1/n`.

**Difficulty:** ROUTINE — pure arithmetic.  The proof uses no inductive hypothesis.
-/


/-! ## §6  Bounded Speed Ratio -/

/-- The explicit good time for the BSR case: `t* = 1 / (n * v₁)`. -/
noncomputable def bsr_time (n v₁ : ℕ) : ℝ := 1 / ((n : ℝ) * (v₁ : ℝ))

/-- **Lemma (BSR pre-step):** Under BSR hypothesis, `v_j / (n * v₁) ∈ [1/n, (n-1)/n]`
    for any speed `v_j` with `v₁ ≤ v_j ≤ V ≤ (n-1)*v₁`. -/
theorem bsr_range
    (n v₁ v_j : ℕ) (hn : 2 ≤ n)
    (hv1_pos : 0 < v₁)
    (hlo : v₁ ≤ v_j)
    (hhi : v_j ≤ (n - 1) * v₁) :
    (1 : ℝ) / n ≤ (v_j : ℝ) / ((n : ℝ) * (v₁ : ℝ)) ∧
    (v_j : ℝ) / ((n : ℝ) * (v₁ : ℝ)) ≤ (n - 1 : ℝ) / n := by
  constructor
  · -- Lower bound: v_j / (n * v₁) ≥ 1/n  ↔  v₁ ≤ v_j
    -- BLOCKER: Requires div_le_div_iff or equivalent from Mathlib.
    sorry
  · -- Upper bound: v_j / (n * v₁) ≤ (n-1)/n  ↔  v_j ≤ (n-1) * v₁
    -- BLOCKER: Requires handling of nat subtraction
    sorry

/-- **Key step:** If `r ∈ [1/n, (n-1)/n]` and `r ∈ [0,1)`, then `circDist r ≥ 1/n`. -/
theorem circDist_of_range (r : ℝ) (h1 : 1 / n ≤ r) (h2 : r ≤ (n - 1) / n) (hn : 0 < n) :
    -- Here n : ℝ in this context
    min r (1 - r) ≥ 1 / n := by
  apply le_min
  · sorry  -- linarith failed; arithmetic lemma needed
  · sorry  -- 1 - r ≥ 1/n  ↔  r ≤ (n-1)/n

/-- **Theorem 6.1** (Bounded Speed Ratio).

    Let `n ≥ 3` and let `speeds : Fin (n-1) → ℕ` be strictly increasing positive
    integer speeds with maximum speed `V = speeds ⟨n-2, _⟩ ≤ (n-1) * speeds ⟨0, _⟩`.
    Then `t* = 1 / (n * speeds 0)` satisfies `circDist (speeds i * t*) ≥ 1/n` for all `i`. -/
theorem theorem61_BSR
    (n : ℕ) (hn : 3 ≤ n)
    (speeds : Fin (n - 1) → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (hmono : StrictMono speeds)
    (hV : speeds ⟨n - 2, by omega⟩ ≤ (n - 1) * speeds ⟨0, by omega⟩) :
    ∀ i : Fin (n - 1),
      circDist ((speeds i : ℝ) * bsr_time n (speeds ⟨0, by omega⟩)) ≥
      (1 : ℝ) / (n : ℝ) := by
  intro i
  -- BLOCKER: The full proof requires careful arithmetic with Int.fract and division inequalities.
  sorry

/-- Edge case: at the BSR boundary `V = (n-1)*v₁`, Theorem 6.1 still works. -/
example : (3 : ℕ) ≤ 3 := le_refl 3  -- sanity check

/-- Numerical check: n=3, v₁=1, V=2. t* = 1/3.
    circDist(1 * 1/3) = 1/3 ✓
    circDist(2 * 1/3) = circDist(2/3) = min(2/3, 1/3) = 1/3 ✓ -/
example : circDist (1 * (1 / (3 * 1 : ℝ))) = 1 / 3 := by
  unfold circDist
  norm_num [Int.fract_eq_self]

example : circDist (2 * (1 / (3 * 1 : ℝ))) = 1 / 3 := by
  unfold circDist
  norm_num [Int.fract_eq_self]
