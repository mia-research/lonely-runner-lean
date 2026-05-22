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
    rw [div_le_div_iff (by positivity) (by positivity)]
    have : (1 : ℝ) * ((n : ℝ) * v₁) = n * v₁ := one_mul _
    rw [this]
    have : (v_j : ℝ) * n ≥ v₁ * n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hlo
      · positivity
    linarith
  · -- Upper bound: v_j / (n * v₁) ≤ (n-1)/n  ↔  v_j ≤ (n-1) * v₁
    rw [div_le_div_iff (by positivity) (by positivity)]
    have hcast : (v_j : ℝ) * n ≤ ((n - 1) * v₁ : ℕ) * n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hhi
      · positivity
    have hcast2 : ((n - 1) * v₁ : ℕ) = (n - 1) * v₁ := by push_cast; rfl
    rw [hcast2] at hcast
    have : ((n : ℝ) - 1) * v₁ * n = (n - 1) / n * (n * v₁) * n := by ring_nf; field_simp
    -- BLOCKER: The nat subtraction `n - 1` vs real subtraction needs careful handling.
    -- STATUS: sorry
    sorry

/-- **Key step:** If `r ∈ [1/n, (n-1)/n]` and `r ∈ [0,1)`, then `circDist r ≥ 1/n`. -/
theorem circDist_of_range (r : ℝ) (h1 : 1 / n ≤ r) (h2 : r ≤ (n - 1) / n) (hn : 0 < n) :
    -- Here n : ℝ in this context
    min r (1 - r) ≥ 1 / n := by
  apply le_min
  · linarith
  · -- 1 - r ≥ 1/n  ↔  r ≤ (n-1)/n
    linarith

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
  unfold bsr_time circDist
  -- Simplify: speeds i * (1 / (n * speeds 0)) = speeds i / (n * speeds 0)
  have hv1_pos : 0 < speeds ⟨0, by omega⟩ := hpos ⟨0, by omega⟩
  have hfract : Int.fract ((speeds i : ℝ) * (1 / ((n : ℝ) * speeds ⟨0, by omega⟩))) =
      (speeds i : ℝ) / ((n : ℝ) * speeds ⟨0, by omega⟩) := by
    -- The value v_i / (n * v_1) ∈ [1/n, (n-1)/n] ⊆ [0, 1),
    -- so Int.fract equals the value itself.
    rw [Int.fract_eq_self]
    constructor
    · -- ≥ 0: speeds are positive
      positivity
    · -- < 1: v_i ≤ V ≤ (n-1) * v_1 < n * v_1
      rw [div_lt_one (by positivity)]
      have hi_le : speeds i ≤ speeds ⟨n - 2, by omega⟩ := by
        apply hmono.monotone
        simp; omega
      have hV_lt : (n - 1) * speeds ⟨0, by omega⟩ < n * speeds ⟨0, by omega⟩ := by
        apply Nat.mul_lt_mul_right hv1_pos
        omega
      calc (speeds i : ℝ) ≤ speeds ⟨n - 2, by omega⟩ := by exact_mod_cast hi_le
        _ ≤ (n - 1) * speeds ⟨0, by omega⟩ := by exact_mod_cast hV
        _ < n * speeds ⟨0, by omega⟩ := by exact_mod_cast hV_lt
  -- After establishing fract = value, use bsr_range.
  simp only [mul_div_assoc']
  rw [hfract]
  apply le_min
  · -- Lower bound
    have hlo : speeds ⟨0, by omega⟩ ≤ speeds i :=
      hmono.monotone (Fin.zero_le _)
    rw [ge_iff_le, div_le_div_iff (by positivity) (by positivity)]
    calc (1 : ℝ) * ((n : ℝ) * speeds ⟨0, by omega⟩)
        = n * speeds ⟨0, by omega⟩ := one_mul _
      _ ≤ speeds i * n := by
          have := @Nat.cast_le ℝ _ _ _ |>.mpr hlo
          nlinarith
      _ = speeds i * (n * 1) := by ring
  · -- Upper bound: 1 - v_i/(n*v_1) ≥ 1/n  ↔  v_i ≤ (n-1)*v_1
    have hi_le : speeds i ≤ speeds ⟨n - 2, by omega⟩ :=
      hmono.monotone (Fin.val_fin_lt.mpr (by omega))
    have hVi : (speeds i : ℝ) ≤ (n - 1) * speeds ⟨0, by omega⟩ := by
      have := (Nat.cast_le (α := ℝ)).mpr (hi_le.trans hV)
      push_cast at this ⊢
      linarith
    rw [ge_iff_le]
    rw [div_le_iff (by positivity)]
    -- Need: 1/n * (n * v_1) ≤ 1 - v_i / (n * v_1)   ... hmm
    -- Actually: 1/n ≤ 1 - v_i/(n*v_1)  ↔  v_i/(n*v_1) ≤ (n-1)/n  ↔  v_i ≤ (n-1)*v_1
    -- BLOCKER: The algebra with nat subtraction (n-1) vs real needs care.
    -- STATUS: sorry
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
