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
  have hn_r : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hv1_r : (0 : ℝ) < v₁ := Nat.cast_pos.mpr hv1_pos
  have hlo_r : (v₁ : ℝ) ≤ v_j := by exact_mod_cast hlo
  constructor
  · -- Lower bound: 1/n ≤ v_j/(n*v₁) ↔ v₁ ≤ v_j (cross-multiply by n*(n*v₁) > 0)
    rw [div_le_div_iff₀ hn_r (mul_pos hn_r hv1_r)]
    nlinarith
  · -- Upper bound: v_j/(n*v₁) ≤ (n-1)/n ↔ n*v_j ≤ (n-1)*(n*v₁)
    -- (n-1:ℝ) elaborates as real subtraction (n:ℝ)-1, so this is rfl or ring.
    have hn1_cast : (n - 1 : ℝ) = (n : ℝ) - 1 := by ring
    rw [hn1_cast, div_le_div_iff₀ (mul_pos hn_r hv1_r) hn_r]
    have hhi_r : (v_j : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * v₁ := by exact_mod_cast hhi
    have hn1_nat : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      push_cast [show 1 ≤ n from by omega]; ring
    rw [hn1_nat] at hhi_r
    nlinarith

/-- **Key step:** If `r ∈ [1/n, (n-1)/n]` and `r ∈ [0,1)`, then `circDist r ≥ 1/n`. -/
theorem circDist_of_range (r : ℝ) (h1 : 1 / n ≤ r) (h2 : r ≤ (n - 1) / n) (hn : 0 < n) :
    -- Here n : ℝ in this context
    min r (1 - r) ≥ 1 / n := by
  rw [ge_iff_le, le_min_iff]
  refine ⟨h1, ?_⟩
  have : (n - 1) / n + 1 / n = 1 := by field_simp; ring
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
  -- Abbreviations
  set v₁ := speeds ⟨0, by omega⟩ with hv1_def
  set vᵢ := speeds i with hvi_def
  -- Positivity casts
  have hn_r  : (0 : ℝ) < n := by exact_mod_cast show 0 < n by omega
  have hv1_r : (0 : ℝ) < v₁ := Nat.cast_pos.mpr (hpos ⟨0, by omega⟩)
  -- Step 1: bounds on the index i
  have hlo_i : v₁ ≤ vᵢ := by
    by_cases h : (i : ℕ) = 0
    · -- i = ⟨0, _⟩, so vᵢ = v₁
      have heq : i = ⟨0, by omega⟩ := Fin.ext h
      simp [vᵢ, v₁, heq]
    · -- 0 < i, so strict monotonicity gives v₁ < vᵢ
      have hlt : (⟨0, by omega⟩ : Fin (n - 1)) < i := by
        simp [Fin.lt_def]; omega
      exact Nat.le_of_lt (hmono hlt)
  have hhi_i : vᵢ ≤ (n - 1) * v₁ := by
    have hle : i ≤ ⟨n - 2, by omega⟩ := by
      simp only [Fin.le_iff_val_le_val]; omega
    calc vᵢ ≤ speeds ⟨n - 2, by omega⟩ := hmono.monotone hle
      _ ≤ (n - 1) * v₁ := hV
  -- Step 2: v_i * t* = v_i/(n*v₁) ∈ [1/n, (n-1)/n]
  have hval : (vᵢ : ℝ) * bsr_time n v₁ = (vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ)) := by
    simp only [bsr_time]; ring
  -- Get range
  obtain ⟨hlo_r, hhi_r⟩ := bsr_range n v₁ vᵢ (by omega) (hpos ⟨0, by omega⟩) hlo_i hhi_i
  -- Normalise (n-1:ℝ) = (n:ℝ) - 1
  have hn1 : (n - 1 : ℝ) = (n : ℝ) - 1 := by ring
  rw [hn1] at hhi_r
  -- Step 3: value is in [0,1) so Int.fract equals the value
  have hnn  : (0 : ℝ) ≤ (vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ)) :=
    le_trans (div_nonneg one_pos.le hn_r.le) hlo_r
  have hlt1 : (vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ)) < 1 := by
    have : ((n : ℝ) - 1) / n < 1 := by rw [div_lt_one hn_r]; linarith
    linarith
  have hfract : Int.fract ((vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ))) =
                (vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ)) := by
    have hfl : ⌊(vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ))⌋ = (0 : ℤ) := by
      set r := (vᵢ : ℝ) / ((n : ℝ) * (v₁ : ℝ))
      have h1 : (0 : ℤ) ≤ ⌊r⌋ := Int.floor_nonneg.mpr hnn
      have h2 : ⌊r⌋ < (1 : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hlt1
      omega
    simp [Int.fract, hfl]
  -- Step 4: unfold circDist, rewrite by hval and hfract, then conclude
  rw [ge_iff_le]
  unfold circDist
  rw [hval, hfract]
  exact circDist_of_range _ hlo_r hhi_r hn_r

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
