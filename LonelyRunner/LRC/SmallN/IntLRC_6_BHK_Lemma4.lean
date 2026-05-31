import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Defs

/-!
# BHK §2 — Lemma 4 (45-block size bound) and Corollary 5

**BHK Lemma 4.** If `I` is a 45-block (maximal closed interval inside
`unsafeOf 3 ∪ unsafeOf 4`) then `|I| < 2 / (3 v_4)`.

In Lean we state the slightly stronger inclusion form: any closed interval
`[a, b]` contained in `unsafeOf 3 ∪ unsafeOf 4` has `b - a < 2 / (3 v_4)`.
The bound holds for all sub-intervals, so the original "45-block" form is
the special case where `[a, b]` is maximal.

**BHK Corollary 5.** Any 123-gap of length `≥ 2 / (3 v_3)` contains a lonely
time. Proved here modulo Lemma 4.

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001)
R3, §2 (p3–4).
-/

open MeasureTheory Set

namespace BHK

/-! ## Helpers for BHK Lemma 4

We follow BHK's proof: every connected component of `unsafeOf i` is an open
interval of length `1/(3 v_i)`. Their gaps are closed intervals of length
`2/(3 v_i)`. -/

/-- **Sub-lemma A (single-runner block bound).** A closed interval contained
    in `unsafeOf speeds i` has length strictly less than `1 / (3 v_i)`.

    Proof: pick the integer `k` so that `a * v_i ∈ (k - 1/6, k + 1/6)`.
    Suppose `b * v_i ≥ k + 1/6`. Then `(k + 1/6) / v_i ∈ [a, b]`, but
    `(k + 1/6)` is not in `bhkB`, contradiction. So `b * v_i < k + 1/6` and
    `b - a < 1/(3 v_i)`. -/
lemma block_length_bound (speeds : Fin 5 → ℕ) (i : Fin 5) (hv : 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ unsafeOf speeds i) :
    b - a < 1 / (3 * (speeds i : ℝ)) := by
  have hvR : (0 : ℝ) < (speeds i : ℝ) := by exact_mod_cast hv
  -- a is in unsafeOf i, so v_i · a is in bhkB
  have ha_mem : a ∈ unsafeOf speeds i := hsub ⟨le_refl a, hab⟩
  rw [mem_unsafeOf_iff_bhkB] at ha_mem
  obtain ⟨k, hk⟩ := ha_mem
  -- v_i · a ∈ (k - 1/6, k + 1/6)
  have ha_lt : (speeds i : ℝ) * a < (k : ℝ) + 1 / 6 := by
    have := lt_of_abs_lt hk; linarith
  have ha_gt : (k : ℝ) - 1 / 6 < (speeds i : ℝ) * a := by
    have := neg_lt_of_abs_lt hk; linarith
  -- Claim: v_i · b < k + 1/6
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : 1 / (3 * v) ≤ b - a
  have hbge : (k : ℝ) + 1 / 6 ≤ (speeds i : ℝ) * b := by
    -- b ≥ a + 1/(3v), so v * b ≥ v * a + 1/3
    have hba : 1 / (3 * (speeds i : ℝ)) ≤ b - a := hcontra
    have h1 : (speeds i : ℝ) * (b - a) ≥ 1 / 3 := by
      have hmul : (speeds i : ℝ) * (1 / (3 * (speeds i : ℝ))) ≤ (speeds i : ℝ) * (b - a) :=
        mul_le_mul_of_nonneg_left hba (le_of_lt hvR)
      have hsimp : (speeds i : ℝ) * (1 / (3 * (speeds i : ℝ))) = 1 / 3 := by
        field_simp
      linarith
    have h2 : (speeds i : ℝ) * b - (speeds i : ℝ) * a ≥ 1 / 3 := by
      have : (speeds i : ℝ) * (b - a) = (speeds i : ℝ) * b - (speeds i : ℝ) * a := by ring
      linarith
    linarith
  -- Define t* := (k + 1/6) / v_i
  set t_star : ℝ := ((k : ℝ) + 1 / 6) / (speeds i : ℝ) with ht_star
  have ht_a : a ≤ t_star := by
    rw [ht_star, le_div_iff₀ hvR]; linarith
  have ht_b : t_star ≤ b := by
    rw [ht_star, div_le_iff₀ hvR]; linarith
  -- t* ∈ [a, b] so t* ∈ unsafeOf i
  have ht_mem : t_star ∈ unsafeOf speeds i := hsub ⟨ht_a, ht_b⟩
  rw [mem_unsafeOf_iff_bhkB] at ht_mem
  obtain ⟨k', hk'⟩ := ht_mem
  -- v_i · t* = k + 1/6
  have ht_eval : (speeds i : ℝ) * t_star = (k : ℝ) + 1 / 6 := by
    rw [ht_star]; field_simp
  rw [ht_eval] at hk'
  -- |k + 1/6 - k'| < 1/6
  -- Since k' is integer and k is integer, the only ints in (k, k + 1/3) are none
  exfalso
  have h1 : (k' : ℝ) > (k : ℝ) := by
    have := lt_of_abs_lt hk'; linarith
  have h2 : (k' : ℝ) < (k : ℝ) + 1 / 3 := by
    have := neg_lt_of_abs_lt hk'; linarith
  have h3 : (k : ℤ) < k' := by exact_mod_cast h1
  have h4 : k + 1 ≤ k' := h3
  have h5 : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast h4
  linarith

/-- **Helper: characterising "not in `unsafeOf i`" via integer gaps.**
    `t ∉ unsafeOf speeds i` iff `v_i · t ∈ [k + 1/6, k + 5/6]` for some integer
    `k`. The complement of the open U3-components is exactly the union of
    closed gaps. -/
lemma not_mem_unsafeOf_iff_in_gap (speeds : Fin 5 → ℕ) (i : Fin 5) (t : ℝ) :
    t ∉ unsafeOf speeds i ↔
    ∃ k : ℤ, (k : ℝ) + 1 / 6 ≤ (speeds i : ℝ) * t ∧ (speeds i : ℝ) * t ≤ (k : ℝ) + 5 / 6 := by
  rw [mem_unsafeOf_iff_bhkB, bhkB]
  simp only [Set.mem_setOf_eq, not_exists]
  constructor
  · intro h
    -- ¬ ∃ k, |v · t - k| < 1/6
    -- So ∀ k, |v · t - k| ≥ 1/6
    -- Let k = ⌊v · t - 1/6⌋, then v · t - 1/6 ≥ k, so v · t ≥ k + 1/6.
    -- And v · t - 1/6 < k + 1, so v · t < k + 7/6.
    -- Need: v · t ≤ k + 5/6. Suppose v · t > k + 5/6, then |v·t - (k+1)| < 1/6. Contradiction.
    refine ⟨⌊(speeds i : ℝ) * t - 1/6⌋, ?_, ?_⟩
    · have hfl := Int.floor_le ((speeds i : ℝ) * t - 1/6)
      linarith
    · have hfl_lt := Int.lt_floor_add_one ((speeds i : ℝ) * t - 1/6)
      by_contra hgt
      push_neg at hgt
      -- v · t > k + 5/6, so |v · t - (k+1)| < 1/6
      have : |(speeds i : ℝ) * t - ((⌊(speeds i : ℝ) * t - 1/6⌋ + 1 : ℤ) : ℝ)| < 1/6 := by
        push_cast
        rw [abs_lt]
        constructor
        · linarith
        · linarith
      exact absurd this (h _)
  · rintro ⟨k, hkl, hkr⟩ k'
    -- v · t ∈ [k + 1/6, k + 5/6]
    -- For any integer k', |v · t - k'| ≥ ? Show ≥ 1/6.
    intro hcontra
    have hh := lt_of_abs_lt hcontra
    have hh' := neg_lt_of_abs_lt hcontra
    -- |v · t - k'| < 1/6 means k' - 1/6 < v · t < k' + 1/6.
    -- Combined with k + 1/6 ≤ v · t ≤ k + 5/6: k + 1/6 < k' + 1/6 (so k < k')
    -- and k' - 1/6 < k + 5/6 (so k' < k + 1). So k < k' < k + 1: no integer.
    have h1 : (k : ℝ) < (k' : ℝ) := by linarith
    have h2 : (k' : ℝ) < (k : ℝ) + 1 := by linarith
    have h1z : k < k' := by exact_mod_cast h1
    have h2z : k' < k + 1 := by exact_mod_cast h2
    omega

/-- **Helper: points in a closed `unsafeOf i`-gap are not in `unsafeOf i`.**
    If `(k + 1/6)/v_i ≤ t ≤ (k + 5/6)/v_i`, then `t ∉ unsafeOf speeds i`. -/
lemma not_mem_unsafeOf_of_in_gap (speeds : Fin 5 → ℕ) (i : Fin 5) (hv : 0 < speeds i)
    (k : ℤ) (t : ℝ)
    (h1 : ((k : ℝ) + 1/6) / (speeds i : ℝ) ≤ t)
    (h2 : t ≤ ((k : ℝ) + 5/6) / (speeds i : ℝ)) :
    t ∉ unsafeOf speeds i := by
  have hvR : (0 : ℝ) < (speeds i : ℝ) := by exact_mod_cast hv
  rw [not_mem_unsafeOf_iff_in_gap]
  refine ⟨k, ?_, ?_⟩
  · -- (k + 1/6) ≤ v_i · t
    rw [div_le_iff₀ hvR] at h1
    linarith
  · -- v_i · t ≤ (k + 5/6)
    rw [le_div_iff₀ hvR] at h2
    linarith

/-- **Sub-lemma B (gap-piece bound).** A closed sub-interval of `[a, b]` that is
    disjoint from `unsafeOf speeds 3` lies in `unsafeOf speeds 4`, and hence
    has length `< 1 / (3 v_5)`. Specifically, for any integer `k`, the closed
    sub-interval `[max(a, (k+1/6)/v_4), min(b, (k+5/6)/v_4)]` (if non-trivial)
    is in `unsafeOf 4`, and has length `< 1/(3 v_5)`. -/
lemma gap_piece_bound (speeds : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩)
    (k : ℤ)
    (sL sR : ℝ) (hsL_a : a ≤ sL) (hsR_b : sR ≤ b) (hsLR : sL ≤ sR)
    (hgapL : ((k : ℝ) + 1/6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ sL)
    (hgapR : sR ≤ ((k : ℝ) + 5/6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    sR - sL < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) := by
  -- Show [sL, sR] ⊆ unsafeOf 4
  have hv3pos : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv4pos : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hsub_U4 : Set.Icc sL sR ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    obtain ⟨htL, htR⟩ := ht
    have ht_ab : t ∈ Set.Icc a b := ⟨le_trans hsL_a htL, le_trans htR hsR_b⟩
    have ht_S : t ∈ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩ := hI ht_ab
    -- Need to rule out t ∈ unsafeOf 3
    have ht_notU3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ :=
      not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ hv3pos k t
        (le_trans hgapL htL) (le_trans htR hgapR)
    rcases ht_S with h | h
    · exact absurd h ht_notU3
    · exact h
  exact block_length_bound speeds ⟨4, by omega⟩ hv4pos sL sR hsLR hsub_U4

/-- **BHK Lemma 4.** Any closed interval `[a, b]` contained in
    `unsafeOf 3 ∪ unsafeOf 4` has length `< 2 / (3 v_4)`. -/
theorem bhk_lemma_4 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩) :
    b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  sorry

/-- **BHK Corollary 5.** If a closed interval `[a, b]` is contained in the
    complement of `unsafeOf 0 ∪ unsafeOf 1 ∪ unsafeOf 2` (a 123-gap) and has
    length `≥ 2 / (3 v_3)`, then it contains a time lonely for all 5 runners.

    Proof: if no lonely time, then `[a, b] ⊆ unsafeOf 3 ∪ unsafeOf 4`; Lemma 4
    bounds this length by `< 2 / (3 v_4) < 2 / (3 v_3)`, contradiction. -/
theorem bhk_corollary_5 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (h123gap : Set.Icc a b ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
                              unsafeOf speeds ⟨1, by omega⟩ ∪
                              unsafeOf speeds ⟨2, by omega⟩)ᶜ)
    (h3len : 2 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ b - a) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra hne
  push_neg at hne
  have hcover : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                              unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    obtain ⟨i, hi⟩ := hne t
    have h123 : t ∉ unsafeOf speeds ⟨0, by omega⟩ ∪
                    unsafeOf speeds ⟨1, by omega⟩ ∪
                    unsafeOf speeds ⟨2, by omega⟩ := h123gap ht
    have ht_unsafe : t ∈ unsafeOf speeds i := (mem_unsafeOf_iff speeds i t).mpr hi
    fin_cases i
    · exact absurd (Or.inl (Or.inl ht_unsafe)) h123
    · exact absurd (Or.inl (Or.inr ht_unsafe)) h123
    · exact absurd (Or.inr ht_unsafe) h123
    · exact Or.inl ht_unsafe
    · exact Or.inr ht_unsafe
  have hbnd : b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    bhk_lemma_4 speeds hmono hpos a b hab hcover
  have hv3pos : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < speeds ⟨3, by omega⟩ := by exact_mod_cast hpos _
  have hlt : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    have : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ :=
      hmono (show (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩ by decide)
    exact_mod_cast this
  have hcmp : 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) <
              2 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  linarith

end BHK
