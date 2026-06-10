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
time.

Both are fully proved (sorry-free). Case C of Lemma 4 (the BHK "k ≥ 2"
case) is closed by a two-5-block separation count in place of BHK's
5-gap-in-4-block alignment argument.

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

/-- **Block containment.** Refinement of `block_length_bound`. If a closed
    interval `[a, b]` is contained in `unsafeOf speeds i`, then there exists
    a single integer `k` such that
    `k - 1/6 < v_i · a` and `v_i · b < k + 1/6`. I.e., `[a, b]` is
    contained in the single "i-block" centred at `k / v_i`. The integer `k`
    is exactly the integer closest to `v_i · a` (and equivalently to
    `v_i · b`). -/
lemma block_containment (speeds : Fin 5 → ℕ) (i : Fin 5) (hv : 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ unsafeOf speeds i) :
    ∃ k : ℤ, (k : ℝ) - 1/6 < (speeds i : ℝ) * a ∧
              (speeds i : ℝ) * b < (k : ℝ) + 1/6 := by
  have hvR : (0 : ℝ) < (speeds i : ℝ) := by exact_mod_cast hv
  have ha_mem : a ∈ unsafeOf speeds i := hsub ⟨le_refl a, hab⟩
  rw [mem_unsafeOf_iff_bhkB] at ha_mem
  obtain ⟨k, hk⟩ := ha_mem
  have ha_gt : (k : ℝ) - 1 / 6 < (speeds i : ℝ) * a := by
    have := neg_lt_of_abs_lt hk; linarith
  refine ⟨k, ha_gt, ?_⟩
  by_contra hcontra
  push_neg at hcontra
  set t_star : ℝ := ((k : ℝ) + 1 / 6) / (speeds i : ℝ) with ht_star
  have ha_lt : (speeds i : ℝ) * a < (k : ℝ) + 1 / 6 := by
    have := lt_of_abs_lt hk; linarith
  have ht_a : a ≤ t_star := by
    rw [ht_star, le_div_iff₀ hvR]; linarith
  have ht_b : t_star ≤ b := by
    rw [ht_star, div_le_iff₀ hvR]; linarith
  have ht_mem : t_star ∈ unsafeOf speeds i := hsub ⟨ht_a, ht_b⟩
  rw [mem_unsafeOf_iff_bhkB] at ht_mem
  obtain ⟨k', hk'⟩ := ht_mem
  have ht_eval : (speeds i : ℝ) * t_star = (k : ℝ) + 1 / 6 := by
    rw [ht_star]; field_simp
  rw [ht_eval] at hk'
  have h1 : (k' : ℝ) > (k : ℝ) := by
    have := lt_of_abs_lt hk'; linarith
  have h3 : (k : ℤ) < k' := by exact_mod_cast h1
  have h5 : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast (h3 : k + 1 ≤ k')
  have := neg_lt_of_abs_lt hk'; linarith

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

/-- **BHK Lemma 4 — Case C (`fract(v_4 · a) ∈ [1/2, 5/6)`).** The genuine
    BHK "k ≥ 2" case. In `v_4`-coordinates, `J = [m+s, m+s+2/3]`
    decomposes as gap-piece + full 4-block + gap-piece:
    `[m+s, m+5/6] ∪ [m+5/6, m+7/6] ∪ [m+7/6, m+s+2/3]`.

    1. The two gap-pieces are closed intervals inside `unsafeOf 4`
       (4-safe times in `J` are 5-unsafe), so each is `< 1/(3 v_5)` by
       `gap_piece_bound`; their lengths sum to exactly `1/(3 v_4)`,
       giving `v_5 < 2 v_4`.
    2. `block_containment` pins each gap-piece inside a *single*
       5-block: integers `k₁, k₂` with each piece within `1/6` of `k_i`
       in `v_5`-coordinates.
    3. The `v_5`-distance between the two facing endpoints is exactly
       `d = v_5/(3 v_4) ∈ (1/3, 2/3)` (left end strict from
       `v_4 < v_5`, right end strict from step 1). Containment forces
       `k₂ - k₁ - 1/3 < d < k₂ - k₁ + 1/3`, i.e. `0 < k₂ - k₁ < 1` —
       no such integer. This replaces BHK's 5-gap-in-4-block
       alignment argument with a purely local two-block separation
       count. -/
theorem bhk_lemma_4_case_C (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (_hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩)
    (hcontra : 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) ≤ b - a)
    (hs_half : 1/2 ≤ Int.fract ((speeds ⟨3, by omega⟩ : ℝ) * a))
    (hs_56 : Int.fract ((speeds ⟨3, by omega⟩ : ℝ) * a) < 5/6) :
    False := by
  have hv3pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_lt_v4 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmlt : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ :=
      hmono (show (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ by decide)
    exact_mod_cast hmlt
  set v3 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv3def
  set v4 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv4def
  set m : ℤ := ⌊v3 * a⌋ with hmdef
  set s : ℝ := Int.fract (v3 * a) with hsdef
  have hs_lt_one : s < 1 := Int.fract_lt_one _
  have hva_eq : v3 * a = (m : ℝ) + s := by
    rw [hsdef, hmdef]
    have := Int.floor_add_fract (v3 * a)
    linarith
  -- J = [a, b'] ⊆ [a, b]
  set b' : ℝ := a + 2 / (3 * v3) with hb'def
  have hb'_le_b : b' ≤ b := by rw [hb'def]; linarith
  have hab' : a ≤ b' := by
    have : (0 : ℝ) < 2 / (3 * v3) := by positivity
    rw [hb'def]
    linarith
  have hJ_sub : Set.Icc a b' ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                                unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ⟨ht1, ht2⟩
    exact hI ⟨ht1, le_trans ht2 hb'_le_b⟩
  have ha_eq : a = ((m : ℝ) + s) / v3 := by
    rw [eq_div_iff (ne_of_gt hv3pos)]; linarith [hva_eq]
  have hb'_eq : b' = ((m : ℝ) + s + 2/3) / v3 := by
    rw [hb'def, ha_eq]
    field_simp
  -- The facing endpoints of the two gap-pieces.
  set e₁ : ℝ := ((m : ℝ) + 5/6) / v3 with he₁def
  set e₂ : ℝ := ((m : ℝ) + 7/6) / v3 with he₂def
  -- Ordering.
  have h_a_e₁ : a ≤ e₁ := by
    rw [ha_eq, he₁def]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  have h_e₁_e₂ : e₁ ≤ e₂ := by
    rw [he₁def, he₂def]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  have h_e₂_b' : e₂ ≤ b' := by
    rw [he₂def, hb'_eq]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  have h_e₁_b' : e₁ ≤ b' := le_trans h_e₁_e₂ h_e₂_b'
  -- Gap conditions for the left piece [a, e₁] (3-gap at m).
  have hgapL₁ : ((m : ℝ) + 1/6) / v3 ≤ a := by
    rw [ha_eq]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  have hgapR₁ : e₁ ≤ ((m : ℝ) + 5/6) / v3 := he₁def.le
  -- Gap conditions for the right piece [e₂, b'] (3-gap at m+1).
  have hgapL₂ : ((↑(m + 1) : ℝ) + 1/6) / v3 ≤ e₂ := by
    rw [he₂def]
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  have hgapR₂ : b' ≤ ((↑(m + 1) : ℝ) + 5/6) / v3 := by
    rw [hb'_eq]
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
  -- Step 1: each gap-piece is < 1/(3 v4); the pieces sum to 1/(3 v3).
  have hgp₁ : e₁ - a < 1 / (3 * v4) :=
    gap_piece_bound speeds hpos a b' hab' hJ_sub m a e₁
      le_rfl h_e₁_b' h_a_e₁ hgapL₁ hgapR₁
  have hgp₂ : b' - e₂ < 1 / (3 * v4) :=
    gap_piece_bound speeds hpos a b' hab' hJ_sub (m + 1) e₂ b'
      (le_trans h_a_e₁ h_e₁_e₂) le_rfl h_e₂_b' hgapL₂ hgapR₂
  have hv4_lt_2v3 : v4 < 2 * v3 := by
    have hsum : (e₁ - a) + (b' - e₂) = 1 / (3 * v3) := by
      rw [he₁def, he₂def, ha_eq, hb'_eq]
      field_simp
      ring
    have htwo : 2 / (3 * v4) = 1 / (3 * v4) + 1 / (3 * v4) := by ring
    have h2 : 1 / (3 * v3) < 2 / (3 * v4) := by
      rw [htwo]
      linarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h2
    linarith
  -- Step 2: each gap-piece lies in unsafeOf 4, hence in a single 5-block.
  have hP₁_sub : Set.Icc a e₁ ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ⟨ht1, ht2⟩
    have h_not3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ :=
      not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) m t
        (le_trans hgapL₁ ht1) (le_trans ht2 hgapR₁)
    rcases hJ_sub ⟨ht1, le_trans ht2 h_e₁_b'⟩ with h | h
    · exact absurd h h_not3
    · exact h
  have hP₂_sub : Set.Icc e₂ b' ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ⟨ht1, ht2⟩
    have h_not3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ :=
      not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) (m + 1) t
        (le_trans hgapL₂ ht1) (le_trans ht2 hgapR₂)
    rcases hJ_sub ⟨le_trans (le_trans h_a_e₁ h_e₁_e₂) ht1, ht2⟩ with h | h
    · exact absurd h h_not3
    · exact h
  obtain ⟨k₁, hk₁l, hk₁r⟩ :=
    block_containment speeds ⟨4, by omega⟩ (hpos _) a e₁ h_a_e₁ hP₁_sub
  obtain ⟨k₂, hk₂l, hk₂r⟩ :=
    block_containment speeds ⟨4, by omega⟩ (hpos _) e₂ b' h_e₂_b' hP₂_sub
  -- Step 3: the v4-distance between the facing endpoints is v4/(3 v3),
  -- strictly between 1/3 and 2/3 — incompatible with two 5-blocks.
  have hd_eq : v4 * e₂ - v4 * e₁ = v4 / (3 * v3) := by
    rw [he₁def, he₂def]
    field_simp
    ring
  have hd_lo : 1/3 < v4 * e₂ - v4 * e₁ := by
    rw [hd_eq, lt_div_iff₀ (by positivity)]
    linarith
  have hd_hi : v4 * e₂ - v4 * e₁ < 2/3 := by
    rw [hd_eq, div_lt_iff₀ (by positivity)]
    linarith
  have h₁ : v4 * a ≤ v4 * e₁ := mul_le_mul_of_nonneg_left h_a_e₁ (le_of_lt hv4pos)
  have h₂ : v4 * e₂ ≤ v4 * b' := mul_le_mul_of_nonneg_left h_e₂_b' (le_of_lt hv4pos)
  -- 0 < k₂ - k₁ < 1 over ℝ, hence over ℤ: contradiction.
  have h_int_lo : k₁ < k₂ := by
    have : (k₁ : ℝ) < (k₂ : ℝ) := by linarith
    exact_mod_cast this
  have h_int_hi : k₂ < k₁ + 1 := by
    have : (k₂ : ℝ) < (k₁ : ℝ) + 1 := by linarith
    exact_mod_cast this
  omega

/-- **BHK Lemma 4.** Any closed interval `[a, b]` contained in
    `unsafeOf 3 ∪ unsafeOf 4` has length `< 2 / (3 v_4)`.

    **Proof outline (fully proved, sorry-free):**

    Suppose for contradiction `b - a ≥ 2/(3 v_4)`. Consider
    `J = [a, a + 2/(3 v_4)] ⊆ [a, b]` and let `s = fract (v_4 · a)`.
    In `v_4`-coordinates, J is `[s, s + 2/3]`.

    * **Case A** (`s ∈ [0, 1/6] ∪ [5/6, 1)`): `a` lies in a 4-block. The 4-gap
      portion of J has length `≥ 1/2` in `v_4`-coords, so `≥ 1/(2 v_4)` in
      `t`-coords. This is one connected sub-interval ⊆ `unsafeOf 4`. By
      `block_length_bound`, length `< 1/(3 v_5)`. Hence `v_5 < 2 v_4 / 3 < v_4`,
      contradicting `hmono`.

    * **Case B1** (`s ∈ (1/6, 5/6)` with `s + 2/3 ≤ 5/6`, i.e. `s ≤ 1/6`):
      vacuous (forces `s = 1/6`).

    * **Case B2** (`s ∈ (1/6, 5/6)` with `s + 2/3 > 5/6`): J crosses from
      4-gap into 4-block (and possibly into the next 4-gap).
      - Subcase `s ∈ (1/6, 1/2]`: single gap-piece `[s, 5/6]` of length
        `5/6 - s ≥ 1/3` in `v_4`-coords. By `gap_piece_bound`,
        `(5/6 - s)/v_4 < 1/(3 v_5) < 1/(3 v_4)`, so `5/6 - s < 1/3`,
        i.e. `s > 1/2` — contradiction.
      - Subcase `s ∈ (1/2, 5/6)`: J covers gap-piece + full 4-block + next
        gap-piece. Gap-pieces sum to `1/3` in `v_4`-coords = `1/(3 v_4)` in
        `t`-coords. Each gap-piece `< 1/(3 v_5)` by `gap_piece_bound`; sum
        `< 2/(3 v_5)`. Hence `v_5 < 2 v_4`.

        **This is BHK's "k ≥ 2" structural case**, closed in
        `bhk_lemma_4_case_C` by a two-5-block separation count: the
        two gap-pieces each sit inside a single 5-block, but their
        facing endpoints are `v_5/(3 v_4) ∈ (1/3, 2/3)` apart in
        `v_5`-coordinates — too far for the same block, too near for
        distinct blocks.

    Helpers `block_length_bound`, `not_mem_unsafeOf_iff_in_gap`,
    `not_mem_unsafeOf_of_in_gap`, `gap_piece_bound` are in scope. -/
theorem bhk_lemma_4 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩) :
    b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  -- Abbreviations and basic positivity
  have hv3pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_lt_v4 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmlt : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ :=
      hmono (show (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ by decide)
    exact_mod_cast hmlt
  set v3 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv3def
  set v4 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv4def
  -- Proof by contradiction
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : 2 / (3 * v3) ≤ b - a
  -- Restrict to J = [a, a + 2/(3 v3)] ⊆ [a, b]
  set L : ℝ := 2 / (3 * v3) with hLdef
  have hL_pos : 0 < L := by positivity
  set b' : ℝ := a + L with hb'def
  have hb'_le_b : b' ≤ b := by rw [hb'def]; linarith
  have hab' : a ≤ b' := by rw [hb'def]; linarith
  have hJ_sub : Set.Icc a b' ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                                unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ⟨ht1, ht2⟩
    exact hI ⟨ht1, le_trans ht2 hb'_le_b⟩
  -- Set m = ⌊v3 · a⌋ so that v3 · a = m + s with s = fract(v3 · a) ∈ [0, 1).
  set m : ℤ := ⌊v3 * a⌋ with hmdef
  set s : ℝ := Int.fract (v3 * a) with hsdef
  have hs_nonneg : 0 ≤ s := Int.fract_nonneg _
  have hs_lt_one : s < 1 := Int.fract_lt_one _
  have hva_eq : v3 * a = (m : ℝ) + s := by
    rw [hsdef, hmdef]
    have := Int.floor_add_fract (v3 * a)
    linarith
  -- We will derive a contradiction by case analysis on s.
  -- The bound we want is `v_4 < v_3` (contradiction with hmono) from a single
  -- gap-piece of v3-coord length ≥ 1/3.
  -- KEY LEMMA: if (sL, sR) is a 3-gap-piece in [a, b'] of v3-coord length ≥ 1/3,
  -- then 1/(3 v3) ≤ sR - sL < 1/(3 v4), so v4 < v3, contradicting hmono.
  -- Cases A (s ∈ [0, 1/6]), B (s ∈ (1/6, 1/2]), D (s ∈ [5/6, 1))
  -- all yield a single gap-piece of v3-coord length ≥ 1/3.
  -- Case C (s ∈ (1/2, 5/6)) is the BHK-residual; we use a different argument.
  rcases lt_or_ge s (1/2) with hs_half | hs_half
  · -- s < 1/2: cases A (s ≤ 1/6) and B (1/6 < s < 1/2)
    -- In both, use the single gap-piece [max(a, (m+1/6)/v3), (m+5/6)/v3]
    -- = [(m+1/6)/v3, (m+5/6)/v3] when s ≤ 1/6 (=case A, gap fully in J)
    --   has length (m + 5/6 - (m + 1/6))/v3 = 2/3 / v3 ≥ 1/3 / v3
    -- = [(m+s)/v3, (m+5/6)/v3] when 1/6 < s < 1/2 (=case B, gap starts at a)
    --   wait, but (m+s)/v3 = a only if a is in the 3-gap, i.e., s ≥ 1/6
    --
    -- Let's define sL, sR carefully:
    -- sL = max(a, (m+1/6)/v3), sR = min(b', (m+5/6)/v3)
    -- For s ∈ [0, 1/2): we want sR - sL ≥ 1/(3 v3).
    set sL : ℝ := max a ((↑m + 1/6) / v3) with hsLdef
    set sR : ℝ := min b' ((↑m + 5/6) / v3) with hsRdef
    -- Need: a ≤ sL, sR ≤ b', sL ≤ sR, and gap conditions.
    have hsL_ge_a : a ≤ sL := le_max_left _ _
    have hsR_le_b' : sR ≤ b' := min_le_left _ _
    have hsL_ge_gap : ((↑m : ℝ) + 1/6) / v3 ≤ sL := le_max_right _ _
    have hsR_le_gap : sR ≤ ((↑m : ℝ) + 5/6) / v3 := min_le_right _ _
    -- Compute sL and sR explicitly:
    -- a = (m+s)/v3, so a vs (m+1/6)/v3: a ≤ (m+1/6)/v3 ⟺ m + s ≤ m + 1/6 ⟺ s ≤ 1/6
    -- Case A (s ≤ 1/6): sL = (m+1/6)/v3.
    -- Case B (1/6 < s < 1/2): sL = a = (m+s)/v3.
    -- b' = a + 2/(3 v3) = (m+s)/v3 + 2/(3 v3) = (m + s + 2/3)/v3
    -- b' vs (m+5/6)/v3: b' ≤ (m+5/6)/v3 ⟺ m + s + 2/3 ≤ m + 5/6 ⟺ s ≤ 1/6
    -- Case A: sR = b' = (m+s+2/3)/v3, length = (s+2/3-1/6)/v3 = (s+1/2)/v3 ≥ 1/2/v3
    -- Case B: sR = (m+5/6)/v3, length = (5/6-s)/v3 ≥ 1/3/v3 (since s ≤ 1/2 ⇒ 5/6-s ≥ 1/3)
    have ha_eq : a = ((↑m : ℝ) + s) / v3 := by
      rw [eq_div_iff (ne_of_gt hv3pos)]; linarith [hva_eq]
    have hb'_eq : b' = ((↑m : ℝ) + s + 2/3) / v3 := by
      rw [hb'def, hLdef, ha_eq]
      field_simp
    have hsLR : sL ≤ sR := by
      rw [hsLdef, hsRdef]
      rw [ha_eq, hb'_eq]
      -- max ((m+s)/v3) ((m+1/6)/v3) ≤ min ((m+s+2/3)/v3) ((m+5/6)/v3)
      apply max_le
      · apply le_min
        · have : (↑m : ℝ) + s ≤ (↑m : ℝ) + s + 2/3 := by linarith
          exact div_le_div_of_nonneg_right this (le_of_lt hv3pos)
        · -- (m+s)/v3 ≤ (m+5/6)/v3 ⟺ s ≤ 5/6, which holds since s < 1/2
          have : (↑m : ℝ) + s ≤ (↑m : ℝ) + 5/6 := by linarith
          exact div_le_div_of_nonneg_right this (le_of_lt hv3pos)
      · apply le_min
        · -- (m+1/6)/v3 ≤ (m+s+2/3)/v3 ⟺ 1/6 ≤ s + 2/3 ⟺ s ≥ -1/2 ✓
          have : (↑m : ℝ) + 1/6 ≤ (↑m : ℝ) + s + 2/3 := by linarith
          exact div_le_div_of_nonneg_right this (le_of_lt hv3pos)
        · have : (↑m : ℝ) + 1/6 ≤ (↑m : ℝ) + 5/6 := by linarith
          exact div_le_div_of_nonneg_right this (le_of_lt hv3pos)
    -- Apply gap_piece_bound
    have hgap : sR - sL < 1 / (3 * v4) := by
      have := gap_piece_bound speeds hpos a b' hab' hJ_sub m sL sR
        hsL_ge_a hsR_le_b' hsLR hsL_ge_gap hsR_le_gap
      exact this
    -- Now bound sR - sL ≥ 1/(3 v3) in both cases A and B
    have hgap_len_ge : 1 / (3 * v3) ≤ sR - sL := by
      rw [hsLdef, hsRdef]
      have ha_eq : a = ((↑m : ℝ) + s) / v3 := by
        field_simp; linarith [hva_eq]
      have hb'_eq : b' = ((↑m : ℝ) + s + 2/3) / v3 := by
        rw [hb'def, hLdef]
        field_simp; linarith [hva_eq]
      rw [ha_eq, hb'_eq]
      -- min ((m+s+2/3)/v3) ((m+5/6)/v3) - max ((m+s)/v3) ((m+1/6)/v3) ≥ 1/(3v3)
      -- Numerator: min(m+s+2/3, m+5/6) - max(m+s, m+1/6)
      -- = m + min(s+2/3, 5/6) - m - max(s, 1/6)
      -- = min(s+2/3, 5/6) - max(s, 1/6)
      -- Case A (s ≤ 1/6): min = s+2/3 (≤ 5/6 iff s ≤ 1/6), max = 1/6.
      --   Numerator = s + 2/3 - 1/6 = s + 1/2 ≥ 1/2 ≥ 1/3
      -- Case B (s > 1/6): min = 5/6, max = s.
      --   Numerator = 5/6 - s ≥ 1/3 (since s ≤ 1/2 ⇒ 5/6 - s ≥ 1/3)
      have hmin_max : min ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) -
                       max ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) ≥ 1/3 := by
        rcases le_or_gt s (1/6) with hsA | hsA
        · -- Case A: min = m+s+2/3 (since s+2/3 ≤ 5/6), max = m+1/6
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          linarith
        · -- Case B: min = m+5/6 (since s+2/3 ≥ 5/6 iff s ≥ 1/6), max = m+s
          rw [min_eq_right (by linarith), max_eq_left (by linarith)]
          linarith
      -- min ((m+s+2/3)/v3) ((m+5/6)/v3) = min (m+s+2/3, m+5/6) / v3
      have hmin_div : min (((↑m : ℝ) + s + 2/3) / v3) (((↑m : ℝ) + 5/6) / v3)
                      = min ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) / v3 := by
        rcases le_or_gt ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) with h | h
        · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h (le_of_lt hv3pos))]
        · rw [min_eq_right (le_of_lt h),
              min_eq_right (div_le_div_of_nonneg_right (le_of_lt h) (le_of_lt hv3pos))]
      have hmax_div : max (((↑m : ℝ) + s) / v3) (((↑m : ℝ) + 1/6) / v3)
                      = max ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) / v3 := by
        rcases le_or_gt ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) with h | h
        · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h (le_of_lt hv3pos))]
        · rw [max_eq_left (le_of_lt h),
              max_eq_left (div_le_div_of_nonneg_right (le_of_lt h) (le_of_lt hv3pos))]
      rw [hmin_div, hmax_div]
      rw [div_sub_div_same, le_div_iff₀ hv3pos]
      have : 1 / (3 * v3) * v3 = 1/3 := by field_simp
      rw [this]
      linarith
    -- 1/(3 v3) ≤ sR - sL < 1/(3 v4) ⇒ 1/(3 v3) < 1/(3 v4) ⇒ v4 < v3
    have hcontr : 1 / (3 * v3) < 1 / (3 * v4) := lt_of_le_of_lt hgap_len_ge hgap
    have hv4_lt_v3 : v4 < v3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hcontr
      linarith
    linarith
  · -- s ≥ 1/2: cases C (1/2 ≤ s < 5/6) and D (s ≥ 5/6)
    rcases lt_or_ge s (5/6) with hs_56 | hs_56
    · -- Case C: s ∈ [1/2, 5/6). The genuine BHK k ≥ 2 case — gap-piece +
      -- 4-block + gap-piece decomposition, closed by the two-5-block
      -- separation count in `bhk_lemma_4_case_C`.
      exact bhk_lemma_4_case_C speeds hmono hpos a b hab hI hcontra hs_half hs_56
    · -- Case D: s ∈ [5/6, 1). Gap-piece at m+1 has v3-coord length ≥ 1/3.
      -- sL = (m+1+1/6)/v3 = (m+7/6)/v3, sR = b' = a + 2/(3v3) = (m+s+2/3)/v3
      -- length = (s+2/3 - 7/6)/v3 = (s - 1/2)/v3 ≥ 1/3/v3 (since s ≥ 5/6)
      have ha_eq : a = ((↑m : ℝ) + s) / v3 := by
        rw [eq_div_iff (ne_of_gt hv3pos)]; linarith [hva_eq]
      have hb'_eq : b' = ((↑m : ℝ) + s + 2/3) / v3 := by
        rw [hb'def, hLdef, ha_eq]
        field_simp
      set sL : ℝ := ((↑m : ℝ) + 7/6) / v3 with hsLdef
      let sR : ℝ := b'
      have hsR_eq : sR = ((↑m : ℝ) + s + 2/3) / v3 := hb'_eq
      have hsL_ge_a : a ≤ sL := by
        rw [hsLdef, ha_eq]
        apply div_le_div_of_nonneg_right _ (le_of_lt hv3pos)
        linarith
      have hsR_le_b' : sR ≤ b' := le_refl _
      have hsLR : sL ≤ sR := by
        change sL ≤ b'
        rw [hsLdef, hb'_eq]
        apply div_le_div_of_nonneg_right _ (le_of_lt hv3pos)
        linarith
      have hsL_ge_gap : ((↑(m + 1) : ℝ) + 1/6) / v3 ≤ sL := by
        rw [hsLdef]
        push_cast
        apply div_le_div_of_nonneg_right _ (le_of_lt hv3pos)
        linarith
      have hsR_le_gap : sR ≤ ((↑(m + 1) : ℝ) + 5/6) / v3 := by
        change b' ≤ _
        rw [hb'_eq]
        push_cast
        apply div_le_div_of_nonneg_right _ (le_of_lt hv3pos)
        linarith
      have hgap : sR - sL < 1 / (3 * v4) :=
        gap_piece_bound speeds hpos a b' hab' hJ_sub (m+1) sL sR
          hsL_ge_a hsR_le_b' hsLR hsL_ge_gap hsR_le_gap
      have hgap_len_ge : 1 / (3 * v3) ≤ sR - sL := by
        change 1 / (3 * v3) ≤ b' - sL
        rw [hsLdef, hb'_eq]
        rw [div_sub_div_same, le_div_iff₀ hv3pos]
        have : 1 / (3 * v3) * v3 = 1/3 := by field_simp
        rw [this]
        linarith
      have hcontr : 1 / (3 * v3) < 1 / (3 * v4) := lt_of_le_of_lt hgap_len_ge hgap
      have hv4_lt_v3 : v4 < v3 := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hcontr
        linarith
      linarith

/-- **§8 structural fact `v_4 < 2 v_3`.** Under failure of loneliness
    (`h_no_lonely`) and the §8 entry condition `hlarge : v_3 ≤ 3 v_1`,
    apply `bhk_lemma_4` to the 123-gap `[1/(6 v_1), 5/(6 v_3)]` to derive
    `v_4 < 2 v_3`.

    Strategy (mirrors `bhk_case_8_2_1`'s opening derivation):
    1. The 123-gap `[1/(6 v_1), 5/(6 v_3)]` is in `unsafeOf ⟨3⟩ ∪ unsafeOf ⟨4⟩`
       because for any `t` in the gap, `h_no_lonely` gives some runner `i`,
       and runners 0, 1, 2 are ruled out by their `k=0` block-gap arguments
       (using `hlarge` and monotonicity to compare `1/(6 v_i) ≤ 1/(6 v_1)`
       and `5/(6 v_3) ≤ 5/(6 v_i)`).
    2. `bhk_lemma_4` gives the length bound `5/(6 v_3) - 1/(6 v_1) < 2/(3 v_4)`.
    3. `hlarge` gives the length lower bound `1/(3 v_3) ≤ 5/(6 v_3) - 1/(6 v_1)`
       (because `5 v_1 - v_3 ≥ 2 v_1`).
    4. Chain: `1/(3 v_3) < 2/(3 v_4)`, so `v_4 < 2 v_3`.

    Reusable across §8 sub-cases. -/
lemma bhk_8_v4_lt_2v3 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    (speeds ⟨3, by omega⟩ : ℝ) < 2 * (speeds ⟨2, by omega⟩ : ℝ) := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv1_le_v2 : v1 ≤ v2 := by
    rw [hv1_def, hv2_def]
    exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]
    exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv2_le_v3 : v2 ≤ v3 := by
    rw [hv2_def, hv3_def]
    exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega)))
  have hlargeR : v3 ≤ 3 * v1 := by
    rw [hv1_def, hv3_def]; exact_mod_cast hlarge
  -- (1) 123-gap inclusion `[1/(6 v_1), 5/(6 v_3)] ⊆ unsafeOf ⟨3⟩ ∪ unsafeOf ⟨4⟩`.
  have h_123_incl : Set.Icc (1 / (6 * v1)) (5 / (6 * v3)) ⊆
      unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    obtain ⟨htL, htR⟩ := ht
    obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
    rw [← mem_unsafeOf_iff] at hi_unsafe
    have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        rw [hv1_def] at htL; exact htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        calc t ≤ 5 / (6 * v3) := htR
          _ ≤ 5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
              rw [hv1_def] at hv1_le_v3 hv1_pos
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv1_le_v3, hv1_pos, hv3_pos]
    have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        calc (1 : ℝ) / (6 * (speeds ⟨1, by omega⟩ : ℝ))
            ≤ 1 / (6 * v1) := by
              rw [hv2_def] at hv1_le_v2
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv1_le_v2, hv1_pos, hv2_pos]
          _ ≤ t := by rw [hv1_def] at htL; exact htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        calc t ≤ 5 / (6 * v3) := htR
          _ ≤ 5 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) := by
              rw [hv2_def] at hv2_le_v3
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv2_le_v3, hv2_pos, hv3_pos]
    have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        calc (1 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
            ≤ 1 / (6 * v1) := by
              rw [hv3_def] at hv1_le_v3
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv1_le_v3, hv1_pos, hv3_pos]
          _ ≤ t := by rw [hv1_def] at htL; exact htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        rw [hv3_def] at htR; exact htR
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact absurd hi_unsafe hnot1
    · exact absurd hi_unsafe hnot2
    · exact Or.inl hi_unsafe
    · exact Or.inr hi_unsafe
  -- (2) `a ≤ b`: `1/(6 v_1) ≤ 5/(6 v_3)` from hlarge (`v_3 ≤ 3 v_1 ≤ 5 v_1`).
  have h_a_le_b : 1 / (6 * v1) ≤ 5 / (6 * v3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlargeR, hv1_pos, hv3_pos]
  -- (3) bhk_lemma_4 gives `5/(6 v_3) - 1/(6 v_1) < 2/(3 v_4)`.
  have h_len_bd : 5 / (6 * v3) - 1 / (6 * v1) < 2 / (3 * v4) := by
    have h := bhk_lemma_4 speeds hmono hpos
      (1 / (6 * v1)) (5 / (6 * v3)) h_a_le_b
      (by intro t ht; exact h_123_incl ht)
    rw [hv4_def]; exact h
  -- (4) `1/(3 v_3) ≤ 5/(6 v_3) - 1/(6 v_1)` from hlarge (`5 v_1 - v_3 ≥ 2 v_1`).
  have hbd : 1 / (3 * v3) ≤ 5 / (6 * v3) - 1 / (6 * v1) := by
    have key : (5 / (6 * v3) - 1 / (6 * v1)) * (6 * v3 * v1) = 5 * v1 - v3 := by
      field_simp
    have key2 : 1 / (3 * v3) * (6 * v3 * v1) = 2 * v1 := by
      field_simp; ring
    nlinarith [key, key2, hlargeR, hv1_pos, hv3_pos,
               mul_pos hv1_pos hv3_pos]
  -- (5) Chain: `1/(3 v_3) < 2/(3 v_4)`, hence `v_4 < 2 v_3`.
  have hlt : 1 / (3 * v3) < 2 / (3 * v4) := lt_of_le_of_lt hbd h_len_bd
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlt
  linarith

/-- **BHK Lemma 4 — weak version under BHK regime.** Same statement as
    `bhk_lemma_4` but with the extra hypothesis `2 v_3 ≤ v_4` (the BHK speed-
    ratio regime). This closes Case C unconditionally and gives a clean proof.

    Under `2 v_3 ≤ v_4`, the two gap-pieces in Case C (sum `= 1/(3 v_3)` each
    `< 1/(3 v_4)`) yield `1/(3 v_3) < 2/(3 v_4) ≤ 1/(3 v_3)`, contradiction. -/
theorem bhk_lemma_4_weak (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hbhk : 2 * (speeds ⟨3, by omega⟩ : ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))
    (a b : ℝ) (_hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩) :
    b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  have hv3pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_lt_v4 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmlt : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ :=
      hmono (show (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ by decide)
    exact_mod_cast hmlt
  set v3 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv3def
  set v4 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv4def
  by_contra hcontra
  push_neg at hcontra
  set L : ℝ := 2 / (3 * v3) with hLdef
  have hL_pos : 0 < L := by positivity
  set b' : ℝ := a + L with hb'def
  have hb'_le_b : b' ≤ b := by rw [hb'def]; linarith
  have hab' : a ≤ b' := by rw [hb'def]; linarith
  have hJ_sub : Set.Icc a b' ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                                unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ⟨ht1, ht2⟩
    exact hI ⟨ht1, le_trans ht2 hb'_le_b⟩
  set m : ℤ := ⌊v3 * a⌋ with hmdef
  set s : ℝ := Int.fract (v3 * a) with hsdef
  have hs_nonneg : 0 ≤ s := Int.fract_nonneg _
  have hs_lt_one : s < 1 := Int.fract_lt_one _
  have hva_eq : v3 * a = (m : ℝ) + s := by
    rw [hsdef, hmdef]
    have := Int.floor_add_fract (v3 * a)
    linarith
  have ha_eq : a = ((↑m : ℝ) + s) / v3 := by
    rw [eq_div_iff (ne_of_gt hv3pos)]; linarith [hva_eq]
  have hb'_eq : b' = ((↑m : ℝ) + s + 2/3) / v3 := by
    rw [hb'def, hLdef, ha_eq]
    field_simp
  -- Case split on s
  rcases lt_or_ge s (1/2) with hs_half | hs_half
  · -- Cases A and B: single gap-piece argument
    set sL : ℝ := max a ((↑m + 1/6) / v3) with hsLdef
    set sR : ℝ := min b' ((↑m + 5/6) / v3) with hsRdef
    have hsL_ge_a : a ≤ sL := le_max_left _ _
    have hsR_le_b' : sR ≤ b' := min_le_left _ _
    have hsL_ge_gap : ((↑m : ℝ) + 1/6) / v3 ≤ sL := le_max_right _ _
    have hsR_le_gap : sR ≤ ((↑m : ℝ) + 5/6) / v3 := min_le_right _ _
    have hsLR : sL ≤ sR := by
      rw [hsLdef, hsRdef, ha_eq, hb'_eq]
      apply max_le
      · apply le_min
        · exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
        · exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      · apply le_min
        · exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
        · exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
    have hgap : sR - sL < 1 / (3 * v4) :=
      gap_piece_bound speeds hpos a b' hab' hJ_sub m sL sR
        hsL_ge_a hsR_le_b' hsLR hsL_ge_gap hsR_le_gap
    have hgap_len_ge : 1 / (3 * v3) ≤ sR - sL := by
      rw [hsLdef, hsRdef, ha_eq, hb'_eq]
      have hmin_max : min ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) -
                       max ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) ≥ 1/3 := by
        rcases le_or_gt s (1/6) with hsA | hsA
        · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          linarith
        · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
          linarith
      have hmin_div : min (((↑m : ℝ) + s + 2/3) / v3) (((↑m : ℝ) + 5/6) / v3)
                      = min ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) / v3 := by
        rcases le_or_gt ((↑m : ℝ) + s + 2/3) ((↑m : ℝ) + 5/6) with h | h
        · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h (le_of_lt hv3pos))]
        · rw [min_eq_right (le_of_lt h),
              min_eq_right (div_le_div_of_nonneg_right (le_of_lt h) (le_of_lt hv3pos))]
      have hmax_div : max (((↑m : ℝ) + s) / v3) (((↑m : ℝ) + 1/6) / v3)
                      = max ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) / v3 := by
        rcases le_or_gt ((↑m : ℝ) + s) ((↑m : ℝ) + 1/6) with h | h
        · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h (le_of_lt hv3pos))]
        · rw [max_eq_left (le_of_lt h),
              max_eq_left (div_le_div_of_nonneg_right (le_of_lt h) (le_of_lt hv3pos))]
      rw [hmin_div, hmax_div, div_sub_div_same, le_div_iff₀ hv3pos]
      have : 1 / (3 * v3) * v3 = 1/3 := by field_simp
      rw [this]
      linarith
    have hcontr : 1 / (3 * v3) < 1 / (3 * v4) := lt_of_le_of_lt hgap_len_ge hgap
    have hv4_lt_v3 : v4 < v3 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hcontr
      linarith
    linarith
  · rcases lt_or_ge s (5/6) with hs_56 | hs_56
    · -- Case C closed using hypothesis 2 v_3 ≤ v_4
      -- Two gap-pieces: left [a, (m+5/6)/v3], right [(m+7/6)/v3, b']
      -- Each in U4 (by gap_piece_bound), each < 1/(3 v_4)
      -- Sum = 1/(3 v_3). So 1/(3 v_3) < 2/(3 v_4) ≤ 1/(3 v_3) under hbhk.
      -- Left gap-piece: sL1=a, sR1=(m+5/6)/v3, length (5/6-s)/v3
      have hLeft_le_b' : ((↑m : ℝ) + 5/6) / v3 ≤ b' := by
        rw [hb'_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hLeft_a_le_sR : a ≤ ((↑m : ℝ) + 5/6) / v3 := by
        rw [ha_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hLeft_gap_le_a : ((↑m : ℝ) + 1/6) / v3 ≤ a := by
        rw [ha_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hgap1 : ((↑m : ℝ) + 5/6) / v3 - a < 1 / (3 * v4) :=
        gap_piece_bound speeds hpos a b' hab' hJ_sub m a (((↑m : ℝ) + 5/6) / v3)
          (le_refl _) hLeft_le_b' hLeft_a_le_sR hLeft_gap_le_a (le_refl _)
      -- Right gap-piece: sL2=(m+7/6)/v3, sR2=b', length (b' - (m+7/6))/v3 = (s-1/2)/v3
      have hRight_a_le_sL : a ≤ ((↑m : ℝ) + 7/6) / v3 := by
        rw [ha_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hRight_sL_le_b' : ((↑m : ℝ) + 7/6) / v3 ≤ b' := by
        rw [hb'_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hRight_gap_le_sL : ((↑(m + 1) : ℝ) + 1/6) / v3 ≤ ((↑m : ℝ) + 7/6) / v3 := by
        push_cast
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hRight_b'_le_gap : b' ≤ ((↑(m + 1) : ℝ) + 5/6) / v3 := by
        rw [hb'_eq]; push_cast
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hgap2 : b' - ((↑m : ℝ) + 7/6) / v3 < 1 / (3 * v4) :=
        gap_piece_bound speeds hpos a b' hab' hJ_sub (m+1) (((↑m : ℝ) + 7/6) / v3) b'
          hRight_a_le_sL (le_refl _) hRight_sL_le_b' hRight_gap_le_sL hRight_b'_le_gap
      -- Sum: ((m+5/6)/v3 - a) + (b' - (m+7/6)/v3) = (m+5/6)/v3 - a + b' - (m+7/6)/v3
      --    = b' - a + (5/6 - 7/6)/v3 = 2/(3v3) - 1/(3v3) = 1/(3v3)
      have hsum_eq : (((↑m : ℝ) + 5/6) / v3 - a) + (b' - ((↑m : ℝ) + 7/6) / v3)
                       = 1 / (3 * v3) := by
        rw [ha_eq, hb'_eq]
        field_simp
        ring
      have hsum_lt : (((↑m : ℝ) + 5/6) / v3 - a) + (b' - ((↑m : ℝ) + 7/6) / v3)
                       < 2 / (3 * v4) := by
        have hadd := add_lt_add hgap1 hgap2
        have heq : 1 / (3 * v4) + 1 / (3 * v4) = 2 / (3 * v4) := by ring
        linarith
      rw [hsum_eq] at hsum_lt
      -- 1/(3 v3) < 2/(3 v4), and hbhk : 2 v3 ≤ v4
      -- 2/(3 v4) ≤ 2/(3 · 2 v3) = 1/(3 v3)
      have h2v4 : 2 / (3 * v4) ≤ 1 / (3 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hbhk, hv3pos]
      linarith
    · -- Case D
      set sL : ℝ := ((↑m : ℝ) + 7/6) / v3 with hsLdef
      let sR : ℝ := b'
      have hsL_ge_a : a ≤ sL := by
        rw [hsLdef, ha_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hsR_le_b' : sR ≤ b' := le_refl _
      have hsLR : sL ≤ sR := by
        change sL ≤ b'
        rw [hsLdef, hb'_eq]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hsL_ge_gap : ((↑(m + 1) : ℝ) + 1/6) / v3 ≤ sL := by
        rw [hsLdef]; push_cast
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hsR_le_gap : sR ≤ ((↑(m + 1) : ℝ) + 5/6) / v3 := by
        change b' ≤ _
        rw [hb'_eq]; push_cast
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hv3pos)
      have hgap : sR - sL < 1 / (3 * v4) :=
        gap_piece_bound speeds hpos a b' hab' hJ_sub (m+1) sL sR
          hsL_ge_a hsR_le_b' hsLR hsL_ge_gap hsR_le_gap
      have hgap_len_ge : 1 / (3 * v3) ≤ sR - sL := by
        change 1 / (3 * v3) ≤ b' - sL
        rw [hsLdef, hb'_eq, div_sub_div_same, le_div_iff₀ hv3pos]
        have : 1 / (3 * v3) * v3 = 1/3 := by field_simp
        rw [this]
        linarith
      have hcontr : 1 / (3 * v3) < 1 / (3 * v4) := lt_of_le_of_lt hgap_len_ge hgap
      have hv4_lt_v3 : v4 < v3 := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hcontr
        linarith
      linarith

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
