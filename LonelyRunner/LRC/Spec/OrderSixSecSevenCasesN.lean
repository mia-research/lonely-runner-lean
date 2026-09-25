import LonelyRunner.LRC.Spec.OrderSixSecSevenN
import LonelyRunner.LRC.Spec.NamedWindowSixN

/-!
# Order six, BHK §7: the exceptional orbits, `G₄`, `G₇` and small `n`, in the framework

2026-09-24.  The meeting-time orbit of BHK §7 either lands in BHK's box — handled in
`OrderSixSecSevenN.lean` by the exact merge and the two-flank window — or has a short step.  This
file carries the short-step cases, the exceptional groups `G₄` and `G₇`, and the small orbits
`n ≤ 6`.  Every witness is a meeting time `k/D` checked by the framework's meeting-time window
(`bhk_s7_witness`, `bhk_s7_witness_num`, both proved from `lonely_of_meeting`); Corollary 5 is the
two-flank window rule; orbit membership is the residue condition `OnOrbit`.  The blocked-zone
vocabulary (`unsafeOf`, `block_containment`, …) is the framework's lap arithmetic under BHK's
names, so that the case bookkeeping reads line for line against BHK.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Set

namespace LRC.OrderSixN.S7

open LRC.OrderSixN


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


/-! ## Fract helpers -/

/-- **No-wraparound fract translation.** If `{vτ} + vδ` stays in `[0, 1)`
    then `{v(τ+δ)} = {vτ} + vδ`. -/
lemma bhk_fract_translate (v τ δ : ℝ)
    (h0 : 0 ≤ Int.fract (v * τ) + v * δ)
    (h1 : Int.fract (v * τ) + v * δ < 1) :
    Int.fract (v * (τ + δ)) = Int.fract (v * τ) + v * δ := by
  have hsplit : v * (τ + δ) = (⌊v * τ⌋ : ℝ) + (Int.fract (v * τ) + v * δ) := by
    have h : Int.fract (v * τ) + ⌊v * τ⌋ = v * τ := Int.fract_add_floor (v * τ)
    nlinarith [h]
  rw [hsplit, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- **Rectangle fract-condition to interval bounds.** For `ρ ∈ [0, 1)` and
    an anchored window `[c, c + L]` with `c ≥ 0`, `c + L < 1`:
    `{ρ - c} ≤ L` forces `c ≤ ρ ≤ c + L`. -/
lemma bhk_fract_window (ρ c L : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : 0 ≤ c) (hcL : c + L < 1) (h : Int.fract (ρ - c) ≤ L) :
    c ≤ ρ ∧ ρ ≤ c + L := by
  have hL0 : 0 ≤ L := le_trans (Int.fract_nonneg _) h
  by_cases hge : c ≤ ρ
  · have hin : Int.fract (ρ - c) = ρ - c :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hin] at h
    exact ⟨hge, by linarith⟩
  · -- ρ < c: then ρ - c ∈ (-1, 0), so {ρ - c} = ρ - c + 1 ≤ L gives ρ < 0.
    exfalso
    have hlt : ρ < c := not_le.mp hge
    have hin : Int.fract (ρ - c) = ρ - c + 1 := by
      have h1 : Int.fract (ρ - c) = Int.fract (ρ - c + 1) :=
        (Int.fract_add_one _).symm
      rw [h1, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hin] at h
    linarith

/-- **Fract of a rational with natural numerator.** For naturals `a`, `n`
    with `0 < n`: `{a/n} = (a % n)/n`. -/
lemma bhk_fract_nat_div (a n : ℕ) (hn : 0 < n) :
    Int.fract ((a : ℝ) / n) = ((a % n : ℕ) : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdecomp : (a : ℝ) / n = ((a % n : ℕ) : ℝ) / n + ((a / n : ℕ) : ℤ) := by
    have h : (a : ℝ) = ((a % n : ℕ) : ℝ) + ((a / n : ℕ) : ℝ) * n := by
      exact_mod_cast (Nat.mod_add_div' a n).symm
    have h2 : (((a / n : ℕ) : ℤ) : ℝ) = ((a / n : ℕ) : ℝ) := Int.cast_natCast _
    rw [h2, h]
    field_simp
  rw [hdecomp, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by positivity, by
    rw [div_lt_one hnR]
    exact_mod_cast Nat.mod_lt a hn⟩]

/-- **Fract-zero iff divides.** For naturals `a`, `d` with `0 < d`:
    `{a/d} = 0 ↔ d ∣ a`. -/
lemma bhk_fract_nat_div_eq_zero_iff (a d : ℕ) (hd : 0 < d) :
    Int.fract ((a : ℝ) / d) = 0 ↔ d ∣ a := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [bhk_fract_nat_div a d hd, div_eq_zero_iff]
  have hdne : ((d : ℝ)) ≠ 0 := ne_of_gt hdR
  simp only [hdne, or_false, Nat.cast_eq_zero]
  omega

/-! ## The bridge: torus window → lonely time -/


/-- **Mod of a scaled multiple.** `c·(m·m₀) ≡ (c·m₀ mod n)·m (mod n)`. -/
lemma bhk_s7_mul_mod (c m₀ m n : ℕ) :
    c * (m * m₀) % n = (c * m₀ % n) * m % n := by
  rw [show c * (m * m₀) = (c * m₀) * m from by ring,
      Nat.mul_mod (c * m₀) m n, Nat.mul_mod (c * m₀ % n) m n,
      Nat.mod_mod_of_dvd _ dvd_rfl]

/-- **Mod of a negative-residue multiple.** For `0 < r`, `0 < m`,
    `r·m < n`: `(n − r)·m ≡ n − r·m (mod n)`. -/
lemma bhk_s7_neg_mod (n r m : ℕ) (hr : 0 < r) (hm : 0 < m) (hrm : r * m < n) :
    (n - r) * m % n = n - r * m := by
  have h3 : r ≤ r * m := by
    calc r = r * 1 := (mul_one r).symm
    _ ≤ r * m := Nat.mul_le_mul_left r hm
  have hppos : 0 < r * m := Nat.mul_pos hr hm
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le (r * m)) hrm
  have h1 : (n - r) * m = n * (m - 1) + (n - r * m) := by
    zify [show r ≤ n by omega, show 1 ≤ m from hm, show r * m ≤ n from hrm.le]
    ring
  rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hn0 hppos)]

/-- **Window form of mod.** If `q·n ≤ x < (q+1)·n` then `x % n = x − q·n`. -/
lemma bhk_s7_mod_window (x q n : ℕ) (h1 : q * n ≤ x) (h2 : x < (q + 1) * n) :
    x % n = x - q * n := by
  have h3 : (q + 1) * n = q * n + n := by ring
  conv_lhs => rw [show x = (x - q * n) + q * n from by omega]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Bezout witness mod `n`.** For every `c` there is a `t` with
    `c·t ≡ gcd(n, c) (mod n)`. -/
lemma bhk_s7_bezout_mod (n c : ℕ) (hn : 0 < n) :
    ∃ t : ℕ, c * t % n = Nat.gcd n c % n := by
  have hB : (Nat.gcd n c : ℤ) = n * Nat.gcdA n c + c * Nat.gcdB n c :=
    Nat.gcd_eq_gcd_ab n c
  set b : ℤ := Nat.gcdB n c with hb_def
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  refine ⟨(b % n).toNat, ?_⟩
  have hbt : (((b % n).toNat : ℕ) : ℤ) = b % n :=
    Int.toNat_of_nonneg (Int.emod_nonneg b hnZ.ne')
  have key : ((c * (b % n).toNat : ℕ) : ℤ) % n = ((Nat.gcd n c : ℕ) : ℤ) % n := by
    push_cast
    rw [hbt]
    have h2 : ((c : ℤ) * (b % n)) % n = ((c : ℤ) * b) % n := by
      conv_lhs => rw [Int.mul_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.mul_emod]
    have h1 : (c : ℤ) * b = (Nat.gcd n c : ℤ) - n * Nat.gcdA n c := by
      rw [hB]; ring
    rw [h2, h1, Int.sub_mul_emod_self_left]
  have keyN : (((c * (b % n).toNat) % n : ℕ) : ℤ) = ((Nat.gcd n c % n : ℕ) : ℤ) := by
    push_cast
    exact key
  exact_mod_cast keyN

/-- **Gcd is determined by residues.**
    `gcd(n, gcd(a mod n, b mod n)) = gcd(n, gcd(a, b))`. -/
lemma bhk_s7_gcd_mod (n a b : ℕ) :
    Nat.gcd n (Nat.gcd (a % n) (b % n)) = Nat.gcd n (Nat.gcd a b) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have hn := Nat.gcd_dvd_left n (Nat.gcd (a % n) (b % n))
    have ha := (Nat.gcd_dvd_right n _).trans (Nat.gcd_dvd_left (a % n) (b % n))
    have hb := (Nat.gcd_dvd_right n _).trans (Nat.gcd_dvd_right (a % n) (b % n))
    exact Nat.dvd_gcd ((Nat.dvd_mod_iff hn).mp ha) ((Nat.dvd_mod_iff hn).mp hb)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have hn := Nat.gcd_dvd_left n (Nat.gcd a b)
    have ha := (Nat.gcd_dvd_right n _).trans (Nat.gcd_dvd_left a b)
    have hb := (Nat.gcd_dvd_right n _).trans (Nat.gcd_dvd_right a b)
    exact Nat.dvd_gcd ((Nat.dvd_mod_iff hn).mpr ha) ((Nat.dvd_mod_iff hn).mpr hb)


/-- **Congruence-solver kernel.** If `a·m = q·n + Δ` with `Δ < n` then
    `a·m ≡ Δ (mod n)`. -/
lemma bhk_s7_solve_aux (n a m q Δ : ℕ) (hΔ : Δ < n)
    (key : a * m = q * n + Δ) :
    a * m % n = Δ := by
  rw [key, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hΔ]

/-- Solve `2m ≡ Δ (mod n)` when `Δ` is even or `n` is odd. -/
lemma bhk_s7_solve2 (n Δ : ℕ) (hΔ : Δ < n) (h : Δ % 2 = 0 ∨ n % 2 = 1) :
    ∃ m : ℕ, 2 * m % n = Δ := by
  rcases h with h | h
  · exact ⟨Δ / 2, by
      rw [show 2 * (Δ / 2) = Δ from by omega, Nat.mod_eq_of_lt hΔ]⟩
  · refine ⟨Δ * ((n + 1) / 2), bhk_s7_solve_aux n 2 _ Δ Δ hΔ ?_⟩
    have he : 2 * ((n + 1) / 2) = n + 1 := by omega
    calc 2 * (Δ * ((n + 1) / 2)) = Δ * (2 * ((n + 1) / 2)) := by ring
      _ = Δ * (n + 1) := by rw [he]
      _ = Δ * n + Δ := by ring

/-- Solve `3m ≡ Δ (mod n)` when `3 ∣ Δ` or `3 ∤ n`. -/
lemma bhk_s7_solve3 (n Δ : ℕ) (hΔ : Δ < n) (h : Δ % 3 = 0 ∨ n % 3 ≠ 0) :
    ∃ m : ℕ, 3 * m % n = Δ := by
  rcases h with h | h
  · exact ⟨Δ / 3, by
      rw [show 3 * (Δ / 3) = Δ from by omega, Nat.mod_eq_of_lt hΔ]⟩
  · rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h3 | h3
    · refine ⟨Δ * ((2 * n + 1) / 3), bhk_s7_solve_aux n 3 _ (2 * Δ) Δ hΔ ?_⟩
      have he : 3 * ((2 * n + 1) / 3) = 2 * n + 1 := by omega
      calc 3 * (Δ * ((2 * n + 1) / 3)) = Δ * (3 * ((2 * n + 1) / 3)) := by ring
        _ = Δ * (2 * n + 1) := by rw [he]
        _ = 2 * Δ * n + Δ := by ring
    · refine ⟨Δ * ((n + 1) / 3), bhk_s7_solve_aux n 3 _ Δ Δ hΔ ?_⟩
      have he : 3 * ((n + 1) / 3) = n + 1 := by omega
      calc 3 * (Δ * ((n + 1) / 3)) = Δ * (3 * ((n + 1) / 3)) := by ring
        _ = Δ * (n + 1) := by rw [he]
        _ = Δ * n + Δ := by ring

/-- Solve `4m ≡ Δ (mod n)` when `4 ∣ Δ`, or `n` is odd, or
    `n ≡ 2 (mod 4)` and `Δ` is even. -/
lemma bhk_s7_solve4 (n Δ : ℕ) (hΔ : Δ < n)
    (h : Δ % 4 = 0 ∨ n % 2 = 1 ∨ (n % 4 = 2 ∧ Δ % 2 = 0)) :
    ∃ m : ℕ, 4 * m % n = Δ := by
  rcases h with h | h | ⟨h4, hΔ2⟩
  · exact ⟨Δ / 4, by
      rw [show 4 * (Δ / 4) = Δ from by omega, Nat.mod_eq_of_lt hΔ]⟩
  · rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h4 | h4
    · refine ⟨Δ * ((3 * n + 1) / 4), bhk_s7_solve_aux n 4 _ (3 * Δ) Δ hΔ ?_⟩
      have he : 4 * ((3 * n + 1) / 4) = 3 * n + 1 := by omega
      calc 4 * (Δ * ((3 * n + 1) / 4)) = Δ * (4 * ((3 * n + 1) / 4)) := by ring
        _ = Δ * (3 * n + 1) := by rw [he]
        _ = 3 * Δ * n + Δ := by ring
    · refine ⟨Δ * ((n + 1) / 4), bhk_s7_solve_aux n 4 _ Δ Δ hΔ ?_⟩
      have he : 4 * ((n + 1) / 4) = n + 1 := by omega
      calc 4 * (Δ * ((n + 1) / 4)) = Δ * (4 * ((n + 1) / 4)) := by ring
        _ = Δ * (n + 1) := by rw [he]
        _ = Δ * n + Δ := by ring
  · refine ⟨Δ / 2 * ((n + 2) / 4), bhk_s7_solve_aux n 4 _ (Δ / 2) Δ hΔ ?_⟩
    have he : 4 * ((n + 2) / 4) = n + 2 := by omega
    have hΔ' : 2 * (Δ / 2) = Δ := by omega
    calc 4 * (Δ / 2 * ((n + 2) / 4)) = Δ / 2 * (4 * ((n + 2) / 4)) := by ring
      _ = Δ / 2 * (n + 2) := by rw [he]
      _ = Δ / 2 * n + 2 * (Δ / 2) := by ring
      _ = Δ / 2 * n + Δ := by rw [hΔ']

/-! ## (13)-minimal selection (BHK §3.3) -/


/-! ## The framework's replacements for BHK's mechanisms -/

/-- A residue pair read off a multiple is on the orbit. -/
theorem onOrbit_of_res {n c₃ c₁ k : ℕ} (hn : 0 < n) {x y : ℤ}
    (hx : x % n = ((c₃ * k % n : ℕ) : ℤ)) (hy : y % n = ((c₁ * k % n : ℕ) : ℤ)) :
    OnOrbit n c₃ c₁ x y := by
  refine ⟨k % n, Nat.mod_lt _ hn, ?_, ?_⟩
  · rw [hx, Nat.mul_mod_mod]
  · rw [hy, Nat.mul_mod_mod]

/-- **BHK Corollary 5, in the framework.**  A window of length `2/(3v₃)` on which the three slow
runners are clear holds an instant where the two fast runners are clear too — the two-flank window
rule (`two_flank_window`), which names it (the window's start or an opening). -/
theorem bhk_corollary_5 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (h123gap : Set.Icc a b ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
                              unsafeOf speeds ⟨1, by omega⟩ ∪
                              unsafeOf speeds ⟨2, by omega⟩)ᶜ)
    (h3len : 2 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ b - a) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have h3 : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by norm_num) : (Fin.mk 2 (by norm_num) : Fin 5) < Fin.mk 3 (by norm_num))
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < speeds ⟨4, by omega⟩ := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by norm_num) : (Fin.mk 3 (by norm_num) : Fin 5) < Fin.mk 4 (by norm_num))
  have h4 : (0 : ℝ) < speeds ⟨3, by omega⟩ := by linarith
  have hL : 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) ≤ b - a :=
    le_trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)) h3len
  obtain ⟨t, h1, h2, c4, c5, -⟩ := LRC.SpecN.two_flank_window h4 h45 a hL
  have hs := h123gap ⟨h1, by linarith⟩
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hs
  obtain ⟨⟨n0, n1⟩, n2⟩ := hs
  have cl : ∀ i, t ∉ unsafeOf speeds i → circDist ((speeds i : ℝ) * t) ≥ 1 / 6 := fun i h =>
    not_lt.mp ((mem_unsafeOf_iff speeds i t).not.mp h)
  refine ⟨t, fun i => ?_⟩
  fin_cases i
  · exact cl _ n0
  · exact cl _ n1
  · exact cl _ n2
  · simpa [one_div] using c4
  · simpa [one_div] using c5

/-- **BHK's witness at a meeting time, in the framework** (`lonely_of_meeting`): runners 2 and 3
merged exactly at `τ = k/D`, runner 1 inside the parallelogram. -/
lemma bhk_s7_witness (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (n c₃ c₁ g : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (k : ℕ)
    (hu_lo : 1/6 ≤ ((c₃ * k % n : ℕ) : ℝ) / n)
    (hu_hi : ((c₃ * k % n : ℕ) : ℝ) / n ≤ 5/6)
    (hw_lo : 1/6 + (((c₃ * k % n : ℕ) : ℝ) / n - 1/6) *
               (speeds ⟨0, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
             ≤ ((c₁ * k % n : ℕ) : ℝ) / n)
    (hw_hi : ((c₁ * k % n : ℕ) : ℝ) / n
             ≤ 5/6 - (5/6 - ((c₃ * k % n : ℕ) : ℝ) / n) *
               (speeds ⟨0, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have m : ∀ i j : Fin 5, i < j → speeds i < speeds j := fun i j h => hmono h
  have h12 := m ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by norm_num))
  have h23 := m ⟨1, by omega⟩ ⟨2, by omega⟩ (Fin.mk_lt_mk.mpr (by norm_num))
  have h34 := m ⟨2, by omega⟩ ⟨3, by omega⟩ (Fin.mk_lt_mk.mpr (by norm_num))
  have h45 := m ⟨3, by omega⟩ ⟨4, by omega⟩ (Fin.mk_lt_mk.mpr (by norm_num))
  have nR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have gR : (0 : ℝ) < g := by exact_mod_cast hgpos
  set V1 := speeds ⟨0, by omega⟩
  set V2 := speeds ⟨1, by omega⟩
  set V3 := speeds ⟨2, by omega⟩
  set U := c₃ * k % n with hU
  set W := c₁ * k % n with hW
  set τ : ℝ := (k : ℝ) / (g * n) with hτ
  have hDR : ((g * n : ℕ) : ℝ) = (V3 : ℝ) - V2 := by rw [hd, Nat.cast_sub h23.le]
  have e3 : (V3 : ℝ) * τ = (((c₃ * k / n : ℕ) : ℤ) : ℝ) + (U : ℝ) / n := by
    have hdm : ((c₃ * k : ℕ) : ℝ) = n * ((c₃ * k / n : ℕ) : ℝ) + U := by
      exact_mod_cast (Nat.div_add_mod (c₃ * k) n).symm
    rw [hτ, ← hc3, Int.cast_natCast]; push_cast at hdm ⊢
    field_simp; linarith
  have e1 : (V1 : ℝ) * τ = (((c₁ * k / n : ℕ) : ℤ) : ℝ) + (W : ℝ) / n := by
    have hdm : ((c₁ * k : ℕ) : ℝ) = n * ((c₁ * k / n : ℕ) : ℝ) + W := by
      exact_mod_cast (Nat.div_add_mod (c₁ * k) n).symm
    rw [hτ, ← hc1, Int.cast_natCast]; push_cast at hdm ⊢
    field_simp; linarith
  have e2 : (V2 : ℝ) * τ = ((((c₃ * k / n : ℕ) : ℤ) - k : ℤ) : ℝ) + (U : ℝ) / n := by
    have hv2 : (V2 : ℝ) = V3 - g * n := by
      have := hDR; push_cast at this; linarith
    rw [hv2, sub_mul, e3, hτ]
    push_cast
    field_simp
    ring
  obtain ⟨t, -, c1, c2, c3, c4, c5⟩ := lonely_of_meeting (v4 := speeds ⟨3, by omega⟩)
    (v5 := speeds ⟨4, by omega⟩) (hpos _) h12 h23 h34 h45 (by positivity) e3 e2 e1
    hu_lo hu_hi hw_lo hw_hi
  refine ⟨t, fun i => ?_⟩
  fin_cases i
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5

/-- **BHK's whole-number witness window** (framework: the meeting-time window with `3v₁ < v₃`). -/
lemma bhk_s7_witness_num (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (h_ulo : n ≤ 6 * (c₃ * k % n)) (h_uhi : 6 * (c₃ * k % n) ≤ 5 * n)
    (h_wlo : n + 3 * (c₃ * k % n) ≤ 9 * (c₁ * k % n))
    (h_whi : 9 * (c₁ * k % n) ≤ 5 * n + 3 * (c₃ * k % n)) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have nR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have v1R : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos _
  have v3R : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hsR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hsmall
  set u : ℝ := ((c₃ * k % n : ℕ) : ℝ) / n with hu
  set w : ℝ := ((c₁ * k % n : ℕ) : ℝ) / n with hw
  have a1 : (n : ℝ) ≤ 6 * ((c₃ * k % n : ℕ) : ℝ) := by exact_mod_cast h_ulo
  have a2 : 6 * ((c₃ * k % n : ℕ) : ℝ) ≤ 5 * n := by exact_mod_cast h_uhi
  have a3 : (n : ℝ) + 3 * ((c₃ * k % n : ℕ) : ℝ) ≤ 9 * ((c₁ * k % n : ℕ) : ℝ) := by
    exact_mod_cast h_wlo
  have a4 : 9 * ((c₁ * k % n : ℕ) : ℝ) ≤ 5 * n + 3 * ((c₃ * k % n : ℕ) : ℝ) := by
    exact_mod_cast h_whi
  have hu1 : 1 / 6 ≤ u := by rw [hu, le_div_iff₀ nR]; linarith
  have hu2 : u ≤ 5 / 6 := by rw [hu, div_le_iff₀ nR]; linarith
  have hw1 : 1 / 9 + u / 3 ≤ w := by
    rw [hu, hw, show 1 / 9 + ((c₃ * k % n : ℕ) : ℝ) / n / 3 =
      ((n : ℝ) + 3 * ((c₃ * k % n : ℕ) : ℝ)) / (9 * n) by field_simp; ring,
      div_le_div_iff₀ (by positivity) nR]
    nlinarith
  have hw2 : w ≤ 5 / 9 + u / 3 := by
    rw [hu, hw, show 5 / 9 + ((c₃ * k % n : ℕ) : ℝ) / n / 3 =
      (5 * (n : ℝ) + 3 * ((c₃ * k % n : ℕ) : ℝ)) / (9 * n) by field_simp; ring,
      div_le_div_iff₀ nR (by positivity)]
    nlinarith
  have hr : (speeds ⟨0, by omega⟩ : ℝ) / speeds ⟨2, by omega⟩ ≤ 1 / 3 := by
    rw [div_le_iff₀ v3R]; linarith
  have hr0 : 0 ≤ (speeds ⟨0, by omega⟩ : ℝ) / speeds ⟨2, by omega⟩ := by positivity
  refine bhk_s7_witness speeds hmono hpos n c₃ c₁ g hnpos hgpos hd hc3 hc1 k hu1 hu2 ?_ ?_
  · rw [mul_div_assoc]
    have : (u - 1 / 6) * ((speeds ⟨0, by omega⟩ : ℝ) / speeds ⟨2, by omega⟩) ≤ (u - 1 / 6) / 3 := by
      nlinarith
    linarith
  · rw [mul_div_assoc]
    have : (5 / 6 - u) * ((speeds ⟨0, by omega⟩ : ℝ) / speeds ⟨2, by omega⟩) ≤ (5 / 6 - u) / 3 := by
      nlinarith
    linarith


/-- **The `G₄` 123-gap.** If at time `τ` the fractional positions are
    `{v₁τ} = 1/4`, `{v₂τ} = {v₃τ} = 1/2`, then on the whole interval
    `[τ - 1/(12 v₁), τ + 1/(3 v₃)]` runners 1, 2, 3 stay safe
    (BHK: `I = [kt₀ - x₁/12, kt₀ + 1/3]` is a 123-gap). Uses
    `3 v₁ < v₃ < 4 v₁` so that the slower runners cannot wrap. -/
lemma bhk_g4_123_gap (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (h41 : speeds ⟨2, by omega⟩ < 4 * speeds ⟨0, by omega⟩)
    (τ : ℝ)
    (hf1 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) * τ) = 1/4)
    (hf2 : Int.fract ((speeds ⟨1, by omega⟩ : ℝ) * τ) = 1/2)
    (hf3 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) * τ) = 1/2)
    (t : ℝ)
    (ht : t ∈ Set.Icc (τ - 1/(12 * (speeds ⟨0, by omega⟩ : ℝ)))
                      (τ + 1/(3 * (speeds ⟨2, by omega⟩ : ℝ)))) :
    t ∉ unsafeOf speeds ⟨0, by omega⟩ ∧ t ∉ unsafeOf speeds ⟨1, by omega⟩ ∧
    t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
  have hv1pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2pos : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv12 : (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (0:ℕ) < 1))
  have hv23 : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2))
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  have h41R : (speeds ⟨2, by omega⟩ : ℝ) < 4 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast h41
  obtain ⟨ht_lo, ht_hi⟩ := ht
  -- Generic safety step: runner with fract position f at τ, staying within
  -- [f - 1/3·(v/v wraps)] — done per runner with explicit floor anchors.
  have key : ∀ j : Fin 5, ∀ f : ℝ, Int.fract ((speeds j : ℝ) * τ) = f →
      1/6 ≤ f - (speeds j : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) →
      f + (speeds j : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 5/6 →
      t ∉ unsafeOf speeds j := by
    intro j f hf hlo hhi
    have hvjpos : (0 : ℝ) < (speeds j : ℝ) := by exact_mod_cast hpos _
    have hfloor : ((⌊(speeds j : ℝ) * τ⌋ : ℝ)) + f = (speeds j : ℝ) * τ := by
      rw [← hf]; exact Int.floor_add_fract _
    apply not_mem_unsafeOf_of_in_gap speeds j (hpos _) ⌊(speeds j : ℝ) * τ⌋ t
    · rw [div_le_iff₀ hvjpos]
      have h1 : (speeds j : ℝ) * t ≥ (speeds j : ℝ) * τ -
          (speeds j : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) := by
        have := mul_le_mul_of_nonneg_left ht_lo (le_of_lt hvjpos)
        have hxx : (speeds j : ℝ) * (τ - 1/(12 * (speeds ⟨0, by omega⟩ : ℝ))) =
            (speeds j : ℝ) * τ - (speeds j : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) := by
          ring
        linarith [hxx ▸ this]
      nlinarith [h1, hfloor, hlo]
    · rw [le_div_iff₀ hvjpos]
      have h2 : (speeds j : ℝ) * t ≤ (speeds j : ℝ) * τ +
          (speeds j : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        have := mul_le_mul_of_nonneg_left ht_hi (le_of_lt hvjpos)
        have hxx : (speeds j : ℝ) * (τ + 1/(3 * (speeds ⟨2, by omega⟩ : ℝ))) =
            (speeds j : ℝ) * τ + (speeds j : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) := by
          ring
        linarith [hxx ▸ this]
      nlinarith [h2, hfloor, hhi]
  refine ⟨key _ (1/4) hf1 ?_ ?_, key _ (1/2) hf2 ?_ ?_, key _ (1/2) hf3 ?_ ?_⟩
  · -- 1/6 ≤ 1/4 - v₁/(12 v₁) = 1/4 - 1/12
    have : (speeds ⟨0, by omega⟩ : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) = 1/12 := by
      field_simp
    rw [this]; norm_num
  · -- 1/4 + v₁/(3 v₃) ≤ 1/4 + 1/9 ≤ 5/6 since 3 v₁ < v₃
    have : (speeds ⟨0, by omega⟩ : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1/9 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/6 ≤ 1/2 - v₂/(12 v₁) since v₂ < 4 v₁
    have : (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) ≤ 1/3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/2 + v₂/(3 v₃) ≤ 1/2 + 1/3 = 5/6 since v₂ < v₃
    have : (speeds ⟨1, by omega⟩ : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1/3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/6 ≤ 1/2 - v₃/(12 v₁) since v₃ < 4 v₁
    have : (speeds ⟨2, by omega⟩ : ℝ) / (12 * (speeds ⟨0, by omega⟩ : ℝ)) ≤ 1/3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/2 + v₃/(3 v₃) = 1/2 + 1/3 = 5/6
    have : (speeds ⟨2, by omega⟩ : ℝ) / (3 * (speeds ⟨2, by omega⟩ : ℝ)) = 1/3 := by
      field_simp
    rw [this]; norm_num

/-- **The exceptional groups' finish, at named instants.**  Given BHK's 123-window `[A, B]`
(runners 1–3 clear throughout, longer than `7/(12v₃)`), the five runners are lonely at a named
instant: `t* = 1/(6v₁)` when `v₅ ≤ 5v₁`; otherwise the window rule `lonely_of_123_window`
(two-flank window, runner 4's clear stretches, runner 5's openings and closings, or `2/(3v₃)`). -/
lemma bhk_s7_named (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h41 : speeds ⟨2, by omega⟩ < 4 * speeds ⟨0, by omega⟩) (A B : ℝ)
    (hL : 7 / (12 * (speeds ⟨2, by omega⟩ : ℝ)) < B - A)
    (htail : 5 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) →
      1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) ≤ B - A - 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h123 : ∀ t ∈ Set.Icc A B, t ∉ unsafeOf speeds ⟨0, by omega⟩ ∧
      t ∉ unsafeOf speeds ⟨1, by omega⟩ ∧ t ∉ unsafeOf speeds ⟨2, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hlt : ∀ a b : Fin 5, a < b → (speeds a : ℝ) < (speeds b : ℝ) :=
    fun a b h => by exact_mod_cast hmono h
  have r01 := hlt ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have r12 := hlt ⟨1, by omega⟩ ⟨2, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have r23 := hlt ⟨2, by omega⟩ ⟨3, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have r34 := hlt ⟨3, by omega⟩ ⟨4, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have p0 : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos _
  have h41R : (speeds ⟨2, by omega⟩ : ℝ) < 4 * (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast h41
  have hall : ∀ i : Fin 5, (speeds ⟨0, by omega⟩ : ℝ) ≤ speeds i ∧
      (speeds i : ℝ) ≤ speeds ⟨4, by omega⟩ := fun i =>
    ⟨by exact_mod_cast hmono.monotone (show (⟨0, by omega⟩ : Fin 5) ≤ i from i.zero_le),
     by exact_mod_cast hmono.monotone (show i ≤ (⟨4, by omega⟩ : Fin 5) from i.le_last)⟩
  by_cases h5 : (speeds ⟨4, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨0, by omega⟩ : ℝ)
  · -- `t* = 1/(6v₁)`: every runner reads `vᵢ/(6v₁) ∈ [1/6, 5/6]`
    refine ⟨1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)), fun i => ?_⟩
    obtain ⟨hi0, hi4⟩ := hall i
    have e : (speeds i : ℝ) * (1 / (6 * (speeds ⟨0, by omega⟩ : ℝ))) =
        (speeds i : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by ring
    have hlo : ((0 : ℤ) : ℝ) + 6⁻¹ ≤ (speeds i : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
      rw [Int.cast_zero, zero_add, inv_eq_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have hhi : (speeds i : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) ≤ ((0 : ℤ) : ℝ) + 5 / 6 := by
      rw [Int.cast_zero, zero_add, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := LRC.SpecN.clear_of_band_six 0 hlo hhi
    rw [e, ge_iff_le, one_div]; exact this
  push Not at h5
  have clear : ∀ (i : Fin 5) (t : ℝ), t ∉ unsafeOf speeds i →
      (6 : ℝ)⁻¹ ≤ circDist ((speeds i : ℝ) * t) := by
    intro i t h
    rw [mem_unsafeOf_iff] at h; push Not at h; rwa [one_div] at h
  obtain ⟨t, c0, c1, c2, c3, c4⟩ := lonely_of_123_window p0 r01 r12 r23 r34 h41R hL (htail h5)
    (fun t h1 h2 => by
      obtain ⟨u0, u1, u2⟩ := h123 t ⟨h1, h2⟩
      exact ⟨clear _ t u0, clear _ t u1, clear _ t u2⟩)
  refine ⟨t, fun i => ?_⟩
  rw [ge_iff_le, one_div]
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4

/-! ## The exceptional groups `G₄` and `G₇`, at named instants -/

/-- **BHK exceptional group `G₄` (named instants).** `n = 4` with generator class
    `±(2, 1)`: the group `{(0,0), (2,1), (0,2), (2,3)}/4` misses the open
    parallelogram `P` exactly when `v₃ < 4 v₁` (i.e. `3 < x₁ < 4`).
    BHK pp. 44–45: pick `k` with `{v₃kt₀} = 1/2`, `{v₁kt₀} = 1/4`
    (`k ∈ {1, 3}` by `c₁ ≡ ±1 (mod 4)`); `[kt₀ - 1/(12v₁), kt₀ + 1/(3v₃)]`
    is a 123-gap (`bhk_g4_123_gap`), and `bhk_s7_named` names the lonely
    instant on it (`t* = 1/(6v₁)`, a runner-4/5 opening or closing in the
    window, or `2/(3v₃)`).  No contradiction over time. -/
lemma bhk_s7_g4_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (h41 : speeds ⟨2, by omega⟩ < 4 * speeds ⟨0, by omega⟩)
    (c₃ c₁ g : ℕ) (hgpos : 0 < g)
    (hd : g * 4 = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hm3 : c₃ % 4 = 2) (hm1 : c₁ % 4 = 1 ∨ c₁ % 4 = 3) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  -- Real-valued speed facts.
  have hv1pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv12R : (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (0:ℕ) < 1))
  have hv23R : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2))
  have hv34R : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (2:ℕ) < 3))
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  have h41R : (speeds ⟨2, by omega⟩ : ℝ) < 4 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast h41
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
  -- Step 1: choose the multiplier k with c₁k ≡ 1, c₃k ≡ 2 (mod 4).
  obtain ⟨k, hk1, hk3⟩ : ∃ k : ℕ, (c₁ * k) % 4 = 1 ∧ (c₃ * k) % 4 = 2 := by
    rcases hm1 with h | h
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨3, by omega, by omega⟩
  -- Step 2: the anchor time τ = k/(4g) and its fract data.
  have hv1cast : ((speeds ⟨0, by omega⟩ : ℕ) : ℝ) = (g : ℝ) * (c₁ : ℝ) := by
    exact_mod_cast hc1.symm
  have hv3cast : ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) = (g : ℝ) * (c₃ : ℝ) := by
    exact_mod_cast hc3.symm
  have hfrac1 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
      ((k : ℝ) / (4 * (g : ℝ)))) = 1/4 := by
    have hprod : (speeds ⟨0, by omega⟩ : ℝ) * ((k : ℝ) / (4 * (g : ℝ))) =
        ((c₁ * k : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by
      rw [hv1cast]
      push_cast
      field_simp
    rw [hprod, bhk_fract_nat_div (c₁ * k) 4 (by omega), hk1]
    norm_num
  have hfrac3 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
      ((k : ℝ) / (4 * (g : ℝ)))) = 1/2 := by
    have hprod : (speeds ⟨2, by omega⟩ : ℝ) * ((k : ℝ) / (4 * (g : ℝ))) =
        ((c₃ * k : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by
      rw [hv3cast]
      push_cast
      field_simp
    rw [hprod, bhk_fract_nat_div (c₃ * k) 4 (by omega), hk3]
    norm_num
  have hfrac2 : Int.fract ((speeds ⟨1, by omega⟩ : ℝ) *
      ((k : ℝ) / (4 * (g : ℝ)))) = 1/2 := by
    have hv2le : speeds ⟨1, by omega⟩ ≤ speeds ⟨2, by omega⟩ :=
      le_of_lt (hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2)))
    have hv2cast : ((speeds ⟨1, by omega⟩ : ℕ) : ℝ) =
        ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) - 4 * (g : ℝ) := by
      have hdR : (g : ℝ) * 4 = ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) -
          ((speeds ⟨1, by omega⟩ : ℕ) : ℝ) := by
        rw [← Nat.cast_sub hv2le]
        exact_mod_cast hd
      linarith
    have hprod : (speeds ⟨1, by omega⟩ : ℝ) * ((k : ℝ) / (4 * (g : ℝ))) =
        (speeds ⟨2, by omega⟩ : ℝ) * ((k : ℝ) / (4 * (g : ℝ))) - ((k : ℕ) : ℝ) := by
      rw [hv2cast]
      field_simp
    rw [hprod, Int.fract_sub_natCast]
    exact hfrac3
  -- Step 3: the 123-window `[τ − 1/(12v₁), τ + 1/(3v₃)]`, lonely at a named instant.
  have hv5pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  exact bhk_s7_named speeds hmono hpos h41
    ((k : ℝ) / (4 * (g : ℝ)) - 1/(12 * (speeds ⟨0, by omega⟩ : ℝ)))
    ((k : ℝ) / (4 * (g : ℝ)) + 1/(3 * (speeds ⟨2, by omega⟩ : ℝ)))
    (by
      -- 7/(12 v₃) = 1/(4 v₃) + 1/(3 v₃) < 1/(12 v₁) + 1/(3 v₃) = B − A.
      have h14 : 1/(4 * (speeds ⟨2, by omega⟩ : ℝ)) <
          1/(12 * (speeds ⟨0, by omega⟩ : ℝ)) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hsplit : (7:ℝ)/(12 * (speeds ⟨2, by omega⟩ : ℝ)) =
          1/(4 * (speeds ⟨2, by omega⟩ : ℝ)) +
          1/(3 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
      linarith [hsplit])
    (by
      -- the tail is 1/(12 v₁) ≥ 1/(3 v₅) since 4 v₁ < v₅
      intro hv15
      have he : (k : ℝ) / (4 * (g : ℝ)) + 1/(3 * (speeds ⟨2, by omega⟩ : ℝ)) -
          ((k : ℝ) / (4 * (g : ℝ)) - 1/(12 * (speeds ⟨0, by omega⟩ : ℝ))) -
          1/(3 * (speeds ⟨2, by omega⟩ : ℝ)) =
          1/(12 * (speeds ⟨0, by omega⟩ : ℝ)) := by ring
      rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith)
    (fun s hs => bhk_g4_123_gap speeds hmono hpos hsmall h41
      ((k : ℝ) / (4 * (g : ℝ))) hfrac1 hfrac2 hfrac3 s hs)

/-- **Axis pairs are impossible.** If some group element has a unit residue
    in one coordinate and zero in the other (`(0, ±1)` or `(1, 0)` scaled by
    `1/n`), then `k₀` is invertible mod `n`, so the zero coordinate forces
    `n ∣ c₃` (resp. `n ∣ c₁`) — contradicting the axis hypotheses. -/
lemma bhk_s7_exc_axis (n c₃ c₁ k₀ : ℕ) (hn : 1 < n)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁)
    (hcase : (c₃ * k₀ % n = 0 ∧ (c₁ * k₀ % n = 1 ∨ c₁ * k₀ % n = n - 1)) ∨
             (c₁ * k₀ % n = 0 ∧ c₃ * k₀ % n = 1)) : False := by
  have key : ∀ a b : ℕ, a * k₀ % n = 0 →
      (b * k₀ % n = 1 ∨ b * k₀ % n = n - 1) → ¬ n ∣ a → False := by
    intro a b h0 hu hane
    -- k₀ is coprime to n because b·k₀ is a unit residue.
    have hk_cop : Nat.gcd k₀ n = 1 := by
      have h₁ : Nat.gcd k₀ n ∣ k₀ := Nat.gcd_dvd_left _ _
      have h₂ : Nat.gcd k₀ n ∣ n := Nat.gcd_dvd_right _ _
      have h₃ : Nat.gcd k₀ n ∣ b * k₀ := Dvd.dvd.mul_left h₁ b
      have hdm := Nat.div_add_mod (b * k₀) n
      have hdvd1 : Nat.gcd k₀ n ∣ 1 := by
        rcases hu with h | h
        · rw [h] at hdm
          have h₄ : Nat.gcd k₀ n ∣ n * (b * k₀ / n) := Dvd.dvd.mul_right h₂ _
          have h₅ := Nat.dvd_sub h₃ h₄
          rwa [show b * k₀ - n * (b * k₀ / n) = 1 from by omega] at h₅
        · rw [h] at hdm
          have h₄ : Nat.gcd k₀ n ∣ n * (b * k₀ / n) + n :=
            dvd_add (Dvd.dvd.mul_right h₂ _) h₂
          have h₅ := Nat.dvd_sub h₄ h₃
          rwa [show n * (b * k₀ / n) + n - b * k₀ = 1 from by omega] at h₅
      exact Nat.dvd_one.mp hdvd1
    have hna : n ∣ a * k₀ := Nat.dvd_of_mod_eq_zero h0
    exact hane ((Nat.coprime_comm.mp hk_cop).dvd_of_dvd_mul_right hna)
  rcases hcase with ⟨h0, hu⟩ | ⟨h0, hu⟩
  · exact key c₃ c₁ h0 hu hc3_ne
  · exact key c₁ c₃ h0 (Or.inl hu) hc1_ne

/-- **Diagonal pairs `(1, ±1)`, `(2, ±2)`.** A single multiple of the group
    element lands in the speed-independent sufficient window: `m = ⌈n/6⌉`
    for `(1,1)`, `⌈n/3⌉` for `(1,-1)`, `⌈n/12⌉` for `(2,2)`, `⌈n/6⌉` for
    `(2,-2)`. All four window checks are `omega`-decidable. -/
lemma bhk_s7_exc_diag (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ : ℕ) (hn7 : 7 ≤ n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hab : (c₃ * k₀ % n = 1 ∧ (c₁ * k₀ % n = 1 ∨ c₁ * k₀ % n = n - 1)) ∨
           (c₃ * k₀ % n = 2 ∧ (c₁ * k₀ % n = 2 ∨ c₁ * k₀ % n = n - 2))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have Wn := bhk_s7_witness_num speeds hmono hpos hsmall
  rcases hab with ⟨ha, hb | hb⟩ | ⟨ha, hb | hb⟩
  · -- (1, 1): m = ⌈n/6⌉.
    set m : ℕ := (n + 5) / 6 with hm_def
    have hmlt : m < n := by omega
    have hmod3 : c₃ * (m * k₀) % n = m := by
      rw [bhk_s7_mul_mod, ha, one_mul, Nat.mod_eq_of_lt hmlt]
    have hmod1 : c₁ * (m * k₀) % n = m := by
      rw [bhk_s7_mul_mod, hb, one_mul, Nat.mod_eq_of_lt hmlt]
    exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
      (by rw [hmod3]; omega) (by rw [hmod3]; omega)
      (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- (1, -1): m = ⌈n/3⌉.
    set m : ℕ := (n + 2) / 3 with hm_def
    have hmlt : m < n := by omega
    have hmod3 : c₃ * (m * k₀) % n = m := by
      rw [bhk_s7_mul_mod, ha, one_mul, Nat.mod_eq_of_lt hmlt]
    have hmod1 : c₁ * (m * k₀) % n = n - m := by
      rw [bhk_s7_mul_mod, hb,
          bhk_s7_neg_mod n 1 m (by omega) (by omega) (by omega : 1 * m < n),
          one_mul]
    exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
      (by rw [hmod3]; omega) (by rw [hmod3]; omega)
      (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- (2, 2): m = ⌈n/12⌉.
    set m : ℕ := (n + 11) / 12 with hm_def
    have hmlt : 2 * m < n := by omega
    have hmod3 : c₃ * (m * k₀) % n = 2 * m := by
      rw [bhk_s7_mul_mod, ha, Nat.mod_eq_of_lt hmlt]
    have hmod1 : c₁ * (m * k₀) % n = 2 * m := by
      rw [bhk_s7_mul_mod, hb, Nat.mod_eq_of_lt hmlt]
    exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
      (by rw [hmod3]; omega) (by rw [hmod3]; omega)
      (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- (2, -2): m = ⌈n/6⌉.
    set m : ℕ := (n + 5) / 6 with hm_def
    have hmlt : 2 * m < n := by omega
    have hmod3 : c₃ * (m * k₀) % n = 2 * m := by
      rw [bhk_s7_mul_mod, ha, Nat.mod_eq_of_lt hmlt]
    have hmod1 : c₁ * (m * k₀) % n = n - 2 * m := by
      rw [bhk_s7_mul_mod, hb,
          bhk_s7_neg_mod n 2 m (by omega) (by omega) hmlt]
    exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
      (by rw [hmod3]; omega) (by rw [hmod3]; omega)
      (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)

/-- **Axis-pair witness (BHK §2, pairs `(2,0)`, `(3,0)`, `(4,0)`).**
    If a group multiple `k₀` has residues `(iv, 0)` with `iv ∈ {2,3,4}`, a
    witness in the sufficient window always exists, for every `n ≥ 7`:

    * Bezout reaches a second coordinate `w` that is a multiple of
      `g' := gcd(n, c₁) < n` lying deep in the window — `w = g'` when
      `n ∈ {2g', 3g'}`, otherwise the first multiple of `g'` past
      `(n + 3(⌈n/6⌉+3))/9` (possible since `9g' ≤ 9n/4 < 4n`).
    * Adding `m·k₀` steps the first coordinate by `iv` without moving the
      second; the congruence `iv·m ≡ Δ (mod n)` is solved explicitly
      (`bhk_s7_solve2/3/4`), steering `u` into `[⌈n/6⌉, ⌈n/6⌉+3]`. -/
lemma bhk_s7_exc_axis_hit (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ iv : ℕ) (hn7 : 7 ≤ n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc1_ne : ¬ n ∣ c₁)
    (hiv : iv = 2 ∨ iv = 3 ∨ iv = 4)
    (ha : c₃ * k₀ % n = iv) (hb : c₁ * k₀ % n = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hnpos : 0 < n := by omega
  have Wn := bhk_s7_witness_num speeds hmono hpos hsmall
  set c : ℕ := (n + 5) / 6 with hc_def
  -- Stage 1: a reachable deep second coordinate.
  obtain ⟨l, w, hw_res, hw_lt, hWlo, hWhi⟩ :
      ∃ l w, c₁ * l % n = w ∧ w < n ∧ n + 3 * (c + 3) ≤ 9 * w ∧
        9 * w ≤ 5 * n + 3 * c := by
    have hg'_dvd : Nat.gcd n c₁ ∣ n := Nat.gcd_dvd_left _ _
    have hg'_pos : 0 < Nat.gcd n c₁ := Nat.gcd_pos_of_pos_left _ hnpos
    have hg'_lt : Nat.gcd n c₁ < n := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd hnpos hg'_dvd) with h | h
      · exact h
      · exact absurd (h ▸ Nat.gcd_dvd_right n c₁) hc1_ne
    obtain ⟨t₁, ht₁⟩ := bhk_s7_bezout_mod n c₁ hnpos
    have ht₁' : c₁ * t₁ % n = Nat.gcd n c₁ := by
      rw [ht₁, Nat.mod_eq_of_lt hg'_lt]
    set g' := Nat.gcd n c₁ with hg'_def
    obtain ⟨d, hdn⟩ := hg'_dvd
    have hd2 : 2 ≤ d := by
      rcases d with _ | _ | d
      · simp at hdn; omega
      · simp at hdn; omega
      · omega
    rcases (by omega : d = 2 ∨ d = 3 ∨ 4 ≤ d) with rfl | rfl | hd4
    · exact ⟨t₁, g', ht₁', hg'_lt, by omega, by omega⟩
    · exact ⟨t₁, g', ht₁', hg'_lt, by omega, by omega⟩
    · have h4 : 4 * g' ≤ n := by
        calc 4 * g' ≤ d * g' := Nat.mul_le_mul_right _ hd4
          _ = n := by rw [hdn, Nat.mul_comm]
      set M := n + 3 * (c + 3) with hM_def
      set q₀ := M / (9 * g') with hq₀_def
      obtain ⟨P, hP1, hP2, hP9⟩ :
          ∃ P, P ≤ M ∧ M < P + 9 * g' ∧ 9 * (g' * (q₀ + 1)) = P + 9 * g' := by
        refine ⟨9 * g' * q₀, ?_, ?_, by ring⟩
        · calc 9 * g' * q₀ ≤ 9 * g' * q₀ + M % (9 * g') := Nat.le_add_right _ _
            _ = M := Nat.div_add_mod M (9 * g')
        · conv_lhs => rw [← Nat.div_add_mod M (9 * g')]
          exact Nat.add_lt_add_left (Nat.mod_lt _ (by omega)) _
      have hWlt : g' * (q₀ + 1) < n := by omega
      refine ⟨(q₀ + 1) * t₁, g' * (q₀ + 1), ?_, hWlt, by omega, by omega⟩
      rw [bhk_s7_mul_mod, ht₁', Nat.mod_eq_of_lt hWlt]
  -- Stage 2: steer the first coordinate into `[c, c+3]` by multiples of k₀.
  set u₀ := c₃ * l % n with hu₀_def
  have hu₀_lt : u₀ < n := Nat.mod_lt _ hnpos
  have step : ∀ m Δ u : ℕ, iv * m % n = Δ → (u₀ + Δ) % n = u →
      c₃ * (l + m * k₀) % n = u ∧ c₁ * (l + m * k₀) % n = w := by
    intro m Δ u hm hsum
    constructor
    · rw [show c₃ * (l + m * k₀) = c₃ * l + c₃ * (m * k₀) from by ring,
          Nat.add_mod, bhk_s7_mul_mod, ha, hm, ← hu₀_def, hsum]
    · rw [show c₁ * (l + m * k₀) = c₁ * l + c₁ * (m * k₀) from by ring,
          Nat.add_mod, bhk_s7_mul_mod, hb, Nat.zero_mul, Nat.zero_mod,
          hw_res, Nat.add_zero, Nat.mod_eq_of_lt hw_lt]
  obtain ⟨k, u, hk3, hk1, hu_lo, hu_hi⟩ :
      ∃ k u, c₃ * k % n = u ∧ c₁ * k % n = w ∧ c ≤ u ∧ u ≤ c + 3 := by
    rcases hiv with rfl | rfl | rfl
    · -- iv = 2
      set u := c + (u₀ + 2 * n - c) % 2 with hu_def
      have hu_lt : u < n := by omega
      rcases (Nat.lt_or_ge u u₀).symm with hle | hlt
      · obtain ⟨m, hm⟩ := bhk_s7_solve2 n (u - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u - u₀) u hm
          (by rw [show u₀ + (u - u₀) = u from by omega,
                  Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
      · obtain ⟨m, hm⟩ := bhk_s7_solve2 n (u + n - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u + n - u₀) u hm
          (by rw [show u₀ + (u + n - u₀) = u + n from by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
    · -- iv = 3
      set u := c + (u₀ + 3 * n - c) % 3 with hu_def
      have hu_lt : u < n := by omega
      rcases (Nat.lt_or_ge u u₀).symm with hle | hlt
      · obtain ⟨m, hm⟩ := bhk_s7_solve3 n (u - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u - u₀) u hm
          (by rw [show u₀ + (u - u₀) = u from by omega,
                  Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
      · obtain ⟨m, hm⟩ := bhk_s7_solve3 n (u + n - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u + n - u₀) u hm
          (by rw [show u₀ + (u + n - u₀) = u + n from by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
    · -- iv = 4
      set u := c + (u₀ + 4 * n - c) % 4 with hu_def
      have hu_lt : u < n := by omega
      rcases (Nat.lt_or_ge u u₀).symm with hle | hlt
      · obtain ⟨m, hm⟩ := bhk_s7_solve4 n (u - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u - u₀) u hm
          (by rw [show u₀ + (u - u₀) = u from by omega,
                  Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
      · obtain ⟨m, hm⟩ := bhk_s7_solve4 n (u + n - u₀) (by omega) (by omega)
        obtain ⟨h1, h2⟩ := step m (u + n - u₀) u hm
          (by rw [show u₀ + (u + n - u₀) = u + n from by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt hu_lt])
        exact ⟨_, u, h1, h2, by omega, by omega⟩
  exact Wn n c₃ c₁ g k hnpos hgpos hd hc3 hc1
    (by rw [hk3]; omega) (by rw [hk3]; omega)
    (by rw [hk3, hk1]; omega) (by rw [hk3, hk1]; omega)

/-- **Pair `(2, 0)` (BHK §2 case 2.1).** Closed by the axis-pair witness
    `bhk_s7_exc_axis_hit` — no minimality needed. -/
lemma bhk_s7_exc_20 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ : ℕ) (hn7 : 7 ≤ n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁)
    (ha : c₃ * k₀ % n = 2) (hb : c₁ * k₀ % n = 0)
    (ij : ℤ × ℤ) (hij1 : ij.1 = 2) (hij2 : ij.2 = 0)
    (hij_min : ∀ kl : ℤ × ℤ, kl ≠ (0, 0) → |kl.1| ≤ |ij.1| → |kl.2| ≤ |ij.2| →
      ¬(|kl.1| = |ij.1| ∧ |kl.2| = |ij.2|) →
      ¬ OnOrbit n c₃ c₁ kl.1 kl.2) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  bhk_s7_exc_axis_hit speeds hmono hpos hsmall n c₃ c₁ g k₀ 2 hn7 hgpos
    hd hc3 hc1 hc1_ne (Or.inl rfl) ha hb

/-- **Direct pair witness.** If the `k₀`-residues are `(A, B)` and an
    explicit multiple `m` puts `(A·m mod n, B·m mod n)` in the sufficient
    window, then `m·k₀` is a witness. For literal `n` the window checks
    are decidable. -/
lemma bhk_s7_pair_witness (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ A B m : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hA : c₃ * k₀ % n = A) (hB : c₁ * k₀ % n = B)
    (w1 : n ≤ 6 * (A * m % n)) (w2 : 6 * (A * m % n) ≤ 5 * n)
    (w3 : n + 3 * (A * m % n) ≤ 9 * (B * m % n))
    (w4 : 9 * (B * m % n) ≤ 5 * n + 3 * (A * m % n)) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hmod3 : c₃ * (m * k₀) % n = A * m % n := by rw [bhk_s7_mul_mod, hA]
  have hmod1 : c₁ * (m * k₀) % n = B * m % n := by rw [bhk_s7_mul_mod, hB]
  exact bhk_s7_witness_num speeds hmono hpos hsmall n c₃ c₁ g (m * k₀) hnpos
    hgpos hd hc3 hc1 (by rw [hmod3]; exact w1) (by rw [hmod3]; exact w2)
    (by rw [hmod3, hmod1]; exact w3) (by rw [hmod3, hmod1]; exact w4)

/-- **Table 9 pairs `(3, j)`, `(4, j)`, `|j| ≤ 2` (BHK §2).** Dispatch on
    the second residue:

    * `j = 0` — axis-pair witness (`bhk_s7_exc_axis_hit`);
    * `j ≠ 0` — an explicit multiple `m·k₀` of the pair lands in the
      sufficient window, uniformly in `n` (per-column ceiling formulas:
      `⌈7n/18⌉` for `(3,±1)`, `⌈7n/24⌉` for `(4,1)`, `⌈n/3⌉` for `(4,-1)`,
      `⌈13n/18⌉` for `(3,2)`, `⌈4n/27⌉` for `(3,-2)`, `⌈n/6⌉` for `(4,2)`,
      `⌈2n/15⌉` for `(4,-2)`), except finitely many small `n` in the
      `(3,-2)`, `(4,±2)` columns: those close by per-`n` witnesses
      (`bhk_s7_pair_witness`), by residue enumeration at `n ∈ {8, 14}`
      (`decide`), or — at `n = 7` — by a (13)-minimality contradiction. -/
lemma bhk_s7_exc_table9 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ : ℕ) (hn7 : 7 ≤ n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁)
    (ij : ℤ × ℤ)
    (hi34 : ij.1 = 3 ∨ ij.1 = 4) (hj2 : |ij.2| ≤ 2)
    (hresA : ij.1 = ((c₃ * k₀ % n : ℕ) : ℤ))
    (hresB : ij.2 = ((c₁ * k₀ % n : ℕ) : ℤ) ∨
             ij.2 + (n : ℤ) = ((c₁ * k₀ % n : ℕ) : ℤ))
    (hij_min : ∀ kl : ℤ × ℤ, kl ≠ (0, 0) → |kl.1| ≤ |ij.1| → |kl.2| ≤ |ij.2| →
      ¬(|kl.1| = |ij.1| ∧ |kl.2| = |ij.2|) →
      ¬ OnOrbit n c₃ c₁ kl.1 kl.2) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hnpos : 0 < n := by omega
  have Wn := bhk_s7_witness_num speeds hmono hpos hsmall
  rw [abs_le] at hj2
  have hBlt : c₁ * k₀ % n < n := Nat.mod_lt _ hnpos
  have hA : c₃ * k₀ % n = 3 ∨ c₃ * k₀ % n = 4 := by
    rcases hi34 with h | h <;> omega
  have hB5 : c₁ * k₀ % n = 0 ∨ c₁ * k₀ % n = 1 ∨ c₁ * k₀ % n = 2 ∨
      c₁ * k₀ % n = n - 1 ∨ c₁ * k₀ % n = n - 2 := by
    rcases hresB with h | h <;> omega
  rcases hB5 with hB | hB | hB | hB | hB
  · -- `j = 0`: axis-pair witness.
    rcases hA with hA | hA
    · exact bhk_s7_exc_axis_hit speeds hmono hpos hsmall n c₃ c₁ g k₀ 3 hn7
        hgpos hd hc3 hc1 hc1_ne (Or.inr (Or.inl rfl)) hA hB
    · exact bhk_s7_exc_axis_hit speeds hmono hpos hsmall n c₃ c₁ g k₀ 4 hn7
        hgpos hd hc3 hc1 hc1_ne (Or.inr (Or.inr rfl)) hA hB
  · -- `j = 1`.
    rcases hA with hA | hA
    · -- `(3, 1)`: `m = ⌈7n/18⌉`, one wrap.
      set m : ℕ := (7 * n + 17) / 18 with hm_def
      have hmod3 : c₃ * (m * k₀) % n = 3 * m - n := by
        rw [bhk_s7_mul_mod, hA,
            bhk_s7_mod_window (3 * m) 1 n (by omega) (by omega), one_mul]
      have hmod1 : c₁ * (m * k₀) % n = m := by
        rw [bhk_s7_mul_mod, hB, one_mul, Nat.mod_eq_of_lt (by omega : m < n)]
      exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
    · -- `(4, 1)`: `m = ⌈7n/24⌉`, one wrap.
      set m : ℕ := (7 * n + 23) / 24 with hm_def
      have hmod3 : c₃ * (m * k₀) % n = 4 * m - n := by
        rw [bhk_s7_mul_mod, hA,
            bhk_s7_mod_window (4 * m) 1 n (by omega) (by omega), one_mul]
      have hmod1 : c₁ * (m * k₀) % n = m := by
        rw [bhk_s7_mul_mod, hB, one_mul, Nat.mod_eq_of_lt (by omega : m < n)]
      exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- `j = 2`.
    rcases hA with hA | hA
    · -- `(3, 2)`: `m = ⌈13n/18⌉`, two wraps / one wrap.
      set m : ℕ := (13 * n + 17) / 18 with hm_def
      have hmod3 : c₃ * (m * k₀) % n = 3 * m - 2 * n := by
        rw [bhk_s7_mul_mod, hA,
            bhk_s7_mod_window (3 * m) 2 n (by omega) (by omega)]
      have hmod1 : c₁ * (m * k₀) % n = 2 * m - n := by
        rw [bhk_s7_mul_mod, hB,
            bhk_s7_mod_window (2 * m) 1 n (by omega) (by omega), one_mul]
      exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
    · -- `(4, 2)`.
      rcases Nat.lt_or_ge n 24 with hn24 | hn24
      · -- `7 ≤ n ≤ 23`: finitely many cases.
        rcases (by omega : n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨
            n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨
            n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl
        · -- `n = 7`: (13)-minimality contradiction at `3k₀ ↦ (-2, -1)`.
          have h3 : c₃ * (3 * k₀) % 7 = 5 := by rw [bhk_s7_mul_mod, hA]
          have h1 : c₁ * (3 * k₀) % 7 = 6 := by rw [bhk_s7_mul_mod, hB]
          have hmem : OnOrbit 7 c₃ c₁ (-2) (-1) := onOrbit_of_res (k := 3 * k₀) (by norm_num)
            (by rw [h3]; norm_num) (by rw [h1]; norm_num)
          have hij1' : ij.1 = 4 := by omega
          have hij2' : ij.2 = 2 := by rcases hresB with h | h <;> omega
          refine absurd ?_ (hij_min (-2, -1) (by decide)
            (by rw [hij1']; decide) (by rw [hij2']; decide)
            (by rw [hij1', hij2']; decide))
          exact hmem
        · -- `n = 8`: residue enumeration.
          set_option synthInstance.maxSize 512 in
          have key : ∀ A' < 8, ∀ B' < 8, ∀ K < 8,
              (A' * K % 8 = 4 ∧ B' * K % 8 = 2 ∧
                Nat.gcd 8 (Nat.gcd A' B') = 1) →
              ∃ t, t < 8 ∧ 8 ≤ 6 * (A' * t % 8) ∧ 6 * (A' * t % 8) ≤ 40 ∧
                8 + 3 * (A' * t % 8) ≤ 9 * (B' * t % 8) ∧
                9 * (B' * t % 8) ≤ 40 + 3 * (A' * t % 8) := by decide
          obtain ⟨t, htlt, w1, w2, w3, w4⟩ :=
            key (c₃ % 8) (Nat.mod_lt _ (by norm_num)) (c₁ % 8)
              (Nat.mod_lt _ (by norm_num)) (k₀ % 8) (Nat.mod_lt _ (by norm_num))
              ⟨by rw [← Nat.mul_mod]; exact hA, by rw [← Nat.mul_mod]; exact hB,
               by rw [bhk_s7_gcd_mod]; exact hg1⟩
          have e3 : c₃ * t % 8 = c₃ % 8 * t % 8 := by
            rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
          have e1 : c₁ * t % 8 = c₁ % 8 * t % 8 := by
            rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
          exact Wn 8 c₃ c₁ g t (by norm_num) hgpos hd hc3 hc1
            (by rw [e3]; omega) (by rw [e3]; omega)
            (by rw [e3, e1]; omega) (by rw [e3, e1]; omega)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 9 c₃ c₁ g k₀ 4 2 3
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 10 c₃ c₁ g k₀ 4 2 2
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 11 c₃ c₁ g k₀ 4 2 2
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 12 c₃ c₁ g k₀ 4 2 2
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 13 c₃ c₁ g k₀ 4 2 4
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · -- `n = 14`: residue enumeration.
          set_option synthInstance.maxSize 512 in
          have key : ∀ A' < 14, ∀ B' < 14, ∀ K < 14,
              (A' * K % 14 = 4 ∧ B' * K % 14 = 2 ∧
                Nat.gcd 14 (Nat.gcd A' B') = 1) →
              ∃ t, t < 14 ∧ 14 ≤ 6 * (A' * t % 14) ∧ 6 * (A' * t % 14) ≤ 70 ∧
                14 + 3 * (A' * t % 14) ≤ 9 * (B' * t % 14) ∧
                9 * (B' * t % 14) ≤ 70 + 3 * (A' * t % 14) := by decide
          obtain ⟨t, htlt, w1, w2, w3, w4⟩ :=
            key (c₃ % 14) (Nat.mod_lt _ (by norm_num)) (c₁ % 14)
              (Nat.mod_lt _ (by norm_num)) (k₀ % 14)
              (Nat.mod_lt _ (by norm_num))
              ⟨by rw [← Nat.mul_mod]; exact hA, by rw [← Nat.mul_mod]; exact hB,
               by rw [bhk_s7_gcd_mod]; exact hg1⟩
          have e3 : c₃ * t % 14 = c₃ % 14 * t % 14 := by
            rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
          have e1 : c₁ * t % 14 = c₁ % 14 * t % 14 := by
            rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
          exact Wn 14 c₃ c₁ g t (by norm_num) hgpos hd hc3 hc1
            (by rw [e3]; omega) (by rw [e3]; omega)
            (by rw [e3, e1]; omega) (by rw [e3, e1]; omega)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 15 c₃ c₁ g k₀ 4 2 3
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 16 c₃ c₁ g k₀ 4 2 3
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 17 c₃ c₁ g k₀ 4 2 3
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 18 c₃ c₁ g k₀ 4 2 3
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 19 c₃ c₁ g k₀ 4 2 6
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 20 c₃ c₁ g k₀ 4 2 4
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 21 c₃ c₁ g k₀ 4 2 4
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 22 c₃ c₁ g k₀ 4 2 4
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
        · exact bhk_s7_pair_witness speeds hmono hpos hsmall 23 c₃ c₁ g k₀ 4 2 4
            (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)
      · -- `n ≥ 24`: `m = ⌈n/6⌉`, no wraps.
        set m : ℕ := (n + 5) / 6 with hm_def
        have hmod3 : c₃ * (m * k₀) % n = 4 * m := by
          rw [bhk_s7_mul_mod, hA, Nat.mod_eq_of_lt (by omega : 4 * m < n)]
        have hmod1 : c₁ * (m * k₀) % n = 2 * m := by
          rw [bhk_s7_mul_mod, hB, Nat.mod_eq_of_lt (by omega : 2 * m < n)]
        exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
          (by rw [hmod3]; omega) (by rw [hmod3]; omega)
          (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- `j = -1`.
    rcases hA with hA | hA
    · -- `(3, -1)`: `m = ⌈7n/18⌉`.
      set m : ℕ := (7 * n + 17) / 18 with hm_def
      have hmod3 : c₃ * (m * k₀) % n = 3 * m - n := by
        rw [bhk_s7_mul_mod, hA,
            bhk_s7_mod_window (3 * m) 1 n (by omega) (by omega), one_mul]
      have hmod1 : c₁ * (m * k₀) % n = n - m := by
        rw [bhk_s7_mul_mod, hB,
            bhk_s7_neg_mod n 1 m (by omega) (by omega) (by omega : 1 * m < n),
            one_mul]
      exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
    · -- `(4, -1)`: `m = ⌈n/3⌉`.
      set m : ℕ := (n + 2) / 3 with hm_def
      have hmod3 : c₃ * (m * k₀) % n = 4 * m - n := by
        rw [bhk_s7_mul_mod, hA,
            bhk_s7_mod_window (4 * m) 1 n (by omega) (by omega), one_mul]
      have hmod1 : c₁ * (m * k₀) % n = n - m := by
        rw [bhk_s7_mul_mod, hB,
            bhk_s7_neg_mod n 1 m (by omega) (by omega) (by omega : 1 * m < n),
            one_mul]
      exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- `j = -2`.
    rcases hA with hA | hA
    · -- `(3, -2)`.
      rcases (by omega : n = 7 ∨ 8 ≤ n) with rfl | hn8
      · -- `n = 7`: (13)-minimality contradiction at `3k₀ ↦ (2, 1)`.
        have h3 : c₃ * (3 * k₀) % 7 = 2 := by rw [bhk_s7_mul_mod, hA]
        have h1 : c₁ * (3 * k₀) % 7 = 1 := by rw [bhk_s7_mul_mod, hB]
        have hmem : OnOrbit 7 c₃ c₁ 2 1 := onOrbit_of_res (k := 3 * k₀) (by norm_num)
          (by rw [h3]; norm_num) (by rw [h1]; norm_num)
        have hij1' : ij.1 = 3 := by omega
        have hij2' : ij.2 = -2 := by rcases hresB with h | h <;> omega
        refine absurd ?_ (hij_min (2, 1) (by decide)
          (by rw [hij1']; decide) (by rw [hij2']; decide)
          (by rw [hij1', hij2']; decide))
        exact hmem
      · -- `n ≥ 8`: `m = ⌈4n/27⌉`, no wrap.
        set m : ℕ := (4 * n + 26) / 27 with hm_def
        have hmod3 : c₃ * (m * k₀) % n = 3 * m := by
          rw [bhk_s7_mul_mod, hA, Nat.mod_eq_of_lt (by omega : 3 * m < n)]
        have hmod1 : c₁ * (m * k₀) % n = n - 2 * m := by
          rw [bhk_s7_mul_mod, hB,
              bhk_s7_neg_mod n 2 m (by omega) (by omega) (by omega : 2 * m < n)]
        exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
          (by rw [hmod3]; omega) (by rw [hmod3]; omega)
          (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
    · -- `(4, -2)`.
      rcases (by omega : n = 8 ∨ n = 7 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
          13 ≤ n) with rfl | rfl | rfl | rfl | rfl | rfl | hn13
      · -- `n = 8`: residue enumeration.
        set_option synthInstance.maxSize 512 in
        have key : ∀ A' < 8, ∀ B' < 8, ∀ K < 8,
            (A' * K % 8 = 4 ∧ B' * K % 8 = 6 ∧
              Nat.gcd 8 (Nat.gcd A' B') = 1) →
            ∃ t, t < 8 ∧ 8 ≤ 6 * (A' * t % 8) ∧ 6 * (A' * t % 8) ≤ 40 ∧
              8 + 3 * (A' * t % 8) ≤ 9 * (B' * t % 8) ∧
              9 * (B' * t % 8) ≤ 40 + 3 * (A' * t % 8) := by decide
        obtain ⟨t, htlt, w1, w2, w3, w4⟩ :=
          key (c₃ % 8) (Nat.mod_lt _ (by norm_num)) (c₁ % 8)
            (Nat.mod_lt _ (by norm_num)) (k₀ % 8) (Nat.mod_lt _ (by norm_num))
            ⟨by rw [← Nat.mul_mod]; exact hA, by rw [← Nat.mul_mod]; exact hB,
             by rw [bhk_s7_gcd_mod]; exact hg1⟩
        have e3 : c₃ * t % 8 = c₃ % 8 * t % 8 := by
          rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
        have e1 : c₁ * t % 8 = c₁ % 8 * t % 8 := by
          rw [Nat.mul_mod, Nat.mod_eq_of_lt htlt]
        exact Wn 8 c₃ c₁ g t (by norm_num) hgpos hd hc3 hc1
          (by rw [e3]; omega) (by rw [e3]; omega)
          (by rw [e3, e1]; omega) (by rw [e3, e1]; omega)
      · exact bhk_s7_pair_witness speeds hmono hpos hsmall 7 c₃ c₁ g k₀ 4 5 1
          (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact bhk_s7_pair_witness speeds hmono hpos hsmall 9 c₃ c₁ g k₀ 4 7 3
          (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact bhk_s7_pair_witness speeds hmono hpos hsmall 10 c₃ c₁ g k₀ 4 8 2
          (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact bhk_s7_pair_witness speeds hmono hpos hsmall 11 c₃ c₁ g k₀ 4 9 2
          (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact bhk_s7_pair_witness speeds hmono hpos hsmall 12 c₃ c₁ g k₀ 4 10 2
          (by norm_num) hgpos hd hc3 hc1 hA hB (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · -- `n ≥ 13`: `m = ⌈2n/15⌉`, no wrap.
        set m : ℕ := (2 * n + 14) / 15 with hm_def
        have hmod3 : c₃ * (m * k₀) % n = 4 * m := by
          rw [bhk_s7_mul_mod, hA, Nat.mod_eq_of_lt (by omega : 4 * m < n)]
        have hmod1 : c₁ * (m * k₀) % n = n - 2 * m := by
          rw [bhk_s7_mul_mod, hB,
              bhk_s7_neg_mod n 2 m (by omega) (by omega) (by omega : 2 * m < n)]
        exact Wn n c₃ c₁ g (m * k₀) hnpos hgpos hd hc3 hc1
          (by rw [hmod3]; omega) (by rw [hmod3]; omega)
          (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)

/-- **The `G₇` 123-gap.** If at time `τ` the fractional positions are
    `{v₁τ} = 2/7`, `{v₂τ} = {v₃τ} = 4/7`, then on the whole interval
    `[τ - 5/(14 v₃), τ + 11/(42 v₃)]` runners 1, 2, 3 stay safe
    (BHK: `J = [kt₀ - 5/14, kt₀ + 11/42]` is a 123-gap; uses `x₁ ≥ 3`,
    i.e. `3 v₁ < v₃`, for runner 1's left edge). -/
lemma bhk_g7_123_gap (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (τ : ℝ)
    (hf1 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) * τ) = 2/7)
    (hf2 : Int.fract ((speeds ⟨1, by omega⟩ : ℝ) * τ) = 4/7)
    (hf3 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) * τ) = 4/7)
    (t : ℝ)
    (ht : t ∈ Set.Icc (τ - 5/(14 * (speeds ⟨2, by omega⟩ : ℝ)))
                      (τ + 11/(42 * (speeds ⟨2, by omega⟩ : ℝ)))) :
    t ∉ unsafeOf speeds ⟨0, by omega⟩ ∧ t ∉ unsafeOf speeds ⟨1, by omega⟩ ∧
    t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
  have hv1pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv12 : (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (0:ℕ) < 1))
  have hv23 : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2))
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  obtain ⟨ht_lo, ht_hi⟩ := ht
  have key : ∀ j : Fin 5, ∀ f : ℝ, Int.fract ((speeds j : ℝ) * τ) = f →
      1/6 ≤ f - 5 * (speeds j : ℝ) / (14 * (speeds ⟨2, by omega⟩ : ℝ)) →
      f + 11 * (speeds j : ℝ) / (42 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 5/6 →
      t ∉ unsafeOf speeds j := by
    intro j f hf hlo hhi
    have hvjpos : (0 : ℝ) < (speeds j : ℝ) := by exact_mod_cast hpos _
    have hfloor : ((⌊(speeds j : ℝ) * τ⌋ : ℝ)) + f = (speeds j : ℝ) * τ := by
      rw [← hf]; exact Int.floor_add_fract _
    apply not_mem_unsafeOf_of_in_gap speeds j (hpos _) ⌊(speeds j : ℝ) * τ⌋ t
    · rw [div_le_iff₀ hvjpos]
      have h1 : (speeds j : ℝ) * t ≥ (speeds j : ℝ) * τ -
          5 * (speeds j : ℝ) / (14 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        have := mul_le_mul_of_nonneg_left ht_lo (le_of_lt hvjpos)
        have hxx : (speeds j : ℝ) * (τ - 5/(14 * (speeds ⟨2, by omega⟩ : ℝ))) =
            (speeds j : ℝ) * τ -
            5 * (speeds j : ℝ) / (14 * (speeds ⟨2, by omega⟩ : ℝ)) := by
          ring
        linarith [hxx ▸ this]
      nlinarith [h1, hfloor, hlo]
    · rw [le_div_iff₀ hvjpos]
      have h2 : (speeds j : ℝ) * t ≤ (speeds j : ℝ) * τ +
          11 * (speeds j : ℝ) / (42 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        have := mul_le_mul_of_nonneg_left ht_hi (le_of_lt hvjpos)
        have hxx : (speeds j : ℝ) * (τ + 11/(42 * (speeds ⟨2, by omega⟩ : ℝ))) =
            (speeds j : ℝ) * τ +
            11 * (speeds j : ℝ) / (42 * (speeds ⟨2, by omega⟩ : ℝ)) := by
          ring
        linarith [hxx ▸ this]
      nlinarith [h2, hfloor, hhi]
  refine ⟨key _ (2/7) hf1 ?_ ?_, key _ (4/7) hf2 ?_ ?_, key _ (4/7) hf3 ?_ ?_⟩
  · -- 1/6 ≤ 2/7 - 5 v₁/(14 v₃): 5 v₁/(14 v₃) ≤ 5/42 since 3 v₁ < v₃.
    have hX : 5 * (speeds ⟨0, by omega⟩ : ℝ) /
        (14 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 5/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 2/7 + 11 v₁/(42 v₃) ≤ 5/6: 11 v₁/(42 v₃) ≤ 23/42 since v₁ < v₃.
    have hX : 11 * (speeds ⟨0, by omega⟩ : ℝ) /
        (42 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 23/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/6 ≤ 4/7 - 5 v₂/(14 v₃): 5 v₂/(14 v₃) ≤ 17/42 since v₂ < v₃.
    have hX : 5 * (speeds ⟨1, by omega⟩ : ℝ) /
        (14 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 17/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 4/7 + 11 v₂/(42 v₃) ≤ 5/6: 11 v₂/(42 v₃) ≤ 11/42 since v₂ ≤ v₃.
    have hX : 11 * (speeds ⟨1, by omega⟩ : ℝ) /
        (42 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 11/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 1/6 ≤ 4/7 - 5 v₃/(14 v₃) = 4/7 - 5/14.
    have hX : 5 * (speeds ⟨2, by omega⟩ : ℝ) /
        (14 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 17/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · -- 4/7 + 11 v₃/(42 v₃) = 4/7 + 11/42 = 5/6.
    have hX : 11 * (speeds ⟨2, by omega⟩ : ℝ) /
        (42 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 11/42 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

/-- **BHK exceptional group `G₇` (named instants).** `n = 7`, pair `(2, 1)`,
    `v₃ < 4 v₁`: the group `⟨(2/7, 1/7)⟩ = ⟨(4/7, 2/7)⟩` misses the open
    parallelogram `P`. BHK p. 45: with `k = 2k₀` the positions at
    `τ = k/(7g)` are `(2/7, 4/7, 4/7)`; `[τ - 5/(14v₃), τ + 11/(42v₃)]`
    is a 123-gap of length `13/(21v₃) > 7/(12v₃)`, and `bhk_s7_named` names
    the lonely instant on it (the tail condition from `v₅ > 5v₁ > (5/4)v₃`). -/
lemma bhk_s7_g7_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (h41 : speeds ⟨2, by omega⟩ < 4 * speeds ⟨0, by omega⟩)
    (c₃ c₁ g k₀ : ℕ) (hgpos : 0 < g)
    (hd : g * 7 = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (ha : c₃ * k₀ % 7 = 2) (hb : c₁ * k₀ % 7 = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  -- Real-valued speed facts.
  have hv1pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv12R : (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (0:ℕ) < 1))
  have hv23R : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2))
  have hv34R : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega : (2:ℕ) < 3))
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  have h41R : (speeds ⟨2, by omega⟩ : ℝ) < 4 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast h41
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
  -- The anchor multiple k = 2k₀ and its residues mod 7.
  have hm3 : c₃ * (2 * k₀) % 7 = 4 := by
    rw [bhk_s7_mul_mod, ha]
  have hm1 : c₁ * (2 * k₀) % 7 = 2 := by
    rw [bhk_s7_mul_mod, hb]
  -- Fract data at τ = 2k₀/(7g).
  have hv1cast : ((speeds ⟨0, by omega⟩ : ℕ) : ℝ) = (g : ℝ) * (c₁ : ℝ) := by
    exact_mod_cast hc1.symm
  have hv3cast : ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) = (g : ℝ) * (c₃ : ℝ) := by
    exact_mod_cast hc3.symm
  have hfrac1 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
      (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)))) = 2/7 := by
    have hprod : (speeds ⟨0, by omega⟩ : ℝ) *
        (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ))) =
        ((c₁ * (2 * k₀) : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by
      rw [hv1cast]
      push_cast
      field_simp
    rw [hprod, bhk_fract_nat_div (c₁ * (2 * k₀)) 7 (by omega), hm1]
    norm_num
  have hfrac3 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
      (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)))) = 4/7 := by
    have hprod : (speeds ⟨2, by omega⟩ : ℝ) *
        (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ))) =
        ((c₃ * (2 * k₀) : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by
      rw [hv3cast]
      push_cast
      field_simp
    rw [hprod, bhk_fract_nat_div (c₃ * (2 * k₀)) 7 (by omega), hm3]
    norm_num
  have hfrac2 : Int.fract ((speeds ⟨1, by omega⟩ : ℝ) *
      (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)))) = 4/7 := by
    have hv2le : speeds ⟨1, by omega⟩ ≤ speeds ⟨2, by omega⟩ :=
      le_of_lt (hmono (Fin.mk_lt_mk.mpr (by omega : (1:ℕ) < 2)))
    have hv2cast : ((speeds ⟨1, by omega⟩ : ℕ) : ℝ) =
        ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) - 7 * (g : ℝ) := by
      have hdR : (g : ℝ) * 7 = ((speeds ⟨2, by omega⟩ : ℕ) : ℝ) -
          ((speeds ⟨1, by omega⟩ : ℕ) : ℝ) := by
        rw [← Nat.cast_sub hv2le]
        exact_mod_cast hd
      linarith
    have hprod : (speeds ⟨1, by omega⟩ : ℝ) *
        (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ))) =
        (speeds ⟨2, by omega⟩ : ℝ) *
        (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ))) - ((2 * k₀ : ℕ) : ℝ) := by
      rw [hv2cast]
      field_simp
    rw [hprod, Int.fract_sub_natCast]
    exact hfrac3
  -- The 123-window `[τ − 5/(14v₃), τ + 11/(42v₃)]`, lonely at a named instant.
  have hv5pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  exact bhk_s7_named speeds hmono hpos h41
    (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) - 5/(14 * (speeds ⟨2, by omega⟩ : ℝ)))
    (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) + 11/(42 * (speeds ⟨2, by omega⟩ : ℝ)))
    (by
      -- B − A = 13/(21 v₃) > 7/(12 v₃) since 147 < 156.
      have he : ((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) +
          11/(42 * (speeds ⟨2, by omega⟩ : ℝ)) -
          (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) -
            5/(14 * (speeds ⟨2, by omega⟩ : ℝ))) =
          13/(21 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
      rw [he, div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith)
    (by
      -- the tail is 2/(7 v₃) ≥ 1/(3 v₅) since v₅ > 5 v₁ > (5/4) v₃
      intro hv15
      have he : ((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) +
          11/(42 * (speeds ⟨2, by omega⟩ : ℝ)) -
          (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ)) -
            5/(14 * (speeds ⟨2, by omega⟩ : ℝ))) -
          1/(3 * (speeds ⟨2, by omega⟩ : ℝ)) =
          2/(7 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
      rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith)
    (fun s hs => bhk_g7_123_gap speeds hmono hpos hsmall
      (((2 * k₀ : ℕ) : ℝ) / (7 * (g : ℝ))) hfrac1 hfrac2 hfrac3 s hs)

/-- **Pair `(2, ±1)` (BHK Table 10).** `(2, -1)` closes for every `n ≥ 7`
    with the witness multiple `m = ⌈4n/15⌉`; `(2, 1)` closes for `n ≥ 8`
    with `m = ⌈n/3⌉`. The residual `n = 7`, `(2, 1)` splits on the ratio:
    `4 v₁ ≤ v₃` admits the exact-window witness at `(4/7, 2/7)` (`k = 2k₀`),
    and `v₃ < 4 v₁` is the exceptional group `G₇` (`bhk_s7_g7_hard`). -/
lemma bhk_s7_exc_21 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g k₀ : ℕ) (hn7 : 7 ≤ n) (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁)
    (ha : c₃ * k₀ % n = 2) (hb : c₁ * k₀ % n = 1 ∨ c₁ * k₀ % n = n - 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have Wn := bhk_s7_witness_num speeds hmono hpos hsmall
  rcases hb with hb | hb
  · -- (2, 1).
    rcases Nat.lt_or_ge n 8 with hn8 | hn8
    · -- n = 7.
      have hn_eq : n = 7 := by omega
      subst hn_eq
      by_cases h41 : speeds ⟨2, by omega⟩ < 4 * speeds ⟨0, by omega⟩
      · exact bhk_s7_g7_hard speeds hmono hpos hsmall h41 c₃ c₁ g k₀ hgpos
          hd hc3 hc1 ha hb
      · -- 4 v₁ ≤ v₃: exact-ratio witness at (4/7, 2/7) with k = 2k₀.
        push_neg at h41
        have hV3Rpos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
          exact_mod_cast hpos _
        have hV1nn : (0 : ℝ) ≤ (speeds ⟨0, by omega⟩ : ℝ) := by positivity
        have h14R : 4 * (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨2, by omega⟩ : ℝ) := by
          exact_mod_cast h41
        have hm3 : c₃ * (2 * k₀) % 7 = 4 := by
          rw [bhk_s7_mul_mod, ha]
        have hm1 : c₁ * (2 * k₀) % 7 = 2 := by
          rw [bhk_s7_mul_mod, hb]
        apply bhk_s7_witness speeds hmono hpos 7 c₃ c₁ g (by norm_num) hgpos
          hd hc3 hc1 (2 * k₀)
        · rw [hm3]; norm_num
        · rw [hm3]; norm_num
        · rw [hm3, hm1]
          have h4c : ((4 : ℕ) : ℝ) = 4 := by norm_num
          have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
          rw [h4c, h2c]
          have hkey : ((4 : ℝ)/7 - 1/6) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 5/42 := by
            rw [div_le_iff₀ hV3Rpos]
            nlinarith
          linarith
        · rw [hm3, hm1]
          have h4c : ((4 : ℕ) : ℝ) = 4 := by norm_num
          have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
          rw [h4c, h2c]
          have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) <
              (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
          have hkey : ((5 : ℝ)/6 - 4/7) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 23/42 := by
            rw [div_le_iff₀ hV3Rpos]
            nlinarith
          linarith
    · -- n ≥ 8: m = ⌈n/3⌉.
      set m : ℕ := (n + 2) / 3 with hm_def
      have h2mlt : 2 * m < n := by omega
      have hmod3 : c₃ * (m * k₀) % n = 2 * m := by
        rw [bhk_s7_mul_mod, ha, Nat.mod_eq_of_lt h2mlt]
      have hmod1 : c₁ * (m * k₀) % n = m := by
        rw [bhk_s7_mul_mod, hb, one_mul, Nat.mod_eq_of_lt (by omega : m < n)]
      exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
        (by rw [hmod3]; omega) (by rw [hmod3]; omega)
        (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)
  · -- (2, -1): m = ⌈4n/15⌉ works for every n ≥ 7.
    set m : ℕ := (4 * n + 14) / 15 with hm_def
    have h2mlt : 2 * m < n := by omega
    have hmod3 : c₃ * (m * k₀) % n = 2 * m := by
      rw [bhk_s7_mul_mod, ha, Nat.mod_eq_of_lt h2mlt]
    have hmod1 : c₁ * (m * k₀) % n = n - m := by
      rw [bhk_s7_mul_mod, hb,
          bhk_s7_neg_mod n 1 m (by omega) (by omega) (by omega : 1 * m < n),
          one_mul]
    exact Wn n c₃ c₁ g (m * k₀) (by omega) hgpos hd hc3 hc1
      (by rw [hmod3]; omega) (by rw [hmod3]; omega)
      (by rw [hmod3, hmod1]; omega) (by rw [hmod3, hmod1]; omega)


/-- **The short-step orbits, dispatched (BHK §§2+7 exceptional pairs).**  When global isolation in
two dimensions (`orbit_isolation_two_bhk`) returns a minimal short step `(i, j)` on the meeting
orbit — `0 ≤ i ≤ 4`, `−(9 + 2i) < 6j < 9 + 2i` — read it as the residues of a multiple `k₀` and
dispatch:

* `(0, ±1)`, `(1, 0)` — impossible (`bhk_s7_exc_axis`);
* `(1, ±1)`, `(2, ±2)` — a multiple of `k₀` lands in the meeting-time window (`bhk_s7_exc_diag`);
* `(2, 0)` — `bhk_s7_exc_20`;  `(3, j)`, `(4, j)` — Table 9;  `(2, ±1)` — Table 10 and `G₇`. -/
lemma bhk_s7_exceptional (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g : ℕ) (hn : 1 < n) (hn7 : 7 ≤ n)
    (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁)
    (ij : ℤ × ℤ) (hij_ne : ij ≠ (0, 0))
    (hon : OnOrbit n c₃ c₁ ij.1 ij.2)
    (hi_lo : 0 ≤ ij.1) (hi4 : ij.1 ≤ 4)
    (hj_dn : -(9 + 2 * ij.1) < 6 * ij.2) (hj_up : 6 * ij.2 < 9 + 2 * ij.1)
    (hij_min : ∀ kl : ℤ × ℤ, kl ≠ (0, 0) → |kl.1| ≤ |ij.1| → |kl.2| ≤ |ij.2| →
      ¬(|kl.1| = |ij.1| ∧ |kl.2| = |ij.2|) → ¬ OnOrbit n c₃ c₁ kl.1 kl.2) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hnpos : 0 < n := by omega
  obtain ⟨k₀, -, hk1, hk2⟩ := hon
  have hne' : ¬(ij.1 = 0 ∧ ij.2 = 0) := by
    rintro ⟨h1, h2⟩
    exact hij_ne (Prod.ext h1 h2)
  have hi_eq : ij.1 = ((c₃ * k₀ % n : ℕ) : ℤ) := by
    rw [← hk1, Int.emod_eq_of_lt hi_lo (by omega)]
  rcases le_or_gt 0 ij.2 with hj0 | hj0
  · have hj_eq : ij.2 = ((c₁ * k₀ % n : ℕ) : ℤ) := by
      rw [← hk2, Int.emod_eq_of_lt hj0 (by omega)]
    -- Enumerate (a, b) = (c₃k₀ mod n, c₁k₀ mod n) ∈ {0..4} × {0..2}.
    rcases (by omega : c₃ * k₀ % n = 0 ∨ c₃ * k₀ % n = 1 ∨ c₃ * k₀ % n = 2 ∨
        c₃ * k₀ % n = 3 ∨ c₃ * k₀ % n = 4) with ha | ha | ha | ha | ha
    · -- (0, b): b = 1 forced; axis contradiction.
      exact absurd (Or.inl ⟨ha, Or.inl (by omega)⟩)
        (fun h => bhk_s7_exc_axis n c₃ c₁ k₀ hn hc3_ne hc1_ne h)
    · -- (1, b): b = 0 → axis; b = 1 → diagonal.
      rcases (by omega : c₁ * k₀ % n = 0 ∨ c₁ * k₀ % n = 1) with hb | hb
      · exact absurd (Or.inr ⟨hb, ha⟩)
          (fun h => bhk_s7_exc_axis n c₃ c₁ k₀ hn hc3_ne hc1_ne h)
      · exact bhk_s7_exc_diag speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 (Or.inl ⟨ha, Or.inl hb⟩)
    · -- (2, b): b = 0 → §2 case 2.1; b = 1 → Table 10; b = 2 → diagonal.
      rcases (by omega : c₁ * k₀ % n = 0 ∨ c₁ * k₀ % n = 1 ∨
          c₁ * k₀ % n = 2) with hb | hb | hb
      · exact bhk_s7_exc_20 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 hg1 hc3_ne hc1_ne ha hb ij (by omega) (by omega) hij_min
      · exact bhk_s7_exc_21 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 hg1 hc3_ne hc1_ne ha (Or.inl hb)
      · exact bhk_s7_exc_diag speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 (Or.inr ⟨ha, Or.inl hb⟩)
    · -- (3, j): Table 9.
      exact bhk_s7_exc_table9 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
        hd hc3 hc1 hg1 hc3_ne hc1_ne ij (Or.inl (by omega))
        (by rw [abs_le]; omega) hi_eq (Or.inl hj_eq) hij_min
    · -- (4, j): Table 9.
      exact bhk_s7_exc_table9 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
        hd hc3 hc1 hg1 hc3_ne hc1_ne ij (Or.inr (by omega))
        (by rw [abs_le]; omega) hi_eq (Or.inl hj_eq) hij_min
  · have hj_eq : ij.2 + n = ((c₁ * k₀ % n : ℕ) : ℤ) := by
      rw [← hk2]
      have h1 : ij.2 + n = (ij.2 + n) % n := (Int.emod_eq_of_lt (by omega) (by omega)).symm
      rw [h1, Int.add_emod_right]
    -- Enumerate: j ∈ {-1, -2} so b ∈ {n-1, n-2}, correlated with a.
    rcases (by omega : c₃ * k₀ % n = 0 ∨ c₃ * k₀ % n = 1 ∨ c₃ * k₀ % n = 2 ∨
        c₃ * k₀ % n = 3 ∨ c₃ * k₀ % n = 4) with ha | ha | ha | ha | ha
    · -- (0, -1): axis (j = -2 would need a ≥ 2).
      exact absurd (Or.inl ⟨ha, Or.inr (by omega)⟩)
        (fun h => bhk_s7_exc_axis n c₃ c₁ k₀ hn hc3_ne hc1_ne h)
    · -- (1, -1): diagonal.
      exact bhk_s7_exc_diag speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
        hd hc3 hc1 (Or.inl ⟨ha, Or.inr (by omega)⟩)
    · -- (2, -1) → Table 10; (2, -2) → diagonal.
      rcases (by omega : c₁ * k₀ % n = n - 1 ∨ c₁ * k₀ % n = n - 2) with hb | hb
      · exact bhk_s7_exc_21 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 hg1 hc3_ne hc1_ne ha (Or.inr hb)
      · exact bhk_s7_exc_diag speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
          hd hc3 hc1 (Or.inr ⟨ha, Or.inr hb⟩)
    · -- (3, j): Table 9.
      exact bhk_s7_exc_table9 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
        hd hc3 hc1 hg1 hc3_ne hc1_ne ij (Or.inl (by omega))
        (by rw [abs_le]; omega) hi_eq (Or.inr hj_eq) hij_min
    · -- (4, j): Table 9.
      exact bhk_s7_exc_table9 speeds hmono hpos hsmall n c₃ c₁ g k₀ hn7 hgpos
        hd hc3 hc1 hg1 hc3_ne hc1_ne ij (Or.inr (by omega))
        (by rw [abs_le]; omega) hi_eq (Or.inr hj_eq) hij_min


/-- **BHK §§2+7 small group order.** When `2 ≤ n ≤ 6` the rectangle
    `2/3 × 2/9` is too small for Corollary 6 (`αβ = 4/27 < 1/n`); handle
    by direct enumeration of the cyclic group `⟨(c₃/n, c₁/n)⟩` against the
    parallelogram `P` (both coordinates nonzero mod `n`).

    Empirically verified landscape (47 of 49 generator classes): a single
    multiple `k ≤ 3` lands in the speed-independent sufficient window
    `u ∈ [1/6, 5/6]`, `w ∈ [1/9 + u/3, 5/9 + u/3]`. The only exceptions
    are `n = 4` with generator class `±(2, 1)` — BHK's `G₄` — where the
    exact window works iff `4 v₁ ≤ v₃`, and the residual `v₃ < 4 v₁` goes
    to the ad hoc covering argument (`bhk_s7_g4_hard`). -/
lemma bhk_s7_small_n (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (n c₃ c₁ g : ℕ) (hn : 1 < n) (hn6 : n ≤ 6)
    (hgpos : 0 < g)
    (hd : g * n = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hc3 : g * c₃ = speeds ⟨2, by omega⟩)
    (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (hc3_ne : ¬ n ∣ c₃) (hc1_ne : ¬ n ∣ c₁) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have Wn := bhk_s7_witness_num speeds hmono hpos hsmall
  interval_cases n
  · -- n = 2: the only generator is (1, 1); k = 1.
    have h3 : c₃ % 2 = 1 := by omega
    have h1 : c₁ % 2 = 1 := by omega
    exact Wn 2 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
      (by omega) (by omega) (by omega) (by omega)
  · -- n = 3: every nonzero pair works with k = 1.
    have h3 : c₃ % 3 = 1 ∨ c₃ % 3 = 2 := by omega
    have h1 : c₁ % 3 = 1 ∨ c₁ % 3 = 2 := by omega
    rcases h3 with h3 | h3 <;> rcases h1 with h1 | h1 <;>
    exact Wn 3 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
      (by omega) (by omega) (by omega) (by omega)
  · -- n = 4: generator class ±(2, 1) is BHK's G₄; the rest have k ≤ 2.
    have h3 : c₃ % 4 = 1 ∨ c₃ % 4 = 2 ∨ c₃ % 4 = 3 := by omega
    have h1 : c₁ % 4 = 1 ∨ c₁ % 4 = 2 ∨ c₁ % 4 = 3 := by omega
    have hV3Rpos : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
    rcases h3 with h3 | h3 | h3
    · rcases h1 with h1 | h1 | h1
      · exact Wn 4 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 4 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 4 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · -- γ₃ = 2.
      rcases h1 with h1 | h1 | h1
      · -- (2, 1): exact window iff 4 v₁ ≤ v₃; else G₄.
        by_cases h14 : 4 * speeds ⟨0, by omega⟩ ≤ speeds ⟨2, by omega⟩
        · have h14R : 4 * (speeds ⟨0, by omega⟩ : ℝ) ≤ speeds ⟨2, by omega⟩ := by
            exact_mod_cast h14
          have hr : (speeds ⟨0, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/4 := by
            rw [div_le_iff₀ hV3Rpos]; linarith
          have hm3 : c₃ * 1 % 4 = 2 := by omega
          have hm1 : c₁ * 1 % 4 = 1 := by omega
          have hkey_lo : (((2:ℕ):ℝ)/4 - 1/6) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/12 := by
            rw [div_le_iff₀ hV3Rpos]
            have h2c : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [h2c]
            linarith [h14R]
          have hkey_hi : (5/6 - ((2:ℕ):ℝ)/4) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/12 := by
            rw [div_le_iff₀ hV3Rpos]
            have h2c : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [h2c]
            linarith [h14R]
          exact bhk_s7_witness speeds hmono hpos 4 c₃ c₁ g (by norm_num) hgpos
            hd hc3 hc1 1
            (by rw [hm3]; norm_num)
            (by rw [hm3]; norm_num)
            (by
              rw [hm3, hm1]
              have h1c : ((1:ℕ):ℝ) = 1 := by norm_num
              rw [h1c]
              linarith [hkey_lo])
            (by
              rw [hm3, hm1]
              have h1c : ((1:ℕ):ℝ) = 1 := by norm_num
              rw [h1c]
              linarith [hkey_hi])
        · push_neg at h14
          exact bhk_s7_g4_hard speeds hmono hpos hsmall h14 c₃ c₁ g hgpos
            hd hc3 hc1 h3 (Or.inl h1)
      · -- (2, 2): excluded by gcd(n, c₃, c₁) = 1.
        exfalso
        have h2c3 : 2 ∣ c₃ := by omega
        have h2c1 : 2 ∣ c₁ := by omega
        have hcontra : (2 : ℕ) ∣ 1 :=
          hg1 ▸ Nat.dvd_gcd (by norm_num) (Nat.dvd_gcd h2c3 h2c1)
        omega
      · -- (2, 3): mirror of (2, 1).
        by_cases h14 : 4 * speeds ⟨0, by omega⟩ ≤ speeds ⟨2, by omega⟩
        · have h14R : 4 * (speeds ⟨0, by omega⟩ : ℝ) ≤ speeds ⟨2, by omega⟩ := by
            exact_mod_cast h14
          have hr : (speeds ⟨0, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/4 := by
            rw [div_le_iff₀ hV3Rpos]; linarith
          have hm3 : c₃ * 1 % 4 = 2 := by omega
          have hm1 : c₁ * 1 % 4 = 3 := by omega
          have hkey_lo : (((2:ℕ):ℝ)/4 - 1/6) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/12 := by
            rw [div_le_iff₀ hV3Rpos]
            have h2c : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [h2c]
            linarith [h14R]
          have hkey_hi : (5/6 - ((2:ℕ):ℝ)/4) * (speeds ⟨0, by omega⟩ : ℝ) /
              (speeds ⟨2, by omega⟩ : ℝ) ≤ 1/12 := by
            rw [div_le_iff₀ hV3Rpos]
            have h2c : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [h2c]
            linarith [h14R]
          exact bhk_s7_witness speeds hmono hpos 4 c₃ c₁ g (by norm_num) hgpos
            hd hc3 hc1 1
            (by rw [hm3]; norm_num)
            (by rw [hm3]; norm_num)
            (by
              rw [hm3, hm1]
              have h3c : ((3:ℕ):ℝ) = 3 := by norm_num
              rw [h3c]
              linarith [hkey_lo])
            (by
              rw [hm3, hm1]
              have h3c : ((3:ℕ):ℝ) = 3 := by norm_num
              rw [h3c]
              linarith [hkey_hi])
        · push_neg at h14
          exact bhk_s7_g4_hard speeds hmono hpos hsmall h14 c₃ c₁ g hgpos
            hd hc3 hc1 h3 (Or.inr h1)
    · -- γ₃ = 3.
      rcases h1 with h1 | h1 | h1
      · exact Wn 4 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 4 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 4 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
  · -- n = 5: k ∈ {1, 2} suffices for all 16 generator pairs.
    have h3 : c₃ % 5 = 1 ∨ c₃ % 5 = 2 ∨ c₃ % 5 = 3 ∨ c₃ % 5 = 4 := by omega
    have h1 : c₁ % 5 = 1 ∨ c₁ % 5 = 2 ∨ c₁ % 5 = 3 ∨ c₁ % 5 = 4 := by omega
    rcases h3 with h3 | h3 | h3 | h3
    · rcases h1 with h1 | h1 | h1 | h1
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1
      · exact Wn 5 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 5 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
  · -- n = 6: k ∈ {1, 2, 3}; pairs with a common factor 2 or 3 are excluded.
    have h3 : c₃ % 6 = 1 ∨ c₃ % 6 = 2 ∨ c₃ % 6 = 3 ∨ c₃ % 6 = 4 ∨ c₃ % 6 = 5 := by
      omega
    have h1 : c₁ % 6 = 1 ∨ c₁ % 6 = 2 ∨ c₁ % 6 = 3 ∨ c₁ % 6 = 4 ∨ c₁ % 6 = 5 := by
      omega
    rcases h3 with h3 | h3 | h3 | h3 | h3
    · rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exfalso
        have hcontra : (2 : ℕ) ∣ 1 := hg1 ▸ Nat.dvd_gcd (by norm_num)
          (Nat.dvd_gcd (show 2 ∣ c₃ by omega) (show 2 ∣ c₁ by omega))
        omega
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exfalso
        have hcontra : (2 : ℕ) ∣ 1 := hg1 ▸ Nat.dvd_gcd (by norm_num)
          (Nat.dvd_gcd (show 2 ∣ c₃ by omega) (show 2 ∣ c₁ by omega))
        omega
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact Wn 6 c₃ c₁ g 3 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exfalso
        have hcontra : (3 : ℕ) ∣ 1 := hg1 ▸ Nat.dvd_gcd (by norm_num)
          (Nat.dvd_gcd (show 3 ∣ c₃ by omega) (show 3 ∣ c₁ by omega))
        omega
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 3 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exfalso
        have hcontra : (2 : ℕ) ∣ 1 := hg1 ▸ Nat.dvd_gcd (by norm_num)
          (Nat.dvd_gcd (show 2 ∣ c₃ by omega) (show 2 ∣ c₁ by omega))
        omega
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exfalso
        have hcontra : (2 : ℕ) ∣ 1 := hg1 ▸ Nat.dvd_gcd (by norm_num)
          (Nat.dvd_gcd (show 2 ∣ c₃ by omega) (show 2 ∣ c₁ by omega))
        omega
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
    · rcases h1 with h1 | h1 | h1 | h1 | h1
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 2 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)
      · exact Wn 6 c₃ c₁ g 1 (by norm_num) hgpos hd hc3 hc1
          (by omega) (by omega) (by omega) (by omega)

/-! ## Assembly -/


theorem bhk_s7_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V2 : ℕ := speeds ⟨1, by omega⟩ with hV2_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hV23 : V2 < V3 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV1pos : 0 < V1 := hpos _
  have hV3pos : 0 < V3 := hpos _
  set D : ℕ := V3 - V2 with hD_def
  have hDpos : 0 < D := by omega
  have hD_cast : ((D : ℕ) : ℝ) = (V3 : ℝ) - V2 := by
    rw [hD_def, Nat.cast_sub hV23.le]
  -- The axis hypotheses as divisibility statements.
  have hdvd3 : ¬ D ∣ V3 := by
    intro hdvd
    apply ht0
    rw [show (V3 : ℝ) * (1 / ((V3 : ℝ) - V2)) = (V3 : ℝ) / D from by
      rw [hD_cast]; ring]
    exact (bhk_fract_nat_div_eq_zero_iff V3 D hDpos).mpr hdvd
  have hdvd1 : ¬ D ∣ V1 := by
    intro hdvd
    apply hv1t0
    rw [show (V1 : ℝ) * (1 / ((V3 : ℝ) - V2)) = (V1 : ℝ) / D from by
      rw [hD_cast]; ring]
    exact (bhk_fract_nat_div_eq_zero_iff V1 D hDpos).mpr hdvd
  -- Reduced group data.
  set g : ℕ := Nat.gcd D (Nat.gcd V3 V1) with hg_def
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  have hgD : g ∣ D := Nat.gcd_dvd_left _ _
  have hgV3 : g ∣ V3 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left V3 V1)
  have hgV1 : g ∣ V1 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right V3 V1)
  set n : ℕ := D / g with hn_def
  set c₃ : ℕ := V3 / g with hc3_def
  set c₁ : ℕ := V1 / g with hc1_def
  have hgn : g * n = D := Nat.mul_div_cancel' hgD
  have hgc3 : g * c₃ = V3 := Nat.mul_div_cancel' hgV3
  have hgc1 : g * c₁ = V1 := Nat.mul_div_cancel' hgV1
  have hg1 : Nat.gcd n (Nat.gcd c₃ c₁) = 1 := by
    set e := Nat.gcd n (Nat.gcd c₃ c₁) with he_def
    have he_n : e ∣ n := Nat.gcd_dvd_left _ _
    have he_c3 : e ∣ c₃ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left c₃ c₁)
    have he_c1 : e ∣ c₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right c₃ c₁)
    have hge_D : g * e ∣ D := hgn ▸ mul_dvd_mul_left g he_n
    have hge_V3 : g * e ∣ V3 := hgc3 ▸ mul_dvd_mul_left g he_c3
    have hge_V1 : g * e ∣ V1 := hgc1 ▸ mul_dvd_mul_left g he_c1
    have hge_g : g * e ∣ g := by
      rw [hg_def]
      exact Nat.dvd_gcd hge_D (Nat.dvd_gcd hge_V3 hge_V1)
    have he1 : e ∣ 1 :=
      Nat.dvd_of_mul_dvd_mul_left hgpos (by rwa [mul_one g])
    exact Nat.dvd_one.mp he1
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0, mul_zero] at hgn; omega
    · exact h
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn_eq : n = 1 := by omega
      rw [hn_eq, mul_one] at hgn
      exact absurd (hgn ▸ hgV1) hdvd1
    · omega
  have hc3_ne : ¬ n ∣ c₃ := by
    rintro ⟨e, he⟩
    exact hdvd3 ⟨e, by rw [← hgc3, he, ← hgn]; ring⟩
  have hc1_ne : ¬ n ∣ c₁ := by
    rintro ⟨e, he⟩
    exact hdvd1 ⟨e, by rw [← hgc1, he, ← hgn]; ring⟩
  by_cases hn7 : 7 ≤ n
  · -- global isolation in two dimensions on the meeting orbit
    rcases orbit_isolation_two_bhk n c₃ c₁ hn7 hg1 with
      ⟨k, -, hu1, hu2, hw1, hw2⟩ | ⟨i, j, hij, hon, hi0, hi4, hjd, hju, -, -, hmin, -⟩
    · exact bhk_s7_witness_num speeds hmono hpos hsmall n c₃ c₁ g k hnpos hgpos hgn
        hgc3 hgc1 hu1 hu2 (by omega) (by omega)
    · exact bhk_s7_exceptional speeds hmono hpos hsmall n c₃ c₁ g hn1 hn7 hgpos hgn hgc3 hgc1
        hg1 hc3_ne hc1_ne (i, j) hij hon hi0 hi4 hjd hju
        (fun kl h1 h2 h3 h4 => hmin kl.1 kl.2 h1 h2 h3 h4)
  · exact bhk_s7_small_n speeds hmono hpos hsmall n c₃ c₁ g hn1 (by omega)
      hgpos hgn hgc3 hgc1 hg1 hc3_ne hc1_ne

/-- A lonely instant is never `0`, and `−t` is lonely with `t`: take it positive. -/
theorem exists_pos_of_lonely (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h : ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  obtain ⟨t, ht⟩ := h
  have hne : t ≠ 0 := by
    intro h0
    have := ht 0
    rw [h0, mul_zero, show circDist 0 = 0 by simp [circDist]] at this
    norm_num at this
  refine ⟨|t|, abs_pos.mpr hne, fun i => ?_⟩
  rcases abs_choice t with h | h
  · rw [h]; exact ht i
  · rw [h, mul_neg, circDist.symm_neg]; exact ht i

/-- **BHK §7 in the framework** (`3v₁ < v₃`, the meeting lattice of runners 2 and 3 off both
axes): five whole-number disparities are lonely at `1/6`, at an instant in the window around a
meeting time. -/
theorem lonely_7 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3)
    (hD3 : ¬ (v3 - v2) ∣ v3) (hD1 : ¬ (v3 - v2) ∣ v1) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  set speeds : Fin 5 → ℕ := ![v1, v2, v3, v4, v5] with hs
  have hmono : StrictMono speeds := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hs] <;> omega
  have hpos : ∀ i, 0 < speeds i := by intro i; fin_cases i <;> simp [hs] <;> omega
  have hD : 0 < v3 - v2 := by omega
  have hDR : ((v3 : ℝ) - v2) = ((v3 - v2 : ℕ) : ℝ) := by rw [Nat.cast_sub h23.le]
  have ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
      (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0 := by
    show Int.fract ((v3 : ℝ) * (1 / ((v3 : ℝ) - (v2 : ℝ)))) ≠ 0
    rw [hDR, show (v3 : ℝ) * (1 / ((v3 - v2 : ℕ) : ℝ)) = (v3 : ℝ) / ((v3 - v2 : ℕ) : ℝ) by ring]
    exact fun h => hD3 ((bhk_fract_nat_div_eq_zero_iff v3 _ hD).mp h)
  have hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
      (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0 := by
    show Int.fract ((v1 : ℝ) * (1 / ((v3 : ℝ) - (v2 : ℝ)))) ≠ 0
    rw [hDR, show (v1 : ℝ) * (1 / ((v3 - v2 : ℕ) : ℝ)) = (v1 : ℝ) / ((v3 - v2 : ℕ) : ℝ) by ring]
    exact fun h => hD1 ((bhk_fract_nat_div_eq_zero_iff v1 _ hD).mp h)
  obtain ⟨t, ht, hl⟩ := exists_pos_of_lonely speeds hpos
    (bhk_s7_main speeds hmono hpos (by simpa [hs] using hsmall) ht0 hv1t0)
  exact ⟨t, ht, by simpa [hs] using hl 0, by simpa [hs] using hl 1, by simpa [hs] using hl 2,
    by simpa [hs] using hl 3, by simpa [hs] using hl 4⟩

end LRC.OrderSixN.S7
