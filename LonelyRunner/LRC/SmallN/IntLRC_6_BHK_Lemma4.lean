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
