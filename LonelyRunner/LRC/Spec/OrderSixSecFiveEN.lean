import LonelyRunner.LRC.Spec.OrderSixSecFiveN
import LonelyRunner.LRC.Spec.OrderSixPropElevenEN

/-!
# BHK §5 at named instants

`OrderSixSecFiveN` ports BHK §5 in BHK's form: Case 5.1 and Proposition 11 are
argued by assuming every time is covered and deriving `False`. This file is the
same proof with the covering removed, as in `OrderSixPropElevenEN`: each lemma
that read the covering at an instant `τ` now reads `τ` (`found_or_blocked`),
and either `τ` is the lonely instant or BHK's argument continues. `lonely_5`
is then proved with no covering anywhere.

The lemmas that do not read the covering are used from `OrderSixSecFiveN`.
-/

open MeasureTheory Set

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

namespace LRC.OrderSixN.S7.Named

open LRC.OrderSixN

/-- A 1234-gap (runners 1–4 all safe on `[a,b]`) is `⊆ B₅` under the covering
    hypothesis: every time is covered by some runner, and runners 1–4 are
    excluded, so runner 5 covers it. -/
lemma bhk_s5_case51_gap1234_subset (speeds : Fin 5 → ℕ)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      (Set.Icc a b ⊆ unsafeOf speeds ⟨4, by omega⟩) := by
  rcases found_or_blocked_on speeds (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  obtain ⟨i, hi⟩ := hblk s hs
  fin_cases i
  · exact absurd hi (not_lt.mpr (hgap s hs 0))
  · exact absurd hi (not_lt.mpr (hgap s hs 1))
  · exact absurd hi (not_lt.mpr (hgap s hs 2))
  · exact absurd hi (not_lt.mpr (hgap s hs 3))
  · exact (mem_unsafeOf_iff speeds _ s).mpr hi

/-- **The 1234-gap length bound.**  A 1234-gap has length `< 1/(3 v₅)`: being
    `⊆ B₅`, it lies in a single 5-block (`block_length_bound`).  The runner-5
    analogue of `bhk_lemma_4` for `B₄ ∪ B₅`. -/
lemma bhk_s5_case51_gap1234_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      (b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))) := by
  rw [or_iff_not_imp_right]
  intro hlong
  obtain ⟨τ, hτ, hτ5⟩ := Set.not_subset.mp
    (fun hsub => hlong (block_length_bound speeds ⟨4, by omega⟩ (hpos _) a b hab hsub))
  rw [mem_unsafeOf_iff, not_lt] at hτ5
  refine ⟨τ, fun i => ?_⟩
  fin_cases i
  · exact hgap τ hτ 0
  · exact hgap τ hτ 1
  · exact hgap τ hτ 2
  · exact hgap τ hτ 3
  · exact hτ5

/-- **Claim 10, eqn (24) — the `I₁` decomposition.**  If the 123-gap
    `I₁ = [t, t+1/(2v₃)]` contains a runner-4 block `[(j−1/6)/v₄, (j+1/6)/v₄]`
    (eqn (23)), then — under covering and `3v₄ < 4v₃` — the two pieces of `I₁`
    flanking the 4-block are 1234-gaps (each `< 1/(3v₅)`), so
    `1/(2v₃) < 2/(3v₅) + 1/(3v₄)`.  This is the second inequality of BHK eqn (24);
    it is the first assembly of the 1234-gap machinery. -/
lemma bhk_s5_case51_claim10_decomp (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      < 2 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  set v3 := (speeds ⟨2, by omega⟩ : ℝ) with hv3def
  set v4 := (speeds ⟨3, by omega⟩ : ℝ) with hv4def
  set v5 := (speeds ⟨4, by omega⟩ : ℝ) with hv5def
  have h12v3 : (1 : ℝ) / (2 * v3) ≤ 1 / v4 := one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / v4 ≤ ((j : ℝ) + 1 / 6) / v4 := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have hI1bound : ((j : ℝ) - 1 / 6) / v4 ≤ t + 1 / (2 * v3) := le_trans hjj hjt'
  have htj1 : t ≤ ((j : ℝ) + 1 / 6) / v4 := le_trans hjt hjj
  -- Positioning: block j-1 is left of I₁, block j+1 is right of I₁ (uses `3v₄<4v₃`).
  have hF1 : ((j : ℝ) - 5 / 6) / v4 ≤ t := by
    have e : ((j : ℝ) - 5 / 6) / v4 = ((j : ℝ) + 1 / 6) / v4 - 1 / v4 := by
      field_simp; ring
    linarith [hjt', h12v3, e]
  have hF2 : t + 1 / (2 * v3) ≤ ((j : ℝ) + 5 / 6) / v4 := by
    have e : ((j : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 + 1 / v4 := by
      field_simp; ring
    linarith [hjt, h12v3, e]
  -- The left flank [t, (j-1/6)/v₄] is a 1234-gap.
  obtain hF | hLshort : Found speeds ∨ (((j : ℝ) - 1 / 6) / v4 - t < 1 / (3 * v5)) := by
    apply bhk_s5_case51_gap1234_short speeds hpos hjt
    intro s hs i
    fin_cases i
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 0
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 1
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 2
    · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) (j - 1) s
      · rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / v4 = ((j : ℝ) - 5 / 6) / v4 from by
            push_cast; ring]
        linarith [hF1, hs.1]
      · rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 from by
            push_cast; ring]
        exact hs.2
  · exact Or.inl hF
  -- The right flank [(j+1/6)/v₄, t+1/(2v₃)] is a 1234-gap.
  obtain hF | hRshort : Found speeds ∨ ((t + 1 / (2 * v3)) - ((j : ℝ) + 1 / 6) / v4 < 1 / (3 * v5)) := by
    apply bhk_s5_case51_gap1234_short speeds hpos hjt'
    intro s hs i
    fin_cases i
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 0
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 1
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 2
    · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) j s
      · exact hs.1
      · exact le_trans hs.2 hF2
  · exact Or.inl hF
  right
  -- Sum the two flank lengths.
  have hsum : (((j : ℝ) - 1 / 6) / v4 - t) + ((t + 1 / (2 * v3)) - ((j : ℝ) + 1 / 6) / v4)
      = 1 / (2 * v3) - 1 / (3 * v4) := by field_simp; ring
  have htwo : (1 : ℝ) / (3 * v5) + 1 / (3 * v5) = 2 / (3 * v5) := by ring
  linarith [hLshort, hRshort, hsum, htwo]

/-- The left flank `[t, (j−1/6)/v₄]` of a 4-block in the 123-gap `I₁` is a
    1234-gap, hence `⊆ B₅`.  (Helper for eqn (24)'s distinct-5-blocks argument.) -/
lemma bhk_s5_case51_flank_left_subset (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (Set.Icc t (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      ⊆ unsafeOf speeds ⟨4, by omega⟩) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12v3 : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨3, by omega⟩ : ℝ) :=
    one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have hI1bound : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := le_trans hjj hjt'
  have hF1 : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    have e : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    linarith [hjt', h12v3, e]
  apply bhk_s5_case51_gap1234_subset speeds
  intro s hs i
  fin_cases i
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 0
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 1
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 2
  · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) (j - 1) s
    · rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
      linarith [hF1, hs.1]
    · rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
      exact hs.2

/-- The right flank `[(j+1/6)/v₄, t+1/(2v₃)]` of a 4-block in `I₁` is a 1234-gap,
    hence `⊆ B₅`. -/
lemma bhk_s5_case51_flank_right_subset (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) : Found speeds ∨
      (Set.Icc (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨4, by omega⟩) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12v3 : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨3, by omega⟩ : ℝ) :=
    one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have htj1 : t ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := le_trans hjt hjj
  have hF2 : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have e : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) + 1 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    linarith [hjt, h12v3, e]
  apply bhk_s5_case51_gap1234_subset speeds
  intro s hs i
  fin_cases i
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 0
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 1
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 2
  · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) j s
    · exact hs.1
    · exact le_trans hs.2 hF2

/-- **Claim 10, eqn (24), first inequality** (`2x₅/3 < x₄/3`).  A 4-block
    `[(j−1/6)/v₄, (j+1/6)/v₄] ⊆ I₁` splits the 123-gap `I₁` into two 1234-gaps.
    Each lies in a single 5-block (`block_containment`), and the two 5-blocks are
    *distinct* (`I₁` is longer than one 5-block since `v₅ > v₃`); the 5-gap
    between them therefore lies inside the 4-block, forcing `2/(3v₅) < 1/(3v₄)`. -/
lemma bhk_s5_case51_claim10_5gap (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (2 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h34 : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    have h45 : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    have : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := lt_trans h34 h45
    exact_mod_cast this
  -- Each flank is ⊆ B₅; pin it inside a single 5-block.
  obtain hF | hLsub := bhk_s5_case51_flank_left_subset speeds hpos t hgap123 h22 j hjt'
  · exact Or.inl hF
  obtain hF | hRsub := bhk_s5_case51_flank_right_subset speeds hpos t hgap123 h22 j hjt
  · exact Or.inl hF
  right
  obtain ⟨k1, hk1a, hk1b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _) t
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) hjt hLsub
  obtain ⟨k2, hk2a, hk2b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) hjt' hRsub
  set v3 := (speeds ⟨2, by omega⟩ : ℝ) with hv3def
  set v4 := (speeds ⟨3, by omega⟩ : ℝ) with hv4def
  set v5 := (speeds ⟨4, by omega⟩ : ℝ) with hv5def
  -- The two 5-blocks `k1, k2` are distinct: I₁ is longer than one 5-block.
  have hv5_2v3 : (1 : ℝ) / 2 < v5 / (2 * v3) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hexp : v5 * (t + 1 / (2 * v3)) = v5 * t + v5 / (2 * v3) := by ring
  have hk12 : (k1 : ℝ) < (k2 : ℝ) := by linarith [hk1a, hk2b, hexp, hv5_2v3]
  have hk1k2R : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by
    have h1 : k1 < k2 := by exact_mod_cast hk12
    have h2 : k1 + 1 ≤ k2 := by omega
    exact_mod_cast h2
  -- The 5-gap between blocks k1, k2 lies inside the 4-block ⇒ width bound.
  have key : ((k2 : ℝ) - 1 / 6) - ((k1 : ℝ) + 1 / 6)
      < v5 * (((j : ℝ) + 1 / 6) / v4) - v5 * (((j : ℝ) - 1 / 6) / v4) := by
    linarith [hk1b, hk2a]
  have hdiff : v5 * (((j : ℝ) + 1 / 6) / v4) - v5 * (((j : ℝ) - 1 / 6) / v4)
      = v5 / (3 * v4) := by field_simp; ring
  have h23 : (2 : ℝ) / 3 < v5 / (3 * v4) := by rw [← hdiff]; linarith [key, hk1k2R]
  have h2v4v5 : 2 * v4 < v5 := by rw [lt_div_iff₀ (by positivity)] at h23; linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith

/-- **Claim 10 — no 4-block in `I₁` together with one in `I₃` (BHK p. 15).**
    The geometric wrapper of the D/E counting core.  Given the triple
    configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃, t+3/(2v₃)]` are
    123-gaps, both `⊆ B₄ ∪ B₅` via the covering `hcover`), a 4-block in `I₁`
    (eqn (23): `h23a`/`h23b`) and the forced 4-block in `I₃` (eqn (25):
    `h25a`/`h25b`) are contradictory.  We extract the runner-5 blocks of the two
    `I₁` flanks (`flank_left/right_subset` + `block_containment`) and of the left
    `I₃` flank (`flank_left_subset` re-used at `t' = t+1/v₃`, `j' = j+1`), then
    invoke `bhk_s5_case51_claim10_count`.  This is the `(23) ∧ (25) ⇒ False` half
    of Claim 10; deriving (25) from (23) (eqn (25) geometry) is the separate
    `x₄/3 + x₅/3 < 1/2` step (`bhk_s5_case51_x45_sum`). -/
lemma bhk_s5_case51_claim10_contra (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h25a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h25b : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  -- eqn (24) and the `x₅` bounds `2v₃ < v₅ < 4v₃`.
  obtain hF | h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos t hgapI1 h22 j h23a h23b
  · exact hF
  obtain hF | h24b := bhk_s5_case51_claim10_decomp speeds hpos t hgapI1 h22 j h23a h23b
  · exact hF
  obtain ⟨_, hv54v3⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  -- eqn (24a) in the form `2 v₄ < v₅`.
  have h24a' : 2 * (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h24a; linarith
  -- The two `I₁` flanks are 1234-gaps `⊆ B₅`; pin each in a single 5-block.
  obtain hF | hL1 := bhk_s5_case51_flank_left_subset speeds hpos t hgapI1 h22 j h23b
  · exact hF
  obtain hF | hR1 := bhk_s5_case51_flank_right_subset speeds hpos t hgapI1 h22 j h23a
  · exact hF
  obtain ⟨a1, hG1a, hG1b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _) t
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) h23a hL1
  obtain ⟨a2, hG2a, hG2b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) h23b hR1
  -- The left `I₃` flank: re-use `flank_left_subset` at `t' = t+1/v₃`, `j' = j+1`.
  obtain hF | hL3 := bhk_s5_case51_flank_left_subset speeds hpos
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 (j + 1)
    (by rw [show (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]; exact h25b)
  · exact hF
  rw [show (((j + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring] at hL3
  obtain ⟨a3, hG3a, hG3b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    h25a hL3
  exact False.elim <| bhk_s5_case51_claim10_count (speeds ⟨2, by omega⟩ : ℝ) (speeds ⟨3, by omega⟩ : ℝ)
    (speeds ⟨4, by omega⟩ : ℝ) t j a1 a2 a3 hv3 hv4 hv54v3 h34 h24a'
    hG1a hG1b hG2a hG2b hG3a hG3b

/-- **A 4-safe sub-interval of `I₁` is a short 1234-gap.**  Companion to
    `bhk_s5_case51_I3_4safe_short` for the gap `I₁ = [t, t+1/(2v₃)]`: if
    `[a,b] ⊆ I₁` lies in the `k`-th runner-4 gap `[(k+1/6)/v₄, (k+5/6)/v₄]`, then
    `[a,b]` is a 1234-gap, so `b−a < 1/(3v₅)` (`gap1234_short`). -/
lemma bhk_s5_case51_I1_4safe_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (k : ℤ) (a b : ℝ) (hab : a ≤ b)
    (ha : t ≤ a) (hb : b ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hg1 : ((k : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ a)
    (hg2 : b ≤ ((k : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) : Found speeds ∨
      (b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))) := by
  apply bhk_s5_case51_gap1234_short speeds hpos hab
  intro s hs i
  fin_cases i
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 0
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 1
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 2
  · exact bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) k s
      (le_trans hg1 hs.1) (le_trans hs.2 hg2)

/-- **Helper for eqn (25): a 4-safe sub-interval of `I₃` is a short 1234-gap.**
    If `[a,b] ⊆ I₃ = [t+1/v₃, t+3/(2v₃)]` lies in the `k`-th runner-4 gap
    `[(k+1/6)/v₄, (k+5/6)/v₄]`, then `[a,b]` is a 1234-gap, so `b−a < 1/(3v₅)`
    (`gap1234_short`).  Runner-5 analogue of the I₁ flank helpers, for I₃. -/
lemma bhk_s5_case51_I3_4safe_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (k : ℤ) (a b : ℝ) (hab : a ≤ b)
    (ha : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ a)
    (hb : b ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hg1 : ((k : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ a)
    (hg2 : b ≤ ((k : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) : Found speeds ∨
      (b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))) := by
  apply bhk_s5_case51_gap1234_short speeds hpos hab
  intro s hs i
  fin_cases i
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 0
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 1
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 2
  · exact bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) k s
      (le_trans hg1 hs.1) (le_trans hs.2 hg2)

/-- **BHK eqn (25): the forced 4-block in `I₃`.**  Given a 4-block in `I₁`
    (eqn (23)) and `I₃ = [t+1/v₃, t+3/(2v₃)] ⊆ B₄ ∪ B₅` (via `hcover` + the I₃
    123-gap), the `(j+1)`-th runner-4 block lies inside `I₃`.  The `j`-th block is
    left of `I₃` and the `(j+2)`-th is right of it (P1/P2, from (23) + `h22`), so
    `(j+1)` is the only candidate; if it is not contained, `I₃` is covered by at
    most one 4-block part plus one 1234-gap flank, of total length `< 1/(3v₄) +
    1/(3v₅) < 1/(2v₃) = |I₃|` (`x45_sum`, `h45sum`), or `I₃` lies in a single
    4-gap forcing `|I₃| < 1/(3v₅)` (`v₅ > 2v₃`, `h2v3v5`) — both impossible. -/
lemma bhk_s5_case51_eqn25 (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h2v3v5 : 2 * (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ))
    (h45sum : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))
      < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hpos2 : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
  -- P1: the j-th 4-block right edge is at/left of I₃'s left end.
  have hP1 : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) := by
    have h : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) :=
      one_div_le_one_div_of_le hv3 (by linarith)
    linarith [h23b, h]
  -- P2: the (j+2)-th 4-block left edge is right of I₃'s right end.
  have hP2 : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have e : ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) + 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    have h32 : 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
    linarith [h23a, e, h32, e2]
  have hlen : (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      - (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hblk : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    field_simp; ring
  have ecast1 : (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast2 : (((j + 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
    (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hbl | hbl
  · rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exact Or.inr ⟨hbl, hbr⟩
    · left
      rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j+1)-th block right of I₃: I₃ ⊆ left 4-gap (k = j) ⊆ B₅, too long for one 5-block.
        obtain hF | hI3 := bhk_s5_case51_I3_4safe_short speeds hpos t hgapI3 j
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _) hP1 hmiss
        · exact hF
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI3
        linarith
      · -- (j+1)-th block straddles I₃'s right end: I₃ = (left flank, k = j) + (block part).
        obtain hF | hL := bhk_s5_case51_I3_4safe_short speeds hpos t hgapI3 j
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          hbl (le_refl _) (le_of_lt hstr) hP1 (le_refl _)
        · exact hF
        linarith [hL, hblk, hbr, h45sum]
  · rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · left
      rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j+1)-th block left of I₃: I₃ ⊆ right 4-gap (k = j+1) ⊆ B₅, too long.
        obtain hF | hI3 := bhk_s5_case51_I3_4safe_short speeds hpos t hgapI3 (j + 1)
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast1]; exact hmiss) (by rw [ecast2]; exact hP2)
        · exact hF
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI3
        linarith
      · -- (j+1)-th block straddles I₃'s left end: I₃ = (block part) + (right flank, k = j+1).
        obtain hF | hR := bhk_s5_case51_I3_4safe_short speeds hpos t hgapI3 (j + 1)
          (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          hbr (le_of_lt hstr) (le_refl _)
          ecast1.le (by rw [ecast2]; exact hP2)
        · exact hF
        linarith [hR, hblk, hbl, h45sum]
    · -- (j+1)-th block ⊇ I₃: impossible since |block| = 1/(3v₄) < 1/(2v₃) = |I₃|.
      exfalso
      have h : (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          - (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        linarith [hblk, hbl, hbr]
      rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at h
      linarith

/-- **BHK eqn (25), reflected: the forced 4-block in `I₁`.**  Mirror of
    `bhk_s5_case51_eqn25` under the left↔right symmetry of the triple
    configuration: a 4-block in `I₃` (the `j`-th) together with the covered
    123-gap `I₁ = [t, t+1/(2v₃)]` forces the `(j−1)`-th 4-block inside `I₁`.
    The `j`-th block is right of `I₁` and the `(j−2)`-th is left of it (P1'/P2'),
    so `(j−1)` is the only candidate; the same length accounting (`h45sum`,
    `h2v3v5`) rules out every non-contained position. -/
lemma bhk_s5_case51_eqn25' (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h2v3v5 : 2 * (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ))
    (h45sum : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))
      < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (t ≤ ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hpos2 : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
  -- P1': the j-th 4-block left edge is at/right of I₁'s right end.
  have hP1 : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) :=
      one_div_le_one_div_of_le hv3 (by linarith)
    linarith [h23a, h]
  -- P2': the (j-2)-th 4-block right edge is left of I₁'s left end.
  have hP2 : ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    have e : ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    have h32 : 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
    linarith [h23b, e, h32, e2]
  have hlen : (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) - t
      = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hblk : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    field_simp; ring
  have ecast1 : (((j - 2 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast2 : (((j - 2 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast3 : (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast4 : (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  rcases le_or_gt t (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hbl | hbl
  · rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exact Or.inr ⟨hbl, hbr⟩
    · left
      rcases le_or_gt (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j-1)-th block right of I₁: I₁ ⊆ left 4-gap (k = j-2) ⊆ B₅, too long.
        obtain hF | hI1 := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 (j - 2)
          t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast1]; exact hP2) (by rw [ecast2]; exact hmiss)
        · exact hF
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI1
        linarith
      · -- (j-1)-th block straddles I₁'s right end: I₁ = (left flank, k=j-2) + (block part).
        obtain hF | hL := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 (j - 2)
          t (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          hbl (le_refl _) (le_of_lt hstr) (by rw [ecast1]; exact hP2) ecast2.symm.le
        · exact hF
        linarith [hL, hblk, hbr, h45sum]
  · rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · left
      rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) t with hmiss | hstr
      · -- (j-1)-th block left of I₁: I₁ ⊆ right 4-gap (k = j-1) ⊆ B₅, too long.
        obtain hF | hI1 := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 (j - 1)
          t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast3]; exact hmiss) (by rw [ecast4]; exact hP1)
        · exact hF
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI1
        linarith
      · -- (j-1)-th block straddles I₁'s left end: I₁ = (block part) + (right flank, k=j-1).
        obtain hF | hR := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 (j - 1)
          (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          hbr (le_of_lt hstr) (le_refl _) ecast3.le (by rw [ecast4]; exact hP1)
        · exact hF
        linarith [hR, hblk, hbl, h45sum]
    · -- (j-1)-th block ⊇ I₁: impossible since |block| = 1/(3v₄) < 1/(2v₃) = |I₁|.
      exfalso
      have h : (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) - t
          < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        linarith [hblk, hbl, hbr]
      rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at h
      linarith

/-- **Claim 10 (BHK p. 15): no 4-block is contained in `I₁`.**  In the triple
    configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃, t+3/(2v₃)]` are
    123-gaps `⊆ B₄ ∪ B₅` under the covering `hcover`), a 4-block in `I₁`
    (eqn (23): `h23a`/`h23b`) is contradictory.  Assembles the section: eqn (24)
    (`claim10_5gap`/`claim10_decomp`) ⟹ `1/4 < x₅ < 1/2` (`x5_bounds`) and
    `x₄/3+x₅/3 < 1/2` (`x45_sum`) ⟹ a forced 4-block in `I₃` (eqn (25),
    `eqn25`) ⟹ the consecutive-5-block counting `False` (`claim10_contra`).  By
    the left-right symmetry of the triple configuration this also rules out a
    4-block in `I₃`. -/
lemma bhk_s5_case51_claim10_no4block_I1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain hF | h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos t hgapI1 h22 j h23a h23b
  · exact hF
  obtain hF | h24b := bhk_s5_case51_claim10_decomp speeds hpos t hgapI1 h22 j h23a h23b
  · exact hF
  obtain ⟨h2v3v5, _⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  have h45sum := bhk_s5_case51_x45_sum _ _ _ hv3 h34 h2v3v5
  obtain hF | ⟨h25a, h25b⟩ :=
    bhk_s5_case51_eqn25 speeds hpos t hgapI3 h22 h34 j h23a h23b h2v3v5 h45sum
  · exact hF
  exact bhk_s5_case51_claim10_contra speeds hmono hpos t hgapI1 hgapI3 h22 j
    h23a h23b h25a h25b

/-- **Claim 10 (BHK p. 15): no 4-block is contained in `I₃`.**  The left↔right
    mirror of `bhk_s5_case51_claim10_no4block_I1`: a 4-block in `I₃` (the `j`-th)
    is contradictory.  Eqn (24)/`x5_bounds`/`x45_sum` (applied to the `I₃` block)
    feed the reflected `eqn25'`, which forces the `(j−1)`-th block into `I₁`;
    `claim10_contra` (at index `j−1`) then closes it.  Together with the `I₁`
    lemma this is the full Claim 10. -/
lemma bhk_s5_case51_claim10_no4block_I3 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  -- eqn (24) and the `x₅` bounds, from the `I₃` 4-block (gap start `t+1/v₃`).
  obtain hF | h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 j h23a h23b
  · exact hF
  obtain hF | h24b := bhk_s5_case51_claim10_decomp speeds hpos
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 j h23a h23b
  · exact hF
  obtain ⟨h2v3v5, _⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  have h45sum := bhk_s5_case51_x45_sum _ _ _ hv3 h34 h2v3v5
  -- Reflected eqn (25): the `(j-1)`-th 4-block lies in `I₁`.
  obtain hF | ⟨h25a, h25b⟩ :=
    bhk_s5_case51_eqn25' speeds hpos t hgapI1 h22 h34 j h23a h23b h2v3v5 h45sum
  · exact hF
  -- `claim10_contra` at index `j-1`: the `I₁` block `(j-1)` and the `I₃` block `j`.
  have c1 : (((j - 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c2 : (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c3 : (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c4 : (((j - 1 : ℤ) : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  exact bhk_s5_case51_claim10_contra speeds hmono hpos t hgapI1 hgapI3 h22 (j - 1)
    (by rw [c1]; exact h25a) (by rw [c2]; exact h25b)
    (by rw [c3]; exact h23a) (by rw [c4]; exact h23b)

/-- **A covered 123-gap meets a 4-block.**  The length-`1/(2v₃)` gap
    `I = [a, a+1/(2v₃)]` (123-safe, so `⊆ B₄ ∪ B₅` under covering) cannot be
    4-safe throughout — that would make it a 1234-gap of length `1/(2v₃)`, but
    `gap1234_short` bounds 1234-gaps by `1/(3v₅) < 1/(2v₃)` (`v₅ > v₃`).  So some
    point of `I` lies in a runner-4 block.  Foundational for the span bound
    (29)/(30): each gap of a multiple configuration meets a 4-block. -/
lemma bhk_s5_case51_gap_meets_block (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (a : ℝ)
    (hgap : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ)) : Found speeds ∨
      (∃ p ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      p ∈ unsafeOf speeds ⟨3, by omega⟩) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  obtain hF | hsub := bhk_prop11_gap_covered speeds hgap
  · exact Or.inl hF
  right
  by_contra hcon
  push_neg at hcon
  -- Every point of `I` avoids `B₄`, so `I ⊆ B₅`.
  have hsub5 : Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨4, by omega⟩ := fun p hp => (hsub hp).resolve_left (hcon p hp)
  have hab : a ≤ a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := block_length_bound speeds ⟨4, by omega⟩ (hpos _) a
    (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub5
  rw [add_sub_cancel_left, div_lt_div_iff₀ (by positivity) (by positivity)] at hlen
  linarith

/-- **Consecutive gaps have consecutive blocks (`p' = p + 1`).**  If block `p`
    meets a covered 123-gap `G = [a, a+1/(2v₃)]` and block `p'` meets the next
    gap `G' = [a+1/v₃, a+1/v₃+1/(2v₃)]`, then `p' = p + 1`.  `block_step` gives
    `p+1 ≤ p' ≤ p+2`; the skip `p' = p+2` traps block `p+1` strictly inside the
    middle `(a+1/(2v₃), a+1/v₃)` — its left edge `> a+1/(2v₃)` (from `hpL` and the
    block period `1/v₄ > 3/(4v₃)`, i.e. (22)) and its right edge `< a+1/v₃` (from
    `hp'R` and (22)) — contradicting Claim 9 (no 4-block in `I₂`).  The
    consecutiveness step of the span bound (29)/(30). -/
lemma bhk_s5_case51_block_succ (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a : ℝ)
    (hgapA : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapB : ∀ s ∈ Set.Icc (a + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (p p' : ℤ)
    (hpL : a < ((p : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hpR : ((p : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hp'L : a + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      < ((p' : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hp'R : ((p' : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (p' = p + 1) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3' : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := ne_of_gt hv3
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain ⟨hstep1, hstep2⟩ :=
    bhk_s5_case51_block_step speeds hpos h22 h34 a p p' hpL hpR hp'L hp'R
  rcases (show p' = p + 1 ∨ p' = p + 2 by omega) with h | h
  · exact Or.inr h
  · left
    subst h
    -- The two gaps in the `⊆ B₄ ∪ B₅` form Claim 9 consumes.
    obtain hF | hsubA := bhk_prop11_gap_covered speeds hgapA
    · exact hF
    obtain hF | hsubB0 := bhk_prop11_gap_covered speeds hgapB
    · exact hF
    have hsubB : Set.Icc (a + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (a + 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩ := by
      rw [show a + 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
            = a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
            from by field_simp; ring]
      exact hsubB0
    -- The shared `1/(2v₃) < 2/(3v₄)` slack (eqn (22): `3v₄ < 4v₃`).
    have hslack : 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    -- Block `p+1`'s left edge is strictly right of `I₁`'s end.
    have hmidL : a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < (((p + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [show (((p + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = ((p : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              + 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by push_cast; field_simp; ring]
      linarith [hpL, hslack]
    -- Block `p+1`'s right edge is strictly left of `I₃`'s start.
    have hmidR : (((p + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < a + 1 / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [show (((p + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = (((p + 2 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by push_cast; field_simp; ring]
      linarith [hp'R, hslack]
    exact False.elim <| bhk_s5_case51_claim9 speeds hmono hpos a hsubA hsubB h22 (p + 1)
      (le_of_lt hmidL) (le_of_lt hmidR)

/-- **A covered 123-gap overlaps a 4-block — extracting the block index.**
    `gap_straddle` without the straddle/`hnofull` part: a covered 123-gap
    `[a, a+1/(2v₃)]` meets some 4-block `m` (`a < (m+1/6)/v₄` and
    `(m−1/6)/v₄ < a+1/(2v₃)`).  The existence half feeding the consecutiveness
    induction `span_consec`. -/
lemma bhk_s5_case51_gap_block_idx (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a : ℝ)
    (hgap : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      (∃ m : ℤ, a < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain hF | ⟨p, hpG, hpB⟩ := bhk_s5_case51_gap_meets_block speeds hpos a hgap h35
  · exact Or.inl hF
  right
  rw [mem_unsafeOf_iff_bhkB] at hpB
  obtain ⟨m, hm⟩ := hpB
  have habs := abs_lt.mp hm
  have hpl : ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < p := by
    rw [div_lt_iff₀ hv4]; nlinarith [habs.1]
  have hpr : p < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [lt_div_iff₀ hv4]; nlinarith [habs.2]
  exact ⟨m, by linarith [hpG.1, hpr], by linarith [hpl, hpG.2]⟩

/-- **Consecutiveness across a multiple configuration (BHK eqn (29) skeleton).**
    Given `l+1` covered 123-gaps `G_m = [t+m/v₃, t+m/v₃+1/(2v₃)]` (`m ≤ l`), there
    is a block index `j` such that block `j` meets `G_0` *and* block `j+l` meets
    `G_l`.  Induction on `l`: existence of a meeting block is `gap_block_idx`; the
    step `j+m ↦ j+(m+1)` is `block_succ` (consecutive gaps ⟹ consecutive blocks).
    This is the consecutiveness backbone of the span bound (29)/(30): it carries
    the *outer two* blocks to the configuration's ends, where the endpoint
    extraction (covering of the end-flanks) then yields the eqn (29) bounds. -/
lemma bhk_s5_case51_span_consec (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      (∃ j : ℤ,
      (t < ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
        ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          < t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) ∧
      (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
          < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
        ((j : ℝ) + (l : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          < t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))) := by
  revert hgaps
  induction l with
  | zero =>
    intro hgaps
    obtain hF | ⟨j, hjL, hjR⟩ := bhk_s5_case51_gap_block_idx speeds hmono hpos t
      (by have h := hgaps 0 (le_refl 0); simpa only [Nat.cast_zero, zero_div, add_zero] using h)
    · exact Or.inl hF
    exact Or.inr ⟨j, ⟨hjL, hjR⟩,
      by simpa only [Nat.cast_zero, zero_div, add_zero] using hjL,
      by simpa only [Nat.cast_zero, zero_div, add_zero] using hjR⟩
  | succ n ih =>
    intro hgaps
    obtain hF | ⟨j, ⟨hj0L, hj0R⟩, hjnL, hjnR⟩ := ih (fun m hm => hgaps m (by omega))
    · exact Or.inl hF
    have hbr : t + (n : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + ((n + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by push_cast; ring
    obtain hF | ⟨p, hqL, hqR⟩ := bhk_s5_case51_gap_block_idx speeds hmono hpos
      (t + ((n + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps (n + 1) (le_refl _))
    · exact Or.inl hF
    have hcast : (((j + (n : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (n : ℝ) := by push_cast; ring
    obtain hF | hstep : Found speeds ∨ p = j + (n : ℤ) + 1 := by
      refine bhk_s5_case51_block_succ speeds hmono hpos
        (t + (n : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps n (by omega)) ?_ h22
        (j + (n : ℤ)) p ?_ ?_ ?_ ?_
      · rw [hbr]; exact hgaps (n + 1) (le_refl _)
      · rw [hcast]; exact hjnL
      · rw [hcast]; exact hjnR
      · rw [hbr]; exact hqL
      · rw [hbr]; exact hqR
    · exact Or.inl hF
    refine Or.inr ⟨j, ⟨hj0L, hj0R⟩, ?_, ?_⟩
    · rw [show (j : ℝ) + ((n + 1 : ℕ) : ℝ) = (p : ℝ) from by rw [hstep]; push_cast; ring]
      exact hqL
    · rw [show (j : ℝ) + ((n + 1 : ℕ) : ℝ) = (p : ℝ) from by rw [hstep]; push_cast; ring]
      exact hqR

/-- **A 4-block fully inside a gap of a multiple configuration is impossible.**
    For a multiple configuration `G_0, …, G_l` (`1 ≤ l`, each `G_m =
    [t+m/v₃, t+m/v₃+1/(2v₃)]` a 123-gap), if the `(j+m)`-th runner-4 block lies
    *fully inside* `G_m` for some `m ≤ l` then `False`.  Dispatches on position:
    an initial/middle gap (`m < l`) is an `I₁` with partner `I₃ = G_{m+1}`
    (`claim10_no4block_I1`); the final gap (`m = l`) is an `I₃` with partner
    `I₁ = G_{l-1}` (the mirror `claim10_no4block_I3`).  This is the leaf consumed
    by the drift-window bad-case argument for eqn (29). -/
lemma bhk_s5_case51_block_fully_in_gap_absurd (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (j : ℤ) (m : ℕ) (hm : m ≤ l)
    (hfullL : t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ (((j : ℝ) + (m : ℝ)) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hfullR : (((j : ℝ) + (m : ℝ)) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds := by
  have hcast : (((j + (m : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (m : ℝ) := by push_cast; ring
  rcases lt_or_eq_of_le hm with hlt | heq
  · -- `m < l`: block `j+m` is fully inside `G_m = I₁`; partner `I₃ = G_{m+1}`.
    have hbr : t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + ((m + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by push_cast; ring
    refine bhk_s5_case51_claim10_no4block_I1 speeds hmono hpos
      (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps m hm) ?_ h22 (j + (m : ℤ)) ?_ ?_
    · rw [hbr]; exact hgaps (m + 1) (by omega)
    · rw [hcast]; exact hfullL
    · rw [hcast]; exact hfullR
  · -- `m = l`: block `j+m` is fully inside `G_m = I₃`; partner `I₁ = G_{m-1}`.
    have hm1 : 1 ≤ m := by omega
    have hτ : t + ((m - 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
          + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [Nat.cast_sub hm1]; push_cast; field_simp; ring
    refine bhk_s5_case51_claim10_no4block_I3 speeds hmono hpos
      (t + ((m - 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps (m - 1) (by omega)) ?_ h22
      (j + (m : ℤ)) ?_ ?_
    · rw [hτ]; exact hgaps m hm
    · rw [hcast, hτ]; exact hfullL
    · rw [hcast, hτ]; exact hfullR

/-- **The bad alignment of eqn (29) is impossible (drift-window argument).**
    In a multiple configuration (`1 ≤ l`, every `G_m = [t+m/v₃, t+m/v₃+1/(2v₃)]`
    a 123-gap), the negation of eqn (29)'s disjunction — block `j` does *not* poke
    left of `G_0` (`t ≤ (j-1/6)/v₄`, i.e. `ψ_0 ≥ B`) *and* block `j+l` does *not*
    poke right of `G_l` (`(j+l+1/6)/v₄ ≤ t+l/v₃+1/(2v₃)`, i.e. `ψ_l ≤ T`) — forces,
    under `(22)`, some block `j+m` fully inside `G_m`, contradicting Claim 10.
    The drift sequence `ψ_m = (j+m)/v₄ − (t+m/v₃)` decreases by the fixed step
    `S = 1/v₃ − 1/v₄ > 0`; the window `[B,T]` (block `j+m ⊆ G_m`) has width
    `W = T − B = 1/(2v₃) − 1/(3v₄)`, and `(22)` is *exactly* `S < W`, so `ψ`
    cannot skip the window between `ψ_0 ≥ B` and `ψ_l ≤ T` (`drift_crossing`). -/
lemma bhk_s5_case51_bad_case_absurd (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (j : ℤ)
    (hbad0 : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hbadl : ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h3ne : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := hv3.ne'
  have h4ne : (speeds ⟨3, by omega⟩ : ℝ) ≠ 0 := hv4.ne'
  -- drift sequence `ψ_m = (j+m)/v₄ − (t + m/v₃)`.
  set ψ : ℕ → ℝ := fun m =>
    ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
      - (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) with hψdef
  -- step `ψ (m+1) = ψ m − S`, `S = 1/v₃ − 1/v₄`.
  have hstep : ∀ m, ψ (m + 1)
      = ψ m - (1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)) := by
    intro m; simp only [hψdef]; push_cast; field_simp; ring
  -- `ψ 0 ≥ B`, `B = 1/(6v₄)` (block `j` does not poke left of `G_0`).
  have h0 : (1 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) ≤ ψ 0 := by
    simp only [hψdef, Nat.cast_zero, add_zero, zero_div]
    rw [show ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = (j : ℝ) / (speeds ⟨3, by omega⟩ : ℝ) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp] at hbad0
    linarith
  -- `ψ l ≤ T`, `T = 1/(2v₃) − 1/(6v₄)` (block `j+l` does not poke right of `G_l`).
  have hlT : ψ l ≤ 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    simp only [hψdef]
    rw [show ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (l : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          + 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp] at hbadl
    linarith
  -- `S < W = T − B` ⟺ `(22)` (`3v₄ < 4v₃`).
  have hSW : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)
      < (1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [show (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)
        = ((speeds ⟨3, by omega⟩ : ℝ) - (speeds ⟨2, by omega⟩ : ℝ))
          / ((speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp,
      show (1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
            - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
        = (3 * (speeds ⟨3, by omega⟩ : ℝ) - 2 * (speeds ⟨2, by omega⟩ : ℝ))
          / (6 * ((speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ)))
      from by field_simp; ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hv3 hv4) (sub_pos.mpr h22), mul_pos hv3 hv4, hv3, hv4]
  obtain ⟨m, hml, hmB, hmT⟩ := drift_crossing ψ _ _ _ l hstep h0 hlT hSW
  simp only [hψdef] at hmB hmT
  refine bhk_s5_case51_block_fully_in_gap_absurd speeds hmono hpos h22 t l hl
    hgaps j m hml ?_ ?_
  · rw [show ((j : ℝ) + (m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp]
    linarith
  · rw [show ((j : ℝ) + (m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          + 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp]
    linarith

/-- **eqn (29a.right): the gap after block `j+l` reaches past `G_l` (covering).**
    If block `j+l` meets `G_l` on its right (`t+l/v₃ < (j+l+1/6)/v₄`), then the
    1234-gap centre `(j+l+1/2)/v₄` lies *past* `G_l`'s right end.  Otherwise the
    4-safe stretch `[(j+l+1/6)/v₄, (j+l+1/2)/v₄] ⊆ G_l ⊆ B₄∪B₅` would be a 1234-gap
    of length `1/(3v₄)`, but `I3_4safe_short` bounds such gaps by `1/(3v₅) < 1/(3v₄)`
    (`v₄ < v₅`).  This is the always-true right half of eqn (29)'s branch 1. -/
lemma bhk_s5_case51_endpoint_right_covering (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ) (l : ℕ) (j : ℤ)
    (hgapl : ∀ s ∈ Set.Icc (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hmeetR : t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) : Found speeds ∨
      (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      < ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have hjl : (((j + (l : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (l : ℝ) := by push_cast; ring
  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  have hbridge : t + ((l : ℝ) - 1) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      = t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by field_simp; ring
  obtain hF | hshort := bhk_s5_case51_I3_4safe_short speeds hpos
    (t + ((l : ℝ) - 1) / (speeds ⟨2, by omega⟩ : ℝ))
    (by rw [hbridge]; exact hgapl) (j + (l : ℤ))
    (((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
    (by rw [← sub_nonneg, show ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    (by rw [hbridge]; exact le_of_lt hmeetR)
    (by rw [hbridge]; exact hcon) (le_of_eq (by rw [hjl]))
    (by rw [hjl, ← sub_nonneg, show ((j : ℝ) + (l : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
  · exact hF
  have hba : ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
  rw [hba] at hshort
  have hlt : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- **eqn (29b.left): the gap before block `j` reaches before `G_0` (covering).**
    Mirror of `endpoint_right_covering`: if block `j` meets `G_0` on its left
    (`(j-1/6)/v₄ < t+1/(2v₃)`), then the 1234-gap centre `(j-1/2)/v₄` lies *before*
    `G_0`'s left end `t`.  Otherwise `[(j-1/2)/v₄, (j-1/6)/v₄] ⊆ G_0` is a 1234-gap
    of length `1/(3v₄) > 1/(3v₅)` (`I1_4safe_short`).  The always-true left half of
    eqn (29)'s branch 2. -/
lemma bhk_s5_case51_endpoint_left_covering (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (t : ℝ) (j : ℤ)
    (hgap0 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hmeetL : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) : Found speeds ∨
      (((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) < t) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have hjl : (((j - 1 : ℤ)) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  obtain hF | hshort := bhk_s5_case51_I1_4safe_short speeds hpos t hgap0 (j - 1)
    (((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (by rw [← sub_nonneg, show ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    hcon (le_of_lt hmeetL)
    (by rw [hjl, ← sub_nonneg, show ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    (le_of_eq (by rw [hjl]; ring))
  · exact hF
  have hba : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
      = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
  rw [hba] at hshort
  have hlt : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- **BHK eqns (29)+(30): the general-`l` span bound `(6l+3)v₄ < (6l+4)v₃`.**
    For a multiple configuration of `l+1` gaps (`1 ≤ l`, every `G_m` a 123-gap),
    `span_consec` pins the straddling blocks to `j, …, j+l`.  The covering gives
    the always-true endpoint facts `29a.right`/`29b.left`
    (`endpoint_right`/`left_covering`); a case split on which end pokes (block `j`
    left, or block `j+l` right) supplies the matching half of eqn (29), and the
    bad alignment (neither) is excluded by `bad_case_absurd`.  Subtracting eqn
    (29)'s two inequalities (`(l+2/3)/v₄ > (l+1/2)/v₃` in both branches) gives the
    bound.  (`l = 1` recovers `span_l1`'s `9v₄ < 10v₃`; here general `l`.) -/
lemma bhk_s5_case51_span_l (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      ((6 * (l : ℝ) + 3) * (speeds ⟨3, by omega⟩ : ℝ)
      < (6 * (l : ℝ) + 4) * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hU : (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      = (2 * (l : ℝ) + 1) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp
  -- both eqn-(29) branches reduce to this single inequality, then clear denominators.
  have finish : (2 * (l : ℝ) + 1) / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) →
      (6 * (l : ℝ) + 3) * (speeds ⟨3, by omega⟩ : ℝ)
        < (6 * (l : ℝ) + 4) * (speeds ⟨2, by omega⟩ : ℝ) := by
    intro hstep
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hstep
    nlinarith [hstep]
  obtain hF | ⟨j, ⟨_, hm0R⟩, hmlL, _⟩ :=
    bhk_s5_case51_span_consec speeds hmono hpos h22 t l hgaps
  · exact Or.inl hF
  obtain hF | h29aR := bhk_s5_case51_endpoint_right_covering speeds hmono hpos t l j
    (hgaps l (le_refl l)) hmlL
  · exact Or.inl hF
  obtain hF | h29bL := bhk_s5_case51_endpoint_left_covering speeds hmono hpos t j
    (by simpa only [Nat.cast_zero, zero_div, add_zero] using hgaps 0 (by omega)) hm0R
  · exact Or.inl hF
  by_cases h29aL : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < t
  · -- branch 1: block `j` pokes left (`29a.left`) + `29a.right`.
    refine Or.inr (finish ?_)
    have hBC : ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
        - ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) := by field_simp; ring
    rw [← hU, ← hBC]; linarith [h29aR, h29aL]
  · push_neg at h29aL
    by_cases h29bR : t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
        + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
    · -- branch 2: block `j+l` pokes right (`29b.right`) + `29b.left`.
      refine Or.inr (finish ?_)
      have hBC : ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) := by field_simp; ring
      rw [← hU, ← hBC]; linarith [h29bR, h29bL]
    · -- bad alignment: neither poke — impossible.
      push_neg at h29bR
      -- bad alignment: the instant `bad_case_absurd` names
      exact Or.inl (bhk_s5_case51_bad_case_absurd speeds hmono hpos h22 t l hl hgaps j
        h29aL h29bR)

/-- **BHK eqn (27): `x₄ > 9/10` (= `9 v₄ < 10 v₃`), the `l = 1` span bound.**
    For a triple configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃,
    t+3/(2v₃)]` are 123-gaps `⊆ B₄ ∪ B₅`), `9 v₄ < 10 v₃`.  Proof by contradiction:
    assume `10 v₃ ≤ 9 v₄`; locate `t` via `j = ⌊v₄ t + 1/6⌋`; a δ-range case
    analysis shows every position of the runner-4 blocks either places a full
    4-block inside `I₁`/`I₃` (killed by `claim10_no4block_I1`/`_I3`) or leaves a
    4-safe stretch `≥ 1/(3v₄) > 1/(3v₅)` inside `I₁`/`I₃` (killed by the covering
    bounds `I1_4safe_short`/`I3_4safe_short`). -/
lemma bhk_s5_case51_span_l1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ)) : Found speeds ∨
      (9 * (speeds ⟨3, by omega⟩ : ℝ) < 10 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h_v45 : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h23 : 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  -- `hcon : 10 v₃ ≤ 9 v₄`.  Locate `t`: `(j-1/6)/v₄ ≤ t < (j+5/6)/v₄`.
  obtain ⟨j, hjlo, hjhi⟩ : ∃ j : ℤ, (j : ℝ) - 1 / 6 ≤ (speeds ⟨3, by omega⟩ : ℝ) * t ∧
      (speeds ⟨3, by omega⟩ : ℝ) * t < (j : ℝ) + 5 / 6 := by
    refine ⟨⌊(speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6⌋, ?_, ?_⟩
    · have h := Int.floor_le ((speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6); linarith
    · have h := Int.lt_floor_add_one ((speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6); linarith
  have hjt_lo : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    rw [div_le_iff₀ hv4]; linarith [hjlo, mul_comm (speeds ⟨3, by omega⟩ : ℝ) t]
  have hjt_hi : t < ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [lt_div_iff₀ hv4]; linarith [hjhi, mul_comm (speeds ⟨3, by omega⟩ : ℝ) t]
  rcases le_or_gt (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) t with hB | hA
  · -- Case B: `I₁` starts in the 4-gap after block `j` (`(j+1/6)/v₄ ≤ t`).
    rcases le_or_gt (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hB1 | hB2
    · -- B1: `I₁ ⊆` 4-gap `j`, so all of `I₁` is a 4-safe stretch `= 1/(2v₃) ≥ 1/(3v₄)`.
      have h_2v3_3v4 : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      obtain hF | hsafe := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 j t
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (le_add_of_nonneg_right (by positivity)) (le_refl _) (le_refl _) hB hB1
      · exact hF
      linarith [hsafe, h_2v3_3v4, h_v45]
    · rcases le_or_gt t (((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)) with hB2a | hB2b
      · -- B2a: `I₁`'s left part `[t, (j+5/6)/v₄]` is a 4-safe gap `≥ 1/(3v₄)`.
        have bD : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
              = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
          field_simp; ring
        obtain hF | hsafe := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 j t
          (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (le_of_lt hjt_hi) (le_refl _) (le_of_lt hB2) hB (le_refl _)
        · exact hF
        have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
            ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - t := by linarith [hB2a, bD]
        linarith [hsafe, hlong, h_v45]
      · rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hB2bi | hB2bii
        · -- B2b-i: block `j+2 ⊆ I₃` — killed by `claim10_no4block_I3`.
          have bE : ((j : ℝ) + 13 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
                = 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
          have h_10v3' : 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
              ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
            rw [show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
                  = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          exact bhk_s5_case51_claim10_no4block_I3 speeds hmono hpos t hgapI1 hgapI3
            h22 (j + 2)
            (by rw [show (((j + 2 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                exact hB2bi)
            (by rw [show (((j + 2 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 13 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                linarith [hB2b, bE, h_10v3'])
        · -- B2b-ii: block `j+1 ⊆ I₁` — killed by `claim10_no4block_I1`.
          have bF : ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
            field_simp; ring
          have ehalf : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
          exact bhk_s5_case51_claim10_no4block_I1 speeds hmono hpos t hgapI1 hgapI3
            h22 (j + 1)
            (by rw [show (((j + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                exact le_of_lt hjt_hi)
            (by rw [show (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                linarith [hB2bii, bF, h23, ehalf])
  · -- Case A: `t < (j+1/6)/v₄`, i.e. `I₁` starts inside block `j`.
    rcases le_or_gt (((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hA1 | hA2
    · -- A1: `I₁`'s right flank `[(j+1/6)/v₄, t+1/(2v₃)]` is a 4-safe gap `≥ 1/(3v₄)`.
      have e2 : ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have e3 : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have hAend : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
          < ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by linarith [hA, e3, h23]
      have hpos34 : (0 : ℝ) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by positivity
      obtain hF | hsafe := bhk_s5_case51_I1_4safe_short speeds hpos t hgapI1 j
        (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (by linarith [hA1, e2, hpos34]) (le_of_lt hA) (le_refl _) (le_refl _) (le_of_lt hAend)
      · exact hF
      have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
            - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by linarith [hA1, e2]
      linarith [hsafe, hlong, h_v45]
    · -- A2: `I₃`'s 4-safe stretch after block `j+1` is `≥ 1/(3v₄)`.
      have bA : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
            = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have bB : (((j + 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
            = 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        push_cast; field_simp; ring
      have bC : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have ehalf : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
          = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
      have h_1v3 : 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have h_8v3 : 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        rw [show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have h_10v3 : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        rw [show 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
              = 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
          show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      obtain hF | hsafe := bhk_s5_case51_I3_4safe_short speeds hpos t hgapI3 (j + 1)
        (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (by linarith [hjt_lo, bC, h_8v3]) (by linarith [hA2, bA, h23, ehalf]) (le_refl _)
        (le_of_eq (by push_cast; ring)) (by linarith [hA2, bB, h_1v3])
      · exact hF
      have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
            - ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
        linarith [hjt_lo, bC, h_10v3]
      linarith [hsafe, hlong, h_v45]

/-- **BHK configuration existence (eqns (31)/(32)) — the multiple configuration.**
    In the generic case (`14/3 ≤ x₁`, not (`k=3 ∧ 8<x₁<26/3`)), there are integers
    `1 ≤ i ≤ l` such that the `l+1` windows `G_m = [(i+m+1/3)/v₃, (i+m+5/6)/v₃]`
    (`m ≤ l`, BHK placement `t = i+1/3`) are all 123-gaps.  Assembled from
    `config_feasible` (eqn (32) integer existence) and `config_window_safe`
    (the three eqn-(32) bounds force runners 1, 2, 3 safe on every window). -/
lemma bhk_s5_case51_config_exists (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (h511 : 14 / 3 ≤ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (h512 : ¬(k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
      ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3)) : Found speeds ∨
      (∃ i l : ℕ, 1 ≤ i ∧ i ≤ l ∧
      ∀ m : ℕ, m ≤ l →
        ∀ s ∈ Set.Icc (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
            + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
          (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
            + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
        ∀ r : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨r.val, by omega⟩ : ℝ) * s)) := by
  obtain ⟨i, l, hi1, hil, hA, hB, hC⟩ :=
    bhk_s5_case51_config_feasible speeds hmono hpos k D hk3 hD hkD h511 h512
  exact Or.inr ⟨i, l, hi1, hil,
    bhk_s5_case51_config_window_safe speeds hmono hpos i l D hD hA hB hC⟩

/-- **BHK generic case: the `l ≥ i` multiple configuration and its bounds.**
    When none of BHK conditions 1–4 hold — here `14/3 ≤ x₁` (`x₁ = v₃/v₁`) *and*
    not (`k = 3 ∧ 8 < x₁ < 26/3`) — eqn (32) yields integers `i ≤ l` realising a
    multiple configuration at `t = i + 1/3`.  The span (eqns (29)/(30), `span_l`)
    gives `x₄ > (6l+3)/(6l+4)` and the placement (eqn (33)) gives
    `x₄ < (6i+2)/(6i+3)` (`x₄ = v₃/v₄`); together with `i ≤ l` this is the
    contradiction `bhk_s5_case51_x4_incompatible`.  *Configuration construction
    (eqns (31)/(32) from `period1` + `runner3_close`, and the placement eqn (33))
    under construction.* -/
lemma bhk_s5_case51_config_bounds (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (h511 : 14 / 3 ≤ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (h512 : ¬(k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
      ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3)) : Found speeds ∨
      (∃ i l : ℕ, i ≤ l ∧
      (6 * (l : ℝ) + 3) / (6 * l + 4)
        < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ)
        < (6 * (i : ℝ) + 2) / (6 * i + 3)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain hF | ⟨i, l, hi1, hil, hgaps⟩ :=
    bhk_s5_case51_config_exists speeds hmono hpos hsmall k D hk3 hD hkD h511 h512
  · exact Or.inl hF
  have hl : 1 ≤ l := le_trans hi1 hil
  set t₀ : ℝ := ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ) with ht0def
  -- `G₀` is a covered 123-gap, giving eqn (22) `3v₄ < 4v₃`.
  have hgap0 : ∀ s ∈ Set.Icc t₀ (t₀ + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ r : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨r.val, by omega⟩ : ℝ) * s) := by
    simpa only [Nat.cast_zero, zero_div, add_zero] using hgaps 0 (by omega)
  obtain hF | hcov0 := bhk_prop11_gap_covered speeds hgap0
  · exact Or.inl hF
  have h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_s5_case51_x4_from_I1 speeds hmono hpos hcov0
  obtain hF | hspan := bhk_s5_case51_span_l speeds hmono hpos h22 t₀ l hl hgaps
  · exact Or.inl hF
  obtain hF | ⟨j, ⟨hm0L, hm0R⟩, _, _⟩ :=
    bhk_s5_case51_span_consec speeds hmono hpos h22 t₀ l hgaps
  · exact Or.inl hF
  obtain hF | hleft := bhk_s5_case51_endpoint_left_covering speeds hmono hpos t₀ j hgap0 hm0R
  · exact Or.inl hF
  right
  refine ⟨i, l, hil, ?_, ?_⟩
  · -- eqn (30) via `span_l`.
    rw [div_lt_div_iff₀ (by positivity) hv4]; nlinarith [hspan]
  · -- eqn (33): `span_consec` gives `j ≥ i+1`; `endpoint_left_covering` gives
    -- `(j-1/2)/v₄ < t₀`, so `(i+1/2)/v₄ < (i+1/3)/v₃`.
    have hblock_i : ((i : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < t₀ := by
      rw [ht0def, div_lt_div_iff₀ hv4 hv3]
      nlinarith [mul_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) (sub_nonneg.mpr h34.le), h34, hv3]
    have hlt_div : ((i : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := lt_trans hblock_i hm0L
    rw [div_lt_div_iff₀ hv4 hv4] at hlt_div
    have h2 : (i : ℝ) + 1 / 6 < (j : ℝ) + 1 / 6 := lt_of_mul_lt_mul_right hlt_div (le_of_lt hv4)
    have hij : (i : ℤ) + 1 ≤ j := by
      have : (i : ℤ) < j := by exact_mod_cast (by linarith : (i : ℝ) < (j : ℝ))
      omega
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    have hge : ((i : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ hv4 hv4]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (j:ℝ) - i - 1) (le_of_lt hv4)]
    have hcomb : ((i : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) < t₀ :=
      lt_of_le_of_lt hge hleft
    rw [ht0def, div_lt_div_iff₀ hv4 hv3] at hcomb
    apply bhk_s5_case51_eqn33 ((speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ)) i
    rw [← mul_div_assoc, div_lt_iff₀ hv4]; nlinarith [hcomb]

/-- **Case 5.1.1, the `x₄` bound `25 v₄ < 32 v₃`** (BHK `2x₄/3 > 25/48`).  The
    covered 123-gap `[21/(16 v₃), 11/(6 v₃)]` (length `25/(48 v₃)`) is `⊆ B₄ ∪ B₅`,
    so `bhk_lemma_4` bounds its length by `2/(3 v₄)`: `25/(48 v₃) < 2/(3 v₄)`,
    i.e. `25 v₄ < 32 v₃`. -/
lemma bhk_s5_case51_511_x4_bound (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hgap123 : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds ∨
      (25 * (speeds ⟨3, by omega⟩ : ℝ) < 32 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hab : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hv3]
  obtain hF | hcov := bhk_prop11_gap_covered speeds hgap123
  · exact Or.inl hF
  right
  have hlen := bhk_lemma_4 speeds hmono hpos _ _ hab hcov
  rw [show (11 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
        - 21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      = 25 / (48 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring] at hlen
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlen
  nlinarith [hlen]

/-- **Case 5.1.1, branch B (`13 x₄ > 11`): runner 5 cannot cover `gap2b`.**  The
    1234-gap `[21/(16 v₃), 121/(78 v₃)]`, being `⊆ B₅`, lies in a single 5-block;
    the width bound `149 v₅ < 208 v₃` forces `k ≤ 1` (left end) while the right end
    forces `k ≥ 2` — no such integer (BHK's "narrowest of margins").  Uses only
    `v₃ < v₅` (`x₅ < 1`); the `bhk_s5_case51_512_no_cover` recipe. -/
lemma bhk_s5_case51_511_no_cover_B (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hgap : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h78 : (0 : ℝ) < 78 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have hab : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 121 / (78 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h16 h78]; nlinarith [hv3]
  obtain hF | hsub := bhk_s5_case51_gap1234_subset speeds hgap
  · exact hF
  obtain ⟨k, hkL, hkR⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))) (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 21 * (speeds ⟨4, by omega⟩ : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h16] at hkL
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 121 * (speeds ⟨4, by omega⟩ : ℝ) / (78 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h78] at hkR
  -- hkL : ((k:ℝ) - 1/6) * (16 v₃) < 21 v₅ ;  hkR : 121 v₅ < ((k:ℝ) + 1/6) * (78 v₃)
  have width : 149 * (speeds ⟨4, by omega⟩ : ℝ) < 208 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [hkL, hkR]
  have hk_lo : (108 : ℝ) < 78 * (k : ℝ) := by
    have step : (108 : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 78 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkR, h35]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk2 : (2 : ℤ) ≤ k := by
    by_contra h; push_neg at h
    have hk1r : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
    linarith [hk_lo]
  have hk_hi : 16 * (k : ℝ) < 32 := by
    have step : 16 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 32 * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkL, width, hv3]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk1 : k ≤ (1 : ℤ) := by
    by_contra h; push_neg at h
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ k)
    linarith [hk_hi]
  omega

/-- **Case 5.1.1, branch A (`13 x₄ ≤ 11`): runner 5 cannot cover `gap1` and
    `gap2a` simultaneously.**  Both are 1234-gaps `⊆ B₅`, each in a single 5-block
    (`k₁` for `gap1`, `k₂` for `gap2a`).  `gap1`'s width bound gives `23 v₅ < 64 v₃`
    so `k₁ ∈ {2, 3}`, whence `gap1`'s right end gives `11 v₅ < 19 v₄` (BHK's
    `19 x₅ > 11 x₄`), bounding `k₂ ∈ {2, 3}`.  The four `(k₁, k₂)` pairs are each
    contradictory (`k₂ = 2`: `11 v₅ < 13 v₃ ≤ 11 v₄ < 11 v₅`; `(2,3)`: `11/13 >
    13/17`; `(3,3)`: `63/136 < 11/19`). -/
lemma bhk_s5_case51_511_no_cover_A (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hx4 : 25 * (speeds ⟨3, by omega⟩ : ℝ) < 32 * (speeds ⟨2, by omega⟩ : ℝ))
    (hA : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ))
    (hgap1 : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgap2 : ∀ s ∈ Set.Icc (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4 : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  -- `gap1 = [21/(16 v₃), 11/(6 v₄)]` lies in a single 5-block `k₁`.
  have hab1 : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h16 h6v4]; nlinarith [hx4, hv3, hv4]
  obtain hF | hsub1 := bhk_s5_case51_gap1234_subset speeds hgap1
  · exact hF
  obtain ⟨k₁, hk1L, hk1R⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))) (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ))) hab1 hsub1
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 21 * (speeds ⟨4, by omega⟩ : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h16] at hk1L
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        = 11 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h6v4] at hk1R
  -- hk1L : ((k₁:ℝ) - 1/6) * (16 v₃) < 21 v₅ ;  hk1R : 11 v₅ < ((k₁:ℝ) + 1/6) * (6 v₄)
  -- `gap2a = [13/(6 v₄), 11/(6 v₃)]` lies in a single 5-block `k₂`.
  have hab2 : (13 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h6v4 h6]; nlinarith [hA, hv3, hv4]
  obtain hF | hsub2 := bhk_s5_case51_gap1234_subset speeds hgap2
  · exact hF
  obtain ⟨k₂, hk2L, hk2R⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ))) (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) hab2 hsub2
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        = 13 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h6v4] at hk2L
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 11 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h6] at hk2R
  -- hk2L : ((k₂:ℝ) - 1/6) * (6 v₄) < 13 v₅ ;  hk2R : 11 v₅ < ((k₂:ℝ) + 1/6) * (6 v₃)
  -- `gap1` width bound: `23 v₅ < 64 v₃` (uses `x₄ > 25/32`).
  have hwidth_deg2 : 23 * (speeds ⟨4, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ)
      < 64 * (speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_right hk1L h6v4, mul_lt_mul_of_pos_right hk1R h16,
               mul_lt_mul_of_pos_right hx4 hv5, hv3, hv4, hv5]
  have hwidth1 : 23 * (speeds ⟨4, by omega⟩ : ℝ) < 64 * (speeds ⟨2, by omega⟩ : ℝ) :=
    lt_of_mul_lt_mul_right hwidth_deg2 hv4.le
  -- `k₁ ∈ {2, 3}`.
  have hk1ge2 : (2 : ℤ) ≤ k₁ := by
    by_contra h; push_neg at h
    have : (k₁ : ℝ) ≤ 1 := by exact_mod_cast (by omega : k₁ ≤ 1)
    nlinarith [hk1R, h45, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (k₁:ℝ)) hv4.le]
  have hk1le3 : k₁ ≤ (3 : ℤ) := by
    by_contra h; push_neg at h
    have hk4 : (4 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast (by omega : (4 : ℤ) ≤ k₁)
    nlinarith [hk1L, hwidth1, hv3, mul_nonneg (by linarith : (0:ℝ) ≤ (k₁:ℝ) - 4) hv3.le]
  -- `gap1`'s right end + `k₁ ≤ 3` ⟹ `11 v₅ < 19 v₄` (BHK's `19 x₅ > 11 x₄`).
  have hk1le3R : (k₁ : ℝ) ≤ 3 := by exact_mod_cast hk1le3
  have hs19 : 11 * (speeds ⟨4, by omega⟩ : ℝ) < 19 * (speeds ⟨3, by omega⟩ : ℝ) := by
    nlinarith [hk1R, hk1le3R, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ 3 - (k₁:ℝ)) hv4.le]
  -- `k₂ ∈ {2, 3}`.
  have hk2ge2 : (2 : ℤ) ≤ k₂ := by
    by_contra h; push_neg at h
    have : (k₂ : ℝ) ≤ 1 := by exact_mod_cast (by omega : k₂ ≤ 1)
    nlinarith [hk2R, h35, hv3, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (k₂:ℝ)) hv3.le]
  have hk2le3 : k₂ ≤ (3 : ℤ) := by
    by_contra h; push_neg at h
    have hk4 : (4 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast (by omega : (4 : ℤ) ≤ k₂)
    nlinarith [hk2L, hs19, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ (k₂:ℝ) - 4) hv4.le]
  -- The four `(k₁, k₂) ∈ {2,3} × {2,3}` pairs are each contradictory (linear).
  interval_cases k₁ <;> interval_cases k₂ <;>
    linarith [hk1L, hk1R, hk2L, hk2R, hA, hv3, hv4, h45]

/-- **BHK Case 5.1.1 (`k ≥ 3`, `x₁ < 14/3`).**  Covers BHK conditions 1, 3, 4
    (their `x₁`-bounds `14/3, 14/4, 17/5` all satisfy `x₁ < 14/3`).  No `l ≥ i`
    configuration exists; BHK argues directly (p. 16).

    `v₂ > 8/9` (`511_v2_lb`) makes `[21/16, 11/6]` a 123-gap (`511_gap123`), whence
    `25 v₄ < 32 v₃` (`511_x4_bound`, i.e. `x₄ > 25/32`).  Then split on the runner-4
    `k = 2` block position relative to `121/78`:
    * `13 x₄ > 11` (branch B): `gap2b = [21/16, 121/78]` is a 1234-gap runner 5
      cannot cover (`511_no_cover_B`).
    * `13 x₄ ≤ 11` (branch A): `gap1 = [21/16, (11/6)x₄]` and `gap2a = [13x₄/6, 11/6]`
      are 1234-gaps that runner 5 cannot cover simultaneously (`511_no_cover_A`),
      via BHK's `19 x₅ > 11 x₄` reconstructed as `11 v₅ < 19 v₄` (numerically
      verified, `experiments/bhk_511_endgame_verify.py`). -/
lemma bhk_s5_case51_subcase_511 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (hx1 : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 14 / 3) : Found speeds := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  have hx1R : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ) := by
    rw [div_lt_div_iff₀ hv1 (by norm_num : (0 : ℝ) < 3)] at hx1; linarith [hx1]
  have hv2lb := bhk_s5_case51_511_v2_lb speeds hmono hsmall k D hk3 hD hkD
  have hgap123 := bhk_s5_case51_511_gap123 speeds hmono hpos hv2lb hsmallR hx1R
  obtain hF | hx4 := bhk_s5_case51_511_x4_bound speeds hmono hpos hgap123
  · exact hF
  by_cases hbranch : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ)
  · -- branch A (`13 x₄ ≤ 11`)
    exact bhk_s5_case51_511_no_cover_A speeds hmono hpos hx4 hbranch
      (bhk_s5_case51_511_gap1 speeds hmono hpos hv2lb hsmallR hx1R)
      (bhk_s5_case51_511_gap2a speeds hmono hpos hv2lb hsmallR hx1R hx4)
  · -- branch B (`13 x₄ > 11`)
    push_neg at hbranch
    exact bhk_s5_case51_511_no_cover_B speeds hmono hpos
      (bhk_s5_case51_511_gap2b speeds hmono hpos hv2lb hsmallR hx1R hbranch)

/-- **Case 5.1.2, the `x₄` upper bound (`x₄ > 9/10`).**  With `k = 3` and
    `8 < x₁ < 26/3`, the eqn-(32) bounds hold for `i = 2`, `l = 1`, so
    `config_window_safe` yields the triple configuration `I₁`, `I₃` (123-gaps at
    `t₀ = (2+1/3)/v₃`); `span_l1` then gives `9 v₄ < 10 v₃`. -/
lemma bhk_s5_case51_512_x4_ub (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (k D : ℕ) (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) (hk : k = 3)
    (hx1 : 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (hx1' : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3) : Found speeds ∨
      (9 * (speeds ⟨3, by omega⟩ : ℝ) < 10 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hDc : (D : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) - (speeds ⟨1, by omega⟩ : ℝ) :=
    bhk_s5_case51_D_cast speeds hmono D hD
  have hV1 : (speeds ⟨0, by omega⟩ : ℝ) = (D : ℝ) * 3 := by rw [hkD, hk]; push_cast; ring
  rw [lt_div_iff₀ hv1] at hx1
  rw [div_lt_iff₀ hv1] at hx1'
  have hsafe := bhk_s5_case51_config_window_safe speeds hmono hpos 2 1 D hD
    (by simp only [Nat.cast_ofNat]; nlinarith [hx1', hv1])
    (by simp only [Nat.cast_ofNat, Nat.cast_one]; nlinarith [hx1, hV1, hDc])
    (by simp only [Nat.cast_ofNat, Nat.cast_one]; nlinarith [hx1])
  simp only [Nat.cast_ofNat] at hsafe
  have hgapI1 := hsafe 0 (by norm_num)
  have hgapI3 := hsafe 1 (by norm_num)
  simp only [Nat.cast_zero, zero_div, add_zero] at hgapI1
  simp only [Nat.cast_one] at hgapI3
  obtain hF | hcovI1 := bhk_prop11_gap_covered speeds hgapI1
  · exact Or.inl hF
  have h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_s5_case51_x4_from_I1 speeds hmono hpos hcovI1
  exact bhk_s5_case51_span_l1 speeds hmono hpos
    ((2 + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)) hgapI1 hgapI3 h22

/-- **Case 5.1.2, runner 5 cannot cover the gap.**  The 1234-gap `[52/(23 v₃),
    51/(20 v₃)]` (BHK `[52/23, 51/20]`), being `⊆ B₅`, lies in a single 5-block
    `[(k−1/6)/v₅, (k+1/6)/v₅]`.  Subtracting the block edges gives the width bound
    `399 v₅ < 460 v₃`; the right end then forces `k ≥ 3` (via `v₃ < v₅`) while the
    left end forces `k ≤ 2` — no such integer exists.  (Only `v₃ < v₅`, i.e.
    `x₅ < 1`, is used, not BHK's conditional `x₅ < 1/2`.) -/
lemma bhk_s5_case51_512_no_cover (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hgap : ∀ s ∈ Set.Icc (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
        (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) : Found speeds := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h23 : (0 : ℝ) < 23 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h20 : (0 : ℝ) < 20 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have hab : (52 : ℝ) / (23 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 51 / (20 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h23 h20]; nlinarith [hv3]
  obtain hF | hsub := bhk_s5_case51_gap1234_subset speeds hgap
  · exact hF
  obtain ⟨k, hkL, hkR⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ))) (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub
  have hVa : (speeds ⟨4, by omega⟩ : ℝ) * (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
      = 52 * (speeds ⟨4, by omega⟩ : ℝ) / (23 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hVb : (speeds ⟨4, by omega⟩ : ℝ) * (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ)))
      = 51 * (speeds ⟨4, by omega⟩ : ℝ) / (20 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  rw [hVa, lt_div_iff₀ h23] at hkL
  rw [hVb, div_lt_iff₀ h20] at hkR
  -- hkL : ((k:ℝ) - 1/6) * (23 v₃) < 52 v₅ ;  hkR : 51 v₅ < ((k:ℝ) + 1/6) * (20 v₃)
  have width : 399 * (speeds ⟨4, by omega⟩ : ℝ) < 460 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [hkL, hkR]
  have hk_lo : (143 : ℝ) / 3 < 20 * (k : ℝ) := by
    have step : (143 : ℝ) / 3 * (speeds ⟨2, by omega⟩ : ℝ)
        < 20 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkR, h35]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk3 : (3 : ℤ) ≤ k := by
    by_contra h; push_neg at h
    have hk2r : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
    linarith [hk_lo]
  have hk_hi : 23 * (k : ℝ) < 64 := by
    have step : 23 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 64 * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkL, width, hv3]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk2 : k ≤ (2 : ℤ) := by
    by_contra h; push_neg at h
    have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (3 : ℤ) ≤ k)
    linarith [hk_hi]
  omega

/-- **BHK Case 5.1.2 (`k = 3`, `8 < x₁ < 26/3`).**  BHK condition 2.  A triple
    configuration exists at `t = 14/6` (`l = 1`), so `x₄ > 9/10` (eqn (27),
    `span_l1`); with `v₂ > 23/24` this puts `[52/23, 51/20]` in a 1234-gap that
    runner 5 cannot cover (no `i ≥ 3` with `(i−1/6)x₅ < 52/23` and
    `(i+1/6)x₅ > 51/20`). -/
lemma bhk_s5_case51_subcase_512 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (hk : k = 3) (hx1 : 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (hx1' : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3) : Found speeds := by
  have hv2lb := bhk_s5_case51_512_v2_lb speeds hmono hpos k D hD hkD hk hx1
  obtain hF | hx4ub := bhk_s5_case51_512_x4_ub speeds hmono hpos k D hD hkD hk hx1 hx1'
  · exact hF
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  rw [lt_div_iff₀ hv1] at hx1
  rw [div_lt_iff₀ hv1] at hx1'
  have hx1hi : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 26 * (speeds ⟨0, by omega⟩ : ℝ) := by
    linarith [hx1']
  have hgap := bhk_s5_case51_512_gap1234 speeds hmono hpos hv2lb hx4ub hx1 hx1hi
  exact bhk_s5_case51_512_no_cover speeds hmono hpos hgap


/-- **BHK §5, Case 5.1** (`v₁ = k D`, `k ≥ 3`) at a named instant: Case 5.1.1, Case 5.1.2,
    or the generic configuration, each ending at the instant its lemmas name. -/
theorem bhk_s5_case51_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  -- Each branch ends at a named lonely instant (`Found speeds`).
  -- Dispatch on `x₁ = v₃/v₁` (BHK conditions 1–4 vs the generic `l ≥ i` config).
  by_cases h511 : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 14 / 3
  · -- Case 5.1.1 (covers conditions 1, 3, 4).
    exact bhk_s5_case51_subcase_511 speeds hmono hpos hsmall k D hk3 hD hkD h511
  · push_neg at h511
    by_cases h512 : k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
        ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3
    · -- Case 5.1.2 (condition 2).
      exact bhk_s5_case51_subcase_512 speeds hmono hpos hsmall k D hk3 hD hkD
        h512.1 h512.2.1 h512.2.2
    · -- Generic case: an `l ≥ i` configuration exists; `x4_incompatible` closes it.
      obtain hF | ⟨i, l, hil, h30, h33⟩ := bhk_s5_case51_config_bounds speeds hmono hpos
        hsmall k D hk3 hD hkD h511 h512
      · exact hF
      exact (bhk_s5_case51_x4_incompatible _ i l hil h30 h33).elim

/-- **BHK §5, Case 5.1.** -/
theorem bhk_s5_k_ge_3 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  -- The triple/multiple-configuration argument (BHK §5, Case 5.1) is developed in
  -- `IntLRC_6_BHK_Section5_Case51.lean`.
  bhk_s5_case51_main speeds hmono hpos hsmall k D hk3 hD hkD

/-- **Window extraction.** `circDist x ≥ 1/6` gives the fract window. -/
lemma bhk_fract_of_circDist {x : ℝ} (h : (1 : ℝ)/6 ≤ circDist x) :
    1/6 ≤ Int.fract x ∧ Int.fract x ≤ 5/6 := by
  unfold circDist at h
  refine ⟨le_trans h (min_le_left _ _), ?_⟩
  have := le_trans h (min_le_right _ _)
  linarith

/-- **The doubling window.** If `{y} ∈ [1/6, 5/6] ∖ (5/12, 7/12)` then
    `{2y} ∈ [1/3, 5/6] ∪ [1/6, 2/3]`, so `circDist (2y) ≥ 1/6`. This is the
    point of part 2 of Proposition 11: it makes the window survive the
    substitution `v₁ ↦ v₁/2`. -/
lemma bhk_s5_double_window (y : ℝ) (h1 : 1/6 ≤ Int.fract y)
    (h2 : Int.fract y ≤ 5/6)
    (h3 : Int.fract y ∉ Set.Ioo (5/12 : ℝ) (7/12)) :
    (1 : ℝ)/6 ≤ circDist (2 * y) := by
  have hsplit : Int.fract (2 * y) = Int.fract (2 * Int.fract y) := by
    conv_lhs => rw [← Int.fract_add_floor y]
    rw [show 2 * (Int.fract y + (⌊y⌋ : ℝ))
          = 2 * Int.fract y + ((2 * ⌊y⌋ : ℤ) : ℝ) from by push_cast; ring,
        Int.fract_add_intCast]
  simp only [Set.mem_Ioo, not_and_or, not_lt] at h3
  unfold circDist
  rw [hsplit]
  rcases h3 with h3 | h3
  · -- `{y} ≤ 5/12`: `{2{y}} = 2{y} ∈ [1/3, 5/6]`.
    have hf : Int.fract (2 * Int.fract y) = 2 * Int.fract y :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf]
    exact le_min (by linarith) (by linarith)
  · -- `{y} ≥ 7/12`: `{2{y}} = 2{y} - 1 ∈ [1/6, 2/3]`.
    have hf : Int.fract (2 * Int.fract y) = 2 * Int.fract y - 1 := by
      conv_lhs => rw [show 2 * Int.fract y
            = (2 * Int.fract y - 1) + ((1 : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf]
    exact le_min (by linarith) (by linarith)

/-- **BHK §5 dispatcher (PROVED).** `{v₁ t₀} = 0` means `D ∣ v₁`
    (`D := v₃ - v₂`); write `v₁ = k·D` and dispatch on `k`:

    * `k = 1`: `v₁ + v₂ = v₃` — Proposition 11 part 1 applies directly;
    * `k = 2`: Proposition 11 part 2 applied to `(D, v₂, v₃, v₄, v₅)`
      (note `6D = 3v₁ < v₃`), then the doubling window recovers runner 1;
    * `k ≥ 3`: Case 5.1. -/
theorem bhk_s5_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V2 : ℕ := speeds ⟨1, by omega⟩ with hV2_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hV12 : V1 < V2 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV23 : V2 < V3 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV1pos : 0 < V1 := hpos _
  set D : ℕ := V3 - V2 with hD_def
  have hDpos : 0 < D := by omega
  have hD_cast : ((D : ℕ) : ℝ) = (V3 : ℝ) - V2 := by
    rw [hD_def, Nat.cast_sub hV23.le]
  -- `D ∣ V1` from the fract-zero hypothesis.
  have hdvd : D ∣ V1 := by
    have h0 : Int.fract ((V1 : ℝ) / D) = 0 := by
      rw [show (V1 : ℝ) / D = (V1 : ℝ) * (1 / ((V3 : ℝ) - V2)) from by
        rw [← hD_cast]; ring]
      exact ht0
    exact (bhk_fract_nat_div_eq_zero_iff V1 D hDpos).mp h0
  obtain ⟨k, hkD⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, mul_zero] at hkD; omega
    · exact h
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · -- `k = 1`: `v₁ + v₂ = v₃`.
    have hsum : V1 + V2 = V3 := by omega
    exact bhk_prop11_part1 speeds hmono hpos hsum hsmall
  · -- `k = 2`: halve the first speed.
    set w : Fin 5 → ℕ := fun i => if i.val = 0 then D else speeds i with hw_def
    have hw0 : w ⟨0, by omega⟩ = D := rfl
    have hw_ne : ∀ i : Fin 5, i.val ≠ 0 → w i = speeds i := by
      intro i hi
      show (if i.val = 0 then D else speeds i) = speeds i
      exact if_neg hi
    have hDV2 : D < V2 := by omega
    have hwmono : StrictMono w := by
      intro i j hij
      have hij' : i.val < j.val := Fin.lt_def.mp hij
      by_cases hi : i.val = 0
      · have hj : j.val ≠ 0 := by omega
        have hwi : w i = D := by
          show (if i.val = 0 then D else speeds i) = D
          exact if_pos hi
        have h1j : (⟨1, by omega⟩ : Fin 5) ≤ j :=
          Fin.le_def.mpr (show 1 ≤ j.val by omega)
        rw [hwi, hw_ne j hj]
        exact lt_of_lt_of_le hDV2 (hmono.monotone h1j)
      · have hj : j.val ≠ 0 := by omega
        rw [hw_ne i hi, hw_ne j hj]
        exact hmono hij
    have hwpos : ∀ i, 0 < w i := by
      intro i
      by_cases hi : i.val = 0
      · have hwi : w i = D := by
          show (if i.val = 0 then D else speeds i) = D
          exact if_pos hi
        rw [hwi]
        exact hDpos
      · rw [hw_ne i hi]
        exact hpos i
    have hwsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩ := by
      have h1 : w ⟨1, by omega⟩ = V2 := hw_ne ⟨1, by omega⟩ (by norm_num)
      have h2 : w ⟨2, by omega⟩ = V3 := hw_ne ⟨2, by omega⟩ (by norm_num)
      rw [hw0, h1, h2]
      omega
    have hwsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by
      have h2 : w ⟨2, by omega⟩ = V3 := hw_ne ⟨2, by omega⟩ (by norm_num)
      rw [hw0, h2]
      omega
    obtain ⟨t, hwin, hfr⟩ := bhk_prop11_part2 w hwmono hwpos hwsum hwsmall6
    refine ⟨t, fun i => ?_⟩
    by_cases hi : i.val = 0
    · -- runner 1: `v₁ = 2D`, use the doubling window.
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      obtain ⟨hf1, hf2⟩ := bhk_fract_of_circDist (hwin ⟨0, by omega⟩)
      rw [hw0] at hf1 hf2
      have hfr' : Int.fract ((D : ℝ) * t) ∉ Set.Ioo (5/12 : ℝ) (7/12) := by
        rw [← hw0]
        exact hfr
      have hdouble := bhk_s5_double_window ((D : ℝ) * t) hf1 hf2 hfr'
      have hcast : ((speeds i : ℕ) : ℝ) * t = 2 * ((D : ℝ) * t) := by
        rw [hi_eq, ← hV1_def, hkD]
        push_cast
        ring
      rw [hcast]
      exact hdouble
    · rw [show ((speeds i : ℕ) : ℝ) = ((w i : ℕ) : ℝ) from by rw [hw_ne i hi]]
      exact hwin i
  · -- `k ≥ 3`: Case 5.1.
    exact bhk_s5_k_ge_3 speeds hmono hpos hsmall k D hk3 hD_def hkD


/-- **BHK §5 in the framework** (`3v₁ < v₃`, `D = v₃ − v₂` divides `v₁`): five whole-number
disparities are lonely at `1/6`. -/
theorem lonely_5 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hD1 : (v3 - v2) ∣ v1) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  set speeds : Fin 5 → ℕ := ![v1, v2, v3, v4, v5] with hs
  have hmono : StrictMono speeds := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hs] <;> omega
  have hpos : ∀ i, 0 < speeds i := by intro i; fin_cases i <;> simp [hs] <;> omega
  have hD : 0 < v3 - v2 := by omega
  have hDR : ((v3 : ℝ) - v2) = ((v3 - v2 : ℕ) : ℝ) := by rw [Nat.cast_sub h23.le]
  have ht0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
      (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0 := by
    show Int.fract ((v1 : ℝ) * (1 / ((v3 : ℝ) - (v2 : ℝ)))) = 0
    rw [hDR, show (v1 : ℝ) * (1 / ((v3 - v2 : ℕ) : ℝ)) = (v1 : ℝ) / ((v3 - v2 : ℕ) : ℝ) by ring]
    exact (bhk_fract_nat_div_eq_zero_iff v1 _ hD).mpr hD1
  obtain ⟨t, ht, hl⟩ := exists_pos_of_lonely speeds hpos
    (bhk_s5_main speeds hmono hpos (by simpa [hs] using hsmall) ht0)
  exact ⟨t, ht, by simpa [hs] using hl 0, by simpa [hs] using hl 1, by simpa [hs] using hl 2,
    by simpa [hs] using hl 3, by simpa [hs] using hl 4⟩

end LRC.OrderSixN.S7.Named
