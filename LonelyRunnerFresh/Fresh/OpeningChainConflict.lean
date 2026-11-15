import Fresh.ChainDomPerRecStart
import Fresh.PinnedCarveChain
import Fresh.WordCoverSide

namespace Fresh

open CapChainsOfCarve ChainDomPerRec8 FilterAssembly
  JoinFamComposed OneSidedComposed UClosure WordCoverSide

/-- At a setter's opening, a reading still in its blocked zone supplies a
strict demand. The laps may coincide. A record can use any weaker demand
with the same two reading indices. -/
theorem openingDemand_of_dominated_ratio {g : Fin 7 → ℝ} {e : ComposedEdge}
    {j k : ℕ} {R : ℝ} (hx : 0 < g e.x) (hy : 0 < g e.y)
    (hk : 1 ≤ k)
    (hopen : g e.x * R = (j : ℝ) * 8 + 1) (hblock : inZone g e.y k R)
    (hdom : ((j : ℝ) * 8 + 1) / ((k : ℝ) * 8 - 1) ≤ (e.A : ℝ) / (e.B : ℝ)) :
    g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) * 8 - 1 := by linarith
  have hleft := mul_lt_mul_of_pos_right hblock.1 hx
  have hright := congrArg (fun z : ℝ => z * g e.y) hopen
  have hratio :
      g e.x / g e.y < ((j : ℝ) * 8 + 1) / ((k : ℝ) * 8 - 1) := by
    apply (div_lt_div_iff₀ hy hden).mpr
    linarith only [hleft, hright]
  exact hratio.trans_le hdom

/-- A single record closes the conflict when its demand and its own
attesting walk occur on the same arrangement. -/
theorem composedFamily_conflict_of_admitted_record {g : Fin 7 → ℝ} {f : ComposedFam}
    (hf : ComposedFamData f) (hpos : ∀ i, 0 < g i)
    {e : ComposedEdge} (he : e ∈ f.edges)
    (hdemand : g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ))
    {U : UTable} {steps : List Step} (hfine : UFine g U)
    (hwalk : ChainRealized g U 0 1 steps) (hattest : AttestsFrom e steps U) :
    False := by
  obtain ⟨V, a, A, hrun, hfine', _⟩ := chain_fine_of_realized hpos hfine hwalk
  have hchain := chainReal_of_capsDom hpos hfine' (hattest V a A hrun)
  exact composedFamRefutes hf ⟨e, he, hpos e.x, hpos e.y, hdemand, hchain⟩

/-- For a surviving pinned box, use the actual first-window chain.
The remaining selection is a second-window opening with a matching
record that the first-window chain attests. -/
theorem twoWindows_of_select_opening_record {b : Fin 7 → ℤ}
    (hb : b ∈ coveredSet) (hn17 : ∀ i, b i ≤ 17)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hpin : g 0 = 1) {U : UTable} (hfine : UFine g U)
    (select : (¬ ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
      ∀ (i : Fin 7) (j₀ : Fin 16) (rest : List Step),
        ChainRealized g U 0 1 (⟨i, zEntry j₀, zExit j₀⟩ :: rest) →
        EnvChain i (zExit j₀) rest →
        ∃ (e : ComposedEdge) (j k : ℕ) (R : ℝ),
          e ∈ (compFamOf b).edges ∧ AttestsFrom e (⟨i, zEntry j₀, zExit j₀⟩ :: rest) U ∧
          9 ≤ R ∧ R ≤ 15 ∧ 1 ≤ k ∧
          g e.x * R = (j : ℝ) * 8 + 1 ∧ inZone g e.y k R ∧
          ((j : ℝ) * 8 + 1) / ((k : ℝ) * 8 - 1) ≤ (e.A : ℝ) / (e.B : ℝ)) :
    ∃ s, ((1 ≤ s ∧ s ≤ 7) ∨ (9 ≤ s ∧ s ≤ 15)) ∧
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  classical
  by_cases h₀ : ∃ s, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))
  · obtain ⟨s, hl, hh, h⟩ := h₀
    exact ⟨s, Or.inl ⟨hl, hh⟩, h⟩
  by_cases h₁ : ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))
  · obtain ⟨s, hl, hh, h⟩ := h₁
    exact ⟨s, Or.inr ⟨hl, hh⟩, h⟩
  obtain ⟨i, j₀, _, rest, _, _, hw, _, henv, _⟩ := pinnedCarve_chain hn17 hface hpin hfine h₀
  obtain ⟨e, j, k, R, he, ha, _, _, hk, ho, hbl, hd⟩ := select h₁ i j₀ rest hw henv
  have hp (i : Fin 7) : 0 < g i :=
    zero_lt_one.trans_le ((faceLo_ge_one b i).trans (hface i).1)
  have hdem := openingDemand_of_dominated_ratio (hp e.x) (hp e.y) hk ho hbl hd
  exact (composedFamily_conflict_of_admitted_record (oneSidedTotalData b hb) hp he
    hdem hfine hw ha).elim

#print axioms openingDemand_of_dominated_ratio
#print axioms composedFamily_conflict_of_admitted_record
#print axioms twoWindows_of_select_opening_record

end Fresh
