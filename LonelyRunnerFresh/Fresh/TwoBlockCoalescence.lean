import Fresh.TwoAPSeparated21
import Fresh.TwoSixThin
import Fresh.MixedStepFourLowerArrangement
import Fresh.UniformStepFourArrangement
import Fresh.MiddleStepFiveArrangementAll
import Fresh.FullThreeFiveArrangement

/-! Coalescence of the two-block alternatives of the 2026-10-26 catalogue (log E646).
Nine alternatives (`SeparatedTwoAP21Class`, `TwoSixNineClass`, `TwoSixThinClass`, `FullThreeFiveArrangementClass`,
`MiddleFiveAllArrangementClass`, `MixedFourTwoArrangementClass`, `MixedFourParamArrangementClass`,
`MixedFourLowerArrangementClass`, `UniformFourArrangementClass`) are one template up to scale, drift, mirror and labels:
two AP blocks `c, c+1, …, c+(p-1)` and `c+A, c+A+b, …, c+A+(7-p) b` (`UnequalAPArrangement.speeds c A 1 b p`).
Each is a region of the parameters `(p, A, b)`. `TwoBlockRegion` is the union of the nine regions; `TwoBlockClass`
is the template over that union, and `twoBlock_iff` proves it is exactly the disjunction of the nine classes.
The inclusions between the regions are proved below.
-/
namespace Fresh.TwoBlockCoalescence
open Fresh Fresh.UnequalAPArrangement

/-- The union of the nine parameter regions (step of the first block normalised to 1). -/
-- STANDING: DEFINITION
def TwoBlockRegion (p : ℕ) (A b : ℝ) : Prop :=
  (2 ≤ p ∧ p ≤ 6 ∧ 21*max (1 : ℝ) b ≤ A-((p : ℝ)-1)) ∨
  (p = 2 ∧ 9*max 1 b ≤ A-1) ∨
  (p = 2 ∧ 4 ≤ 3*(A-1) ∧ 40*b ≤ (A-1)*(6-5*b)) ∨
  (p = 3 ∧ (32/3 : ℝ)*max (1 : ℝ) b ≤ A-2) ∨
  (p = 3 ∧ (6/7 : ℝ) ≤ b ∧ 32*b ≤ 3*(A-2)) ∨
  (p = 4 ∧ b = 2 ∧ (51/4 : ℝ) ≤ A-3) ∨
  (p = 4 ∧ 2 ≤ b ∧ 0<A-3 ∧ 9*b^2 ≤ (A-3)*(8-3*b)) ∨
  (p = 4 ∧ (8/7 : ℝ) ≤ b ∧ b ≤ 2 ∧ 9*b ≤ A-3)

-- STANDING: DEFINITION
def TwoBlockClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    0 < b ∧ s ≠ 0 ∧ TwoBlockRegion p A b ∧
    V = (fun i => B+s*speeds c A 1 b p (σ i))

-- STANDING: DEFINITION
def NineClasses (V : Fin 8 → ℝ) : Prop :=
  Fresh.TwoAPSeparated21.SeparatedTwoAP21Class V ∨
  Fresh.TwoSixNine.TwoSixNineClass V ∨
  Fresh.TwoSixThin.TwoSixThinClass V ∨
  Fresh.FullThreeFiveArrangement.FullThreeFiveArrangementClass V ∨
  Fresh.MiddleStepFiveArrangementAll.MiddleFiveAllArrangementClass V ∨
  Fresh.MixedStepFourArrangement.MixedFourTwoArrangementClass V ∨
  Fresh.MixedStepFourParamArrangement.MixedFourParamArrangementClass V ∨
  Fresh.MixedStepFourLowerArrangement.MixedFourLowerArrangementClass V ∨
  Fresh.UniformStepFourArrangement.UniformFourArrangementClass V

theorem nine_imp_twoBlock {V : Fin 8 → ℝ} (h : NineClasses V) : TwoBlockClass V := by
  rcases h with h|h|h|h|h|h|h|h|h
  · obtain ⟨hp,hi,c,A,b,B,s,p,σ,hp2,hp6,hb,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,p,σ,hb,hs,Or.inl ⟨hp2,hp6,hg⟩,hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,2,σ,hb,hs,Or.inr (Or.inl ⟨rfl,hg⟩),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,h1,h2,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,2,σ,hb,hs,Or.inr (Or.inr (Or.inl ⟨rfl,h1,h2⟩)),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,3,σ,hb,hs,Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,hg⟩))),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,3,σ,by linarith,hs,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,hb,hg⟩)))),hV⟩
  · obtain ⟨hp,hi,c,A,B,s,σ,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,2,B,s,4,σ,by norm_num,hs,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hg⟩))))),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,hA,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,4,σ,by linarith,hs,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,hb,hA,hg⟩)))))),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb1,hb2,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,4,σ,by linarith,hs,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,hb1,hb2,hg⟩)))))),hV⟩
  · obtain ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩ := h
    exact ⟨hp,hi,c,A,b,B,s,4,σ,hb,hs,Or.inl ⟨by norm_num,by norm_num,by norm_num; linarith⟩,hV⟩

theorem twoBlock_imp_nine {V : Fin 8 → ℝ} (h : TwoBlockClass V) : NineClasses V := by
  obtain ⟨hp,hi,c,A,b,B,s,p,σ,hb,hs,hR,hV⟩ := h
  rcases hR with ⟨hp2,hp6,hg⟩|⟨rfl,hg⟩|⟨rfl,h1,h2⟩|⟨rfl,hg⟩|⟨rfl,hb1,hg⟩|⟨rfl,rfl,hg⟩|⟨rfl,hb1,hA,hg⟩|⟨rfl,hb1,hb2,hg⟩
  · exact Or.inl ⟨hp,hi,c,A,b,B,s,p,σ,hp2,hp6,hb,hg,hs,hV⟩
  · exact Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb,h1,h2,hs,hV⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb,by norm_num at hg ⊢; linarith,hs,hV⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb1,hg,hs,hV⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,B,s,σ,hg,hs,hV⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb1,hA,hg,hs,hV⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp,hi,c,A,b,B,s,σ,hb1,hb2,hg,hs,hV⟩)))))))

theorem twoBlock_iff {V : Fin 8 → ℝ} : TwoBlockClass V ↔ NineClasses V :=
  ⟨twoBlock_imp_nine, nine_imp_twoBlock⟩

theorem twoBlock_isolation {V : Fin 8 → ℝ} (h : TwoBlockClass V) (k : Fin 8) : Isolation V k := by
  rcases twoBlock_imp_nine h with h|h|h|h|h|h|h|h|h
  · exact Fresh.TwoAPSeparated21.separatedTwoAP21_isolation h k
  · exact Fresh.TwoSixNine.twoSixNine_isolation h k
  · exact Fresh.TwoSixThin.twoSixThin_isolation h k
  · exact Fresh.FullThreeFiveArrangement.fullThreeFiveArrangement_isolation h k
  · exact Fresh.MiddleStepFiveArrangementAll.middleFiveAllArrangement_isolation h k
  · exact Fresh.MixedStepFourArrangement.mixedFourTwoArrangement_isolation h k
  · exact Fresh.MixedStepFourParamArrangement.mixedFourParamArrangement_isolation h k
  · exact Fresh.MixedStepFourLowerArrangement.mixedFourLowerArrangement_isolation h k
  · exact Fresh.UniformStepFourArrangement.uniformFourArrangement_isolation h k

/-! Intersections of the regions. -/

theorem uniformFour_iff_separated_four {V : Fin 8 → ℝ} :
    Fresh.UniformStepFourArrangement.UniformFourArrangementClass V ↔
    ((∀ i, 0 < V i) ∧ Function.Injective V ∧
      ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
        0 < b ∧ 21*max (1 : ℝ) b ≤ A-((4 : ℕ) - (1 : ℝ)) ∧ s ≠ 0 ∧
        V=(fun i => B+s*speeds c A 1 b 4 (σ i))) := by
  constructor
  · rintro ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩
    exact ⟨hp,hi,c,A,b,B,s,σ,hb,by norm_num; linarith,hs,hV⟩
  · rintro ⟨hp,hi,c,A,b,B,s,σ,hb,hg,hs,hV⟩
    exact ⟨hp,hi,c,A,b,B,s,σ,hb,by norm_num at hg; linarith,hs,hV⟩

theorem separated_two_imp_twoSixNine {V : Fin 8 → ℝ}
    (h : Fresh.TwoAPSeparated21.SeparatedTwoAP21Class V)
    (hp : ∀ (c A b B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)), V = (fun i => B+s*speeds c A 1 b p (σ i)) →
      21*max (1 : ℝ) b ≤ A-((p : ℝ)-1) → p = 2) :
    Fresh.TwoSixNine.TwoSixNineClass V := by
  obtain ⟨hpos,hi,c,A,b,B,s,p,σ,hp2,hp6,hb,hg,hs,hV⟩ := h
  have h2 := hp c A b B s p σ hV hg
  subst h2
  have hm : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  exact ⟨hpos,hi,c,A,b,B,s,σ,hb,by norm_num at hg; linarith,hs,hV⟩

theorem separated_three_imp_fullThreeFive {V : Fin 8 → ℝ}
    (h : Fresh.TwoAPSeparated21.SeparatedTwoAP21Class V)
    (hp : ∀ (c A b B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)), V = (fun i => B+s*speeds c A 1 b p (σ i)) →
      21*max (1 : ℝ) b ≤ A-((p : ℝ)-1) → p = 3) :
    Fresh.FullThreeFiveArrangement.FullThreeFiveArrangementClass V := by
  obtain ⟨hpos,hi,c,A,b,B,s,p,σ,hp2,hp6,hb,hg,hs,hV⟩ := h
  have h3 := hp c A b B s p σ hV hg
  subst h3
  have hm : (1 : ℝ) ≤ max 1 b := le_max_left _ _
  exact ⟨hpos,hi,c,A,b,B,s,σ,hb,by norm_num at hg; linarith,hs,hV⟩

/-- For `b ≥ 6/7` the full three-five region lies inside the middle-five region. -/
theorem fullThreeFive_imp_middleFive {V : Fin 8 → ℝ}
    (h : Fresh.FullThreeFiveArrangement.FullThreeFiveArrangementClass V)
    (hb : ∀ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)), V = (fun i => B+s*speeds c A 1 b 3 (σ i)) → (6/7 : ℝ) ≤ b) :
    Fresh.MiddleStepFiveArrangementAll.MiddleFiveAllArrangementClass V := by
  obtain ⟨hpos,hi,c,A,b,B,s,σ,hb0,hg,hs,hV⟩ := h
  have hbm : b ≤ max 1 b := le_max_right _ _
  exact ⟨hpos,hi,c,A,b,B,s,σ,hb c A b B s σ hV,by nlinarith,hs,hV⟩

/-- On `8/7 ≤ b ≤ 2` the uniform four-four region lies inside the lower mixed region. -/
theorem uniformFour_imp_mixedLower {V : Fin 8 → ℝ}
    (h : Fresh.UniformStepFourArrangement.UniformFourArrangementClass V)
    (hb : ∀ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)), V = (fun i => B+s*speeds c A 1 b 4 (σ i)) → (8/7 : ℝ) ≤ b ∧ b ≤ 2) :
    Fresh.MixedStepFourLowerArrangement.MixedFourLowerArrangementClass V := by
  obtain ⟨hpos,hi,c,A,b,B,s,σ,hb0,hg,hs,hV⟩ := h
  obtain ⟨h1,h2⟩ := hb c A b B s σ hV
  have hbm : b ≤ max 1 b := le_max_right _ _
  exact ⟨hpos,hi,c,A,b,B,s,σ,h1,h2,by nlinarith,hs,hV⟩

#print axioms twoBlock_iff
#print axioms twoBlock_isolation
#print axioms uniformFour_iff_separated_four
#print axioms separated_two_imp_twoSixNine
#print axioms separated_three_imp_fullThreeFive
#print axioms fullThreeFive_imp_middleFive
#print axioms uniformFour_imp_mixedLower
end Fresh.TwoBlockCoalescence
