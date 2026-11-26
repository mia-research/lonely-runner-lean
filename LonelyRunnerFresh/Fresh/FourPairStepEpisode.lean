import Fresh.FourPairStepBounds

/-! Rules:1–4,8–18. Native fast-pair resumption after an internally moved
reading. Existing FastPairResumptionN's fast→slow retained-pair argument
was source-inspected; this fresh proof checks the exact6,7 AP laps in the
current native IsMove relation. Every retained core reading is derived. -/
open Classical
namespace Fresh.FourPairStepEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds

theorem at_U (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    LonelyAt (core g m σ) (U m κ) ∧
    (1/8 : ℝ) ≤ distInt (moved m κ*U m κ) ∧
    (1/8 : ℝ) ≤ distInt (6*U m κ) ∧ InWay 7 (U m κ) ∧
    nextOpening 7 (U m κ)=V m := by
  obtain ⟨hTU,hUmax,hUV,hVW⟩ := opening_bounds m hm κ hκ0 hκ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U]; field_simp
  have hcore := core_retained g m hm hg he1 he2 σ hσ0 hσ1 (U m κ) hTU.le (hUV.le.trans hVW.le)
  have hDclear : (1/8 : ℝ) ≤ distInt (moved m κ*U m κ) := by
    apply clear_of_window (2*m+1) <;> push_cast <;> nlinarith
  have h6clear : (1/8 : ℝ) ≤ distInt (6*U m κ) := by
    apply clear_of_window (6*m) <;> push_cast <;> dsimp [T] at * <;> linarith
  have habs : |(7 : ℝ)*U m κ-((7*m+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    dsimp [T] at *
    constructor <;> linarith
  have h7way : InWay 7 (U m κ) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (7*m+1)) habs
  refine ⟨hcore,hDclear,h6clear,h7way,?_⟩
  rw [nextOpening_eq habs]
  dsimp [V]
  push_cast
  ring

theorem at_V (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    LonelyAt (core g m σ) (V m) ∧
    (1/8 : ℝ) ≤ distInt (moved m κ*V m) ∧
    (1/8 : ℝ) ≤ distInt (7*V m) ∧ InWay 6 (V m) ∧ nextOpening 6 (V m)=W m := by
  have hTV : T m ≤ V m := by dsimp [T,V]; linarith
  have hVW : V m ≤ W m := by dsimp [V,W]; linarith
  have hcore := core_retained g m hm hg he1 he2 σ hσ0 hσ1 (V m) hTV hVW
  have hDclear := moved_retained m hm κ hκ0 hκ1 (V m) le_rfl hVW
  have h7clear : (1/8 : ℝ) ≤ distInt (7*V m) := by
    apply clear_of_window (7*m+1) <;> push_cast <;> dsimp [V] <;> linarith
  have habs : |(6 : ℝ)*V m-((6*m+1 : ℤ) : ℝ)| < 1/8 := by
    have he : (6 : ℝ)*V m-((6*m+1 : ℤ) : ℝ)= -1/28 := by dsimp [V]; push_cast; ring
    rw [he]
    norm_num
  have h6way : InWay 6 (V m) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (6*m+1)) habs
  refine ⟨hcore,hDclear,h7clear,h6way,?_⟩
  rw [nextOpening_eq habs]
  dsimp [W]
  push_cast
  ring

theorem at_W (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    LonelyAt (readings g m κ σ) (W m) := by
  have hTW : T m ≤ W m := by dsimp [T,W]; linarith
  have hVW : V m ≤ W m := by dsimp [V,W]; linarith
  have hcore := core_retained g m hm hg he1 he2 σ hσ0 hσ1 (W m) hTW le_rfl
  have hDclear := moved_retained m hm κ hκ0 hκ1 (W m) hVW le_rfl
  have h6clear : (1/8 : ℝ) ≤ distInt (6*W m) := by
    apply clear_of_window (6*m+1) <;> push_cast <;> dsimp [W] <;> linarith
  have h7clear : (1/8 : ℝ) ≤ distInt (7*W m) := by
    apply clear_of_window (7*m+1) <;> push_cast <;> dsimp [W] <;> linarith
  intro d hd
  simp only [readings,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
  rcases hd with rfl|hd|rfl|rfl
  · exact hDclear
  · exact hcore d hd
  · exact h6clear
  · exact h7clear

theorem native_pair_episode (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    IsMove (readings g m κ σ) (U m κ) (V m) ∧
    IsMove (readings g m κ σ) (V m) (W m) ∧ LonelyAt (readings g m κ σ) (W m) := by
  obtain ⟨hcU,hdU,h6U,hw7,hop7⟩ := at_U g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1
  obtain ⟨hcV,hdV,h7V,hw6,hop6⟩ := at_V g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1
  refine ⟨?_,?_,at_W g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1⟩
  · refine Or.inr ⟨7,by simp [readings],hw7,hop7.symm,?_⟩
    intro d hd hw
    simp only [readings,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|hd|rfl|rfl
    · exact False.elim ((not_lt_of_ge hdU) hw)
    · exact False.elim ((not_lt_of_ge (hcU d hd)) hw)
    · exact False.elim ((not_lt_of_ge h6U) hw)
    · exact hop7.le
  · refine Or.inr ⟨6,by simp [readings],hw6,hop6.symm,?_⟩
    intro d hd hw
    simp only [readings,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|hd|rfl|rfl
    · exact False.elim ((not_lt_of_ge hdV) hw)
    · exact False.elim ((not_lt_of_ge (hcV d hd)) hw)
    · exact hop6.le
    · exact False.elim ((not_lt_of_ge h7V) hw)

#print axioms at_U
#print axioms at_V
#print axioms at_W
#print axioms native_pair_episode
end Fresh.FourPairStepEpisode
