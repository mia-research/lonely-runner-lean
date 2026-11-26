import Fresh.FourPairStepPerturbedBounds

/-! Rules:1–4,8–18. Native frozen-pair resumption under the original real
far-pair deformationρ∈[0,κ]. Captures and openings are derived at U,VP,WP;
every frozen core reading and the moved reading is retained, not assumed. -/
open Classical
namespace Fresh.FourPairStepPerturbedEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds
  Fresh.FourPairStepPerturbedBounds

theorem at_U_perturbed (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    LonelyAt (core g m σ) (U m κ) ∧
    (1/8 : ℝ) ≤ distInt (moved m κ*U m κ) ∧
    (1/8 : ℝ) ≤ distInt (slow m ρ*U m κ) ∧ InWay (fast m ρ) (U m κ) ∧
    nextOpening (fast m ρ) (U m κ)=VP m ρ := by
  obtain ⟨hcU,hdU,_,_,_⟩ := Fresh.FourPairStepEpisode.at_U g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1
  obtain ⟨hTU,hUmax,hUV,hVW⟩ := opening_bounds m hm κ hκ0 hκ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U]; field_simp
  have hdiff : moved m κ*(U m κ-T m)=κ/8 := by nlinarith
  have hprod := mul_lt_mul_of_pos_right (by linarith : moved m κ < fast m ρ) (sub_pos.mpr hTU)
  have haBound := mul_le_mul_of_nonneg_left hUmax (by linarith : 0 ≤ slow m ρ)
  have hfBound := mul_le_mul_of_nonneg_left hUmax (by linarith : 0 ≤ fast m ρ)
  have haclear : (1/8 : ℝ) ≤ distInt (slow m ρ*U m κ) := by
    apply clear_of_window (6*m) <;> push_cast <;> nlinarith
  have habs : |fast m ρ*U m κ-((7*m+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  have hfway : InWay (fast m ρ) (U m κ) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (7*m+1)) habs
  refine ⟨hcU,hdU,haclear,hfway,?_⟩
  rw [nextOpening_eq habs]
  dsimp [VP]
  push_cast
  ring

theorem at_VP (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    LonelyAt (core g m σ) (VP m ρ) ∧
    (1/8 : ℝ) ≤ distInt (moved m κ*VP m ρ) ∧
    (1/8 : ℝ) ≤ distInt (fast m ρ*VP m ρ) ∧ InWay (slow m ρ) (VP m ρ) ∧
    nextOpening (slow m ρ) (VP m ρ)=WP m ρ := by
  obtain ⟨hVlo,hVhi,hWlo,hWhi,hVW⟩ := perturbed_opening_bounds m hm κ ρ hκ1 hρ0 hρκ
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hTV : T m ≤ V m := by dsimp [T,V]; linarith
  have hupper : VP m ρ ≤ W m+1/128 := hVW.le.trans hWhi
  have hc := core_retained_extended g m hm hg he1 he2 σ hσ0 hσ1 (VP m ρ) (hTV.trans hVlo) hupper
  have hd := moved_retained_extended m hm κ hκ0 hκ1 (VP m ρ) hVlo hupper
  have hFVP : fast m ρ*VP m ρ=7*(m : ℝ)+9/8 := by dsimp [VP]; field_simp
  have hAVP : slow m ρ*VP m ρ=7*(m : ℝ)+9/8-VP m ρ := by
    have he : slow m ρ=fast m ρ-1 := by linarith
    rw [he,sub_mul,hFVP,one_mul]
  have hfclear : (1/8 : ℝ) ≤ distInt (fast m ρ*VP m ρ) := by
    apply clear_of_window (7*m+1) <;> push_cast <;> nlinarith
  have habs : |slow m ρ*VP m ρ-((6*m+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    dsimp [V] at hVlo hVhi
    constructor <;> nlinarith
  have haway : InWay (slow m ρ) (VP m ρ) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (6*m+1)) habs
  refine ⟨hc,hd,hfclear,haway,?_⟩
  rw [nextOpening_eq habs]
  dsimp [WP]
  push_cast
  ring

theorem at_WP (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    LonelyAt (readingsP g m κ σ ρ) (WP m ρ) := by
  obtain ⟨hVlo,hVhi,hWlo,hWhi,hVW⟩ := perturbed_opening_bounds m hm κ ρ hκ1 hρ0 hρκ
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hTW : T m ≤ W m := by dsimp [T,W]; linarith
  have hVW0 : V m ≤ W m := by dsimp [V,W]; linarith
  have hc := core_retained_extended g m hm hg he1 he2 σ hσ0 hσ1 (WP m ρ) (hTW.trans hWlo) hWhi
  have hd := moved_retained_extended m hm κ hκ0 hκ1 (WP m ρ) (hVW0.trans hWlo) hWhi
  have hAWP : slow m ρ*WP m ρ=6*(m : ℝ)+9/8 := by dsimp [WP]; field_simp
  have hFWP : fast m ρ*WP m ρ=6*(m : ℝ)+9/8+WP m ρ := by rw [hfa,add_mul,hAWP,one_mul]
  have haclear : (1/8 : ℝ) ≤ distInt (slow m ρ*WP m ρ) := by
    apply clear_of_window (6*m+1) <;> push_cast <;> nlinarith
  have hfclear : (1/8 : ℝ) ≤ distInt (fast m ρ*WP m ρ) := by
    apply clear_of_window (7*m+1) <;> push_cast <;> dsimp [W] at hWlo hWhi <;> nlinarith
  intro d hmem
  simp only [readingsP,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hmem
  rcases hmem with rfl|hmem|rfl|rfl
  · exact hd
  · exact hc d hmem
  · exact haclear
  · exact hfclear

theorem perturbed_native_pair_episode (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    IsMove (readingsP g m κ σ ρ) (U m κ) (VP m ρ) ∧
    IsMove (readingsP g m κ σ ρ) (VP m ρ) (WP m ρ) ∧ LonelyAt (readingsP g m κ σ ρ) (WP m ρ) := by
  obtain ⟨hcU,hdU,haU,hwF,hopF⟩ := at_U_perturbed g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  obtain ⟨hcV,hdV,hfV,hwA,hopA⟩ := at_VP g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  refine ⟨?_,?_,at_WP g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ⟩
  · refine Or.inr ⟨fast m ρ,by simp [readingsP],hwF,hopF.symm,?_⟩
    intro d hd hw
    simp only [readingsP,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|hd|rfl|rfl
    · exact False.elim ((not_lt_of_ge hdU) hw)
    · exact False.elim ((not_lt_of_ge (hcU d hd)) hw)
    · exact False.elim ((not_lt_of_ge haU) hw)
    · exact hopF.le
  · refine Or.inr ⟨slow m ρ,by simp [readingsP],hwA,hopA.symm,?_⟩
    intro d hd hw
    simp only [readingsP,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|hd|rfl|rfl
    · exact False.elim ((not_lt_of_ge hdV) hw)
    · exact False.elim ((not_lt_of_ge (hcV d hd)) hw)
    · exact hopA.le
    · exact False.elim ((not_lt_of_ge hfV) hw)

#print axioms at_U_perturbed
#print axioms at_VP
#print axioms at_WP
#print axioms perturbed_native_pair_episode
end Fresh.FourPairStepPerturbedEpisode
