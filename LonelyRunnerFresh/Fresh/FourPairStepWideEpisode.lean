import Fresh.FourPairStepWideClear
import Fresh.FourPairStepWideCapture

/-! Actual far-pair resumption for the wider original deformation.
The raw slow-entry face selects a direct jump to WP or the VP continuation.
Closed entry equality stays clear; no global move bound is asserted. -/
namespace Fresh.FourPairStepWideEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds
  Fresh.FourPairStepPerturbedBounds Fresh.FourPairStepWideClear
  Fresh.FourPairStepWideCapture

theorem retained_at_VP (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ)
    (hUV : U m κ < VP m ρ) :
    LonelyAt (core g m σ) (VP m ρ) ∧
    (1/8 : ℝ) ≤ distInt (moved m κ*VP m ρ) ∧
    (1/8 : ℝ) ≤ distInt (fast m ρ*VP m ρ) := by
  obtain ⟨_,_,hVm,hVhi,hVlo,_,hVW,_⟩ := wide_opening_order m hm κ ρ hκ0 hκ1 hρ0 hρκ
  have hTV : T m ≤ VP m ρ := by dsimp [T,V] at *;linarith
  have hc := core_retained_wide g m hm hg he1 he2 σ hσ0 hσ1 (VP m ρ) hTV hVhi.le
  have hd := moved_retained_wide m hm κ ρ hκ0 hκ1 hρ0 hρκ (VP m ρ) hUV.le hVW.le
  obtain ⟨_,_,hf6,_,_⟩ := wide_pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hfne : fast m ρ ≠ 0 := ne_of_gt (by linarith)
  have hFV : fast m ρ*VP m ρ=7*(m : ℝ)+9/8 := by
    dsimp [VP]
    field_simp [hfne]
  refine ⟨hc,hd,?_⟩
  apply clear_of_window (7*m+1) <;> push_cast <;> linarith

theorem native_wide_tail (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    (((1+ρ)*(2*grid m+7)<κ*(6*grid m+1) ∧
        IsMove (readingsP g m κ σ ρ) (U m κ) (WP m ρ)) ∨
     (¬(1+ρ)*(2*grid m+7)<κ*(6*grid m+1) ∧
        IsMove (readingsP g m κ σ ρ) (U m κ) (VP m ρ) ∧
        IsMove (readingsP g m κ σ ρ) (VP m ρ) (WP m ρ))) ∧
      LonelyAt (readingsP g m κ σ ρ) (WP m ρ) := by
  have hfinal := wide_clear g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  obtain ⟨hTU,hUhi,hVm,hVhi,hVlo,hWlo,hVW,hUW⟩ := wide_opening_order m hm κ ρ hκ0 hκ1 hρ0 hρκ
  have hpos : ∀ d∈readingsP g m κ σ ρ, 0 < d := by
    intro d hd
    simp only [readingsP,core,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|(rfl|rfl|rfl|rfl)|rfl|rfl <;> linarith
  refine ⟨?_,hfinal⟩
  rcases at_U_split m hm κ ρ hκ0 hκ1 hρ0 hρκ with
    ⟨hcap,hwA,hopA⟩|⟨hcap,haU,hUV,hwF,hopF⟩
  · refine Or.inl ⟨hcap,Or.inr ⟨slow m ρ,by simp [readingsP],hwA,hopA.symm,?_⟩⟩
    intro d hd hw
    exact nextOpening_le_of_lonely hpos hfinal hUW.le hd hw
  · obtain ⟨_,_,hWhi,_,_,_⟩ := wide_wp_bounds m hm κ ρ hκ1 hρ0 hρκ
    have hcU := core_retained_wide g m hm hg he1 he2 σ hσ0 hσ1 (U m κ) hTU.le (hUW.le.trans hWhi)
    have hdU := moved_retained_wide m hm κ ρ hκ0 hκ1 hρ0 hρκ (U m κ) le_rfl hUW.le
    obtain ⟨hcV,hdV,hfV⟩ := retained_at_VP g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ hUV
    obtain ⟨_,_,hwA,hopA⟩ := slow_at_VP m hm κ ρ hκ0 hκ1 hρ0 hρκ
    refine Or.inr ⟨hcap,?_,?_⟩
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

#print axioms retained_at_VP
#print axioms native_wide_tail
end Fresh.FourPairStepWideEpisode
