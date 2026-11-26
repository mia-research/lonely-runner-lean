import Fresh.FourPairStepPerturbedEpisode

/-! Rules:1–4,8–18. Original entry determines whether the internally moved
reading bypasses the frozen partner reference or captures immediately after
it. Both branches merge at its own opening U, then the proved frozen fast
pair resumes. Every original reading and its initial gate is retained.
No assertion that the intermediate reference T is always visited. -/
set_option maxHeartbeats 1200000
open Classical
namespace Fresh.FourPairStepPerturbedMerge
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepEpisode Fresh.FourPairStepPerturbedBounds Fresh.FourPairStepPerturbedEpisode

theorem native_original_episode (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    IsLeast (readingsP g m κ σ ρ : Set ℝ) g ∧
    (((2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧
        IsMove (readingsP g m κ σ ρ) (1/(8*g)) (U m κ)) ∨
     ((¬2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧
        IsMove (readingsP g m κ σ ρ) (1/(8*g)) (T m) ∧
        IsMove (readingsP g m κ σ ρ) (T m) (U m κ))) ∧
    IsMove (readingsP g m κ σ ρ) (U m κ) (VP m ρ) ∧
    IsMove (readingsP g m κ σ ρ) (VP m ρ) (WP m ρ) ∧ LonelyAt (readingsP g m κ σ ρ) (WP m ρ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  obtain ⟨hspos,hsmax,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  obtain ⟨hTU,hUmax,hUV,hVW⟩ := opening_bounds m hm κ hκ0 hκ1
  obtain ⟨hUVmove,hVWmove,hfinal⟩ := perturbed_native_pair_episode g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hleast : IsLeast (readingsP g m κ σ ρ : Set ℝ) g := by
    refine ⟨by simp [readingsP,core],?_⟩
    intro d hd
    simp only [Finset.mem_coe,readingsP,core,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with rfl|(rfl|rfl|rfl|rfl)|rfl|rfl <;> linarith
  have hpos : ∀d∈readingsP g m κ σ ρ,0 < d := fun d hd => lt_of_lt_of_le hg (hleast.2 hd)
  have hden : (0 : ℝ) < 8*g := by positivity
  have htl : (m : ℝ)-1/8 < 1/(8*g) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have htu : 1/(8*g) < T m := by
    apply (div_lt_iff₀ hden).2
    dsimp [T]
    nlinarith
  have hnear1 : |(1 : ℝ)*(1/(8*g))-(m : ℝ)| < 1/8 := by
    rw [abs_lt]
    dsimp [T] at htu
    constructor <;> nlinarith
  have hway1 : InWay 1 (1/(8*g)) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ m) hnear1
  have hopen1 : nextOpening 1 (1/(8*g))=T m := by
    rw [nextOpening_eq hnear1]
    simp [T]
  let F : Finset ℝ := core g m σ ∪ {slow m ρ,fast m ρ}
  have hFclear : LonelyAt F (T m) := by
    have hTW : T m ≤ W m := by dsimp [T,W]; linarith
    have hc := core_retained g m hm hg he1 he2 σ hσ0 hσ1 (T m) le_rfl hTW
    intro d hd
    simp only [F,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with hd|rfl|rfl
    · exact hc d hd
    · apply clear_of_window (6*m) <;> push_cast <;> linarith
    · apply clear_of_window (7*m) <;> push_cast <;> linarith
  have hFpos : ∀d∈F,0 < d := by
    intro d hd
    exact hpos d (Finset.mem_insert_of_mem hd)
  have hFmax : ∀d∈F,InWay d (1/(8*g)) → nextOpening d (1/(8*g)) ≤ T m :=
    fun d hd hw => nextOpening_le_of_lonely hFpos hFclear htu.le hd hw
  have hDlower : 2*(m : ℝ)+1/8 < moved m κ*(1/(8*g)) := by
    have hmultiply := mul_lt_mul_of_pos_left htl (by linarith : 0 < moved m κ)
    dsimp [T] at hdt
    nlinarith
  have hDupper : moved m κ*(1/(8*g)) < 2*(m : ℝ)+9/8 := by
    have hmultiply := mul_lt_mul_of_pos_left htu (by linarith : 0 < moved m κ)
    nlinarith
  have hDnearT : |moved m κ*T m-((2*m+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  have hDwayT : InWay (moved m κ) (T m) :=
    lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (2*m+1)) hDnearT
  have hopenDT : nextOpening (moved m κ) (T m)=U m κ := by
    rw [nextOpening_eq hDnearT]
    dsimp [U]
    push_cast
    ring
  have hTUmove : IsMove (readingsP g m κ σ ρ) (T m) (U m κ) := by
    refine Or.inr ⟨moved m κ,by simp [readingsP],hDwayT,hopenDT.symm,?_⟩
    intro d hd hw
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact hopenDT.le
    · exact False.elim ((not_lt_of_ge (hFclear d hd)) hw)
  refine ⟨hleast,?_,hUVmove,hVWmove,hfinal⟩
  by_cases hcap : 2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))
  · have hnear : |moved m κ*(1/(8*g))-((2*m+1 : ℤ) : ℝ)| < 1/8 := by
      rw [abs_lt]
      push_cast
      constructor <;> linarith
    have hway : InWay (moved m κ) (1/(8*g)) :=
      lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (2*m+1)) hnear
    have hopen : nextOpening (moved m κ) (1/(8*g))=U m κ := by
      rw [nextOpening_eq hnear]
      dsimp [U]
      push_cast
      ring
    refine Or.inl ⟨hcap,Or.inr ⟨moved m κ,by simp [readingsP],hway,hopen.symm,?_⟩⟩
    intro d hd hw
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact hopen.le
    · exact (hFmax d hd hw).trans hTU.le
  · have hDclear : (1/8 : ℝ) ≤ distInt (moved m κ*(1/(8*g))) := by
      apply clear_of_window (2*m) <;> push_cast <;> linarith
    refine Or.inr ⟨hcap,?_,hTUmove⟩
    refine Or.inr ⟨1,by simp [readingsP,core],hway1,hopen1.symm,?_⟩
    intro d hd hw
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact False.elim ((not_lt_of_ge hDclear) hw)
    · exact hFmax d hd hw

#print axioms native_original_episode
end Fresh.FourPairStepPerturbedMerge
