import Fresh.FourPairStepNativePhysical

/-! Rules:1–4,8–18. Exact far-pair step deformation retained from original
parameterρ∈[0,κ]. Original far readings6−ρ/q,7−ρ/q keep their unit spacing;
new opening shifts are derived from their actual lap equations. No assumed
uniform displacement of the complete cascade. -/
open Classical
namespace Fresh.FourPairStepPerturbedBounds
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds

noncomputable def slow (m : ℤ) (ρ : ℝ) : ℝ := 6-ρ/grid m
noncomputable def fast (m : ℤ) (ρ : ℝ) : ℝ := 7-ρ/grid m
noncomputable def VP (m : ℤ) (ρ : ℝ) : ℝ := (7*(m : ℝ)+9/8)/fast m ρ
noncomputable def WP (m : ℤ) (ρ : ℝ) : ℝ := (6*(m : ℝ)+9/8)/slow m ρ
noncomputable def readingsP (g : ℝ) (m : ℤ) (κ σ ρ : ℝ) : Finset ℝ :=
  insert (moved m κ) (core g m σ ∪ {slow m ρ,fast m ρ})

theorem pair_spec (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ1 : κ ≤ 1/4) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    5 < slow m ρ ∧ slow m ρ ≤ 6 ∧ 6 < fast m ρ ∧ fast m ρ ≤ 7 ∧
    fast m ρ=slow m ρ+1 ∧
    slow m ρ*T m=6*(m : ℝ)+3/4-ρ/8 ∧
    fast m ρ*T m=7*(m : ℝ)+7/8-ρ/8 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  have hr0 : 0 ≤ ρ/grid m := div_nonneg hρ0 hq.le
  have hr1 : ρ/grid m ≤ 1/36 := by
    apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith
  refine ⟨by dsimp [slow]; linarith,by dsimp [slow]; linarith,
    by dsimp [fast]; linarith,by dsimp [fast]; linarith,
    by dsimp [slow,fast]; ring,?_,?_⟩
  · dsimp [slow,T,grid]
    field_simp <;> ring
  · dsimp [fast,T,grid]
    field_simp <;> ring

theorem perturbed_opening_bounds (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ1 : κ ≤ 1/4) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    V m ≤ VP m ρ ∧ VP m ρ ≤ V m+1/128 ∧
    W m ≤ WP m ρ ∧ WP m ρ ≤ W m+1/128 ∧ VP m ρ < WP m ρ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  have hρq : ρ ≤ (1/4 : ℝ) := hρκ.trans hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have hVpos : 0 < V m := by dsimp [V]; linarith
  have hWpos : 0 < W m := by dsimp [W]; linarith
  have hvr : V m/grid m ≤ 1/7 := by
    apply (div_le_iff₀ hq).2
    dsimp [V,grid]
    linarith
  have hwr : W m/grid m ≤ 1/7 := by
    apply (div_le_iff₀ hq).2
    dsimp [W,grid]
    linarith
  have hrV : (ρ/grid m)*V m ≤ 1/28 := by
    calc
      (ρ/grid m)*V m=ρ*(V m/grid m) := by ring
      _ ≤ (1/4 : ℝ)*(1/7) := mul_le_mul hρq hvr (by positivity) (by norm_num)
      _ = 1/28 := by norm_num
  have hrW : (ρ/grid m)*W m ≤ 1/28 := by
    calc
      (ρ/grid m)*W m=ρ*(W m/grid m) := by ring
      _ ≤ (1/4 : ℝ)*(1/7) := mul_le_mul hρq hwr (by positivity) (by norm_num)
      _ = 1/28 := by norm_num
  have hFVP : fast m ρ*VP m ρ=7*V m := by dsimp [VP,V]; field_simp <;> ring
  have hAWP : slow m ρ*WP m ρ=6*W m := by dsimp [WP,W]; field_simp <;> ring
  have hVF : fast m ρ*(VP m ρ-V m)=(ρ/grid m)*V m := by
    calc
      fast m ρ*(VP m ρ-V m)=7*V m-fast m ρ*V m := by rw [mul_sub,hFVP]
      _ = (ρ/grid m)*V m := by dsimp [fast]; ring
  have hWA : slow m ρ*(WP m ρ-W m)=(ρ/grid m)*W m := by
    calc
      slow m ρ*(WP m ρ-W m)=6*W m-slow m ρ*W m := by rw [mul_sub,hAWP]
      _ = (ρ/grid m)*W m := by dsimp [slow]; ring
  have hnrV : 0 ≤ (ρ/grid m)*V m := by positivity
  have hnrW : 0 ≤ (ρ/grid m)*W m := by positivity
  have hVlo : V m ≤ VP m ρ := by nlinarith
  have hWlo : W m ≤ WP m ρ := by nlinarith
  have hVhi : VP m ρ ≤ V m+1/128 := by nlinarith
  have hWhi : WP m ρ ≤ W m+1/128 := by nlinarith
  refine ⟨hVlo,hVhi,hWlo,hWhi,?_⟩
  dsimp [V,W] at *
  linarith

theorem core_retained_extended (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (t : ℝ)
    (htl : T m ≤ t) (hth : t ≤ W m+1/128) : LonelyAt (core g m σ) t := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hgtlo : (1/8 : ℝ) ≤ g*t := by dsimp [T] at htl; nlinarith
  have hgthi : g*t ≤ 1/4 := by dsimp [W] at hth; nlinarith
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  have hstlo : 1 ≤ packet m σ*t := by nlinarith
  have hsthi : packet m σ*t ≤ 153/128 := by
    have ht : t-T m ≤ 9/128 := by dsimp [T,W] at *; linarith
    nlinarith
  intro d hd
  simp only [core,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl
  · apply clear_of_window 0 <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T,W] at * <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T,W] at * <;> push_cast <;> nlinarith
  · apply clear_of_window (m+1) <;> dsimp [T,W] at * <;> push_cast <;> nlinarith

theorem moved_retained_extended (m : ℤ) (hm : 1 ≤ m) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4)
    (t : ℝ) (htl : V m ≤ t) (hth : t ≤ W m+1/128) :
    (1/8 : ℝ) ≤ distInt (moved m κ*t) := by
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  have ht1 : (1/28 : ℝ) ≤ t-T m := by dsimp [T,V] at *; linarith
  have ht2 : t-T m ≤ 9/128 := by dsimp [T,W] at *; linarith
  have hl : (1/14 : ℝ) ≤ moved m κ*(t-T m) := by nlinarith
  have hu : moved m κ*(t-T m) ≤ 27/128 := by nlinarith
  apply clear_of_window (2*m+1) <;> push_cast <;> nlinarith

#print axioms pair_spec
#print axioms perturbed_opening_bounds
#print axioms core_retained_extended
#print axioms moved_retained_extended
end Fresh.FourPairStepPerturbedBounds
