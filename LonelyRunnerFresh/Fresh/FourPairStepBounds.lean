import Fresh.FourAPPairsNativeClass

/-! Rules:1–4,8–18. Exact retained-band algebra for an internal pair-step
carry into the native frozen pair6,7. All bounds derive from original
speed parameters. The local episode does not impose any global move cap. -/
open Classical
namespace Fresh.FourPairStepBounds
open Fresh Fresh.Cascade Fresh.Localisation

noncomputable def grid (m : ℤ) : ℝ := 8*(m : ℝ)+1
noncomputable def packet (m : ℤ) (σ : ℝ) : ℝ := (8+σ)/grid m
noncomputable def moved (m : ℤ) (κ : ℝ) : ℝ := 2+(7-κ)/grid m
noncomputable def T (m : ℤ) : ℝ := (m : ℝ)+1/8
noncomputable def U (m : ℤ) (κ : ℝ) : ℝ := (2*(m : ℝ)+9/8)/moved m κ
noncomputable def V (m : ℤ) : ℝ := (m : ℝ)+9/56
noncomputable def W (m : ℤ) : ℝ := (m : ℝ)+3/16

noncomputable def core (g : ℝ) (m : ℤ) (σ : ℝ) : Finset ℝ :=
  {g,1,1+g,1+packet m σ}
noncomputable def readings (g : ℝ) (m : ℤ) (κ σ : ℝ) : Finset ℝ :=
  insert (moved m κ) (core g m σ ∪ {6,7})

theorem packet_spec (m : ℤ) (hm : 1 ≤ m) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 < packet m σ ∧ packet m σ ≤ 1 ∧ packet m σ*T m=1+σ/8 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  refine ⟨by dsimp [packet]; positivity,?_,?_⟩
  · apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith
  · dsimp [packet,T,grid]
    field_simp
    <;> ring

theorem moved_spec (m : ℤ) (hm : 1 ≤ m) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) :
    2 < moved m κ ∧ moved m κ ≤ 3 ∧
      moved m κ*T m=2*(m : ℝ)+9/8-κ/8 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  refine ⟨?_,?_,?_⟩
  · dsimp [moved]
    have hp : 0 < (7-κ)/grid m := div_pos (by linarith) hq
    linarith
  · have hd : (7-κ)/grid m ≤ 1 := by
      apply (div_le_iff₀ hq).2
      dsimp [grid]
      linarith
    dsimp [moved]
    linarith
  · dsimp [moved,T,grid]
    field_simp
    <;> ring

theorem opening_bounds (m : ℤ) (hm : 1 ≤ m) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) :
    T m < U m κ ∧ U m κ ≤ T m+1/64 ∧ U m κ < V m ∧ V m < W m := by
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  have he : moved m κ*U m κ=2*(m : ℝ)+9/8 := by
    dsimp [U]
    field_simp
  have hdiff : moved m κ*(U m κ-T m)=κ/8 := by nlinarith
  have hUmax : U m κ ≤ T m+1/64 := by nlinarith
  refine ⟨by nlinarith,hUmax,?_,?_⟩
  · dsimp [T,V] at *
    linarith
  · dsimp [V,W]
    norm_num

theorem core_retained (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (t : ℝ)
    (htl : T m ≤ t) (hth : t ≤ W m) : LonelyAt (core g m σ) t := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hgtlo : (1/8 : ℝ) ≤ g*t := by dsimp [T] at htl; nlinarith
  have hgthi : g*t ≤ 1/4 := by dsimp [W] at hth; nlinarith
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  have hstlo : 1 ≤ packet m σ*t := by nlinarith
  have hsthi : packet m σ*t ≤ 19/16 := by
    have ht : t-T m ≤ 1/16 := by dsimp [T,W] at *; linarith
    nlinarith
  intro d hd
  simp only [core,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl
  · apply clear_of_window 0 <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T,W] at * <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T,W] at * <;> push_cast <;> nlinarith
  · apply clear_of_window (m+1) <;> dsimp [T,W] at * <;> push_cast <;> nlinarith

theorem moved_retained (m : ℤ) (hm : 1 ≤ m) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4)
    (t : ℝ) (htl : V m ≤ t) (hth : t ≤ W m) :
    (1/8 : ℝ) ≤ distInt (moved m κ*t) := by
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  have ht1 : (1/28 : ℝ) ≤ t-T m := by dsimp [T,V] at *; linarith
  have ht2 : t-T m ≤ 1/16 := by dsimp [T,W] at *; linarith
  have hl : (1/14 : ℝ) ≤ moved m κ*(t-T m) := by nlinarith
  have hu : moved m κ*(t-T m) ≤ 3/16 := by nlinarith
  apply clear_of_window (2*m+1) <;> push_cast <;> nlinarith

#print axioms packet_spec
#print axioms moved_spec
#print axioms opening_bounds
#print axioms core_retained
#print axioms moved_retained
end Fresh.FourPairStepBounds
