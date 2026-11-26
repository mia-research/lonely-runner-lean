import Fresh.FourPairStepPerturbedBounds

/-! Rules: 1–4, 8–18. Retained seven-reading bands at the actual slow far-pair
opening WP for the wider original strip0<κ≤1 and independent0≤ρ≤1. Original cascade
controls precede this proof (four_pair_kappa_extension_v1.py/json).
Clearance does not assume that the full cascade visits VP; branch gluing
is separate. All original packet readings and closed equality edges remain.
-/
namespace Fresh.FourPairStepIndependentClear
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds
open Fresh.FourPairStepPerturbedBounds

theorem independent_pair_spec (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    5 < slow m ρ ∧ slow m ρ ≤ 6 ∧ 6 < fast m ρ ∧ fast m ρ ≤ 7 ∧
      fast m ρ=slow m ρ+1 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  have hρ1 : ρ ≤ 1 := hρκ
  have hnr : 0 ≤ ρ/grid m := div_nonneg hρ0 hq.le
  have hur : ρ/grid m ≤ 1/9 := by
    apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith
  refine ⟨by dsimp [slow];linarith,by dsimp [slow];linarith,
    by dsimp [fast];linarith,by dsimp [fast];linarith,?_⟩
  dsimp [fast,slow]
  ring

theorem independent_wp_bounds (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    0 < WP m ρ ∧ (m : ℝ)+3/16 ≤ WP m ρ ∧ WP m ρ ≤ (m : ℝ)+1/4 ∧
      (1/8 : ℝ) ≤ WP m ρ/grid m ∧ WP m ρ/grid m ≤ 5/36 ∧
      slow m ρ*WP m ρ=6*(m : ℝ)+9/8 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid];linarith
  have hρ1 : ρ ≤ 1 := hρκ
  obtain ⟨ha5,ha6,hf6,hf7,hfa⟩ := independent_pair_spec m hm κ ρ hκ1 hρ0 hρκ
  have ha : 0 < slow m ρ := by linarith
  have hWP : 0 < WP m ρ := by dsimp [WP];positivity
  have hAW : slow m ρ*WP m ρ=6*(m : ℝ)+9/8 := by
    dsimp [WP]
    field_simp
  have hWlo : (m : ℝ)+3/16 ≤ WP m ρ := by nlinarith
  have hτpos : 0 ≤ ((m : ℝ)+1/4)/grid m := by positivity
  have hτhi : ((m : ℝ)+1/4)/grid m ≤ 5/36 := by
    apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith
  have hρτ : ρ*(((m : ℝ)+1/4)/grid m) ≤ 5/36 := by
    have hh := mul_le_mul_of_nonneg_right hρ1 hτpos
    linarith
  have hτeq : slow m ρ*((m : ℝ)+1/4)=
      6*((m : ℝ)+1/4)-ρ*(((m : ℝ)+1/4)/grid m) := by
    dsimp [slow]
    ring
  have hWle : WP m ρ ≤ (m : ℝ)+1/4 := by nlinarith
  refine ⟨hWP,hWlo,hWle,?_,?_,hAW⟩
  · apply (le_div_iff₀ hq).2
    dsimp [grid]
    linarith
  · apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith

/-- Retained core up to the wider quarter-phase time, independently ofκ/ρ. -/
theorem core_retained_wide (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (t : ℝ)
    (htl : T m ≤ t) (hth : t ≤ (m : ℝ)+1/4) : LonelyAt (core g m σ) t := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hgtlo : (1/8 : ℝ) ≤ g*t := by dsimp [T] at htl;nlinarith
  have hgthi : g*t ≤ 1/4 := by nlinarith
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  have hstlo : 1 ≤ packet m σ*t := by nlinarith
  have hsthi : packet m σ*t ≤ 5/4 := by
    have ht : t-T m ≤ 1/8 := by dsimp [T] at *;linarith
    nlinarith
  intro d hd
  simp only [core,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl
  · apply clear_of_window 0 <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T] at * <;> push_cast <;> linarith
  · apply clear_of_window m <;> dsimp [T] at * <;> push_cast <;> nlinarith
  · apply clear_of_window (m+1) <;> dsimp [T] at * <;> push_cast <;> nlinarith

/-- The moved reading remains in its actual lap2m+1 band through WP. -/
theorem moved_retained_wide (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1)
    (t : ℝ) (htl : U m κ ≤ t) (hth : t ≤ WP m ρ) :
    (1/8 : ℝ) ≤ distInt (moved m κ*t) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid];linarith
  have hdpos : 0 < moved m κ := by
    have hp : 0 < (7-κ)/grid m := div_pos (by linarith) hq
    dsimp [moved]
    linarith
  obtain ⟨hWP,hWlo,hWhi,hrlo,hrhi,hAW⟩ := independent_wp_bounds m hm κ ρ hκ1 hρ0 hρκ
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by
    dsimp [U]
    field_simp
  have hDWP : moved m κ*WP m ρ ≤ 2*(m : ℝ)+53/36 := by
    have hp : 0 ≤ 7-κ := by linarith
    have hh := mul_le_mul_of_nonneg_left hrhi hp
    have he : moved m κ*WP m ρ=2*WP m ρ+(7-κ)*(WP m ρ/grid m) := by
      dsimp [moved]
      ring
    nlinarith
  have hdtlo : 2*(m : ℝ)+9/8 ≤ moved m κ*t := by nlinarith
  have hdthi : moved m κ*t ≤ 2*(m : ℝ)+53/36 := by nlinarith
  apply clear_of_window (2*m+1) <;> push_cast <;> linarith

/-- Whole original seven-reading packet clear at the actual far-slow opening. -/
theorem independent_clear (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    LonelyAt (readingsP g m κ σ ρ) (WP m ρ) := by
  obtain ⟨ha5,ha6,hf6,hf7,hfa⟩ := independent_pair_spec m hm κ ρ hκ1 hρ0 hρκ
  obtain ⟨hWP,hWlo,hWhi,hrlo,hrhi,hAW⟩ := independent_wp_bounds m hm κ ρ hκ1 hρ0 hρκ
  have hTWP : T m ≤ WP m ρ := by dsimp [T];linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid];linarith
  have hDlo : 2*(m : ℝ)+9/8 ≤ moved m κ*WP m ρ := by
    have hp : 6 ≤ 7-κ := by linarith
    have hh := mul_le_mul hp hrlo (by norm_num) (by positivity)
    have he : moved m κ*WP m ρ=2*WP m ρ+(7-κ)*(WP m ρ/grid m) := by dsimp [moved];ring
    nlinarith
  have hdpos : 0 < moved m κ := by
    have hp : 0 < (7-κ)/grid m := div_pos (by linarith) hq
    dsimp [moved]
    linarith
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U];field_simp
  have hUWP : U m κ ≤ WP m ρ := by nlinarith
  have hcore := core_retained_wide g m hm hg he1 he2 σ hσ0 hσ1 (WP m ρ) hTWP hWhi
  have hmoved := moved_retained_wide m hm κ ρ hκ0 hκ1 hρ0 hρκ (WP m ρ) hUWP le_rfl
  intro d hd
  simp only [readingsP,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
  rcases hd with rfl | hd | rfl | rfl
  · exact hmoved
  · exact hcore d hd
  · apply clear_of_window (6*m+1) <;> push_cast <;> linarith
  · have he : fast m ρ*WP m ρ=6*(m : ℝ)+9/8+WP m ρ := by rw [hfa,add_mul,hAW];ring
    apply clear_of_window (7*m+1) <;> push_cast <;> linarith

#print axioms independent_pair_spec
#print axioms independent_wp_bounds
#print axioms core_retained_wide
#print axioms moved_retained_wide
#print axioms independent_clear
end Fresh.FourPairStepIndependentClear
