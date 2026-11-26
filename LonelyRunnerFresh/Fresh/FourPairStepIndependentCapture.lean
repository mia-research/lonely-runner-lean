import Fresh.FourPairStepPerturbedJoins

/-! Rules:1–4,8–18. Actual captured/clear faces for the moved reading
whenκ≤1. U need not precede VP: slow capture at U may bypass VP.
The slow-clear face, including equality, forces U<VP instead. -/
open Classical
namespace Fresh.FourPairStepIndependentCapture
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepPerturbedBounds

theorem moved_wide_spec (m : ℤ) (hm : 1 ≤ m) (κ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
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
    field_simp <;> ring

theorem pair_wide_spec (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    5 < slow m ρ ∧ slow m ρ ≤ 6 ∧ 6 < fast m ρ ∧ fast m ρ ≤ 7 ∧
    fast m ρ=slow m ρ+1 ∧
    slow m ρ*T m=6*(m : ℝ)+3/4-ρ/8 ∧
    fast m ρ*T m=7*(m : ℝ)+7/8-ρ/8 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < grid m := by dsimp [grid]; linarith
  have hr0 : 0 ≤ ρ/grid m := div_nonneg hρ0 hq.le
  have hr1 : ρ/grid m ≤ 1/9 := by
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

theorem wide_opening_order (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    T m < U m κ ∧ U m κ < T m+1/16 ∧
    (m : ℝ)<VP m ρ ∧ VP m ρ<(m : ℝ)+1/4 ∧
    V m ≤ VP m ρ ∧ W m ≤ WP m ρ ∧ VP m ρ < WP m ρ ∧ U m κ<WP m ρ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U]; field_simp
  have hFV : fast m ρ*VP m ρ=7*(m : ℝ)+9/8 := by dsimp [VP]; field_simp
  have hAW : slow m ρ*WP m ρ=6*(m : ℝ)+9/8 := by dsimp [WP]; field_simp
  have hdiff : moved m κ*(U m κ-T m)=κ/8 := by nlinarith only [hDU,hdt]
  have hTU : T m<U m κ := by nlinarith only [hd2,hdiff,hκ0]
  have hUhi : U m κ<T m+1/16 := by nlinarith only [hd2,hdiff,hκ1,hTU]
  have hq : 0 < grid m := by dsimp [grid]; linarith
  have hratio : ((m : ℝ)+1/4)/grid m ≤ 1/7 := by
    apply (div_le_iff₀ hq).2
    dsimp [grid]
    linarith
  have hFsmall : fast m ρ*((m : ℝ)+1/4)>7*(m : ℝ)+9/8 := by
    have hp : ρ*(((m : ℝ)+1/4)/grid m) ≤ 1/7 := by
      calc
        _ ≤ (1 : ℝ)*(1/7) := mul_le_mul (hρκ) hratio (by positivity) (by norm_num)
        _ = 1/7 := by ring
    have hp2 : (ρ/grid m)*((m : ℝ)+1/4) ≤ 1/7 := by
      convert hp using 1 <;> ring
    dsimp [fast]
    nlinarith only [hp2]
  have hVhi : VP m ρ<(m : ℝ)+1/4 := by nlinarith only [hFV,hFsmall,hf6]
  have hVlo : V m≤VP m ρ := by
    have hVpos : 0<V m := by dsimp [V]; linarith
    have hh := mul_le_mul_of_nonneg_right hf7 hVpos.le
    dsimp [V] at hh ⊢
    nlinarith only [hh,hFV,hf6]
  have hWlo : W m≤WP m ρ := by
    have hWpos : 0<W m := by dsimp [W]; linarith
    have hh := mul_le_mul_of_nonneg_right ha6 hWpos.le
    dsimp [W] at hh ⊢
    nlinarith only [hh,hAW,ha5]
  have hVm : (m : ℝ)<VP m ρ := by dsimp [V] at hVlo; linarith
  have hAV : slow m ρ*VP m ρ=7*(m : ℝ)+9/8-VP m ρ := by
    rw [hfa] at hFV
    nlinarith only [hFV]
  have hVW : VP m ρ<WP m ρ := by nlinarith only [hAV,hAW,ha5,hVm]
  have hUW : U m κ<WP m ρ := by dsimp [T,W] at *; linarith only [hUhi,hWlo]
  exact ⟨hTU,hUhi,hVm,hVhi,hVlo,hWlo,hVW,hUW⟩

theorem slow_at_VP (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    6*(m : ℝ)+7/8<slow m ρ*VP m ρ ∧
    slow m ρ*VP m ρ<6*(m : ℝ)+9/8 ∧
    InWay (slow m ρ) (VP m ρ) ∧ nextOpening (slow m ρ) (VP m ρ)=WP m ρ := by
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  obtain ⟨_,_,hVm,hVhi,_,_,_,_⟩ := wide_opening_order m hm κ ρ hκ0 hκ1 hρ0 hρκ
  have hFV : fast m ρ*VP m ρ=7*(m : ℝ)+9/8 := by dsimp [VP]; field_simp
  have hAV : slow m ρ*VP m ρ=7*(m : ℝ)+9/8-VP m ρ := by
    rw [hfa] at hFV
    nlinarith only [hFV]
  have hlo : 6*(m : ℝ)+7/8<slow m ρ*VP m ρ := by linarith
  have hhi : slow m ρ*VP m ρ<6*(m : ℝ)+9/8 := by linarith
  have hnear : |slow m ρ*VP m ρ-((6*m+1 : ℤ) : ℝ)|<1/8 := by
    rw [abs_lt]; push_cast; constructor <;> linarith
  refine ⟨hlo,hhi,lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (6*m+1)) hnear,?_⟩
  rw [nextOpening_eq hnear]
  dsimp [WP]; push_cast; ring

theorem slow_U_input_face (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ 1) :
    (6*(m : ℝ)+7/8<slow m ρ*U m κ) ↔
    (1+ρ)*(2*grid m+7)<κ*(6*grid m+1) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0<grid m := by dsimp [grid]; linarith
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U]; field_simp
  have hdiff : moved m κ*(U m κ-T m)=κ/8 := by nlinarith only [hDU,hdt]
  have hphase : slow m ρ*U m κ-(6*(m : ℝ)+7/8)=
      slow m ρ*(U m κ-T m)-(1+ρ)/8 := by nlinarith only [hat]
  have hmain : (8*moved m κ)*(slow m ρ*U m κ-(6*(m : ℝ)+7/8))=
      κ*slow m ρ-(1+ρ)*moved m κ := by
    rw [hphase]
    calc
      _ = 8*slow m ρ*(moved m κ*(U m κ-T m))-(1+ρ)*moved m κ := by ring
      _ = _ := by rw [hdiff]; ring
  have halg : grid m*(κ*slow m ρ-(1+ρ)*moved m κ)=
      κ*(6*grid m+1)-(1+ρ)*(2*grid m+7) := by
    dsimp [slow,moved]
    field_simp
    <;> ring
  have hid : (grid m*(8*moved m κ))*(slow m ρ*U m κ-(6*(m : ℝ)+7/8))=
      κ*(6*grid m+1)-(1+ρ)*(2*grid m+7) := by
    calc
      _ = grid m*((8*moved m κ)*(slow m ρ*U m κ-(6*(m : ℝ)+7/8))) := by ring
      _ = _ := by rw [hmain,halg]
  have hp : 0<grid m*(8*moved m κ) := by positivity
  constructor
  · intro h
    have hh := mul_pos hp (sub_pos.mpr h)
    linarith only [hid,hh]
  · intro h
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (le_of_not_gt hn))
    linarith only [hid,hh,h]

theorem fast_U_input_face (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (7*(m : ℝ)+7/8<fast m ρ*U m κ) ↔
    ρ*(2*grid m+7)<κ*(7*grid m) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0<grid m := by dsimp [grid]; linarith
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρ1
  have hDU : moved m κ*U m κ=2*(m : ℝ)+9/8 := by dsimp [U]; field_simp
  have hdiff : moved m κ*(U m κ-T m)=κ/8 := by nlinarith only [hDU,hdt]
  have hphase : fast m ρ*U m κ-(7*(m : ℝ)+7/8)=
      fast m ρ*(U m κ-T m)-ρ/8 := by nlinarith only [hft]
  have hmain : (8*moved m κ)*(fast m ρ*U m κ-(7*(m : ℝ)+7/8))=
      κ*fast m ρ-ρ*moved m κ := by
    rw [hphase]
    calc
      _ = 8*fast m ρ*(moved m κ*(U m κ-T m))-ρ*moved m κ := by ring
      _ = _ := by rw [hdiff]; ring
  have halg : grid m*(κ*fast m ρ-ρ*moved m κ)=
      κ*(7*grid m)-ρ*(2*grid m+7) := by
    dsimp [fast,moved]
    field_simp <;> ring
  have hid : (grid m*(8*moved m κ))*(fast m ρ*U m κ-(7*(m : ℝ)+7/8))=
      κ*(7*grid m)-ρ*(2*grid m+7) := by
    calc
      _ = grid m*((8*moved m κ)*(fast m ρ*U m κ-(7*(m : ℝ)+7/8))) := by ring
      _ = _ := by rw [hmain,halg]
  have hp : 0<grid m*(8*moved m κ) := by positivity
  constructor
  · intro h
    have hh := mul_pos hp (sub_pos.mpr h)
    linarith only [hid,hh]
  · intro h
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (le_of_not_gt hn))
    linarith only [hid,hh,h]

theorem at_U_split (m : ℤ) (hm : 1 ≤ m) (κ ρ : ℝ)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (((1+ρ)*(2*grid m+7)<κ*(6*grid m+1)) ∧
      InWay (slow m ρ) (U m κ) ∧ nextOpening (slow m ρ) (U m κ)=WP m ρ) ∨
    ((¬(1+ρ)*(2*grid m+7)<κ*(6*grid m+1)) ∧
      ρ*(2*grid m+7)<κ*(7*grid m) ∧
      (1/8 : ℝ)≤distInt (slow m ρ*U m κ) ∧ U m κ<VP m ρ ∧
      InWay (fast m ρ) (U m κ) ∧ nextOpening (fast m ρ) (U m κ)=VP m ρ) ∨
    ((¬(1+ρ)*(2*grid m+7)<κ*(6*grid m+1)) ∧
      (¬ρ*(2*grid m+7)<κ*(7*grid m)) ∧
      (1/8 : ℝ)≤distInt (slow m ρ*U m κ) ∧
      (1/8 : ℝ)≤distInt (fast m ρ*U m κ)) := by
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρ1
  obtain ⟨hTU,hUhi,hVm,hVhi,hVlo,hWlo,hVW,hUW⟩ := wide_opening_order m hm κ ρ hκ0 hκ1 hρ0 hρ1
  obtain ⟨hAVlo,hAVhi,_,_⟩ := slow_at_VP m hm κ ρ hκ0 hκ1 hρ0 hρ1
  have hAW : slow m ρ*WP m ρ=6*(m : ℝ)+9/8 := by dsimp [WP]; field_simp
  have hAUhi : slow m ρ*U m κ<6*(m : ℝ)+9/8 := by nlinarith only [hUW,ha5,hAW]
  have hAUlo : 6*(m : ℝ)+1/8 ≤ slow m ρ*U m κ := by
    have hh := mul_lt_mul_of_pos_left hTU (by linarith : 0<slow m ρ)
    nlinarith only [hh,hat,hρ1]
  by_cases hcap : (1+ρ)*(2*grid m+7)<κ*(6*grid m+1)
  · have hentry := (slow_U_input_face m hm κ ρ hκ0 hκ1 hρ0 hρ1).2 hcap
    have hnear : |slow m ρ*U m κ-((6*m+1 : ℤ) : ℝ)|<1/8 := by
      rw [abs_lt]; push_cast; constructor <;> linarith
    refine Or.inl ⟨hcap,lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (6*m+1)) hnear,?_⟩
    rw [nextOpening_eq hnear]
    dsimp [WP]; push_cast; ring
  · have hclearface : slow m ρ*U m κ≤6*(m : ℝ)+7/8 :=
      le_of_not_gt (fun h => hcap ((slow_U_input_face m hm κ ρ hκ0 hκ1 hρ0 hρ1).1 h))
    have hAclear : (1/8 : ℝ)≤distInt (slow m ρ*U m κ) := by
      apply clear_of_window (6*m) <;> push_cast <;> linarith
    have hUV : U m κ<VP m ρ := by nlinarith only [hclearface,hAVlo,ha5]
    by_cases hfast : ρ*(2*grid m+7)<κ*(7*grid m)
    · have hFUlo := (fast_U_input_face m hm κ ρ hκ0 hκ1 hρ0 hρ1).2 hfast
      have hFV : fast m ρ*VP m ρ=7*(m : ℝ)+9/8 := by dsimp [VP]; field_simp
      have hFUhi : fast m ρ*U m κ<7*(m : ℝ)+9/8 := by nlinarith only [hUV,hFV,hf6]
      have hnear : |fast m ρ*U m κ-((7*m+1 : ℤ) : ℝ)|<1/8 := by
        rw [abs_lt]; push_cast; constructor <;> linarith
      refine Or.inr (Or.inl ⟨hcap,hfast,hAclear,hUV,
        lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (7*m+1)) hnear,?_⟩)
      rw [nextOpening_eq hnear]
      dsimp [VP]; push_cast; ring
    · have hFUhi : fast m ρ*U m κ≤7*(m : ℝ)+7/8 :=
        le_of_not_gt (fun h => hfast ((fast_U_input_face m hm κ ρ hκ0 hκ1 hρ0 hρ1).1 h))
      have hFUlo : 7*(m : ℝ)+1/8 ≤ fast m ρ*U m κ := by
        have hh := mul_lt_mul_of_pos_left hTU (by linarith : 0<fast m ρ)
        nlinarith only [hh,hft,hρ1]
      refine Or.inr (Or.inr ⟨hcap,hfast,hAclear,?_⟩)
      apply clear_of_window (7*m) <;> push_cast <;> linarith

#print axioms moved_wide_spec
#print axioms pair_wide_spec
#print axioms wide_opening_order
#print axioms slow_at_VP
#print axioms slow_U_input_face
#print axioms fast_U_input_face
#print axioms at_U_split
end Fresh.FourPairStepIndependentCapture
