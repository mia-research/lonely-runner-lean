import Fresh.BufferedSectors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Data.Rat.Floor

namespace Fresh.FiniteRelations

open Set MeasureTheory Fresh.Cascade Fresh.Harmonic
open scoped BigOperators

noncomputable section

private def badBase : Set ℝ :=
  Icc 0 (1/8) ∪ Icc (7/16) (9/16) ∪ Icc (7/8) 1

private def badPair : Set ℝ := Int.fract ⁻¹' badBase
private def badFn : ℝ → ℝ := badPair.indicator (fun _ => 1)

private theorem bad_meas : MeasurableSet badPair :=
  ((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).preimage measurable_fract

private theorem bad_int (a b : ℝ) : IntervalIntegrable badFn volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
  · exact (measurable_const.indicator bad_meas).aestronglyMeasurable
  · filter_upwards with x
    unfold badFn
    by_cases h : x ∈ badPair <;> simp [h]

private theorem bad_periodic : Function.Periodic badFn 1 := by
  intro x
  have he : x+1 ∈ badPair ↔ x ∈ badPair := by
    simp only [badPair,mem_preimage,Int.fract_add_one]
  by_cases h : x ∈ badPair <;> simp [badFn,he,h]

private def basePrimitive {K : Type*} [Field K] [LinearOrder K] (x : K) : K :=
  min x (1/8) + max 0 (min (x-7/16) (1/8)) + max 0 (x-7/8)

private def primitive (x : ℝ) : ℝ := ∫ t in 0..x, badFn t

theorem indicator_interval (a b x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    (∫ t in 0..x, (Icc a b).indicator (fun _ => (1:ℝ)) t) =
      max 0 (min b x-a) := by
  rw [intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
  rw [inter_comm, Icc_inter_Icc, max_eq_left ha, Real.volume_real_Icc]
  exact max_comm _ _

private theorem primitive_base (x : ℝ) (hx : x ∈ Icc 0 1) :
    primitive x = basePrimitive x := by
  let f (a b : ℝ) := (Icc a b).indicator (fun _ => (1:ℝ))
  have hi (a b : ℝ) : IntervalIntegrable (f a b) volume 0 x := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
    · exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with y
      unfold f
      by_cases h : y ∈ Icc a b <;> simp [h]
  have he : (∫ t in 0..x, badFn t) = ∫ t in 0..x,
      (f 0 (1/8)+ f (7/16) (9/16)+ f (7/8) 1) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    have ht1 := ht.2.trans hx.2
    have hmem : t ∈ badPair ↔ t ∈ badBase := by
      rcases lt_or_eq_of_le ht1 with h | rfl
      · simp only [badPair,mem_preimage,Int.fract_eq_self.mpr ⟨ht.1,h⟩]
      · norm_num [badPair,badBase,Int.fract,Int.floor_one]
    by_cases h₁ : t ≤ 1/8
    · have hA : t ∈ Icc (0:ℝ) (1/8) := ⟨ht.1,h₁⟩
      have hB : t ∉ Icc (7/16:ℝ) (9/16) := fun h => by linarith [h.1]
      have hC : t ∉ Icc (7/8:ℝ) 1 := fun h => by linarith [h.1]
      have hP : t ∈ badPair := hmem.mpr (Or.inl (Or.inl hA))
      simp only [badFn,f,Pi.add_apply,indicator_of_mem hP,indicator_of_mem hA,
        indicator_of_notMem hB,indicator_of_notMem hC,add_zero]
    · have hA : t ∉ Icc (0:ℝ) (1/8) := fun h => h₁ h.2
      by_cases hB : t ∈ Icc (7/16:ℝ) (9/16)
      · have hC : t ∉ Icc (7/8:ℝ) 1 := fun h => by linarith [h.1,hB.2]
        have hP : t ∈ badPair := hmem.mpr (Or.inl (Or.inr hB))
        simp only [badFn,f,Pi.add_apply,indicator_of_mem hP,indicator_of_mem hB,
          indicator_of_notMem hA,indicator_of_notMem hC,zero_add,add_zero]
      · by_cases hC : t ∈ Icc (7/8:ℝ) 1
        · have hP : t ∈ badPair := hmem.mpr (Or.inr hC)
          simp only [badFn,f,Pi.add_apply,indicator_of_mem hP,indicator_of_mem hC,
            indicator_of_notMem hA,indicator_of_notMem hB,zero_add]
        · have hP : t ∉ badPair := fun h => by
            have hh := hmem.mp h
            rcases hh with (hh | hh) | hh
            exacts [hA hh,hB hh,hC hh]
          simp only [badFn,f,Pi.add_apply,indicator_of_notMem hP,indicator_of_notMem hA,
            indicator_of_notMem hB,indicator_of_notMem hC,zero_add]
  unfold primitive
  rw [he]
  change (∫ t in 0..x, f 0 (1/8) t + f (7/16) (9/16) t + f (7/8) 1 t) = _
  rw [intervalIntegral.integral_add ((hi 0 (1/8)).add (hi (7/16) (9/16))) (hi (7/8) 1),
    intervalIntegral.integral_add (hi 0 (1/8)) (hi (7/16) (9/16))]
  simp only [f, indicator_interval _ _ x (by norm_num : (0:ℝ) ≤ 0) hx.1,
    indicator_interval _ _ x (by norm_num : (0:ℝ) ≤ 7/16) hx.1,
    indicator_interval _ _ x (by norm_num : (0:ℝ) ≤ 7/8) hx.1]
  unfold basePrimitive
  have hfirst : max 0 (min (1/8:ℝ) x - 0) = min x (1/8) := by
    rw [sub_zero,max_eq_right (le_min (by norm_num) hx.1),min_comm]
  have hmid : min (9/16:ℝ) x-7/16 = min (x-7/16) (1/8) := by
    rw [← min_sub_sub_right, min_comm]
    norm_num
  rw [hfirst,hmid,min_eq_right hx.2]

theorem periodic_primitive_fract {f : ℝ → ℝ} (hperiod : Function.Periodic f 1)
    (hint : ∀ a b, IntervalIntegrable f volume a b) (x : ℝ) :
    (∫ t in 0..x, f t) = (⌊x⌋:ℝ)*(∫ t in 0..1, f t) + (∫ t in 0..Int.fract x, f t) := by
  let y := Int.fract x
  have hsum : y + ⌊x⌋ • (1:ℝ) = x := by
    rw [zsmul_eq_mul, mul_one]
    exact Int.fract_add_floor x
  conv_lhs => rw [← hsum]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 y) (hint y _)]
  rw [hperiod.intervalIntegral_add_zsmul_eq ⌊x⌋ y hint,
    hperiod.intervalIntegral_add_eq y 0,zero_add,zsmul_eq_mul,add_comm]

private theorem primitive_formula (x : ℝ) :
    primitive x = (⌊x⌋:ℝ)*(3/8) + basePrimitive (Int.fract x) := by
  have hbase := primitive_base (Int.fract x) ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have hperiod : (∫ t in 0..1, badFn t) = 3/8 := by
    rw [show (∫ t in 0..1, badFn t) = primitive 1 from rfl,
      primitive_base 1 (by norm_num),basePrimitive]
    norm_num
  unfold primitive
  rw [periodic_primitive_fract bad_periodic bad_int, hperiod]
  exact congrArg _ hbase

private theorem discrepancy (x : ℝ) :
    -(5/64:ℝ) ≤ primitive x - (3/8)*x ∧ primitive x - (3/8)*x ≤ 5/64 := by
  rw [primitive_formula]
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  have he := Int.fract_add_floor x
  generalize Int.fract x = t at *
  unfold basePrimitive
  simp only [min_def,max_def]
  split_ifs <;> constructor <;> linarith

private theorem primitive_increment {a b : ℝ} (h : a ≤ b) :
    0 ≤ primitive b-primitive a ∧ primitive b-primitive a ≤ b-a := by
  have he : primitive b-primitive a = ∫ t in a..b, badFn t := by
    unfold primitive
    linarith [intervalIntegral.integral_add_adjacent_intervals (bad_int 0 a) (bad_int a b)]
  rw [he]
  constructor
  · apply intervalIntegral.integral_nonneg h
    intro t _
    unfold badFn
    by_cases h : t ∈ badPair <;> simp [h]
  · have hh := intervalIntegral.integral_mono_on h (bad_int a b) intervalIntegrable_const
      (f := badFn) (g := fun _ => (1:ℝ)) (by
        intro t _
        unfold badFn
        by_cases h : t ∈ badPair <;> simp [h])
    simpa using hh

private def primitiveQ (x : ℚ) : ℚ := (⌊x⌋:ℚ)*(3/8) + basePrimitive (Int.fract x)

private theorem cast_primitiveQ (x : ℚ) : ((primitiveQ x : ℚ) : ℝ) = primitive (x:ℝ) := by
  rw [primitive_formula,primitiveQ,basePrimitive,basePrimitive]
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,
    Rat.cast_intCast,Rat.cast_min,Rat.cast_max,Rat.floor_cast,Rat.cast_fract,Rat.cast_one]

private def loss (a : ℝ) : ℝ :=
  primitive (7/16*a)-primitive (1/8*a)+primitive (7/8*a)-primitive (9/16*a)

private def grid (i : Fin 193) : ℚ := 1+(i.val:ℚ)/64

private theorem grid_bound : ∀ i : Fin 193,
    let a := grid i
    primitiveQ (7/16*a)-primitiveQ (1/8*a)+primitiveQ (7/8*a)-primitiveQ (9/16*a)
      ≤ 7/24*a := by decide +kernel

private theorem grid_bound_real (i : Fin 193) : loss (grid i : ℝ) ≤ 7/24*(grid i : ℝ) := by
  have h := grid_bound i
  dsimp only at h
  have h' := (Rat.cast_le (K := ℝ)).2 h
  simp only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,
    cast_primitiveQ] at h'
  exact h'

/-- Each additional slow rate blocks less than half of the pinned
reading's paired window. Above 4 this follows from the discrepancy of
one period; below 4 a one-variable rational grid has certified slack. -/
theorem paired_slow_loss_lt_half {a : ℝ} (ha : 1 ≤ a) : loss a < (5/16)*a := by
  by_cases hb : a ≤ 4
  · let k : ℤ := ⌊64*(a-1)⌋
    have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (by linarith)
    have hkl : (k:ℝ) ≤ 64*(a-1) := Int.floor_le _
    have hku : 64*(a-1) < (k:ℝ)+1 := Int.lt_floor_add_one _
    have hk' : k ≤ 192 := by
      exact_mod_cast (show (k:ℝ) ≤ 192 by linarith)
    let i : Fin 193 := ⟨k.toNat,by omega⟩
    let a₀ : ℝ := grid i
    have hea : a₀ = 1+(k:ℝ)/64 := by
      unfold a₀ grid
      push_cast
      change 1+(k.toNat:ℝ)/64 = _
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hk0]
    have ha₀ : a₀ ≤ a := by rw [hea]; linarith
    have he : a < a₀+1/64 := by rw [hea]; linarith
    have h₁ := (primitive_increment (mul_le_mul_of_nonneg_left ha₀ (by norm_num : (0:ℝ) ≤ 7/16))).2
    have h₂ := (primitive_increment (mul_le_mul_of_nonneg_left ha₀ (by norm_num : (0:ℝ) ≤ 1/8))).1
    have h₃ := (primitive_increment (mul_le_mul_of_nonneg_left ha₀ (by norm_num : (0:ℝ) ≤ 7/8))).2
    have h₄ := (primitive_increment (mul_le_mul_of_nonneg_left ha₀ (by norm_num : (0:ℝ) ≤ 9/16))).1
    have h := grid_bound_real i
    change loss a₀ ≤ 7/24*a₀ at h
    unfold loss at h ⊢
    linarith only [h₁,h₂,h₃,h₄,h,ha,ha₀,he]
  · have h₁ := (discrepancy (7/16*a)).2
    have h₂ := (discrepancy (1/8*a)).1
    have h₃ := (discrepancy (7/8*a)).2
    have h₄ := (discrepancy (9/16*a)).1
    have h : 4 < a := lt_of_not_ge hb
    unfold loss
    linarith only [h₁,h₂,h₃,h₄,h]

theorem unit_dist {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    distInt x = min x (1-x) := by
  by_cases h : x < 1/2
  · have hr : round x = 0 := round_eq_zero_iff.mpr ⟨by linarith,h⟩
    simp only [distInt,hr,Int.cast_zero,sub_zero,abs_of_nonneg hx,min_eq_left (by linarith : x ≤ 1-x)]
  · have hr : round x = 1 := by
      rw [round_eq,Int.floor_eq_iff]
      norm_num
      constructor <;> linarith
    simp only [distInt,hr,Int.cast_one,abs_of_nonpos (sub_nonpos.mpr hx'),
      min_eq_right (by linarith : 1-x ≤ x)]
    ring

private theorem badPair_iff (x : ℝ) :
    x ∈ badPair ↔ distInt x ≤ 1/8 ∨ distInt (2*x) ≤ 1/8 := by
  let y := Int.fract x
  have h0 : 0 ≤ y := Int.fract_nonneg x
  have h1 : y ≤ 1 := (Int.fract_lt_one x).le
  have e1 : x = y+(⌊x⌋:ℝ) := (Int.fract_add_floor x).symm
  have e2 : 2*x = 2*y+((2*⌊x⌋:ℤ):ℝ) := by push_cast; linarith
  rw [e2,distInt_add_int]
  have hdx : distInt x = distInt y := by nth_rw 1 [e1]; exact distInt_add_int _ _
  rw [hdx,unit_dist h0 h1]
  change y ∈ badBase ↔ _
  by_cases h : y ≤ 1/2
  · rw [unit_dist (by linarith : 0 ≤ 2*y) (by linarith : 2*y ≤ 1)]
    simp only [badBase,mem_union,mem_Icc,min_le_iff]
    grind
  · have hh : distInt (2*y) = distInt (2*y-1) := by
      have he : 2*y = (2*y-1)+((1:ℤ):ℝ) := by norm_num
      nth_rw 1 [he]
      exact distInt_add_int _ _
    rw [hh,unit_dist (by linarith : 0 ≤ 2*y-1) (by linarith : 2*y-1 ≤ 1)]
    simp only [badBase,mem_union,mem_Icc,min_le_iff]
    grind

def pairedWindow : Set ℝ := Ioo (1/8) (7/16) ∪ Ioo (9/16) (7/8)

private theorem pairedWindow_pinned {t : ℝ} (ht : t ∈ pairedWindow) :
    InWindows t ∧ InWindows (2*t) ∧ (1/8:ℝ) < distInt t ∧ (1/8:ℝ) < distInt (2*t) := by
  have h0 : 0 ≤ t := by rcases ht with h | h <;> linarith [h.1]
  have h1 : t < 1 := by rcases ht with h | h <;> linarith [h.2]
  have hc : t ∉ badPair := by
    rw [badPair,mem_preimage,Int.fract_eq_self.mpr ⟨h0,h1⟩]
    rcases ht with ht | ht <;> simp only [badBase,mem_union,mem_Icc] <;>
      rcases ht with ⟨hL,hU⟩ <;> grind
  rw [badPair_iff] at hc
  push Not at hc
  refine ⟨Or.inl ⟨by rcases ht with h | h <;> linarith [h.1],
    by rcases ht with h | h <;> linarith [h.2]⟩,?_,hc⟩
  rcases ht with ht | ht
  · exact Or.inl ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · exact Or.inr ⟨by linarith [ht.1],by linarith [ht.2]⟩

private theorem scaled_bad_int (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    (∫ t in u..v, badFn (a*t)) = (primitive (a*v)-primitive (a*u))/a := by
  rw [intervalIntegral.integral_comp_mul_left badFn ha.ne', smul_eq_mul,← div_eq_inv_mul]
  congr 1
  unfold primitive
  linarith [intervalIntegral.integral_add_adjacent_intervals (bad_int 0 (a*u)) (bad_int (a*u) (a*v))]

set_option maxHeartbeats 500000 in
/-- Every pair of slow rates above the pinned rate has a strictly clear
time and double time in the two windows. -/
theorem three_slow_pair {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ t ∈ pairedWindow, (1/8:ℝ) < distInt (a*t) ∧ (1/8:ℝ) < distInt (a*(2*t)) ∧
      (1/8:ℝ) < distInt (b*t) ∧ (1/8:ℝ) < distInt (b*(2*t)) := by
  by_contra! h
  have ha' : 0 < a := zero_lt_one.trans_le ha
  have hb' : 0 < b := zero_lt_one.trans_le hb
  have hin (u v : ℝ) (huv : u ≤ v) (hW : Ioo u v ⊆ pairedWindow) :
      v-u ≤ (∫ t in u..v, badFn (a*t))+(∫ t in u..v, badFn (b*t)) := by
    have hI (c : ℝ) (hc : 0 < c) : IntervalIntegrable (fun t => badFn (c*t)) volume u v := by
      simpa only [mul_div_cancel_left₀ _ hc.ne'] using (bad_int (c*u) (c*v)).comp_mul_left (c := c)
    have he := intervalIntegral.integral_mono_on_of_le_Ioo huv
      (intervalIntegrable_const (c := (1:ℝ))) ((hI a ha').add (hI b hb')) (by
        intro t ht
        have hh := h t (hW ht)
        by_cases hA : a*t ∈ badPair
        · by_cases hB : b*t ∈ badPair <;> norm_num [badFn,hA,hB]
        have hB : b*t ∈ badPair := by
          rw [badPair_iff] at hA ⊢
          push Not at hA
          have haa : (1/8:ℝ) < distInt (a*(2*t)) := by
            rw [← mul_assoc,mul_comm a 2,mul_assoc]
            exact hA.2
          have hh' := hh hA.1 haa
          rw [mul_left_comm b 2 t] at hh'
          by_cases hbc : distInt (b*t) ≤ 1/8
          · exact Or.inl hbc
          · exact Or.inr (hh' (lt_of_not_ge hbc))
        norm_num [badFn,hA,hB])
    change (∫ t in u..v, (1:ℝ)) ≤ (∫ t in u..v, badFn (a*t)+badFn (b*t)) at he
    rw [intervalIntegral.integral_add (hI a ha') (hI b hb')] at he
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using he
  have h1 := hin (1/8) (7/16) (by norm_num) (subset_union_left)
  have h2 := hin (9/16) (7/8) (by norm_num) (subset_union_right)
  rw [scaled_bad_int a ha',scaled_bad_int b hb'] at h1 h2
  simp_rw [mul_comm a, mul_comm b] at h1 h2
  have h₁ := (div_lt_iff₀ ha').2 (paired_slow_loss_lt_half ha)
  have h₂ := (div_lt_iff₀ hb').2 (paired_slow_loss_lt_half hb)
  unfold loss at h₁ h₂
  simp only [sub_div,add_div] at h₁ h₂ h1 h2
  linarith only [h₁,h₂,h1,h2]

def slowOK (a b t : ℝ) : Prop :=
  InWindows t ∧ (1/8:ℝ) ≤ distInt t ∧ (1/8:ℝ) ≤ distInt (a*t) ∧
    (1/8:ℝ) ≤ distInt (b*t)

/-- A compact parameter domain turns pointwise strict feasibility into
a single positive interval radius. -/
theorem uniform_interval_in_open {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) {G : Set (X × ℝ)} (hG : IsOpen G)
    (h : ∀ x ∈ K, ∃ t : ℝ, (x,t) ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ t : ℝ,
      ∀ s ∈ Icc (t-δ) (t+δ), (x,s) ∈ G := by
  classical
  let P := {p : X × ℝ × ℝ // 0 < p.2.2 ∧
    Metric.ball (p.1,p.2.1) p.2.2 ⊆ G}
  let U (p : P) : Set X := Metric.ball p.val.1 (p.val.2.2/2)
  have hU : K ⊆ ⋃ p : P, U p := by
    intro x hx
    obtain ⟨t,ht⟩ := h x hx
    obtain ⟨r,hr,hr'⟩ := Metric.isOpen_iff.mp hG (x,t) ht
    exact mem_iUnion.mpr ⟨⟨(x,t,r),hr,hr'⟩,Metric.mem_ball_self (by positivity)⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover
    U (fun _ => Metric.isOpen_ball) hU
  have hsmall (s : Finset P) : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ s, δ ≤ p.val.2.2/2 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert p s _ ih =>
      obtain ⟨δ,hδ,hle⟩ := ih
      have hp : 0 < p.val.2.2/2 := half_pos p.property.1
      refine ⟨min δ (p.val.2.2/2),lt_min hδ hp,fun q hq => ?_⟩
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle q hq)
  obtain ⟨δ,hδ,hle⟩ := hsmall S
  refine ⟨δ,hδ,fun x hx => ?_⟩
  obtain ⟨p,hp,hpu⟩ := mem_iUnion₂.mp (hS hx)
  refine ⟨p.val.2.1,fun s hs => ?_⟩
  have hs' : |s-p.val.2.1| ≤ δ := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hr : p.val.2.2/2 < p.val.2.2 := by linarith [p.property.1]
  apply p.property.2
  change dist (x,s) (p.val.1,p.val.2.1) < p.val.2.2
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨(Metric.mem_ball.mp hpu).trans hr,
      ((by simpa only [Real.dist_eq] using hs' :
        dist s p.val.2.1 ≤ δ).trans (hle p hp)).trans_lt hr⟩

private theorem compact_paired_intervals (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ B → 1 ≤ b → b ≤ B →
      ∃ t : ℝ, ∀ s ∈ Icc (t-δ) (t+δ), slowOK a b s ∧ slowOK a b (2*s) := by
  classical
  let K : Set (ℝ×ℝ) := Icc 1 B ×ˢ Icc 1 B
  let G : Set ((ℝ×ℝ)×ℝ) := {x | x.2 ∈ pairedWindow ∧
    (1/8:ℝ) < distInt (x.1.1*x.2) ∧ (1/8:ℝ) < distInt (x.1.1*(2*x.2)) ∧
    (1/8:ℝ) < distInt (x.1.2*x.2) ∧ (1/8:ℝ) < distInt (x.1.2*(2*x.2))}
  have hc : Continuous distInt := by
    have h := (AddCircle.continuous_mk' (1:ℝ)).norm
    convert h using 1
    funext x
    exact UnitAddCircle.norm_eq.symm
  have hG : IsOpen G := by
    apply IsOpen.inter (isOpen_Ioo.union isOpen_Ioo |>.preimage continuous_snd)
    exact (isOpen_lt continuous_const (hc.comp (by fun_prop))).inter
      ((isOpen_lt continuous_const (hc.comp (by fun_prop))).inter
        ((isOpen_lt continuous_const (hc.comp (by fun_prop))).inter
          (isOpen_lt continuous_const (hc.comp (by fun_prop)))))
  obtain ⟨δ,hδ,h⟩ := uniform_interval_in_open
    (isCompact_Icc.prod isCompact_Icc : IsCompact K) hG (by
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      exact three_slow_pair ha.1 hb.1)
  refine ⟨δ,hδ,fun a b ha haB hb hbB => ?_⟩
  obtain ⟨t,ht⟩ := h (a,b) ⟨⟨ha,haB⟩,⟨hb,hbB⟩⟩
  refine ⟨t,fun s hs => ?_⟩
  have hg := ht s hs
  obtain ⟨hW,ha1,ha2,hb1,hb2⟩ := hg
  obtain ⟨hw1,hw2,hp1,hp2⟩ := pairedWindow_pinned hW
  exact ⟨⟨hw1,hp1.le,ha1.le,hb1.le⟩,⟨hw2,hp2.le,ha2.le,hb2.le⟩⟩

/-- The four-row alternative is impossible for four fast readings:
their exact kernel would be zero and could not contain a positive point. -/
theorem four_fast_window (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ B → 1 ≤ b → b ≤ B →
      ∀ v : Fin 4 → ℝ, (∀ i, C < v i) →
        ∃ t : ℝ, slowOK a b t ∧ ∀ i, (1/8:ℝ) < distInt (v i*t) := by
  obtain ⟨δ,hδ,h⟩ := compact_paired_intervals B
  obtain ⟨N,E,C,_,hC,hv⟩ := buffered_clear_or_finite_kernels 4 (show 0 < 2*δ by positivity)
  refine ⟨C,hC,fun a b ha haB hb hbB v hf => ?_⟩
  obtain ⟨t,ht⟩ := h a b ha haB hb hbB
  rcases hv v (t-δ) (t+δ) (by linarith) hf with ⟨s,hs,hq⟩ | ⟨A,w,hw,_,hpos,hdim⟩
  · rcases hq with hq | hq
    · exact ⟨s,(ht s hs).1,hq⟩
    · refine ⟨2*s,(ht s hs).2,fun i => ?_⟩
      rw [← mul_assoc, mul_comm (v i) 2, mul_assoc]
      exact hq i
  · have hz : Module.finrank ℝ (LinearMap.ker (evaluate (tableRows A))) = 0 := hdim
    rw [Submodule.finrank_eq_zero.mp hz,Submodule.mem_bot] at hw
    subst w
    exact (lt_irrefl (0:ℝ) (hpos 0)).elim

/-- Every sorted normalized input either clears, enters a finite family
of line or plane neighborhoods, or has four bounded smallest readings. -/
theorem normalized_four_fast_dispatch :
    ∃ (B : ℝ) (N₅ N₆ : ℕ) (E₅ E₆ : ℝ), 1 ≤ B ∧ 0 ≤ E₅ ∧ 0 ≤ E₆ ∧
      ∀ (a b : ℝ) (v : Fin 4 → ℝ), 1 ≤ a → a ≤ b → (∀ i, b ≤ v i) → Monotone v →
        (∃ t : ℝ, slowOK a b t ∧ ∀ i, (1/8:ℝ) ≤ distInt (v i*t)) ∨
        NearKernelType N₅ E₅ (Fin.cons b v) ∨
        NearKernelType N₆ E₆ (Fin.cons a (Fin.cons b v)) ∨ v 0 ≤ B := by
  obtain ⟨B,N₅,N₆,E₅,E₆,hB,hE₅,hE₆,h⟩ := normalized_fast_dispatch
  obtain ⟨C,_,hc⟩ := four_fast_window B
  refine ⟨max B C,N₅,N₆,E₅,E₆,hB.trans (le_max_left _ _),hE₅,hE₆,
    fun a b v ha hab hv hm => ?_⟩
  rcases h a b v ha hab hv with ⟨t,hW,hp,ha',hb',hf⟩ | h₅ | h₆ | hb
  · exact Or.inl ⟨t,⟨hW,hp,ha',hb'⟩,hf⟩
  · exact Or.inr (Or.inl h₅)
  · exact Or.inr (Or.inr (Or.inl h₆))
  by_cases hf : C < v 0
  · obtain ⟨t,ht,hw⟩ := hc a b ha (hab.trans hb) (ha.trans hab) hb v
      (fun i => hf.trans_le (hm (Fin.zero_le i)))
    exact Or.inl ⟨t,ht,fun i => (hw i).le⟩
  · exact Or.inr (Or.inr (Or.inr ((le_of_not_gt hf).trans (le_max_right _ _))))

#print axioms primitive_formula
#print axioms discrepancy
#print axioms three_slow_pair
#print axioms four_fast_window
#print axioms normalized_four_fast_dispatch

end
end Fresh.FiniteRelations
