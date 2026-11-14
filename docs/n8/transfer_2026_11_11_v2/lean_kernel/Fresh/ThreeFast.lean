import Fresh.PairedSlow

namespace Fresh.FiniteRelations

open Set MeasureTheory Fresh.Cascade Fresh.Harmonic
open scoped BigOperators

noncomputable section

private def singleBad : Set ℝ := {x | distInt x ≤ 1/8}
private def singleFn : ℝ → ℝ := singleBad.indicator (fun _ => 1)
private def singlePrimitive (x : ℝ) : ℝ := ∫ t in 0..x, singleFn t

private theorem continuous_clearance : Continuous distInt := by
  have h := (AddCircle.continuous_mk' (1:ℝ)).norm
  convert h using 1
  funext x
  exact UnitAddCircle.norm_eq.symm

private theorem single_meas : MeasurableSet singleBad :=
  (isClosed_le continuous_clearance continuous_const).measurableSet

private theorem single_integrable (a b : ℝ) : IntervalIntegrable singleFn volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
  · exact (measurable_const.indicator single_meas).aestronglyMeasurable
  · filter_upwards with t
    unfold singleFn
    by_cases h : t ∈ singleBad <;> simp [h]

private theorem single_periodic : Function.Periodic singleFn 1 := by
  intro t
  have h : t+1 ∈ singleBad ↔ t ∈ singleBad := by
    change distInt (t+1) ≤ 1/8 ↔ distInt t ≤ 1/8
    rw [show (1:ℝ) = ((1:ℤ):ℝ) by norm_num,distInt_add_int]
  unfold singleFn
  by_cases ht : t ∈ singleBad
  · rw [indicator_of_mem (h.mpr ht),indicator_of_mem ht]
  · rw [indicator_of_notMem (fun h' => ht (h.mp h')),indicator_of_notMem ht]

private theorem single_base (x : ℝ) (hx : x ∈ Icc 0 1) :
    singlePrimitive x = min x (1/8) + max 0 (x-7/8) := by
  let f (a b : ℝ) := (Icc a b).indicator (fun _ => (1:ℝ))
  have hi (a b : ℝ) : IntervalIntegrable (f a b) volume 0 x := by
    apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
    · exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    · filter_upwards with y
      unfold f
      by_cases h : y ∈ Icc a b <;> simp [h]
  have he : (∫ t in 0..x, singleFn t) =
      ∫ t in 0..x, f 0 (1/8) t + f (7/8) 1 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    have ht1 := ht.2.trans hx.2
    have hmem : t ∈ singleBad ↔ t ∈ Icc (0:ℝ) (1/8) ∪ Icc (7/8:ℝ) 1 := by
      change distInt t ≤ _ ↔ _
      rw [unit_dist ht.1 ht1,min_le_iff]
      simp only [mem_union,mem_Icc]
      grind
    by_cases hA : t ∈ Icc (0:ℝ) (1/8)
    · have hB : t ∉ Icc (7/8:ℝ) 1 := fun h => by linarith [hA.2,h.1]
      simp only [singleFn,f,indicator_of_mem (hmem.mpr (Or.inl hA)),
        indicator_of_mem hA,indicator_of_notMem hB,add_zero]
    · by_cases hB : t ∈ Icc (7/8:ℝ) 1
      · simp only [singleFn,f,indicator_of_mem (hmem.mpr (Or.inr hB)),
          indicator_of_notMem hA,indicator_of_mem hB,zero_add]
      · have hP : t ∉ singleBad := fun h => (hmem.mp h).elim hA hB
        simp only [singleFn,f,indicator_of_notMem hP,indicator_of_notMem hA,
          indicator_of_notMem hB,zero_add]
  unfold singlePrimitive
  rw [he,intervalIntegral.integral_add (hi 0 (1/8)) (hi (7/8) 1)]
  simp only [f,indicator_interval _ _ x (by norm_num : (0:ℝ) ≤ 0) hx.1,
    indicator_interval _ _ x (by norm_num : (0:ℝ) ≤ 7/8) hx.1]
  have hmin : 0 ≤ min (1/8:ℝ) x := le_min (by norm_num) hx.1
  rw [min_eq_right hx.2,sub_zero,max_eq_right hmin,min_comm (1/8:ℝ) x]

private theorem single_formula (x : ℝ) :
    singlePrimitive x = (⌊x⌋:ℝ)/4 + min (Int.fract x) (1/8) + max 0 (Int.fract x-7/8) := by
  have hp : (∫ t in 0..1, singleFn t) = 1/4 := by
    change singlePrimitive 1 = _
    rw [single_base 1 (by norm_num)]
    norm_num
  have he := single_base (Int.fract x) ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  unfold singlePrimitive
  rw [periodic_primitive_fract single_periodic single_integrable,hp]
  change _ + singlePrimitive (Int.fract x) = _
  rw [he]
  ring

private theorem single_discrepancy (x : ℝ) :
    -(3/32:ℝ) ≤ singlePrimitive x - x/4 ∧ singlePrimitive x - x/4 ≤ 3/32 := by
  rw [single_formula]
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  have he := Int.fract_add_floor x
  generalize Int.fract x = t at *
  simp only [min_def,max_def]
  split_ifs <;> constructor <;> linarith

private theorem single_nonneg (t : ℝ) : 0 ≤ singleFn t := by
  unfold singleFn
  by_cases h : t ∈ singleBad <;> simp [h]

private theorem single_mono : Monotone singlePrimitive := by
  intro a b hab
  have h := intervalIntegral.integral_nonneg (μ := volume) hab (fun t _ => single_nonneg t)
  unfold singlePrimitive
  linarith only [h,intervalIntegral.integral_add_adjacent_intervals
    (single_integrable 0 a) (single_integrable a b)]

private theorem scaled_single (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    (∫ t in u..v, singleFn (a*t)) = (singlePrimitive (a*v)-singlePrimitive (a*u))/a := by
  rw [intervalIntegral.integral_comp_mul_left singleFn ha.ne', smul_eq_mul,← div_eq_inv_mul]
  congr 1
  unfold singlePrimitive
  linarith [intervalIntegral.integral_add_adjacent_intervals
    (single_integrable 0 (a*u)) (single_integrable (a*u) (a*v))]

private theorem scaled_single_integrable (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    IntervalIntegrable (fun t => singleFn (a*t)) volume u v := by
  simpa only [mul_div_cancel_left₀ _ ha.ne'] using
    (single_integrable (a*u) (a*v)).comp_mul_left (c := a)

private theorem scaled_loss_bound (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    (∫ t in u..v, singleFn (a*t)) ≤ (v-u)/4 + (3/16)/a := by
  rw [scaled_single a ha]
  apply (div_le_iff₀ ha).2
  have h1 := (single_discrepancy (a*v)).2
  have h2 := (single_discrepancy (a*u)).1
  rw [add_mul,div_mul_cancel₀ _ ha.ne']
  nlinarith only [h1,h2]

/-- A single reading above the pinned one loses less than a quarter
of a unit of time in the pinned first window. -/
private theorem first_window_loss (a : ℝ) (ha : 1 ≤ a) :
    (∫ t in (1/8:ℝ)..(7/8:ℝ), singleFn (a*t)) < 1/4 := by
  have ha' : 0 < a := zero_lt_one.trans_le ha
  rcases eq_or_lt_of_le ha with rfl | ha1
  · rw [scaled_single 1 (by norm_num)]
    norm_num [single_formula, Int.fract, Int.floor_eq_iff]
  by_cases h2 : a ≤ 2
  · rw [scaled_single a ha']
    apply (div_lt_iff₀ ha').2
    have hl := single_mono (show (1/8:ℝ) ≤ a*(1/8) by linarith)
    have hu := single_mono (show a*(7/8) ≤ (7/4:ℝ) by linarith)
    rw [single_formula (1/8)] at hl
    rw [single_formula (7/4)] at hu
    norm_num [Int.fract, Int.floor_eq_iff] at hl hu
    linarith
  by_cases h3 : a ≤ 3
  · rw [scaled_single a ha']
    apply (div_lt_iff₀ ha').2
    have hl := single_mono (show (1/8:ℝ) ≤ a*(1/8) by linarith)
    have hu := single_mono (show a*(7/8) ≤ (21/8:ℝ) by linarith)
    rw [single_formula (1/8)] at hl
    rw [single_formula (21/8)] at hu
    norm_num [Int.fract, Int.floor_eq_iff] at hl hu
    linarith [lt_of_not_ge h2]
  apply (scaled_loss_bound a ha' _ _).trans_lt
  have h : (3/16:ℝ)/a < 1/16 := (div_lt_iff₀ ha').2 (by linarith)
  linarith

private theorem count_cover {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (u v : ℝ) (huv : u ≤ v) (h : ∀ t ∈ Ioo u v, ∃ i, t*r i ∈ singleBad) :
    v-u ≤ ∑ i, ∫ t in u..v, singleFn (r i*t) := by
  have hi : IntervalIntegrable (fun t => ∑ i, singleFn (r i*t)) volume u v := by
    have heq : (∑ i, (fun t => singleFn (r i*t))) =
        (fun t => ∑ i, singleFn (r i*t)) := by
      funext t
      rw [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum Finset.univ fun i _ => scaled_single_integrable (r i) (hr i) u v
  have he := intervalIntegral.integral_mono_on_of_le_Ioo huv
    (intervalIntegrable_const (c := (1:ℝ))) hi (by
      intro t ht
      obtain ⟨i,hi⟩ := h t ht
      rw [mul_comm] at hi
      have he : singleFn (r i*t) = 1 := indicator_of_mem hi _
      exact he ▸ Finset.single_le_sum (f := fun j => singleFn (r j*t))
        (fun j _ => single_nonneg _) (Finset.mem_univ i))
  rw [intervalIntegral.integral_finset_sum (fun i _ => scaled_single_integrable (r i) (hr i) u v)] at he
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using he

/-- Four slow readings including the pinned reading have a strict
first-window witness, for arbitrary real rates. -/
theorem four_slow_strict (r : Fin 3 → ℝ) (hr : ∀ i, 1 ≤ r i) :
    ∃ t ∈ Ioo (1/8:ℝ) (7/8), ∀ i, (1/8:ℝ) < distInt (r i*t) := by
  by_contra! h
  have hc := count_cover r (fun i => zero_lt_one.trans_le (hr i)) (1/8) (7/8) (by norm_num) (by
    intro t ht
    obtain ⟨i,hi⟩ := h t ht
    exact ⟨i,by simpa only [singleBad,mem_setOf_eq,mul_comm] using hi⟩)
  have h₀ := first_window_loss (r 0) (hr 0)
  have h₁ := first_window_loss (r 1) (hr 1)
  have h₂ := first_window_loss (r 2) (hr 2)
  rw [Fin.sum_univ_three] at hc
  linarith

/-- Three arbitrarily related fast readings cannot cover a fixed interval. -/
theorem three_fast_on_interval (r : Fin 3 → ℝ) {u v ℓ : ℝ} (hℓ : 0 < ℓ) (h : ℓ ≤ v-u)
    (hr : ∀ i, 3/ℓ < r i) :
    ∃ t ∈ Ioo u v, ∀ i, (1/8:ℝ) < distInt (r i*t) := by
  have hp (i : Fin 3) : 0 < r i := (by positivity : 0 < 3/ℓ).trans (hr i)
  by_contra! hn
  have hc := count_cover r hp u v (by linarith) (by
    intro t ht
    obtain ⟨i,hi⟩ := hn t ht
    exact ⟨i,by simpa only [singleBad,mem_setOf_eq,mul_comm] using hi⟩)
  have hb (i : Fin 3) : (∫ t in u..v, singleFn (r i*t)) < (v-u)/3 := by
    apply (scaled_loss_bound (r i) (hp i) _ _).trans_lt
    have hh := (div_lt_iff₀ hℓ).1 (hr i)
    have he : (3/16:ℝ)/r i < ℓ/16 := (div_lt_iff₀ (hp i)).2 (by nlinarith only [hh])
    linarith
  rw [Fin.sum_univ_three] at hc
  linarith only [hb 0,hb 1,hb 2,hc]

/-- One interval argument serves every fast block of size at most three. -/
theorem at_most_three_fast_on_interval {n : ℕ} (hn : n ≤ 3) (r : Fin n → ℝ)
    {u v ℓ : ℝ} (hℓ : 0 < ℓ) (h : ℓ ≤ v-u) (hr : ∀ i, 3/ℓ < r i) :
    ∃ t ∈ Ioo u v, ∀ i, (1/8:ℝ) < distInt (r i*t) := by
  let f (i : Fin 3) : ℝ := if hi : i.val < n then r ⟨i.val,hi⟩ else 3/ℓ+1
  have hf (i : Fin 3) : 3/ℓ < f i := by
    unfold f
    split
    · exact hr _
    · linarith
  obtain ⟨t,ht,h⟩ := three_fast_on_interval f hℓ h hf
  refine ⟨t,ht,fun i => ?_⟩
  have he : f (Fin.castLE hn i) = r i := by simp [f,i.isLt]
  exact he ▸ h (Fin.castLE hn i)

/-- On a compact domain of slow rates it suffices to find a single
strict point in an open window. The resulting uniform cutoff appends
any block of at most three fast rates. -/
theorem fast_append_of_open_window {k n : ℕ} (hn : n ≤ 3) (B : ℝ)
    (W : Set ℝ) (hW : IsOpen W)
    (hslow : ∀ r : Fin k → ℝ, (∀ i, 1 ≤ r i) → (∀ i, r i ≤ B) →
      ∃ t ∈ W, ∀ i, (1/8:ℝ) < distInt (r i*t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin k → ℝ) (v : Fin n → ℝ),
      (∀ i, 1 ≤ r i) → (∀ i, r i ≤ B) → (∀ i, C < v i) →
      ∃ t ∈ W, (∀ i, (1/8:ℝ) < distInt (r i*t)) ∧
        (∀ i, (1/8:ℝ) < distInt (v i*t)) := by
  let K : Set (Fin k → ℝ) := Icc 1 (fun _ => B)
  let G : Set ((Fin k → ℝ) × ℝ) := {p | p.2 ∈ W ∧
    ∀ i, (1/8:ℝ) < distInt (p.1 i*p.2)}
  have hG : IsOpen G := by
    have he : G = (Prod.snd ⁻¹' W) ∩
        ⋂ i : Fin k, {p : (Fin k → ℝ) × ℝ | (1/8:ℝ) < distInt (p.1 i*p.2)} := by
      ext p
      simp only [G, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iInter]
    rw [he]
    exact (hW.preimage continuous_snd).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_clearance.comp (by fun_prop)))
  obtain ⟨δ,hδ,h⟩ := uniform_interval_in_open (isCompact_Icc : IsCompact K) hG (by
    intro r hr
    exact hslow r hr.1 hr.2)
  refine ⟨3/(2*δ),by positivity,fun r v hr hrB hv => ?_⟩
  obtain ⟨t,ht⟩ := h r ⟨hr,hrB⟩
  obtain ⟨s,hs,hf⟩ := at_most_three_fast_on_interval hn v (show 0 < 2*δ by positivity)
    (u := t-δ) (v := t+δ) (by linarith) hv
  obtain ⟨hw,hr'⟩ := ht s ⟨hs.1.le,hs.2.le⟩
  exact ⟨s,hw,hr',hf⟩

/-- Sufficiently fast triples over four bounded slow readings always
clear inside the first window. -/
theorem three_fast_window (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r v : Fin 3 → ℝ), (∀ i, 1 ≤ r i) → (∀ i, r i ≤ B) →
      (∀ i, C < v i) →
      ∃ t ∈ Ioo (1/8:ℝ) (7/8), (∀ i, (1/8:ℝ) < distInt (r i*t)) ∧
        (∀ i, (1/8:ℝ) < distInt (v i*t)) :=
  fast_append_of_open_window (by decide : 3 ≤ 3) B _ isOpen_Ioo
    (fun r hr _ => four_slow_strict r hr)

/-- The remaining unclassified tail has at most two unbounded rates.
The five- and six-fast alternatives retain their finite line and plane
types. -/
theorem normalized_three_fast_dispatch :
    ∃ (B : ℝ) (N₅ N₆ : ℕ) (E₅ E₆ : ℝ), 1 ≤ B ∧ 0 ≤ E₅ ∧ 0 ≤ E₆ ∧
      ∀ (a b c : ℝ) (v : Fin 3 → ℝ), 1 ≤ a → a ≤ b → b ≤ c →
        (∀ i, c ≤ v i) → Monotone v →
        (∃ t : ℝ, slowOK a b t ∧ (1/8:ℝ) ≤ distInt (c*t) ∧
          ∀ i, (1/8:ℝ) ≤ distInt (v i*t)) ∨
        NearKernelType N₅ E₅ (Fin.cons b (Fin.cons c v)) ∨
        NearKernelType N₆ E₆ (Fin.cons a (Fin.cons b (Fin.cons c v))) ∨ v 0 ≤ B := by
  obtain ⟨B,N₅,N₆,E₅,E₆,hB,hE₅,hE₆,h⟩ := normalized_four_fast_dispatch
  obtain ⟨C,_,hc⟩ := three_fast_window B
  refine ⟨max B C,N₅,N₆,E₅,E₆,hB.trans (le_max_left _ _),hE₅,hE₆,
    fun a b c v ha hab hbc hv hm => ?_⟩
  let f : Fin 4 → ℝ := Fin.cons c v
  have hbv (i : Fin 4) : b ≤ f i := Fin.cases hbc (fun j => hbc.trans (hv j)) i
  have hfm : Monotone f := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · intro _
      exact Fin.cases le_rfl (fun j' => hv j') j
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij
        have hn : ¬ i'.succ ≤ (0:Fin 4) := by simp
        exact (hn hij).elim
      · intro hij
        exact hm (Fin.succ_le_succ_iff.mp hij)
  rcases h a b f ha hab hbv hfm with ⟨t,ht,hf⟩ | h₅ | h₆ | hb
  · exact Or.inl ⟨t,ht,hf 0,fun i => hf i.succ⟩
  · exact Or.inr (Or.inl h₅)
  · exact Or.inr (Or.inr (Or.inl h₆))
  by_cases hf : C < v 0
  · let r : Fin 3 → ℝ := ![a,b,c]
    have hr (i : Fin 3) : 1 ≤ r i := by
      fin_cases i
      · exact ha
      · exact ha.trans hab
      · exact ha.trans (hab.trans hbc)
    have hrB (i : Fin 3) : r i ≤ B := by
      fin_cases i
      · exact (hab.trans hbc).trans hb
      · exact hbc.trans hb
      · exact hb
    obtain ⟨t,ht,hslow,hfast⟩ := hc r v hr hrB (fun i => hf.trans_le (hm (Fin.zero_le i)))
    have hpin : (1/8:ℝ) < distInt t := by
      rw [unit_dist (by linarith [ht.1]) (by linarith [ht.2]),lt_min_iff]
      exact ⟨ht.1,by linarith [ht.2]⟩
    exact Or.inl ⟨t,⟨Or.inl ⟨ht.1.le,ht.2.le⟩,hpin.le,(hslow 0).le,(hslow 1).le⟩,
      (hslow 2).le,fun i => (hfast i).le⟩
  · exact Or.inr (Or.inr (Or.inr ((le_of_not_gt hf).trans (le_max_right _ _))))

#print axioms four_slow_strict
#print axioms three_fast_on_interval
#print axioms fast_append_of_open_window
#print axioms three_fast_window
#print axioms normalized_three_fast_dispatch

end
end Fresh.FiniteRelations
