import LonelyRunner.LRC.Spec.DoubleBacktrackN

/-!
# Forced earlier labels and disjoint obstruction classes

An incompatible lower opening and upper deadline force an earlier label;
the old known clear event bounds this diagnostic below. This does not prove
that its returned window differs from the old one or extends the deformation.

For an old clear reading, capture at multipliers 2, 3, and 5 has pairwise
disjoint phase ranges. These scalar facts do not assert simultaneous clearance.
-/

namespace LRC.DeadlineRelabel

/-- Any clear candidate at or before U is forced below this computed label. -/
theorem label_bound_before_deadline {d u U : ℝ} (q : ℤ)
    (hd : 0 ≤ d) (hu : u ≤ U) (hl : (q : ℝ)+1/8 ≤ d*u) :
    q ≤ ⌊d*U-1/8⌋ := by
  apply Int.le_floor.mpr
  have := mul_le_mul_of_nonneg_left hu hd
  linarith

/-- If the current opening lies after the deadline, its label must drop. -/
theorem forced_label_drop {d U : ℝ} (p : ℤ)
    (hconflict : d*U < (p : ℝ)+1/8) : ⌊d*U-1/8⌋ < p := by
  apply Int.floor_lt.mpr
  linarith

/-- Recomputing at a time before every current closing never increases a label. -/
theorem label_update_le {d U : ℝ} (p : ℤ)
    (hupper : d*U ≤ (p : ℝ)+7/8) : ⌊d*U-1/8⌋ ≤ p := by
  have h : ⌊d*U-1/8⌋ < p+1 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith
  omega

/-- Exact decrease of labels in a failed intersection. The lower bound comes
from a known OLD event, not from an assumed future isolation. -/
theorem relabel_bounds (S : Finset ι) (d : ι → ℝ) (q p : ι → ℤ)
    {t U : ℝ} (hd : ∀ i ∈ S, 0 ≤ d i) (htU : t ≤ U)
    (hold : ∀ i ∈ S, (q i : ℝ)+1/8 ≤ d i*t)
    (hupper : ∀ i ∈ S, d i*U ≤ (p i : ℝ)+7/8)
    (hconflict : ∃ i ∈ S, d i*U < (p i : ℝ)+1/8) :
    (∀ i ∈ S, q i ≤ ⌊d i*U-1/8⌋ ∧ ⌊d i*U-1/8⌋ ≤ p i) ∧
      (∑ i ∈ S, ⌊d i*U-1/8⌋) < ∑ i ∈ S, p i := by
  constructor
  · intro i hi
    exact ⟨label_bound_before_deadline (q i) (hd i hi) htU (hold i hi),
      label_update_le (p i) (hupper i hi)⟩
  · apply Finset.sum_lt_sum (fun i hi => label_update_le (p i) (hupper i hi))
    obtain ⟨i, hi, hc⟩ := hconflict
    exact ⟨i, hi, forced_label_drop (p i) hc⟩

/-- Tripling clears every old middle phase which could block doubling. -/
theorem triple_clears_middle {f : ℝ} (hl : 7/16 ≤ f) (hu : f ≤ 9/16) :
    (8 : ℝ)⁻¹ ≤ circDist (3*f) := by
  apply TwoPinner.clear_of_band (N := 1) <;> norm_num <;> linarith

/-- Multiplication by five clears those same middle phases. -/
theorem five_clears_middle {f : ℝ} (hl : 7/16 ≤ f) (hu : f ≤ 9/16) :
    (8 : ℝ)⁻¹ ≤ circDist (5*f) := by
  apply TwoPinner.clear_of_band (N := 2) <;> norm_num <;> linarith

/-- A doubled blocker has precisely the old middle-phase obstruction. -/
theorem double_blocker_middle {f : ℝ} (hl : 1/8 ≤ f) (hu : f ≤ 7/8)
    (hb : circDist (2*f) < (8 : ℝ)⁻¹) : 7/16 < f ∧ f < 9/16 := by
  have he := DoubleBacktrack.doubled_clear_iff (x := f) 0
    (by simpa using hl) (by simpa using hu)
  simp only [Int.cast_zero, sub_zero] at he
  have hn : ¬ (f ≤ 7/16 ∨ 9/16 ≤ f) := fun h => (not_le_of_gt hb) (he.mpr h)
  constructor <;> by_contra h <;> apply hn <;> simp only [not_lt] at h
  · exact Or.inl h
  · exact Or.inr h

/-- The two possible tripled capture slots within an old clear phase. -/
theorem triple_blocker_ranges {f : ℝ} (hl : 1/8 ≤ f) (hu : f ≤ 7/8)
    (hb : circDist (3*f) < (8 : ℝ)⁻¹) :
    (7/24 < f ∧ f < 3/8) ∨ (5/8 < f ∧ f < 17/24) := by
  by_cases h1 : f ≤ 7/24
  · have hc : (8 : ℝ)⁻¹ ≤ circDist (3*f) := by
      apply TwoPinner.clear_of_band (N := 0) <;> norm_num <;> linarith
    exact False.elim ((not_le_of_gt hb) hc)
  by_cases h2 : f < 3/8
  · exact Or.inl ⟨by linarith, h2⟩
  by_cases h3 : f ≤ 5/8
  · have hc : (8 : ℝ)⁻¹ ≤ circDist (3*f) := by
      apply TwoPinner.clear_of_band (N := 1) <;> norm_num <;> linarith
    exact False.elim ((not_le_of_gt hb) hc)
  by_cases h4 : f < 17/24
  · exact Or.inr ⟨by linarith, h4⟩
  · have hc : (8 : ℝ)⁻¹ ≤ circDist (3*f) := by
      apply TwoPinner.clear_of_band (N := 2) <;> norm_num <;> linarith
    exact False.elim ((not_le_of_gt hb) hc)

/-- No old clear reading can obstruct both the tripled and quintupled events. -/
theorem five_clears_triple_blocker {f : ℝ} (hl : 1/8 ≤ f) (hu : f ≤ 7/8)
    (hb : circDist (3*f) < (8 : ℝ)⁻¹) : (8 : ℝ)⁻¹ ≤ circDist (5*f) := by
  rcases triple_blocker_ranges hl hu hb with h | h
  · apply TwoPinner.clear_of_band (N := 1) <;> norm_num <;> linarith [h.1, h.2]
  · apply TwoPinner.clear_of_band (N := 3) <;> norm_num <;> linarith [h.1, h.2]

/-- Both pinching boundary phases are clear at all three candidate multipliers. -/
theorem boundary_clear (m : ℕ) (hm : m ∈ ({2,3,5} : Finset ℕ)) :
    (8 : ℝ)⁻¹ ≤ circDist ((m : ℝ)*(1/8)) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((m : ℝ)*(7/8)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl <;> norm_num [circDist, Int.fract]

/-- Three disjoint obstruction groups among five readings cannot all have two
members. This is a count lemma, not a clearance/termination assumption. -/
theorem one_small_group (T A B C : Finset ι) (hT : T.card ≤ 5)
    (hA : A ⊆ T) (hB : B ⊆ T) (hC : C ⊆ T)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    A.card ≤ 1 ∨ B.card ≤ 1 ∨ C.card ≤ 1 := by
  classical
  have hsub : (A ∪ B) ∪ C ⊆ T := Finset.union_subset (Finset.union_subset hA hB) hC
  have hc := (Finset.card_le_card hsub).trans hT
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC,hBC⟩),
    Finset.card_union_of_disjoint hAB] at hc
  omega

/-- At a seven-reading pinch, one of the three dilations has at most one
obstruction. This asserts neither clearance after separation nor transport. -/
theorem pinch_one_blocker (f : Fin 7 → ℝ) (a b : Fin 7) (hab : a ≠ b)
    (hf : ∀ i, 1 / 8 ≤ f i ∧ f i ≤ 7 / 8)
    (ha : f a = 1 / 8) (hb : f b = 7 / 8) :
    ∃ m ∈ ({2, 3, 5} : Finset ℕ),
      (Finset.univ.filter (fun i => circDist ((m : ℝ) * f i) < (8 : ℝ)⁻¹)).card ≤ 1 := by
  classical
  let T := (Finset.univ : Finset (Fin 7)).erase a |>.erase b
  let B (m : ℕ) := Finset.univ.filter (fun i => circDist ((m : ℝ) * f i) < (8 : ℝ)⁻¹)
  have hT : T.card ≤ 5 := by
    simp [T, Finset.card_erase_of_mem, hab, Ne.symm hab]
  have hsub (m : ℕ) (hm : m ∈ ({2, 3, 5} : Finset ℕ)) : B m ⊆ T := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hia : i ≠ a := by
      intro h
      subst i
      rw [ha] at hi'
      exact (not_le_of_gt hi') (boundary_clear m hm).1
    have hib : i ≠ b := by
      intro h
      subst i
      rw [hb] at hi'
      exact (not_le_of_gt hi') (boundary_clear m hm).2
    simp [T, hia, hib]
  have h23 : Disjoint (B 2) (B 3) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h := double_blocker_middle (hf i).1 (hf i).2 (by simpa [B] using hi)
    exact (not_le_of_gt (show circDist (3 * f i) < (8 : ℝ)⁻¹ by simpa [B] using hj))
      (triple_clears_middle h.1.le h.2.le)
  have h25 : Disjoint (B 2) (B 5) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h := double_blocker_middle (hf i).1 (hf i).2 (by simpa [B] using hi)
    exact (not_le_of_gt (show circDist (5 * f i) < (8 : ℝ)⁻¹ by simpa [B] using hj))
      (five_clears_middle h.1.le h.2.le)
  have h35 : Disjoint (B 3) (B 5) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_le_of_gt (show circDist (5 * f i) < (8 : ℝ)⁻¹ by simpa [B] using hj))
      (five_clears_triple_blocker (hf i).1 (hf i).2 (by simpa [B] using hi))
  rcases one_small_group T (B 2) (B 3) (B 5) hT
    (hsub 2 (by simp)) (hsub 3 (by simp)) (hsub 5 (by simp)) h23 h25 h35 with h | h | h
  · exact ⟨2, by simp, h⟩
  · exact ⟨3, by simp, h⟩
  · exact ⟨5, by simp, h⟩

/-- Integer lap labels disappear under integer dilation, so the phase theorem
applies to actual readings, not just numbers in the first unit interval. -/
theorem dilated_phase (m : ℕ) (x : ℝ) (q : ℤ) :
    circDist ((m : ℝ) * x) = circDist ((m : ℝ) * (x - (q : ℝ))) := by
  have he : (m : ℝ) * x = (m : ℝ) * (x - (q : ℝ)) + (((m : ℤ) * q : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he, ConstructionN.circDist_add_int]

/-- The seven-reading result lifted to an actual clear event with integer laps. -/
theorem pinch_one_blocker_readings (d : Fin 7 → ℝ) (q : Fin 7 → ℤ)
    (t : ℝ) (a b : Fin 7) (hab : a ≠ b)
    (hband : ∀ i, (q i : ℝ) + 1 / 8 ≤ d i * t ∧ d i * t ≤ (q i : ℝ) + 7 / 8)
    (ha : d a * t = (q a : ℝ) + 1 / 8)
    (hb : d b * t = (q b : ℝ) + 7 / 8) :
    ∃ m ∈ ({2, 3, 5} : Finset ℕ),
      (Finset.univ.filter (fun i => circDist (d i * ((m : ℝ) * t)) < (8 : ℝ)⁻¹)).card ≤ 1 := by
  classical
  obtain ⟨m, hm, hc⟩ := pinch_one_blocker (fun i => d i * t - (q i : ℝ)) a b hab
    (fun i => by constructor <;> linarith [(hband i).1, (hband i).2])
    (by linarith) (by linarith)
  refine ⟨m, hm, ?_⟩
  have he (i : Fin 7) : circDist (d i * ((m : ℝ) * t)) =
      circDist ((m : ℝ) * (d i * t - (q i : ℝ))) := by
    rw [show d i * ((m : ℝ) * t) = (m : ℝ) * (d i * t) by ring]
    exact dilated_phase m (d i * t) (q i)
  simpa only [he] using hc

/-- At the lone blocker's forward exit, a currently clear reading retains its
band exactly when its remaining upper margin pays for the displacement.
Here z is the blocker's signed phase from its capture centre, and g the other
reading's phase in its current clear band. No lap-return claim is made. -/
theorem forward_margin_iff {b d z g : ℝ} (hb : 0 < b) (hd : 0 ≤ d)
    (hz : z ≤ 1 / 8) (hg : 1 / 8 ≤ g) :
    (1 / 8 ≤ g + d * ((1 / 8 - z) / b) ∧
      g + d * ((1 / 8 - z) / b) ≤ 7 / 8) ↔
      d * (1 / 8 - z) ≤ b * (7 / 8 - g) := by
  have hn : 0 ≤ d * ((1 / 8 - z) / b) :=
    mul_nonneg hd (div_nonneg (sub_nonneg.mpr hz) hb.le)
  have he : d * ((1 / 8 - z) / b) = (d * (1 / 8 - z)) / b := by ring
  rw [he]
  constructor
  · intro h
    have hh : (d * (1 / 8 - z)) / b ≤ 7 / 8 - g := by linarith [h.2]
    have := (div_le_iff₀ hb).mp hh
    nlinarith
  · intro h
    have hh : (d * (1 / 8 - z)) / b ≤ 7 / 8 - g :=
      (div_le_iff₀ hb).mpr (by nlinarith)
    constructor <;> linarith

/-- A family explaining a forward-repair exception. K is an arbitrary lap
parameter, not a tested upper bound. These are positive subject disparities. -/
noncomputable def exceptionReadings (K : ℕ) : Fin 7 → ℝ :=
  ![1 / 8, 7 / 8, 1 / 2, (K : ℝ) + 1 / 3, 1 / 5, 7 / 16, 5 / 8]

/-- Retreat from the tripled event to the fast reading's preceding closing.
All other readings retain their bands, uniformly in the fast reading's lap. -/
theorem exception_backward_bands (K : ℕ) :
    let T := 3 - (1 / 8) / ((K : ℝ) + 1 / 3)
    let q : Fin 7 → ℤ := ![0, 2, 1, 3 * (K : ℤ), 0, 1, 1]
    0 < T ∧ ∀ i, (q i : ℝ) + 1 / 8 ≤ exceptionReadings K i * T ∧
      exceptionReadings K i * T ≤ (q i : ℝ) + 7 / 8 := by
  dsimp only
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hr : 0 < (K : ℝ) + 1 / 3 := by linarith
  have hh : (0 : ℝ) ≤ (1 / 8) / ((K : ℝ) + 1 / 3) := by positivity
  have hu : (1 / 8 : ℝ) / ((K : ℝ) + 1 / 3) ≤ 3 / 8 := by
    apply (div_le_iff₀ hr).mpr
    linarith
  have he : ((K : ℝ) + 1 / 3) * (3 - (1 / 8) / ((K : ℝ) + 1 / 3)) =
      3 * (K : ℝ) + 7 / 8 := by
    field_simp
    <;> ring
  constructor
  · linarith
  · intro i
    fin_cases i <;> norm_num [exceptionReadings] <;> constructor <;> nlinarith

/-- The family therefore has a positive lonely instant at the derived place. -/
theorem exception_backward_clear (K : ℕ) :
    let T := 3 - (1 / 8) / ((K : ℝ) + 1 / 3)
    0 < T ∧ ∀ i, (8 : ℝ)⁻¹ ≤ circDist (exceptionReadings K i * T) := by
  have h := exception_backward_bands K
  refine ⟨h.1, ?_⟩
  intro i
  exact TwoPinner.clear_of_band (h.2 i).1 (h.2 i).2

end LRC.DeadlineRelabel
