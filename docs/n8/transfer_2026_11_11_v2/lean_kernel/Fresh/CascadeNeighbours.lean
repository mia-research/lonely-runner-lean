import Fresh.CascadeAnchor

namespace Fresh.Cascade

open Set

noncomputable section

/-- The opening and closing of a reading's clear interval at radius `r`. -/
def lapLeft (d : ℝ) (k : ℤ) (r : ℝ) : ℝ := ((k:ℝ)+r)/d

def lapRight (d : ℝ) (k : ℤ) (r : ℝ) : ℝ := ((k:ℝ)+1-r)/d

/-- The radius at which one opening and one closing coincide. -/
def pairRadius (d e : ℝ) (k l : ℤ) : ℝ :=
  (d*((l:ℝ)+1)-e*(k:ℝ))/(d+e)

theorem lap_edges_le_iff_radius {d e r : ℝ} {k l : ℤ}
    (hd : 0 < d) (he : 0 < e) :
    lapLeft d k r ≤ lapRight e l r ↔ r ≤ pairRadius d e k l := by
  unfold lapLeft lapRight pairRadius
  rw [div_le_div_iff₀ hd he,le_div_iff₀ (add_pos hd he)]
  constructor <;> intro h <;> linarith only [h]

/-- Two inequalities per reading describe the common cell. The only
potential obstruction is an opening after a closing. -/
theorem lap_cell_iff_pair_radius {S : Finset ℝ} (hne : S.Nonempty)
    (hp : ∀ d ∈ S, 0 < d) (k : ℝ → ℤ) (r : ℝ) :
    (∃ t, ∀ d ∈ S, t ∈ Icc (lapLeft d (k d) r) (lapRight d (k d) r)) ↔
      ∀ d ∈ S, ∀ e ∈ S, r ≤ pairRadius d e (k d) (k e) := by
  constructor
  · rintro ⟨t,ht⟩ d hd e he
    exact (lap_edges_le_iff_radius (hp d hd) (hp e he)).mp ((ht d hd).1.trans (ht e he).2)
  · intro h
    obtain ⟨d,hd,hmax⟩ := S.exists_max_image (fun d => lapLeft d (k d) r) hne
    refine ⟨lapLeft d (k d) r,fun e he => ⟨hmax e he,?_⟩⟩
    exact (lap_edges_le_iff_radius (hp d hd) (hp e he)).mpr (h d hd e he)

/-- The maximum radius of a fixed-lap cell is attained at a pair.
All smaller radii are feasible, with equality allowed at the maximum. -/
theorem lap_cell_critical_pair {S : Finset ℝ} (hne : S.Nonempty)
    (hp : ∀ d ∈ S, 0 < d) (k : ℝ → ℤ) :
    ∃ d ∈ S, ∃ e ∈ S, ∀ r : ℝ,
      (∃ t, ∀ i ∈ S, t ∈ Icc (lapLeft i (k i) r) (lapRight i (k i) r)) ↔
        r ≤ pairRadius d e (k d) (k e) := by
  classical
  let cap (p : ℝ × ℝ) := pairRadius p.1 p.2 (k p.1) (k p.2)
  obtain ⟨⟨d,e⟩,hde,hmin⟩ := (S ×ˢ S).exists_min_image cap (hne.product hne)
  obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
  refine ⟨d,hd,e,he,fun r => (lap_cell_iff_pair_radius hne hp k r).trans ?_⟩
  exact ⟨fun h => h d hd e he,fun h i hi j hj =>
    h.trans (hmin (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩))⟩

/-- The forward restriction adds one inequality per reader, for the
closing edge staying on or after the start. -/
theorem forward_lap_cell_iff {S : Finset ℝ} (hne : S.Nonempty)
    (hp : ∀ d ∈ S, 0 < d) (k : ℝ → ℤ) (a r : ℝ) :
    (∃ t, a ≤ t ∧ ∀ d ∈ S, t ∈ Icc (lapLeft d (k d) r) (lapRight d (k d) r)) ↔
      (∀ d ∈ S, r ≤ (k d : ℝ)+1-d*a) ∧
      (∀ d ∈ S, ∀ e ∈ S, r ≤ pairRadius d e (k d) (k e)) := by
  have hedge (d : ℝ) (hd : d ∈ S) : a ≤ lapRight d (k d) r ↔ r ≤ (k d : ℝ)+1-d*a := by
    unfold lapRight
    rw [le_div_iff₀ (hp d hd)]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨t,hat,ht⟩
    exact ⟨fun d hd => (hedge d hd).mp (hat.trans (ht d hd).2),
      (lap_cell_iff_pair_radius hne hp k r).mp ⟨t,ht⟩⟩
  · rintro ⟨ha,hp'⟩
    obtain ⟨t,ht⟩ := (lap_cell_iff_pair_radius hne hp k r).mpr hp'
    refine ⟨max a t,le_max_left _ _,fun d hd => ⟨(ht d hd).1.trans (le_max_right _ _),?_⟩⟩
    exact max_le ((hedge d hd).mpr (ha d hd)) (ht d hd).2

/-- Measured from the current instant, the boundaries need only the
current phase and the reading, with no absolute lap label. -/
theorem lap_edges_from_phase {d : ℝ} (hd : 0 < d) (a r : ℝ) :
    lapLeft d ⌊d*a⌋ r = a+(r-Int.fract (d*a))/d ∧
    lapRight d ⌊d*a⌋ r = a+(1-r-Int.fract (d*a))/d := by
  unfold lapLeft lapRight Int.fract
  constructor <;> field_simp <;> ring

private theorem lap_window_clear {d t : ℝ} {k : ℤ} (hd : 0 < d)
    (h : t ∈ Icc (lapLeft d k (1/8)) (lapRight d k (1/8))) :
    ¬ InWay d t := by
  apply not_inWay_iff.mpr
  apply Fresh.Localisation.clear_of_window k
  · simpa only [mul_comm] using (div_le_iff₀ hd).mp h.1
  · have hh := (le_div_iff₀ hd).mp h.2
    unfold lapRight at hh
    linarith

private theorem later_clear_ge_open {d a t : ℝ} (hd : 0 < d) (ht : a ≤ t)
    (h : ¬ InWay d t) :
    lapLeft d ⌊d*a⌋ (1/8) ≤ t := by
  have hk : (⌊d*a⌋ : ℝ) ≤ d*t :=
    (Int.floor_le _).trans (mul_le_mul_of_nonneg_left ht hd.le)
  have hh := (not_inWay_iff.mp h).trans (distInt_le (d*t) ⌊d*a⌋)
  rw [abs_of_nonneg (sub_nonneg.mpr hk)] at hh
  unfold lapLeft
  apply (div_le_iff₀ hd).mpr
  linarith

private theorem clear_after_close_ge_next {e a t : ℝ} (he : 0 < e)
    (hclose : lapRight e ⌊e*a⌋ (1/8) < t) (ht : ¬ InWay e t) :
    lapLeft e (⌊e*a⌋+1) (1/8) ≤ t := by
  have h := (not_inWay_iff.mp ht).trans (distInt_le (e*t) (⌊e*a⌋+1))
  unfold lapRight at hclose
  have hh := (div_lt_iff₀ he).mp hclose
  unfold lapLeft
  push_cast at h ⊢
  apply (div_le_iff₀ he).mpr
  by_contra! hf
  have : |e*t - ((⌊e*a⌋ : ℝ)+1)| < 1/8 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge h) this

/-- A pair conflict forces the early closer into its next lap before
any future isolation, even if that reading is clear at the start. -/
theorem neighbour_conflict_forces_next_opening {S : Finset ℝ}
    {d e a t : ℝ} (hd : d ∈ S) (he : e ∈ S) (hp : ∀ i ∈ S, 0 < i)
    (ht : a ≤ t) (hl : LonelyAt S t)
    (hc : lapRight e ⌊e*a⌋ (1/8) < lapLeft d ⌊d*a⌋ (1/8)) :
    lapLeft e (⌊e*a⌋+1) (1/8) ≤ t := by
  have ho := later_clear_ge_open (hp d hd) ht (not_inWay_iff.mpr (hl d hd))
  exact clear_after_close_ge_next (hp e he) (hc.trans_le ho) (not_inWay_iff.mpr (hl e he))

/-- A proved lower bound for a future witness rules out every earlier
closing edge at once. The greatest forced opening is a safe batch jump. -/
theorem rejected_edges_batch {S : Finset ℝ} {a L : ℝ}
    (hp : ∀ d ∈ S, 0 < d)
    (hL : ∀ t, a ≤ t → LonelyAt S t → L ≤ t)
    (hne : (S.filter fun e => lapRight e ⌊e*a⌋ (1/8) < L).Nonempty) :
    ∃ e ∈ S, lapRight e ⌊e*a⌋ (1/8) < L ∧
      (∀ d ∈ S, lapRight d ⌊d*a⌋ (1/8) < L →
        lapLeft d (⌊d*a⌋+1) (1/8) ≤ lapLeft e (⌊e*a⌋+1) (1/8)) ∧
      (∀ t, a ≤ t → LonelyAt S t → lapLeft e (⌊e*a⌋+1) (1/8) ≤ t) := by
  classical
  obtain ⟨e,he,hmax⟩ := _root_.Finset.exists_max_image _
    (fun d => lapLeft d (⌊d*a⌋+1) (1/8)) hne
  obtain ⟨heS,heL⟩ := Finset.mem_filter.mp he
  exact ⟨e,heS,heL,fun d hd hdL => hmax d (Finset.mem_filter.mpr ⟨hd,hdL⟩),
    fun t ht hl => clear_after_close_ge_next (hp e heS) (heL.trans_le (hL t ht hl))
      (not_inWay_iff.mpr (hl e heS))⟩

/-- The reading selected for the jump has advanced to the next lap,
with its phase on the closed opening edge. -/
theorem forced_opening_lap {d a : ℝ} (hd : 0 < d) :
    ⌊d * lapLeft d (⌊d*a⌋+1) (1/8)⌋ = ⌊d*a⌋+1 := by
  have h : d * lapLeft d (⌊d*a⌋+1) (1/8) = (((⌊d*a⌋+1 : ℤ):ℝ)+1/8) := by
    unfold lapLeft
    field_simp
  rw [h,Int.floor_eq_iff]
  norm_num

/-- At the current laps, take the latest opening, or stay at the start
if it is later. Either that point is the first clear time, or a reading's
closing has already been passed and its next opening is forced. -/
theorem neighbour_dispatch {S : Finset ℝ} (hne : S.Nonempty)
    (hp : ∀ i ∈ S, 0 < i) (a : ℝ) :
    (∃ t, FirstClearFrom S a t ∧
      (t = a ∨ ∃ d ∈ S, t = lapLeft d ⌊d*a⌋ (1/8))) ∨
    (∃ e ∈ S, a < lapLeft e (⌊e*a⌋+1) (1/8) ∧
      ∀ t, a ≤ t → LonelyAt S t → lapLeft e (⌊e*a⌋+1) (1/8) ≤ t) := by
  obtain ⟨d,hd,hmax⟩ := S.exists_max_image (fun d => lapLeft d ⌊d*a⌋ (1/8)) hne
  let L := max a (lapLeft d ⌊d*a⌋ (1/8))
  by_cases h : ∀ e ∈ S, L ≤ lapRight e ⌊e*a⌋ (1/8)
  · left
    have hclear : LonelyAt S L := by
      intro e he
      exact not_inWay_iff.mp (lap_window_clear (hp e he) ⟨
        (hmax e he).trans (le_max_right _ _),h e he⟩)
    refine ⟨L,⟨le_max_left _ _,hclear,fun t ht hl => ?_⟩,?_⟩
    · exact max_le ht (later_clear_ge_open (hp d hd) ht (not_inWay_iff.mpr (hl d hd)))
    · rcases max_choice a (lapLeft d ⌊d*a⌋ (1/8)) with ha | hd'
      · exact Or.inl ha
      · exact Or.inr ⟨d,hd,hd'⟩
  · right
    push Not at h
    obtain ⟨e,he,hclose⟩ := h
    have hL (t : ℝ) (ht : a ≤ t) (hl : LonelyAt S t) : L ≤ t :=
      max_le ht (later_clear_ge_open (hp d hd) ht (not_inWay_iff.mpr (hl d hd)))
    obtain ⟨e',he',_,_,hsafe⟩ := rejected_edges_batch hp hL
      ⟨e,Finset.mem_filter.mpr ⟨he,hclose⟩⟩
    have ha : a < lapLeft e' (⌊e'*a⌋+1) (1/8) := by
      unfold lapLeft
      apply (lt_div_iff₀ (hp e' he')).mpr
      push_cast
      linarith [Int.lt_floor_add_one (e'*a)]
    exact ⟨e',he',ha,hsafe⟩

/-- If a required opening exceeds the first clear window of the least
reading, the whole rest of that window can be skipped in one step. -/
theorem first_min_window_forced_exit {S : Finset ℝ} {m d a t : ℝ}
    (hm : m ∈ S) (hd : d ∈ S) (hp : ∀ i ∈ S, 0 < i)
    (hm0 : ⌊m*a⌋ = 0) (ha : a ≤ t) (ht : LonelyAt S t)
    (hconflict : 7/(8*m) < lapLeft d ⌊d*a⌋ (1/8)) :
    9/(8*m) ≤ t := by
  have hright : lapRight m ⌊m*a⌋ (1/8) = 7/(8*m) := by
    rw [hm0]
    unfold lapRight
    push_cast
    field_simp
    ring
  have hnext : lapLeft m (⌊m*a⌋+1) (1/8) = 9/(8*m) := by
    rw [hm0]
    unfold lapLeft
    push_cast
    field_simp
    ring
  rw [← hnext]
  apply neighbour_conflict_forces_next_opening hd hm hp ha ht
  rwa [hright]

/-- Each forced opening advances by at least one radius measured
at the fastest allowed reading. -/
theorem forced_opening_progress {d M a : ℝ} (hd : 0 < d) (hM : d ≤ M) :
    a + 1/(8*M) < lapLeft d (⌊d*a⌋+1) (1/8) := by
  have hpos := hd.trans_le hM
  have hmono : (1:ℝ)/(8*M) ≤ 1/(8*d) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  apply lt_of_le_of_lt (show a + 1/(8*M) ≤ a + 1/(8*d) by linarith)
  unfold lapLeft
  apply (lt_div_iff₀ hd).mpr
  have hscale : (1/(8*d):ℝ)*d = 1/8 := by field_simp
  rw [add_mul,hscale]
  push_cast
  linarith [Int.lt_floor_add_one (d*a)]

/-- The neighbour dispatch either accepts a point or exits a bounded
time band after finitely many forced steps. -/
theorem bounded_forced_steps {S : Finset ℝ} {M : ℝ} {seq : ℕ → ℝ} {n : ℕ}
    (hp : ∀ d ∈ S, 0 < d) (hM : ∀ d ∈ S, d ≤ M)
    (hstep : ∀ j < n, ∃ d ∈ S, seq (j+1) = lapLeft d (⌊d*seq j⌋+1) (1/8)) :
    seq 0 + (n:ℝ)/(8*M) ≤ seq n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨d,hd,he⟩ := hstep n (Nat.lt_succ_self n)
    have hh := forced_opening_progress (hp d hd) (hM d hd) (a := seq n)
    have hprev := ih (fun j hj => hstep j (hj.trans (Nat.lt_succ_self n)))
    rw [he]
    push_cast
    rw [add_div]
    linarith

#print axioms lap_cell_critical_pair
#print axioms forward_lap_cell_iff
#print axioms lap_edges_from_phase
#print axioms neighbour_conflict_forces_next_opening
#print axioms rejected_edges_batch
#print axioms forced_opening_lap
#print axioms neighbour_dispatch
#print axioms first_min_window_forced_exit
#print axioms bounded_forced_steps

end
end Fresh.Cascade
