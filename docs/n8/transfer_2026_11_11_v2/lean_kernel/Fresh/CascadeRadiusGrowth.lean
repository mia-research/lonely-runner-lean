import Fresh.CascadeNeighbours

namespace Fresh.Cascade

open Set

/-- In the initial lap, only the least and greatest readings bound
the achievable clearance radius. -/
theorem initial_lap_radius_iff {S : Finset ℝ} {m M r : ℝ}
    (hm : m ∈ S) (hM : M ∈ S) (hmpos : 0 < m)
    (hspan : ∀ d ∈ S, m ≤ d ∧ d ≤ M) :
    (∃ t : ℝ, ∀ d ∈ S, r ≤ d*t ∧ d*t ≤ 1-r) ↔ r ≤ m/(m+M) := by
  have hMpos := hmpos.trans_le (hspan M hM).1
  constructor
  · rintro ⟨t,ht⟩
    have h : r/m ≤ t := (div_le_iff₀ hmpos).mpr
      (by simpa only [mul_comm] using (ht m hm).1)
    have hu : t ≤ (1-r)/M := (le_div_iff₀ hMpos).mpr
      (by simpa only [mul_comm] using (ht M hM).2)
    have hpair := (lap_edges_le_iff_radius (k := 0) (l := 0) hmpos hMpos).mp
      (show lapLeft m 0 r ≤ lapRight M 0 r by
        simpa [lapLeft,lapRight] using h.trans hu)
    simpa [pairRadius] using hpair
  · intro hr
    refine ⟨1/(m+M),fun d hd => ?_⟩
    have hsum : 0 < m+M := add_pos hmpos hMpos
    have hlo := div_le_div_of_nonneg_right (hspan d hd).1 hsum.le
    have hhi := div_le_div_of_nonneg_right (hspan d hd).2 hsum.le
    have he : m/(m+M) + M/(m+M) = 1 := by
      rw [← add_div,div_self hsum.ne']
    constructor
    · simpa [div_eq_mul_inv] using hr.trans hlo
    · have h : d/(m+M) ≤ 1-r := by linarith
      simpa [div_eq_mul_inv] using h

/-- The exact thresholds at radii one sixteenth and one eighth,
with every reading in its initial lap. -/
theorem initial_lap_two_radii {S : Finset ℝ} {m M : ℝ}
    (hm : m ∈ S) (hM : M ∈ S) (hmpos : 0 < m)
    (hspan : ∀ d ∈ S, m ≤ d ∧ d ≤ M) :
    ((∃ t : ℝ, ∀ d ∈ S, (1/16:ℝ) ≤ d*t ∧ d*t ≤ 1-1/16) ↔ M ≤ 15*m) ∧
    ((∃ t : ℝ, ∀ d ∈ S, (1/8:ℝ) ≤ d*t ∧ d*t ≤ 1-1/8) ↔ M ≤ 7*m) := by
  have hsum : 0 < m+M := add_pos hmpos (hmpos.trans_le (hspan M hM).1)
  constructor <;> rw [initial_lap_radius_iff hm hM hmpos hspan,le_div_iff₀ hsum] <;>
    constructor <;> intro h <;> linarith

/-- When the fastest reading lies in the first blocked band at the
minimum reading's opening, it recovers in the same slow cell exactly
when its next opening precedes the slow closing. -/
theorem first_rollover_iff {m B x : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    (hB : B ≤ 7*m) (hx₁ : 7*m < x) (hx₂ : x < 9*m) :
    (∃ t ∈ Icc (1/(8*m)) (7/(8*B)), ¬ InWay x t) ↔ 9*B ≤ 7*x := by
  have hBp := hm.trans_le hmB
  have hxp : 0 < x := by linarith
  have ha : (1:ℝ)/(8*m) ≤ 7/(8*B) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hnear : |x*(1/(8*m))-((1:ℤ):ℝ)| < 1/8 := by
    have hlo : (7/8:ℝ) < x/(8*m) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have hhi : x/(8*m) < (9/8:ℝ) := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rw [Int.cast_one,mul_one_div,abs_lt]
    constructor <;> linarith
  have hblocked : InWay x (1/(8*m)) :=
    (distInt_le _ 1).trans_lt hnear
  rw [single_reading_cell_iff hxp ha,or_iff_right (not_not.mpr hblocked),
    nextOpening_eq hnear,div_le_div_iff₀ hxp (by positivity)]
  norm_num
  constructor <;> intro h <;> linarith only [h]

/-- The upper part of the one-rollover range already clears at the
minimum reading's original opening. -/
theorem first_opening_after_rollover {m x : ℝ} (hm : 0 < m)
    (hlo : 9*m ≤ x) (hhi : x ≤ 15*m) :
    ¬ InWay x (1/(8*m)) := by
  apply not_inWay_iff.mpr
  apply Fresh.Localisation.clear_of_window 1 <;> rw [mul_one_div]
  · rw [le_div_iff₀ (by positivity)]
    norm_num
    linarith
  · rw [div_le_iff₀ (by positivity)]
    norm_num
    linarith

#print axioms initial_lap_two_radii
#print axioms first_rollover_iff
#print axioms first_opening_after_rollover

/-- At the first rollover candidate, all readings in the initial
one-sixteenth span fall into three explicit clear bands or their gaps. -/
theorem rollover_candidate_clear_iff {m x d : ℝ} (hm : 0 < m)
    (hx₁ : 7*m < x) (hx₂ : x < 9*m) (hd₁ : m ≤ d) (hd₂ : d ≤ 15*m) :
    (¬ InWay d (9/(8*x))) ↔
      9*d ≤ 7*x ∨ (x ≤ d ∧ 3*d ≤ 5*x) ∨ 17*x ≤ 9*d := by
  have hx : 0 < x := by linarith
  let y := d*(9/(8*x))
  have hy : y = (9*d)/(8*x) := by dsimp [y]; ring
  have hl : (1/8:ℝ) ≤ y := by
    rw [hy,le_div_iff₀ (by positivity)]
    linarith
  have hu : y ≤ (23/8:ℝ) := by
    rw [hy,div_le_iff₀ (by positivity)]
    linarith
  have h7 : y ≤ (7/8:ℝ) ↔ 9*d ≤ 7*x := by
    rw [hy,div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  have h9 : (9/8:ℝ) ≤ y ↔ x ≤ d := by
    rw [hy,le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  have h15 : y ≤ (15/8:ℝ) ↔ 3*d ≤ 5*x := by
    rw [hy,div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  have h17 : (17/8:ℝ) ≤ y ↔ 17*x ≤ 9*d := by
    rw [hy,le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [← h7,← h9,← h15,← h17,not_inWay_iff]
  change (1/8:ℝ) ≤ distInt y ↔ _
  constructor
  · intro h
    by_cases hA : y ≤ 7/8
    · exact Or.inl hA
    have hB : (9/8:ℝ) ≤ y := by
      by_contra! hb
      have he := h.trans (distInt_le y 1)
      norm_num at he
      exact (not_lt_of_ge he) (abs_lt.mpr ⟨by linarith,by linarith⟩)
    by_cases hC : y ≤ 15/8
    · exact Or.inr (Or.inl ⟨hB,hC⟩)
    apply Or.inr ∘ Or.inr
    by_contra! hd
    have he := h.trans (distInt_le y 2)
    norm_num at he
    exact (not_lt_of_ge he) (abs_lt.mpr ⟨by linarith,by linarith⟩)
  · rintro (hA | ⟨hB,hC⟩ | hD)
    · exact Fresh.Localisation.clear_of_window 0 (by simpa using hl) (by simpa using hA)
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith

#print axioms rollover_candidate_clear_iff

private noncomputable def sixAP : Finset ℝ := {1,2,3,4,5,6}

private theorem sixAP_first {t : ℝ} (ht : t ∈ Icc (1/8:ℝ) (7/48)) :
    LonelyAt sixAP t := by
  intro d hd
  simp only [sixAP,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]

private theorem sixAP_second {t : ℝ} (ht : t ∈ Icc (9/32:ℝ) (7/24)) :
    LonelyAt sixAP t := by
  intro d hd
  simp only [sixAP,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]
    | apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [ht.1,ht.2]

private theorem sixAP_point : LonelyAt sixAP (3/8) := by
  intro d hd
  simp only [sixAP,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
  · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
  · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
  · exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)

private theorem sixAP_skip_one {t : ℝ} (h : LonelyAt sixAP t)
    (ht : (7/48:ℝ) < t) : (9/32:ℝ) ≤ t := by
  by_contra! hh
  have hb (d : ℝ) (hd : d ∈ sixAP) (hl : (7/8:ℝ) < d*t) (hu : d*t < 9/8) : False := by
    have hc := (h d hd).trans (distInt_le (d*t) 1)
    norm_num at hc
    exact (not_lt_of_ge hc) (abs_lt.mpr ⟨by linarith,by linarith⟩)
  by_cases h6 : t < 3/16
  · exact hb 6 (by simp [sixAP]) (by linarith) (by linarith)
  by_cases h5 : t < 9/40
  · exact hb 5 (by simp [sixAP]) (by linarith) (by linarith)
  exact hb 4 (by simp [sixAP]) (by linarith) (by linarith)

private theorem sixAP_skip_two {t : ℝ} (h : LonelyAt sixAP t)
    (ht : (7/24:ℝ) < t) : (3/8:ℝ) ≤ t := by
  by_contra! hh
  have hc := (h 3 (by simp [sixAP])).trans (distInt_le (3*t) 1)
  norm_num at hc
  exact (not_lt_of_ge hc) (abs_lt.mpr ⟨by linarith,by linarith⟩)

private theorem first_at_opening_of_near {x a : ℝ} {k : ℤ}
    (hx : 0 < x) (h : |x*a-(k:ℝ)| < 1/8) :
    FirstClearFrom {x} a (((k:ℝ)+1/8)/x) := by
  have hw : InWay x a := (distInt_le _ k).trans_lt h
  rw [← nextOpening_eq h]
  refine ⟨(lt_nextOpening hx hw).le,?_,fun s hs hs' => ?_⟩
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact not_inWay_iff.mp (not_inWay_at_nextOpening hx)
  · by_contra! ht
    exact (not_inWay_iff.mpr (hs' x (Finset.mem_singleton_self _)))
      (inWay_until_opening hx hw hs ht)

/-- The first forced opening is the first isolation exactly when
every reading lies in the three rate bands. The readings may have
arbitrary intermediate spacing within the initial span. -/
theorem first_rollover_dispatch {S : Finset ℝ} {m x : ℝ} (hm : 0 < m)
    (hxS : x ∈ S) (hx₁ : 7*m < x) (hx₂ : x < 9*m)
    (hspan : ∀ d ∈ S, m ≤ d ∧ d ≤ 15*m) :
    FirstClearFrom S (1/(8*m)) (9/(8*x)) ↔
      ∀ d ∈ S, 9*d ≤ 7*x ∨ (x ≤ d ∧ 3*d ≤ 5*x) ∨ 17*x ≤ 9*d := by
  have hx : 0 < x := by linarith
  have hnear : |x*(1/(8*m))-((1:ℤ):ℝ)| < 1/8 := by
    rw [Int.cast_one,mul_one_div,abs_lt]
    constructor
    · have h : (7/8:ℝ) < x/(8*m) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
      linarith
    · have h : x/(8*m) < (9/8:ℝ) := (div_lt_iff₀ (by positivity)).mpr (by linarith)
      linarith
  have he : (((1:ℤ):ℝ)+1/8)/x = 9/(8*x) := by
    push_cast
    field_simp
    norm_num
  have hf := first_at_opening_of_near hx hnear
  rw [he] at hf
  constructor
  · intro h d hd
    exact (rollover_candidate_clear_iff hm hx₁ hx₂ (hspan d hd).1 (hspan d hd).2).mp
      (not_inWay_iff.mpr (h.2.1 d hd))
  · intro h
    refine ⟨hf.1,fun d hd => ?_,fun t ht hl => hf.2.2 t ht ?_⟩
    · exact not_inWay_iff.mp ((rollover_candidate_clear_iff hm hx₁ hx₂
        (hspan d hd).1 (hspan d hd).2).mpr (h d hd))
    · intro d hd
      rw [Finset.mem_singleton.mp hd]
      exact hl x hxS

#print axioms first_rollover_dispatch

/-- A one-reader deformation of the AP is covered by three slow cells.
The formula gives the exact first landing throughout the whole range
allowed by the initial one-sixteenth radius. -/
theorem ap_outlier_first_landing (x : ℝ) (hx : 7 ≤ x) (h15 : x ≤ 15) :
    FirstClearFrom (({1,2,3,4,5,6} : Finset ℝ) ∪ {x}) (1/8)
      (if x = 7 ∨ 9 ≤ x then 1/8
       else if 54/7 ≤ x then 9/(8*x)
       else if 68/9 ≤ x then 9/32
       else if 51/7 ≤ x then 17/(8*x)
       else 3/8) := by
  classical
  change FirstClearFrom (sixAP ∪ {x}) _ _
  have hxpos : 0 < x := by linarith
  have hslow0 : FirstClearFrom sixAP (1/8) (1/8) :=
    ⟨le_rfl,sixAP_first ⟨le_rfl,by norm_num⟩,fun _ h _ => h⟩
  have hfinish {a u : ℝ} (ha : (1/8:ℝ) ≤ a)
      (hs : ∀ t, (1/8:ℝ) ≤ t → LonelyAt (sixAP ∪ {x}) t → a ≤ t)
      (hu : FirstClearFrom {x} a u) (hl : LonelyAt sixAP u) :
      FirstClearFrom (sixAP ∪ {x}) (1/8) u := by
    refine ⟨ha.trans hu.1,fun d hd => ?_,fun t ht htclear => ?_⟩
    · rcases Finset.mem_union.mp hd with hd | hd
      · exact hl d hd
      · exact hu.2.1 d hd
    · exact hu.2.2 t (hs t ht htclear) (fun d hd =>
        htclear d (Finset.mem_union_right sixAP hd))
  have hnow {a : ℝ} (h : ¬ InWay x a) : FirstClearFrom {x} a a := by
    refine ⟨le_rfl,fun d hd => ?_,fun _ hs _ => hs⟩
    rw [Finset.mem_singleton.mp hd]
    exact not_inWay_iff.mp h
  by_cases h0 : x = 7 ∨ 9 ≤ x
  · rw [if_pos h0]
    apply block_first_clear_in_cell hslow0 (hnow ?_) (fun _ => sixAP_first) (by norm_num)
    rcases h0 with rfl | h0
    · exact not_inWay_iff.mpr (Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num))
    · simpa only [mul_one] using
        first_opening_after_rollover (m := 1) (by norm_num) (by linarith) (by linarith)
  rw [if_neg h0]
  have hx7 : 7 < x := lt_of_le_of_ne hx (fun h => h0 (Or.inl h.symm))
  have hx9 : x < 9 := lt_of_not_ge (fun h => h0 (Or.inr h))
  have hnear1 : |x*(1/8)-((1:ℤ):ℝ)| < 1/8 := by
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  have hu1 : FirstClearFrom {x} (1/8) (9/(8*x)) := by
    have he : (((1:ℤ):ℝ)+1/8)/x = 9/(8*x) := by
      push_cast
      field_simp
      norm_num
    rw [← he]
    exact first_at_opening_of_near hxpos hnear1
  by_cases h1 : (54/7:ℝ) ≤ x
  · rw [if_pos h1]
    exact block_first_clear_in_cell hslow0 hu1 (fun _ => sixAP_first) (by
      rw [div_le_iff₀ (by positivity)]
      linarith)
  rw [if_neg h1]
  have ha2 (t : ℝ) (ht : (1/8:ℝ) ≤ t) (hl : LonelyAt (sixAP ∪ {x}) t) :
      (9/32:ℝ) ≤ t := by
    apply sixAP_skip_one (fun d hd => hl d (Finset.mem_union_left {x} hd))
    have hu := block_first_clear_lower hslow0 hu1 ht hl
    have he : (7/48:ℝ) < 9/(8*x) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    exact he.trans_le hu
  by_cases h2 : (68/9:ℝ) ≤ x
  · rw [if_pos h2]
    apply hfinish (by norm_num) ha2 (hnow ?_) (sixAP_second ⟨le_rfl,by norm_num⟩)
    apply not_inWay_iff.mpr
    apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
  rw [if_neg h2]
  have hnear2 : |x*(9/32)-((2:ℤ):ℝ)| < 1/8 := by
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  have hu2 : FirstClearFrom {x} (9/32) (17/(8*x)) := by
    have he : (((2:ℤ):ℝ)+1/8)/x = 17/(8*x) := by
      push_cast
      field_simp
      norm_num
    rw [← he]
    exact first_at_opening_of_near hxpos hnear2
  by_cases h3 : (51/7:ℝ) ≤ x
  · rw [if_pos h3]
    apply hfinish (by norm_num) ha2 hu2
    exact sixAP_second ⟨hu2.1,by rw [div_le_iff₀ (by positivity)]; linarith⟩
  rw [if_neg h3]
  have ha3 (t : ℝ) (ht : (1/8:ℝ) ≤ t) (hl : LonelyAt (sixAP ∪ {x}) t) :
      (3/8:ℝ) ≤ t := by
    apply sixAP_skip_two (fun d hd => hl d (Finset.mem_union_left {x} hd))
    have hu := hu2.2.2 t (ha2 t ht hl) (fun d hd => hl d (Finset.mem_union_right sixAP hd))
    have he : (7/24:ℝ) < 17/(8*x) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    exact he.trans_le hu
  apply hfinish (by norm_num) ha3 (hnow ?_) sixAP_point
  apply not_inWay_iff.mpr
  apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith

#print axioms ap_outlier_first_landing

end Fresh.Cascade
