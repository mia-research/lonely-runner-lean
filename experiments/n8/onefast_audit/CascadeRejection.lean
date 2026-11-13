import Fresh.CascadeAnchor

namespace Fresh.Cascade

open Set

/-- The phase shifts rejected by an open interval taken modulo one. -/
def RejectArc (l u θ : ℝ) : Prop :=
  ∃ k : ℤ, l < (k : ℝ) - θ ∧ (k : ℝ) - θ < u

/-- A single fast reading blocks a whole closed cell precisely when the
cell fits strictly inside one of its blocked intervals. -/
theorem reject_cell_iff {d a b θ : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    (∀ t ∈ Icc a b, distInt (d*t+θ) < 1/8) ↔
      RejectArc (d*b-1/8) (d*a+1/8) θ := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := exists_near_int (d := d*a+θ) (t := 1) (by
      simpa [InWay] using h a ⟨le_rfl,hab⟩)
    rw [mul_one,abs_lt] at hk
    refine ⟨k,?_,by linarith [hk.1]⟩
    by_contra! hkb
    let t := ((k:ℝ)+1/8-θ)/d
    have ht : t ∈ Icc a b := by
      constructor
      · dsimp [t]
        rw [le_div_iff₀ hd]
        linarith [hk.2]
      · dsimp [t]
        rw [div_le_iff₀ hd]
        linarith
    have he : d*t+θ = 1/8+(k:ℝ) := by
      dsimp [t]
      field_simp
      ring
    have hh := h t ht
    rw [he,distInt_eighth_add_int] at hh
    exact (lt_irrefl _) hh
  · rintro ⟨k,hl,hu⟩ t ht
    apply (distInt_le _ k).trans_lt
    rw [abs_lt]
    have ha := mul_le_mul_of_nonneg_left ht.1 hd.le
    have hb := mul_le_mul_of_nonneg_left ht.2 hd.le
    constructor <;> linarith


/-- Two cells suffice when the difference of the blocking integers would
lie strictly between two consecutive integers. -/
theorem clear_of_integer_gap {d a b c e θ : ℝ} (hd : 0 < d)
    (hab : a ≤ b) (hce : c ≤ e) (j : ℤ)
    (hL : (j:ℝ)+1/4 ≤ d*(e-a)) (hU : d*(c-b) ≤ (j:ℝ)+3/4) :
    ∃ t ∈ Icc a b ∪ Icc c e, (1/8:ℝ) ≤ distInt (d*t+θ) := by
  by_contra! h
  obtain ⟨p,hpL,hpU⟩ := (reject_cell_iff hd hab).mp (fun t ht => h t (Or.inl ht))
  obtain ⟨q,hqL,hqU⟩ := (reject_cell_iff hd hce).mp (fun t ht => h t (Or.inr ht))
  have h₀ : (j:ℝ) < ((q-p:ℤ):ℝ) := by push_cast; linarith
  have h₁ : ((q-p:ℤ):ℝ) < ((j+1:ℤ):ℝ) := by push_cast; linarith
  have h₀' : j < q-p := by exact_mod_cast h₀
  have h₁' : q-p < j+1 := by exact_mod_cast h₁
  omega

/-- If the first integer gap already applies at the bottom of the rate
range and lasts to the width threshold of another cell, these cells
work at every faster rate and phase. -/
theorem clear_for_fast_rates_of_gap_and_width {d₀ d a b c e u v θ : ℝ}
    (hd₀ : 0 < d₀) (hd : d₀ ≤ d) (hab : a ≤ b) (hbc : b ≤ c)
    (hce : c ≤ e) (huv : u ≤ v)
    (hstart : (1/4:ℝ) ≤ d₀*(e-a)) (hgap : c-b ≤ 3*(v-u)) :
    ∃ t ∈ (Icc a b ∪ Icc c e) ∪ Icc u v, (1/8:ℝ) ≤ distInt (d*t+θ) := by
  have hd' := hd₀.trans_le hd
  by_cases hwide : (1/4:ℝ) ≤ d*(v-u)
  · by_contra! h
    obtain ⟨k,hkL,hkU⟩ := (reject_cell_iff hd' huv).mp (fun t ht => h t (Or.inr ht))
    linarith
  · have hL := hstart.trans (mul_le_mul_of_nonneg_right hd
        (sub_nonneg.mpr (hab.trans (hbc.trans hce))))
    have hU := mul_le_mul_of_nonneg_left hgap hd'.le
    obtain ⟨t,ht,hclear⟩ := clear_of_integer_gap (θ := θ) hd' hab hce 0
      (by simpa using hL) (by norm_num; linarith)
    exact ⟨t,Or.inl ht,hclear⟩

/-- The compatibility test for two nonempty rejection arcs uses just
the difference of the two integer centres. -/
theorem reject_pair_iff {l₁ u₁ l₂ u₂ : ℝ} (h₁ : l₁ < u₁) (h₂ : l₂ < u₂) :
    (∃ θ, RejectArc l₁ u₁ θ ∧ RejectArc l₂ u₂ θ) ↔
      ∃ k : ℤ, l₂-u₁ < (k:ℝ) ∧ (k:ℝ) < u₂-l₁ := by
  constructor
  · rintro ⟨θ,⟨i,hil,hiu⟩,⟨j,hjl,hju⟩⟩
    refine ⟨j-i,?_⟩
    push_cast
    constructor <;> linarith
  · rintro ⟨k,hl,hu⟩
    let l := max l₁ (l₂-(k:ℝ))
    let u := min u₁ (u₂-(k:ℝ))
    have h : l < u := by
      apply lt_min <;> apply max_lt <;> linarith
    let x := (l+u)/2
    have hx₁ := (le_max_left l₁ (l₂-(k:ℝ))).trans_lt
      (show l < x by dsimp [x]; linarith)
    have hx₂ := (le_max_right l₁ (l₂-(k:ℝ))).trans_lt
      (show l < x by dsimp [x]; linarith)
    have hx₃ := (show x < u by dsimp [x]; linarith).trans_le (min_le_left _ _)
    have hx₄ := (show x < u by dsimp [x]; linarith).trans_le (min_le_right _ _)
    refine ⟨-x,⟨0,?_⟩,⟨k,?_⟩⟩
    · push_cast
      constructor <;> linarith
    · constructor <;> linarith

/-- Short open arcs modulo one have a common point whenever every pair
intersects. This includes tests of an arc against itself, so an empty arc
already supplies an obstruction. -/
theorem reject_arcs_pairwise_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (l u : ι → ℝ) (hwidth : ∀ i, u i - l i ≤ 1/3) :
    (∃ θ, ∀ i, RejectArc (l i) (u i) θ) ↔
      ∀ i j, ∃ θ, RejectArc (l i) (u i) θ ∧ RejectArc (l j) (u j) θ := by
  classical
  constructor
  · rintro ⟨θ,h⟩ i j
    exact ⟨θ,h i,h j⟩
  · intro h
    let a : ι := Classical.choice inferInstance
    have hlift (i : ι) : ∃ m : ℤ,
        l i-(m:ℝ) < u a ∧ l a < u i-(m:ℝ) := by
      obtain ⟨θ,⟨ka,hal,hau⟩,⟨ki,hil,hiu⟩⟩ := h a i
      refine ⟨ki-ka,?_⟩
      push_cast
      constructor <;> linarith
    choose m hm using hlift
    let L (i : ι) := l i-(m i:ℝ)
    let U (i : ι) := u i-(m i:ℝ)
    have hl (i : ι) : l a-1/3 < L i := by
      dsimp [L]
      linarith [(hm i).2,hwidth i]
    have hu (i : ι) : U i < u a+1/3 := by
      dsimp [U]
      linarith [(hm i).1,hwidth i]
    have hab (i j : ι) : L i < U j := by
      obtain ⟨θ,⟨ki,hil,hiu⟩,⟨kj,hjl,hju⟩⟩ := h i j
      let x := ((ki-m i : ℤ):ℝ)-θ
      let y := ((kj-m j : ℤ):ℝ)-θ
      have hx₁ : L i < x := by dsimp [L,x]; push_cast; linarith
      have hx₂ : x < U i := by dsimp [U,x]; push_cast; linarith
      have hy₁ : L j < y := by dsimp [L,y]; push_cast; linarith
      have hy₂ : y < U j := by dsimp [U,y]; push_cast; linarith
      let n : ℤ := ki-m i-(kj-m j)
      have hn : (n:ℝ) = x-y := by dsimp [n,x,y]; push_cast; ring
      have hnlo : (-1:ℝ) < (n:ℝ) := by
        rw [hn]
        linarith [hl i,hu j,hwidth a]
      have hnhi : (n:ℝ) < 1 := by
        rw [hn]
        linarith [hl j,hu i,hwidth a]
      have h₀ : (-1:ℤ) < n := by exact_mod_cast hnlo
      have h₁ : n < (1:ℤ) := by exact_mod_cast hnhi
      have hz : n = 0 := by omega
      have he : x = y := by
        rw [hz,Int.cast_zero] at hn
        linarith
      exact hx₁.trans (he ▸ hy₂)
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image (Finset.univ : Finset ι) L
      ⟨a,Finset.mem_univ a⟩
    obtain ⟨j,_,hj⟩ := Finset.exists_min_image (Finset.univ : Finset ι) U
      ⟨a,Finset.mem_univ a⟩
    let x := (L i+U j)/2
    have hxi : L i < x := by dsimp [x]; linarith [hab i j]
    have hxj : x < U j := by dsimp [x]; linarith [hab i j]
    refine ⟨-x,fun k => ⟨m k,?_⟩⟩
    have hL := (hi k (Finset.mem_univ k)).trans_lt hxi
    have hU := hxj.trans_le (hj k (Finset.mem_univ k))
    dsimp [L] at hL
    dsimp [U] at hU
    constructor <;> linarith

/-- If no phase shift can block a finite family of slow cells, at most
two of those cells already force an opening for every shift. -/
theorem two_cells_of_no_common_rejection {ι : Type*} [Fintype ι] [Nonempty ι]
    {d : ℝ} (hd : 0 < d) (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (h : ¬ ∃ θ, ∀ i, ∀ t ∈ Icc (a i) (b i), distInt (d*t+θ) < 1/8) :
    ∃ i j, ∀ θ, ∃ t ∈ Icc (a i) (b i) ∪ Icc (a j) (b j),
      (1/8:ℝ) ≤ distInt (d*t+θ) := by
  classical
  let l (i : ι) := d*b i-1/8
  let u (i : ι) := d*a i+1/8
  have hwidth (i : ι) : u i - l i ≤ 1/3 := by
    dsimp [u,l]
    linarith [mul_le_mul_of_nonneg_left (hab i) hd.le]
  have hn : ¬ ∀ i j, ∃ θ, RejectArc (l i) (u i) θ ∧ RejectArc (l j) (u j) θ := by
    intro hpair
    obtain ⟨θ,hθ⟩ := (reject_arcs_pairwise_iff l u hwidth).mpr hpair
    exact h ⟨θ,fun i => (reject_cell_iff hd (hab i)).mpr (hθ i)⟩
  obtain ⟨i,hi⟩ := not_forall.mp hn
  obtain ⟨j,hij⟩ := not_forall.mp hi
  refine ⟨i,j,fun θ => ?_⟩
  by_contra! ht
  exact hij ⟨θ, (reject_cell_iff hd (hab i)).mp
    (fun t hti => ht t (Or.inl hti)), (reject_cell_iff hd (hab j)).mp
    (fun t htj => ht t (Or.inr htj))⟩

/-- Three cells force a common rejection contradiction when their
cross-cell endpoint differences satisfy the two ratio bounds. -/
theorem three_cells_of_endpoint_comparison {d a b c e f g θ : ℝ}
    (hd : 0 < d) (hA : a ≤ b) (hB : c ≤ e) (hC : f ≤ g)
    (hspacing : 3*(f-e) ≤ e-a)
    (hsep : (5/4:ℝ) ≤ d*(g-c)) (hratio : 9*(c-b) ≤ 23*(g-c)) :
    ∃ t ∈ (Icc a b ∪ Icc c e) ∪ Icc f g, (1/8:ℝ) ≤ distInt (d*t+θ) := by
  by_contra! h
  obtain ⟨i,hiL,hiU⟩ := (reject_cell_iff hd hA).mp
    (fun t ht => h t (Or.inl (Or.inl ht)))
  obtain ⟨j,hjL,hjU⟩ := (reject_cell_iff hd hB).mp
    (fun t ht => h t (Or.inl (Or.inr ht)))
  obtain ⟨p,hpL,hpU⟩ := (reject_cell_iff hd hC).mp
    (fun t ht => h t (Or.inr ht))
  let k : ℤ := j-i
  let m : ℤ := p-j
  have hkL : d*(e-a)-1/4 < (k:ℝ) := by dsimp [k]; push_cast; linarith
  have hkU : (k:ℝ) < d*(c-b)+1/4 := by dsimp [k]; push_cast; linarith
  have hmL : d*(g-c)-1/4 < (m:ℝ) := by dsimp [m]; push_cast; linarith
  have hmU : (m:ℝ) < d*(f-e)+1/4 := by dsimp [m]; push_cast; linarith
  have hm1 : (1:ℝ) < (m:ℝ) := by linarith
  have hm2 : 2 ≤ m := by
    have : (1:ℤ) < m := by exact_mod_cast hm1
    omega
  have hspacing' := mul_le_mul_of_nonneg_left hspacing hd.le
  have hk3 : ((3*m-1:ℤ):ℝ) < (k:ℝ) := by push_cast; linarith [hspacing']
  have hk3' : 3*m-1 < k := by exact_mod_cast hk3
  have hmk : 3*m ≤ k := by omega
  have hm2' : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
  have hmk' : (3:ℝ)*(m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hmk
  have hscale := mul_le_mul_of_nonneg_left hratio hd.le
  linarith

/-- The three cells formed by the pinned reading and the moving slow
reading satisfy the endpoint comparison for every faster rate. -/
theorem three_anchored_cells {w d θ : ℝ}
    (hw : w ∈ Icc (41/7:ℝ) (55/9)) (hd : w ≤ d) :
    ∃ t ∈ (Icc (1/8:ℝ) (7/(8*w)) ∪ Icc (41/(8*w)) (7/8)) ∪
        Icc (9/8:ℝ) (55/(8*w)), (1/8:ℝ) ≤ distInt (d*t+θ) := by
  have hw0 : 0 < w := by linarith [hw.1]
  have hw8 : 0 < 8*w := by positivity
  have hA : (1/8:ℝ) ≤ 7/(8*w) := by rw [le_div_iff₀ hw8]; linarith [hw.2]
  have hB : 41/(8*w) ≤ (7/8:ℝ) := by rw [div_le_iff₀ hw8]; linarith [hw.1]
  have hC : (9/8:ℝ) ≤ 55/(8*w) := by rw [le_div_iff₀ hw8]; linarith [hw.2]
  apply three_cells_of_endpoint_comparison (hw0.trans_le hd) hA hB hC (by norm_num)
  · rw [← sub_div,← mul_div_assoc,le_div_iff₀ hw8]
    linarith
  · rw [← sub_div,← sub_div,← mul_div_assoc,← mul_div_assoc,
      div_le_div_iff_of_pos_right hw8]
    norm_num

/-- A slow reading can retain the three cells in any pair of laps.
The endpoint inequalities describe whole bands of readings. -/
theorem clear_on_anchored_cells_of_laps {q w : ℝ} (hw : 0 < w) (hq : q ∈ Icc (1:ℝ) w)
    {k l : ℤ} (hB : (8*(k:ℝ)+1)*w ≤ 41*q ∧ 7*q ≤ 8*(k:ℝ)+7)
    (hC : 8*(l:ℝ)+1 ≤ 9*q ∧ 55*q ≤ (8*(l:ℝ)+7)*w) {t : ℝ}
    (ht : t ∈ (Icc (1/8:ℝ) (7/(8*w)) ∪ Icc (41/(8*w)) (7/8)) ∪
        Icc (9/8:ℝ) (55/(8*w))) : (1/8:ℝ) ≤ distInt (q*t) := by
  have hw8 : 0 < 8*w := by positivity
  have hq₀ : 0 ≤ q := zero_le_one.trans hq.1
  have hlo (a : ℝ) (h : a ≤ t) : q*a ≤ q*t := mul_le_mul_of_nonneg_left h hq₀
  have hup (b : ℝ) (h : t ≤ b) : q*t ≤ q*b := mul_le_mul_of_nonneg_left h hq₀
  rcases ht with (ht | ht) | ht
  · apply Fresh.Localisation.clear_of_window 0 <;> norm_num
    · linarith [hlo _ ht.1,hq.1]
    · apply (hup _ ht.2).trans
      rw [← mul_div_assoc,div_le_iff₀ hw8]
      linarith [hq.2]
  · apply Fresh.Localisation.clear_of_window k
    · apply le_trans _ (hlo _ ht.1)
      rw [← mul_div_assoc,le_div_iff₀ hw8]
      linarith [hB.1]
    · exact (hup _ ht.2).trans (by linarith [hB.2])
  · apply Fresh.Localisation.clear_of_window l
    · exact (by linarith [hC.1] : (l:ℝ)+1/8 ≤ q*(9/8)).trans (hlo _ ht.1)
    · apply (hup _ ht.2).trans
      rw [← mul_div_assoc,div_le_iff₀ hw8]
      linarith [hC.2]

private theorem clear_on_anchored_cells {q w : ℝ} {j : ℕ}
    (hj₂ : 2 ≤ j) (hj₅ : j ≤ 5) (hq : |q-(j:ℝ)| ≤ 1/256)
    (hw : w ∈ Icc (41/7:ℝ) (55/9)) {t : ℝ}
    (ht : t ∈ (Icc (1/8:ℝ) (7/(8*w)) ∪ Icc (41/(8*w)) (7/8)) ∪
        Icc (9/8:ℝ) (55/(8*w))) : (1/8:ℝ) ≤ distInt (q*t) := by
  have hq' := abs_le.mp hq
  have hj₂' : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj₂
  have hj₅' : (j:ℝ) ≤ (5:ℝ) := by exact_mod_cast hj₅
  apply clear_on_anchored_cells_of_laps (by linarith [hw.1])
    (⟨by linarith [hq'.1],by linarith [hq'.2,hw.1]⟩ : q ∈ Icc 1 w)
    (k := (j:ℤ)-1) (l := (j:ℤ)) _ _ ht
  · constructor <;> interval_cases j <;> norm_num <;> linarith [hq'.1,hq'.2,hw.2]
  · constructor <;> interval_cases j <;> norm_num <;> linarith [hq'.1,hq'.2,hw.1]

/-- A rectangular family of six slow readings around the arithmetic
progression forces a clear time for every faster reading and phase. -/
theorem one_fast_of_six_anchored_readings {r : Fin 4 → ℝ} {w d θ : ℝ}
    (hr : ∀ i, |r i - ((i.val:ℝ)+2)| ≤ 1/256)
    (hw : w ∈ Icc (41/7:ℝ) (55/9)) (hd : w ≤ d) :
    ∃ t ∈ (Icc (1/8:ℝ) (7/8) ∪ Icc (9/8) (15/8)),
      LonelyAt (insert 1 (insert w (Finset.univ.image r))) t ∧
        (1/8:ℝ) ≤ distInt (d*t+θ) := by
  obtain ⟨t,ht,hfast⟩ := three_anchored_cells (θ := θ) hw hd
  have hw8 : 0 < 8*w := by linarith [hw.1]
  have hW : t ∈ Icc (1/8:ℝ) (7/8) ∪ Icc (9/8) (15/8) := by
    rcases ht with (h | h) | h
    · exact Or.inl ⟨h.1,h.2.trans (by rw [div_le_iff₀ hw8]; linarith [hw.1])⟩
    · refine Or.inl ⟨le_trans ?_ h.1,h.2⟩
      rw [le_div_iff₀ hw8]
      linarith [hw.2]
    · exact Or.inr ⟨h.1,h.2.trans (by rw [div_le_iff₀ hw8]; linarith [hw.1])⟩
  refine ⟨t,hW,?_,hfast⟩
  intro q hq
  simp only [Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hq
  rcases hq with rfl | rfl | ⟨i,rfl⟩
  · rcases hW with ht | ht
    · exact Fresh.Localisation.clear_of_window 0 (by simpa using ht.1) (by simpa using ht.2)
    · exact Fresh.Localisation.clear_of_window 1
        (by norm_num; linarith [ht.1]) (by norm_num; linarith [ht.2])
  · have hq0 : 0 ≤ q := by linarith [hw.1]
    have hmul (c : ℝ) : q*(c/(8*q)) = c/8 := by
      have hq' : q ≠ 0 := by linarith [hw.1]
      field_simp
    rcases ht with (ht | ht) | ht
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num
      · linarith [mul_le_mul_of_nonneg_left ht.1 hq0,hw.1]
      · simpa only [hmul] using mul_le_mul_of_nonneg_left ht.2 hq0
    · apply Fresh.Localisation.clear_of_window 5 <;> norm_num
      · simpa only [hmul] using mul_le_mul_of_nonneg_left ht.1 hq0
      · linarith [mul_le_mul_of_nonneg_left ht.2 hq0,hw.2]
    · apply Fresh.Localisation.clear_of_window 6 <;> norm_num
      · linarith [mul_le_mul_of_nonneg_left ht.1 hq0,hw.1]
      · simpa only [hmul] using mul_le_mul_of_nonneg_left ht.2 hq0
  · apply clear_on_anchored_cells (j := i.val+2) (by omega) (by omega) _ hw ht
    simpa using hr i

/-- Near the first-window pinch, either the two blocked intervals require
an integer strictly between zero and one, or the second cell is wide. -/
theorem one_fast_of_first_window_pinch {S : Finset ℝ} {w d θ : ℝ}
    (hS : ∀ q ∈ S, q ∈ Icc (1:ℝ) 5)
    (hw : w ∈ Icc (145/21:ℝ) 7) (hd : w ≤ d) :
    ∃ t ∈ Icc (1/8:ℝ) (7/40), LonelyAt (insert w S) t ∧
      (1/8:ℝ) ≤ distInt (d*t+θ) := by
  have hw0 : 0 < w := by linarith [hw.1]
  have hw8 : 0 < 8*w := by positivity
  let b := 7/(8*w)
  let c := 9/(8*w)
  have hb : (1/8:ℝ) ≤ b := by dsimp [b]; rw [le_div_iff₀ hw8]; linarith [hw.2]
  have hc : c ≤ (7/40:ℝ) := by dsimp [c]; rw [div_le_iff₀ hw8]; linarith [hw.1]
  have hc₀ : (1/8:ℝ) ≤ c := by dsimp [c]; rw [le_div_iff₀ hw8]; linarith [hw.2]
  have hbc : b ≤ c := div_le_div_of_nonneg_right (by norm_num) hw8.le
  have hstart : (1/4:ℝ) ≤ w*(7/40-1/8) := by linarith [hw.1]
  have hgap : c-b ≤ 3*(7/40-c) := by
    suffices (29:ℝ)/(8*w) ≤ 21/40 by
      dsimp [c,b]
      rw [show (29:ℝ)/(8*w) = 4*(9/(8*w))-7/(8*w) by ring] at this
      linarith
    rw [div_le_iff₀ hw8]
    linarith [hw.1]
  obtain ⟨t,hmem,hfast⟩ := clear_for_fast_rates_of_gap_and_width (θ := θ)
    hw0 hd hb hbc hc hc hstart hgap
  have ht : t ∈ Icc (1/8:ℝ) b ∪ Icc c (7/40) := hmem.elim id Or.inr
  have ht' : t ∈ Icc (1/8:ℝ) (7/40) := by
    rcases ht with h | h
    · exact ⟨h.1,h.2.trans (hbc.trans hc)⟩
    · exact ⟨hc₀.trans h.1,h.2⟩
  refine ⟨t,ht',?_,hfast⟩
  intro q hq
  rcases Finset.mem_insert.mp hq with he | he
  · subst q
    rcases ht with h | h
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num
      · linarith [mul_le_mul_of_nonneg_left h.1 hw0.le,hw.1]
      · have hh := (le_div_iff₀ hw8).mp h.2
        linarith
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num
      · have hh := (div_le_iff₀ hw8).mp h.1
        linarith
      · linarith [mul_le_mul_of_nonneg_left h.2 hw0.le,hw.2]
  · have hq' := hS q he
    have ht0 : 0 ≤ t := by linarith [ht'.1]
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num
    · linarith [mul_le_mul_of_nonneg_right hq'.1 ht0,ht'.1]
    · have hmul := mul_le_mul_of_nonneg_right hq'.2 ht0
      linarith [ht'.2]

/-- Two ordinary-phase witnesses for the rate ranges found in the
one-fast controls that require larger gaps when the phase is free. -/
theorem one_fast_of_phase_zero_witness {S : Finset ℝ} {d : ℝ}
    (h : (LonelyAt S (1/6) ∧ d ∈ Icc (75/4:ℝ) (93/4)) ∨
      (LonelyAt S (5/6) ∧ d ∈ Icc (459/20:ℝ) (477/20))) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8), LonelyAt (insert d S) t := by
  have append {t : ℝ} (hs : LonelyAt S t) (hd : (1/8:ℝ) ≤ distInt (d*t)) :
      LonelyAt (insert d S) t := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hd
    · exact hs q hq
  rcases h with ⟨hs,hd⟩ | ⟨hs,hd⟩
  · refine ⟨1/6,by constructor <;> norm_num,append hs ?_⟩
    apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith [hd.1,hd.2]
  · refine ⟨5/6,by constructor <;> norm_num,append hs ?_⟩
    apply Fresh.Localisation.clear_of_window 19 <;> norm_num <;> linarith [hd.1,hd.2]

#print axioms reject_cell_iff
#print axioms clear_of_integer_gap
#print axioms clear_for_fast_rates_of_gap_and_width
#print axioms reject_pair_iff
#print axioms reject_arcs_pairwise_iff
#print axioms two_cells_of_no_common_rejection
#print axioms three_cells_of_endpoint_comparison
#print axioms three_anchored_cells
#print axioms clear_on_anchored_cells_of_laps
#print axioms one_fast_of_six_anchored_readings
#print axioms one_fast_of_first_window_pinch
#print axioms one_fast_of_phase_zero_witness

end Fresh.Cascade
