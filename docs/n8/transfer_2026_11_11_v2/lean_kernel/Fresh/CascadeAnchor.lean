import Fresh.Cascade
import Fresh.Localisation

namespace Fresh.Cascade

open Set

/-- The earliest clear point on or after the specified start. -/
def FirstClearFrom (ds : Finset ℝ) (start t : ℝ) : Prop :=
  start ≤ t ∧ LonelyAt ds t ∧ ∀ s, start ≤ s → LonelyAt ds s → t ≤ s

theorem fixed_is_first_clear_from {ds : Finset ℝ} {start : ℝ}
    (hp : ∀ d ∈ ds, 0 < d) {N : ℕ}
    (hf : cascadeSeq ds start (N+1) = cascadeSeq ds start N) :
    FirstClearFrom ds start (cascadeSeq ds start N) := by
  let seq := cascadeSeq ds start
  have hm := cascadeSeq_isMove ds start
  have hl := hm N
  rw [hf] at hl
  refine ⟨?_,(isMove_self_iff hp).mp hl,fun s hs hsl => ?_⟩
  · simpa only [cascadeSeq_zero] using start_le_seq hp hm N
  · exact seq_le_of_lonely hp hsl (by simpa only [cascadeSeq_zero] using hs) hm N

/-- Alternating the two blocks' first clear times is a valid cascade shortcut.
After the two moves, every joint clear time is at least the new start. -/
theorem block_first_clear_lower {S F : Finset ℝ} {start a u s : ℝ}
    (ha : FirstClearFrom S start a) (hu : FirstClearFrom F a u)
    (hs : start ≤ s) (hjoint : LonelyAt (S ∪ F) s) : u ≤ s := by
  have hslow : LonelyAt S s := fun d hd => hjoint d (Finset.mem_union_left F hd)
  have hfast : LonelyAt F s := fun d hd => hjoint d (Finset.mem_union_right S hd)
  exact hu.2.2 s (ha.2.2 s hs hslow) hfast

/-- If the second block lands inside a clear cell of the first, its landing
is the first joint clear point. Both ends of the slow cell are allowed. -/
theorem block_first_clear_in_cell {S F : Finset ℝ} {start a b u : ℝ}
    (ha : FirstClearFrom S start a) (hu : FirstClearFrom F a u)
    (hcell : ∀ s ∈ Icc a b, LonelyAt S s) (hb : u ≤ b) :
    FirstClearFrom (S ∪ F) start u := by
  refine ⟨ha.1.trans hu.1,?_,fun s hs hj => block_first_clear_lower ha hu hs hj⟩
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hcell u ⟨hu.1,hb⟩ d hd
  · exact hu.2.1 d hd

/-- Contract time around the anchor by the factor used to dilate the rates. -/
noncomputable def anchorTime (a c t : ℝ) : ℝ := a + (t-a)/c

private theorem anchorTime_mono {a c : ℝ} (hc : 0 < c) :
    StrictMono (anchorTime a c) := by
  intro x y h
  unfold anchorTime
  have hd := div_lt_div_of_pos_right (sub_lt_sub_right h a) hc
  linarith

private theorem anchor_phase {a c d : ℝ} (hc : 0 < c) {m : ℤ}
    (hm : (c*d-d)*a = (m:ℝ)) (t : ℝ) :
    (c*d)*anchorTime a c t = d*t + (m:ℝ) := by
  rw [← hm]
  unfold anchorTime
  field_simp
  ring

private theorem anchor_inWay {a c d t : ℝ} (hc : 0 < c) {m : ℤ}
    (hm : (c*d-d)*a = (m:ℝ)) : InWay (c*d) (anchorTime a c t) ↔ InWay d t := by
  unfold InWay
  rw [anchor_phase hc hm,distInt_add_int]

private theorem anchor_nextOpening {a c d t : ℝ} (hc : 0 < c) (hd : 0 < d)
    {m : ℤ} (hm : (c*d-d)*a = (m:ℝ)) (ht : InWay d t) :
    nextOpening (c*d) (anchorTime a c t) = anchorTime a c (nextOpening d t) := by
  obtain ⟨k,hk⟩ := exists_near_int ht
  have hk' : |(c*d)*anchorTime a c t - ((k+m : ℤ):ℝ)| < 1/8 := by
    rw [anchor_phase hc hm,Int.cast_add,add_sub_add_right_eq_sub]
    exact hk
  rw [nextOpening_eq hk',nextOpening_eq hk,Int.cast_add,← hm]
  unfold anchorTime
  field_simp
  ring

/-- The whole move is conjugate under an anchored dilation when each
rate changes its phase at the anchor by an integer. -/
theorem anchor_isMove {F : Finset ℝ} {a c t u : ℝ} (hc : 0 < c)
    (hp : ∀ d ∈ F, 0 < d)
    (hphase : ∀ d ∈ F, ∃ m : ℤ, (c*d-d)*a = (m:ℝ))
    (h : IsMove F t u) :
    IsMove (F.image fun d => c*d) (anchorTime a c t) (anchorTime a c u) := by
  rcases h with ⟨hn,rfl⟩ | ⟨d,hd,hw,rfl,hmax⟩
  · left
    refine ⟨fun e he => ?_,rfl⟩
    obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp he
    subst e
    obtain ⟨m,hm⟩ := hphase d hd
    exact fun h => hn d hd ((anchor_inWay hc hm).mp h)
  · right
    obtain ⟨m,hm⟩ := hphase d hd
    refine ⟨c*d,Finset.mem_image_of_mem _ hd,(anchor_inWay hc hm).mpr hw,
      (anchor_nextOpening hc (hp d hd) hm hw).symm,fun e he hb => ?_⟩
    obtain ⟨e₀,he₀,heq⟩ := Finset.mem_image.mp he
    subst e
    obtain ⟨k,hk⟩ := hphase e₀ he₀
    have hb' := (anchor_inWay hc hk).mp hb
    rw [anchor_nextOpening hc (hp e₀ he₀) hk hb']
    exact (anchorTime_mono hc).monotone (hmax e₀ he₀ hb')

theorem anchor_cascadeSeq {F : Finset ℝ} {a c : ℝ} (hc : 0 < c)
    (hp : ∀ d ∈ F, 0 < d)
    (hphase : ∀ d ∈ F, ∃ m : ℤ, (c*d-d)*a = (m:ℝ)) (N : ℕ) :
    cascadeSeq (F.image fun d => c*d) a N = anchorTime a c (cascadeSeq F a N) := by
  induction N with
  | zero => simp [anchorTime,cascadeSeq_zero]
  | succ N ih =>
    have h := cascadeSeq_isMove (F.image fun d => c*d) a N
    rw [ih] at h
    exact isMove_unique h (anchor_isMove hc hp hphase (cascadeSeq_isMove F a N))

/-- An anchored dilation also transports minimality, so the first fast
clear time can be reused for every dilation in the same phase class. -/
theorem anchor_first_clear {F : Finset ℝ} {a c t : ℝ} (hc : 0 < c)
    (hphase : ∀ d ∈ F, ∃ m : ℤ, (c*d-d)*a = (m:ℝ))
    (ht : FirstClearFrom F a t) :
    FirstClearFrom (F.image fun d => c*d) a (anchorTime a c t) := by
  have hzero : anchorTime a c a = a := by simp [anchorTime]
  have hstart : a ≤ anchorTime a c t := by
    have hmono := (anchorTime_mono (a := a) hc).monotone ht.1
    rwa [hzero] at hmono
  refine ⟨hstart,?_,fun s hs hsc => ?_⟩
  · intro e he
    obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp he
    subst e
    obtain ⟨m,hm⟩ := hphase d hd
    rw [anchor_phase hc hm,distInt_add_int]
    exact ht.2.1 d hd
  let u := a+c*(s-a)
  have hu : a ≤ u := le_add_of_nonneg_right (mul_nonneg hc.le (sub_nonneg.mpr hs))
  have hsu : anchorTime a c u = s := by
    unfold anchorTime u
    field_simp
    ring
  have huf : LonelyAt F u := by
    intro d hd
    obtain ⟨m,hm⟩ := hphase d hd
    have h := hsc (c*d) (Finset.mem_image_of_mem _ hd)
    rw [← hsu,anchor_phase hc hm,distInt_add_int] at h
    exact h
  rw [← hsu]
  exact (anchorTime_mono hc).monotone (ht.2.2 u hu huf)

/-- At a fixed slow cell, all dilations that preserve the anchor phases
obey a single inequality. The criterion includes singleton cells. -/
theorem anchor_cell_accepts_iff {S F : Finset ℝ} {a b c t : ℝ}
    (hc : 0 < c) (hslow : ∀ s ∈ Icc a b, LonelyAt S s)
    (ht : FirstClearFrom F a t)
    (hphase : ∀ d ∈ F, ∃ m : ℤ, (c*d-d)*a = (m:ℝ)) :
    (∃ s ∈ Icc a b, LonelyAt (S ∪ F.image fun d => c*d) s) ↔ t-a ≤ c*(b-a) := by
  have hf := anchor_first_clear hc hphase ht
  have hb : anchorTime a c t ≤ b ↔ t-a ≤ c*(b-a) := by
    unfold anchorTime
    rw [← le_sub_iff_add_le',div_le_iff₀ hc,mul_comm]
  constructor
  · rintro ⟨s,hs,hclear⟩
    exact hb.mp ((hf.2.2 s hs.1 (fun d hd =>
      hclear d (Finset.mem_union_right S hd))).trans hs.2)
  · intro h
    have hs : anchorTime a c t ∈ Icc a b := ⟨hf.1,hb.mpr h⟩
    refine ⟨_,hs,fun d hd => ?_⟩
    rcases Finset.mem_union.mp hd with hd | hd
    · exact hslow _ hs d hd
    · exact hf.2.1 d hd

/-- An entire anchored dilation family inherits a joint witness in the
same slow cell, including when the cell is a singleton. -/
theorem anchor_cell_transport {S F : Finset ℝ} {a b c t : ℝ}
    (hc : 1 ≤ c) (ht : t ∈ Icc a b)
    (hslow : ∀ s ∈ Icc a b, LonelyAt S s) (hfast : LonelyAt F t)
    (hphase : ∀ d ∈ F, ∃ m : ℤ, (c*d-d)*a = (m:ℝ)) :
    anchorTime a c t ∈ Icc a b ∧ LonelyAt (S ∪ F.image fun d => c*d) (anchorTime a c t) := by
  have hcp : 0 < c := zero_lt_one.trans_le hc
  have hmem : anchorTime a c t ∈ Icc a b := by
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ht.1) hcp.le)
    · have h := div_le_self (sub_nonneg.mpr ht.1) hc
      unfold anchorTime
      linarith [ht.2]
  refine ⟨hmem,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hslow _ hmem d hd
  · obtain ⟨d₀,hd₀,heq⟩ := Finset.mem_image.mp hd
    subst d
    obtain ⟨m,hm⟩ := hphase d₀ hd₀
    rw [anchor_phase hcp hm,distInt_add_int]
    exact hfast d₀ hd₀

/-- A single appended reading accepts the cell exactly when it is clear
at the left endpoint or its current blocked interval ends in the cell. -/
theorem single_reading_cell_iff {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    (∃ t ∈ Icc a b, ¬ InWay d t) ↔ ¬ InWay d a ∨ nextOpening d a ≤ b := by
  constructor
  · rintro ⟨t,ht,htclear⟩
    by_cases ha : InWay d a
    · right
      by_contra! h
      exact htclear (inWay_until_opening hd ha ht.1 (ht.2.trans_lt h))
    · exact Or.inl ha
  · rintro (ha | hb)
    · exact ⟨a,⟨le_rfl,hab⟩,ha⟩
    · by_cases ha : InWay d a
      · exact ⟨nextOpening d a,⟨(lt_nextOpening hd ha).le,hb⟩,not_inWay_at_nextOpening hd⟩
      · exact ⟨a,⟨le_rfl,hab⟩,ha⟩

/-- One fast reading cannot reject a slow cell at least as wide as one
of its blocked intervals. -/
theorem single_reading_cell_of_width {a b d : ℝ} (hd : 0 < d)
    (hw : 1 / (4*d) ≤ b-a) : ∃ t ∈ Icc a b, ¬ InWay d t := by
  have hp : 0 < 1 / (4*d) := by positivity
  have hab : a ≤ b := by linarith
  apply (single_reading_cell_iff hd hab).mpr
  by_cases ha : InWay d a
  · right
    obtain ⟨k,hk⟩ := exists_near_int ha
    rw [nextOpening_eq hk,div_le_iff₀ hd]
    have hw' : (1/4:ℝ) ≤ (b-a)*d := by
      have h := (div_le_iff₀ (show 0 < 4*d by positivity)).mp hw
      nlinarith
    linarith [(abs_lt.mp hk).1,hw']
  · exact Or.inl ha

/-- For a fixed slow cell and a fast direction, one first-clear time
for each positive residue representative determines acceptance at every
integer scale in that class. -/
theorem anchor_residue_cell {S F : Finset ℝ} {a b t : ℝ}
    (hslow : ∀ s ∈ Icc a b, LonelyAt S s) (D r k : ℕ) (hr : 0 < r)
    (hden : ∀ d ∈ F, ∃ m : ℤ, (D:ℝ)*d*a = (m:ℝ))
    (ht : FirstClearFrom (F.image fun d => (r:ℝ)*d) a t) :
    (∃ s ∈ Icc a b, LonelyAt (S ∪ F.image fun d => ((r:ℝ)+D*k)*d) s) ↔
      (r:ℝ)*(t-a) ≤ ((r:ℝ)+D*k)*(b-a) := by
  let n : ℝ := (r:ℝ)+D*k
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hn : 0 < n := by dsimp [n]; positivity
  let c := n/(r:ℝ)
  have hc : 0 < c := div_pos hn hr'
  have he (d : ℝ) : c*((r:ℝ)*d) = n*d := by
    dsimp [c]
    field_simp
  have hphase : ∀ d ∈ F.image (fun d => (r:ℝ)*d),
      ∃ m : ℤ, (c*d-d)*a = (m:ℝ) := by
    intro d hd
    obtain ⟨e,heF,heq⟩ := Finset.mem_image.mp hd
    subst d
    obtain ⟨m,hm⟩ := hden e heF
    refine ⟨(k:ℤ)*m,?_⟩
    rw [he,Int.cast_mul,Int.cast_natCast,← hm]
    dsimp [n]
    ring
  have hh := anchor_cell_accepts_iff hc hslow ht hphase
  have himage : (F.image (fun d => (r:ℝ)*d)).image (fun d => c*d) =
      F.image (fun d => n*d) := by
    rw [Finset.image_image]
    apply congrArg (fun f : ℝ → ℝ => F.image f)
    funext d
    exact he d
  rw [himage] at hh
  change (∃ s ∈ Icc a b, LonelyAt (S ∪ F.image fun d => n*d) s) ↔
    (r:ℝ)*(t-a) ≤ n*(b-a)
  rw [hh]
  dsimp [c]
  rw [div_mul_eq_mul_div,le_div_iff₀ hr',mul_comm (r:ℝ)]

/-- Scales from 1 through the denominator cover every positive integer
scale. This form uses a positive representative for residue zero. -/
theorem positive_residue_representative {n D : ℕ} (hn : 0 < n) (hD : 0 < D) :
    ∃ r k : ℕ, 0 < r ∧ r ≤ D ∧ n = r+D*k := by
  refine ⟨(n-1)%D+1,(n-1)/D,by omega,?_ ,?_⟩
  · have := Nat.mod_lt (n-1) hD
    omega
  · have := Nat.mod_add_div (n-1) D
    omega

/-- One witnessed cell gives all the rate dilations in the arithmetic
progression determined by a common denominator of its anchor phases. -/
theorem anchor_progression_transport {S F : Finset ℝ} {a b t : ℝ}
    (ht : t ∈ Icc a b) (hslow : ∀ s ∈ Icc a b, LonelyAt S s)
    (hfast : LonelyAt F t) (D : ℕ)
    (hden : ∀ d ∈ F, ∃ m : ℤ, (D:ℝ)*d*a = (m:ℝ)) (k : ℕ) :
    let c : ℝ := 1+(D:ℝ)*k
    anchorTime a c t ∈ Icc a b ∧ LonelyAt (S ∪ F.image fun d => c*d) (anchorTime a c t) := by
  dsimp only
  apply anchor_cell_transport (by
    have h : 0 ≤ (D:ℝ)*k := by positivity
    linarith) ht hslow hfast
  intro d hd
  obtain ⟨m,hm⟩ := hden d hd
  refine ⟨(k:ℤ)*m,?_⟩
  push_cast
  rw [← hm]
  ring

/-- The corpus's sole-free-flank control extends to an infinite family.
The first isolation follows one fast opening in the first slow cell. -/
theorem six_consecutive_and_multiple (k : ℕ) :
    FirstClearFrom ({2,3,4,5,6,7,16*((k:ℝ)+1)} : Finset ℝ) (1/16)
      (1/16 + 1/(128*((k:ℝ)+1))) := by
  classical
  let S : Finset ℝ := {2,3,4,5,6,7}
  let c : ℝ := (k:ℝ)+1
  have hc : 1 ≤ c := by
    have h : (0:ℝ) ≤ k := by positivity
    dsimp [c]
    linarith
  have hd : 0 < 16*c := by positivity
  have hcell (s : ℝ) (hs : s ∈ Icc (1/16:ℝ) (1/8)) : LonelyAt S s := by
    intro d hm
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply Fresh.Localisation.clear_of_window 0 <;> push_cast <;>
      linarith [hs.1,hs.2]
  have hslow : FirstClearFrom S (1/16) (1/16) :=
    ⟨le_rfl,hcell _ ⟨le_rfl,by norm_num⟩,fun _ h _ => h⟩
  have hphase : (16*c)*(1/16) = (((k:ℤ)+1 : ℤ):ℝ) := by
    push_cast
    dsimp [c]
    ring
  have hnear : |(16*c)*(1/16)-(((k:ℤ)+1 : ℤ):ℝ)| < 1/8 := by
    rw [hphase,sub_self,abs_zero]
    norm_num
  have hway : InWay (16*c) (1/16) := (distInt_le _ _).trans_lt hnear
  let u := nextOpening (16*c) (1/16)
  have hu : FirstClearFrom {16*c} (1/16) u := by
    refine ⟨(lt_nextOpening hd hway).le,?_,fun s hs hclear => ?_⟩
    · intro d hd'
      rw [Finset.mem_singleton.mp hd']
      exact not_inWay_iff.mp (not_inWay_at_nextOpening hd)
    · by_contra! h
      exact (not_inWay_iff.mpr (hclear _ (Finset.mem_singleton_self _)))
        (inWay_until_opening hd hway hs h)
  have huform : u = 1/16 + 1/(128*c) := by
    dsimp only [u]
    rw [nextOpening_eq hnear]
    push_cast
    change (c+1/8)/(16*c) = _
    field_simp
    ring
  have hub : u ≤ 1/8 := by
    rw [huform]
    have hq : (1:ℝ)/(128*c) ≤ 1/128 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith
  have hj := block_first_clear_in_cell hslow hu hcell hub
  rw [huform] at hj
  have he : S ∪ {16*c} = ({2,3,4,5,6,7,16*((k:ℝ)+1)} : Finset ℝ) := by
    ext x
    simp [S,c]
  rw [he] at hj
  exact hj

#print axioms block_first_clear_lower
#print axioms block_first_clear_in_cell
#print axioms anchor_cascadeSeq
#print axioms anchor_cell_transport
#print axioms anchor_cell_accepts_iff
#print axioms single_reading_cell_of_width
#print axioms anchor_progression_transport
#print axioms anchor_residue_cell
#print axioms six_consecutive_and_multiple

end Fresh.Cascade
