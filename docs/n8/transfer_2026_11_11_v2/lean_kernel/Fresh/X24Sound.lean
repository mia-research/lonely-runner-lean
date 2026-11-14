import X24Compute
import Fresh.GapPairs

namespace Fresh.X24Replay

open Fresh.SymbolicWindow Fresh.Certs

noncomputable def Ratio.val (p : Ratio) : ℝ := (p.n : ℝ) / p.d
noncomputable def time (p : Ratio) : ℝ := (scale : ℝ) * p.val

def coordinate (i : Fin 5) : Fin 7 := ⟨i.val+1, by have := i.isLt; omega⟩
def inBox (box : Box) (g : Fin 7 → ℝ) : Prop :=
  ∀ i, (box.lo i : ℝ) ≤ scale * g (coordinate i) ∧ scale * g (coordinate i) ≤ box.hi i

private theorem scale_pos : (0 : ℝ) < scale := by norm_num [scale]

private theorem Ratio.real_le {p q : Ratio} (hp : 0 < p.d) (hq : 0 < q.d)
    (h : p.le q = true) : p.val ≤ q.val := by
  have h' : p.n * q.d ≤ q.n * p.d := by simpa [Ratio.le] using h
  unfold val
  exact (div_le_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)).2 (by exact_mod_cast h')

private theorem Ratio.lt_true {p q : Ratio} (hp : 0 < p.d) (hq : 0 < q.d)
    (h : p.val < q.val) : p.lt q = true := by
  unfold val at h
  have h' := (div_lt_div_iff₀ (show (0 : ℝ) < p.d by exact_mod_cast hp)
    (show (0 : ℝ) < q.d by exact_mod_cast hq)).1 h
  have h'' : p.n * q.d < q.n * p.d := by exact_mod_cast h'
  simpa [Ratio.lt] using h''

private theorem time_unit (k : Nat) : time ⟨k, scale⟩ = k := by
  unfold time Ratio.val
  dsimp
  field_simp [ne_of_gt scale_pos]

private theorem window_sound {c : Cell} (h : windowCheck c = true) :
    0 < c.lo.n ∧ 0 < c.hi.n ∧ 0 < c.lo.d ∧ 0 < c.hi.d ∧ InBandCell (time c.lo) (time c.hi) := by
  simp only [windowCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hn₀, hn₁, hd₀, hd₁, hL, hLU, hU, hw⟩ := h
  have hs : 0 < scale := by decide
  have lift {p q : Ratio} (hp : 0 < p.d) (hq : 0 < q.d) (hle : p.le q = true) :
      time p ≤ time q :=
    mul_le_mul_of_nonneg_left (Ratio.real_le hp hq hle) scale_pos.le
  refine ⟨hn₀, hn₁, hd₀, hd₁, ?_⟩
  have hL' := lift hs hd₀ hL
  have hU' := lift hd₁ hs hU
  rw [time_unit] at hL' hU'
  norm_num at hL' hU'
  refine ⟨hL', lift hd₀ hd₁ hLU, hU', ?_⟩
  rcases hw with h₀ | h₁
  · have hh := lift hd₁ hs h₀
    rw [time_unit] at hh
    exact Or.inl (by simpa using hh)
  · have hh := lift hs hd₀ h₁
    rw [time_unit] at hh
    exact Or.inr (by simpa using hh)

private theorem face_sound {c : Cell} {lo hi : Nat} {x R : ℝ}
    (hlod : 0 < c.lo.d) (hhid : 0 < c.hi.d)
    (h : faceCheck c lo hi = true) (hx : (lo : ℝ) ≤ scale*x ∧ scale*x ≤ hi)
    (hR : R ∈ Set.Icc (time c.lo) (time c.hi)) :
    (1 / 8 : ℝ) ≤ distInt (x * (R / 8)) := by
  let j := (c.lo.n * lo - c.lo.d) / (8*c.lo.d)
  have raw : (8*j+1)*c.lo.d ≤ c.lo.n*lo ∧ c.hi.n*hi ≤ (8*j+7)*c.hi.d := by
    simpa only [faceCheck, Bool.and_eq_true, decide_eq_true_eq, j] using h
  have lo' : (8*(j : ℝ)+1)*(c.lo.d : ℝ) ≤ (c.lo.n : ℝ)*lo := by exact_mod_cast raw.1
  have hi' : (c.hi.n : ℝ)*hi ≤ (8*(j : ℝ)+7)*(c.hi.d : ℝ) := by exact_mod_cast raw.2
  have hd₀ : (0 : ℝ) < c.lo.d := by exact_mod_cast hlod
  have hd₁ : (0 : ℝ) < c.hi.d := by exact_mod_cast hhid
  have hxpos : 0 ≤ x :=
    nonneg_of_mul_nonneg_right ((Nat.cast_nonneg lo).trans hx.1) scale_pos
  have hlow : 8*(j : ℝ)+1 ≤ time c.lo * x := by
    unfold time Ratio.val
    rw [show (scale : ℝ) * ((c.lo.n : ℝ)/c.lo.d) * x =
      ((c.lo.n : ℝ)*((scale : ℝ)*x))/c.lo.d by ring]
    exact (le_div_iff₀ hd₀).2
      (lo'.trans (mul_le_mul_of_nonneg_left hx.1 (Nat.cast_nonneg _)))
  have hhigh : time c.hi * x ≤ 8*(j : ℝ)+7 := by
    unfold time Ratio.val
    rw [show (scale : ℝ) * ((c.hi.n : ℝ)/c.hi.d) * x =
      ((c.hi.n : ℝ)*((scale : ℝ)*x))/c.hi.d by ring]
    exact (div_le_iff₀ hd₁).2
      ((mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg _)).trans hi')
  rw [clearAt_R_iff]
  refine ⟨(j : ℤ), ?_⟩
  push_cast
  rw [mul_comm x R]
  exact ⟨hlow.trans (mul_le_mul_of_nonneg_right hR.1 hxpos),
    (mul_le_mul_of_nonneg_right hR.2 hxpos).trans hhigh⟩

private theorem slow_sound {box : Box} {c : Cell} {g : Fin 7 → ℝ}
    (h : slowCheck box c = true) (hbox : inBox box g) (hpin : g 0 = 1) :
    InBandCell (time c.lo) (time c.hi) ∧
    ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Set.Icc (time c.lo) (time c.hi),
      (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  simp only [slowCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨_, _, hd₀, hd₁, hW⟩ := window_sound h.1
  refine ⟨hW, ?_⟩
  intro j hj R hR
  have hstep (i : Fin 5) : (1 / 8 : ℝ) ≤ distInt (g (coordinate i) * (R / 8)) :=
    face_sound hd₀ hd₁ (h.2 i (List.mem_finRange _)) (hbox i) hR
  fin_cases j
  · change (1 / 8 : ℝ) ≤ distInt (g (0 : Fin 7) * (R / 8))
    rw [hpin, clearAt_R_iff]
    rcases hW.2.2.2 with h₀ | h₁
    · refine ⟨0, ?_⟩
      norm_num
      exact ⟨hW.1.trans hR.1, hR.2.trans h₀⟩
    · refine ⟨1, ?_⟩
      norm_num
      exact ⟨h₁.trans hR.1, hR.2.trans hW.2.2.1⟩
  · exact hstep 0
  · exact hstep 1
  · exact hstep 2
  · exact hstep 3
  · exact hstep 4
  · exact (hj rfl).elim

private theorem blocked_mem {c : Cell} {lo : Nat} {x : ℝ}
    (h : windowCheck c = true) (hlo : (lo : ℝ) ≤ scale*x)
    (hmin : (minTop : ℝ) ≤ scale*x) (hmax : scale*x ≤ maxTop)
    (bad : BlocksCell x (time c.lo) (time c.hi)) :
    ∃ q ∈ checkedBlockers c lo, 0 < q.lo.d ∧ 0 < q.hi.d ∧
      q.lo.val < scale*x ∧ scale*x < q.hi.val := by
  obtain ⟨hn₀, hn₁, hd₀, hd₁, hw⟩ := window_sound h
  obtain ⟨j, hj₀, hj₁⟩ := bad
  have ha := (div_lt_iff₀ (show 0 < time c.lo by linarith [hw.1])).1 hj₀
  have hb := (lt_div_iff₀ (show 0 < time c.hi by linarith [hw.1,hw.2.1])).1 hj₁
  have hx₀ : 45/2 ≤ x := by norm_num [minTop,scale] at hmin; linarith
  have hx₁ : x ≤ 51/2 := by norm_num [maxTop,scale] at hmax; linarith
  have hh₀ : (45/2 : ℝ) ≤ x * time c.hi := by
    have ht : 1 ≤ time c.hi := hw.1.trans hw.2.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₀) (sub_nonneg.mpr ht)]
  have hh₁ : x * time c.lo ≤ (765/2 : ℝ) := by
    have ht := hw.2.1.trans hw.2.2.1
    calc
      x * time c.lo ≤ x * 15 := mul_le_mul_of_nonneg_left ht (by linarith)
      _ ≤ 765/2 := by linarith
  have jlo : 1 ≤ j := by
    by_contra hbad
    have hj : (j : ℝ) ≤ 0 := by exact_mod_cast (show j ≤ 0 by omega)
    linarith
  have jhi : j ≤ 47 := by
    by_contra hbad
    have hj : (48 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 48 ≤ j by omega)
    linarith
  let k := j.toNat
  have hk : (k : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hkR : (k : ℝ) = (j : ℝ) := by exact_mod_cast hk
  have kr : 1 ≤ k ∧ k < 48 := by omega
  have hdl : (0 : ℝ) < c.lo.d := by exact_mod_cast hd₀
  have hdr : (0 : ℝ) < c.hi.d := by exact_mod_cast hd₁
  have hnl : (0 : ℝ) < c.lo.n := by exact_mod_cast hn₀
  have hnr : (0 : ℝ) < c.hi.n := by exact_mod_cast hn₁
  have obsLo : (obstruction c k).lo.val < scale*x := by
    unfold obstruction Ratio.val
    dsimp only
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 8*k)]
    push_cast
    rw [hkR]
    apply (div_lt_iff₀ hnl).2
    apply (lt_div_iff₀ hdl).1
    calc
      _ < x * time c.lo := ha
      _ = ((scale : ℝ)*x*(c.lo.n : ℝ))/c.lo.d := by unfold time Ratio.val; ring
  have obsHi : scale*x < (obstruction c k).hi.val := by
    unfold obstruction Ratio.val
    dsimp only
    push_cast
    rw [hkR]
    apply (lt_div_iff₀ hnr).2
    apply (div_lt_iff₀ hdr).1
    calc
      ((scale : ℝ)*x*(c.hi.n : ℝ))/c.hi.d = x * time c.hi := by
        unfold time Ratio.val
        ring
      _ < _ := hb
  refine ⟨obstruction c k, ?_, hn₀, hn₁, obsLo, obsHi⟩
  apply List.mem_filter.2
  refine ⟨List.mem_map.2 ⟨k, List.mem_range'_1.2 kr, rfl⟩, ?_⟩
  have hmax' : scale*x ≤ (whole maxTop).val := by simpa [whole, Ratio.val] using hmax
  have hlo' : (whole lo).val ≤ scale*x := by simpa [whole, Ratio.val] using hlo
  simp only [inTopBand, Bool.and_eq_true]
  exact ⟨⟨Ratio.lt_true hn₀ hn₁ (obsLo.trans obsHi),
    Ratio.lt_true hn₀ (by decide) (obsLo.trans_le hmax')⟩,
    Ratio.lt_true (by change 0 < 1; decide) hn₁ (hlo'.trans_lt obsHi)⟩

/-- The same two cells work for the entire admissible interval of the last
reading. A single universally available cell may be used twice. -/
def CellPairFor (g : Fin 7 → ℝ) : Prop :=
  ∃ L₀ U₀ L₁ U₁ : ℝ, InBandCell L₀ U₀ ∧ InBandCell L₁ U₁ ∧
    (∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Set.Icc L₀ U₀, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8))) ∧
    (∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Set.Icc L₁ U₁, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8))) ∧
    ∀ x : ℝ, 45/2 ≤ x → g 5 ≤ x → x ≤ 51/2 →
      ¬ (BlocksCell x L₀ U₀ ∧ BlocksCell x L₁ U₁)

theorem CellPairFor.bandClearPoint {g : Fin 7 → ℝ} (h : CellPairFor g)
    (ordered : g 5 ≤ g 6) (hmin : 45/2 ≤ g 6) (hmax : g 6 ≤ 51/2) :
    Fresh.BandNoCarve.BandClearPoint g := by
  obtain ⟨L₀,U₀,L₁,U₁,hw₀,hw₁,hs₀,hs₁,disjoint⟩ := h
  exact bandClearPoint_of_two_cells g 6 hw₀ hw₁ (by linarith) hs₀ hs₁
    (disjoint _ hmin ordered hmax)

private theorem pair_sound {box : Box} {c d : Cell} {g : Fin 7 → ℝ}
    (check : pairCheck box c d = true) (hbox : inBox box g) (pin : g 0 = 1) :
    CellPairFor g := by
  simp only [pairCheck, Bool.and_eq_true] at check
  obtain ⟨⟨hc, hd⟩, hsep⟩ := check
  obtain ⟨hwc, hsc⟩ := slow_sound hc hbox pin
  obtain ⟨hwd, hsd⟩ := slow_sound hd hbox pin
  refine ⟨time c.lo, time c.hi, time d.lo, time d.hi, hwc, hwd, hsc, hsd, ?_⟩
  intro x hx₀ ordered hx₁
  have hmin : (minTop : ℝ) ≤ scale*x := by norm_num [minTop,scale]; linarith
  have hmax : (scale : ℝ)*x ≤ maxTop := by norm_num [maxTop,scale]; linarith
  have hface := (hbox 4).1
  change (box.lo 4 : ℝ) ≤ scale * g 5 at hface
  have hlo : ((max minTop (box.lo 4) : Nat) : ℝ) ≤ scale*x := by
    push_cast
    exact max_le hmin (hface.trans (mul_le_mul_of_nonneg_left ordered scale_pos.le))
  rintro ⟨b₀,b₁⟩
  have hcw : windowCheck c = true := by
    simp only [slowCheck, Bool.and_eq_true] at hc
    exact hc.1
  have hdw : windowCheck d = true := by
    simp only [slowCheck, Bool.and_eq_true] at hd
    exact hd.1
  obtain ⟨p,hp,hpl,hpu,h₀,h₁⟩ := blocked_mem hcw hlo hmin hmax b₀
  obtain ⟨q,hq,hql,hqu,h₂,h₃⟩ := blocked_mem hdw hlo hmin hmax b₁
  have h := List.all_eq_true.mp (List.all_eq_true.mp hsep p hp) q hq
  simp only [apart, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (h₁.trans_le (Ratio.real_le hpu hql h)).not_ge h₂.le
  · exact (h₃.trans_le (Ratio.real_le hqu hpl h)).not_ge h₀.le

private theorem cellCover_sound {box : Box} {g : Fin 7 → ℝ}
    (h : cellCover box = true) (hbox : inBox box g) (pin : g 0 = 1) : CellPairFor g := by
  unfold cellCover at h
  split at h
  · exact pair_sound h hbox pin
  · contradiction

theorem cover_sound {g : Fin 7 → ℝ} (pin : g 0 = 1) (depth : Nat) (box : Box)
    (h : cover box depth = true) (hbox : inBox box g) : CellPairFor g := by
  induction depth generalizing box with
  | zero =>
    by_cases hc : cellCover box = true
    · exact cellCover_sound hc hbox pin
    · simp [cover, hc] at h
  | succ n ih =>
    by_cases hc : cellCover box = true
    · exact cellCover_sound hc hbox pin
    · simp only [cover, hc, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
      let i := widest box
      rcases le_total ((scale : ℝ)*g (coordinate i)) (mid box i : ℝ) with ha | hb
      · apply ih (left box i) h.1
        intro j
        by_cases hj : j=i
        · subst j
          simpa [left] using And.intro (hbox i).1 ha
        · simpa [left, hj] using hbox j
      · apply ih (right box i) h.2
        intro j
        by_cases hj : j=i
        · subst j
          simpa [right] using And.intro hb (hbox i).2
        · simpa [right, hj] using hbox j

end Fresh.X24Replay
