import Fresh.TailStrip49Compute
import Fresh.BandNoCarve
import Fresh.TailCoverComposition
import Mathlib.Data.Fin.Tuple.Sort

namespace Fresh.TailStrip49

open Fresh Fresh.Certs Set

/-- [PROVISIONAL: covering] A blocker is an open fast-rate interval
in which a single bad lap contains both ends of a slow cell. -/
-- STANDING: DEFINITION
def BlocksCell (x L U : ℝ) : Prop :=
  ∃ j : ℤ, (8 * (j : ℝ) - 1) / L < x ∧ x < (8 * (j : ℝ) + 1) / U

-- STANDING: DEFINITION
def InBandCell (L U : ℝ) : Prop :=
  1 ≤ L ∧ L ≤ U ∧ U ≤ 15 ∧ (U ≤ 7 ∨ 9 ≤ L)

theorem clear_of_unblocked {g : Fin 7 → ℝ} {L U : ℝ}
    (hw : InBandCell L U) (hd : 0 < g 6)
    (slow : ∀ j, j ≠ 6 → ∀ R ∈ Icc L U, (1/8 : ℝ) ≤ distInt (g j * (R/8)))
    (available : ¬ BlocksCell (g 6) L U) :
    Fresh.BandNoCarve.BandClearPoint g := by
  have hfast : ∃ R ∈ Icc L U, ¬ InWay (g 6) (R/8) := by
    by_contra! blocked
    obtain ⟨j,hL,hU⟩ := (tailCell_blocked_iff hd hw.2.1).1 blocked
    have ha : 0 < L := by linarith [hw.1]
    have hb : 0 < U := ha.trans_le hw.2.1
    exact available ⟨j, (div_lt_iff₀ ha).2 hL, (lt_div_iff₀ hb).2 hU⟩
  obtain ⟨R,hR,hclear⟩ := hfast
  refine ⟨R,hw.1.trans hR.1,hR.2.trans hw.2.2.1,
    hw.2.2.2.imp (hR.2.trans ·) (·.trans hR.1),fun j => ?_⟩
  by_cases hj : j = 6
  · simpa [hj] using Fresh.Cascade.not_inWay_iff.mp hclear
  · exact slow j hj R hR

noncomputable def Ratio.val (p : Ratio) : ℝ := (p.n : ℝ) / p.d
noncomputable def time (p : Ratio) : ℝ := (scale : ℝ) * p.val

def coordinate (i : Fin 5) : Fin 7 := ⟨i.val+1, by have := i.isLt; omega⟩
-- STANDING: DEFINITION
def inBox (box : Box) (g : Fin 7 → ℝ) : Prop :=
  ∀ i, (box.lo i : ℝ) ≤ scale * g (coordinate i) ∧ scale * g (coordinate i) ≤ box.hi i

private theorem scale_pos : (0 : ℝ) < scale := by norm_num [scale]

theorem Ratio.real_le {p q : Ratio} (hp : 0 < p.d) (hq : 0 < q.d)
    (h : p.le q = true) : p.val ≤ q.val := by
  have h' : p.n * q.d ≤ q.n * p.d := by simpa [Ratio.le] using h
  unfold val
  exact (div_le_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)).2 (by exact_mod_cast h')

theorem Ratio.lt_true {p q : Ratio} (hp : 0 < p.d) (hq : 0 < q.d)
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

theorem window_sound {c : Cell} (h : windowCheck c = true) :
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

theorem slow_sound {box : Box} {c : Cell} {g : Fin 7 → ℝ}
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
  have hx₀ : 49 ≤ x := by norm_num [minTop,scale] at hmin; linarith
  have hx₁ : x ≤ 51 := by norm_num [maxTop,scale] at hmax; linarith
  have hh₀ : (49 : ℝ) ≤ x * time c.hi := by
    have ht : 1 ≤ time c.hi := hw.1.trans hw.2.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₀) (sub_nonneg.mpr ht)]
  have hh₁ : x * time c.lo ≤ (765 : ℝ) := by
    have ht := hw.2.1.trans hw.2.2.1
    calc
      x * time c.lo ≤ x * 15 := mul_le_mul_of_nonneg_left ht (by linarith)
      _ ≤ 765 := by linarith
  have jlo : 1 ≤ j := by
    by_contra hbad
    have hj : (j : ℝ) ≤ 0 := by exact_mod_cast (show j ≤ 0 by omega)
    linarith
  have jhi : j ≤ 95 := by
    by_contra hbad
    have hj : (96 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 96 ≤ j by omega)
    linarith
  let k := j.toNat
  have hk : (k : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hkR : (k : ℝ) = (j : ℝ) := by exact_mod_cast hk
  have kr : 1 ≤ k ∧ k < 96 := by omega
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
-- STANDING: DEFINITION
def CellPairFor (g : Fin 7 → ℝ) : Prop :=
  ∃ L₀ U₀ L₁ U₁ : ℝ, InBandCell L₀ U₀ ∧ InBandCell L₁ U₁ ∧
    (∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Set.Icc L₀ U₀, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8))) ∧
    (∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Set.Icc L₁ U₁, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8))) ∧
    ∀ x : ℝ, 49 ≤ x → g 5 ≤ x → x ≤ 51 →
      ¬ (BlocksCell x L₀ U₀ ∧ BlocksCell x L₁ U₁)

theorem CellPairFor.bandClearPoint {g : Fin 7 → ℝ} (h : CellPairFor g)
    (ordered : g 5 ≤ g 6) (hmin : 49 ≤ g 6) (hmax : g 6 ≤ 51) :
    Fresh.BandNoCarve.BandClearPoint g := by
  obtain ⟨L₀,U₀,L₁,U₁,hw₀,hw₁,hs₀,hs₁,disjoint⟩ := h
  have hd : 0 < g 6 := by linarith
  by_cases h₀ : BlocksCell (g 6) L₀ U₀
  · exact clear_of_unblocked hw₁ hd hs₁ (fun h₁ => disjoint _ hmin ordered hmax ⟨h₀,h₁⟩)
  · exact clear_of_unblocked hw₀ hd hs₀ h₀

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

theorem coverWith_sound {g : Fin 7 → ℝ} {accept : Box → Bool} {P : Prop}
    (sound : ∀ box, accept box = true → inBox box g → P) (depth : Nat) (box : Box)
    (h : coverWith accept box depth = true) (hbox : inBox box g) : P := by
  induction depth generalizing box with
  | zero =>
    by_cases hc : accept box = true
    · exact sound box hc hbox
    · simp [coverWith, hc] at h
  | succ n ih =>
    by_cases hc : accept box = true
    · exact sound box hc hbox
    · simp only [coverWith, hc, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
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

private noncomputable def index (r : ℝ) : Nat :=
  min 26 ⌊(r + 1)/2⌋₊

private theorem index_mono : Monotone index := by
  intro a b hab
  exact min_le_min_left _ (Nat.floor_mono (by linarith))

private theorem index_bounds {r : ℝ} (hr : 1 ≤ r) : 1 ≤ index r ∧ index r ≤ 26 := by
  refine ⟨le_min (by decide) ((Nat.le_floor_iff' (by decide : (1 : Nat) ≠ 0)).2 ?_),
    min_le_left _ _⟩
  norm_num
  linarith

private theorem center_mem {r : ℝ} (hr : 1 ≤ r) (ht : r ≤ 51) :
    ((centerFace (index r)).1 : ℝ) ≤ scale*r ∧ scale*r ≤ (centerFace (index r)).2 := by
  have hf := Nat.floor_le (show 0 ≤ (r+1)/2 by linarith)
  have hs := Nat.lt_floor_add_one ((r+1)/2)
  have hk := (index_bounds hr).1
  have hidx : ((index r : ℕ) : ℝ) * 2 - 1 ≤ r ∧ r ≤ (index r : ℝ) * 2 + 1 := by
    unfold index
    rcases le_total ⌊(r+1)/2⌋₊ 26 with h | h
    · rw [min_eq_right h]
      exact ⟨by linarith, by linarith⟩
    · rw [min_eq_left h]
      have hc : (26 : ℝ) ≤ (⌊(r+1)/2⌋₊ : ℝ) := by exact_mod_cast h
      norm_num
      exact ⟨by linarith, by linarith⟩
  unfold centerFace
  dsimp only
  push_cast [Nat.cast_sub (show 1 ≤ 2 * index r by omega)]
  have sp : (0 : ℝ) ≤ scale := by positivity
  refine ⟨max_le ?_ ?_, le_min ?_ ?_⟩
  · simpa using mul_le_mul_of_nonneg_left hr sp
  · nlinarith [mul_le_mul_of_nonneg_left hidx.1 sp]
  · norm_num [maxTop,scale]
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left hidx.2 sp]

theorem roots_cover {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hmax : g 5 ≤ 51) :
    ∃ a b c d e : Nat, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ 26 ∧
      inBox (root a b c d e) g := by
  let k (i : Fin 5) := index (g (coordinate i))
  have hLow (i : Fin 5) : 1 ≤ g (coordinate i) := by
    rw [← pin]
    exact ordered (by omega)
  have hHigh (i : Fin 5) : g (coordinate i) ≤ 51 := (ordered (by decide +revert)).trans hmax
  have hmon : Monotone k := by
    intro i j hij
    exact index_mono (ordered (show coordinate i ≤ coordinate j by
      change i.val+1 ≤ j.val+1
      exact Nat.add_le_add_right hij 1))
  refine ⟨k 0, k 1, k 2, k 3, k 4, (index_bounds (hLow 0)).1,
    hmon (by decide), hmon (by decide), hmon (by decide), hmon (by decide),
    (index_bounds (hLow 4)).2, ?_⟩
  intro i
  have hh := center_mem (hLow i) (hHigh i)
  fin_cases i <;> exact hh

theorem of_checkFirstWith {accept : Box → Bool} {P : Prop}
    (checked : (List.range' 1 26).all (checkFirstWith accept) = true)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmax : g 5 ≤ 51)
    (sound : ∀ box, accept box = true → inBox box g → P) : P := by
  obtain ⟨a,b,c,d,e,ha,hab,hbc,hcd,hde,he,hbox⟩ := roots_cover pin ordered hmax
  have ha' : a ∈ List.range' 1 26 := List.mem_range'_1.mpr ⟨ha,by omega⟩
  have hb' : b ∈ List.range' a (27-a) := List.mem_range'_1.mpr ⟨hab,by omega⟩
  have hc' : c ∈ List.range' b (27-b) := List.mem_range'_1.mpr ⟨hbc,by omega⟩
  have hd' : d ∈ List.range' c (27-c) := List.mem_range'_1.mpr ⟨hcd,by omega⟩
  have he' : e ∈ List.range' d (27-d) := List.mem_range'_1.mpr ⟨hde,by omega⟩
  have ca := List.all_eq_true.mp checked a ha'
  simp only [checkFirstWith, List.all_eq_true] at ca
  exact coverWith_sound sound 32 (root a b c d e) (ca b hb' c hc' d hd' e he') hbox

theorem cells_of_check (checked : (List.range' 1 26).all checkFirst = true)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmax : g 5 ≤ 51) : CellPairFor g :=
  of_checkFirstWith checked g pin ordered hmax
    (fun _ hc hbox => cellCover_sound hc hbox pin)

theorem width_of_checked_cell {den : Nat} {c : Cell}
    (hden : 0 < den) (hw : wideCell den c = true) (hs : windowCheck c = true) :
    (1/(den : ℝ)) ≤ time c.hi - time c.lo := by
  obtain ⟨_, _, hd₀, hd₁, _⟩ := window_sound hs
  have hn : c.hi.d * c.lo.d + (den * scale) * c.lo.n * c.hi.d
      ≤ (den * scale) * c.hi.n * c.lo.d := of_decide_eq_true hw
  have hr : (c.hi.d : ℝ) * c.lo.d + (den * scale) * c.lo.n * c.hi.d
      ≤ (den * scale) * c.hi.n * c.lo.d := by exact_mod_cast hn
  have hp : (0 : ℝ) < c.lo.d := by exact_mod_cast hd₀
  have hq : (0 : ℝ) < c.hi.d := by exact_mod_cast hd₁
  unfold time Ratio.val
  rw [show (scale : ℝ) * ((c.hi.n : ℝ) / c.hi.d) -
      (scale : ℝ) * ((c.lo.n : ℝ) / c.lo.d) =
      ((scale : ℝ) * c.hi.n * c.lo.d - (scale : ℝ) * c.lo.n * c.hi.d) /
        ((c.lo.d : ℝ) * c.hi.d) by field_simp]
  apply (le_div_iff₀ (mul_pos hp hq)).2
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_iff₀ hd).2
  nlinarith only [hr]

private theorem retainedCell_of_widthCover {den : Nat} {box : Box} {g : Fin 7 → ℝ}
    (hden : 0 < den) (pin : g 0 = 1) (hc : widthCover den box = true)
    (hbox : inBox box g) :
    ∃ L U : ℝ, InBandCell L U ∧ 1/(den : ℝ) ≤ U-L ∧
      ∀ j, j ≠ 6 → ∀ R ∈ Icc L U, (1/8 : ℝ) ≤ distInt (g j * (R/8)) := by
  obtain ⟨c, _, h⟩ := List.any_eq_true.mp hc
  obtain ⟨hw, hs⟩ := Bool.and_eq_true_iff.mp h
  have hwindow : windowCheck c = true := (Bool.and_eq_true_iff.mp hs).1
  obtain ⟨hW, hslow⟩ := slow_sound hs hbox pin
  exact ⟨time c.lo, time c.hi, hW, width_of_checked_cell hden hw hwindow, hslow⟩

private theorem widthCover_sound {den : Nat} {box : Box} {g : Fin 7 → ℝ}
    (hden : 0 < den) (pin : g 0 = 1) (hc : widthCover den box = true)
    (hbox : inBox box g) (hfast : 2 * (den : ℝ) ≤ g 6) :
    Fresh.BandNoCarve.BandClearPoint g := by
  obtain ⟨L,U,hW,hwidth,hslow⟩ := retainedCell_of_widthCover hden pin hc hbox
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  apply clear_of_unblocked hW (by linarith) hslow
  rintro ⟨j, hj₀, hj₁⟩
  have ha : 0 < L := by linarith [hW.1]
  have hb : 0 < U := ha.trans_le hW.2.1
  have h₀ := (div_lt_iff₀ ha).mp hj₀
  have h₁ := (lt_div_iff₀ hb).mp hj₁
  have h₂ := mul_le_mul hfast hwidth (by norm_num) (by linarith : (0:ℝ) ≤ g 6)
  have hthree : 2 ≤ g 6 * (U - L) := by
    convert h₂ using 1
    field_simp
  linarith [show g 6 * (U - L) =
    g 6 * U - g 6 * L by ring]

theorem bandClearPoint_of_capped_width_check {cap den : Nat}
    (checked : (List.range' 1 26).all (checkFirstWith (cappedWidthCover cap den)) = true)
    {g : Fin 7 → ℝ} (hden : 0 < den) (pin : g 0 = 1) (ordered : Monotone g)
    (hmax : g 5 ≤ 51) (hcap : g 5 ≤ cap) (hfast : 2 * (den : ℝ) ≤ g 6) :
    Fresh.BandNoCarve.BandClearPoint g := by
  apply of_checkFirstWith checked g pin ordered hmax
  intro box hc hbox
  simp only [cappedWidthCover, Bool.or_eq_true, decide_eq_true_eq] at hc
  have hbound (i : Fin 5) : (scale : ℝ) * g (coordinate i) ≤ (cap * scale : ℕ) := by
    push_cast
    rw [mul_comm (cap : ℝ)]
    exact mul_le_mul_of_nonneg_left
      ((ordered (by decide +revert : coordinate i ≤ 5)).trans hcap) scale_pos.le
  rcases hc with empty | hw
  · exact ((lt_of_lt_of_le (by exact_mod_cast empty) (hbox 4).1).not_ge (hbound 4)).elim
  · apply widthCover_sound hden pin hw _ hfast
    intro i
    refine ⟨(hbox i).1, ?_⟩
    push_cast
    exact le_min (by simpa only [Nat.cast_mul] using hbound i) (hbox i).2

/-- Soundness of a width check on slow tuples padded with copies of 1. -/
theorem retainedCell_of_paddedWidth_check {copies den : Nat}
    (checked : (List.range' 1 26).all (checkFirstWith (paddedWidthCover copies den)) = true)
    {f : Fin 7 → ℝ} (denPos : 0 < den) (pin : f 0 = 1) (hf : Monotone f)
    (hf5 : f 5 ≤ 17) (fixed : ∀ i : Fin 5, i.val < copies → f (coordinate i) = 1) :
    ∃ L U : ℝ, InBandCell L U ∧ (1 / (den : ℝ)) ≤ U-L ∧
      ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Icc L U, (1/8 : ℝ) ≤ distInt (f j * (R/8)) := by
  apply of_checkFirstWith checked f pin hf (hf5.trans (by norm_num))
  intro box h hbox
  have bounds (i : Fin 5) : (scale : ℝ) * f (coordinate i) ≤ (17 * scale : ℕ) := by
    push_cast
    rw [mul_comm (17 : ℝ)]
    exact mul_le_mul_of_nonneg_left
      ((hf (by decide +revert : coordinate i ≤ 5)).trans hf5) scale_pos.le
  have hfirst (i : Fin 5) (hi : i.val < copies) :
      (scale : ℝ) * f (coordinate i) = scale := by rw [fixed i hi, mul_one]
  simp only [paddedWidthCover, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hempty | h
  · obtain ⟨i, _, hi, hlow⟩ := hempty
    have h' : (scale : ℝ) < (box.lo i : ℝ) := by exact_mod_cast hlow
    rw [← hfirst i hi] at h'
    exact (h'.not_ge (hbox i).1).elim
  simp only [cappedWidthCover, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hempty | hw
  · have h' : ((17 * scale : ℕ) : ℝ) < (box.lo 4 : ℝ) := by exact_mod_cast hempty
    exact ((h'.trans_le (hbox 4).1).not_ge (bounds 4)).elim
  have hm : inBox
      ⟨box.lo, fun i => min (17 * scale) (if i.val < copies then scale else box.hi i)⟩ f := by
    intro i
    refine ⟨(hbox i).1, ?_⟩
    push_cast
    refine le_min (by simpa only [Nat.cast_mul] using bounds i) ?_
    by_cases hi : i.val < copies
    · simpa only [hi, if_true] using (hfirst i hi).le
    · simpa [hi] using (hbox i).2
  exact retainedCell_of_widthCover denPos pin hw hm

/-- A certificate for the five slow readings, before either fast reading is appended. -/
theorem retainedCell_of_twoFast_check
    (checked : (List.range' 1 26).all (checkFirstWith twoFastWidthCover) = true)
    {g : Fin 7 → ℝ} (pin : g 0 = 1) (ordered : Monotone g) (hcap : g 4 ≤ 17) :
    ∃ L U : ℝ, InBandCell L U ∧ (1/10 : ℝ) ≤ U-L ∧
      ∀ j : Fin 7, j.val < 5 → ∀ R ∈ Icc L U, (1/8 : ℝ) ≤ distInt (g j * (R/8)) := by
  let f : Fin 7 → ℝ := ![1,1,g 1,g 2,g 3,g 4,g 6]
  have hf : Monotone f := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · exact le_rfl
    · change 1 ≤ g 1
      rw [← pin]
      exact ordered (by decide)
    · exact ordered (show (1 : Fin 7) ≤ 2 by decide)
    · exact ordered (show (2 : Fin 7) ≤ 3 by decide)
    · exact ordered (show (3 : Fin 7) ≤ 4 by decide)
    · exact ordered (show (4 : Fin 7) ≤ 6 by decide)
  have hf5 : f 5 ≤ 17 := hcap
  obtain ⟨L,U,hW,hwid,hs⟩ :=
    retainedCell_of_paddedWidth_check (copies := 1) (den := 10) checked
      (by decide) rfl hf hf5 (by intro i hi; fin_cases i <;> first | rfl | (norm_num at hi))
  refine ⟨L,U,hW,by exact hwid,fun j hj R hR => ?_⟩
  fin_cases j
  · simpa [f, pin] using hs 0 (by decide) R hR
  · exact hs 2 (by decide) R hR
  · exact hs 3 (by decide) R hR
  · exact hs 4 (by decide) R hR
  · exact hs 5 (by decide) R hR
  · norm_num at hj
  · norm_num at hj

#print axioms retainedCell_of_twoFast_check
#print axioms bandClearPoint_of_capped_width_check

theorem bandClearPoint_of_check (checked : (List.range' 1 26).all checkFirst = true)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmin : 49 ≤ g 6) (hmax : g 6 ≤ 51) : Fresh.BandNoCarve.BandClearPoint g :=
  have ho := ordered (show (5 : Fin 7) ≤ 6 by decide)
  (cells_of_check checked g pin ordered (ho.trans hmax)).bandClearPoint ho hmin hmax

/-- The verified domain cover applies to normalized readings in any order. -/
theorem bandClearPoint_of_check_unsorted (checked : (List.range' 1 26).all checkFirst = true)
    (g : Fin 7 → ℝ) (bounds : ∀ i, 1 ≤ g i ∧ g i ≤ 51)
    (pin : ∃ i, g i = 1) (fast : ∃ i, 49 ≤ g i) :
    Fresh.BandNoCarve.BandClearPoint g := by
  let σ := Tuple.sort g
  let f := g ∘ σ
  have ordered : Monotone f := Tuple.monotone_sort g
  obtain ⟨i, hi⟩ := pin
  obtain ⟨j, hj⟩ := fast
  have hp : f 0 = 1 := by
    apply le_antisymm _ (bounds (σ 0)).1
    calc
      f 0 ≤ f (σ.symm i) := ordered (Fin.zero_le _)
      _ = 1 := by simpa [f] using hi
  have hf : 49 ≤ f 6 := by
    calc
      49 ≤ f (σ.symm j) := by simpa [f] using hj
      _ ≤ f 6 := ordered (by have := (σ.symm j).isLt; omega)
  obtain ⟨R, hL, hU, hW, hclear⟩ :=
    bandClearPoint_of_check checked f hp ordered hf (bounds (σ 6)).2
  exact ⟨R, hL, hU, hW, fun i => by simpa [f] using hclear (σ.symm i)⟩

#print axioms cells_of_check
#print axioms bandClearPoint_of_check
#print axioms bandClearPoint_of_check_unsorted

open Fresh.FilterAssembly Fresh.FilterSkeleton in
/-- [PROVISIONAL: covering] An arrangement in the closed 49–51 strip
satisfies the tail assembly's landing condition. -/
theorem tailStrip49_lands_of_check
    (stripCheck : (List.range' 1 26).all checkFirst = true)
    {v : Fin 8 → ℝ} (hv : Fresh.IsArrangement v)
    {k : Fin 8} {m : ℝ} (hm : Fresh.IsDmin v k m)
    (fast : ∃ d ∈ disparitySet v k, 49 * m ≤ d)
    (bound : ∀ d ∈ disparitySet v k, d ≤ 51 * m) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  let g (i : Fin 7) := |v (k.succAbove i) - v k| / m
  have hm0 : 0 < m := Fresh.Cascade.disparitySet_pos hv k m hm.1
  have hmem (i : Fin 7) : |v (k.succAbove i) - v k| ∈ disparitySet v k :=
    Finset.mem_image.mpr ⟨k.succAbove i, Finset.mem_erase.mpr
      ⟨Fin.succAbove_ne k i, Finset.mem_univ _⟩, rfl⟩
  have read (d : ℝ) (hd : d ∈ disparitySet v k) : ∃ i, g i = d/m := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
    exact ⟨i,rfl⟩
  have bounds (i : Fin 7) : 1 ≤ g i ∧ g i ≤ 51 := by
    refine ⟨(le_div_iff₀ hm0).2 ?_, (div_le_iff₀ hm0).2 (bound _ (hmem i))⟩
    simpa using hm.2 (hmem i)
  obtain ⟨i,hi⟩ := read m hm.1
  have pin : ∃ i, g i = 1 := ⟨i, hi.trans (div_self (ne_of_gt hm0))⟩
  obtain ⟨d,hd,hd49⟩ := fast
  obtain ⟨j,hj⟩ := read d hd
  have top : ∃ j, 49 ≤ g j := ⟨j, hj.symm ▸ (le_div_iff₀ hm0).2 hd49⟩
  obtain ⟨s,hs,hu,hw,hclear⟩ := bandClearPoint_of_check_unsorted stripCheck g bounds pin top
  apply cascadeLandsBelow17_of_clearPoint hv hm s hs hu hw
  intro d hd
  obtain ⟨i,hi⟩ := read d hd
  simpa [hi] using hclear i

#print axioms tailStrip49_lands_of_check

end Fresh.TailStrip49
