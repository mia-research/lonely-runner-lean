import Fresh.NativeRationalGuardPaths
import Fresh.NativeMixedLapWindow

namespace Fresh.NativeGuardedRouteRows

open Fresh Cascade Localisation NativeRationalGuardPaths NativeStrictRatioGuards
open scoped Classical

inductive Mode where
  | clear | capture | optional
  deriving DecidableEq

structure Band where
  lap : ℤ
  mode : Mode

def Band.lower (b : Band) : ℚ := (b.lap : ℚ) + match b.mode with
  | .clear => 1 / 8
  | .capture => -1 / 8
  | .optional => -7 / 8

def Band.upper (b : Band) : ℚ := (b.lap : ℚ) + match b.mode with
  | .capture => 1 / 8
  | _ => 7 / 8

def Band.exit (b : Band) : ℚ := (b.lap : ℚ) + 1 / 8

def Band.strict (b : Band) : Bool := decide (b.mode = .capture)

structure Anchor where
  index : Fin 7
  num : ℚ
  deriving DecidableEq

noncomputable def Anchor.time (a : Anchor) (r : Fin 7 → ℝ) : ℝ := (a.num : ℝ) / r a.index

structure Row where
  src : Anchor
  dst : Anchor
  band : Fin 7 → Band

def phaseGuards (a : Anchor) (b : Band) (i : Fin 7) : List Guard :=
  [⟨i, a.index, a.num / b.lower, b.strict⟩,
   ⟨a.index, i, b.upper / a.num, b.strict⟩]

def Row.guards (w : Row) : List Guard :=
  (List.finRange 7).flatMap fun i =>
    phaseGuards w.src (w.band i) i ++
      if (w.band i).mode = .clear then [] else
        [⟨i, w.dst.index, w.dst.num / (w.band i).exit, i != w.dst.index⟩]

private theorem cross {b x y c : ℝ} (hb : 0 < b) (q : Bool)
    (h : Holds q y ((c / b) * x)) : Holds q (b * y) (c * x) := by
  rw [div_mul_eq_mul_div] at h
  cases q
  · change y ≤ (c * x) / b at h
    change b * y ≤ c * x
    simpa only [mul_comm b y] using (le_div_iff₀ hb).1 h
  · change y < (c * x) / b at h
    change b * y < c * x
    simpa only [mul_comm b y] using (lt_div_iff₀ hb).1 h

private theorem bounds (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (a : Anchor) (b : Band) (i : Fin 7) (ha : 0 < a.num) (hl : 0 < b.lower)
    (hg : ∀ g ∈ phaseGuards a b i, g.valid r) :
    Holds b.strict (b.lower : ℝ) (r i * a.time r) ∧
      Holds b.strict (r i * a.time r) (b.upper : ℝ) := by
  have hlo := hg ⟨i, a.index, a.num / b.lower, b.strict⟩ (by simp [phaseGuards])
  have hhi := hg ⟨a.index, i, b.upper / a.num, b.strict⟩ (by simp [phaseGuards])
  unfold Guard.valid at hlo hhi
  dsimp at hlo hhi
  push_cast at hlo hhi
  have hlow := cross (by exact_mod_cast hl) b.strict hlo
  have hhigh := cross (by exact_mod_cast ha) b.strict hhi
  cases h : b.strict
  · simp only [Holds, h, Bool.false_eq_true, if_false] at hlow hhigh ⊢
    unfold Anchor.time
    rw [← mul_div_assoc, le_div_iff₀ (hp _), div_le_iff₀ (hp _), mul_comm (r i) (a.num : ℝ)]
    exact ⟨hlow, hhigh⟩
  · simp only [Holds, h] at hlow hhigh ⊢
    unfold Anchor.time
    rw [← mul_div_assoc, lt_div_iff₀ (hp _), div_lt_iff₀ (hp _), mul_comm (r i) (a.num : ℝ)]
    exact ⟨hlow, hhigh⟩

private theorem captures (b : Band) {d T : ℝ} (hm : b.mode = .capture)
    (h : Holds b.strict (b.lower : ℝ) (d * T) ∧ Holds b.strict (d * T) (b.upper : ℝ)) :
    |d * T - (b.lap : ℝ)| < 1 / 8 := by
  simp [Band.strict, Band.lower, Band.upper, Holds, hm] at h
  exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem clears (b : Band) {d T : ℝ} (hm : b.mode = .clear)
    (h : Holds b.strict (b.lower : ℝ) (d * T) ∧ Holds b.strict (d * T) (b.upper : ℝ)) :
    1 / 8 ≤ Fresh.distInt (d * T) := by
  simp [Band.strict, Band.lower, Band.upper, Holds, hm] at h
  exact clear_of_window b.lap (by linarith [h.1]) (by linarith [h.2])

/-- The listed rational guards suffice for this native move, including
readings whose capture status may vary without changing the winner. -/
theorem Row.move (w : Row) (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (ha : 0 < w.src.num) (hl : ∀ i, 0 < (w.band i).lower)
    (he : ∀ i, 0 < (w.band i).exit)
    (hwin : (w.band w.dst.index).mode = .capture)
    (hnum : w.dst.num = (w.band w.dst.index).exit)
    (hg : ∀ g ∈ w.guards, g.valid r) :
    IsMove (Finset.univ.image r) (w.src.time r) (w.dst.time r) := by
  have phase (i : Fin 7) := bounds r hp w.src (w.band i) i ha (hl i)
    (fun g hg' => hg g (List.mem_flatMap.mpr ⟨i, by simp, List.mem_append_left _ hg'⟩))
  have hw := captures _ hwin (phase w.dst.index)
  have num (i : Fin 7) : ((w.band i).exit : ℝ) = ((w.band i).lap : ℝ) + 1 / 8 := by
    simp [Band.exit]
  refine Or.inr ⟨r w.dst.index, Finset.mem_image_of_mem r (Finset.mem_univ _),
    (Cascade.distInt_le _ _).trans_lt hw, ?_, ?_⟩
  · rw [nextOpening_eq hw, Anchor.time, hnum, num]
  · intro d hd hway
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    have hmode : (w.band i).mode ≠ .clear := fun h => (not_lt_of_ge (clears _ h (phase i))) hway
    let g : Guard := ⟨i, w.dst.index, w.dst.num / (w.band i).exit, i != w.dst.index⟩
    have hguard := hg g (List.mem_flatMap.mpr ⟨i, by simp, by simp [hmode, g]⟩)
    unfold Guard.valid at hguard
    dsimp [g] at hguard
    push_cast at hguard
    have hx := cross (by exact_mod_cast he i) (i != w.dst.index) hguard
    have hbound : ((w.band i).exit : ℝ) * r w.dst.index ≤ (w.dst.num : ℝ) * r i := by
      generalize h : (i != w.dst.index) = q at hx
      cases q <;> simp [Holds] at hx
      · exact hx
      · exact hx.le
    have hsingle : step ({r i} : Finset ℝ) (w.src.time r) = ((w.band i).exit : ℝ) / r i := by
      have ho : step ({r i} : Finset ℝ) (w.src.time r) = nextOpening (r i) (w.src.time r) := by
        apply isMove_unique (isMove_step _ _)
        exact Or.inr ⟨r i, by simp, hway, rfl, by simp⟩
      have hlo : ((w.band i).lap : ℝ) - 7 / 8 ≤ r i * w.src.time r := by
        rcases hm : (w.band i).mode with _ | _ | _
        · exact (hmode hm).elim
        · have hh := (phase i).1
          simp [Band.strict, Band.lower, Holds, hm] at hh
          linarith
        · have hh := (phase i).1
          simp [Band.strict, Band.lower, Holds, hm] at hh
          linarith
      have hhi : r i * w.src.time r ≤ ((w.band i).lap : ℝ) + 7 / 8 := by
        rcases hm : (w.band i).mode with _ | _ | _
        · exact (hmode hm).elim
        · have hh := (phase i).2
          simp [Band.strict, Band.upper, Holds, hm] at hh
          linarith
        · have hh := (phase i).2
          simp [Band.strict, Band.upper, Holds, hm] at hh
          linarith
      have hs := NativeMixedLapWindow.single_step (w.band i).lap hlo hhi
      by_cases hc : ((w.band i).lap : ℝ) - 1 / 8 < r i * w.src.time r ∧
          r i * w.src.time r < ((w.band i).lap : ℝ) + 1 / 8
      · simpa only [if_pos hc, num] using hs
      · rw [if_neg hc, ho] at hs
        exact (lt_nextOpening (hp i) hway).ne' hs |>.elim
    have hactual := isMove_unique (isMove_step ({r i} : Finset ℝ) (w.src.time r))
      (Or.inr ⟨r i, by simp, hway, rfl, by simp⟩)
    rw [← hactual, hsingle, Anchor.time, div_le_div_iff₀ (hp i) (hp _)]
    exact hbound

theorem terminal (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i) (a : Anchor) (b : Fin 7 → Band)
    (ha : 0 < a.num) (hl : ∀ i, 0 < (b i).lower)
    (hc : ∀ i, (b i).mode = .clear)
    (hg : ∀ i, ∀ g ∈ phaseGuards a (b i) i, g.valid r) :
    LonelyAt (Finset.univ.image r) (a.time r) := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  exact clears _ (hc i) (bounds r hp a (b i) i ha (hl i) (hg i))

#print axioms Row.move
#print axioms terminal

end Fresh.NativeGuardedRouteRows
