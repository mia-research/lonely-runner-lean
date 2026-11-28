import Fresh.TailStrip49Cert
import Fresh.TailWidthCertCode

/-!
# Soundness of the width-check certificates (E984)

Written 2026-11-28.  New file; nothing existing is edited.

The four width checks of E927 (`smallSlowWidthCheck`, `slowCap51WidthCheck`,
`twoFastWidthCheck`, `threeFastWidthCheck`) each feed `of_checkFirstWith`, whose only
consumed facts are the leaf-level soundness steps of `Fresh.TailStrip49Cover`:
`slow_sound` (a passing `slowCheck` gives an in-band cell with clearance for every reading
but the last) and `width_of_checked_cell` (a passing `wideCell` gives its width).  This
file re-derives that chain for the coded certificates of `Fresh.TailWidthCertCode`, so
that a kernel-checked code list gives the same conclusions the checked searches gave:

* `widthLeafOK_sound`: each of the three leaf kinds gives a retained cell (or a
  contradiction with the hypotheses), for every tuple in the box.
* `checkWCode_sound`: a passing code gives `WidthOK` on its box; splits compose by
  `widthOK_split` (the `boxOK_split` induction).
* `wseg_of_chunk`, `wseg_one`, `wseg_join`, `wslice_of_seg`: the `Seg` bookkeeping of
  `Fresh.TailStrip49Cert`, generalised to an arbitrary box predicate `P`.
* `widthCells_of_slices`: slices for every root of the strip give the retained-cell
  conclusion, the shape `retainedCell_of_paddedWidth_check` returns.
* `bandClearPoint_of_retained_cell`: the capped route's last step, the body of
  `TailStrip49Cover.widthCover_sound` (private there) — a retained cell of width at
  least `1/den` with `2 * den ≤ g 6` is a clear point, by the blocker-width inequality
  `x * (U - L) < 2` against `2 ≤ g 6 * (U - L)`.

Grades: [L] for every theorem here.  The claim the width checks support is the covering
tag of their consumers (`bandClearPoint_of_slow_cap17`, `bandClearPoint_of_slow_cap51`,
`bandClearPoint_of_twoFast`, `bandClearPoint_of_threeFast` and the composites), carried
over unchanged by the kernel restatements in `Fresh.TailSlowWidthKernel` and
`Fresh.TailTwoFastKernel`.  The search is not trusted: any code that passes `checkWCode`
gives the conclusion.
-/

namespace Fresh.TailWidthCert

open Fresh Fresh.TailStrip49 Fresh.TailStrip49Cert Set

/-- The retained-cell conclusion every width leaf feeds. -/
def WidthOK (copies cap den : Nat) (box : Box) : Prop :=
  ∀ g : Fin 7 → ℝ, inBox box g → g 0 = 1 → Monotone g →
    (∀ i : Fin 5, i.val < copies → g (coordinate i) = 1) → g 5 ≤ cap →
    ∃ L U : ℝ, InBandCell L U ∧ (1 / (den : ℝ)) ≤ U - L ∧
      ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Icc L U, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8))

private theorem scale_pos' : (0 : ℝ) < scale := by norm_num [scale]

/-- The coordinate bound the capped route uses: every reading at or below the
fifth sits below the cap, in scaled units. -/
private theorem scaled_le_cap {cap : Nat} {g : Fin 7 → ℝ}
    (ordered : Monotone g) (hcap : g 5 ≤ cap) (i : Fin 5) :
    (scale : ℝ) * g (coordinate i) ≤ ((cap * scale : Nat) : ℝ) := by
  push_cast
  rw [mul_comm (cap : ℝ)]
  exact mul_le_mul_of_nonneg_left
    ((ordered (by decide +revert : coordinate i ≤ 5)).trans hcap) scale_pos'.le

/-- **A passing width leaf gives the retained cell** [L]: the leaf disjuncts of the
width route, through `slow_sound` and `width_of_checked_cell` of `Fresh.TailStrip49Cover`. -/
theorem widthLeafOK_sound {copies cap den : Nat} (hcap1 : 1 ≤ cap) (hden : 0 < den)
    {box : Box} {k : Nat} {g : Fin 7 → ℝ}
    (hbox : inBox box g) (pin : g 0 = 1) (ordered : Monotone g)
    (fixed : ∀ i : Fin 5, i.val < copies → g (coordinate i) = 1) (hcap : g 5 ≤ cap)
    (h : widthLeafOK copies cap den box k = true) :
    ∃ L U : ℝ, InBandCell L U ∧ (1 / (den : ℝ)) ≤ U - L ∧
      ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Icc L U, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  unfold widthLeafOK at h
  split at h
  · simp only [List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨i, -, hi, hlow⟩ := h
    have h1 : (box.lo i : ℝ) ≤ scale * g (coordinate i) := (hbox i).1
    rw [fixed i hi, mul_one] at h1
    have h1' : box.lo i ≤ scale := by exact_mod_cast h1
    exact absurd hlow (by omega)
  · split at h
    · simp only [decide_eq_true_eq] at h
      have h4 : (box.lo 4 : ℝ) ≤ scale * g (coordinate 4) := (hbox 4).1
      have hcaple : (scale : ℝ) * g (coordinate 4) ≤ ((cap * scale : Nat) : ℝ) :=
        scaled_le_cap ordered hcap 4
      have hlow' : (((cap * scale : Nat) : ℝ)) < (box.lo 4 : ℝ) := by exact_mod_cast h
      exact absurd hlow' (by linarith)
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hc, hw⟩ := h
      have hcw : windowCheck (decodeCell box (k - 2)) = true := by
        have h' := hc
        simp only [slowCheck, Bool.and_eq_true] at h'
        exact h'.1
      have hwork : inBox (workBox copies cap box) g := by
        intro i
        refine ⟨(hbox i).1, ?_⟩
        simp only [workBox]
        by_cases hic : i.val < copies
        · rw [if_pos hic, fixed i hic, mul_one]
          have hmin : (scale : Nat) ≤ cap * scale := by
            calc
              scale = scale * 1 := (Nat.mul_one _).symm
              _ ≤ scale * cap := Nat.mul_le_mul (Nat.le_refl _) hcap1
              _ = cap * scale := mul_comm _ _
          rw [min_eq_right hmin]
        · rw [if_neg hic, Nat.cast_min]
          exact le_min (scaled_le_cap ordered hcap i) (hbox i).2
      obtain ⟨hW, hcl⟩ := slow_sound hc hwork pin
      exact ⟨time (decodeCell box (k - 2)).lo, time (decodeCell box (k - 2)).hi, hW,
        width_of_checked_cell hden hw hcw, hcl⟩

/-- **Splits compose** [L]: the two halves of a split box carry `WidthOK`. -/
theorem widthOK_split {copies cap den : Nat} {box : Box}
    (hl : WidthOK copies cap den (left box (widest box)))
    (hr : WidthOK copies cap den (right box (widest box))) :
    WidthOK copies cap den box := by
  intro g hbox pin ordered fixed hcap
  let i := widest box
  have hl' : WidthOK copies cap den (left box i) := hl
  have hr' : WidthOK copies cap den (right box i) := hr
  rcases le_total ((scale : ℝ) * g (coordinate i)) (mid box i : ℝ) with ha | hb
  · apply hl' g _ pin ordered fixed hcap
    intro j
    by_cases hj : j = i
    · subst j
      simpa [left] using And.intro (hbox i).1 ha
    · simpa [left, hj] using hbox j
  · apply hr' g _ pin ordered fixed hcap
    intro j
    by_cases hj : j = i
    · subst j
      simpa [right] using And.intro hb (hbox i).2
    · simpa [right, hj] using hbox j

/-- **A passing code gives the retained cell on its box** [L]; the induction of
`checkCode_sound`. -/
theorem checkWCode_sound {copies cap den : Nat} (hcap1 : 1 ≤ cap) (hden : 0 < den) :
    ∀ (d : Nat) (box : Box) (code : Nat), checkWCode copies cap den d box code = true →
      WidthOK copies cap den box := by
  intro d
  induction d with
  | zero => intro box code h; simp [checkWCode] at h
  | succ d ih =>
    intro box code h
    unfold checkWCode at h
    split at h
    · intro g hbox pin ordered fixed hcap
      exact widthLeafOK_sound hcap1 hden hbox pin ordered fixed hcap h
    · simp only [Bool.and_eq_true] at h
      exact widthOK_split (ih _ _ h.1) (ih _ _ h.2)

/-! ## Slices: checking the codes in separate kernel declarations -/

/-- A run of root tuples, each satisfying the box predicate `P`. -/
def WSeg (P : Box → Prop) (a s n : Nat) : Prop :=
  ∀ t ∈ ((rootTuples a).drop s).take n, P (rootOf t)

/-- **A passing chunk is a segment** [L]. -/
theorem wseg_of_chunk {copies cap den a s : Nat} {codes : List Nat}
    (hcap1 : 1 ≤ cap) (hden : 0 < den)
    (h : wChunkOK copies cap den a s codes = true) :
    WSeg (WidthOK copies cap den) a s codes.length := by
  intro t ht
  simp only [wChunkOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem ht
  have hi' : i < codes.length := hlen ▸ hi
  have hiz : i < (List.zip (((rootTuples a).drop s).take codes.length) codes).length := by
    rw [List.length_zip]; omega
  have hc := hall _ (List.getElem_mem hiz)
  rw [List.getElem_zip] at hc
  rw [← hti]
  exact checkWCode_sound hcap1 hden 40 _ _ hc

/-- **A one-tuple segment** [L]. -/
theorem wseg_one {P : Box → Prop} {a s : Nat} {t : Nat × Nat × Nat × Nat × Nat}
    (ht : ((rootTuples a).drop s).take 1 = [t]) (h : P (rootOf t)) : WSeg P a s 1 := by
  intro u hu
  rw [ht, List.mem_singleton] at hu
  exact hu ▸ h

/-- **Two segments that split a run combine** [L]. -/
theorem wseg_join {P : Box → Prop} {a s n s' m : Nat} (h₁ : WSeg P a s n) (h₂ : WSeg P a s' m)
    (e : s' = s + n) : WSeg P a s (n + m) := by
  intro t ht
  subst e
  rw [List.take_add, List.mem_append, List.drop_drop] at ht
  rcases ht with ht | ht
  · exact h₁ t ht
  · have h' : t ∈ ((rootTuples a).drop (s + n)).take m := by
      simpa only [Nat.add_comm] using ht
    exact h₂ t h'

/-- **A segment covering the whole slice** [L]. -/
theorem wslice_of_seg {P : Box → Prop} {a n : Nat} (h : WSeg P a 0 n)
    (hn : (rootTuples a).length ≤ n) : ∀ t ∈ rootTuples a, P (rootOf t) := by
  intro t ht
  apply h t
  rw [List.drop_zero, List.take_of_length_le hn]
  exact ht

/-- **The strip from slices** [L; the covering tag carries over]: if every root tuple of
every slice `1..26` satisfies `WidthOK`, the width route's retained-cell conclusion holds
for every normalised tuple with `g 5 ≤ cap`, whenever `cap ≤ 51`. -/
theorem widthCells_of_slices {copies cap den : Nat} (hcap1 : 1 ≤ cap) (hden : 0 < den)
    (hcap51 : cap ≤ 51)
    (hs : ∀ a, 1 ≤ a → a ≤ 26 → ∀ t ∈ rootTuples a, WidthOK copies cap den (rootOf t))
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (fixed : ∀ i : Fin 5, i.val < copies → g (coordinate i) = 1) (hcap : g 5 ≤ cap) :
    ∃ L U : ℝ, InBandCell L U ∧ (1 / (den : ℝ)) ≤ U - L ∧
      ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Icc L U, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  obtain ⟨a, b, c, d, e, ha, hab, hbc, hcd, hde, he, hbox⟩ :=
    roots_cover pin ordered (hcap.trans (by exact_mod_cast hcap51))
  exact hs a ha (by omega) (a, b, c, d, e) (mem_rootTuples hab hbc hcd hde he)
    g hbox pin ordered fixed hcap

/-- **A wide retained cell is a clear point** [L]: the body of
`TailStrip49Cover.widthCover_sound` (private there) — the last reading's blocker
intervals have width below `2`, against the cell's `g 6 * (U - L) ≥ 2`. -/
theorem bandClearPoint_of_retained_cell {den : Nat} {g : Fin 7 → ℝ} {L U : ℝ}
    (hden : 0 < den) (hW : InBandCell L U) (hwidth : (1 / (den : ℝ)) ≤ U - L)
    (hs : ∀ j : Fin 7, j ≠ 6 → ∀ R ∈ Icc L U, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (hfast : 2 * (den : ℝ) ≤ g 6) :
    Fresh.BandNoCarve.BandClearPoint g := by
  have hden' : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hd : (0 : ℝ) < g 6 := by linarith
  apply clear_of_unblocked hW hd hs
  rintro ⟨j, hj₀, hj₁⟩
  have ha : 0 < L := by linarith [hW.1]
  have hb : 0 < U := ha.trans_le hW.2.1
  have h₀ := (div_lt_iff₀ ha).mp hj₀
  have h₁ := (lt_div_iff₀ hb).mp hj₁
  have h₂ := mul_le_mul hfast hwidth (by norm_num) (by linarith : (0:ℝ) ≤ g 6)
  have hthree : 2 ≤ g 6 * (U - L) := by
    convert h₂ using 1
    field_simp
  linarith [show g 6 * (U - L) = g 6 * U - g 6 * L by ring]

#print axioms widthLeafOK_sound
#print axioms widthOK_split
#print axioms checkWCode_sound
#print axioms wseg_of_chunk
#print axioms wseg_join
#print axioms wslice_of_seg
#print axioms widthCells_of_slices
#print axioms bandClearPoint_of_retained_cell

end Fresh.TailWidthCert
