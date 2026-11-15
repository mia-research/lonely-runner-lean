import Fresh.WordCoverSide

/-!
# The word-extraction lemma (domain-carried): falsified exactly, and the repaired shape

Written 2026-11-15.  New file; nothing existing is edited.  This is the repair the external
review demanded for the OWED `Fresh.WordCoverSide.NoClearPointWordRealized` (WordCoverSide.lean:235):
"no `W₁` clear point on `[9,15]` ⟹ some `W₁` word realized on `g`".  The review's counterexample
(all `g i = 1/16`) killed the statement as written, and the sanctioned repair was to carry the
normalization domain `∀ i, (1:ℝ) ≤ g i`.  **That repaired statement is false too.**  This file
proves the falsification with an exact rational witness, proves the boundary of what is true
without per-box census data, and provides the box-carried consumer bridge the glue must re-wire to.

## The witness (`g0`)

`g0 = (7/4, 8/5, 16/11, 4/3, 16/13, 8/7, 16/15)` — readings `16/k`, all in `[16/15, 7/4] ⊆ [1, 2]`.
Zones of reading `ρ` at level `j` are the open intervals `((8j−1)/ρ, (8j+1)/ρ)` (`inZone`).

* **No clear point**: the seven level-`2` zones `(15/ρ, 17/ρ)` overlap left-to-right and their
  union is `(60/7, 255/16) ⊇ [9,15]` (`g0_noClearPoint`; seven closed sub-intervals of `[9,15]`,
  each inside one zone, are proved by `linarith` on exact rationals).
* **No word** (`g0_noWord`): the unique zone covering `9` is `(0, 2)` (level bounds: with readings
  in `[16/15, 7/4]`, any zone covering `9` has `8j ∈ (8.6, 16.75)`, so `j = 2`, forcing
  `ρ ∈ (5/3, 17/9)`, i.e. reading `7/4` — index `0`); the zones covering `15` are exactly
  `(6, 2)` and `(1, 3)`.  Every word must contain `(0,2)` and one of those two.  Since consecutive
  word entries have strictly increasing levels (`adj_before_lt`: levels increase along list order),
  the `(6,2)` case dies as `2 < 2`.  In the `(1,3)` case `(0,2)` precedes `(1,3)`, so `(0,2)` has an
  immediate successor `z` with `2 < z.2` whose zone overlaps `(0,2)`'s inside `[9,15]`; but any such
  overlap point `R` satisfies `R < 68/7` (from `(7/4)·R < 17`), so `8·z.2 − 1 < (7/4)·(68/7) = 17`,
  i.e. `z.2 ≤ 2` — contradiction.  The only level-`3` zones in window (`(92/7, 100/7)`,
  `(115/8, 125/8)`) never reach back to `(0,2)`'s zone: the unique `9`-coverer is a sink.

## Boundaries proved (`sharp`)

* `clearPoint_of_le_five_thirds`: readings in `[1, 5/3]` always admit the clear point `s = 9`
  (`9ρ/8 ∈ [9/8, 15/8]`, so `distInt ≥ 1/8`); hence `NoClearPointWordRealized` holds **vacuously**
  there (`wordExtract_of_low`).  A nearby failure: the exact rational sweep of the session log
  finds counterexamples with all readings in `(1, 27/16]` (`27/16 > 5/3`), e.g.
  `(37, 35, 41, 45, 49, 54, 50)/32`; there is provably no counterexample with all readings `≤ 5/3`.
  This example rules out bounds at or above `27/16`. The falsifying regime
  also extends upward (`WordCoverSide`'s own `(1..6, 8)` census scale admits mixed-reading counterexamples
  in half-unit face boxes — see the session log sweep; distinct box coordinates do not repair).
* `domainCarried_refuted`: `¬ (∀ g, (∀ i, 1 ≤ g i) → NoClearPointWordRealized g)` — the
  domain-carried restatement is refuted by `g0`.
* `boxCarried_arbitrary_refuted`: `g0` lies inside the face box of `b0 = (2,2,1,1,1,1,1)`
  (`FaceLo/FaceHi` of `Fresh.FilterAssembly`), so box membership for an **arbitrary** `b` does not
  repair either.  The word-cover direction is genuinely per-box census data.

## The repaired consumer shape

`NoClearPointWordRealizedBox b g` (box-carried) with the glue `composedTotal_of_wordCover_box` /
`oneSidedSound_of_wordCover_box` — exactly `Fresh.WordCoverSide.composedTotal_of_wordCover` with
the OWED hypothesis weakened to carry the box, which is the weakest form the falsifications above
leave viable (all stronger uniform forms are refuted).  For low boxes (`FaceLo b i ≥ 1`,
`FaceHi b i ≤ 5/3`, e.g. the all-`1` box where `FaceHi = 3/2`) the hypothesis is **discharged**
here (`wordCoverBox_of_low`) via the vacuity lemma.  The sibling OWED `FamilyCoversWordEdges`
needs nothing from this file (it already carries box membership in its hypothesis).

All arithmetic is exact (`norm_num`/`linarith` on rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound) — `sorryAx` is failure.
-/

namespace Fresh.WordExtract

open Fresh.WordCoverSide Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
open Fresh.FilterAssembly Fresh.FrontierFamilyCap Fresh.Localisation

/-! ## 1. Levels increase along list order -/

/-- Prepending an entry preserves adjacency. -/
private theorem hadj_cons {a p q : Fin 7 × ℕ} {r : List (Fin 7 × ℕ)} (h : HasAdj r p q) :
    HasAdj (a :: r) p q := by
  obtain ⟨m₁, m₂, he⟩ := h
  exact ⟨a :: m₁, m₂, by simp [he]⟩

/-- **Levels increase along list order**: if every adjacent pair of a list has strictly
increasing levels, then any entry occurring earlier in the list has strictly smaller level
than any entry occurring later. -/
private theorem adj_before_lt : ∀ (w l₁ : List (Fin 7 × ℕ)) (x y : Fin 7 × ℕ)
    (l₂ l₃ : List (Fin 7 × ℕ)), (∀ p q, HasAdj w p q → p.2 < q.2) →
    w = l₁ ++ x :: l₂ ++ y :: l₃ → x.2 < y.2 := by
  intro w
  induction w with
  | nil => intro l₁ x y l₂ l₃ _ heq; simp at heq
  | cons a r ih =>
    intro l₁ x y l₂ l₃ h heq
    cases l₁ with
    | nil =>
      simp only [List.nil_append] at heq
      injection heq with hx hr
      subst hx
      cases l₂ with
      | nil =>
        exact h a y ⟨[], l₃, by simp [hr]⟩
      | cons b l₂' =>
        have hab : a.2 < b.2 := h a b ⟨[], l₂' ++ y :: l₃, by simp [hr]⟩
        have hby : b.2 < y.2 :=
          ih [] b y l₂' l₃ (fun p q hpq => h p q (hadj_cons hpq)) (by simp [hr])
        omega
    | cons c l₁' =>
      simp only [List.cons_append] at heq
      injection heq with hc hr
      exact ih l₁' x y l₂ l₃ (fun p q hpq => h p q (hadj_cons hpq)) (by rw [hr])

/-- Two distinct members of a list occur in one order or the other. -/
private theorem mem_before_or_after {w : List (Fin 7 × ℕ)} {x y : Fin 7 × ℕ}
    (hx : x ∈ w) (hy : y ∈ w) (hne : x ≠ y) :
    (∃ l₁ l₂ l₃, w = l₁ ++ x :: l₂ ++ y :: l₃) ∨ (∃ l₁ l₂ l₃, w = l₁ ++ y :: l₂ ++ x :: l₃) := by
  obtain ⟨m₁, m₂, e⟩ := List.mem_iff_append.mp hx
  rw [e] at hy
  rcases List.mem_append.mp hy with hy1 | hy2
  · obtain ⟨m₁', m₁'', e1⟩ := List.mem_iff_append.mp hy1
    refine Or.inr ⟨m₁', m₁'', m₂, ?_⟩
    rw [e, e1]
  · rcases List.mem_cons.mp hy2 with rfl | hy2'
    · exact absurd rfl hne
    · obtain ⟨m₂', m₂'', e2⟩ := List.mem_iff_append.mp hy2'
      refine Or.inl ⟨m₁, m₂', m₂'', ?_⟩
      rw [e, e2]; simp

/-! ## 2. The witness `g0` and its basic bounds -/

/-- The falsifying arrangement: seven readings `16/k`-spaced in `[16/15, 7/4]`. -/
noncomputable def g0 : Fin 7 → ℝ := ![7/4, 8/5, 16/11, 4/3, 16/13, 8/7, 16/15]

theorem g0_bounds (i : Fin 7) : 16/15 ≤ g0 i ∧ g0 i ≤ 7/4 := by
  fin_cases i <;> norm_num [g0]

#print axioms g0_bounds

theorem g0_dom (i : Fin 7) : (1 : ℝ) ≤ g0 i := by linarith [g0_bounds i]

#print axioms g0_dom

theorem g0_le (i : Fin 7) : g0 i ≤ 7/4 := (g0_bounds i).2

#print axioms g0_le

/-! ## 3. `g0` has no clear point on `[9,15]` -/

/-- A zone reading at level `j` puts the phase `g i · (s/8)` within `1/8` of the integer `j`. -/
-- STANDING: PROVED (helper)
theorem distInt_lt_of_zone {g : Fin 7 → ℝ} {i : Fin 7} {j : ℕ} {s : ℝ}
    (hz : inZone g i j s) : distInt (g i * (s / 8)) < 1/8 := by
  obtain ⟨h1, h2⟩ := hz
  by_contra hcle
  have hle := (le_distInt_iff (1/8) (g i * (s / 8))).mp (not_lt.mp hcle) (j : ℤ)
  push_cast at hle
  have e : g i * (s / 8) - (j : ℝ) = (g i * s - (j : ℝ) * 8) / 8 := by
    field_simp
  have habs : |g i * (s / 8) - (j : ℝ)| < 1/8 := by
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8), div_lt_iff₀ (by norm_num : (0 : ℝ) < 8),
      abs_lt]
    constructor <;> linarith
  linarith

#print axioms distInt_lt_of_zone

theorem g0_noClearPoint :
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g0 i * (s / 8))) := by
  rintro ⟨s, hs9, hs15, hall⟩
  have g00 : g0 0 = 7/4 := rfl
  have g01 : g0 1 = 8/5 := rfl
  have g02 : g0 2 = 16/11 := rfl
  have g03 : g0 3 = 4/3 := rfl
  have g04 : g0 4 = 16/13 := rfl
  have g05 : g0 5 = 8/7 := rfl
  have g06 : g0 6 = 16/15 := rfl
  have key : ∃ i : Fin 7, distInt (g0 i * (s / 8)) < 1/8 := by
    rcases le_or_gt s (19/2) with h | h
    · have hz : inZone g0 0 2 s := ⟨by rw [g00]; linarith, by rw [g00]; linarith⟩
      exact ⟨0, distInt_lt_of_zone hz⟩
    rcases le_or_gt s (21/2) with h | h
    · have hz : inZone g0 1 2 s := ⟨by rw [g01]; linarith, by rw [g01]; linarith⟩
      exact ⟨1, distInt_lt_of_zone hz⟩
    rcases le_or_gt s (23/2) with h | h
    · have hz : inZone g0 2 2 s := ⟨by rw [g02]; linarith, by rw [g02]; linarith⟩
      exact ⟨2, distInt_lt_of_zone hz⟩
    rcases le_or_gt s (25/2) with h | h
    · have hz : inZone g0 3 2 s := ⟨by rw [g03]; linarith, by rw [g03]; linarith⟩
      exact ⟨3, distInt_lt_of_zone hz⟩
    rcases le_or_gt s (27/2) with h | h
    · have hz : inZone g0 4 2 s := ⟨by rw [g04]; linarith, by rw [g04]; linarith⟩
      exact ⟨4, distInt_lt_of_zone hz⟩
    rcases le_or_gt s (29/2) with h | h
    · have hz : inZone g0 5 2 s := ⟨by rw [g05]; linarith, by rw [g05]; linarith⟩
      exact ⟨5, distInt_lt_of_zone hz⟩
    have hz : inZone g0 6 2 s := ⟨by rw [g06]; linarith, by rw [g06]; linarith⟩
    exact ⟨6, distInt_lt_of_zone hz⟩
  obtain ⟨i, hi⟩ := key
  exact absurd hi (not_lt.mpr (hall i))

#print axioms g0_noClearPoint

/-! ## 4. `g0` realizes no word -/

/-- The unique in-window zone of `g0` covering `R = 9` is reading `0` at level `2`. -/
theorem g0_cover9 {i : Fin 7} {j : ℕ} (h : inZone g0 i j 9) : i = 0 ∧ j = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hb := g0_bounds i
  have hj3 : (j : ℝ) < 3 := by linarith
  have hj1 : (1 : ℝ) < (j : ℝ) := by linarith
  have jlt : j < 3 := by exact_mod_cast hj3
  have jgt : 1 < j := by exact_mod_cast hj1
  have hj2 : j = 2 := by omega
  subst hj2
  refine ⟨?_, rfl⟩
  fin_cases i
  · rfl
  all_goals norm_num [g0] at h1

#print axioms g0_cover9

/-- The only in-window zones of `g0` covering `R = 15` are reading `6` at level `2` and
reading `1` at level `3`. -/
theorem g0_cover15 {i : Fin 7} {j : ℕ} (h : inZone g0 i j 15) :
    (i = 6 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by
  obtain ⟨h1, h2⟩ := h
  have hb := g0_bounds i
  have hj4 : (j : ℝ) < 4 := by linarith
  have hj1 : (1 : ℝ) < (j : ℝ) := by linarith
  have jlt : j < 4 := by exact_mod_cast hj4
  have jgt : 1 < j := by exact_mod_cast hj1
  rcases (by omega : j = 3 ∨ j = 2) with rfl | rfl
  · refine Or.inr ⟨?_, rfl⟩
    fin_cases i
    · norm_num [g0] at h2
    · rfl
    all_goals norm_num [g0] at h1
  · refine Or.inl ⟨?_, rfl⟩
    fin_cases i
    all_goals norm_num [g0] at h2
    · rfl

#print axioms g0_cover15

/-- **The sink argument**: no level-`≥ 3` zone of `g0` overlaps the `(0,2)`-zone inside
`[9,15]`, because an overlap point `R` would satisfy `(7/4)·R < 17`, so `8·z.2 − 1 <
(7/4)·(68/7) = 17`, forcing `z.2 ≤ 2`. -/
private theorem g0_sink {z : Fin 7 × ℕ} {R : ℝ} (hz2 : 2 < z.2) (hR9 : (9 : ℝ) ≤ R)
    (hu : g0 0 * R < (2 : ℝ) * 8 + 1) (hlo : (z.2 : ℝ) * 8 - 1 < g0 z.1 * R) : False := by
  have g00 : g0 0 = 7/4 := rfl
  rw [g00] at hu
  have hRup : R < 68/7 := by linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hbound : g0 z.1 * R ≤ 7/4 * R := mul_le_mul_of_nonneg_right (g0_le z.1) hR0
  have hlt : (z.2 : ℝ) * 8 - 1 < 17 := by linarith
  have h3 : (z.2 : ℝ) < 3 := by linarith
  have hlt3 : z.2 < 3 := by exact_mod_cast h3
  omega

/-- **`g0` realizes no `W₁` word.** -/
theorem g0_noWord : ∀ w : List (Fin 7 × ℕ), ¬ WordRealized g0 w := by
  intro w hw
  obtain ⟨hpos, hcov, hlink⟩ := hw
  obtain ⟨p, hp, hpz⟩ := hcov 9 (by norm_num) (by norm_num)
  obtain ⟨hp1, hp2⟩ := g0_cover9 hpz
  obtain ⟨q, hq, hqz⟩ := hcov 15 (by norm_num) (by norm_num)
  rcases g0_cover15 hqz with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · -- q = (6, 2): equal levels
    exfalso
    have hne : p ≠ q := by
      rintro rfl; rw [hp1] at hq1; simp at hq1
    rcases mem_before_or_after hp hq hne with ⟨l₁, l₂, l₃, heq⟩ | ⟨l₁, l₂, l₃, heq⟩
    · exact absurd (adj_before_lt w l₁ p q l₂ l₃ (fun p q hpq => (hlink p q hpq).1) heq) (by rw [hp2, hq2]; simp)
    · exact absurd (adj_before_lt w l₁ q p l₂ l₃ (fun p q hpq => (hlink p q hpq).1) heq) (by rw [hp2, hq2]; simp)
  · -- q = (1, 3): the (0,2) zone is a sink
    exfalso
    have hne : p ≠ q := by
      rintro rfl; rw [hp1] at hq1; simp at hq1
    rcases mem_before_or_after hp hq hne with ⟨l₁, l₂, l₃, heq⟩ | ⟨l₁, l₂, l₃, heq⟩
    · -- p before q: p has an immediate successor z
      cases l₂ with
      | nil =>
        obtain ⟨hlt, R, hR1, hR2, hzp, hzq⟩ := hlink p q ⟨l₁, l₃, by simp [heq]⟩
        rw [hp1, hp2] at hzp
        rw [hp2] at hlt
        exact g0_sink hlt hR1 hzp.2 hzq.1
      | cons b l₂' =>
        obtain ⟨hlt, R, hR1, hR2, hzp, hzb⟩ :=
          hlink p b ⟨l₁, l₂' ++ q :: l₃, by rw [heq]; simp [List.cons_append]⟩
        rw [hp1, hp2] at hzp
        rw [hp2] at hlt
        exact g0_sink hlt hR1 hzp.2 hzb.1
    · -- q before p: 3 < 2
      exact absurd (adj_before_lt w l₁ q p l₂ l₃ (fun p q hpq => (hlink p q hpq).1) heq) (by rw [hp2, hq2]; simp)

#print axioms g0_noWord

/-! ## 5. The falsifications -/

/-- **The domain-carried restatement** of the OWED (the shape the external review's repair
proposed).  Refuted as a `∀ g` statement below: `g0` satisfies the domain, has no clear point,
and realizes no word. -/
-- STANDING: OWED (refuted as a universal statement; see `domShape_refuted`)
def NoClearPointWordRealizedDom (g : Fin 7 → ℝ) : Prop :=
  (∀ i, (1 : ℝ) ≤ g i) → NoClearPointWordRealized g

theorem domShape_refuted : ¬ (∀ g : Fin 7 → ℝ, NoClearPointWordRealizedDom g) := by
  intro h
  obtain ⟨w, hw⟩ := h g0 g0_dom g0_noClearPoint
  exact g0_noWord w hw

#print axioms domShape_refuted

/-- **The domain-carried repair is refuted**: `g0` satisfies the normalization domain, has no
clear point, and realizes no word.  So the OWED `NoClearPointWordRealized` cannot be repaired by
carrying `∀ i, 1 ≤ g i` alone. -/
theorem domainCarried_refuted :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, (1 : ℝ) ≤ g i) → NoClearPointWordRealized g) := by
  intro h
  obtain ⟨w, hw⟩ := h g0 g0_dom g0_noClearPoint
  exact g0_noWord w hw

#print axioms domainCarried_refuted

/-- The box of the falsification: `g0` lives in the face box of `b0 = (2,2,1,1,1,1,1)`. -/
def b0 : Fin 7 → ℤ := ![2, 2, 1, 1, 1, 1, 1]

theorem g0_in_b0_face : ∀ i, FaceLo b0 i ≤ g0 i ∧ g0 i ≤ FaceHi b0 i := by
  intro i
  fin_cases i <;> simp [FaceLo, FaceHi, g0, b0] <;> norm_num

#print axioms g0_in_b0_face

/-- **Box membership for an arbitrary `b` does not repair either**: the same witness lies in the
face box of `b0 = (2,2,1,1,1,1,1)`.  The word-cover direction is genuinely per-box census data
(the boxes of `coveredSet`, not arbitrary half-unit boxes). -/
theorem boxCarried_arbitrary_refuted :
    ¬ (∀ (b : Fin 7 → ℤ) (g : Fin 7 → ℝ),
        (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) → NoClearPointWordRealized g) := by
  intro h
  obtain ⟨w, hw⟩ := h b0 g0 g0_in_b0_face g0_noClearPoint
  exact g0_noWord w hw

#print axioms boxCarried_arbitrary_refuted

/-! ## 5bis. Monotone orderings do not repair: the increasing permutation of the witness -/

/-- The index reversal on `Fin 7`. -/
private def rev (i : Fin 7) : Fin 7 := ⟨6 - i.val, by have := i.isLt; omega⟩

theorem rev_rev (i : Fin 7) : rev (rev i) = i := by
  have hi := i.isLt
  exact Fin.ext (by simp only [rev]; omega)

/-- The strictly increasing permutation of `g0` (its reversal): readings
`(16/15, 8/7, 16/13, 4/3, 16/11, 8/5, 7/4)`.  Both the clear-point condition and `WordRealized`
depend only on the multiset of readings, so the falsification transports along `rev`. -/
noncomputable def g0m : Fin 7 → ℝ := fun i => g0 (rev i)

theorem g0m_rev (i : Fin 7) : g0m (rev i) = g0 i := by simp [g0m, rev_rev]

theorem g0m_dom (i : Fin 7) : (1 : ℝ) ≤ g0m i := g0_dom (rev i)

theorem g0_antitone (k l : Fin 7) (h : k < l) : g0 l < g0 k := by
  fin_cases k <;> fin_cases l <;> norm_num [g0] at *

theorem g0m_strictMono : StrictMono g0m := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv : i.val < j.val := h
  have hrev : rev j < rev i := by
    show 6 - j.val < 6 - i.val
    omega
  exact g0_antitone (rev j) (rev i) hrev

#print axioms g0m_strictMono

theorem g0m_noClearPoint :
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g0m i * (s / 8))) := by
  rintro ⟨s, h1, h2, hall⟩
  refine g0_noClearPoint ⟨s, h1, h2, ?_⟩
  intro i
  have h := hall (rev i)
  rw [g0m_rev i] at h
  exact h

#print axioms g0m_noClearPoint

/-- Adjacency inverts along an involutive relabelling of the word. -/
private theorem hasadj_map_inv {f : Fin 7 × ℕ → Fin 7 × ℕ} (hf : ∀ x, f (f x) = x)
    {w : List (Fin 7 × ℕ)} {a b : Fin 7 × ℕ} (h : HasAdj (w.map f) a b) : HasAdj w (f a) (f b) := by
  obtain ⟨l₁, l₂, he⟩ := h
  refine ⟨l₁.map f, l₂.map f, ?_⟩
  have h1 : (w.map f).map f = (l₁ ++ a :: b :: l₂).map f := by rw [he]
  rw [List.map_map] at h1
  have hid : (f ∘ f) = id := by
    funext x
    exact hf x
  rw [hid, List.map_id] at h1
  simpa only [List.map_append, List.map_cons] using h1

theorem g0m_noWord : ∀ w : List (Fin 7 × ℕ), ¬ WordRealized g0m w := by
  intro w hw
  obtain ⟨hpos, hcov, hlink⟩ := hw
  have hf : ∀ x : Fin 7 × ℕ, (rev (rev x.1), x.2) = x := by
    intro x; rw [Prod.mk.injEq]; exact ⟨rev_rev x.1, rfl⟩
  refine g0_noWord (w.map (fun p => (rev p.1, p.2))) ?_
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hpos q hq
  · intro R hR1 hR2
    obtain ⟨p, hp, hpz⟩ := hcov R hR1 hR2
    exact ⟨_, List.mem_map_of_mem hp, hpz⟩
  · intro p q hpq
    obtain ⟨hlt, R, hR1', hR2', hz1, hz2⟩ :=
      hlink _ _ (hasadj_map_inv hf hpq)
    change inZone g0m (rev p.1) p.2 R at hz1
    change inZone g0m (rev q.1) q.2 R at hz2
    exact ⟨hlt, R, hR1', hR2', by simpa only [inZone, g0m_rev] using hz1,
      by simpa only [inZone, g0m_rev] using hz2⟩

#print axioms g0m_noWord

/-- **Strict monotonicity does not repair either**: the strictly increasing arrangement `g0m`
(the same readings, ordered) has no clear point and realizes no word.  Since both sides of the
implication are invariant under relabelling, no ordering hypothesis on the indexing can repair
the word-extraction direction. -/
theorem monotoneCarried_refuted :
    ¬ (∀ g : Fin 7 → ℝ, StrictMono g → (∀ i, (1 : ℝ) ≤ g i) → NoClearPointWordRealized g) := by
  intro h
  obtain ⟨w, hw⟩ := h g0m g0m_strictMono g0m_dom g0m_noClearPoint
  exact g0m_noWord w hw

#print axioms monotoneCarried_refuted

/-! ## 6. The provable region (vacuity) -/

/-- **The vacuity threshold**: with readings in `[1, 5/3]`, the point `s = 9` is always clear
(`9ρ/8 ∈ [9/8, 15/8]`, the middle of the unit window).  This bound is sharp: the exact sweep of
the session log finds counterexamples with all readings in `(1, 27/16]`, `27/16 > 5/3`. -/
theorem clearPoint_of_le_five_thirds (g : Fin 7 → ℝ) (h1 : ∀ i, (1 : ℝ) ≤ g i)
    (h2 : ∀ i, g i ≤ 5/3) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  refine ⟨9, by norm_num, by norm_num, ?_⟩
  intro i
  have hx1 : ((1 : ℤ) : ℝ) + 1/8 ≤ g i * (9/8) := by
    have h := mul_le_mul_of_nonneg_right (h1 i) (by norm_num : (0 : ℝ) ≤ 9/8)
    push_cast
    linarith
  have hx2 : g i * (9/8) ≤ ((1 : ℤ) : ℝ) + 7/8 := by
    have h := mul_le_mul_of_nonneg_right (h2 i) (by norm_num : (0 : ℝ) ≤ 9/8)
    push_cast
    linarith
  exact clear_of_window 1 hx1 hx2

#print axioms clearPoint_of_le_five_thirds

/-- In the provable region `[1, 5/3]` the OWED holds vacuously (its hypothesis never fires). -/
theorem wordExtract_of_low (g : Fin 7 → ℝ) (h1 : ∀ i, (1 : ℝ) ≤ g i) (h2 : ∀ i, g i ≤ 5/3) :
    NoClearPointWordRealized g := by
  intro hnoc
  exact absurd (clearPoint_of_le_five_thirds g h1 h2) hnoc

#print axioms wordExtract_of_low

/-! ## 7. The repaired consumer shape (box-carried) -/

/-- **The box-carried word-cover direction** — the OWED restated with the face box carried in
(the weakest uniform form the falsifications of §5 leave viable; consumers supply it per covered
box, as census data). -/
-- STANDING: OWED
def NoClearPointWordRealizedBox (b : Fin 7 → ℤ) (g : Fin 7 → ℝ) : Prop :=
  (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) → NoClearPointWordRealized g

/-- For low boxes (`FaceLo ≥ 1`, `FaceHi ≤ 5/3` — e.g. the all-`1` box, where `FaceHi = 3/2`)
the box-carried word-cover direction is **discharged** by the vacuity lemma. -/
theorem wordCoverBox_of_low (b : Fin 7 → ℤ) (hlo : ∀ i, (1 : ℝ) ≤ FaceLo b i)
    (hhi : ∀ i, FaceHi b i ≤ 5/3) (g : Fin 7 → ℝ) : NoClearPointWordRealizedBox b g := by
  intro hface hnoc
  exact absurd (clearPoint_of_le_five_thirds g (fun i => (hlo i).trans (hface i).1)
    (fun i => (hface i).2.trans (hhi i))) hnoc

#print axioms wordCoverBox_of_low

/-- **The repaired glue (direction (b))**: exactly `Fresh.WordCoverSide.composedTotal_of_wordCover`
with the word-cover OWED weakened to the box-carried form `NoClearPointWordRealizedBox` — the
shape the falsifications of §5 show is necessary. -/
theorem composedTotal_of_wordCover_box (b : Fin 7 → ℤ) (_hb : b ∈ coveredSet)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealizedBox b g)
    (hexh : FamilyCoversWordEdges b (compFamOf b)) :
    ComposedTotalOneSided b (compFamOf b) := by
  intro g hface hchains hcarve hnoc
  obtain ⟨w, hw⟩ := hword g hface hnoc
  obtain ⟨e, he, hxpos, hypos, hdem, _⟩ :=
    wordCover_realizes hchains hw (hexh g w hface hw)
  exact ⟨e, he, hxpos, hypos, hdem⟩

#print axioms composedTotal_of_wordCover_box

/-- **The OneSided conclusion through the box-carried word-cover side** (mirror of
`Fresh.WordCoverSide.oneSidedSound_of_wordCover`). -/
theorem oneSidedSound_of_wordCover_box (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealizedBox b g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb (composedTotal_of_wordCover_box b hb hword hexh)
    g hface hchains hcarve

#print axioms oneSidedSound_of_wordCover_box

end Fresh.WordExtract
