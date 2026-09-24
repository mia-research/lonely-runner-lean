import LonelyRunner.LRC.Spec.FlankFiniteN

/-!
# Incommensurable disparities at general `n` — the case the whole-number criteria do not reach

2026-09-21.  Everything in `FlankFiniteN`, `ResonanceN`, `WindowN`, `SelfSimilarN` and
`OtherFlankN` is stated for a **whole-number** difference set, and by `lonely_flank_smul_iff`
that covers every difference set all of whose ratios are rational.  A handover of 2026-09-21
recorded the remainder as *"irrational ratios are untouched"*.  That was wrong twice over.

**First**, the framework is real-valued throughout and already carries the general machinery:
`Flanks.class_killer_int` treats rational and irrational ratios in one case with no rationality
input, `Flanks.off_lattice_of_irrational_ratio` names the irrational case explicitly, and
`Flanks.lonely_opening_of_free_off_lattice` converts an off-lattice ratio into a lonely opening.
What was missing was not machinery but the **connection** from the whole-number criteria to it.
This file is that connection.

**Second**, an irrational ratio is not an obstacle here, it is a *help*: a disparity off every
lattice can never shadow a whole residue class of openings (`class_killer_int`), so it cannot be
the runner that defeats a flank.  The hard sets are the commensurable ones.

## What is proved

`lonely_of_one_free` — at any order `n ≥ 4`, if **one** disparity sits off the `P`-lattice of
every other and the rest are on a common `P`-lattice and number at most three, the subject is
lonely.  No rationality hypothesis anywhere; `n` is general.

`lonely_five_of_one_irrational` — the order-five reading: a subject with at most four disparities,
one of them incommensurable with all the others, is lonely.  Since a five-runner subject has at
most four disparities, this settles every order-five subject whose four disparities fall into
commensurability classes of shape `3+1`, leaving the shapes `4`, `2+2`, `2+1+1` and `1+1+1+1`.
(Shapes with fewer than four disparities need nothing from this file:
`exists_lonely_of_card_le_three` already settles them, unconditionally.)

`4` is the whole-number case, which is where the criteria live.  The other three are **not**
proved here and are not claimed; see the findings block at the foot of the file.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.IrrationalN

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## 1. a rational ratio is on a lattice; an irrational one is on none -/

/-- **A rational ratio sits on the lattice of its denominator.**  The pointwise building block
for the `P` in everything below. -/
theorem lattice_of_rat_ratio {d f : ℝ} {q : ℚ} (hf : f ≠ 0) (hd : d = (q : ℝ) * f) :
    Int.fract ((q.den : ℝ) * (d / f)) = 0 := by
  have hden : ((q.den : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < q.den := q.pos
    positivity
  refine on_lattice_of_ratio_den (a := q.num) (c := q.den) q.pos ?_
  rw [hd, mul_div_assoc, div_self hf, mul_one, Rat.cast_def]

/-- **An irrational ratio sits on no lattice at all** — restated at the multiple flanks this file
needs it at.  Content: `Flanks.off_lattice_of_irrational_ratio`. -/
theorem off_every_lattice_of_irrational {ds : Finset ℝ} {x : ℝ}
    (hirr : ∀ f ∈ ds, Irrational (x / f)) {P : ℕ} (hP : 0 < P) :
    ∀ f ∈ ds, Int.fract ((P : ℝ) * (x / f)) ≠ 0 :=
  fun f hf => off_lattice_of_irrational_ratio (hirr f hf) hP

/-! ## 2. one free disparity is enough, at every order `n ≥ 4`

The argument is three existing theorems in a row and no new analysis.

1. Delete the free disparity.  What is left has at most three members, so
   `exists_lonely_of_card_le_three` gives it a lonely instant — over the reals, at general `n`,
   with no rationality input.
2. `lonely_iff_exists_flank` turns that instant into a **flank** `f` of the remaining set and an
   opening index `r` at which all of them are clear.
3. The deleted disparity is off the `P`-lattice of `f`, so `lonely_opening_of_free_off_lattice`
   finds an opening in the class `r + jP` at which it is clear too.  The others are unchanged
   there, because a lattice ratio is periodic in the index mod `P`.

Step 3 is where the incommensurability is *used*, not worked around: it is the hypothesis that
makes the free disparity harmless. -/

/-- **One disparity off the lattice of the rest is enough**, at every order `n ≥ 4`.

`P` is any common lattice for the other disparities, at every flank among them; `x` is off that
lattice at every such flank.  Nothing here is whole-number and nothing is rational. -/
theorem lonely_of_one_free (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {x : ℝ} (hxds : x ∈ ds) (hcard : (ds.erase x).card ≤ 3) (P : ℕ)
    (hlat : ∀ f ∈ ds.erase x, ∀ d ∈ ds.erase x, Int.fract ((P : ℝ) * (d / f)) = 0)
    (hoff : ∀ f ∈ ds.erase x, Int.fract ((P : ℝ) * (x / f)) ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s := by
  classical
  have hpos' : ∀ d ∈ ds.erase x, 0 < d := fun d hd => hpos d (Finset.mem_of_mem_erase hd)
  rcases Finset.eq_empty_or_nonempty (ds.erase x) with hemp | hne
  · -- nothing but `x`: the whole set has at most one member
    have hc : ds.card ≤ 3 := by
      have h1 : (ds.erase x).card = ds.card - 1 := Finset.card_erase_of_mem hxds
      have h2 : 1 ≤ ds.card := Finset.card_pos.mpr ⟨x, hxds⟩
      rw [hemp] at h1; simp only [Finset.card_empty] at h1; omega
    exact exists_lonely_of_card_le_three (n := n) hn4 hpos hc
  · obtain ⟨s, hs, hl⟩ := exists_lonely_of_card_le_three (n := n) hn4 hpos' hcard
    obtain ⟨f, hf, r, hr⟩ := (lonely_iff_exists_flank (n := n) hpos' hne).mp ⟨s, hs, hl⟩
    have hf0 : 0 < f := hpos' f hf
    obtain ⟨k, hk⟩ :=
      lonely_opening_of_free_off_lattice (n := n) (ds := ds) (e := f) (x := x) hn4 hf0 P r
        (fun d hd hdx => hlat f hf d (Finset.mem_erase.mpr ⟨hdx, hd⟩))
        (fun d hd hdx => hr d (Finset.mem_erase.mpr ⟨hdx, hd⟩))
        (hoff f hf)
    exact ⟨flankOpening n f k, flankOpening_pos hf0 k, hk⟩

/-- **The irrational reading of the same theorem.**  `Irrational (x / f)` at every remaining
flank `f` gives the off-lattice hypothesis for free, at every `P`. -/
theorem lonely_of_one_irrational (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {x : ℝ} (hxds : x ∈ ds) (hcard : (ds.erase x).card ≤ 3) (P : ℕ) (hP : 0 < P)
    (hlat : ∀ f ∈ ds.erase x, ∀ d ∈ ds.erase x, Int.fract ((P : ℝ) * (d / f)) = 0)
    (hirr : ∀ f ∈ ds.erase x, Irrational (x / f)) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s :=
  lonely_of_one_free hn4 hpos hxds hcard P hlat
    (off_every_lattice_of_irrational (ds := ds.erase x) hirr hP)

/-! ## 3. order five -/


/-- **Order five, one incommensurable disparity.**  A subject with at most four disparities, one
of which is off the common lattice of the others, is lonely.

A five-runner subject has at most four disparities (`LRC.SpecN.diffSet_card_le`), so this settles
every order-five subject whose four disparities fall into commensurability classes of shape
`3+1`, with the singleton as `x`: a common lattice `P` for the three-class exists because every
ratio inside it is rational, and `x` is off that lattice at each of them because every ratio to
`x` is not. -/
theorem lonely_five_of_one_free {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 4) {x : ℝ} (hxds : x ∈ ds) (P : ℕ)
    (hlat : ∀ f ∈ ds.erase x, ∀ d ∈ ds.erase x, Int.fract ((P : ℝ) * (d / f)) = 0)
    (hoff : ∀ f ∈ ds.erase x, Int.fract ((P : ℝ) * (x / f)) ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s := by
  have h3 : (ds.erase x).card ≤ 3 := by
    have h1 : (ds.erase x).card = ds.card - 1 := Finset.card_erase_of_mem hxds
    have h2 : 1 ≤ ds.card := Finset.card_pos.mpr ⟨x, hxds⟩
    omega
  exact lonely_of_one_free (n := 5) (by norm_num) hpos hxds h3 P hlat hoff

/-- **The same, named for irrationality.** -/
theorem lonely_five_of_one_irrational {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 4) {x : ℝ} (hxds : x ∈ ds) (P : ℕ) (hP : 0 < P)
    (hlat : ∀ f ∈ ds.erase x, ∀ d ∈ ds.erase x, Int.fract ((P : ℝ) * (d / f)) = 0)
    (hirr : ∀ f ∈ ds.erase x, Irrational (x / f)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s :=
  lonely_five_of_one_free hpos hcard hxds P hlat
    (off_every_lattice_of_irrational (ds := ds.erase x) hirr hP)

/-! ## 4. a worked instance, so the theorem is not vacuous

`ds = {1, 2, 3, √2}` at order five.  The three whole numbers share the lattice `P = 6` at each of
the flanks `1, 2, 3` — `6·(d/f) ∈ ℤ` for every pair — and `√2 / f` is irrational at each.  So the
subject is lonely, and **no whole-number criterion in this development can see this set at all**:
it is not a scalar multiple of any set of integers. -/

theorem irrational_instance_1_2_3_sqrt2 :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ({1, 2, 3, Real.sqrt 2} : Finset ℝ) s := by
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hne : Real.sqrt 2 ∉ ({1, 2, 3} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hsq <;> norm_num at hsq
  have hins : ({1, 2, 3, Real.sqrt 2} : Finset ℝ) = insert (Real.sqrt 2) {1, 2, 3} := by
    ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have herase : ({1, 2, 3, Real.sqrt 2} : Finset ℝ).erase (Real.sqrt 2) = {1, 2, 3} := by
    rw [hins]; exact Finset.erase_insert hne
  have hpos : ∀ d ∈ ({1, 2, 3, Real.sqrt 2} : Finset ℝ), 0 < d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> [norm_num; norm_num; norm_num; exact hs0]
  have hcard : ({1, 2, 3, Real.sqrt 2} : Finset ℝ).card ≤ 4 := by
    have a1 := Finset.card_insert_le (1 : ℝ) {2, 3, Real.sqrt 2}
    have a2 := Finset.card_insert_le (2 : ℝ) {3, Real.sqrt 2}
    have a3 := Finset.card_insert_le (3 : ℝ) ({Real.sqrt 2} : Finset ℝ)
    simp only [Finset.card_singleton] at a1 a2 a3 ⊢
    omega
  refine lonely_five_of_one_irrational (x := Real.sqrt 2) hpos hcard (by simp) 6 (by norm_num)
    ?_ ?_
  · -- the three whole ratios all sit on the 6-lattice
    intro f hf d hd
    rw [herase] at hf hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf hd
    have hz : ∀ (m : ℤ) (y : ℝ), y = (m : ℝ) → Int.fract y = 0 := by
      intro m y h; rw [h]; exact Int.fract_intCast m
    rcases hf with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
      [ exact hz 6 _ (by norm_num); exact hz 12 _ (by norm_num); exact hz 18 _ (by norm_num);
        exact hz 3 _ (by norm_num); exact hz 6 _ (by norm_num);  exact hz 9 _ (by norm_num);
        exact hz 2 _ (by norm_num); exact hz 4 _ (by norm_num);  exact hz 6 _ (by norm_num)]
  · -- and `√2 / f` is irrational at each of them
    intro f hf
    rw [herase] at hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · simpa using h2
    · have := Irrational.div_intCast h2 (m := 2) (by norm_num)
      simpa using this
    · have := Irrational.div_intCast h2 (m := 3) (by norm_num)
      simpa using this

/-! ## findings — what this file does NOT prove

A five-runner subject has at most four disparities.  Partition them into commensurability
classes (`d ~ d'` when `d/d' ∈ ℚ`).  The possible shapes, and their standing:

| shape | standing |
|---|---|
| `4` — all commensurable | the whole-number case.  `lonely_flank_smul_iff` reduces it to a set of integers, where the criteria of `FlankFiniteN`/`ResonanceN`/`WindowN`/`SelfSimilarN`/`OtherFlankN` live.  **Not closed**: a residue of integer sets survives every criterion |
| `3+1` | **proved here** — `lonely_five_of_one_free`, with the singleton as `x` |
| `2+2`, `2+1+1`, `1+1+1+1` | **open.**  Not proved, not claimed |

Why the last row resists the same argument: `lonely_opening_of_free_off_lattice` needs *all but
one* disparity on a common lattice of the chosen flank.  Deleting one member of a four-set leaves
three, and in those shapes no choice of flank among the three puts the other two on a lattice with
it.  Closing them needs one of

* a **two-ratio** version of `Flanks.exists_clear_step` — for `n ≥ 5` and ratios `f₁, f₂` with
  `1, f₁, f₂` rationally independent, an index `j` at which `j·f₁ + c₁` and `j·f₂ + c₂` are both
  at least `1/n` from `ℤ`.  This is a genuine strengthening and is not in the tree; or
* an equidistribution or three-distance argument, which **firewall row six bans** (`MANUSCRIPT_v19`
  §6A, *no measure or density*).  Note that row six's stated justification — the clear set at the
  arithmetic progression is eight isolated points of measure zero — is a fact about a *rational*
  configuration and does not itself bite on incommensurable sets.  Whether the ban is meant to
  extend there is the author's call, not this file's.

**Direction of the phenomenon.**  Incommensurability is not what makes a set hard.  An off-lattice
disparity can never shadow a whole residue class (`Flanks.class_killer_int`), so it can never be
the runner that defeats a flank.  The sets that survive every criterion are the commensurable ones.
-/

end LRC.IrrationalN
