import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.FiveReach
import Fresh.Ladder
import Fresh.Ladder5
import Fresh.Gate

/-!
# `FourDistinctLaw` is false; its true part, and the reason for four (Task AZ)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is stationary); no floats.

## Result in one paragraph

`Ladder5.FourDistinctLaw` (four distinct intermediate setters at a first return of the slowest reading `a`, in the cascade
from `1/(8m)` with every reading `≥ m`) is **FALSE** (`not_fourDistinctLaw`): the four readings `{1, 26/25, 533/500, 204/125}`
with `m = 12/875` have a first return of `a = 1` through THREE values.  The reason is exact and symbolic.  A window with three
values is, by the budget law alone, the word `z x y z` or `z y x z` (`word_4 … word_7`, `three_distinct_shape`); this word is
excluded by integer lap arithmetic for the lap `j` of `a` at the move that sets it exactly when `j ≤ 8` or `j = 10`
(`lap_arith`, `three_distinct_lap`, `four_distinct_of_lap`).  For `j = 9` (the example) and for `j = 11 … 40`
(`experiments/n8/four_distinct_v1.out`, section 4, exact) three values occur.  So "four" is an OUTPUT of the laws at small `j`
(no cap, no move bound is used), not a law for every `j`.

## Contents and grades

* (1) Tools: `not_inWay_of_between`, `inWay_of_abs`, `isMove_of_single`, `isSetterAt_of` [L].
* (2) `not_fourDistinctLaw`, `slowest_of_four_can_return` [L]: the exact counterexample (`CE`, `ceSeq`, `ce_*`).
* (3) `word_4 … word_7` [L]: the budget system on three setter values is a linear system in `u = a / w`; exactly `z x y z` and
  `z y x z` survive among all words without an immediate repeat of length 4 to 7 (case tree of `linarith`).
* (4) `a_lt_w`, `pair_budget`, `min_once`, `window_has_min`, `four_of_min_recurs`, `exists_sorted_three`,
  `three_distinct_shape` [L]: a window with at most three values has exactly four moves and is `z y x z` / `z x y z`.
  `four_of_min_recurs`: if the smallest setter value of the window recurs, the window has at least four values.
* (5) `lap_arith`, `three_distinct_lap`, `four_distinct_of_lap`, `FourDistinctLawLap`/`fourDistinctLawLap`,
  `slowest_of_four_never_returns_lap`, `five_first_return_all_others_lap`, `lap_le_eight_of_lt`, `four_distinct_in_gate` [L]:
  the true part.  `four_distinct_in_gate`: readings `≤ 10 m`, `a` set inside the first window, then four distinct values.

## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED)

| hypothesis | status |
|---|---|
| `0 < m`, `m ≤ d`, `seq 0 = 1/(8m)` in `FourDistinctLaw` | NOT REQUIRED by the true theorems (`four_distinct_of_lap` uses only `0 < seq 0`); `FourDistinctLaw` with them is FALSE (`m ≪ a`) |
| `a` at most every reading | REQUIRED (AY's `x y x` return after one move has `a` not the minimum; `four_distinct_v1.out` section 5) |
| `a` is the SETTER at `n` | REQUIRED (`ladder5_v2.out` section 4 exact counterexample for 'in the way') |
| first return (`hfirst`) | used (`a_lt_w`); necessity UNDECIDED |
| lap `j` of `a` at its setting: `j ≤ 8 ∨ j = 10` | REQUIRED for the conclusion: `j = 9` is attained (`not_fourDistinctLaw`), `j = 11 … 40` exact examples (python) |
| `a ≤ 10 m` and `seq n ≤ 7/(8m)` in `four_distinct_in_gate` | `a ≤ 10 m` REQUIRED in that form (counterexample `a = 875/12 m`, inside the window); `seq n ≤ 7/(8m)` used |
| `m = a` (slowest reading is the unit) | UNDECIDED: no proof, no counterexample (search log in the python file) |
| positivity of the disparities | REQUIRED as stated (the proofs divide by them) |

Rule 7: the `Finset.card` steps in `min_once`, `window_has_min` and the bound `k ≤ n + 8` in `three_distinct_shape` are
`[PROVISIONAL: counting tool]` steps supporting the single claim "a window with three setter values has exactly four moves";
no move bound is offered as a result.

Provenance (existing declarations whose argument was read and understood, nothing copied): `Ladder5.budget_sum`,
`Ladder5.four_consecutive_distinct`, `Ladder5.return_after_four`, `Ladder5.return_three_distinct`, `ChainLaws.later_lap_of_ge`,
`ChainLaws.setter_recur_lap`, `Dilation.setter_reading`, `Dilation.abs_sub_lap_lt`.  The cycle inequality `lap_arith` (ratio
windows of consecutive links multiply to `1`) and the weights `u = a/w` are new here.
-/

open Classical

namespace Fresh

namespace FourDistinct

open Cascade Dilation ChainLaws Ladder5

/-! ## (1) Concrete verification tools -/

/-- A point strictly between `k + 1/8` and `k + 7/8` (closed) is not in the way. -/
theorem not_inWay_of_between {d t : ℝ} (k : ℤ) (h1 : (k : ℝ) + 1 / 8 ≤ d * t) (h2 : d * t ≤ (k : ℝ) + 7 / 8) :
    ¬ InWay d t := by
  intro h
  obtain ⟨k', hk'⟩ := exists_near_int h
  have hb := abs_lt.mp hk'
  rcases le_or_gt k' k with hle | hgt
  · have : (k' : ℝ) ≤ k := by exact_mod_cast hle
    linarith
  · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hgt
    linarith

#print axioms not_inWay_of_between

theorem inWay_of_abs {d t : ℝ} (k : ℤ) (hk : |d * t - k| < 1 / 8) : InWay d t :=
  lt_of_le_of_lt (distInt_le (d * t) k) hk

#print axioms inWay_of_abs

/-- A move with a single runner in the way. -/
theorem isMove_of_single {E : Finset ℝ} {t t' d : ℝ} (hd : d ∈ E) (k : ℤ)
    (hk : |d * t - k| < 1 / 8) (ht' : t' = ((k : ℝ) + 1 / 8) / d)
    (hother : ∀ e ∈ E, e ≠ d → ¬ InWay e t) : IsMove E t t' := by
  right
  refine ⟨d, hd, inWay_of_abs k hk, ?_, ?_⟩
  · rw [ht', nextOpening_eq hk]
  · intro e he hw
    by_cases hed : e = d
    · subst hed
      rw [ht', nextOpening_eq hk]
    · exact absurd hw (hother e he hed)

#print axioms isMove_of_single

theorem isSetterAt_of {E : Finset ℝ} {seq : ℕ → ℝ} {n : ℕ} {d : ℝ} (hd : d ∈ E) (k : ℤ)
    (hk : |d * seq n - k| < 1 / 8) (ht' : seq (n + 1) = ((k : ℝ) + 1 / 8) / d) : IsSetterAt E seq n d :=
  ⟨hd, inWay_of_abs k hk, by rw [ht', nextOpening_eq hk]⟩

#print axioms isSetterAt_of

/-! ## (2) An exact counterexample to `FourDistinctLaw` -/

noncomputable def CE : Finset ℝ := {1, 26 / 25, 533 / 500, 204 / 125}

noncomputable def ceSeq : ℕ → ℝ
  | 0 => 875 / 96
  | 1 => 73 / 8
  | 2 => 15125 / 1632
  | 3 => 10125 / 1066
  | 4 => 2025 / 208
  | 5 => 5375 / 544
  | _ => 81 / 8

theorem mem_CE {e : ℝ} : e ∈ CE ↔ e = 1 ∨ e = 26 / 25 ∨ e = 533 / 500 ∨ e = 204 / 125 := by
  simp [CE]

theorem ce_move0 : IsMove CE (ceSeq 0) (ceSeq 1) := by
  refine isMove_of_single (d := 1) (k := 9) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · exact absurd rfl hne
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 14 (by norm_num) (by norm_num)

#print axioms ce_move0


theorem ce_move1 : IsMove CE (ceSeq 1) (ceSeq 2) := by
  refine isMove_of_single (d := 204 / 125) (k := 15) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · exact absurd rfl hne

theorem ce_move2 : IsMove CE (ceSeq 2) (ceSeq 3) := by
  refine isMove_of_single (d := 533 / 500) (k := 10) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · exact absurd rfl hne
    · simp only [ceSeq]; exact not_inWay_of_between 15 (by norm_num) (by norm_num)

theorem ce_move3 : IsMove CE (ceSeq 3) (ceSeq 4) := by
  refine isMove_of_single (d := 26 / 25) (k := 10) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · exact absurd rfl hne
    · simp only [ceSeq]; exact not_inWay_of_between 10 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 15 (by norm_num) (by norm_num)

theorem ce_move4 : IsMove CE (ceSeq 4) (ceSeq 5) := by
  refine isMove_of_single (d := 204 / 125) (k := 16) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 10 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 10 (by norm_num) (by norm_num)
    · exact absurd rfl hne

theorem ce_move5 : IsMove CE (ceSeq 5) (ceSeq 6) := by
  refine isMove_of_single (d := 1) (k := 10) (by simp [CE]) ?_ ?_ ?_
  · simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  · simp only [ceSeq]; norm_num
  · intro e he hne
    rcases mem_CE.mp he with h | h | h | h <;> subst h
    · exact absurd rfl hne
    · simp only [ceSeq]; exact not_inWay_of_between 10 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 10 (by norm_num) (by norm_num)
    · simp only [ceSeq]; exact not_inWay_of_between 16 (by norm_num) (by norm_num)

theorem ce_fixed (n : ℕ) : IsMove CE (ceSeq (n + 6)) (ceSeq (n + 6 + 1)) := by
  left
  have e1 : ceSeq (n + 6) = 81 / 8 := rfl
  have e2 : ceSeq (n + 6 + 1) = 81 / 8 := rfl
  refine ⟨?_, by rw [e1, e2]⟩
  intro e he
  rw [e1]
  rcases mem_CE.mp he with h | h | h | h <;> subst h
  · exact not_inWay_of_between 10 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 10 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 10 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 16 (by norm_num) (by norm_num)

theorem ce_isMove : ∀ n, IsMove CE (ceSeq n) (ceSeq (n + 1)) := by
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | n
  · exact ce_move0
  · exact ce_move1
  · exact ce_move2
  · exact ce_move3
  · exact ce_move4
  · exact ce_move5
  · exact ce_fixed n

#print axioms ce_isMove


theorem ce_setter0 : IsSetterAt CE ceSeq 0 1 :=
  isSetterAt_of (by simp [CE]) 9 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)
    (by show ceSeq 1 = _; simp only [ceSeq]; norm_num)

theorem ce_setter1 : IsSetterAt CE ceSeq 1 (204 / 125) :=
  isSetterAt_of (by simp [CE]) 15 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)
    (by show ceSeq 2 = _; simp only [ceSeq]; norm_num)

theorem ce_setter2 : IsSetterAt CE ceSeq 2 (533 / 500) :=
  isSetterAt_of (by simp [CE]) 10 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)
    (by show ceSeq 3 = _; simp only [ceSeq]; norm_num)

theorem ce_setter3 : IsSetterAt CE ceSeq 3 (26 / 25) :=
  isSetterAt_of (by simp [CE]) 10 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)
    (by show ceSeq 4 = _; simp only [ceSeq]; norm_num)

theorem ce_setter4 : IsSetterAt CE ceSeq 4 (204 / 125) :=
  isSetterAt_of (by simp [CE]) 16 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)
    (by show ceSeq 5 = _; simp only [ceSeq]; norm_num)

theorem ce_inWay5 : InWay 1 (ceSeq 5) :=
  inWay_of_abs 10 (by simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num)

theorem ce_first : ∀ s, 0 < s → s < 5 → ¬ InWay 1 (ceSeq s) := by
  intro s h1 h2
  interval_cases s
  · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
  · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
  · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)
  · simp only [ceSeq]; exact not_inWay_of_between 9 (by norm_num) (by norm_num)

noncomputable def ceW : ℕ → ℝ := fun s => if s = 1 then 204 / 125 else if s = 2 then 533 / 500 else if s = 3 then 26 / 25 else 204 / 125

theorem ce_image : (Finset.Ico (0 + 1) 5).image ceW = {204 / 125, 533 / 500, 26 / 25} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    interval_cases s <;> simp [ceW]
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, ⟨by norm_num, by norm_num⟩, by simp [ceW]⟩
    · exact ⟨2, ⟨by norm_num, by norm_num⟩, by simp [ceW]⟩
    · exact ⟨3, ⟨by norm_num, by norm_num⟩, by simp [ceW]⟩

theorem ce_card : ((Finset.Ico (0 + 1) 5).image ceW).card = 3 := by
  rw [ce_image, Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
    Finset.card_singleton]

/-- **`FourDistinctLaw` is FALSE** [L].  The four readings `{1, 26/25, 533/500, 204/125}` with lower bound
`m = 12/875` (so `seq 0 = 1/(8m) = 875/96`): the slowest reading `1` sets the move at `n = 0` (lap 9), and is in the way
at `seq 5` with `1` not in the way at `seq 1 … seq 4`; the intermediate setters are `204/125, 533/500, 26/25, 204/125` --
THREE distinct values.  Every hypothesis of `FourDistinctLaw` holds; its conclusion `3 < card` does not. -/
theorem not_fourDistinctLaw : ¬ FourDistinctLaw := by
  intro h
  have key := h CE (12 / 875) ceSeq 1 0 5 (by norm_num)
    (by intro d hd; rcases mem_CE.mp hd with h | h | h | h <;> subst h <;> norm_num)
    (by show (875 : ℝ) / 96 = _; norm_num) ce_isMove
    (by intro d hd; rcases mem_CE.mp hd with h | h | h | h <;> subst h <;> norm_num)
    ce_setter0 (by norm_num) ce_inWay5 ce_first ceW (by
      intro s h1 h2
      interval_cases s
      · simpa [ceW] using ce_setter1
      · simpa [ceW] using ce_setter2
      · simpa [ceW] using ce_setter3
      · simpa [ceW] using ce_setter4)
  rw [ce_card] at key
  exact lt_irrefl _ key

#print axioms not_fourDistinctLaw

/-- Consequence [L]: the conclusion of `Ladder5.slowest_of_four_never_returns` is false for the four readings above,
so the hypothesis `FourDistinctLaw` of that theorem cannot be discharged. -/
theorem slowest_of_four_can_return :
    ∃ (E : Finset ℝ) (m : ℝ) (seq : ℕ → ℝ) (a : ℝ) (n k : ℕ), 0 < m ∧ (∀ d ∈ E, m ≤ d) ∧ seq 0 = 1 / (8 * m) ∧
      (∀ i, IsMove E (seq i) (seq (i + 1))) ∧ E.card ≤ 4 ∧ (∀ d ∈ E, a ≤ d) ∧ IsSetterAt E seq n a ∧ n < k ∧
      (∀ s, n < s → s < k → ¬ InWay a (seq s)) ∧ InWay a (seq k) := by
  refine ⟨CE, 12 / 875, ceSeq, 1, 0, 5, by norm_num, ?_, by show (875 : ℝ) / 96 = _; norm_num, ce_isMove, ?_, ?_,
    ce_setter0, by norm_num, ce_first, ce_inWay5⟩
  · intro d hd; rcases mem_CE.mp hd with h | h | h | h <;> subst h <;> norm_num
  · have : CE = {1, 26 / 25, 533 / 500, 204 / 125} := rfl
    rw [this]
    refine (Finset.card_le_four).trans le_rfl
  · intro d hd; rcases mem_CE.mp hd with h | h | h | h <;> subst h <;> norm_num

#print axioms slowest_of_four_can_return


/-! ## (3) Words of at most three letters: the budget system is an LP in `u = a/w` (all lengths up to seven)

Write `U s = a / w s` (the weight of the setter `w s` against the slowest reading `a`).  Every inequality of the budget
law is LINEAR in these weights: the return of `a` is `3 < ∑ U s`; the return of a repeated setter `v` (between two
visits, no other visit of `v`) is `3 · U v < ∑_{between} U s` (`x / w = U w / U x`).  For three letters
`u_z < u_y < u_x < 1` (`z` the fastest) the lemmas `word_4 … word_7` list ALL words without an immediate repeat
(adjacent setters differ: `setter_not_twice_in_row`) and show that exactly two, `z x y z` and `z y x z`, satisfy every
budget; the proof is a case tree of `linarith` (generated from the exact Fourier–Motzkin check of
`experiments/n8/four_distinct_v1.py`, which also lists the other lengths).  No hypothesis on the word beyond the budgets
is used: this is the whole content of the budget law for three letters. -/

theorem word_4 {U : ℕ → ℝ} {ux uy uz : ℝ} (hz : 0 < uz) (hzy : uz < uy) (hyx : uy < ux) (hx1 : ux < 1)
    (hS : ∀ s, 1 ≤ s → s ≤ 4 → U s = ux ∨ U s = uy ∨ U s = uz)
    (hne : ∀ s, 1 ≤ s → s < 4 → U s ≠ U (s + 1))
    (hbud : ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ 4 → U s1 = U s2 →
      3 * U s1 < ∑ s ∈ Finset.Ico (s1 + 1) s2, U s)
    (htot : 3 < ∑ s ∈ Finset.Ico 1 5, U s) : U 1 = uz ∧ U 4 = uz ∧ ((U 2 = ux ∧ U 3 = uy) ∨ (U 2 = uy ∧ U 3 = ux)) := by
  have t : 3 < U 1 + U 2 + U 3 + U 4 := by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using htot
  have b1_3 : U 1 = U 3 → 3 * U 1 < U 2 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 3 (by norm_num) (by norm_num) (by norm_num) h
  have b1_4 : U 1 = U 4 → 3 * U 1 < U 2 + U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 4 (by norm_num) (by norm_num) (by norm_num) h
  have b2_4 : U 2 = U 4 → 3 * U 2 < U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 4 (by norm_num) (by norm_num) (by norm_num) h
  have n1 : U 1 ≠ U 2 := hne 1 (by norm_num) (by norm_num)
  have n2 : U 2 ≠ U 3 := hne 2 (by norm_num) (by norm_num)
  have n3 : U 3 ≠ U 4 := hne 3 (by norm_num) (by norm_num)
  rcases hS 1 (by norm_num) (by norm_num) with e1 | e1 | e1
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_4 (e1.trans e4.symm)]
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_4 (e1.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
        · exfalso
          linarith [t, b1_4 (e1.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b1_4 (e1.trans e4.symm)]
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · exact ⟨e1, e4, Or.inl ⟨e2, e3⟩⟩
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · exfalso
          linarith [t, b2_4 (e2.trans e4.symm)]
        · exact ⟨e1, e4, Or.inr ⟨e2, e3⟩⟩
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm)]
        · exfalso
          linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1

theorem word_5 {U : ℕ → ℝ} {ux uy uz : ℝ} (hz : 0 < uz) (hzy : uz < uy) (hyx : uy < ux) (hx1 : ux < 1)
    (hS : ∀ s, 1 ≤ s → s ≤ 5 → U s = ux ∨ U s = uy ∨ U s = uz)
    (hne : ∀ s, 1 ≤ s → s < 5 → U s ≠ U (s + 1))
    (hbud : ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ 5 → U s1 = U s2 →
      3 * U s1 < ∑ s ∈ Finset.Ico (s1 + 1) s2, U s)
    (htot : 3 < ∑ s ∈ Finset.Ico 1 6, U s) : False := by
  have t : 3 < U 1 + U 2 + U 3 + U 4 + U 5 := by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using htot
  have b1_3 : U 1 = U 3 → 3 * U 1 < U 2 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 3 (by norm_num) (by norm_num) (by norm_num) h
  have b1_4 : U 1 = U 4 → 3 * U 1 < U 2 + U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 4 (by norm_num) (by norm_num) (by norm_num) h
  have b1_5 : U 1 = U 5 → 3 * U 1 < U 2 + U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 5 (by norm_num) (by norm_num) (by norm_num) h
  have b2_4 : U 2 = U 4 → 3 * U 2 < U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 4 (by norm_num) (by norm_num) (by norm_num) h
  have b2_5 : U 2 = U 5 → 3 * U 2 < U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 5 (by norm_num) (by norm_num) (by norm_num) h
  have b3_5 : U 3 = U 5 → 3 * U 3 < U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 5 (by norm_num) (by norm_num) (by norm_num) h
  have n1 : U 1 ≠ U 2 := hne 1 (by norm_num) (by norm_num)
  have n2 : U 2 ≠ U 3 := hne 2 (by norm_num) (by norm_num)
  have n3 : U 3 ≠ U 4 := hne 3 (by norm_num) (by norm_num)
  have n4 : U 4 ≠ U 5 := hne 4 (by norm_num) (by norm_num)
  rcases hS 1 (by norm_num) (by norm_num) with e1 | e1 | e1
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exfalso
            linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm)]
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm)]
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · exfalso
            linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1

theorem word_6 {U : ℕ → ℝ} {ux uy uz : ℝ} (hz : 0 < uz) (hzy : uz < uy) (hyx : uy < ux) (hx1 : ux < 1)
    (hS : ∀ s, 1 ≤ s → s ≤ 6 → U s = ux ∨ U s = uy ∨ U s = uz)
    (hne : ∀ s, 1 ≤ s → s < 6 → U s ≠ U (s + 1))
    (hbud : ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ 6 → U s1 = U s2 →
      3 * U s1 < ∑ s ∈ Finset.Ico (s1 + 1) s2, U s)
    (htot : 3 < ∑ s ∈ Finset.Ico 1 7, U s) : False := by
  have t : 3 < U 1 + U 2 + U 3 + U 4 + U 5 + U 6 := by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using htot
  have b1_3 : U 1 = U 3 → 3 * U 1 < U 2 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 3 (by norm_num) (by norm_num) (by norm_num) h
  have b1_4 : U 1 = U 4 → 3 * U 1 < U 2 + U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 4 (by norm_num) (by norm_num) (by norm_num) h
  have b1_5 : U 1 = U 5 → 3 * U 1 < U 2 + U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 5 (by norm_num) (by norm_num) (by norm_num) h
  have b1_6 : U 1 = U 6 → 3 * U 1 < U 2 + U 3 + U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 6 (by norm_num) (by norm_num) (by norm_num) h
  have b2_4 : U 2 = U 4 → 3 * U 2 < U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 4 (by norm_num) (by norm_num) (by norm_num) h
  have b2_5 : U 2 = U 5 → 3 * U 2 < U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 5 (by norm_num) (by norm_num) (by norm_num) h
  have b2_6 : U 2 = U 6 → 3 * U 2 < U 3 + U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 6 (by norm_num) (by norm_num) (by norm_num) h
  have b3_5 : U 3 = U 5 → 3 * U 3 < U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 5 (by norm_num) (by norm_num) (by norm_num) h
  have b3_6 : U 3 = U 6 → 3 * U 3 < U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 6 (by norm_num) (by norm_num) (by norm_num) h
  have b4_6 : U 4 = U 6 → 3 * U 4 < U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 4 6 (by norm_num) (by norm_num) (by norm_num) h
  have n1 : U 1 ≠ U 2 := hne 1 (by norm_num) (by norm_num)
  have n2 : U 2 ≠ U 3 := hne 2 (by norm_num) (by norm_num)
  have n3 : U 3 ≠ U 4 := hne 3 (by norm_num) (by norm_num)
  have n4 : U 4 ≠ U 5 := hne 4 (by norm_num) (by norm_num)
  have n5 : U 5 ≠ U 6 := hne 5 (by norm_num) (by norm_num)
  rcases hS 1 (by norm_num) (by norm_num) with e1 | e1 | e1
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
            · exfalso
              linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm)]
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm)]
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm)]
            · exfalso
              linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1

theorem word_7 {U : ℕ → ℝ} {ux uy uz : ℝ} (hz : 0 < uz) (hzy : uz < uy) (hyx : uy < ux) (hx1 : ux < 1)
    (hS : ∀ s, 1 ≤ s → s ≤ 7 → U s = ux ∨ U s = uy ∨ U s = uz)
    (hne : ∀ s, 1 ≤ s → s < 7 → U s ≠ U (s + 1))
    (hbud : ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ 7 → U s1 = U s2 →
      3 * U s1 < ∑ s ∈ Finset.Ico (s1 + 1) s2, U s)
    (htot : 3 < ∑ s ∈ Finset.Ico 1 8, U s) : False := by
  have t : 3 < U 1 + U 2 + U 3 + U 4 + U 5 + U 6 + U 7 := by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using htot
  have b1_3 : U 1 = U 3 → 3 * U 1 < U 2 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 3 (by norm_num) (by norm_num) (by norm_num) h
  have b1_4 : U 1 = U 4 → 3 * U 1 < U 2 + U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 4 (by norm_num) (by norm_num) (by norm_num) h
  have b1_5 : U 1 = U 5 → 3 * U 1 < U 2 + U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 5 (by norm_num) (by norm_num) (by norm_num) h
  have b1_6 : U 1 = U 6 → 3 * U 1 < U 2 + U 3 + U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 6 (by norm_num) (by norm_num) (by norm_num) h
  have b1_7 : U 1 = U 7 → 3 * U 1 < U 2 + U 3 + U 4 + U 5 + U 6 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 1 7 (by norm_num) (by norm_num) (by norm_num) h
  have b2_4 : U 2 = U 4 → 3 * U 2 < U 3 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 4 (by norm_num) (by norm_num) (by norm_num) h
  have b2_5 : U 2 = U 5 → 3 * U 2 < U 3 + U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 5 (by norm_num) (by norm_num) (by norm_num) h
  have b2_6 : U 2 = U 6 → 3 * U 2 < U 3 + U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 6 (by norm_num) (by norm_num) (by norm_num) h
  have b2_7 : U 2 = U 7 → 3 * U 2 < U 3 + U 4 + U 5 + U 6 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 2 7 (by norm_num) (by norm_num) (by norm_num) h
  have b3_5 : U 3 = U 5 → 3 * U 3 < U 4 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 5 (by norm_num) (by norm_num) (by norm_num) h
  have b3_6 : U 3 = U 6 → 3 * U 3 < U 4 + U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 6 (by norm_num) (by norm_num) (by norm_num) h
  have b3_7 : U 3 = U 7 → 3 * U 3 < U 4 + U 5 + U 6 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 3 7 (by norm_num) (by norm_num) (by norm_num) h
  have b4_6 : U 4 = U 6 → 3 * U 4 < U 5 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 4 6 (by norm_num) (by norm_num) (by norm_num) h
  have b4_7 : U 4 = U 7 → 3 * U 4 < U 5 + U 6 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 4 7 (by norm_num) (by norm_num) (by norm_num) h
  have b5_7 : U 5 = U 7 → 3 * U 5 < U 6 := fun h => by
    simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using hbud 5 7 (by norm_num) (by norm_num) (by norm_num) h
  have n1 : U 1 ≠ U 2 := hne 1 (by norm_num) (by norm_num)
  have n2 : U 2 ≠ U 3 := hne 2 (by norm_num) (by norm_num)
  have n3 : U 3 ≠ U 4 := hne 3 (by norm_num) (by norm_num)
  have n4 : U 4 ≠ U 5 := hne 4 (by norm_num) (by norm_num)
  have n5 : U 5 ≠ U 6 := hne 5 (by norm_num) (by norm_num)
  have n6 : U 6 ≠ U 7 := hne 6 (by norm_num) (by norm_num)
  rcases hS 1 (by norm_num) (by norm_num) with e1 | e1 | e1
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
  · rcases hS 2 (by norm_num) (by norm_num) with e2 | e2 | e2
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · rcases hS 3 (by norm_num) (by norm_num) with e3 | e3 | e3
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · exact absurd (e3.trans e4.symm) n3
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_4 (e1.trans e4.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
      · exact absurd (e2.trans e3.symm) n2
      · rcases hS 4 (by norm_num) (by norm_num) with e4 | e4 | e4
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_5 (e2.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_5 (e2.trans e5.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · rcases hS 5 (by norm_num) (by norm_num) with e5 | e5 | e5
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · exact absurd (e5.trans e6.symm) n5
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b3_6 (e3.trans e6.symm), b5_7 (e5.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_6 (e1.trans e6.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_6 (e3.trans e6.symm), b4_7 (e4.trans e7.symm)]
              · exact absurd (e6.trans e7.symm) n6
          · exact absurd (e4.trans e5.symm) n4
          · rcases hS 6 (by norm_num) (by norm_num) with e6 | e6 | e6
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_7 (e2.trans e7.symm), b3_5 (e3.trans e5.symm), b4_7 (e4.trans e7.symm)]
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b5_7 (e5.trans e7.symm)]
            · rcases hS 7 (by norm_num) (by norm_num) with e7 | e7 | e7
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b4_6 (e4.trans e6.symm)]
              · exact absurd (e6.trans e7.symm) n6
              · exfalso
                linarith [t, b1_3 (e1.trans e3.symm), b1_5 (e1.trans e5.symm), b1_7 (e1.trans e7.symm), b2_4 (e2.trans e4.symm), b2_6 (e2.trans e6.symm), b3_5 (e3.trans e5.symm), b3_7 (e3.trans e7.symm), b4_6 (e4.trans e6.symm), b5_7 (e5.trans e7.symm)]
            · exact absurd (e5.trans e6.symm) n5
        · exact absurd (e3.trans e4.symm) n3
    · exact absurd (e1.trans e2.symm) n1


/-! ## (4) The window of a first return of the slowest -/

section Window

variable {E : Finset ℝ} {seq : ℕ → ℝ}

/-- Inside the window of a first return, every setter is strictly faster than `a`. -/
theorem a_lt_w {a : ℝ} (ha : ∀ d ∈ E, a ≤ d) {n k : ℕ} (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s))
    {w : ℕ → ℝ} (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) {s : ℕ} (h1 : n < s) (h2 : s < k) :
    a < w s := by
  have hle : a ≤ w s := ha _ (hws s h1 h2).1
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply hfirst s h1 h2
    rw [h]
    exact (hws s h1 h2).2.1

#print axioms a_lt_w

/-- The budget law between two visits of one setter (value form). -/
theorem pair_budget (hpos : ∀ d ∈ E, 0 < d) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k s1 s2 : ℕ}
    {w : ℕ → ℝ} (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) (h1 : n < s1) (h12 : s1 < s2) (h2 : s2 < k)
    (heq : w s1 = w s2) : 3 < ∑ t ∈ Finset.Ico (s1 + 1) s2, w s1 / w t := by
  refine budget_sum hpos hmv h12 (hws s1 h1 (by omega)) ?_ w (fun s hs1 hs2 => hws s (by omega) (by omega))
  have := (hws s2 (by omega) h2).2.1
  rwa [← heq] at this

#print axioms pair_budget

/-- **The smallest setter value of a window with at most three values occurs once** [L].  Two visits of the minimum `x`
(consecutive ones, by `Nat.find`) have at least four moves between them (the budget: each term `x / w t ≤ 1`), none of
value `x`; four consecutive setters take at least three values (`four_consecutive_distinct`), but only the other two
values are left.  This is the symbolic reason for FOUR in the form: *if the slowest setter value of the window
recurs, the window has at least four distinct values*. -/
theorem min_once (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ}
    {w : ℕ → ℝ} (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) {S : Finset ℝ}
    (hSmem : ∀ t, n < t → t < k → w t ∈ S) (hS3 : S.card ≤ 3) {x : ℝ} (hxS : x ∈ S)
    (hmin : ∀ t, n < t → t < k → x ≤ w t) {s1 s2 : ℕ} (h1 : n < s1) (h12 : s1 < s2) (h2 : s2 < k)
    (e1 : w s1 = x) (e2 : w s2 = x) : False := by
  have hP : ∃ s, s1 < s ∧ s < k ∧ w s = x := ⟨s2, h12, h2, e2⟩
  have hmP := Nat.find_spec hP
  have hmin' : ∀ s, s < Nat.find hP → ¬ (s1 < s ∧ s < k ∧ w s = x) := fun s hs => Nat.find_min hP hs
  obtain ⟨hm1, hm2, hm3⟩ := hmP
  have hb := pair_budget hpos hmv hws h1 hm1 hm2 (by rw [e1, hm3])
  have hterm : ∀ t ∈ Finset.Ico (s1 + 1) (Nat.find hP), w s1 / w t ≤ 1 := by
    intro t ht
    have ht' := Finset.mem_Ico.mp ht
    have hpt : 0 < w t := hpos _ (hws t (by omega) (by omega)).1
    rw [e1, div_le_one hpt]
    exact hmin t (by omega) (by omega)
  have hle := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico] at hle
  simp only [nsmul_eq_mul, mul_one] at hle
  have h3 : (3 : ℝ) < ((Nat.find hP - (s1 + 1) : ℕ) : ℝ) := by linarith
  have h3' : 3 < Nat.find hP - (s1 + 1) := by exact_mod_cast h3
  -- [PROVISIONAL: counting tool] pigeonhole on `Finset.card`: three distinct values among four consecutive setters cannot fit
  -- into `S.erase x` of size at most two; supports `min_once` only.
  have hd := four_consecutive_distinct hpos h0 hmv (hws (s1 + 1) (by omega) (by omega))
    (hws (s1 + 2) (by omega) (by omega)) (hws (s1 + 3) (by omega) (by omega)) (hws (s1 + 4) (by omega) (by omega))
  have hsub : ({w (s1 + 1), w (s1 + 2), w (s1 + 3), w (s1 + 4)} : Finset ℝ) ⊆ S.erase x := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    have key : ∀ i, 1 ≤ i → i ≤ 4 → w (s1 + i) ∈ S.erase x := by
      intro i hi1 hi2
      refine Finset.mem_erase.mpr ⟨?_, hSmem _ (by omega) (by omega)⟩
      intro hx
      exact hmin' (s1 + i) (by omega) ⟨by omega, by omega, hx⟩
    rcases hv with rfl | rfl | rfl | rfl
    · exact key 1 le_rfl (by omega)
    · exact key 2 (by omega) (by omega)
    · exact key 3 (by omega) (by omega)
    · exact key 4 (by omega) le_rfl
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_erase_of_mem hxS
  omega

#print axioms min_once

/-- Every four consecutive moves of the window contain the smallest value, when the window has exactly three values
[L]. -/
theorem window_has_min (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ}
    {w : ℕ → ℝ} (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) {S : Finset ℝ}
    (hSmem : ∀ t, n < t → t < k → w t ∈ S) (hS3 : S.card ≤ 3) {x : ℝ} (hxS : x ∈ S) {s : ℕ} (h1 : n < s)
    (h2 : s + 3 < k) : ∃ t, s ≤ t ∧ t ≤ s + 3 ∧ w t = x := by
  by_contra hno
  push Not at hno
  -- [PROVISIONAL: counting tool] pigeonhole: three distinct values among four consecutive setters, none equal to `x`,
  -- cannot fit into `S.erase x`; supports `window_has_min` only.
  have hd := four_consecutive_distinct hpos h0 hmv (hws s h1 (by omega)) (hws (s + 1) (by omega) (by omega))
    (hws (s + 2) (by omega) (by omega)) (hws (s + 3) (by omega) (by omega))
  have hsub : ({w s, w (s + 1), w (s + 2), w (s + 3)} : Finset ℝ) ⊆ S.erase x := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    have key : ∀ i, i ≤ 3 → w (s + i) ∈ S.erase x := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨hno (s + i) (by omega) (by omega), hSmem _ (by omega) (by omega)⟩
    rcases hv with rfl | rfl | rfl | rfl
    · exact key 0 (by omega)
    · exact key 1 (by omega)
    · exact key 2 (by omega)
    · exact key 3 le_rfl
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_erase_of_mem hxS
  omega

#print axioms window_has_min


theorem exists_sorted_three {S : Finset ℝ} (h : S.card = 3) : ∃ x y z : ℝ, x < y ∧ y < z ∧ S = {x, y, z} := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqr with h3 | h3
  · exact ⟨p, q, r, h1, h3, rfl⟩
  · exact ⟨p, r, q, h2, h3, by ext; simp; tauto⟩
  · exfalso; linarith
  · exact ⟨r, p, q, h2, h1, by ext; simp; tauto⟩
  · exact ⟨q, p, r, h1, h2, by ext; simp; tauto⟩
  · exfalso; linarith
  · exact ⟨q, r, p, h3, h2, by ext; simp; tauto⟩
  · exact ⟨r, q, p, h3, h1, by ext; simp; tauto⟩

#print axioms exists_sorted_three

theorem div_inj_left {a u v : ℝ} (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (h : a / u = a / v) : u = v := by
  rw [div_eq_div_iff hu hv] at h
  exact (mul_left_cancel₀ ha h).symm

#print axioms div_inj_left

/-- **The shape of a three-valued window** [L].  Let `a` be at most every reading, set the move at `n`, and be in the way
again at `k` with no visit in between (a first return); let `w s` be the setters in between and suppose they take at most
three values.  Then there are exactly four intermediate moves, the first and the fourth are the same (the FASTEST) value
`z`, and the second and third are the two slower values, in either order:
`z y x z` or `z x y z`, `a < x < y < z`.  Every other word on three values violates the budget law of `a` or of a repeated
setter (`word_4 … word_7`), and a window of eight or more moves repeats its smallest value (`window_has_min`,
`min_once`).  Hypotheses: the cascade, `0 < seq 0`, `a` at most every reading, `a` the setter at `n`, first return.
NOT REQUIRED: `m`, `seq 0 = 1/(8m)`, the lap of `a`, any bound on the number of moves. -/
theorem three_distinct_shape {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d) {n k : ℕ}
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k))
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s))
    (hcard : ((Finset.Ico (n + 1) k).image w).card ≤ 3) :
    k = n + 5 ∧ ∃ x y z : ℝ, a < x ∧ x < y ∧ y < z ∧ w (n + 1) = z ∧ w (n + 4) = z ∧
      ((w (n + 2) = x ∧ w (n + 3) = y) ∨ (w (n + 2) = y ∧ w (n + 3) = x)) := by
  have ha0 : 0 < a := hpos a hn.1
  have hge : ∀ s, n < s → s < k → ∀ y, IsSetterAt E seq s y → a ≤ y := fun s _ _ y hy => ha y hy.1
  have h5 := return_after_four hpos hmv hnk hn hw hge
  have hS2 := return_three_distinct hpos h0 hmv hnk hn hw hge w hws
  have hSmem : ∀ t, n < t → t < k → w t ∈ (Finset.Ico (n + 1) k).image w := fun t h1 h2 =>
    Finset.mem_image.mpr ⟨t, Finset.mem_Ico.mpr ⟨by omega, h2⟩, rfl⟩
  have hS3 : ((Finset.Ico (n + 1) k).image w).card = 3 := by omega
  obtain ⟨x, y, z, hxy, hyz, hS⟩ := exists_sorted_three hS3
  have hxS : x ∈ (Finset.Ico (n + 1) k).image w := by rw [hS]; simp
  have hwxyz : ∀ t, n < t → t < k → w t = x ∨ w t = y ∨ w t = z := by
    intro t h1 h2
    have := hSmem t h1 h2
    rw [hS] at this
    simpa using this
  have hxmin : ∀ t, n < t → t < k → x ≤ w t := by
    intro t h1 h2
    rcases hwxyz t h1 h2 with h | h | h <;> rw [h] <;> linarith
  have hax : a < x := by
    obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hxS
    have ht' := Finset.mem_Ico.mp ht
    rw [← htx]
    exact a_lt_w ha hfirst hws (by omega) ht'.2
  have hx0 : 0 < x := lt_trans ha0 hax
  have hy0 : 0 < y := lt_trans hx0 hxy
  have hz0 : 0 < z := lt_trans hy0 hyz
  -- the window has at most seven moves.  [PROVISIONAL: counting tool] two disjoint windows of four moves each contain the
  -- smallest value (`window_has_min`), so it occurs twice, contradicting `min_once`; supports 'exactly four moves' only.
  have hL7 : k ≤ n + 8 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t1, ht1a, ht1b, ht1c⟩ := window_has_min hpos h0 hmv hws hSmem hS3.le hxS (s := n + 1) (by omega) (by omega)
    obtain ⟨t2, ht2a, ht2b, ht2c⟩ := window_has_min hpos h0 hmv hws hSmem hS3.le hxS (s := n + 5) (by omega) (by omega)
    exact min_once hpos h0 hmv hws hSmem hS3.le hxS hxmin (s1 := t1) (s2 := t2) (by omega) (by omega) (by omega)
      ht1c ht2c
  obtain ⟨L, hL⟩ : ∃ L, k = n + 1 + L := ⟨k - (n + 1), by omega⟩
  -- the weights u = a / w
  have hwpos : ∀ t, n < t → t < k → 0 < w t := fun t h1 h2 => hpos _ (hws t h1 h2).1
  have hux : a / z < a / y := div_lt_div_of_pos_left ha0 hy0 hyz
  have huy : a / y < a / x := div_lt_div_of_pos_left ha0 hx0 hxy
  have hu1 : a / x < 1 := (div_lt_one hx0).mpr hax
  have huz : 0 < a / z := div_pos ha0 hz0
  have hSh : ∀ s, 1 ≤ s → s ≤ L → a / w (n + s) = a / x ∨ a / w (n + s) = a / y ∨ a / w (n + s) = a / z := by
    intro s h1 h2
    rcases hwxyz (n + s) (by omega) (by omega) with h | h | h
    · left; rw [h]
    · right; left; rw [h]
    · right; right; rw [h]
  have hNe : ∀ s, 1 ≤ s → s < L → a / w (n + s) ≠ a / w (n + (s + 1)) := by
    intro s h1 h2 h
    have hh := div_inj_left ha0.ne' (hwpos (n + s) (by omega) (by omega)).ne'
      (hwpos (n + (s + 1)) (by omega) (by omega)).ne' h
    apply setter_not_twice_in_row hpos (hws (n + s) (by omega) (by omega))
    have := hws (n + (s + 1)) (by omega) (by omega)
    rw [← hh] at this
    exact this
  have hBud : ∀ s1 s2, 1 ≤ s1 → s1 < s2 → s2 ≤ L → a / w (n + s1) = a / w (n + s2) →
      3 * (a / w (n + s1)) < ∑ s ∈ Finset.Ico (s1 + 1) s2, a / w (n + s) := by
    intro s1 s2 h1 h12 h2 heq
    have hh := div_inj_left ha0.ne' (hwpos (n + s1) (by omega) (by omega)).ne'
      (hwpos (n + s2) (by omega) (by omega)).ne' heq
    have hb := pair_budget hpos hmv hws (s1 := n + s1) (s2 := n + s2) (by omega) (by omega) (by omega) hh
    have hre : ∑ t ∈ Finset.Ico (n + s1 + 1) (n + s2), w (n + s1) / w t =
        ∑ s ∈ Finset.Ico (s1 + 1) s2, w (n + s1) / w (n + s) := by
      have := Finset.sum_Ico_add (fun t => w (n + s1) / w t) (s1 + 1) s2 n
      have e1 : n + s1 + 1 = s1 + 1 + n := by omega
      have e2 : n + s2 = s2 + n := by omega
      rw [e1, e2]
      exact this.symm
    rw [hre] at hb
    have hterm : ∀ s ∈ Finset.Ico (s1 + 1) s2, w (n + s1) / w (n + s) = (a / w (n + s)) / (a / w (n + s1)) := by
      intro s hs
      have hs' := Finset.mem_Ico.mp hs
      have h1' := (hwpos (n + s1) (by omega) (by omega)).ne'
      have h2' := (hwpos (n + s) (by omega) (by omega)).ne'
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div] at hb
    have hpos1 : 0 < a / w (n + s1) := div_pos ha0 (hwpos (n + s1) (by omega) (by omega))
    rwa [lt_div_iff₀ hpos1] at hb
  have hTot : 3 < ∑ s ∈ Finset.Ico 1 (L + 1), a / w (n + s) := by
    have hb := budget_sum hpos hmv hnk hn hw w hws
    have hre : ∑ t ∈ Finset.Ico (n + 1) k, a / w t = ∑ s ∈ Finset.Ico 1 (L + 1), a / w (n + s) := by
      have := Finset.sum_Ico_add (fun t => a / w t) 1 (L + 1) n
      have e1 : n + 1 = 1 + n := by omega
      have e2 : k = L + 1 + n := by omega
      rw [e1, e2]
      exact this.symm
    rwa [hre] at hb
  have hL4 : 4 ≤ L := by omega
  have hL7' : L ≤ 7 := by omega
  interval_cases L
  · obtain ⟨e1, e4, hm⟩ := word_4 (U := fun s => a / w (n + s)) huz hux huy hu1 hSh hNe hBud hTot
    refine ⟨by omega, x, y, z, hax, hxy, hyz, ?_, ?_, ?_⟩
    · exact div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hz0.ne' e1
    · exact div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hz0.ne' e4
    · rcases hm with ⟨e2, e3⟩ | ⟨e2, e3⟩
      · left
        exact ⟨div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hx0.ne' e2,
          div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hy0.ne' e3⟩
      · right
        exact ⟨div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hy0.ne' e2,
          div_inj_left ha0.ne' (hwpos _ (by omega) (by omega)).ne' hx0.ne' e3⟩
  · exact (word_5 (U := fun s => a / w (n + s)) huz hux huy hu1 hSh hNe hBud hTot).elim
  · exact (word_6 (U := fun s => a / w (n + s)) huz hux huy hu1 hSh hNe hBud hTot).elim
  · exact (word_7 (U := fun s => a / w (n + s)) huz hux huy hu1 hSh hNe hBud hTot).elim

#print axioms three_distinct_shape


/-! ## (5) The lap arithmetic of the word `z y x z` -/

/-- **The position law of the three-valued window, in integers** [L].  `j` is the lap of the slowest reading `a` at the move
that sets it, `A, A'` the laps of `z` at its two settings, `B, C` the laps of the two middle setters (all laps of the
window are `≥ j + 1`, `A' ≥ A + 1`).  The cycle `z → y → x → z` of link windows has product `1` (`h2`: the ratio windows
`(B ± 1/8)/(A + 1/8)`, `(C ± 1/8)/(B + 1/8)`, `(A' ± 1/8)/(C + 1/8)` must contain `1`), and `z` is the same real number at
`a`'s exit and at `a`'s return (`h1`).  These force `9 ≤ j` and `j ≠ 10`: for `j ≤ 8` and for `j = 10` no integer lap `A`
exists in the interval `(3j/2 + 1, (5j + 1)/3)` that survives `h1`, `h2` (exact integer arithmetic below). -/
theorem lap_arith {j A A' B C : ℤ} (hj : 0 ≤ j) (hA0 : j + 1 ≤ A) (hA : A + 1 ≤ A') (hB : j + 1 ≤ B)
    (hC : j + 1 ≤ C) (h1 : (8 * A - 1) * (8 * j + 7) < (8 * A' + 1) * (8 * j + 1))
    (h2 : (8 * B - 1) * (8 * C - 1) * (8 * A' - 1) < (8 * A + 1) * (8 * B + 1) * (8 * C + 1)) :
    9 ≤ j ∧ j ≠ 10 := by
  have hP : (8 * j + 7) * (8 * B + 1) ≤ (8 * B - 1) * (8 * j + 9) := by nlinarith
  have hQ : (8 * j + 7) * (8 * C + 1) ≤ (8 * C - 1) * (8 * j + 9) := by nlinarith
  have hP0 : 0 ≤ (8 * j + 7) * (8 * B + 1) := mul_nonneg (by omega) (by omega)
  have hQ0 : 0 ≤ (8 * j + 7) * (8 * C + 1) := mul_nonneg (by omega) (by omega)
  have hPQ : (8 * j + 7) ^ 2 * ((8 * B + 1) * (8 * C + 1)) ≤ (8 * j + 9) ^ 2 * ((8 * B - 1) * (8 * C - 1)) := by
    have := mul_le_mul hP hQ hQ0 (by nlinarith)
    nlinarith
  have hA' : 0 ≤ 8 * A' - 1 := by omega
  have h3 : (8 * A' - 1) * ((8 * j + 7) ^ 2 * ((8 * B + 1) * (8 * C + 1))) ≤
      (8 * A' - 1) * ((8 * j + 9) ^ 2 * ((8 * B - 1) * (8 * C - 1))) := mul_le_mul_of_nonneg_left hPQ hA'
  have h4 : (8 * j + 9) ^ 2 * ((8 * B - 1) * (8 * C - 1) * (8 * A' - 1)) <
      (8 * j + 9) ^ 2 * ((8 * A + 1) * (8 * B + 1) * (8 * C + 1)) := mul_lt_mul_of_pos_left h2 (pow_pos (by omega) 2)
  have h5 : (8 * A' - 1) * (8 * j + 7) ^ 2 * ((8 * B + 1) * (8 * C + 1)) <
      (8 * A + 1) * (8 * j + 9) ^ 2 * ((8 * B + 1) * (8 * C + 1)) := by nlinarith
  have h6 : (8 * A' - 1) * (8 * j + 7) ^ 2 < (8 * A + 1) * (8 * j + 9) ^ 2 :=
    lt_of_mul_lt_mul_right h5 (mul_nonneg (by omega) (by omega))
  clear h2 h3 h4 h5 hPQ hP hQ hP0 hQ0
  by_contra hcon
  have : j ≤ 8 ∨ j = 10 := by omega
  rcases this with hj8 | hj10
  · interval_cases j <;> norm_num at h1 h6 <;>
      (have hAb : A ≤ 60 := by omega
       interval_cases A <;> omega)
  · subst hj10; norm_num at h1 h6
    have hAb : A ≤ 60 := by omega
    interval_cases A <;> omega

#print axioms lap_arith

/-- **The window `z y x z` forces `9 ≤ j` and `j ≠ 10`** [L]: `j` the lap of `a` at the move that sets it.  Hypotheses: the
cascade with `0 < seq 0`; `a` at most every reading; `a` the setter at `n`; first return at `k`; the setters in between take
at most three values.  NOT REQUIRED: `m`, `seq 0 = 1/(8m)`, any bound on moves. -/
theorem three_distinct_lap {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d) {n k : ℕ}
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k))
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s))
    (hcard : ((Finset.Ico (n + 1) k).image w).card ≤ 3) :
    9 ≤ lap a (seq n) ∧ lap a (seq n) ≠ 10 := by
  obtain ⟨hk5, x, y, z, hax, hxy, hyz, e1, e4, hmid⟩ := three_distinct_shape hpos h0 hmv ha hn hnk hw hfirst hws hcard
  subst hk5
  have ha0 : 0 < a := hpos a hn.1
  have hx0 : 0 < x := lt_trans ha0 hax
  have hy0 : 0 < y := lt_trans hx0 hxy
  have hz0 : 0 < z := lt_trans hy0 hyz
  -- the four setters
  have hs1 := hws (n + 1) (by omega) (by omega)
  have hs2 := hws (n + 2) (by omega) (by omega)
  have hs3 := hws (n + 3) (by omega) (by omega)
  have hs4 := hws (n + 4) (by omega) (by omega)
  set p := w (n + 2) with hp
  set q := w (n + 3) with hq
  have hp0 : 0 < p := hpos _ hs2.1
  have hq0 : 0 < q := hpos _ hs3.1
  have hap : a ≤ p := ha _ hs2.1
  have haq : a ≤ q := ha _ hs3.1
  have haz : a ≤ z := le_of_lt (lt_trans hax (lt_trans hxy hyz))
  rw [e1] at hs1
  rw [e4] at hs4
  -- landing readings
  have lz1 : z * seq (n + 2) = (lap z (seq (n + 1)) : ℝ) + 1 / 8 := by
    rw [hs1.2.2]; exact setter_reading hz0 hs1.2.1
  have lp2 : p * seq (n + 3) = (lap p (seq (n + 2)) : ℝ) + 1 / 8 := by
    rw [hs2.2.2]; exact setter_reading hp0 hs2.2.1
  have lq3 : q * seq (n + 4) = (lap q (seq (n + 3)) : ℝ) + 1 / 8 := by
    rw [hs3.2.2]; exact setter_reading hq0 hs3.2.1
  have lz4 : z * seq (n + 5) = (lap z (seq (n + 4)) : ℝ) + 1 / 8 := by
    rw [hs4.2.2]; exact setter_reading hz0 hs4.2.1
  have la0 : a * seq (n + 1) = (lap a (seq n) : ℝ) + 1 / 8 := by
    rw [hn.2.2]; exact setter_reading ha0 hn.2.1
  -- windows (in the way)
  have wz1 := abs_lt.mp (abs_sub_lap_lt hs1.2.1)
  have wp := abs_lt.mp (abs_sub_lap_lt hs2.2.1)
  have wq := abs_lt.mp (abs_sub_lap_lt hs3.2.1)
  have wz4 := abs_lt.mp (abs_sub_lap_lt hs4.2.1)
  have wa := abs_lt.mp (abs_sub_lap_lt hw)
  -- laps
  have hj0 : 0 ≤ lap a (seq n) := setter_lap_nonneg hpos h0 hmv hn
  have hlapA : lap a (seq n) + 1 ≤ lap z (seq (n + 1)) :=
    later_lap_of_ge hpos h0 hmv (show n < n + 1 by omega) hn haz hs1.2.1
  have hlapB : lap a (seq n) + 1 ≤ lap p (seq (n + 2)) :=
    later_lap_of_ge hpos h0 hmv (show n < n + 2 by omega) hn hap hs2.2.1
  have hlapC : lap a (seq n) + 1 ≤ lap q (seq (n + 3)) :=
    later_lap_of_ge hpos h0 hmv (show n < n + 3 by omega) hn haq hs3.2.1
  have hlapJ : lap a (seq n) + 1 ≤ lap a (seq (n + 5)) := setter_later_lap hpos h0 hmv hnk hn hw
  have hrec : lap z (seq (n + 1)) < lap z (seq (n + 4)) :=
    setter_recur_lap hpos h0 hmv (show n + 1 < n + 4 by omega) hs1 hs4
  -- integer names
  set j := lap a (seq n) with hjdef
  set A := lap z (seq (n + 1)) with hAdef
  set B := lap p (seq (n + 2)) with hBdef
  set C := lap q (seq (n + 3)) with hCdef
  set A' := lap z (seq (n + 4)) with hA'def
  set J := lap a (seq (n + 5)) with hJdef
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj0
  have hAR : (j : ℝ) + 1 ≤ A := by exact_mod_cast hlapA
  have hBR : (j : ℝ) + 1 ≤ B := by exact_mod_cast hlapB
  have hCR : (j : ℝ) + 1 ≤ C := by exact_mod_cast hlapC
  have hA'R : (A : ℝ) + 1 ≤ A' := by exact_mod_cast (show A + 1 ≤ A' by omega)
  have hJR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hlapJ
  -- h1: (A - 1/8)(j + 7/8) < (A' + 1/8)(j + 1/8)
  have key1 : ((A : ℝ) - 1 / 8) * ((j : ℝ) + 1 - 1 / 8) < ((A' : ℝ) + 1 / 8) * ((j : ℝ) + 1 / 8) := by
    have e : (z * seq (n + 5)) * (a * seq (n + 1)) = (z * seq (n + 1)) * (a * seq (n + 5)) := by ring
    rw [lz4, la0] at e
    have m1 : ((A : ℝ) - 1 / 8) * ((j : ℝ) + 1 - 1 / 8) < (z * seq (n + 1)) * (a * seq (n + 5)) := by
      apply mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  -- h2: cycle
  have key2 : ((B : ℝ) - 1 / 8) * ((C : ℝ) - 1 / 8) * ((A' : ℝ) - 1 / 8) <
      ((A : ℝ) + 1 / 8) * ((B : ℝ) + 1 / 8) * ((C : ℝ) + 1 / 8) := by
    have e : (p * seq (n + 2)) * (q * seq (n + 3)) * (z * seq (n + 4)) =
        (z * seq (n + 2)) * (p * seq (n + 3)) * (q * seq (n + 4)) := by ring
    rw [lz1, lp2, lq3] at e
    have m1 : ((B : ℝ) - 1 / 8) * ((C : ℝ) - 1 / 8) * ((A' : ℝ) - 1 / 8) <
        (p * seq (n + 2)) * (q * seq (n + 3)) * (z * seq (n + 4)) := by
      apply mul_lt_mul'' (mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith))
        (by linarith) (by nlinarith) (by linarith)
    linarith
  have int1 : (8 * A - 1) * (8 * j + 7) < (8 * A' + 1) * (8 * j + 1) := by
    have : (((8 * A - 1) * (8 * j + 7) : ℤ) : ℝ) < (((8 * A' + 1) * (8 * j + 1) : ℤ) : ℝ) := by
      push_cast
      linarith [key1]
    exact_mod_cast this
  have int2 : (8 * B - 1) * (8 * C - 1) * (8 * A' - 1) < (8 * A + 1) * (8 * B + 1) * (8 * C + 1) := by
    have : (((8 * B - 1) * (8 * C - 1) * (8 * A' - 1) : ℤ) : ℝ) <
        (((8 * A + 1) * (8 * B + 1) * (8 * C + 1) : ℤ) : ℝ) := by
      push_cast
      linarith [key2]
    exact_mod_cast this
  exact lap_arith hj0 (by omega) (by omega) (by omega) (by omega) int1 int2

#print axioms three_distinct_lap

/-- **Four distinct intermediate setters when the slowest is set on a lap that the window cannot use** [L]: if the lap `j`
of `a` at the move that sets it satisfies `j ≤ 8` or `j = 10`, a first return of `a` has at least FOUR distinct
intermediate setter values.  This is the true part of `Ladder5.FourDistinctLaw` (which is false: `not_fourDistinctLaw`,
the example has `j = 9`).  Hypotheses used: the cascade, `0 < seq 0`, `a` at most every reading, first return; NOT used:
`m`, `seq 0 = 1/(8m)`. -/
theorem four_distinct_of_lap {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d) {n k : ℕ}
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k))
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s))
    (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) :
    3 < ((Finset.Ico (n + 1) k).image w).card := by
  by_contra hcon
  have := three_distinct_lap hpos h0 hmv ha hn hnk hw hfirst hws (by omega)
  omega

#print axioms four_distinct_of_lap


/-- **If the smallest setter value of the window recurs, the window has at least four distinct values** [L] -- the
symbolic reason for FOUR: the budget forces four moves between two visits of one value (`x / w ≤ 1` for every term), four
consecutive moves take three distinct values (`four_consecutive_distinct`), none of them the recurring value. -/
theorem four_of_min_recurs {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) {x : ℝ}
    (hmin : ∀ t, n < t → t < k → x ≤ w t) {s1 s2 : ℕ} (h1 : n < s1) (h12 : s1 < s2) (h2 : s2 < k)
    (e1 : w s1 = x) (e2 : w s2 = x) : 3 < ((Finset.Ico (n + 1) k).image w).card := by
  by_contra hcon
  have hSmem : ∀ t, n < t → t < k → w t ∈ (Finset.Ico (n + 1) k).image w := fun t ht1 ht2 =>
    Finset.mem_image.mpr ⟨t, Finset.mem_Ico.mpr ⟨by omega, ht2⟩, rfl⟩
  have hxS : x ∈ (Finset.Ico (n + 1) k).image w := by rw [← e1]; exact hSmem s1 h1 (by omega)
  exact min_once hpos h0 hmv hws hSmem (by omega) hxS hmin h1 h12 h2 e1 e2

#print axioms four_of_min_recurs

/-- **The corrected statement** (a definition of the statement; proved below): `FourDistinctLaw` with the hypothesis on the
base `m` replaced by the lap condition on the slowest reading. -/
-- STANDING: DEFINITION
def FourDistinctLawLap : Prop :=
  ∀ (E : Finset ℝ) (seq : ℕ → ℝ) (a : ℝ) (n k : ℕ),
    (∀ d ∈ E, 0 < d) → 0 < seq 0 → (∀ i, IsMove E (seq i) (seq (i + 1))) →
    (∀ d ∈ E, a ≤ d) → IsSetterAt E seq n a → n < k → InWay a (seq k) →
    (∀ s, n < s → s < k → ¬ InWay a (seq s)) → (lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) →
    ∀ w : ℕ → ℝ, (∀ s, n < s → s < k → IsSetterAt E seq s (w s)) →
      3 < ((Finset.Ico (n + 1) k).image w).card

/-- `FourDistinctLawLap` is a theorem [L]. -/
theorem fourDistinctLawLap : FourDistinctLawLap :=
  fun _ _ _ _ _ hpos h0 hmv ha hn hnk hw hfirst hj _ hws =>
    four_distinct_of_lap hpos h0 hmv ha hn hnk hw hfirst hws hj

#print axioms fourDistinctLawLap

/-- **Corrected `slowest_of_four_never_returns`** [L]: at most four readings, `a` the slowest, set on a lap `j ≤ 8` or
`j = 10`: `a` does not return.  (Without the lap condition the statement is false: `slowest_of_four_can_return`.) -/
theorem slowest_of_four_never_returns_lap {E : Finset ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ}
    (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0) (hmv : ∀ i, IsMove E (seq i) (seq (i + 1)))
    (hcard : E.card ≤ 4) (ha : ∀ d ∈ E, a ≤ d) (hn : IsSetterAt E seq n a) (hnk : n < k)
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s))
    (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) : ¬ InWay a (seq k) := by
  intro hw
  have hex : ∀ s, n < s → s < k → ∃ y, IsSetterAt E seq s y :=
    fun s _ hs => setter_before_visit hmv hn.1 hw hs
  choose! w hw' using hex
  have h3 := four_distinct_of_lap hpos h0 hmv ha hn hnk hw hfirst hw' hj
  have hsub : (Finset.Ico (n + 1) k).image w ⊆ E.erase a := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    have hs' := Finset.mem_Ico.mp hs
    have hset := hw' s (by omega) hs'.2
    refine Finset.mem_erase.mpr ⟨?_, hset.1⟩
    intro hva
    have := hset.2.1
    rw [hva] at this
    exact hfirst s (by omega) hs'.2 this
  have hE : (E.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem hn.1
    omega
  have := Finset.card_le_card hsub
  omega

#print axioms slowest_of_four_never_returns_lap

/-- **Corrected `five_first_return_all_others`** [L]: at most five readings, `a` the slowest set on a lap `j ≤ 8` or
`j = 10`: the first return of `a` passes through every other reading. -/
theorem five_first_return_all_others_lap {E : Finset ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ}
    (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0) (hmv : ∀ i, IsMove E (seq i) (seq (i + 1)))
    (hcard : E.card ≤ 5) (ha : ∀ d ∈ E, a ≤ d) (hn : IsSetterAt E seq n a) (hnk : n < k)
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) (hw : InWay a (seq k))
    (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    (Finset.Ico (n + 1) k).image w = E.erase a := by
  have h3 := four_distinct_of_lap hpos h0 hmv ha hn hnk hw hfirst hws hj
  have hsub : (Finset.Ico (n + 1) k).image w ⊆ E.erase a := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    have hs' := Finset.mem_Ico.mp hs
    have hset := hws s (by omega) hs'.2
    refine Finset.mem_erase.mpr ⟨?_, hset.1⟩
    intro hva
    have := hset.2.1
    rw [hva] at this
    exact hfirst s (by omega) hs'.2 this
  have hE : (E.erase a).card ≤ 4 := by
    have := Finset.card_erase_of_mem hn.1
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

#print axioms five_first_return_all_others_lap


/-- A slowest reading in the way with `a · t < 71/8` is on a lap at most `8`. -/
theorem lap_le_eight_of_lt {a t : ℝ} (hin : InWay a t) (hlt : a * t < 71 / 8) : lap a t ≤ 8 := by
  have hb := (abs_lt.mp (abs_sub_lap_lt hin)).1
  have h1 : (lap a t : ℝ) < 9 := by linarith
  have h2 : lap a t < 9 := by exact_mod_cast h1
  omega

#print axioms lap_le_eight_of_lt

/-- **The old statement, inside the first window, for readings below ten units** [L].  The cascade from `1/(8m)`, every
reading at least `m`, `a` the slowest, `a ≤ 10 m`, and `a` set at a move that starts inside the first window
`seq n ≤ 7/(8m)` (`R = 8 m t ≤ 7`, the gate of `Gate`): a first return of `a` has at least four distinct intermediate
setter values.  This is `Ladder5.FourDistinctLaw` with the two added hypotheses `a ≤ 10 m` and `seq n ≤ 7/(8m)`; the
counterexample `not_fourDistinctLaw` has `a = 875/12 m` (and `seq 0 = 1/(8m)`, inside the window).  It explains the exact
data of `ladder5_v2.out` for the populations with all readings at most `10 m`. -/
theorem four_distinct_in_gate {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d)
    (hamax : a ≤ 10 * m) {n k : ℕ} (hn : IsSetterAt E seq n a) (hgate : seq n ≤ 7 / (8 * m)) (hnk : n < k)
    (hw : InWay a (seq k)) (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    3 < ((Finset.Ico (n + 1) k).image w).card := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have h00 : 0 < seq 0 := by rw [h0]; positivity
  have hseq : 0 ≤ seq n := le_trans h00.le (seq_mono hpos hmv (Nat.zero_le n))
  have h1 : a * seq n ≤ (10 * m) * (7 / (8 * m)) :=
    mul_le_mul hamax hgate hseq (by positivity)
  have h2 : (10 * m) * (7 / (8 * m)) = 70 / 8 := by field_simp; norm_num
  refine four_distinct_of_lap hpos h00 hmv ha hn hnk hw hfirst hws (Or.inl ?_)
  exact lap_le_eight_of_lt hn.2.1 (by linarith)

#print axioms four_distinct_in_gate

end Window

#print axioms word_4
#print axioms word_5
#print axioms word_6
#print axioms word_7
#print axioms ce_setter0
#print axioms ce_setter1
#print axioms ce_setter2
#print axioms ce_setter3
#print axioms ce_setter4
#print axioms ce_inWay5
#print axioms ce_first
#print axioms ce_card
#print axioms mem_CE

end FourDistinct

end Fresh
