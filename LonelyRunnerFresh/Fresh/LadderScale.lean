import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.FiveReach
import Fresh.Ladder
import Fresh.Ladder5
import Fresh.FourDistinct
import Fresh.QuotientReduction
import Fresh.ScaleHierarchy
import Fresh.DispCell

/-!
# Five disparities by the cascade chain, and where the scale of the slowest reading enters (Task BE)

Written 2026-10-09.  Nothing is imported from the existing `LonelyRunner` repo.  Exact reals only; every disparity is
positive (no runner is stationary); no floats.  Data (exact fractions, explicit grids, counts are observations of those grids only): `experiments/n8/ladder_scale_v1.py/.out`.

Setting.  `E` is a finite set of readings (disparities) all at least `m > 0`; the cascade runs from `seq 0 = 1/(8m)`
(`R = 8 m t = 1`).  `a = min E` is the slowest reading and `ρ = a/m` its quotient.

## Results (grades in the docstrings; each [L] theorem has its `#print axioms` line)

* (1) The lap of a reading in the way against its quotient (exact relation, no cap): `ratio_lt_lap` says `ρ < 8 j + 1`
  for a reading on lap `j` at any instant `≥ 1/(8m)`; `lap_le_eight_of_ratio_time` says `j ≤ 8` as soon as the instant is at
  most `B/(8m)` and `ρ B < 71`.  `elapsed_le` is the additive time law: the instant after `n` moves, all by readings
  `≥ a`, is at most `1/(8m) + n/(4a)`; so the slowest reading's setting at move `n` has `j ≤ 8` when `ρ + 2 n < 71`
  (`lap_le_eight_of_moves`).  The lap condition of FourDistinct's true law is thereby read off the cascade, not offered as
  a ceiling on the readings.
* (2) The chain argument for four readings, in the setting where FourDistinct's true law applies:
  `window_has_setter` (every element of a set of at most four readings sets in every window of eight consecutive
  non-fixed moves; the pigeonhole is `[PROVISIONAL: counting tool]`), `min_sets_once` (`a` sets once when its lap
  satisfies the lap condition), `four_cascade_fixes` (the cascade over at most four readings is fixed after at most
  fifteen moves).
* (3) `position_of_moves`: the additive position law `8 m seq N ≤ 1 + 2 N m / a`.
  `reach_four_of_lap`, `reach_four_of_ratio`: Reach-type conclusion in the first window `R ∈ [1, 7]` for `5 m ≤ a < 57 m`
  (and, with the lap condition as the hypothesis, `5 m ≤ a`).  `five_disparities_of_ratio`: five disparities have a lonely
  instant when the second smallest is in `[5 d_min, 57 d_min)`.
* (4) Six disparities and the large-quotient regime: what the laws give, and exactly what is missing (docstrings of
  section (4)).

## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED)

| hypothesis | status |
|---|---|
| `E.card ≤ 4` in `window_has_setter`, `four_cascade_fixes`, `reach_four_of_lap` | REQUIRED for the proof (`E.erase a` must have at most three members for `block_four_false'`); at six readings the window statement itself is false [OBS] (E_six, `ladder_scale_v1.out` section 7: an element does not set in eight consecutive moves); at five readings UNDECIDED (no failure on the grids searched) |
| `a ∈ E` in `window_has_setter` | REQUIRED (a reading outside `E` is never a setter) |
| `0 < seq 0` | REQUIRED for the proof (`triple_law`, `later_lap_of_ge`); NOT REQUIRED: any base `m`, `seq 0 = 1/(8m)`, in sections (2) and `elapsed_le` |
| `a` least in `min_sets_once`, `four_cascade_fixes` | REQUIRED for the proof (`FourDistinct`: AY's `x y x` return after one move has `a` not least) |
| `LapCond` | REQUIRED for the proof of `min_sets_once`; the statement 'a sets once' is false without it (`slowest_of_four_can_return`); false for `CE` (`not_lapCond_CE`); the conclusion of `four_cascade_fixes` itself: no counterexample found, no proof without `LapCond`, UNDECIDED |
| `5 m ≤ a` in `reach_four_of_lap` | REQUIRED for the proof (fifteen moves against `3 a/m`); NOT shown required for the statement: [OBS] no set of the grids with `a < 5 m` has `R > 7` (section 1-4 of the data); UNDECIDED |
| `a < 57 m` in `lapCond_of_ratio` | REQUIRED for that derivation (the additive time law gives `ρ + 2 n < 71` at `n ≤ 7`); at `ρ ≥ 65` the lap is `≥ 9` (`nine_le_lap_of_ratio`); `57 ≤ ρ < 65`: not decided by the two inequalities of `lap_range` |
| `B ≤ 7`, `0 < m` in `add_dmin` | REQUIRED (`Ladder.audit_gate_needed`, `Ladder.audit_zero_disparity`) |
| positivity of the disparities | REQUIRED as stated (divisions by them) |

Provenance (existing declarations whose argument was read and understood, nothing copied):
`Ladder.reach_three_cascade` (the template: slowest return, `no_xyxy`, `block_four_false`), `Ladder5.sum_incr` and
`Ladder5.return_after_four`, `FourDistinct.slowest_of_four_never_returns_lap`, `FourDistinct.lap_le_eight_of_lt`,
`Ladder.ladder_step`.  The window pigeonhole with the excluded reading `a` is new here; the additive time law and the
position law are new here.
-/

open Classical

namespace Fresh

namespace LadderScale

open Cascade Dilation ChainLaws FiveReachStudy Ladder Ladder5 FourDistinct

/-! ## (1) The lap of a reading in the way against its quotient -/

/-- **The quotient is below `8 j + 1`** [L].  A reading `y ≥ m` in the way at an instant `t ≥ 1/(8m)` is on a lap `j` with
`y/m < 8 j + 1`.  Hypotheses: `0 < m` (REQUIRED: the instant `1/(8m)` is the start), `1/(8m) ≤ t` (REQUIRED: it gives
`y t ≥ y/(8m)`); `m ≤ y` is NOT REQUIRED (the proof never uses it; only `y/m` is bounded). -/
theorem ratio_lt_lap {m y t : ℝ} (hm : 0 < m) (ht : 1 / (8 * m) ≤ t) (hy : 0 ≤ y) (hw : InWay y t) :
    y / m < 8 * (lap y t : ℝ) + 1 := by
  have hb := (abs_lt.mp (abs_sub_lap_lt hw)).2
  have h1 : y / (8 * m) ≤ y * t := by
    have := mul_le_mul_of_nonneg_left ht hy
    calc y / (8 * m) = y * (1 / (8 * m)) := by ring
      _ ≤ y * t := this
  have h2 : y / m = 8 * (y / (8 * m)) := by field_simp
  rw [h2]
  linarith

#print axioms ratio_lt_lap

/-- **The lap of a reading in the way is at most eight when the instant is at most `B/(8m)` and `ρ B < 71`** [L]. -/
theorem lap_le_eight_of_ratio_time {m y t B : ℝ} (hm : 0 < m) (hy : 0 ≤ y) (htB : t ≤ B / (8 * m))
    (hB : y / m * B < 71) (hw : InWay y t) : lap y t ≤ 8 := by
  refine lap_le_eight_of_lt hw ?_
  have h1 : y * t ≤ y * (B / (8 * m)) := mul_le_mul_of_nonneg_left htB hy
  have h2 : y * (B / (8 * m)) = (y / m * B) / 8 := by field_simp
  linarith

#print axioms lap_le_eight_of_ratio_time

/-- **The exact range of the lap at the start** [L]: at an instant `t` with `1/(8m) ≤ t ≤ B/(8m)`, a reading in the way
has `(ρ − 1)/8 < j` and `j < ρ B/8 + 1/8`.  So `j ≤ 8` forces `ρ < 65`, and `ρ B < 71` forces `j ≤ 8`. `[PROVISIONAL: covering]`, a window against a lap, supporting the lap relation only. -/
theorem lap_range {m y t B : ℝ} (hm : 0 < m) (hy : 0 ≤ y) (ht : 1 / (8 * m) ≤ t) (htB : t ≤ B / (8 * m))
    (hw : InWay y t) :
    (y / m - 1) / 8 < (lap y t : ℝ) ∧ (lap y t : ℝ) < (y / m * B) / 8 + 1 / 8 := by
  refine ⟨?_, ?_⟩
  · have := ratio_lt_lap hm ht hy hw
    linarith
  · have hb := (abs_lt.mp (abs_sub_lap_lt hw)).1
    have h1 : y * t ≤ y * (B / (8 * m)) := mul_le_mul_of_nonneg_left htB hy
    have h2 : y * (B / (8 * m)) = (y / m * B) / 8 := by field_simp
    linarith

#print axioms lap_range

/-- A lap of at most eight forces the quotient below 65, and a lap of at most ten (the other value allowed by
`FourDistinct.four_distinct_of_lap`) forces it below 81. -/
theorem ratio_lt_of_lap_le {m y t : ℝ} (hm : 0 < m) (ht : 1 / (8 * m) ≤ t) (hy : 0 ≤ y) (hw : InWay y t) {j : ℤ}
    (hj : lap y t ≤ j) : y / m < 8 * (j : ℝ) + 1 := by
  have := ratio_lt_lap hm ht hy hw
  have hj' : (lap y t : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

#print axioms ratio_lt_of_lap_le

/-! ## (1b) The additive time law -/

/-- **Elapsed time, additive form** [L].  If the moves `0, …, n−1` of the cascade all have setters and every member of
`E` is at least `a > 0`, then `seq n ≤ seq 0 + n/(4a)`.  (The telescoping of `Ladder5.sum_incr`; each move advances by
less than `1/(4y) ≤ 1/(4a)`.)  Not used: any ordering of the readings, any base `m`, `seq 0 = 1/(8m)`. `[PROVISIONAL: counting tool]` at this step, supporting the position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this bound) shows where it lands. -/
theorem elapsed_le {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {a : ℝ} (ha0 : 0 < a)
    (ha : ∀ d ∈ E, a ≤ d) (n : ℕ) (hset : ∀ s, s < n → ∃ y, IsSetterAt E seq s y) :
    seq n ≤ seq 0 + (n : ℝ) / (4 * a) := by
  choose! w hw using hset
  have hs := sum_incr hpos 0 w n (by intro s _ h2; exact hw s (by omega))
  rw [zero_add] at hs
  have hterm : ∀ s ∈ Finset.Ico 0 n, 1 / (4 * w s) ≤ 1 / (4 * a) := by
    intro s hs'
    have hs'' := Finset.mem_Ico.mp hs'
    have hwE := (hw s hs''.2).1
    have hw0 := hpos _ hwE
    have := ha _ hwE
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hle := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico] at hle
  simp only [nsmul_eq_mul, Nat.sub_zero] at hle
  have : (n : ℝ) * (1 / (4 * a)) = (n : ℝ) / (4 * a) := by ring
  linarith

#print axioms elapsed_le

/-! ## (2) The chain argument for at most four readings, from any start -/

/-- **Four consecutive moves whose setters avoid two readings are impossible when only two values remain** [L].
The generalisation of `Ladder.block_four_false` that the window argument needs: the excluded readings `a`, `b` are
arbitrary members, `E` itself is the set whose cascade runs, and `((E.erase a).erase b).card ≤ 2`.
`[PROVISIONAL: counting tool]` (`FiveReach.eq_of_card_le_two`: two letters cannot be three distinct letters), supporting
only this statement. -/
theorem block_four_false' {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a b : ℝ} (hcard : ((E.erase a).erase b).card ≤ 2) {n : ℕ}
    {w : ℕ → ℝ} (hw : ∀ i, n ≤ i → i ≤ n + 3 → IsSetterAt E seq i (w i))
    (hna : ∀ i, n ≤ i → i ≤ n + 3 → w i ≠ a) (hnb : ∀ i, n ≤ i → i ≤ n + 3 → w i ≠ b) : False := by
  have hmem : ∀ i, n ≤ i → i ≤ n + 3 → w i ∈ (E.erase a).erase b :=
    fun i h1 h2 => Finset.mem_erase.mpr ⟨hnb i h1 h2, Finset.mem_erase.mpr ⟨hna i h1 h2, (hw i h1 h2).1⟩⟩
  have hne : ∀ i, n ≤ i → i + 1 ≤ n + 3 → w (i + 1) ≠ w i := by
    intro i h1 h2 heq
    exact setter_not_twice_in_row hpos (hw i h1 (by omega)) (heq ▸ hw (i + 1) (by omega) h2)
  have e02 : w n = w (n + 2) :=
    eq_of_card_le_two hcard (hmem n le_rfl (by omega)) (hmem (n + 1) (by omega) (by omega))
      (hmem (n + 2) (by omega) (by omega))
      (Ne.symm (hne n le_rfl (by omega))) (Ne.symm (hne (n + 1) (by omega) (by omega)))
  have e13 : w (n + 1) = w (n + 3) :=
    eq_of_card_le_two hcard (hmem (n + 1) (by omega) (by omega)) (hmem (n + 2) (by omega) (by omega))
      (hmem (n + 3) (by omega) (by omega))
      (Ne.symm (hne (n + 1) (by omega) (by omega))) (Ne.symm (hne (n + 2) (by omega) (by omega)))
  exact no_xyxy hpos h0 hmv (hw n le_rfl (by omega)) (hw (n + 1) (by omega) (by omega))
    (e02 ▸ hw (n + 2) (by omega) (by omega)) (e13 ▸ hw (n + 3) (by omega) (by omega))

#print axioms block_four_false'

/-- **Every member of a set of at most four readings sets in every window of eight consecutive non-fixed moves** [L].
`E` has at most four members, `a ∈ E` (any member, not necessarily the slowest), and each of the moves `s, …, s+7` has a
setter.  Then `a` is a setter at one of them.  The proof is `Ladder.reach_three_cascade`'s, with the three other readings
`E.erase a` in place of the whole set: the least `b` of `E.erase a` returns only after four moves
(`Ladder5.return_after_four`, whose hypothesis is only that the intermediate setters are `≥ b`: they lie in `E.erase a`),
so two of eight moves, and a block of four consecutive moves without `b` and without `a` leaves two values, which cannot
alternate (`no_xyxy`).  `[PROVISIONAL: counting tool]` in the pigeonhole of the five blocks (`omega`) and in
`block_four_false'`, supporting only the claim 'an eight-window has a setting of every member'; no move bound is offered as a
result here.  Hypotheses: `E.card ≤ 4` REQUIRED for this proof (with five readings `E.erase a` has four and
`block_four_false'` fails: the window of eight is then not forced to contain `a`); `0 < seq 0` used (laps of later settings);
NOT used: any base `m`, `seq 0 = 1/(8m)`, any ordering of `a` among the readings. -/
theorem window_has_setter {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E) {s : ℕ}
    (hset : ∀ i, s ≤ i → i ≤ s + 7 → ∃ x, IsSetterAt E seq i x) :
    ∃ i, s ≤ i ∧ i ≤ s + 7 ∧ IsSetterAt E seq i a := by
  by_contra hno
  push Not at hno
  choose! w hw using hset
  have hwa : ∀ i, s ≤ i → i ≤ s + 7 → w i ≠ a := fun i h1 h2 h => hno i h1 h2 (h ▸ hw i h1 h2)
  have hS : (E.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem haE
    omega
  have hmem : ∀ i, s ≤ i → i ≤ s + 7 → w i ∈ E.erase a :=
    fun i h1 h2 => Finset.mem_erase.mpr ⟨hwa i h1 h2, (hw i h1 h2).1⟩
  have hne : (E.erase a).Nonempty := ⟨w s, hmem s le_rfl (by omega)⟩
  obtain ⟨b, hb⟩ := exists_isLeast hne
  -- two settings of `b` inside the window are at least five moves apart
  have hS5 : ∀ i j, s ≤ i → j ≤ s + 7 → IsSetterAt E seq i b → IsSetterAt E seq j b → i < j → i + 5 ≤ j := by
    intro i j hi hj hbi hbj hij
    refine return_after_four hpos hmv hij hbi hbj.2.1 ?_
    intro t ht1 ht2 y hy
    have hya : y ≠ a := fun h => hno t (by omega) (by omega) (h ▸ hy)
    exact hb.2 (Finset.mem_erase.mpr ⟨hya, hy.1⟩)
  -- some block of four consecutive moves has no setting of `b`
  have hwin : ∃ t, s ≤ t ∧ t ≤ s + 4 ∧ ∀ i, t ≤ i → i ≤ t + 3 → ¬ IsSetterAt E seq i b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, h0a, h0b, h0c⟩ := hcon s le_rfl (by omega)
    obtain ⟨i1, h1a, h1b, h1c⟩ := hcon (s + 1) (by omega) (by omega)
    obtain ⟨i2, h2a, h2b, h2c⟩ := hcon (s + 2) (by omega) (by omega)
    obtain ⟨i3, h3a, h3b, h3c⟩ := hcon (s + 3) (by omega) (by omega)
    obtain ⟨i4, h4a, h4b, h4c⟩ := hcon (s + 4) (by omega) (by omega)
    have p01 := hS5 i0 i1 (by omega) (by omega) h0c h1c
    have p10 := hS5 i1 i0 (by omega) (by omega) h1c h0c
    have p12 := hS5 i1 i2 (by omega) (by omega) h1c h2c
    have p21 := hS5 i2 i1 (by omega) (by omega) h2c h1c
    have p23 := hS5 i2 i3 (by omega) (by omega) h2c h3c
    have p32 := hS5 i3 i2 (by omega) (by omega) h3c h2c
    have p34 := hS5 i3 i4 (by omega) (by omega) h3c h4c
    have p43 := hS5 i4 i3 (by omega) (by omega) h4c h3c
    omega
  obtain ⟨t, hts, ht4, htb⟩ := hwin
  have hbmem : b ∈ E.erase a := hb.1
  have hc2 : ((E.erase a).erase b).card ≤ 2 := by
    have := Finset.card_erase_of_mem hbmem
    omega
  refine block_four_false' hpos h0 hmv hc2 (n := t) (w := w) (fun i h1 h2 => hw i (by omega) (by omega))
    (fun i h1 h2 => hwa i (by omega) (by omega)) (fun i h1 h2 h => ?_)
  exact htb i h1 h2 (h ▸ hw i (by omega) (by omega))

#print axioms window_has_setter

/-- **The slowest reading sets only once, when its lap at the first setting satisfies the lap condition** [L].  `a` is at
most every member of `E` (`E.card ≤ 4`), sets at `n` and again at `n' > n`; if `lap a (seq n) ≤ 8` or `= 10` this is
impossible.  The first return after `n` is taken from the least visit (`Nat.find`) and handed to
`FourDistinct.slowest_of_four_never_returns_lap`.  The lap condition is REQUIRED for this proof (without it the
statement is false: `FourDistinct.slowest_of_four_can_return`, `a` sets at laps 9 and 10 in
`experiments/n8/ladder_scale_v1.out` section 5). -/
theorem min_sets_once {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (ha : ∀ d ∈ E, a ≤ d) {n n' : ℕ}
    (hn : IsSetterAt E seq n a) (hn' : IsSetterAt E seq n' a) (hnn' : n < n')
    (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) : False := by
  have hex : ∃ k, n < k ∧ InWay a (seq k) := ⟨n', hnn', hn'.2.1⟩
  have hk := Nat.find_spec hex
  have hmin : ∀ s, n < s → s < Nat.find hex → ¬ InWay a (seq s) :=
    fun s h1 h2 h => Nat.find_min hex h2 ⟨h1, h⟩
  exact slowest_of_four_never_returns_lap hpos h0 hmv hcard ha hn hk.1 hmin hj hk.2

#print axioms min_sets_once

/-- **The lap condition**, about the cascade object itself: whenever the slowest reading `a` sets at a move `n ≤ 7` all of
whose predecessors have setters, its lap there is at most 8 or equal to 10.  This is the hypothesis of
`FourDistinct.four_distinct_of_lap`, read at the settings that the window lemma can produce; it is not a ceiling on the
readings (`lapCond_of_ratio` derives it from one). -/
-- STANDING: DEFINITION
def LapCond (E : Finset ℝ) (seq : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 7 → (∀ s, s < n → ∃ y, IsSetterAt E seq s y) → IsSetterAt E seq n a →
    lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10

/-- **The cascade over at most four readings is fixed within fifteen moves, when the lap condition holds** [L].
`E.card ≤ 4`, `a` its least member; under `LapCond`, there is `N ≤ 15` at which nobody is in the way, and every move
before `N` has a setter.  Why: the first eight moves, if none is fixed, contain a setting of `a` (`window_has_setter`),
at some `n ≤ 7`; `a` sets only once (`min_sets_once`); the eight moves `n+1, …, n+8`, if none is fixed, would contain a
second setting.  `[PROVISIONAL: counting tool]` for the number fifteen (seven moves, `a`, seven moves); it is an OUTPUT of
the laws, used inside `reach_four_of_lap`, and is not offered as a bound on where a lonely instant lies. -/
theorem four_cascade_fixes {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E) (ha : ∀ d ∈ E, a ≤ d)
    (hlap : LapCond E seq a) :
    ∃ N, N ≤ 15 ∧ (∀ d ∈ E, ¬ InWay d (seq N)) ∧ ∀ s, s < N → ∃ y, IsSetterAt E seq s y := by
  have hex15 : ∃ N, N ≤ 15 ∧ ∀ d ∈ E, ¬ InWay d (seq N) := by
    by_contra hcon
    push Not at hcon
    have hset : ∀ i, i ≤ 15 → ∃ x, IsSetterAt E seq i x := fun i hi =>
      exists_setter hmv (fun hall => by
        obtain ⟨d, hd, hdw⟩ := hcon i hi
        exact hall d hd hdw)
    obtain ⟨n, hn0, hn7, hna⟩ :=
      window_has_setter hpos h0 hmv hcard haE (s := 0) (fun i h1 h2 => hset i (by omega))
    have hj := hlap n (by omega) (fun s hs => hset s (by omega)) hna
    obtain ⟨n', hn'1, hn'2, hn'a⟩ :=
      window_has_setter hpos h0 hmv hcard haE (s := n + 1) (fun i h1 h2 => hset i (by omega))
    exact min_sets_once hpos h0 hmv hcard ha hna hn'a (by omega) hj
  obtain ⟨N0, hN0, hN0f⟩ := hex15
  have hex : ∃ N, ∀ d ∈ E, ¬ InWay d (seq N) := ⟨N0, hN0f⟩
  refine ⟨Nat.find hex, (Nat.find_min' hex hN0f).trans hN0, Nat.find_spec hex, fun s hs => ?_⟩
  have hmin := Nat.find_min hex hs
  exact exists_setter hmv hmin

#print axioms four_cascade_fixes

/-! ## (3) The lap condition from the quotient, the position law, and five disparities -/

/-- **The lap condition from a ceiling on the quotient** [L].  For `0 < a < 57 m`, the slowest reading `a` of the cascade
from `1/(8m)` satisfies `LapCond`: a setting at a move `n ≤ 7` whose predecessors have setters is at an instant at most
`1/(8m) + n/(4a)` (`elapsed_le`), so `a · seq n ≤ ρ/8 + 7/4 < 71/8` and the lap is at most eight
(`FourDistinct.lap_le_eight_of_lt`).  The ceiling `57` is what THIS argument gives, it is not the boundary of the lap
condition: the exact range of the lap against the quotient is `lap_range` (`ρ ≥ 65` forces a lap `≥ 9`; `57 ≤ ρ < 65`
is undecided by these two inequalities).  Hypotheses: `a < 57 m` is REQUIRED for this proof (at `ρ ≥ 65` the lap is `≥ 9`
and `lap = 9` is attained, `not_lapCond_CE`). `[PROVISIONAL: counting tool]` at this step, supporting the position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this bound) shows where it lands. The ceiling is a tool for the lap, not a cap offered as a result. -/
theorem lapCond_of_ratio {E : Finset ℝ} {seq : ℕ → ℝ} {m a : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d)
    (ha0 : 0 < a) (ham : ∀ d ∈ E, a ≤ d) (h0 : seq 0 = 1 / (8 * m)) (h57 : a < 57 * m) : LapCond E seq a := by
  intro n hn7 hpre hna
  have hel := elapsed_le hpos ha0 ham n hpre
  refine Or.inl (lap_le_eight_of_lt hna.2.1 ?_)
  have h1 : a * seq n ≤ a * (seq 0 + (n : ℝ) / (4 * a)) := mul_le_mul_of_nonneg_left hel ha0.le
  have h2 : a * (seq 0 + (n : ℝ) / (4 * a)) = a / (8 * m) + (n : ℝ) / 4 := by
    rw [h0]; field_simp
  have h3 : a / (8 * m) < 57 / 8 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hn : (n : ℝ) ≤ 7 := by exact_mod_cast hn7
  linarith

#print axioms lapCond_of_ratio

/-- **A quotient of at least 65 forces a lap of at least 9** [L]: the other side of the relation `lap_range`.  So the lap
condition `lap ≤ 8` can hold at a setting only if `ρ < 65`; for `ρ ≥ 65` the true law of FourDistinct is not available at that
setting (`lap = 10` needs `ρ < 81`; `lap = 9` and `lap ≥ 11` are outside the condition). -/
theorem nine_le_lap_of_ratio {m y t : ℝ} (hm : 0 < m) (ht : 1 / (8 * m) ≤ t) (hy : 0 ≤ y) (hw : InWay y t)
    (h65 : 65 ≤ y / m) : 9 ≤ lap y t := by
  have h := (lap_range (B := t * (8 * m)) hm hy ht (by rw [mul_div_cancel_right₀ _ (by positivity)])
    hw).1
  have : (8 : ℝ) < (lap y t : ℝ) := by linarith
  have h8 : (8 : ℤ) < lap y t := by exact_mod_cast this
  omega

#print axioms nine_le_lap_of_ratio

/-- **The position law** [L].  If the moves `0, …, N−1` of the cascade from `1/(8m)` all have setters and every member of
`E` is at least `a > 0`, then `8 m · seq N ≤ 1 + 2 N m / a`: in the coordinate `R = 8 m t`, `R_N ≤ 1 + 2 N/ρ`.  It is the
additive time law in the record's coordinate.  `[PROVISIONAL: counting tool]`: the number of moves `N` is used as a tool
that bounds the elapsed time; it supports the statement 'the instant lies in the first window' (`lonely_window_of_moves`)
and nothing else. -/
theorem position_of_moves {E : Finset ℝ} {seq : ℕ → ℝ} {m a : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d) (ha0 : 0 < a)
    (ham : ∀ d ∈ E, a ≤ d) (h0 : seq 0 = 1 / (8 * m)) (N : ℕ) (hset : ∀ s, s < N → ∃ y, IsSetterAt E seq s y) :
    8 * m * seq N ≤ 1 + 2 * (N : ℝ) * m / a := by
  have hel := elapsed_le hpos ha0 ham N hset
  have h1 : 8 * m * seq N ≤ 8 * m * (seq 0 + (N : ℝ) / (4 * a)) := mul_le_mul_of_nonneg_left hel (by positivity)
  have h2 : 8 * m * (seq 0 + (N : ℝ) / (4 * a)) = 1 + 2 * (N : ℝ) * m / a := by
    rw [h0]; field_simp; ring
  linarith

#print axioms position_of_moves

/-- **A fixed point after `N` moves with `N m ≤ 3 a` lies in the first window `R ∈ [1, 7]`** [L].  No cardinality
hypothesis on `E`.  `[PROVISIONAL: counting tool]` as `position_of_moves`.  This is the exact form of what is missing for
five or more readings: a bound `N m ≤ 3 a` on the number of non-fixed moves against the quotient of the slowest reading. -/
theorem lonely_window_of_moves {E : Finset ℝ} {seq : ℕ → ℝ} {m a : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d)
    (ha0 : 0 < a) (ham : ∀ d ∈ E, a ≤ d) (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1)))
    {N : ℕ} (hfix : ∀ d ∈ E, ¬ InWay d (seq N)) (hset : ∀ s, s < N → ∃ y, IsSetterAt E seq s y)
    (hN : (N : ℝ) * m ≤ 3 * a) :
    1 / (8 * m) ≤ seq N ∧ seq N ≤ 7 / (8 * m) ∧ LonelyAt E (seq N) := by
  refine ⟨h0 ▸ start_le_seq hpos hmv N, ?_, lonely_of_notInWay hfix⟩
  have h := position_of_moves hm hpos ha0 ham h0 N hset
  have h1 : 2 * (N : ℝ) * m / a ≤ 6 := by
    rw [div_le_iff₀ ha0]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

#print axioms lonely_window_of_moves

/-- **Four readings in the first window, with the lap condition as the hypothesis** [L].  `E` has at most four members,
all at least `m > 0`, `a` is the least and `5 m ≤ a`, and the cascade from `1/(8m)` satisfies the lap condition at the
settings of `a`.  Then `E` has a lonely instant in `[1/(8m), 7/(8m)]` (`R ∈ [1, 7]`).  Proof: `four_cascade_fixes` gives
a fixed point after at most fifteen moves, and `15 m ≤ 3 a` is `5 m ≤ a` (`lonely_window_of_moves`).
`[PROVISIONAL: counting tool]` (the fifteen).  Hypotheses: `LapCond` REQUIRED for the proof (`min_sets_once`); `5 m ≤ a`
REQUIRED for the proof (it turns fifteen moves into the first window), NOT shown required for the statement
(`experiments/n8/ladder_scale_v1.out` section 1-4: no grid set with `a < 5 m` has `R > 7`); `E.card ≤ 4` REQUIRED for the
proof (`window_has_setter`). `[PROVISIONAL: counting tool]` at this step, supporting the position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this bound) shows where it lands. -/
theorem reach_four_of_lap {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (h5 : 5 * m ≤ a)
    (hlap : LapCond E (cascadeSeq E (1 / (8 * m))) a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt E s := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ha0 : 0 < a := hpos a haE
  have h0 : cascadeSeq E (1 / (8 * m)) 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < cascadeSeq E (1 / (8 * m)) 0 := by rw [h0]; positivity
  have hmv := cascadeSeq_isMove E (1 / (8 * m))
  obtain ⟨N, hN15, hfix, hset⟩ := four_cascade_fixes hpos h0pos hmv hcard haE ham hlap
  have hN : (N : ℝ) * m ≤ 3 * a := by
    have : (N : ℝ) ≤ 15 := by exact_mod_cast hN15
    nlinarith
  obtain ⟨h1, h2, h3⟩ := lonely_window_of_moves hm hpos ha0 ham h0 hmv hfix hset hN
  exact ⟨_, h1, h2, h3⟩

#print axioms reach_four_of_lap

/-- **Four readings in the first window, slowest quotient in `[5, 57)`** [L]: `reach_four_of_lap` with the lap condition
derived from the ceiling `a < 57 m` (`lapCond_of_ratio`).  The ceiling is not the hypothesis of the true law; the lap
condition is. -/
theorem reach_four_of_ratio {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (h5 : 5 * m ≤ a) (h57 : a < 57 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt E s := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  exact reach_four_of_lap hm hlow hcard haE ham h5
    (lapCond_of_ratio hm hpos (hpos a haE) ham (cascadeSeq_zero E _) h57)

#print axioms reach_four_of_ratio

/-- **From the readings other than `d_min` to the whole set** [L]: if `E = ds.erase m` has a lonely instant in
`[1/(8m), 7/(8m)]` then so does `ds` (`d_min` reads in `[1/8, 7/8]` there: `Gate.dmin_clear_first_window`).  The same step
as `Ladder.ladder_step`, here for a given `E`. -/
theorem add_dmin {ds : Finset ℝ} {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (h : ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt (ds.erase m) s) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  obtain ⟨s, hs1, hs2, hsl⟩ := h
  refine ⟨s, hs1, hs2, fun d hd => ?_⟩
  by_cases hdm : d = m
  · subst hdm
    exact Gate.dmin_clear_first_window hm0 hs1 hs2
  · exact hsl d (Finset.mem_erase.mpr ⟨hdm, hd⟩)

#print axioms add_dmin

/-- **Five disparities, second smallest in `[5 d_min, 57 d_min)`** [L].  `ds` has at most five members, least element `m`;
`a` is the least of the other four, `5 m ≤ a < 57 m`.  Then `ds` has a lonely instant in `R ∈ [1, 7]`.  The four larger
readings are arbitrary (no ceiling on them, no commensurability).  `[PROVISIONAL: counting tool]` as `reach_four_of_lap`.
This is `Ladder.five_disparities_of_reach_four` restricted to a range of the quotient, proved without `Reach 4`. `[PROVISIONAL: counting tool]` at this step, supporting the position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this bound) shows where it lands. -/
theorem five_disparities_of_ratio {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h5 : 5 * m ≤ a)
    (h57 : a < 57 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  have hc : (ds.erase m).card ≤ 4 := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  exact add_dmin hm hm0 (reach_four_of_ratio hm0 hlow hc haE ham h5 h57)

#print axioms five_disparities_of_ratio

/-- The same with the lap condition as the hypothesis (no ceiling on the quotient). -/
theorem five_disparities_of_lap {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h5 : 5 * m ≤ a)
    (hlap : LapCond (ds.erase m) (cascadeSeq (ds.erase m) (1 / (8 * m))) a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  have hc : (ds.erase m).card ≤ 4 := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  exact add_dmin hm hm0 (reach_four_of_lap hm0 hlow hc haE ham h5 hlap)

#print axioms five_disparities_of_lap

/-- **The lap condition fails for the exact example of FourDistinct** [L]: `CE` with `a = 1` set at move `0` on lap `9`.
So the hypothesis `LapCond` of `four_cascade_fixes` is not a vacuous restatement: it is false for `CE`, at the quotient
`875/12`.  (The conclusion of `four_cascade_fixes` happens to hold for `CE`: it is fixed after six moves; `min_sets_once`
is the lemma that is false there, `slowest_of_four_can_return`.) -/
theorem not_lapCond_CE : ¬ LapCond CE ceSeq 1 := by
  intro h
  have hl : lap 1 (ceSeq 0) = 9 := by
    refine lap_eq_of_near (k := 9) ?_
    simp only [ceSeq]; rw [abs_lt]; constructor <;> norm_num
  have := h 0 (by norm_num) (fun s hs => absurd hs (Nat.not_lt_zero s)) ce_setter0
  rw [hl] at this
  omega

#print axioms not_lapCond_CE

/-! ## (4) Six disparities and the large-quotient regime: what the laws give, and what is missing

**Six disparities (five readings besides `d_min`).**  Three facts are proved.  (i) The position law needs no cardinality
(`lonely_window_of_moves`, `disparities_of_moves`): a fixed point after `N` moves with `N m ≤ 3 a` is in the first window.
(ii) At a first return of the slowest reading `a`, set on a lap satisfying the lap condition, the intermediate setters are
exactly the other four readings and their budget exceeds three (`five_return_shape`): `a` returns only through every other
reading.  (iii) The window lemma `window_has_setter` is a statement about at most four readings; with five, `E.erase a`
has four readings and `block_four_false'` no longer closes (three values can alternate), so the eight-window is not forced
to contain `a` by these laws.  What is missing is a law bounding the number of settings of `a`, or equivalently a bound
`N m ≤ 3 a` on the number of non-fixed moves against the quotient.  The budget laws are necessary and not sufficient for
a return (the AY/BA findings, exact data in `ladder5_v2.out`, `ladder_cap_word_*`); a law of position is not formalised here.

**Large quotient.**  The lap condition fails at quotient `≥ 65` (`nine_le_lap_of_ratio`), and `FourDistinct` shows the
failure is real (`not_lapCond_CE`: lap 9, `a` returns).  The exact reduction available is the position law above, which
holds at every quotient: if the number of non-fixed moves is at most `3 ρ`, the lonely instant is in the first window.
The scale-separation lemma `fine_reading_survives` (a lonely interval of `S` of length `≥ 1/(4x)` survives the insertion of
`x`) is the large-quotient statement for the finest reading; the cascade does not supply the interval.  The interval's
length is the phase problem of `ScaleHierarchy` (`touch_cell_not_long`: cells of length zero occur), not a scale problem. -/

/-- **The position law for any set, any number of readings** [L].  `ds` has least element `m > 0`; `E = ds.erase m`, `a` is the
least of `E`; the cascade over `E` from `1/(8m)` is fixed at `N` after `N` moves, `N m ≤ 3 a`.  Then `ds` has a lonely
instant in `R ∈ [1, 7]`.  `[PROVISIONAL: counting tool]` as `position_of_moves`.  This is the six-disparity (and any
larger) reduction: the bound on `N` is the missing law. `[PROVISIONAL: counting tool]` at this step, supporting the position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this bound) shows where it lands. -/
theorem disparities_of_moves {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (ha0 : 0 < a) (ham : ∀ d ∈ ds.erase m, a ≤ d) (hlow : ∀ d ∈ ds.erase m, m ≤ d) {N : ℕ}
    (hfix : ∀ d ∈ ds.erase m, ¬ InWay d (cascadeSeq (ds.erase m) (1 / (8 * m)) N))
    (hset : ∀ s, s < N → ∃ y, IsSetterAt (ds.erase m) (cascadeSeq (ds.erase m) (1 / (8 * m))) s y)
    (hN : (N : ℝ) * m ≤ 3 * a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  have hpos : ∀ d ∈ ds.erase m, 0 < d := fun d hd => lt_of_lt_of_le hm0 (hlow d hd)
  obtain ⟨h1, h2, h3⟩ := lonely_window_of_moves hm0 hpos ha0 ham (cascadeSeq_zero _ _)
    (cascadeSeq_isMove (ds.erase m) (1 / (8 * m))) hfix hset hN
  exact add_dmin hm hm0 ⟨_, h1, h2, h3⟩

#print axioms disparities_of_moves

/-- **The shape of a first return of the slowest of five readings** [L].  `E` has at most five members, `a` is the least,
sets at `n` on a lap satisfying the lap condition and is in the way again at `k` for the first time.  Then the setters of the
moves in between are exactly the other readings `E.erase a`, and their budget exceeds three: `3 < ∑ a / w s`.  (Combines
`FourDistinct.five_first_return_all_others_lap` and `Ladder5.budget_sum`.)  The budget is a necessary condition describing
what a return requires `[PROVISIONAL: covering]`; it supports the chain account of the return and is not an existence
argument. -/
theorem five_return_shape {E : Finset ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ i, IsMove E (seq i) (seq (i + 1))) (hcard : E.card ≤ 5) (ha : ∀ d ∈ E, a ≤ d)
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s))
    (hw : InWay a (seq k)) (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    (Finset.Ico (n + 1) k).image w = E.erase a ∧ 3 < ∑ s ∈ Finset.Ico (n + 1) k, a / w s :=
  ⟨five_first_return_all_others_lap hpos h0 hmv hcard ha hn hnk hfirst hw hj hws,
    budget_sum hpos hmv hnk hn hw w hws⟩

#print axioms five_return_shape

/-- **Scale separation for the finest reading** [L].  If `S` has a lonely interval `[u, w]` of length at least `1/(4x)` (a
zone width of `x`), then `insert x S` has a lonely instant in `[u, w]`.  `[PROVISIONAL: covering]`, a cell length against a
zone width (`DispCell.long_cell_survives`); it supports the survival of a cell under an added reading and no existence
claim for the cascade.  Hypotheses: `0 < x` REQUIRED (`DispCell.exists_iff_fails_zero`); the interval must lie in the lonely
set of `S` (a cell). -/
theorem fine_reading_survives {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x)
    (hsub : Set.Icc u w ⊆ Fresh.LonelyCells.lonelySet S) (h : 1 / (4 * x) ≤ w - u) :
    ∃ s, u ≤ s ∧ s ≤ w ∧ LonelyAt (insert x S) s := by
  obtain ⟨-, s, hs, hl⟩ := Fresh.DispCell.long_cell_survives hx hsub h
  exact ⟨s, hs.1, hs.2, hl⟩

#print axioms fine_reading_survives

/-- The statement owed for six disparities in the quotient-bounded regime: seven runners, the second smallest disparity
below `57 d_min`.  It is a consequence of `Ladder.SixDisparitiesLonely` (OWED there) and is not proved here. -/
-- STANDING: OWED
def SixDisparitiesQuotientBounded : Prop :=
  ∀ (ds : Finset ℝ) (m a : ℝ), IsLeast (ds : Set ℝ) m → 0 < m → ds.card ≤ 6 → a ∈ ds.erase m →
    (∀ d ∈ ds.erase m, a ≤ d) → a < 57 * m → ∃ s, 0 < s ∧ LonelyAt ds s

/-- The same for five disparities with the slowest quotient below `5`: the part of the five-disparity statement that
`five_disparities_of_ratio` does not reach.  Equivalent to `Reach 4 7` on the sets with `a < 5 m`; not proved here. -/
-- STANDING: OWED
def FiveDisparitiesLowQuotient : Prop :=
  ∀ (ds : Finset ℝ) (m a : ℝ), IsLeast (ds : Set ℝ) m → 0 < m → ds.card ≤ 5 → a ∈ ds.erase m →
    (∀ d ∈ ds.erase m, a ≤ d) → a < 5 * m → ∃ s, 0 < s ∧ LonelyAt ds s

/-- The two ranges together are `Ladder.FiveDisparitiesLonely` restricted to `a < 57 m`; with `FiveDisparitiesLowQuotient`
OWED and `five_disparities_of_ratio` proved, what remains of the quotient-bounded five-disparity statement is exactly the
low-quotient part. -/
theorem five_quotient_bounded_of_low (h : FiveDisparitiesLowQuotient) :
    ∀ (ds : Finset ℝ) (m a : ℝ), IsLeast (ds : Set ℝ) m → 0 < m → ds.card ≤ 5 → a ∈ ds.erase m →
      (∀ d ∈ ds.erase m, a ≤ d) → a < 57 * m → ∃ s, 0 < s ∧ LonelyAt ds s := by
  intro ds m a hm hm0 hcard haE ham h57
  by_cases h5 : 5 * m ≤ a
  · obtain ⟨s, hs1, -, hsl⟩ := five_disparities_of_ratio hm hm0 hcard haE ham h5 h57
    exact ⟨s, lt_of_lt_of_le (by positivity) hs1, hsl⟩
  · exact h ds m a hm hm0 hcard haE ham (not_le.mp h5)

#print axioms five_quotient_bounded_of_low

end LadderScale

end Fresh
