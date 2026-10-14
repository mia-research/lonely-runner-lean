import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.FiveReach
import Fresh.Ladder
import Fresh.Ladder5
import Fresh.FourDistinct
import Fresh.LadderScale
import Fresh.LawOfPosition

/-!
# Six disparities (the unit plus five readings): the chain laws that extend, and the exact residual (Task CC)

Written 2026-10-10.  Imports `Mathlib` and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is stationary); no floats.
Data (exact integer cascade, explicit grids, every count is an observation of those grids only): `experiments/n8/six_v1.py/.out`.

Setting.  `E` is a finite set of at most five readings, all at least `m > 0`, `a = min E`; the cascade runs from `1/(8m)`
(`R = 8 m t = 1`).  `ds = insert m E` is the set of six disparities (`d_min = m` plus five readings).  What is owed
(`Ladder.SixDisparitiesLonely`, `FiveReach`): a lonely instant of `ds` in `R ∈ [1, 7]`.  It follows (`LadderScale.add_dmin`) from a
lonely instant of `E` in `[1, 7]`, and the position law (`LadderScale.lonely_window_of_moves`) turns a bound on the number of
non-fixed moves, `N m ≤ 3 a`, into one.

## What is proved here (grades [L]; each theorem has its `#print axioms` line)

* (1) `eight_four_distinct`, `eight_not_three`: **any eight consecutive non-fixed moves of any cascade have at least four distinct
  setter values.**  No cardinality of `E`, no ordering of the readings, no base `m`, no lap condition.  It generalises
  `LadderScale.window_has_setter` (the case `E.card ≤ 4`, recovered as `window_has_setter_of_eight`) from "every member of a
  four-set sets in every eight-window" to "an eight-window misses at most `E.card - 4` members".  At five readings:
  `five_window_misses_at_most_one`, and `a_free_window_all_others` (an eight-window without `a` contains each of the other four).
  The value four is attained on the exact grids ([OBS], `six_v1.out`).  `budget_admits_word7`: the additive budget alone admits a
  word of length seven on three letters (`r q r p r q r`, exact readings), so eight is the limit of THIS proof.
  `[PROVISIONAL: counting tool]` in the pigeonhole of the five blocks and in the two-letter step (it supports "an eight-window has
  four values" and no existence claim; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is
  displaced by the setters, and the cascade shows where it lands).
* (2) `elapsed_two_sided`, `elapsed_upper`, `elapsed_lower`: the elapsed time of a chain is two-sided in the weights of its
  setters: `∑_{s=1}^{N-1} 1/(4 w_s) ≤ 2 (seq N - seq 0)` and `seq N - seq 0 ≤ ∑_{s=0}^{N-1} 1/(4 w_s)`.  In the coordinate
  `R = 8 m t` with the weight `W = ∑ m / w_s`: `W' ≤ R_N - 1 ≤ 2 W` (`W'` omits the first setter).  `lonely_window_of_weight`:
  a total setter weight `W ≤ 3` puts the fixed point in the first window `R ∈ [1, 7]`; `weight_le_moves`: `N m ≤ 3 a` implies
  `W ≤ 3`, so this reduction is STRONGER than `LadderScale.disparities_of_moves` (which it contains).
  `[PROVISIONAL: counting tool]` (a sum over the moves), supporting the position of the fixed point only.
* (2b) `final_gap_identity`, `return_gap_identity`: **the exact forms.**  `8 m · seq N = 1 + ∑_{s<N} gap_s · (m / w_s)` (each gap in `(0, 2)`),
  and, for a reading `x` set at `n` and in the way at `seq k`: `∑_{s=n+1}^{k-1} gap_s · (x / w_s) + gap x (seq k) = 8 (lap_k - lap_n)`: the lap of a
  reading is consumed exactly by the gaps of the moves between its visits.  Both budget halves are corollaries of it with the bounds on the gaps.
  `landing_in_window_iff`: the final landing is the opening of its last setter, so `R ≤ 7` is the lap bound `8 j + 1 ≤ 7 z / m` on that setter
  (a restatement, not a bound).
* (3) `return_upper_budget`: **the budget of a return is two-sided**: with `Δj = lap_k - lap_n ≥ 1`,
  `4 Δj - 1 < ∑_{s=n+1}^{k-1} x / w_s < 8 Δj + 1` (the lower half is `LawOfPosition.lap_budget`; the upper half is new and uses
  `LawOfPosition.two_step_lower`).
* (3b) `settings_weight_bound`: **the number of settings of a reading is an output of the weight**: `4 · |settings of x| < (x/m) · W + 5`, `W = ∑ m / w_s` the total
  setter weight.  No lap condition.  It is the reason the count of settings of the slowest has no bound from the laws alone (the exact AP family, section 6).
* (4) `settings_le_nine`, `slowest_settings_le_nine`: **the number of settings of a reading on laps in `{1,…,8} ∪ {10}` is at most nine**
  (an OUTPUT of the strict increase of the lap, `ChainLaws.setter_recur_lap`; no move bound is assumed).
  `three_settings_of_slowest` [L]: an exact five-reading cascade (`E3 = {40, 83/2, 43, 89/2, 46}`, `m = 1`, thirteen moves) in which
  the slowest reading is the setter at moves `0, 5, 11` on laps `5, 6, 7`, so the count on the allowed laps is at least three; the
  exact AP family of `six_v1.out` section 6 has more settings (28 at `a = 640`), on laps past ten.  `[PROVISIONAL: counting tool]`:
  injection of the settings into the lap set, supporting the count of settings only.
* (5) `moves_le_of_lap_all`, `six_dichotomy`: **for `15 m ≤ a` (the least of the five readings), either some setter among the first
  forty-six moves is on lap `9` or on a lap `≥ 11`, or `ds` has a lonely instant in `R ∈ [1, 7]`.**  A dichotomy, not an existence theorem:
  the exceptional branch is not excluded (it occurs on the exact grid `Q = 2, M = 60`: 96,426 of 46,504,458 sets with `a ≥ 15`).
  `[PROVISIONAL: counting tool]` (five readings, nine settings each).
* (6) The reduction `six_disparities_of_chain_weight` and the statement left OWED, `FiveChainWeight` (total setter weight at most three).

## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED), each by trying to drop it

| hypothesis | status |
|---|---|
| `0 < seq 0`, positivity of `E` in `eight_four_distinct` | REQUIRED for the proof (`triple_law` uses the laps of later settings; the budget divides by the readings); necessity for the statement UNDECIDED |
| ordering of readings, base `m`, `seq 0 = 1/(8m)`, `E.card` in `eight_four_distinct` | NOT REQUIRED (not used) |
| that a SETTER is supplied at each of the eight moves | REQUIRED (a fixed move has no setter; the statement is about non-fixed moves) |
| the window length `8` | REQUIRED FOR THE PROOF (`budget_admits_word7`: a seven-letter word on three letters passes every budget inequality).  For the STATEMENT: UNDECIDED; the longest run of consecutive moves with at most three values is five on the grids Q = 12, 8, 4, 3, 1, 6 and six on Q = 2, M = 60 (set 10 15 36 40 114, `six_v1.out` section 1, RUN3); none of length seven, and a float-steered search of three-reading cascades with free start finds no realisation of any three-letter word of length six or seven (setter laps up to 12, readings up to 60) |
| `E.card ≤ 5` in `five_window_misses_at_most_one`, `a_free_window_all_others` | REQUIRED (the count of misses is `E.card - 4`) |
| `Δj ≥ 1` (two settings/visits on different laps) in `return_upper_budget` | REQUIRED for the form `8 Δj + 1` (the proof uses the laps of the two ends); the lap order is `LawOfPosition.lap_diff_pos` |
| lap condition (`j ∈ {1,…,8,10}`) in `settings_le_nine` | REQUIRED for the count nine (without it the lap set is infinite and no count follows from the laws; the exact AP family has 28 settings at `a = 640`) |
| `1 ≤ lap` in `settings_le_nine` | REQUIRED for the count nine (with lap `0` allowed the set has ten values); holds at every setting of a reading `≥ m` from `1/(8m)` (`Dilation.one_le_lap_of_bound`) |
| `15 m ≤ a` in `six_dichotomy` | REQUIRED FOR THE PROOF (`5 · 9 = 45` moves against `3 a`); necessity for the statement UNDECIDED (no violation of `N m ≤ 3 a` among the exact sets with `a ≥ 5`, `six_v1.out`) |
| `a ∈ ds.erase m` in `six_dichotomy` | NOT REQUIRED (dropped: `ham` and `15 m ≤ a` are all the proof uses) |
| the weight bound `3` in `lonely_window_of_weight` | REQUIRED for the form `7/(8m)` (`seq N - seq 0 ≤ W/(4 m)`); the exact grids have `W ≤ 21608934/10200085` |
| `0 < m`, `seq 0 = 1/(8 m)` in `lonely_window_of_weight` | REQUIRED (division by `m`; the start is where the elapsed time is measured) |

Provenance (existing declarations whose argument was read and understood, nothing copied): `Ladder.reach_three_cascade`
and `LadderScale.window_has_setter` (the block-of-four argument), `Ladder5.return_after_four`, `Ladder5.budget_sum`,
`Ladder5.sum_incr`, `LawOfPosition.two_step_lower`, `ChainLaws.setter_recur_lap`, `LadderScale.lonely_window_of_moves`,
`LadderScale.disparities_of_moves`, `FourDistinct.isMove_of_single` (the shape of the table lemma `isMove_of_table`).
-/

open Classical

namespace Fresh

namespace SixDisparities

open Cascade Dilation ChainLaws FiveReachStudy Ladder Ladder5 FourDistinct LadderScale LawOfPosition

/-! ## (1) Eight consecutive moves have four distinct setters -/

/-- **Eight consecutive non-fixed moves have at least four distinct setter values** [L].  `w i` is a setter of the move
at `i` for `s ≤ i ≤ s + 7`.  Proof: if the values lay in a set `T` of at most three, the least `b ∈ T` is set at most twice
in the window (two settings are five moves apart: the budget `3 < ∑ b / w`, each term at most `1`, so four terms), hence some
four consecutive moves avoid `b`; their values lie in `T.erase b` (at most two letters), never repeat in a row
(`setter_not_twice_in_row`), so alternate `x y x y`, which `no_xyxy` forbids.  The proof never asks the setters in the window to
be the ONLY setters of the moves: ties are harmless because the budget is applied to the chosen `w`.
`[PROVISIONAL: counting tool]`: the pigeonhole of five blocks (`omega`) and `eq_of_card_le_two`, supporting this statement only. -/
theorem eight_four_distinct {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {s : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i, s ≤ i → i ≤ s + 7 → IsSetterAt E seq i (w i)) :
    3 < ((Finset.Icc s (s + 7)).image w).card := by
  by_contra hcon
  push Not at hcon
  set T : Finset ℝ := (Finset.Icc s (s + 7)).image w with hT
  have hmemT : ∀ i, s ≤ i → i ≤ s + 7 → w i ∈ T := fun i h1 h2 =>
    Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩
  have hTne : T.Nonempty := ⟨w s, hmemT s le_rfl (by omega)⟩
  obtain ⟨b, hb⟩ := exists_isLeast hTne
  have hwpos : ∀ i, s ≤ i → i ≤ s + 7 → 0 < w i := fun i h1 h2 => hpos _ (hw i h1 h2).1
  -- two settings of `b` inside the window are at least five moves apart (budget law, chosen setters)
  have hS5 : ∀ i j, s ≤ i → j ≤ s + 7 → w i = b → w j = b → i < j → i + 5 ≤ j := by
    intro i j hi hj hwi hwj hij
    have hbi : IsSetterAt E seq i b := by have := hw i hi (by omega); rwa [hwi] at this
    have hbj : InWay b (seq j) := by have := (hw j (by omega) hj).2.1; rwa [hwj] at this
    have hsum := budget_sum hpos hmv hij hbi hbj w
      (fun t ht1 ht2 => hw t (by omega) (by omega))
    have hterm : ∀ t ∈ Finset.Ico (i + 1) j, b / w t ≤ 1 := by
      intro t ht
      have ht' := Finset.mem_Ico.mp ht
      have hp := hwpos t (by omega) (by omega)
      rw [div_le_one hp]
      exact hb.2 (hmemT t (by omega) (by omega))
    have hle := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Nat.card_Ico] at hle
    simp only [nsmul_eq_mul, mul_one] at hle
    have h3 : (3 : ℝ) < ((j - (i + 1) : ℕ) : ℝ) := by linarith
    have h3' : 3 < j - (i + 1) := by exact_mod_cast h3
    omega
  -- some block of four consecutive moves has no setting of `b`
  have hwin : ∃ t, s ≤ t ∧ t ≤ s + 4 ∧ ∀ i, t ≤ i → i ≤ t + 3 → w i ≠ b := by
    by_contra hcon2
    push Not at hcon2
    obtain ⟨i0, h0a, h0b, h0c⟩ := hcon2 s le_rfl (by omega)
    obtain ⟨i1, h1a, h1b, h1c⟩ := hcon2 (s + 1) (by omega) (by omega)
    obtain ⟨i2, h2a, h2b, h2c⟩ := hcon2 (s + 2) (by omega) (by omega)
    obtain ⟨i3, h3a, h3b, h3c⟩ := hcon2 (s + 3) (by omega) (by omega)
    obtain ⟨i4, h4a, h4b, h4c⟩ := hcon2 (s + 4) (by omega) (by omega)
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
  have hE2 : (T.erase b).card ≤ 2 := by
    have := Finset.card_erase_of_mem hb.1
    omega
  have hmem : ∀ i, t ≤ i → i ≤ t + 3 → w i ∈ T.erase b :=
    fun i h1 h2 => Finset.mem_erase.mpr ⟨htb i h1 h2, hmemT i (by omega) (by omega)⟩
  have hne : ∀ i, t ≤ i → i + 1 ≤ t + 3 → w (i + 1) ≠ w i := by
    intro i h1 h2 heq
    exact setter_not_twice_in_row hpos (hw i (by omega) (by omega)) (heq ▸ hw (i + 1) (by omega) (by omega))
  have e02 : w t = w (t + 2) :=
    eq_of_card_le_two hE2 (hmem t le_rfl (by omega)) (hmem (t + 1) (by omega) (by omega))
      (hmem (t + 2) (by omega) (by omega))
      (Ne.symm (hne t le_rfl (by omega))) (Ne.symm (hne (t + 1) (by omega) (by omega)))
  have e13 : w (t + 1) = w (t + 3) :=
    eq_of_card_le_two hE2 (hmem (t + 1) (by omega) (by omega)) (hmem (t + 2) (by omega) (by omega))
      (hmem (t + 3) (by omega) (by omega))
      (Ne.symm (hne (t + 1) (by omega) (by omega))) (Ne.symm (hne (t + 2) (by omega) (by omega)))
  exact no_xyxy hpos h0 hmv (hw t (by omega) (by omega)) (hw (t + 1) (by omega) (by omega))
    (e02 ▸ hw (t + 2) (by omega) (by omega)) (e13 ▸ hw (t + 3) (by omega) (by omega))

#print axioms eight_four_distinct

/-- The same, as "no set of at most three readings contains the setters of eight consecutive moves" [L]. -/
theorem eight_not_three {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {s : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i, s ≤ i → i ≤ s + 7 → IsSetterAt E seq i (w i)) {T : Finset ℝ} (hT : T.card ≤ 3)
    (hin : ∀ i, s ≤ i → i ≤ s + 7 → w i ∈ T) : False := by
  have h4 := eight_four_distinct hpos h0 hmv hw
  have hsub : (Finset.Icc s (s + 7)).image w ⊆ T := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_Icc.mp hi
    exact hin i hi'.1 hi'.2
  have := Finset.card_le_card hsub
  omega

#print axioms eight_not_three

/-- **`LadderScale.window_has_setter` is a corollary** [L]: at most four readings, every member sets in every eight-window. -/
theorem window_has_setter_of_eight {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E) {s : ℕ}
    (hset : ∀ i, s ≤ i → i ≤ s + 7 → ∃ x, IsSetterAt E seq i x) :
    ∃ i, s ≤ i ∧ i ≤ s + 7 ∧ IsSetterAt E seq i a := by
  choose! w hw using hset
  have h4 := eight_four_distinct hpos h0 hmv hw
  have hsub : (Finset.Icc s (s + 7)).image w ⊆ E := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_Icc.mp hi
    exact (hw i hi'.1 hi'.2).1
  have heq : (Finset.Icc s (s + 7)).image w = E :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have ha : a ∈ (Finset.Icc s (s + 7)).image w := by rw [heq]; exact haE
  obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
  have hi' := Finset.mem_Icc.mp hi
  refine ⟨i, hi'.1, hi'.2, ?_⟩
  have := hw i hi'.1 hi'.2
  rwa [hia] at this

#print axioms window_has_setter_of_eight

/-- **Five readings: an eight-window misses at most one** [L]: the set of members of `E` that do not set in the window has at most
one element. -/
theorem five_window_misses_at_most_one {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 5) {s : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i, s ≤ i → i ≤ s + 7 → IsSetterAt E seq i (w i)) :
    (E \ (Finset.Icc s (s + 7)).image w).card ≤ 1 := by
  have h4 := eight_four_distinct hpos h0 hmv hw
  have hsub : (Finset.Icc s (s + 7)).image w ⊆ E := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_Icc.mp hi
    exact (hw i hi'.1 hi'.2).1
  rw [Finset.card_sdiff_of_subset hsub]
  omega

#print axioms five_window_misses_at_most_one

/-- **Five readings: an eight-window without a setting of `a` contains each of the other four** [L]: the set of its setter values is
exactly `E.erase a`. -/
theorem a_free_window_all_others {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 5) {a : ℝ} (haE : a ∈ E) {s : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i, s ≤ i → i ≤ s + 7 → IsSetterAt E seq i (w i))
    (hna : ∀ i, s ≤ i → i ≤ s + 7 → w i ≠ a) :
    (Finset.Icc s (s + 7)).image w = E.erase a := by
  have h4 := eight_four_distinct hpos h0 hmv hw
  have hsub : (Finset.Icc s (s + 7)).image w ⊆ E.erase a := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_erase.mpr ⟨hna i hi'.1 hi'.2, (hw i hi'.1 hi'.2).1⟩
  have hE : (E.erase a).card ≤ 4 := by
    have := Finset.card_erase_of_mem haE
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

#print axioms a_free_window_all_others

/-! ## (2) The elapsed time of a chain is two-sided in the weights of its setters -/

/-- **Elapsed time, upper half** [L]: `seq N - seq 0 ≤ ∑_{s<N} 1/(4 w_s)` (each move advances by less than `1/(4 w)`). -/
theorem elapsed_upper {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ s, s < N → IsSetterAt E seq s (w s)) :
    seq N - seq 0 ≤ ∑ s ∈ Finset.range N, 1 / (4 * w s) := by
  have h := sum_incr hpos 0 w N (by intro s _ h2; exact hw s (by omega))
  rw [zero_add, ← Finset.range_eq_Ico] at h
  simpa using h

#print axioms elapsed_upper

/-- **Elapsed time, lower half** [L]: the sum of `1/(4 w_s)` over `s = 1, …, M` is at most `seq (M+1) + seq M - seq 1 - seq 0`
(each setter's window has length `1/(4 w)` and was entered after the previous instant: `LawOfPosition.two_step_lower`).  The
first setter is omitted: its window may have been entered before the start.  `[PROVISIONAL: counting tool]` (a sum over the moves),
supporting `elapsed_two_sided` only. -/
theorem elapsed_lower {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (w : ℕ → ℝ) :
    ∀ M : ℕ, (∀ s, s < M + 1 → IsSetterAt E seq s (w s)) →
      ∑ s ∈ Finset.Ico 1 (M + 1), 1 / (4 * w s) ≤ seq (M + 1) + seq M - seq 1 - seq 0 := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hw
    have ih' := ih (fun s hs => hw s (by omega))
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ M + 1)]
    have hts := two_step_lower hpos hmv (s := M) (x := w (M + 1)) (hw (M + 1) (by omega))
    have e : seq (M + 2) = seq (M + 1 + 1) := rfl
    rw [e] at hts
    linarith

#print axioms elapsed_lower

/-- **Elapsed time is two-sided in the setter weights** [L]: for `N = M + 1` setters,
`∑_{s=1}^{M} 1/(4 w_s) ≤ 2 (seq N - seq 0)` and `seq N - seq 0 ≤ ∑_{s=0}^{M} 1/(4 w_s)`.  In `R = 8 m t` and the weight
`W = ∑ m / w_s` this is `W' ≤ R_N - 1 ≤ 2 W` (`W'` omits the first setter).  `[PROVISIONAL: counting tool]` (sums over moves). -/
theorem elapsed_two_sided {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (w : ℕ → ℝ) (M : ℕ)
    (hw : ∀ s, s < M + 1 → IsSetterAt E seq s (w s)) :
    ∑ s ∈ Finset.Ico 1 (M + 1), 1 / (4 * w s) ≤ 2 * (seq (M + 1) - seq 0) ∧
      seq (M + 1) - seq 0 ≤ ∑ s ∈ Finset.range (M + 1), 1 / (4 * w s) := by
  refine ⟨?_, elapsed_upper hpos (M + 1) w hw⟩
  have h := elapsed_lower hpos hmv w M hw
  have h1 : seq M ≤ seq (M + 1) := le_of_isMove hpos (hmv M)
  have h2 : seq 0 ≤ seq 1 := le_of_isMove hpos (hmv 0)
  linarith

#print axioms elapsed_two_sided

/-- **The weight form of the position law** [L].  The cascade from `1/(8m)`, moves `s < N` with setters `w s`, fixed at `N`
(nobody in the way), and total setter weight `∑_{s<N} m / w_s ≤ 3`.  Then `N`-th instant lies in `[1/(8m), 7/(8m)]` (`R ∈ [1, 7]`)
and is lonely for `E`.  `[PROVISIONAL: counting tool]`, supporting the position of the fixed point only; the displacement-frame
step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade (not this
weight) shows where it lands.  `0 < m` REQUIRED (division); no ordering, no cardinality. -/
theorem lonely_window_of_weight {E : Finset ℝ} {seq : ℕ → ℝ} {m : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {N : ℕ}
    (hfix : ∀ d ∈ E, ¬ InWay d (seq N)) (w : ℕ → ℝ) (hw : ∀ s, s < N → IsSetterAt E seq s (w s))
    (hW : ∑ s ∈ Finset.range N, m / w s ≤ 3) :
    1 / (8 * m) ≤ seq N ∧ seq N ≤ 7 / (8 * m) ∧ LonelyAt E (seq N) := by
  refine ⟨h0 ▸ start_le_seq hpos hmv N, ?_, lonely_of_notInWay hfix⟩
  have hel := elapsed_upper hpos N w hw
  have hcongr : ∑ s ∈ Finset.range N, 1 / (4 * w s) = (1 / (4 * m)) * ∑ s ∈ Finset.range N, m / w s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hw0 := hpos _ (hw s (Finset.mem_range.mp hs)).1
    field_simp
  have hle : (1 / (4 * m)) * ∑ s ∈ Finset.range N, m / w s ≤ (1 / (4 * m)) * 3 :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have e : 1 / (8 * m) + (1 / (4 * m)) * 3 = 7 / (8 * m) := by field_simp; norm_num
  rw [hcongr] at hel
  linarith

#print axioms lonely_window_of_weight

/-- **The move form implies the weight form** [L]: if every setter in the first `N` moves is at least `a > 0` and `N m ≤ 3 a`
then `∑_{s<N} m / w_s ≤ 3`.  So `lonely_window_of_weight` contains `LadderScale.lonely_window_of_moves`, and the weight hypothesis
is weaker (a reading far above `a` contributes almost nothing).  `[PROVISIONAL: counting tool]` (a sum over the moves), supporting the position
of the fixed point only. -/
theorem weight_le_moves {E : Finset ℝ} {seq : ℕ → ℝ} {m a : ℝ} (hm : 0 < m) (ha0 : 0 < a)
    (ham : ∀ d ∈ E, a ≤ d) {N : ℕ} (w : ℕ → ℝ) (hw : ∀ s, s < N → IsSetterAt E seq s (w s))
    (hN : (N : ℝ) * m ≤ 3 * a) : ∑ s ∈ Finset.range N, m / w s ≤ 3 := by
  have hterm : ∀ s ∈ Finset.range N, m / w s ≤ m / a := by
    intro s hs
    have hwE := (hw s (Finset.mem_range.mp hs)).1
    exact div_le_div_of_nonneg_left hm.le ha0 (ham _ hwE)
  have hle := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range] at hle
  simp only [nsmul_eq_mul] at hle
  have h2 : (N : ℝ) * (m / a) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ ha0]; linarith
  linarith

#print axioms weight_le_moves

/-! ## (2b) The gap identities: the exact form of the elapsed time -/

/-- **Telescoped gap law** [L]: along moves with setters `w s` from `a` to `a + d`,
`seq (a + d) - seq a = ∑ gap (w s) (seq s) / (8 w s)` (each move advances by `gap/(8 w)`: `Dilation.nextOpening_eq_add_gap`).
`[PROVISIONAL: counting tool]` (a sum over the moves), supporting the two gap identities below only. -/
theorem gap_telescope {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (a : ℕ) (w : ℕ → ℝ) :
    ∀ d : ℕ, (∀ s, a ≤ s → s < a + d → IsSetterAt E seq s (w s)) →
      seq (a + d) - seq a = ∑ s ∈ Finset.Ico a (a + d), gap (w s) (seq s) / (8 * w s) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hw
    have ih' := ih (fun s h1 h2 => hw s h1 (by omega))
    have e1 : a + (d + 1) = (a + d) + 1 := by omega
    rw [e1, Finset.sum_Ico_succ_top (by omega : a ≤ a + d)]
    have hs := hw (a + d) (by omega) (by omega)
    have hstep : seq (a + d + 1) = seq (a + d) + gap (w (a + d)) (seq (a + d)) / (8 * w (a + d)) := by
      rw [hs.2.2]; exact nextOpening_eq_add_gap (hpos _ hs.1) hs.2.1
    linarith

#print axioms gap_telescope

/-- **The final instant in terms of the gaps** [L]: in the coordinate `R = 8 m t` with `seq 0 = 1/(8 m)`,
`8 m · seq N = 1 + ∑_{s<N} gap_s · (m / w_s)`, each gap in `(0, 2)` (`Dilation.gap_pos`, `Dilation.gap_lt_two`).  So the landing point is the
sum, over the moves, of the position of the previous landing inside the setter's window (`gap`) times the weight `m / w`.  Hypotheses:
`0 < m` REQUIRED (division); `seq 0 = 1/(8 m)` REQUIRED for the constant `1`; the positivity of the readings REQUIRED.
`[PROVISIONAL: counting tool]` (a sum over the moves), supporting the position of the fixed point only. -/
theorem final_gap_identity {E : Finset ℝ} {seq : ℕ → ℝ} {m : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d)
    (h0 : seq 0 = 1 / (8 * m)) (N : ℕ) (w : ℕ → ℝ) (hw : ∀ s, s < N → IsSetterAt E seq s (w s)) :
    8 * m * seq N = 1 + ∑ s ∈ Finset.range N, gap (w s) (seq s) * (m / w s) := by
  have ht := gap_telescope hpos 0 w N (by intro s _ h2; exact hw s (by omega))
  rw [zero_add, ← Finset.range_eq_Ico] at ht
  have hcongr : ∑ s ∈ Finset.range N, gap (w s) (seq s) * (m / w s) =
      8 * m * ∑ s ∈ Finset.range N, gap (w s) (seq s) / (8 * w s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have := hpos _ (hw s (Finset.mem_range.mp hs)).1
    field_simp
  rw [hcongr, ← ht]
  have : 8 * m * seq 0 = 1 := by rw [h0]; field_simp
  nlinarith [this]

#print axioms final_gap_identity

/-- **The lap of a reading is consumed exactly by the gaps of the moves between its visits** [L].  `x` sets at `n` and is in the way at
`seq k` (`k > n`), `w s` the setter of the move at `s`, `n < s < k`.  Then
`∑_{s=n+1}^{k-1} gap_s · (x / w_s) + gap x (seq k) = 8 (lap_k - lap_n)`.
Every gap lies in `(0, 2)`, so the two budget halves are corollaries in the form: `4 Δj - 1 < ∑ x / w` (since `gap x (seq k) < 2`; this is
`LawOfPosition.lap_budget` and `Ladder5.budget_sum` for `Δj ≥ 1`) and, with `LawOfPosition.two_step_lower` on the gaps, `∑ x / w < 8 Δj + 1`
(`return_upper_budget`).  Data: the identity holds in 303 of 303 first returns of the slowest on the grid `Q = 12, M = 10` (`ladder5_v2.out`).
`[PROVISIONAL: counting tool]` (a sum over the moves), supporting the chain account of the return and no existence claim. -/
theorem return_gap_identity {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {n k : ℕ} (hnk : n < k) {x : ℝ}
    (hx : IsSetterAt E seq n x) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    ∑ s ∈ Finset.Ico (n + 1) k, gap (w s) (seq s) * (x / w s) + gap x (seq k) =
      8 * ((lap x (seq k) : ℝ) - (lap x (seq n) : ℝ)) := by
  have hx0 := hpos x hx.1
  obtain ⟨d, rfl⟩ : ∃ d, k = n + 1 + d := ⟨k - (n + 1), by omega⟩
  have ht := gap_telescope hpos (n + 1) w d (fun s h1 h2 => hws s (by omega) h2)
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have hcongr : ∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), gap (w s) (seq s) * (x / w s) =
      8 * x * ∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), gap (w s) (seq s) / (8 * w s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_Ico.mp hs
    have := hpos _ (hws s (by omega) (by omega)).1
    field_simp
  rw [hcongr, ← ht]
  unfold gap
  have e : 8 * x * (seq (n + 1 + d) - seq (n + 1)) = 8 * (x * seq (n + 1 + d)) - 8 * (x * seq (n + 1)) := by ring
  rw [e]
  have e2 : 8 * (x * seq (n + 1 + d)) = 8 * x * seq (n + 1 + d) := by ring
  linarith

#print axioms return_gap_identity

/-! ## (3) The budget of a return is two-sided -/

/-- Telescoped two-step law [L] (`[PROVISIONAL: counting tool]`, a sum over the moves, supporting `return_upper_budget` only): from `n + 1` to `n + 1 + d`, `∑ 1/(4 w_s) ≤ seq (n+1+d) + seq (n+d) - seq (n+1) - seq n`. -/
theorem two_step_sum {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (n : ℕ) (w : ℕ → ℝ) :
    ∀ d : ℕ, (∀ s, n < s → s < n + 1 + d → IsSetterAt E seq s (w s)) →
      ∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), 1 / (4 * w s) ≤ seq (n + 1 + d) + seq (n + d) - seq (n + 1) - seq n := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hw
    have ih' := ih (fun s h1 h2 => hw s h1 (by omega))
    have e1 : n + 1 + (d + 1) = (n + 1 + d) + 1 := by omega
    rw [e1, Finset.sum_Ico_succ_top (by omega : n + 1 ≤ n + 1 + d)]
    have hset : IsSetterAt E seq (n + d + 1) (w (n + 1 + d)) := by
      have e2 : n + d + 1 = n + 1 + d := by omega
      rw [e2]
      exact hw (n + 1 + d) (by omega) (by omega)
    have hts := two_step_lower hpos hmv (s := n + d) (x := w (n + 1 + d)) hset
    have e3 : n + d + 2 = n + 1 + d + 1 := by omega
    rw [e3] at hts
    have e5 : n + (d + 1) = n + 1 + d := by omega
    rw [e5]
    linarith

#print axioms two_step_sum

/-- **The budget of a return is two-sided** [L].  `x` sets at `n` on lap `j`, is in the way at `seq k` (`k > n`) on lap `j'`, and
`w s` is the setter of the move at `s`, `n < s < k`.  Then `∑_{s=n+1}^{k-1} x / w_s < 8 (j' - j) + 1`.  Together with
`LawOfPosition.lap_budget` (needs `x` set again at `k`) or `Ladder5.budget_sum` (`3 <`): for `j' - j = 1`, `3 < ∑ < 9`.
Hypotheses: positive readings (REQUIRED: division); the moves; `x` the setter at `n`; `x` in the way at `k`.  NOT REQUIRED: `x`
the slowest, a base `m`, `seq 0 = 1/(8m)`, `0 < seq 0`.  The bound `8 Δj + 1` has slack on the grids (`six_v1.out`: for `Δj = 1` the largest budget is `10349409600/1638109800` on the grid
`Q = 12, M = 10`), so this half is a law and not a description of the extremal chains.  `[PROVISIONAL: covering]`: the additive budget is a
necessary condition on a return, supporting the chain account of the return and no existence claim; the displacement-frame step it serves
is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters, and the cascade shows where it lands. -/
theorem return_upper_budget {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    ∑ s ∈ Finset.Ico (n + 1) k, x / w s < 8 * ((lap x (seq k) : ℝ) - (lap x (seq n) : ℝ)) + 1 := by
  have hx0 := hpos x hx.1
  obtain ⟨d, rfl⟩ : ∃ d, k = n + 1 + d := ⟨k - (n + 1), by omega⟩
  have hsum := two_step_sum hpos hmv n w d (fun s h1 h2 => hws s h1 h2)
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have hb0 := abs_lt.mp (abs_sub_lap_lt hx.2.1)
  have hbk := abs_lt.mp (abs_sub_lap_lt hw)
  have hle : seq (n + d) ≤ seq (n + 1 + d) := by
    have : n + d ≤ n + 1 + d := by omega
    exact seq_mono hpos hmv this
  have hmul : x * ∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), 1 / (4 * w s) ≤
      x * (seq (n + 1 + d) + seq (n + d) - seq (n + 1) - seq n) := mul_le_mul_of_nonneg_left hsum hx0.le
  have hcongr : x * ∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), 1 / (4 * w s) =
      (∑ s ∈ Finset.Ico (n + 1) (n + 1 + d), x / w s) / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_Ico.mp hs
    have hw0 := hpos _ (hws s (by omega) (by omega)).1
    field_simp
  rw [hcongr] at hmul
  have h2 : x * seq (n + d) ≤ x * seq (n + 1 + d) := mul_le_mul_of_nonneg_left hle hx0.le
  have e : x * (seq (n + 1 + d) + seq (n + d) - seq (n + 1) - seq n) =
      x * seq (n + 1 + d) + x * seq (n + d) - x * seq (n + 1) - x * seq n := by ring
  rw [e] at hmul
  linarith

#print axioms return_upper_budget

/-! ## (3b) The number of settings of a reading is an output of the weight -/

/-- **Settings against weight** [L].  Let `S` be a nonempty finite set of moves at which the same reading `x` is the setter, all before `N`,
and `w s` the setters of the moves `s < N`.  Then `4 · |S| < (x / m) · ∑_{s<N} m / w_s + 5`: the number of settings of `x` is controlled by
the weight available, `|S| - 1 < ((x/m) W + 1)/4` with `W = ∑ m / w_s` the total setter weight.  Proof: the laps of the settings are strictly
increasing integers between the first and the last, so `|S| ≤ Δj + 1`; the lap budget `4 Δj - 1 < ∑ x / w` (`LawOfPosition.lap_budget`) is at
most `(x/m) W`.  No lap condition, no ordering of the readings, no cap on `N`.  This is the reason (a law, not a cap) the count of settings of the slowest is
not bounded by the laws: it grows with `ρ_x W`; in the exact AP family (`six_v1.out`, section 6) at `ρ = 640` the number of settings is 28, and
`six_v1.py` checks `4 · 28 < ρ W + 5` in Fractions.  `[PROVISIONAL: counting tool]` (a sum over the moves and a count of settings), supporting the statement that
the count is controlled by the weight and no existence claim; the displacement-frame step it serves is rule 1: the isolation of the `d_min`
window `[1,7]` is displaced by the setters, and the cascade shows where it lands.  Hypotheses: `0 < m`, positivity, `0 < seq 0` REQUIRED
(division; `ChainLaws.setter_recur_lap`); the moves REQUIRED; `x` the slowest NOT REQUIRED. -/
theorem settings_weight_bound {E : Finset ℝ} {seq : ℕ → ℝ} {m x : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ E, 0 < d)
    (h0 : 0 < seq 0) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (S : Finset ℕ) (hSne : S.Nonempty)
    (hS : ∀ n ∈ S, IsSetterAt E seq n x) (N : ℕ) (hSN : ∀ n ∈ S, n < N) (w : ℕ → ℝ)
    (hw : ∀ s, s < N → IsSetterAt E seq s (w s)) :
    4 * (S.card : ℝ) < x / m * ∑ s ∈ Finset.range N, m / w s + 5 := by
  have hx0 : 0 < x := by
    obtain ⟨n0, hn0⟩ := hSne
    exact hpos x (hS n0 hn0).1
  have hT : 0 ≤ x / m * ∑ s ∈ Finset.range N, m / w s := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun s hs => ?_))
    have := hpos _ (hw s (Finset.mem_range.mp hs)).1
    positivity
  have hn : S.min' hSne ∈ S := S.min'_mem hSne
  have hk : S.max' hSne ∈ S := S.max'_mem hSne
  have hnk' : S.min' hSne ≤ S.max' hSne := S.min'_le _ hk
  rcases hnk'.lt_or_eq with hnk | heq
  · have hkN := hSN _ hk
    have hb := lap_budget hpos hnk (hS _ hn) (hS _ hk) w (fun s h1 h2 => hw s (by omega))
    have hsub : ∑ s ∈ Finset.Ico (S.min' hSne + 1) (S.max' hSne), x / w s ≤
        x / m * ∑ s ∈ Finset.range N, m / w s := by
      calc ∑ s ∈ Finset.Ico (S.min' hSne + 1) (S.max' hSne), x / w s ≤ ∑ s ∈ Finset.range N, x / w s := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => ?_)
            · intro s hs
              have := Finset.mem_Ico.mp hs
              exact Finset.mem_range.mpr (by omega)
            · have := hpos _ (hw s (Finset.mem_range.mp hs)).1
              positivity
        _ = x / m * ∑ s ∈ Finset.range N, m / w s := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun s hs => ?_)
            have := hpos _ (hw s (Finset.mem_range.mp hs)).1
            field_simp
    have hinj : Set.InjOn (fun n => lap x (seq n)) (S : Set ℕ) := by
      intro a ha b hb' heq'
      by_contra hne
      simp only at heq'
      rcases lt_or_gt_of_ne hne with h | h
      · have := setter_recur_lap hpos h0 hmv h (hS a ha) (hS b hb')
        omega
      · have := setter_recur_lap hpos h0 hmv h (hS b hb') (hS a ha)
        omega
    have hmaps : ∀ n ∈ S, lap x (seq n) ∈ Finset.Icc (lap x (seq (S.min' hSne))) (lap x (seq (S.max' hSne))) := by
      intro n hn'
      refine Finset.mem_Icc.mpr ⟨lap_seq_mono hpos hmv hx0 (S.min'_le n hn'), lap_seq_mono hpos hmv hx0 (S.le_max' n hn')⟩
    have hcard := Finset.card_le_card_of_injOn (fun n => lap x (seq n)) hmaps hinj
    rw [Int.card_Icc] at hcard
    have hlapnk : lap x (seq (S.min' hSne)) ≤ lap x (seq (S.max' hSne)) := lap_seq_mono hpos hmv hx0 hnk.le
    have hcard' : (S.card : ℤ) ≤ lap x (seq (S.max' hSne)) + 1 - lap x (seq (S.min' hSne)) := by
      have h1 : (S.card : ℤ) ≤ ((lap x (seq (S.max' hSne)) + 1 - lap x (seq (S.min' hSne))).toNat : ℤ) := by
        exact_mod_cast hcard
      rwa [Int.toNat_of_nonneg (by omega)] at h1
    have hcardR : (S.card : ℝ) ≤ (lap x (seq (S.max' hSne)) : ℝ) + 1 - (lap x (seq (S.min' hSne)) : ℝ) := by
      exact_mod_cast hcard'
    linarith
  · have hone : S.card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb' => ?_)
      have h1 := S.min'_le a ha
      have h2 := S.le_max' a ha
      have h3 := S.min'_le b hb'
      have h4 := S.le_max' b hb'
      omega
    have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hone
    linarith

#print axioms settings_weight_bound

/-! ## (4) The number of settings of a reading on the allowed laps -/

/-- The allowed laps of `FourDistinct.four_distinct_of_lap`: `1, …, 8` and `10`. -/
def goodLaps : Finset ℤ := {1, 2, 3, 4, 5, 6, 7, 8, 10}

theorem goodLaps_card : goodLaps.card = 9 := by decide

theorem mem_goodLaps {j : ℤ} : j ∈ goodLaps ↔ 1 ≤ j ∧ (j ≤ 8 ∨ j = 10) := by
  simp only [goodLaps, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **A reading has at most nine settings on the allowed laps** [L].  The settings of one reading `a` are on strictly increasing laps
(`ChainLaws.setter_recur_lap`), so the lap map is injective on the set `S` of its settings, and lands in the nine-element set
`goodLaps`.  The count is an OUTPUT of the strict increase of the lap and the lap condition; no move bound and no ordering of
the readings is assumed.  `[PROVISIONAL: counting tool]` (injection into a nine-element set), supporting the count of settings only. -/
theorem settings_le_nine {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, IsSetterAt E seq n a ∧ lap a (seq n) ∈ goodLaps) : S.card ≤ 9 := by
  have hinj : Set.InjOn (fun n => lap a (seq n)) (S : Set ℕ) := by
    intro n hn n' hn' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := setter_recur_lap hpos h0 hmv h (hS n hn).1 (hS n' hn').1
      simp only at heq
      omega
    · have := setter_recur_lap hpos h0 hmv h (hS n' hn').1 (hS n hn).1
      simp only at heq
      omega
  have := Finset.card_le_card_of_injOn (fun n => lap a (seq n)) (t := goodLaps)
    (fun n hn => (hS n hn).2) hinj
  rw [goodLaps_card] at this
  exact this

#print axioms settings_le_nine

/-- **The lap of a setting of a reading `≥ m` from `1/(8m)` is at least one** and the allowed laps then give nine: the form with
the lap condition as a statement about the cascade object [L]. -/
theorem slowest_settings_le_nine {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {a : ℝ}
    (hlapc : ∀ n, IsSetterAt E seq n a → lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) (S : Finset ℕ)
    (hS : ∀ n ∈ S, IsSetterAt E seq n a) : S.card ≤ 9 := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  refine settings_le_nine hpos h0pos hmv S (fun n hn => ⟨hS n hn, mem_goodLaps.mpr ⟨?_, hlapc n (hS n hn)⟩⟩)
  have hb : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  exact one_le_lap_of_bound hm (hlow a (hS n hn).1) hb (hS n hn).2.1

#print axioms slowest_settings_le_nine

/-! ## (4b) The landing point in the framework's own objects -/

/-- **The final landing is the opening of its last setter, so `R ≤ 7` is a lap bound on that setter** [L].  If `z` is in the way at `t` and
`t'` is the landing of the move it sets (`t' = nextOpening z t`), then `t' ≤ 7/(8m)` (that is, `R = 8 m t' ≤ 7`) holds iff
`8 j + 1 ≤ 7 z / m` for the lap `j = lap z t`.  This is a restatement of the position of the fixed point in terms of the last
setter (`DisplacedLanding.final_landing` names the same fact); it is not a bound, and the data (`six_v1.out`, the `LAST` lines) show which
laps the last setters occupy.  Hypotheses: `0 < z`, `0 < m` REQUIRED (division); `InWay z t` REQUIRED for the exact landing
`z t' = j + 1/8` (`Dilation.setter_reading`).  `[PROVISIONAL: covering]`: a bound on the landing point, supporting only the statement
that the landing lies in the window `[1, 7]`. -/
theorem landing_in_window_iff {z m t t' : ℝ} (hz : 0 < z) (hm : 0 < m) (hw : InWay z t) (ht' : t' = nextOpening z t) :
    t' ≤ 7 / (8 * m) ↔ 8 * (lap z t : ℝ) + 1 ≤ 7 * z / m := by
  have hland : z * t' = (lap z t : ℝ) + 1 / 8 := by rw [ht']; exact setter_reading hz hw
  have e : t' = ((lap z t : ℝ) + 1 / 8) / z := by
    field_simp; linarith
  rw [e, div_le_div_iff₀ hz (by positivity), le_div_iff₀ hm]
  constructor <;> intro h <;> nlinarith [h]

#print axioms landing_in_window_iff

/-! ## (5) Reductions for six disparities, and the statements left owed -/

/-- **A chain on the allowed laps has at most forty-five moves** [L]: five readings, every setter of the moves `s < N` on a lap in
`goodLaps`.  The count is the sum over the five readings of at most nine settings each (`settings_le_nine`).  An OUTPUT of the strict
increase of the lap of each reading; `N` is not assumed.  `[PROVISIONAL: counting tool]` (fibre count over the readings), supporting
`six_dichotomy` only. -/
theorem moves_le_of_lap_all {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 5) (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ s, s < N → IsSetterAt E seq s (w s)) (hlap : ∀ s, s < N → lap (w s) (seq s) ∈ goodLaps) : N ≤ 45 := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := w) (s := Finset.range N) (t := E)
    (fun x hx => (hw x (Finset.mem_range.mp hx)).1)
  rw [Finset.card_range] at hfib
  have hz : ∀ z ∈ E, ((Finset.range N).filter (fun s => w s = z)).card ≤ 9 := by
    intro z hz
    refine settings_le_nine hpos h0 hmv (a := z) _ (fun n hn => ?_)
    have hn' := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hn'.1
    have h1 := hw n hnN
    have h2 := hlap n hnN
    rw [hn'.2] at h1 h2
    exact ⟨h1, h2⟩
  have hle := Finset.sum_le_sum hz
  rw [Finset.sum_const] at hle
  simp only [smul_eq_mul] at hle
  have : E.card * 9 ≤ 5 * 9 := Nat.mul_le_mul_right 9 hcard
  omega

#print axioms moves_le_of_lap_all

/-- **Six disparities, the dichotomy** [L].  `ds` has at most six members, least element `m > 0`, and the least of the other five is
`a ≥ 15 m`.  Then EITHER some setter among the first forty-six moves of the cascade over `ds.erase m` from `1/(8m)` sits on lap `9`
or on a lap `≥ 11`, OR `ds` has a lonely instant in `R ∈ [1, 7]`.  Proof: with every setter on an allowed lap the chain has at most
forty-five moves (`moves_le_of_lap_all`), so it is fixed by then, and `45 m ≤ 3 a` is `15 m ≤ a` (position law,
`LadderScale.disparities_of_moves`).  The lap exception class is the class of `FourDistinct` (`j = 9` and `j ≥ 11` are where the
three-value window occurs, `FourDistinct.not_fourDistinctLaw`).  `[PROVISIONAL: counting tool]` (the forty-five), supporting the
position of the fixed point only; the displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is
displaced by the setters, and the cascade (not this count) shows where it lands.  It is a dichotomy, not an existence theorem: the
exceptional branch is not excluded here.  The constant `15` is what the count of the proof gives (`5 · 9 = 45`, `45/3`); it is not
shown to be required. -/
theorem six_dichotomy {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 6) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h15 : 15 * m ≤ a) :
    (∃ s, s ≤ 45 ∧ ∃ y, IsSetterAt (ds.erase m) (cascadeSeq (ds.erase m) (1 / (8 * m))) s y ∧
        (lap y (cascadeSeq (ds.erase m) (1 / (8 * m)) s) = 9 ∨ 11 ≤ lap y (cascadeSeq (ds.erase m) (1 / (8 * m)) s))) ∨
      ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  set E : Finset ℝ := ds.erase m with hE
  have hEc : E.card ≤ 5 := by
    have : E.card = ds.card - 1 := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ E, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm0 (hlow d hd)
  set seq : ℕ → ℝ := cascadeSeq E (1 / (8 * m)) with hseq
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  have hmv : ∀ n, IsMove E (seq n) (seq (n + 1)) := cascadeSeq_isMove E _
  by_cases hbad : ∃ s, s ≤ 45 ∧ ∃ y, IsSetterAt E seq s y ∧ (lap y (seq s) = 9 ∨ 11 ≤ lap y (seq s))
  · exact Or.inl hbad
  · right
    push Not at hbad
    -- some state `N ≤ 45` has nobody in the way
    have hex45 : ∃ N, N ≤ 45 ∧ ∀ d ∈ E, ¬ InWay d (seq N) := by
      by_contra hcon
      push Not at hcon
      have hset : ∀ i, i ≤ 45 → ∃ x, IsSetterAt E seq i x := fun i hi =>
        exists_setter hmv (fun hall => by
          obtain ⟨d, hd, hdw⟩ := hcon i hi
          exact hall d hd hdw)
      choose! w hw using hset
      have hgood : ∀ s, s < 46 → lap (w s) (seq s) ∈ goodLaps := by
        intro s hs
        have hws := hw s (by omega)
        have hb : 1 / (8 * m) ≤ seq s := h0 ▸ start_le_seq hpos hmv s
        have h1 : 1 ≤ lap (w s) (seq s) := one_le_lap_of_bound hm0 (hlow _ hws.1) hb hws.2.1
        have h2 := hbad s (by omega) (w s) hws
        rw [mem_goodLaps]
        refine ⟨h1, ?_⟩
        omega
      have := moves_le_of_lap_all hpos h0pos hmv hEc 46 w (fun s hs => hw s (by omega)) hgood
      omega
    obtain ⟨N0, hN0, hN0f⟩ := hex45
    have hex : ∃ N, ∀ d ∈ E, ¬ InWay d (seq N) := ⟨N0, hN0f⟩
    have hfix := Nat.find_spec hex
    have hNle : Nat.find hex ≤ 45 := (Nat.find_min' hex hN0f).trans hN0
    have hset : ∀ s, s < Nat.find hex → ∃ y, IsSetterAt E seq s y := fun s hs =>
      exists_setter hmv (Nat.find_min hex hs)
    have ha0 : 0 < a := lt_of_lt_of_le (by positivity) h15
    have hN : ((Nat.find hex : ℕ) : ℝ) * m ≤ 3 * a := by
      have : ((Nat.find hex : ℕ) : ℝ) ≤ 45 := by exact_mod_cast hNle
      nlinarith
    exact disparities_of_moves hm hm0 ha0 ham hlow hfix hset hN

#print axioms six_dichotomy

/-- **The first return of the slowest passes every other reading, so it takes at least five moves** [L].  At most five readings, `a` the
least, set at `n` on a lap `j ≤ 8` or `j = 10`, in the way again at `k` with `a` not in the way at the moves strictly between.  Then the
setters of the moves `n+1, …, k-1` are exactly the other readings (`FourDistinct.five_first_return_all_others_lap`, the law of the chain for the
readings other than `a`), and `n + 5 ≤ k` when `E` has five members.  An OUTPUT of the laws: the length of the return is read off
`E.erase a`, not assumed.  The length is a count of the intermediate moves, `[PROVISIONAL: counting tool]`, supporting the account of
the returns of the slowest (five_first_return_all_others) and no existence claim.  Hypothesis `E.card = 5` is REQUIRED for the bound
five (at four members the same argument gives `n + 4 ≤ k`).  Provenance: `Ladder5.return_after_four` (the bound four there). -/
theorem first_return_length {E : Finset ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ}
    (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0) (hmv : ∀ i, IsMove E (seq i) (seq (i + 1)))
    (hcard : E.card = 5) (ha : ∀ d ∈ E, a ≤ d) (hn : IsSetterAt E seq n a) (hnk : n < k)
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) (hw : InWay a (seq k))
    (hj : lap a (seq n) ≤ 8 ∨ lap a (seq n) = 10) {w : ℕ → ℝ}
    (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    (Finset.Ico (n + 1) k).image w = E.erase a ∧ n + 5 ≤ k := by
  have himg := five_first_return_all_others_lap hpos h0 hmv hcard.le ha hn hnk hfirst hw hj hws
  refine ⟨himg, ?_⟩
  have h4 : (E.erase a).card = 4 := by
    rw [Finset.card_erase_of_mem (hn.1), hcard]
  have hle := Finset.card_image_le (s := Finset.Ico (n + 1) k) (f := w)
  rw [himg, h4, Nat.card_Ico] at hle
  omega

#print axioms first_return_length

/-- **Chain weight** (OWED, sufficient and not necessary): for at most five readings `≥ m`, the cascade from `1/(8m)` is fixed at some
`N`, every earlier move has a setter, and the total setter weight is at most three.  By `lonely_window_of_weight` this gives a lonely
instant in `R ∈ [1, 7]`.  The exact grids of `six_v1.out` have weight at most `21608934/10200085` (all readings `≥ m`), and at most `78759002/48076505` when the
second smallest disparity is at least `5 m` (grids `Q = 12, M = 10`); the statement is a candidate invariant for `R_final ≤ 7` (`R_N - 1 ≤ 2 W`,
`elapsed_two_sided`), not an obligation of the framework: it is a bound with slack the AP does not have. `[PROVISIONAL: covering]`
(a bound on the landing point), supporting only the statement that the landing lies in the window `[1, 7]`. -/
-- STANDING: OWED
def FiveChainWeight : Prop :=
  ∀ (E : Finset ℝ) (m : ℝ), E.card ≤ 5 → 0 < m → (∀ d ∈ E, m ≤ d) →
    ∃ N : ℕ, (∀ d ∈ E, ¬ InWay d (cascadeSeq E (1 / (8 * m)) N)) ∧
      ∃ w : ℕ → ℝ, (∀ s, s < N → IsSetterAt E (cascadeSeq E (1 / (8 * m))) s (w s)) ∧
        ∑ s ∈ Finset.range N, m / w s ≤ 3

/-- **Six disparities from the chain weight** [L]. -/
theorem six_disparities_of_chain_weight (h : FiveChainWeight) : SixDisparitiesLonely := by
  intro ds hpos hcard
  by_cases hne : ds.Nonempty
  · obtain ⟨m, hm⟩ := exists_isLeast hne
    have hm0 : 0 < m := hpos m hm.1
    have hEc : (ds.erase m).card ≤ 5 := by
      have := Finset.card_erase_of_mem hm.1
      omega
    have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
    have hpos' : ∀ d ∈ ds.erase m, 0 < d := fun d hd => lt_of_lt_of_le hm0 (hlow d hd)
    obtain ⟨N, hfix, w, hw, hW⟩ := h (ds.erase m) m hEc hm0 hlow
    obtain ⟨h1, h2, h3⟩ := lonely_window_of_weight hm0 hpos' (cascadeSeq_zero _ _)
      (cascadeSeq_isMove (ds.erase m) (1 / (8 * m))) hfix w hw hW
    obtain ⟨s, hs1, -, hsl⟩ := add_dmin hm hm0 ⟨_, h1, h2, h3⟩
    exact ⟨s, lt_of_lt_of_le (by positivity) hs1, hsl⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨1, one_pos, fun d hd => absurd hd (Finset.notMem_empty d)⟩

#print axioms six_disparities_of_chain_weight

/-- **The additive budget alone admits a seven-move window on three letters** [L].  The word `r q r p r q r` (`p < q < r`: the settings of
`r` at moves `0, 2, 4, 6`, of `q` at `1, 5`, of `p` at `3`) satisfies every budget inequality of the repeated letters, with the exact
readings `p = 1`, `q = 1576/671`, `r = 2319084/325435`: `r/q > 3` (twice), `r/p > 3` (the `r` at `2` and `4` with only `p` between),
and `q/r + q/p + q/r > 3` (the `q` at `1` and `5`).  So the budget laws used in `eight_four_distinct` cannot give a window of seven; the
length eight is REQUIRED FOR THIS PROOF.  Whether a cascade realises the word is a different question (the exact census finds no
run of seven moves with three values (longest six, grid Q = 2, M = 60), `six_v1.out` sections 1 and 5, and a float-steered search of three-reading cascades finds none of length six
or seven, section 7: UNDECIDED, not excluded). -/
theorem budget_admits_word7 :
    ∃ p q r : ℝ, 0 < p ∧ p < q ∧ q < r ∧ 3 < r / q ∧ 3 < r / p ∧ 3 < q / r + q / p + q / r := by
  refine ⟨1, 1576 / 671, 2319084 / 325435, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms budget_admits_word7

/-! ## (6) The slowest reading can be set three times inside the lap condition: an exact instance

`settings_le_nine` is an OUTPUT bound.  The instance below shows that the bound cannot be taken to be one or two inside the lap
condition `j ∈ {1,…,8,10}`: five readings `40, 83/2, 43, 89/2, 46` (the d_min unit is `m = 1`, `R = 8 m t`), the cascade from
`R = 1` is thirteen moves long, and the slowest reading `40` is the setter at moves `0`, `5`, `11` on laps `5`, `6`, `7`.  The moves
are proved one by one from the definition `IsMove` with the table lemma `isMove_of_table` (every reading is classified at every
state: clear, or in the way with its opening not beyond the landing).  The instance was found by the exact census (`six_v1.out`,
section 3); this theorem is the [L] statement of it. -/

/-- **A move from a table of the five readings** [L]: the setter `x` on lap `k` lands at its opening `t'`; every member `e` of `E` is
either clear at `t` or in the way with its opening not beyond `t'`. -/
theorem isMove_of_table {E : Finset ℝ} {t t' x : ℝ} (hx : x ∈ E) (k : ℤ) (hk : |x * t - k| < 1 / 8)
    (ht' : t' = ((k : ℝ) + 1 / 8) / x)
    (hrest : ∀ e ∈ E, (∃ j : ℤ, (j : ℝ) + 1 / 8 ≤ e * t ∧ e * t ≤ (j : ℝ) + 7 / 8) ∨
      (∃ j : ℤ, |e * t - j| < 1 / 8 ∧ ((j : ℝ) + 1 / 8) / e ≤ t')) : IsMove E t t' := by
  right
  refine ⟨x, hx, inWay_of_abs k hk, ?_, ?_⟩
  · rw [ht', nextOpening_eq hk]
  · intro e he hw
    rcases hrest e he with ⟨j, h1, h2⟩ | ⟨j, hj, hle⟩
    · exact absurd hw (not_inWay_of_between j h1 h2)
    · rw [nextOpening_eq hj]; exact hle

#print axioms isMove_of_table

noncomputable def E3 : Finset ℝ := {40, 83 / 2, 43, 89 / 2, 46}

noncomputable def seq3 : ℕ → ℝ
  | 0 => (1 / 8 : ℝ)
  | 1 => (41 / 320 : ℝ)
  | 2 => (49 / 368 : ℝ)
  | 3 => (49 / 356 : ℝ)
  | 4 => (49 / 344 : ℝ)
  | 5 => (49 / 332 : ℝ)
  | 6 => (49 / 320 : ℝ)
  | 7 => (57 / 368 : ℝ)
  | 8 => (57 / 356 : ℝ)
  | 9 => (57 / 344 : ℝ)
  | 10 => (57 / 332 : ℝ)
  | 11 => (65 / 368 : ℝ)
  | 12 => (57 / 320 : ℝ)
  | _ => (65 / 356 : ℝ)

theorem seq3_move0 : IsMove E3 (seq3 0) (seq3 1) := by
  refine isMove_of_table (x := 40) (by simp [E3]) 5 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨5, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move1 : IsMove E3 (seq3 1) (seq3 2) := by
  refine isMove_of_table (x := 46) (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨6, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move2 : IsMove E3 (seq3 2) (seq3 3) := by
  refine isMove_of_table (x := 89 / 2) (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨6, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move3 : IsMove E3 (seq3 3) (seq3 4) := by
  refine isMove_of_table (x := 43) (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨6, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move4 : IsMove E3 (seq3 4) (seq3 5) := by
  refine isMove_of_table (x := 83 / 2) (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨5, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨6, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move5 : IsMove E3 (seq3 5) (seq3 6) := by
  refine isMove_of_table (x := 40) (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨6, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move6 : IsMove E3 (seq3 6) (seq3 7) := by
  refine isMove_of_table (x := 46) (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨7, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move7 : IsMove E3 (seq3 7) (seq3 8) := by
  refine isMove_of_table (x := 89 / 2) (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨7, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move8 : IsMove E3 (seq3 8) (seq3 9) := by
  refine isMove_of_table (x := 43) (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨7, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move9 : IsMove E3 (seq3 9) (seq3 10) := by
  refine isMove_of_table (x := 83 / 2) (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨7, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move10 : IsMove E3 (seq3 10) (seq3 11) := by
  refine isMove_of_table (x := 46) (by simp [E3]) 8 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨6, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨8, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move11 : IsMove E3 (seq3 11) (seq3 12) := by
  refine isMove_of_table (x := 40) (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨7, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨8, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_move12 : IsMove E3 (seq3 12) (seq3 13) := by
  refine isMove_of_table (x := 89 / 2) (by simp [E3]) 8 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by simp only [seq3]; norm_num) ?_
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨7, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inr ⟨8, by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num, by simp only [seq3]; norm_num⟩
  · exact Or.inl ⟨8, by simp only [seq3]; norm_num, by simp only [seq3]; norm_num⟩

theorem seq3_fixed (n : ℕ) : IsMove E3 (seq3 (n + 13)) (seq3 (n + 13 + 1)) := by
  have e1 : seq3 (n + 13) = (65 / 356 : ℝ) := rfl
  have e2 : seq3 (n + 13 + 1) = (65 / 356 : ℝ) := rfl
  rw [e1, e2]
  left
  refine ⟨?_, rfl⟩
  intro e he
  simp only [E3, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_inWay_of_between 7 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 7 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 7 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 8 (by norm_num) (by norm_num)
  · exact not_inWay_of_between 8 (by norm_num) (by norm_num)

theorem seq3_isMove : ∀ n, IsMove E3 (seq3 n) (seq3 (n + 1)) := by
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · exact seq3_move0
  · exact seq3_move1
  · exact seq3_move2
  · exact seq3_move3
  · exact seq3_move4
  · exact seq3_move5
  · exact seq3_move6
  · exact seq3_move7
  · exact seq3_move8
  · exact seq3_move9
  · exact seq3_move10
  · exact seq3_move11
  · exact seq3_move12
  · exact seq3_fixed n

theorem seq3_setter0 : IsSetterAt E3 seq3 0 40 :=
  isSetterAt_of (by simp [E3]) 5 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by show seq3 1 = _; simp only [seq3]; norm_num)

theorem seq3_setter5 : IsSetterAt E3 seq3 5 40 :=
  isSetterAt_of (by simp [E3]) 6 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by show seq3 6 = _; simp only [seq3]; norm_num)

theorem seq3_setter11 : IsSetterAt E3 seq3 11 40 :=
  isSetterAt_of (by simp [E3]) 7 (by simp only [seq3]; rw [abs_lt]; constructor <;> norm_num)
    (by show seq3 12 = _; simp only [seq3]; norm_num)


/-- **The slowest reading is set three times on laps `5, 6, 7`** [L].  `E3 = {40, 83/2, 43, 89/2, 46}`, all at least `m = 1`, the cascade
`seq3` from `1/8` (`R = 1`) is a cascade sequence (`IsMove` at every step), and the slowest reading `40` is the setter at moves `0`, `5`,
`11`, on laps `5`, `6`, `7` (all inside the lap condition of `FourDistinct.four_distinct_of_lap`).  So the number of settings of the
slowest of five readings is not at most two, even on the allowed laps; `settings_le_nine` gives at most nine; the exact value of the
largest number on the allowed laps is UNDECIDED (the arithmetic-progression family of `six_v1.out` section 6 has more settings, on laps
past ten).  `[PROVISIONAL: counting tool]`: a count of the settings of one reading in one instance, supporting the statement that the count is
not at most two; it is an observation of the instance and no existence claim. -/
theorem three_settings_of_slowest :
    (∀ n, IsMove E3 (seq3 n) (seq3 (n + 1))) ∧ seq3 0 = 1 / (8 * 1) ∧ (∀ d ∈ E3, (1 : ℝ) ≤ d) ∧ (∀ d ∈ E3, (40 : ℝ) ≤ d) ∧
      IsSetterAt E3 seq3 0 40 ∧ IsSetterAt E3 seq3 5 40 ∧ IsSetterAt E3 seq3 11 40 ∧
      lap 40 (seq3 0) = 5 ∧ lap 40 (seq3 5) = 6 ∧ lap 40 (seq3 11) = 7 := by
  refine ⟨seq3_isMove, by simp only [seq3]; norm_num, ?_, ?_, seq3_setter0, seq3_setter5, seq3_setter11, ?_, ?_, ?_⟩
  · intro d hd
    simp only [E3, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro d hd
    simp only [E3, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · refine lap_eq_of_near (k := 5) ?_
    simp only [seq3]; rw [abs_lt]; constructor <;> norm_num
  · refine lap_eq_of_near (k := 6) ?_
    simp only [seq3]; rw [abs_lt]; constructor <;> norm_num
  · refine lap_eq_of_near (k := 7) ?_
    simp only [seq3]; rw [abs_lt]; constructor <;> norm_num

#print axioms three_settings_of_slowest

end SixDisparities

end Fresh
