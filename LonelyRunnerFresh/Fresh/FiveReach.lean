import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.Gate
import Fresh.Types
import Fresh.StrongGateStudy

/-!
# Reach of `k` readings: what is proved, what the data say, and where the argument for five stalls (Task Y)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules named in the task; nothing from the existing `LonelyRunner`
repo.  Exact reals only; every reading is positive (no runner is stationary).  The coordinate is `R = 8·m·t`
(`t = R/(8m)`), `m > 0` a lower bound of the readings.

Object.  `Reach k B` : any finite set `E` of at most `k` positive readings, all `≥ m`, has a lonely instant (`LonelyAt E s`)
with `1/(8m) ≤ s ≤ B/(8m)`, i.e. in `R ∈ [1, B]`.  `StrongGateStudy.FiveReach` is `Reach 5 6` (`fiveReach_iff`).  The
statement is a bound on WHERE a lonely instant lies; no move count appears in it.

## What is proved ([L]; each theorem has its `#print axioms` line, all `[propext, choice, Quot.sound]`)
* Bookkeeping: `reach_mono_card`, `reach_mono_bound`, `fiveReach_iff`, `strongGate_of_reach_five`, `fiveReach_of_sharp`,
  `fiveReach_of_reach_five`, `exists_setter`, `step_lt`, `step_nine`, `seq_le_pow`.
* Laws of the cascade, general `k` (symbolic):
  - `return_law`: if `x` sets at `n` on lap `j` and is in the way again at `seq m`, `m > n`, then
    `(8j+7)/(8j+1) · seq (n+1) < seq m`.
  - `triple_law`: if `x` sets at `n` and `n+2` and `y` at `n+1`, then `3 y < x`, `6 i ≤ 2 j` (laps of `y` and `x`), and the
    later lap of `x` is `≥ j+1`.
  - `lap_one_return_gap`: a reading that sets on lap 1 is not in the way again within three moves
    (`(9/7)^2 = 81/49 < 5/3 = (8·1+7)/(8·1+1)`).
* `reach_one` (`Reach 1 (9/7)`), `reach_two` (`Reach 2 (81/49)`) by the cascade: the number of moves is an OUTPUT
  of `triple_law` (a fourth move is impossible), never an assumption.
* `reach_union`, `reach_union_gt`, `reach_three` (`Reach 3 (729/343)`): `Reach k ((9/7)^k)` for `(9/7)^k < 15/7`, i.e.
  `k ≤ 3` (`union_bound_range`).  Proof: a union bound in the scale-invariant measure `dR/R`: no lonely instant in `[1, B]`
  means the zones of the readings cover it (`cover_prod`, a finite multiplicative covering lemma), and one reading has
  clipped zone ratio at most `9/7` against a window `[1, B]`, `B ≤ 15/7` (`prod_zr_le`: both boundary zones by the integer
  inequality `abint` — a finite check for `a ≤ 17` and one polynomial inequality for `a ≥ 18` — the interior zones by the telescoping
  `qz N ^ 4 ≤ (2N+1)/(2N−1)`).  The exact supremum is attained in the limit: `not_reach_one`, `not_reach_two`,
  `not_reach_three` (lap-1 chains).
* `reach_small`, `reach_small_unit`: readings in `[m, 15m/B]` have a lonely instant by `R = B` once `B > (9/7)^k`
  (only lap 1 can enter the window).  So to beat the pure lap-1 value a reading must reach its second lap inside the window.
* Exact lower-bound witnesses (rational readings, generated from the exact cascade, `norm_num` on literals):
  `not_reach_four` (`E_four`, first lonely `R = 8500/3089 ≈ 2.7517`), `not_reach_four_pure` (`Reach 4 ((9/7)^4)` is false),
  `not_reach_five` / `not_reach_five_le` (`E_five`, `R = 6250/1421 ≈ 4.3983`),
  `not_reach_six` / `not_reach_six_six`: `Reach 6 6` is FALSE (`E_six`, first lonely `R = 4900000/562313 ≈ 8.714`, twenty moves).

## What is OWED ([OWED]; tagged `-- STANDING: OWED`)
`ReachFourSharp` (`Reach 4 (289/105)`), `ReachFiveSharp` (`Reach 5 (2125/483)`), and `FiveReach` (`Reach 5 6`, in
`StrongGateStudy`).  `fiveReach_of_sharp` shows the second implies the third.

## Data ([OBS]: exact Fractions plus float-steered searches; none of it is a Lean statement)
Supremum of the first lonely `R` over sets of `k` readings `≥ 1`, with the chain that attains it as a limit; exact vertex of
the linear programme of the chain pattern (rational readings, all inequalities of the pattern, objective the final `R`):
* `k=1`: `9/7`; chain `(a,1)`, `a → 7`.
* `k=2`: `81/49`; `(a,1)(b,1)`, `7, 49/9`.     `k=3`: `729/343`; three lap-1 moves, `7, 49/9, 343/81`.
* `k=4`: `289/105`; laps `1,1,1,1,2,2`; vertex readings `7, 105/17, 245/51, 1715/459`.
* `k=5`: `2125/483`; twelve moves, laps `1,1,1,1,2,2,2,2,3,3,2,3`, setters (by vertex reading)
  `7, 483/85, 1449/289, 1127/289 | 7, 161/25, 483/85, 1449/289 | 7, 161/25, 1127/289, 483/85`, instants
  `R = 9/7, 255/161, 289/161, 2601/1127, 17/7, 425/161, 1445/483, 4913/1449, 25/7, 625/161, 4913/1127, 2125/483`.
  At the vertex five non-landing constraints are tight (a setter's zone starts exactly where the previous landing is);
  the reading `7` lands at `(8j+1)/7` on laps `1, 2, 3`.
* `k=6`: sets with first lonely `R ≈ 8.7` exist (`E_six`, [L]).  The exact vertex of a 21-move chain pattern gives `R = 9`
  (readings `161/33, 7, 833/279, 119/55, 49/9, 1127/297`; the last move is `49/9` on lap 6, `(8·6+1)·9/49 = 9`), so the
  six-reading supremum is at least `9` [OBS]; compare the five-reading `2125/483 ≈ 4.40`.
* Exact enumeration (integer cascade, all sets of readings `a/Q`, distinct, `1 ≤ a/Q ≤ M`): `k=3`, `Q ∈ {20,40,60,84,105}`,
  `M=10`: max `945/446 ≈ 2.1188`; `k=4`, `Q ∈ {12,24,36,51}`, `M=9`: max `867/316 ≈ 2.7437`; `k=5`, `Q ≤ 8` with `M=14`,
  `Q ∈ [9,20] ∪ {24}` with `M=9`, `Q ≤ 6` with `M=30` (up to `2.1·10^9` sets per run): max `100/23 ≈ 4.3478` (`Q = 16, 20, 24`).  No set above
  the vertex values; none above `6`.  (`d_min = 1` as a sixth runner is clear on `R ∈ [1,7]`, so these are the 6-sets.)

## Where it stalls ([reasoned] unless a theorem is named)
* The exact range of the union bound is `k ≤ 3` (`union_bound_range`: `(9/7)^3 < 15/7 < (9/7)^4`).  Each reading of large
  disparity shadows a quarter of the log-line (zone width `2/8`), so for any measure `k = 4` readings meet the bound `1` and
  `k ≥ 5` exceed it: covering is then not excluded by measure, and `Reach 4`, `Reach 5` are statements about how the zones of
  large readings can be arranged (a lonely-runner statement for five and six runners with gap `1/8`), not about lengths.
* The lap labels of a chain range over all positive integers (a reading of size `8j` sets on lap `j`; compare
  `Types.firstMove_lap`), so the list of setter-lap patterns of `k ≥ 3` readings is infinite, although the chain lengths seen
  are small (exact integer sets: at most 5 moves for `k = 3`, readings `≤ 1000`; float-steered real sets: 7 moves for `k = 3`;
  12 at the `k = 5` vertex; 20 for `E_six`).  A proof that enumerates patterns therefore needs the laps as parameters;
  `triple_law` and `return_law` are the symbolic constraints found in that form, and they close `k = 2` only.
* The fifth reading changes the extremum from `(9/7)^k` (pure lap-1 chains, `k ≤ 3`) to a twelve-move chain through laps
  `1, 2, 3` because the lap-2 zones of all five readings fit inside `[1, 4.4]`, and a first-lap return needs three moves in between
  (`lap_one_return_gap`), which a chain of four distinct readings supplies (the reading `7` sets on lap 1 at step 1 and on
  lap 2 at step 5).
* No symbolic argument for `Reach 4` or `Reach 5` was found; no counterexample to `FiveReach` was found in the exact data.

Provenance.  `step_lt` is `Dilation.dilation_lt` made monotone in the lap; `exists_setter` is the second disjunct of
`IsMove`; `triple_law` and `return_law` combine `Dilation.setter_reading`, `ChainLaws.setter_recur_lap` and the exact reading
`x · seq (n+1) = j + 1/8`; in the existing tree the nearest statements are `LRC/Spec/ZoneLinkN.lean` (`slower_lap_le`,
`faster_lap_lt`, the link rule) and `LRC/Spec/LapDeadlineN.lean`; I did not find in those two files a ratio constraint
between a reading and its single intermediate setter (the rest of `LRC/` was not searched exhaustively).  The log-time picture (scale invariance as translation, `LRC/Spec/LogTimeN.lean`) is the setting of
`cover_prod`/`prod_zr_le`, which have no counterpart there; `LRC/Spec/FlankFiniteN.lean` (`four_clears_small` by `decide`)
is a finite check of a different statement (flank openings for integer disparities).  I read those arguments and wrote every
proof here for this file; nothing was copied.
-/

open Classical

namespace Fresh

namespace FiveReachStudy

open Cascade Dilation ChainLaws StrongGateStudy

/-! ## (1) The statement family -/

/-- **`Reach k B`**: every set of at most `k` readings, all at least `m > 0`, has a lonely instant in
`[1/(8m), B/(8m)]` (in readings: the first lonely point from `R = 1` is at `R ≤ B`).  A bound on where a lonely
instant lies; no move count appears. -/
-- STANDING: DEFINITION
def Reach (k : ℕ) (B : ℝ) : Prop :=
  ∀ (E : Finset ℝ) (m : ℝ), E.card ≤ k → 0 < m → (∀ d ∈ E, m ≤ d) →
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ B / (8 * m) ∧ LonelyAt E s

/-- `StrongGateStudy.FiveReach` is `Reach 5 6`. -/
theorem fiveReach_iff : FiveReach ↔ Reach 5 6 := Iff.rfl

#print axioms fiveReach_iff

/-- A reach statement for `k` readings gives one for fewer readings. -/
theorem reach_mono_card {j k : ℕ} {B : ℝ} (hjk : j ≤ k) (h : Reach k B) : Reach j B :=
  fun E m hE hm hlow => h E m (hE.trans hjk) hm hlow

#print axioms reach_mono_card

/-- A reach statement with a smaller bound gives one with a larger bound (`m > 0`). -/
theorem reach_mono_bound {k : ℕ} {B B' : ℝ} (hBB : B ≤ B') (h : Reach k B) : Reach k B' := by
  intro E m hE hm hlow
  obtain ⟨s, hs1, hs2, hsl⟩ := h E m hE hm hlow
  refine ⟨s, hs1, hs2.trans ?_, hsl⟩
  exact div_le_div_of_nonneg_right hBB (by positivity)

#print axioms reach_mono_bound

/-- `Reach 5 6` gives the strong gate (through `FiveCarve`). -/
theorem strongGate_of_reach_five (h : Reach 5 6) : Types.StrongGate :=
  strongGate_of_fiveCarve (fiveCarve_of_fiveReach h)

#print axioms strongGate_of_reach_five

/-! ## (2) Cascade bookkeeping -/

/-- If nobody is in the way at `t`, then `t` is lonely. -/
theorem lonely_of_notInWay {E : Finset ℝ} {t : ℝ} (h : ∀ d ∈ E, ¬ InWay d t) : LonelyAt E t :=
  fun d hd => not_inWay_iff.mp (h d hd)

#print axioms lonely_of_notInWay

/-- If somebody is in the way at `seq n`, the move at `n` has a setter. -/
theorem exists_setter {E : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ}
    (h : ¬ ∀ d ∈ E, ¬ InWay d (seq n)) : ∃ x, IsSetterAt E seq n x := by
  rcases hmv n with ⟨h1, _⟩ | ⟨x, hx, hwx, hs, _⟩
  · exact absurd h1 h
  · exact ⟨x, hx, hwx, hs⟩

#print axioms exists_setter

/-- **One forward move on a lap `≥ N0 ≥ 1` multiplies the instant by less than `(8N0+1)/(8N0−1)`.** -/
theorem step_lt {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x : ℝ} (hx : IsSetterAt E seq n x) {N0 : ℝ}
    (hN0 : 1 ≤ N0) (hlap : N0 ≤ (lap x (seq n) : ℝ)) :
    seq (n + 1) < (8 * N0 + 1) / (8 * N0 - 1) * seq n := by
  have htn : 0 < seq n := lt_of_lt_of_le h0 (start_le_seq hpos hmv n)
  have hx0 := hpos x hx.1
  have hlap1 : 1 ≤ lap x (seq n) := by
    have : (1 : ℝ) ≤ (lap x (seq n) : ℝ) := hN0.trans hlap
    exact_mod_cast this
  have hd := dilation_lt hx0 htn hx.2.1 hlap1
  rw [← hx.2.2] at hd
  have hmono : (8 * (lap x (seq n) : ℝ) + 1) / (8 * (lap x (seq n) : ℝ) - 1) ≤ (8 * N0 + 1) / (8 * N0 - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  rw [div_lt_iff₀ htn] at hd
  have := mul_le_mul_of_nonneg_right hmono htn.le
  linarith

#print axioms step_lt

/-- A bound of the form `s ≤ c · (1/(8m))` with `c ≤ B` is a bound `s ≤ B/(8m)`. -/
theorem le_bound {m c B s : ℝ} (hm : 0 < m) (hcB : c ≤ B) (hs : s ≤ c * (1 / (8 * m))) : s ≤ B / (8 * m) := by
  have h1 : c * (1 / (8 * m)) = c / (8 * m) := by ring
  rw [h1] at hs
  exact hs.trans (div_le_div_of_nonneg_right hcB (by positivity))

#print axioms le_bound

/-- **A setter of a cascade from the bound `1/(8m)` multiplies the instant by less than `9/7`.** -/
theorem step_nine {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x : ℝ}
    (hx : IsSetterAt E seq n x) : seq (n + 1) < 9 / 7 * seq n := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  have hb : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  have hl : 1 ≤ lap x (seq n) := one_le_lap_of_bound hm (hlow x hx.1) hb hx.2.1
  have hl' : (1 : ℝ) ≤ (lap x (seq n) : ℝ) := by exact_mod_cast hl
  have := step_lt hpos h0pos hmv hx (N0 := 1) le_rfl hl'
  norm_num at this
  linarith

#print axioms step_nine

/-- A set with at most one element: any two members are equal. -/
theorem eq_of_card_le_one {E : Finset ℝ} (hE : E.card ≤ 1) {a b : ℝ} (ha : a ∈ E) (hb : b ∈ E) : a = b :=
  Finset.card_le_one.mp hE a ha b hb

/-- A set with at most two elements has no three distinct members. -/
theorem eq_of_card_le_two {E : Finset ℝ} (hE : E.card ≤ 2) {a b c : ℝ} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  -- [PROVISIONAL: counting tool] pigeonhole: three distinct members contradict `E.card ≤ 2`; supports `reach_two`.
  by_contra hac
  have : 2 < E.card := Finset.two_lt_card_iff.mpr ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  omega

#print axioms eq_of_card_le_one
#print axioms eq_of_card_le_two

/-! ## (3) One reading -/

/-- **One reading `x ≥ m` has a lonely instant in `R ∈ [1, 9/7]`.**  The cascade from `1/(8m)` makes at most one move
(the setter is not in the way at its own opening, and it is the only reading); that move multiplies the instant by less
than `9/7`.  `9/7` is the exact supremum: `E = {x}` with `x → 7⁺`.  [PROVISIONAL: covering] this is a covering step (one
reading cannot shadow `[1, 9/7]`); it supports `Reach 5 6` only through the monotone chain of `Reach k` statements. -/
theorem reach_one : Reach 1 (9 / 7) := by
  intro E m hE hm hlow
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ht0 : 0 < 1 / (8 * m) := by positivity
  set seq : ℕ → ℝ := cascadeSeq E (1 / (8 * m)) with hseq
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have hmv : ∀ n, IsMove E (seq n) (seq (n + 1)) := cascadeSeq_isMove E _
  by_cases c0 : ∀ d ∈ E, ¬ InWay d (seq 0)
  · exact ⟨seq 0, h0.ge, le_bound hm (by norm_num : (1 : ℝ) ≤ 9 / 7) (by rw [h0]; linarith), lonely_of_notInWay c0⟩
  obtain ⟨a1, h1⟩ := exists_setter hmv c0
  have c1 : ∀ d ∈ E, ¬ InWay d (seq 1) := by
    intro d hd
    have : d = a1 := eq_of_card_le_one hE hd h1.1
    subst this
    exact setter_not_inWay hpos h1.1 h1.2.2 (hmv 0)
  have hs1 := step_nine hm hlow h0 hmv h1
  -- [PROVISIONAL: counting tool] the cascade fixes after one move because `E` has one member (the setter is not in the
  -- way at its own opening); the count is a consequence, not an assumption.  Supports `Reach 1 (9/7)`, a covering step
  -- towards `Reach 5 6` and `Types.StrongGate`.
  exact ⟨seq 1, h0 ▸ start_le_seq hpos hmv 1, le_bound hm le_rfl (by rw [h0] at hs1; linarith), lonely_of_notInWay c1⟩

#print axioms reach_one

/-! ## (4) The return laws (general `k`) -/

/-- **Return law.**  If `x` sets the move at `n` on lap `j` and is in the way again at some later `seq m`, then the
instant has been dilated, since the landing `seq (n+1)`, by more than `(8j+7)/(8j+1)`.  Reason: the setter stands at
`x · seq (n+1) = j + 1/8`; being in the way again it is on a later lap (`setter_later_lap`), so `x · seq m > j + 7/8`.
In readings: between two visits of one reading the moves in between dilate `R` by more than `(8j+7)/(8j+1)`, while
each of them dilates by less than `(8i+1)/(8i−1)` on its lap `i` (`step_lt`). -/
theorem return_law {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n < m) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq m)) :
    (8 * (lap x (seq n) : ℝ) + 7) / (8 * (lap x (seq n) : ℝ) + 1) * seq (n + 1) < seq m := by
  have hx0 := hpos x hx.1
  have hj0 : (0 : ℝ) ≤ (lap x (seq n) : ℝ) := by exact_mod_cast setter_lap_nonneg hpos h0 hmv hx
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have ha0 : 0 < seq (n + 1) := lt_of_lt_of_le h0 (start_le_seq hpos hmv (n + 1))
  have hlap : lap x (seq n) + 1 ≤ lap x (seq m) := setter_later_lap hpos h0 hmv hnm hx hw
  have hlap' : (lap x (seq n) : ℝ) + 1 ≤ (lap x (seq m) : ℝ) := by exact_mod_cast hlap
  have hb := (abs_lt.mp (abs_sub_lap_lt hw)).1
  -- x * seq m > j + 7/8
  have h1 : (lap x (seq n) : ℝ) + 7 / 8 < x * seq m := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  have h2 : 8 * (lap x (seq n) : ℝ) + 1 = 8 * (x * seq (n + 1)) := by linarith
  rw [h2]
  have h3 : (8 * (lap x (seq n) : ℝ) + 7) * seq (n + 1) < 8 * (x * seq m) * seq (n + 1) := by
    apply mul_lt_mul_of_pos_right _ ha0
    linarith
  nlinarith

#print axioms return_law

/-- **Triple law.**  If the same reading `x` sets the moves at `n` and at `n + 2` and `y` sets the move at `n + 1`, then
`3 y < x`; the lap `i` of `y` at `seq (n+1)` and the lap `j` of `x` at `seq n` satisfy `6 i ≤ 2 j`; and `x` sets the later
move on a lap `≥ j + 1`.  In readings: a reading that comes back after exactly one other move needs that other reading
below a third of it.  This is the symbolic reason a chain of two readings has at most three moves (`reach_two`); it is the
one-intermediate case of the return law, with the exact value of `y` on its lap used. -/
theorem triple_law {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x)
    (hy : IsSetterAt E seq (n + 1) y) (hx' : IsSetterAt E seq (n + 2) x) :
    3 * y < x ∧ 6 * lap y (seq (n + 1)) ≤ 2 * lap x (seq n) ∧ lap x (seq n) + 1 ≤ lap x (seq (n + 2)) := by
  have hx0 := hpos x hx.1
  have hy0 := hpos y hy.1
  have hj : (0 : ℝ) ≤ (lap x (seq n) : ℝ) := by exact_mod_cast setter_lap_nonneg hpos h0 hmv hx
  have hrec : lap x (seq n) + 1 ≤ lap x (seq (n + 2)) := by
    have := setter_recur_lap hpos h0 hmv (show n < n + 2 by omega) hx hx'
    omega
  have hrec' : (lap x (seq n) : ℝ) + 1 ≤ (lap x (seq (n + 2)) : ℝ) := by exact_mod_cast hrec
  have hxa : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have hyb : y * seq (n + 2) = (lap y (seq (n + 1)) : ℝ) + 1 / 8 := by
    have := hy.2.2
    rw [this]; exact setter_reading hy0 hy.2.1
  have hya := abs_lt.mp (abs_sub_lap_lt hy.2.1)
  have hxb := (abs_lt.mp (abs_sub_lap_lt hx'.2.1)).1
  set j : ℝ := (lap x (seq n) : ℝ) with hjdef
  set i : ℝ := (lap y (seq (n + 1)) : ℝ) with hidef
  set a := seq (n + 1) with hadef
  set b := seq (n + 2) with hbdef
  -- H1: x (i + 1/8) > (j + 7/8) y
  have H1 : (j + 7 / 8) * y < x * (i + 1 / 8) := by
    have hxb' : j + 7 / 8 < x * b := by linarith
    have : y * (j + 7 / 8) < y * (x * b) := mul_lt_mul_of_pos_left hxb' hy0
    have e : y * (x * b) = x * (i + 1 / 8) := by rw [← hyb]; ring
    nlinarith
  -- H2: x (i - 1/8) < (j + 1/8) y
  have H2 : x * (i - 1 / 8) < (j + 1 / 8) * y := by
    have h1 : x * (i - 1 / 8) < x * (y * a) := mul_lt_mul_of_pos_left (by linarith) hx0
    have e : x * (y * a) = (j + 1 / 8) * y := by rw [← hxa]; ring
    linarith
  -- eliminate x, y: 2 j + 1 > 6 i
  have hji : 6 * i < 2 * j + 1 := by
    have hk1 : 0 < j + 1 / 8 := by linarith
    have hk2 : 0 < j + 7 / 8 := by linarith
    have A1 := mul_lt_mul_of_pos_left H1 hk1
    have A2 := mul_lt_mul_of_pos_left H2 hk2
    have key : 0 < x * (2 * j + 1 - 6 * i) := by nlinarith
    have := (pos_iff_pos_of_mul_pos key).mp hx0
    linarith
  have hint : 6 * lap y (seq (n + 1)) ≤ 2 * lap x (seq n) := by
    have h' : (6 * lap y (seq (n + 1)) : ℝ) < 2 * (lap x (seq n) : ℝ) + 1 := by
      linarith
    have h'' : 6 * lap y (seq (n + 1)) < 2 * lap x (seq n) + 1 := by exact_mod_cast h'
    omega
  refine ⟨?_, hint, hrec⟩
  -- 3 y < x
  have hint' : 6 * i ≤ 2 * j := by
    have : ((6 * lap y (seq (n + 1)) : ℤ) : ℝ) ≤ ((2 * lap x (seq n) : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at this; linarith
  have hk2 : 0 < j + 7 / 8 := by linarith
  have h3 : 3 * x * (i + 1 / 8) < x * (j + 7 / 8) := by nlinarith
  have h4 : (j + 7 / 8) * (3 * y) < (j + 7 / 8) * x := by nlinarith
  exact lt_of_mul_lt_mul_left h4 hk2.le

#print axioms triple_law

/-- Along a cascade from the bound `1/(8m)`, `j` further moves multiply the instant by at most `(9/7)^j`. -/
theorem seq_le_pow {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (i : ℕ) :
    ∀ j : ℕ, seq (i + j) ≤ (9 / 7 : ℝ) ^ j * seq i := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
    have hb : 1 / (8 * m) ≤ seq (i + j) := h0 ▸ start_le_seq hpos hmv (i + j)
    have hp : 0 < seq (i + j) := lt_of_lt_of_le (by positivity) hb
    have hstep : seq (i + j + 1) ≤ 9 / 7 * seq (i + j) := by
      rcases seq_fix_or_ratio_lt hm hlow h0 hmv (i + j) with h | h
      · rw [h]; nlinarith
      · rw [div_lt_iff₀ hp] at h; linarith
    calc seq (i + (j + 1)) = seq (i + j + 1) := rfl
      _ ≤ 9 / 7 * seq (i + j) := hstep
      _ ≤ 9 / 7 * ((9 / 7 : ℝ) ^ j * seq i) := by gcongr
      _ = (9 / 7 : ℝ) ^ (j + 1) * seq i := by ring

#print axioms seq_le_pow

/-- **A reading that sets on lap 1 is not in the way again within three moves.**  A return needs the instant dilated by
more than `(8·1+7)/(8·1+1) = 5/3` since the landing (`return_law`), while two moves dilate by less than `(9/7)^2 = 81/49 < 5/3`
(`seq_le_pow`).  This is the same `81/49` as in `reach_two`; it is why a first-lap return needs at least three other
moves in between, hence (with the per-lap decrease) readings that are not all first-lap setters. -/
theorem lap_one_return_gap {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} {x : ℝ}
    (hx : IsSetterAt E seq n x) (hlap : lap x (seq n) = 1) (hk : n < k) (hw : InWay x (seq k)) : n + 4 ≤ k := by
  -- [PROVISIONAL: counting tool] the statement counts moves between two visits of one reading; the count is a derived
  -- consequence of the dilation bounds `(9/7)^2 < 5/3`, used to explain `reach_two` and the break at four readings,
  -- not a budget.
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  have hret := return_law hpos h0pos hmv hk hx hw
  rw [hlap] at hret
  by_contra hcon
  have hk3 : k ≤ n + 3 := by omega
  have hap : 0 < seq (n + 1) := lt_of_lt_of_le h0pos (start_le_seq hpos hmv (n + 1))
  have hle : seq k ≤ 81 / 49 * seq (n + 1) := by
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    have hj2 : j ≤ 2 := by omega
    have := seq_le_pow hm hlow h0 hmv (n + 1) j
    rw [hj]
    refine this.trans ?_
    interval_cases j <;> norm_num <;> nlinarith
  norm_num at hret
  nlinarith

#print axioms lap_one_return_gap

/-! ## (5) Two readings -/

/-- **Two readings `≥ m` have a lonely instant in `R ∈ [1, 81/49]`.**  The cascade from `1/(8m)`: setters alternate
(`setter_not_twice_in_row`) and `E` has two members, so a third move is set by the first setter again; then
`triple_law` gives `3 a₂ < a₁` and `6 i ≤ 2 j`, and a fourth move would be set by `a₂` returning, giving `3 a₁ < a₂`:
a contradiction.  So the cascade fixes at `seq 3` at the latest.  Bounds: two moves multiply by less than `(9/7)²`; three
moves have `i ≥ 1`, hence `j ≥ 3`, hence factors `< 25/23`, `< 9/7`, `< 33/31`, product `7425/4991 < 81/49`.
`81/49` is the exact supremum (`E = {7⁺, (49/9)⁺}`; see the data in the header).  No move count is assumed: the number of
moves is the output of `triple_law`.  [PROVISIONAL: covering] two readings cannot shadow `[1, 81/49]`; this supports
`Reach 5 6` only through the chain of `Reach k` statements. -/
theorem reach_two : Reach 2 (81 / 49) := by
  intro E m hE hm hlow
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ht0 : 0 < 1 / (8 * m) := by positivity
  set seq : ℕ → ℝ := cascadeSeq E (1 / (8 * m)) with hseq
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < seq 0 := by rw [h0]; exact ht0
  have hmv : ∀ n, IsMove E (seq n) (seq (n + 1)) := cascadeSeq_isMove E _
  have hb : ∀ n, 1 / (8 * m) ≤ seq n := fun n => h0 ▸ start_le_seq hpos hmv n
  have s9 : ∀ n x, IsSetterAt E seq n x → seq (n + 1) < 9 / 7 * seq n := fun n x hx => step_nine hm hlow h0 hmv hx
  -- [PROVISIONAL: counting tool] the case split below is on the number of moves (at most three); that number is DERIVED:
  -- a fourth move would be a return of `a₂` after one move, giving `3 a₁ < a₂` against `3 a₂ < a₁` (`triple_law`).
  -- Supports `Reach 2 (81/49)`, a covering step towards `Reach 5 6` and `Types.StrongGate`.
  -- finishing: a lonely seq n with seq n ≤ c * seq 0, c ≤ 81/49
  have fin : ∀ n, (∀ d ∈ E, ¬ InWay d (seq n)) → ∀ c : ℝ, c ≤ 81 / 49 → seq n ≤ c * seq 0 →
      ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 81 / 49 / (8 * m) ∧ LonelyAt E s := by
    intro n hn c hc hle
    exact ⟨seq n, hb n, le_bound hm hc (by rw [h0] at hle; exact hle), lonely_of_notInWay hn⟩
  by_cases c0 : ∀ d ∈ E, ¬ InWay d (seq 0)
  · exact fin 0 c0 1 (by norm_num) (by linarith)
  obtain ⟨a1, h1⟩ := exists_setter hmv c0
  by_cases c1 : ∀ d ∈ E, ¬ InWay d (seq 1)
  · have := s9 0 a1 h1
    exact fin 1 c1 (9 / 7) (by norm_num) this.le
  obtain ⟨a2, h2⟩ := exists_setter hmv c1
  have ne21 : a2 ≠ a1 := by
    intro h
    exact setter_not_twice_in_row hpos h1 (h ▸ h2)
  by_cases c2 : ∀ d ∈ E, ¬ InWay d (seq 2)
  · have e1 := s9 0 a1 h1
    have e2 := s9 1 a2 h2
    exact fin 2 c2 (81 / 49) le_rfl (by nlinarith)
  obtain ⟨a3, h3⟩ := exists_setter hmv c2
  have ne32 : a3 ≠ a2 := by
    intro h
    exact setter_not_twice_in_row hpos h2 (h ▸ h3)
  have e31 : a1 = a3 := eq_of_card_le_two hE h1.1 h2.1 h3.1 (Ne.symm ne21) (Ne.symm ne32)
  subst e31
  obtain ⟨T1, T2, T3⟩ := triple_law hpos h0pos hmv h1 h2 h3
  by_cases c3 : ∀ d ∈ E, ¬ InWay d (seq 3)
  · -- bounds on the three factors
    have hi : 1 ≤ lap a2 (seq 1) := one_le_lap_of_bound hm (hlow a2 h2.1) (hb 1) h2.2.1
    have T2' : 6 * lap a2 (seq 1) ≤ 2 * lap a1 (seq 0) := T2
    have T3' : lap a1 (seq 0) + 1 ≤ lap a1 (seq 2) := T3
    have hj3 : 3 ≤ lap a1 (seq 0) := by omega
    have hj4 : 4 ≤ lap a1 (seq 2) := by omega
    have hj3' : (3 : ℝ) ≤ (lap a1 (seq 0) : ℝ) := by exact_mod_cast hj3
    have hj4' : (4 : ℝ) ≤ (lap a1 (seq 2) : ℝ) := by exact_mod_cast hj4
    have f1 := step_lt hpos h0pos hmv h1 (N0 := 3) (by norm_num) hj3'
    have f2 := s9 1 a2 h2
    have f3 := step_lt hpos h0pos hmv h3 (N0 := 4) (by norm_num) hj4'
    norm_num at f1 f3
    have p1 : 0 < seq 1 := lt_of_lt_of_le ht0 (hb 1)
    have p2 : 0 < seq 2 := lt_of_lt_of_le ht0 (hb 2)
    have g1 : seq 2 < 9 / 7 * (25 / 23 * seq 0) := by nlinarith
    have g2 : seq 3 < 33 / 31 * (9 / 7 * (25 / 23 * seq 0)) := by nlinarith
    exact fin 3 c3 (33 / 31 * (9 / 7 * (25 / 23))) (by norm_num) (by nlinarith)
  · obtain ⟨a4, h4⟩ := exists_setter hmv c3
    have ne43 : a4 ≠ a1 := by
      intro h
      exact setter_not_twice_in_row hpos h3 (h ▸ h4)
    have e42 : a2 = a4 := eq_of_card_le_two hE h2.1 h3.1 h4.1 (Ne.symm ne32) (Ne.symm ne43)
    subst e42
    obtain ⟨U1, -, -⟩ := triple_law hpos h0pos hmv h2 h3 h4
    have := hpos a2 h2.1
    have := hpos a1 h1.1
    linarith

#print axioms reach_two

/-! ## (6) Lower bounds: sets of readings whose zones chain, so no lonely instant lies below a stated `R` -/

/-- A reading `d > 0` is in the way on `[a, b)` when `d·a > N − 1/8` and `d·b ≤ N + 1/8` (its lap-`N` zone). -/
theorem inWay_of_between {d : ℝ} {N : ℤ} {a b s : ℝ} (hd : 0 < d) (ha : (N : ℝ) - 1 / 8 < d * a)
    (hb : d * b ≤ (N : ℝ) + 1 / 8) (h1 : a ≤ s) (h2 : s < b) : InWay d s := by
  have hs1 : d * a ≤ d * s := mul_le_mul_of_nonneg_left h1 hd.le
  have hs2 : d * s < d * b := mul_lt_mul_of_pos_left h2 hd
  unfold InWay
  refine lt_of_le_of_lt (distInt_le (d * s) N) ?_
  rw [abs_lt]
  constructor <;> linarith

#print axioms inWay_of_between

/-- **A covering of `[1/8, T)` by zones gives a lower bound for the reach**: if every instant of `[1/8, T)` has a
reading of `E` in the way, `E` has at most `k` readings and all are `≥ 1`, then `Reach k B` fails for every `B/8 < T`
(in readings: the first lonely instant of `E` from `R = 1` is at `R ≥ 8T`). -/
theorem not_reach_of_cover {k : ℕ} {B T : ℝ} {E : Finset ℝ} (hE : E.card ≤ k) (hlow : ∀ d ∈ E, (1 : ℝ) ≤ d)
    (hcov : ∀ s : ℝ, 1 / 8 ≤ s → s < T → ∃ d ∈ E, InWay d s) (hBT : B / 8 < T) : ¬ Reach k B := by
  intro h
  obtain ⟨s, hs1, hs2, hl⟩ := h E 1 hE one_pos hlow
  norm_num at hs1 hs2
  obtain ⟨d, hd, hw⟩ := hcov s hs1 (lt_of_le_of_lt hs2 hBT)
  exact not_inWay_iff.mpr (hl d hd) hw

#print axioms not_reach_of_cover

/-- **Sharpness of `reach_one`**: for `1 ≤ B < 9/7` the single reading `a ∈ (7, 9/B)` has no lonely instant in `R ∈ [1, B]`. -/
theorem not_reach_one {B : ℝ} (hB1 : 1 ≤ B) (hB : B < 9 / 7) : ¬ Reach 1 B := by
  have hB0 : 0 < B := by linarith
  have h9 : 7 < 9 / B := by rw [lt_div_iff₀ hB0]; linarith
  set a : ℝ := (7 + 9 / B) / 2 with ha
  have ha7 : 7 < a := by rw [ha]; linarith
  have haB : a < 9 / B := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  refine not_reach_of_cover (E := {a}) (T := 9 / (8 * a)) (by simp) ?_ ?_ ?_
  · intro d hd; rw [Finset.mem_singleton] at hd; rw [hd]; linarith
  · intro s hs1 hs2
    refine ⟨a, Finset.mem_singleton_self a, ?_⟩
    refine inWay_of_between (N := 1) ha0 ?_ ?_ hs1 hs2
    · push_cast; linarith
    · push_cast; field_simp; norm_num
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    rw [lt_div_iff₀ hB0] at haB
    nlinarith

#print axioms not_reach_one

/-- **Sharpness of `reach_two`**: for `1 ≤ B < 81/49` the two readings `a = 7 + δ`, `b = 7a/9 + δ` have no lonely
instant in `R ∈ [1, B]` (two lap-1 moves, each by almost `9/7`). -/
theorem not_reach_two {B : ℝ} (hB1 : 1 ≤ B) (hB : B < 81 / 49) : ¬ Reach 2 B := by
  have hB0 : 0 < B := by linarith
  set δ : ℝ := (81 - 49 * B) / (32 * B) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  have hδ1 : δ * (32 * B) = 81 - 49 * B := by rw [hδ]; field_simp
  set a : ℝ := 7 + δ with ha
  set b : ℝ := 7 * a / 9 + δ with hb
  have ha7 : 7 < a := by rw [ha]; linarith
  have hab : 7 * a < 9 * b := by rw [hb]; nlinarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have ha0 : 0 < a := by linarith
  have hbB : b * B < 9 := by
    rw [hb, ha]; nlinarith
  have hb1 : 1 ≤ b := by rw [hb, ha]; nlinarith
  refine not_reach_of_cover (E := {a, b}) (T := 9 / (8 * b)) (Finset.card_le_two) ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> linarith
  · intro s hs1 hs2
    rcases lt_or_ge s (9 / (8 * a)) with h | g
    · refine ⟨a, by simp, inWay_of_between (N := 1) ha0 ?_ ?_ hs1 h⟩
      · push_cast; linarith
      · push_cast; field_simp; norm_num
    · refine ⟨b, by simp, inWay_of_between (N := 1) hb0 ?_ ?_ g hs2⟩
      · push_cast
        rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
        nlinarith
      · push_cast; field_simp; norm_num
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith

#print axioms not_reach_two

/-- **Sharpness of the three-reading bound `729/343`**: for `1 ≤ B < 729/343` the readings `a = 7 + δ`,
`b = 7a/9 + δ`, `c = 7b/9 + δ` have no lonely instant in `R ∈ [1, B]` (three lap-1 moves).  This is the lower bound
for `Reach 3`; its upper bound is OWED (`Reach3Sharp` below). -/
theorem not_reach_three {B : ℝ} (hB1 : 1 ≤ B) (hB : B < 729 / 343) : ¬ Reach 3 B := by
  have hB0 : 0 < B := by linarith
  set δ : ℝ := (729 - 343 * B) / (200 * B) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  have hδ1 : δ * (200 * B) = 729 - 343 * B := by rw [hδ]; field_simp
  set a : ℝ := 7 + δ with ha
  set b : ℝ := 7 * a / 9 + δ with hb
  set c : ℝ := 7 * b / 9 + δ with hc
  have ha7 : 7 < a := by rw [ha]; linarith
  have hab : 7 * a < 9 * b := by rw [hb]; nlinarith
  have hbc : 7 * b < 9 * c := by rw [hc]; nlinarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcB : c * B < 9 := by
    rw [hc, hb, ha]; nlinarith
  have hb1 : 1 ≤ b := by rw [hb, ha]; nlinarith
  have hc1 : 1 ≤ c := by rw [hc, hb, ha]; nlinarith
  refine not_reach_of_cover (E := {a, b, c}) (T := 9 / (8 * c)) (Finset.card_le_three) ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> linarith
  · intro s hs1 hs2
    rcases lt_or_ge s (9 / (8 * a)) with h | g
    · refine ⟨a, by simp, inWay_of_between (N := 1) ha0 ?_ ?_ hs1 h⟩
      · push_cast; linarith
      · push_cast; field_simp; norm_num
    rcases lt_or_ge s (9 / (8 * b)) with h' | g'
    · refine ⟨b, by simp, inWay_of_between (N := 1) hb0 ?_ ?_ g h'⟩
      · push_cast
        rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
        nlinarith
      · push_cast; field_simp; norm_num
    · refine ⟨c, by simp, inWay_of_between (N := 1) hc0 ?_ ?_ g' hs2⟩
      · push_cast
        rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
        nlinarith
      · push_cast; field_simp; norm_num
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith

#print axioms not_reach_three

/-! ### Exact witnesses (generated from the exact cascade; each covering step is `norm_num` on rational literals) -/

/-- Five rational readings, all at least `1`, whose zones chain over `R ∈ [1, 6250/1421)` (about `4.3983`), 12 cascade moves with laps `1,1,1,1,2,2,2,2,3,3,2,3`. -/
noncomputable def E_five : Finset ℝ := {(6441 / 1000 : ℝ), (7001 / 1000 : ℝ), (627 / 125 : ℝ), (1951 / 500 : ℝ), (1421 / 250 : ℝ)}

/-- Every instant of `[1/8, (3125 / 5684 : ℝ))` has a reading of `E_five` in the way (the cascade's zones chain: 12 moves). -/
theorem cover_five : ∀ s : ℝ, 1 / 8 ≤ s → s < (3125 / 5684 : ℝ) → ∃ d ∈ E_five, InWay d s := by
  intro s h0 hT
  rcases lt_or_ge s (1125 / 7001 : ℝ) with h1 | g1
  · exact ⟨(7001 / 1000 : ℝ), by simp [E_five], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) h0 h1⟩
  rcases lt_or_ge s (1125 / 5684 : ℝ) with h2 | g2
  · exact ⟨(1421 / 250 : ℝ), by simp [E_five], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g1 h2⟩
  rcases lt_or_ge s (375 / 1672 : ℝ) with h3 | g3
  · exact ⟨(627 / 125 : ℝ), by simp [E_five], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g2 h3⟩
  rcases lt_or_ge s (1125 / 3902 : ℝ) with h4 | g4
  · exact ⟨(1951 / 500 : ℝ), by simp [E_five], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g3 h4⟩
  rcases lt_or_ge s (2125 / 7001 : ℝ) with h5 | g5
  · exact ⟨(7001 / 1000 : ℝ), by simp [E_five], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g4 h5⟩
  rcases lt_or_ge s (2125 / 6441 : ℝ) with h6 | g6
  · exact ⟨(6441 / 1000 : ℝ), by simp [E_five], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g5 h6⟩
  rcases lt_or_ge s (2125 / 5684 : ℝ) with h7 | g7
  · exact ⟨(1421 / 250 : ℝ), by simp [E_five], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g6 h7⟩
  rcases lt_or_ge s (2125 / 5016 : ℝ) with h8 | g8
  · exact ⟨(627 / 125 : ℝ), by simp [E_five], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g7 h8⟩
  rcases lt_or_ge s (3125 / 7001 : ℝ) with h9 | g9
  · exact ⟨(7001 / 1000 : ℝ), by simp [E_five], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g8 h9⟩
  rcases lt_or_ge s (3125 / 6441 : ℝ) with h10 | g10
  · exact ⟨(6441 / 1000 : ℝ), by simp [E_five], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g9 h10⟩
  rcases lt_or_ge s (2125 / 3902 : ℝ) with h11 | g11
  · exact ⟨(1951 / 500 : ℝ), by simp [E_five], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g10 h11⟩
  exact ⟨(1421 / 250 : ℝ), by simp [E_five], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g11 hT⟩

theorem card_E_five : E_five.card ≤ 5 := by
  unfold E_five; exact Finset.card_le_five

theorem low_E_five : ∀ d ∈ E_five, (1 : ℝ) ≤ d := by
  intro d hd
  simp only [E_five, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem not_reach_five : ¬ Reach 5 (4398 / 1000) :=
  not_reach_of_cover card_E_five low_E_five cover_five (by norm_num)

/-- Six rational readings, all at least `1`, whose zones chain over `R ∈ [1, 4900000/562313)` (about `8.714`), 20 cascade moves. -/
noncomputable def E_six : Finset ℝ := {(700251 / 100000 : ℝ), (7809 / 3125 : ℝ), (562313 / 100000 : ℝ), (19899 / 6250 : ℝ), (197403 / 50000 : ℝ), (88263 / 20000 : ℝ)}

/-- Every instant of `[1/8, (612500 / 562313 : ℝ))` has a reading of `E_six` in the way (the cascade's zones chain: 20 moves). -/
theorem cover_six : ∀ s : ℝ, 1 / 8 ≤ s → s < (612500 / 562313 : ℝ) → ∃ d ∈ E_six, InWay d s := by
  intro s h0 hT
  rcases lt_or_ge s (37500 / 233417 : ℝ) with h1 | g1
  · exact ⟨(700251 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) h0 h1⟩
  rcases lt_or_ge s (112500 / 562313 : ℝ) with h2 | g2
  · exact ⟨(562313 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g1 h2⟩
  rcases lt_or_ge s (2500 / 9807 : ℝ) with h3 | g3
  · exact ⟨(88263 / 20000 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g2 h3⟩
  rcases lt_or_ge s (18750 / 65801 : ℝ) with h4 | g4
  · exact ⟨(197403 / 50000 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g3 h4⟩
  rcases lt_or_ge s (3125 / 8844 : ℝ) with h5 | g5
  · exact ⟨(19899 / 6250 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g4 h5⟩
  rcases lt_or_ge s (9375 / 20824 : ℝ) with h6 | g6
  · exact ⟨(7809 / 3125 : ℝ), by simp [E_six], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g5 h6⟩
  rcases lt_or_ge s (42500 / 88263 : ℝ) with h7 | g7
  · exact ⟨(88263 / 20000 : ℝ), by simp [E_six], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g6 h7⟩
  rcases lt_or_ge s (106250 / 197403 : ℝ) with h8 | g8
  · exact ⟨(197403 / 50000 : ℝ), by simp [E_six], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g7 h8⟩
  rcases lt_or_ge s (312500 / 562313 : ℝ) with h9 | g9
  · exact ⟨(562313 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g8 h9⟩
  rcases lt_or_ge s (137500 / 233417 : ℝ) with h10 | g10
  · exact ⟨(700251 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 4) (by norm_num) (by norm_num) (by norm_num) g9 h10⟩
  rcases lt_or_ge s (53125 / 79596 : ℝ) with h11 | g11
  · exact ⟨(19899 / 6250 : ℝ), by simp [E_six], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g10 h11⟩
  rcases lt_or_ge s (62500 / 88263 : ℝ) with h12 | g12
  · exact ⟨(88263 / 20000 : ℝ), by simp [E_six], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g11 h12⟩
  rcases lt_or_ge s (412500 / 562313 : ℝ) with h13 | g13
  · exact ⟨(562313 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 4) (by norm_num) (by norm_num) (by norm_num) g12 h13⟩
  rcases lt_or_ge s (156250 / 197403 : ℝ) with h14 | g14
  · exact ⟨(197403 / 50000 : ℝ), by simp [E_six], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g13 h14⟩
  rcases lt_or_ge s (53125 / 62472 : ℝ) with h15 | g15
  · exact ⟨(7809 / 3125 : ℝ), by simp [E_six], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g14 h15⟩
  rcases lt_or_ge s (612500 / 700251 : ℝ) with h16 | g16
  · exact ⟨(700251 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 6) (by norm_num) (by norm_num) (by norm_num) g15 h16⟩
  rcases lt_or_ge s (512500 / 562313 : ℝ) with h17 | g17
  · exact ⟨(562313 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 5) (by norm_num) (by norm_num) (by norm_num) g16 h17⟩
  rcases lt_or_ge s (78125 / 79596 : ℝ) with h18 | g18
  · exact ⟨(19899 / 6250 : ℝ), by simp [E_six], inWay_of_between (N := 3) (by norm_num) (by norm_num) (by norm_num) g17 h18⟩
  rcases lt_or_ge s (68750 / 65801 : ℝ) with h19 | g19
  · exact ⟨(197403 / 50000 : ℝ), by simp [E_six], inWay_of_between (N := 4) (by norm_num) (by norm_num) (by norm_num) g18 h19⟩
  exact ⟨(562313 / 100000 : ℝ), by simp [E_six], inWay_of_between (N := 6) (by norm_num) (by norm_num) (by norm_num) g19 hT⟩

theorem card_E_six : E_six.card ≤ 6 := by
  unfold E_six; exact Finset.card_le_six

theorem low_E_six : ∀ d ∈ E_six, (1 : ℝ) ≤ d := by
  intro d hd
  simp only [E_six, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem not_reach_six : ¬ Reach 6 (8) :=
  not_reach_of_cover card_E_six low_E_six cover_six (by norm_num)

#print axioms cover_five
#print axioms not_reach_five
#print axioms cover_six
#print axioms not_reach_six

/-- Four rational readings, all at least `1`, whose zones chain over `R ∈ [1, 8500/3089)` (about `2.7517`), 6 cascade moves with laps `1,1,1,1,2,2`; the pure lap-1 value is `(9/7)^4 ≈ 2.7328`. -/
noncomputable def E_four : Finset ℝ := {(3089 / 500 : ℝ), (3739 / 1000 : ℝ), (7001 / 1000 : ℝ), (2403 / 500 : ℝ)}

/-- Every instant of `[1/8, (2125 / 6178 : ℝ))` has a reading of `E_four` in the way (the cascade's zones chain: 6 moves). -/
theorem cover_four : ∀ s : ℝ, 1 / 8 ≤ s → s < (2125 / 6178 : ℝ) → ∃ d ∈ E_four, InWay d s := by
  intro s h0 hT
  rcases lt_or_ge s (1125 / 7001 : ℝ) with h1 | g1
  · exact ⟨(7001 / 1000 : ℝ), by simp [E_four], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) h0 h1⟩
  rcases lt_or_ge s (1125 / 6178 : ℝ) with h2 | g2
  · exact ⟨(3089 / 500 : ℝ), by simp [E_four], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g1 h2⟩
  rcases lt_or_ge s (125 / 534 : ℝ) with h3 | g3
  · exact ⟨(2403 / 500 : ℝ), by simp [E_four], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g2 h3⟩
  rcases lt_or_ge s (1125 / 3739 : ℝ) with h4 | g4
  · exact ⟨(3739 / 1000 : ℝ), by simp [E_four], inWay_of_between (N := 1) (by norm_num) (by norm_num) (by norm_num) g3 h4⟩
  rcases lt_or_ge s (2125 / 7001 : ℝ) with h5 | g5
  · exact ⟨(7001 / 1000 : ℝ), by simp [E_four], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g4 h5⟩
  exact ⟨(3089 / 500 : ℝ), by simp [E_four], inWay_of_between (N := 2) (by norm_num) (by norm_num) (by norm_num) g5 hT⟩

theorem card_E_four : E_four.card ≤ 4 := by
  unfold E_four; exact Finset.card_le_four

theorem low_E_four : ∀ d ∈ E_four, (1 : ℝ) ≤ d := by
  intro d hd
  simp only [E_four, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> norm_num

theorem not_reach_four : ¬ Reach 4 (2751 / 1000) :=
  not_reach_of_cover card_E_four low_E_four cover_four (by norm_num)

#print axioms cover_four
#print axioms not_reach_four

/-- **Four readings break the pure lap-1 value**: `Reach 4 B` fails for `B ≤ 2751/1000`, in particular for `B = (9/7)^4`
(`≈ 2.7328`).  The extra comes from the two lap-2 moves at the end of the chain; compare `reach_three`, where
`(9/7)^3` is exact. -/
theorem not_reach_four_pure : ¬ Reach 4 (6561 / 2401) :=
  fun h => not_reach_four (reach_mono_bound (by norm_num) h)

#print axioms not_reach_four_pure

/-- **The six-reading analogue of `FiveReach` is false**: `Reach 6 6` fails (the set `E_six` has no lonely instant in
`R ∈ [1, 8.7)`).  Exception understood by naming the pattern: the cascade of `E_six` has twenty moves, laps
`1,1,1,1,1,1,2,2,3,4,2,3,4,3,2,6,5,3,4,6`; with five readings the best chain found stops at `R ≈ 4.4`. -/
theorem not_reach_six_six : ¬ Reach 6 6 := fun h => not_reach_six (reach_mono_bound (by norm_num) h)

#print axioms not_reach_six_six

/-- **Lower bound for the five-reading reach**: `Reach 5 B` fails for `B ≤ 4398/1000` (exact rational witness). -/
theorem not_reach_five_le {B : ℝ} (hB : B ≤ 4398 / 1000) : ¬ Reach 5 B :=
  fun h => not_reach_five (reach_mono_bound hB h)

#print axioms not_reach_five_le

/-! ## (7) Three readings: a union bound in the measure `dR/R` -/


/-- the clipped ratio is monotone in the left clip: a larger denominator gives a smaller `max 1 (a / D)`. -/
theorem max_one_div_mono {a D D' : ℝ} (hD : 0 < D) (hDD : D ≤ D') : max 1 (a / D') ≤ max 1 (a / D) := by
  rcases le_or_gt 0 a with ha | ha
  · exact max_le_max le_rfl (div_le_div_of_nonneg_left ha hD hDD)
  · have : a / D' < 0 := div_neg_of_neg_of_pos ha (lt_of_lt_of_le hD hDD)
    exact max_le (le_max_left _ _) (by linarith [le_max_left (1 : ℝ) (a / D)])

/-- **Finite covering lemma (multiplicative form).**  If finitely many open intervals `(lo i, hi i)` cover `[c, d]`
(`0 < c ≤ d`), then `d / c` is at most the product of their clipped ratios `max 1 (min d (hi i) / max c (lo i))`.
Induction on the family: the interval through `c` is used once and the rest covers `[hi i0, d]`. -/
theorem cover_prod {ι : Type*} (S : Finset ι) (lo hi : ι → ℝ) :
    ∀ (c d : ℝ), 0 < c → c ≤ d → (∀ s, c ≤ s → s ≤ d → ∃ i ∈ S, lo i < s ∧ s < hi i) →
      d / c ≤ ∏ i ∈ S, max 1 (min d (hi i) / max c (lo i)) := by
  induction S using Finset.strongInduction with
  | H S ih =>
  intro c d hc hcd hcov
  obtain ⟨i0, hi0, hlo0, hhi0⟩ := hcov c le_rfl hcd
  rw [← Finset.mul_prod_erase S _ hi0]
  have hrest : 1 ≤ ∏ i ∈ S.erase i0, max 1 (min d (hi i) / max c (lo i)) := by
    calc (1 : ℝ) = ∏ i ∈ S.erase i0, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => le_max_left _ _)
  have hmaxc : max c (lo i0) = c := max_eq_left hlo0.le
  have hd0 : 0 ≤ d / c := div_nonneg (hc.le.trans hcd) hc.le
  by_cases hd : d ≤ hi i0
  · have hf : max 1 (min d (hi i0) / max c (lo i0)) = d / c := by
      rw [min_eq_left hd, hmaxc]
      exact max_eq_right ((one_le_div hc).mpr hcd)
    rw [hf]
    calc d / c = d / c * 1 := by ring
      _ ≤ d / c * ∏ i ∈ S.erase i0, max 1 (min d (hi i) / max c (lo i)) :=
        mul_le_mul_of_nonneg_left hrest hd0
  · have hd' : hi i0 < d := not_le.mp hd
    have hc' : 0 < hi i0 := lt_trans hc hhi0
    have hcov' : ∀ s, hi i0 ≤ s → s ≤ d → ∃ i ∈ S.erase i0, lo i < s ∧ s < hi i := by
      intro s hs1 hs2
      obtain ⟨i, hi', h1, h2⟩ := hcov s (hhi0.le.trans hs1) hs2
      refine ⟨i, Finset.mem_erase.mpr ⟨?_, hi'⟩, h1, h2⟩
      rintro rfl
      linarith
    have IH := ih (S.erase i0) (Finset.erase_ssubset hi0) (hi i0) d hc' hd'.le hcov'
    have hmono : ∏ i ∈ S.erase i0, max 1 (min d (hi i) / max (hi i0) (lo i)) ≤
        ∏ i ∈ S.erase i0, max 1 (min d (hi i) / max c (lo i)) := by
      refine Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_left _ _)) (fun i _ => ?_)
      exact max_one_div_mono (lt_of_lt_of_le hc (le_max_left _ _)) (max_le_max hhi0.le le_rfl)
    have hf : max 1 (min d (hi i0) / max c (lo i0)) = hi i0 / c := by
      rw [min_eq_right hd'.le, hmaxc]
      exact max_eq_right ((one_le_div hc).mpr hhi0.le)
    rw [hf]
    have hne : hi i0 ≠ 0 := hc'.ne'
    have hne' : c ≠ 0 := hc.ne'
    calc d / c = (d / hi i0) * (hi i0 / c) := by field_simp
      _ ≤ (∏ i ∈ S.erase i0, max 1 (min d (hi i) / max (hi i0) (lo i))) * (hi i0 / c) :=
        mul_le_mul_of_nonneg_right IH (by positivity)
      _ ≤ (∏ i ∈ S.erase i0, max 1 (min d (hi i) / max c (lo i))) * (hi i0 / c) :=
        mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = hi i0 / c * ∏ i ∈ S.erase i0, max 1 (min d (hi i) / max c (lo i)) := mul_comm _ _




/-- The ratio of the ends of the lap-`N` zone: `qz N = (8N+1)/(8N−1)`. -/
noncomputable def qz (N : ℕ) : ℝ := (8 * (N : ℝ) + 1) / (8 * (N : ℝ) - 1)

theorem qz_ge_one {N : ℕ} (hN : 1 ≤ N) : 1 ≤ qz N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold qz
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem qz_le_nine_sevenths {N : ℕ} (hN : 1 ≤ N) : qz N ≤ 9 / 7 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold qz
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Fourth-power telescoping inequality**: `qz N ^ 4 ≤ (2N+1)/(2N−1)`.  (Difference of cross-multiplied sides
is `640 N² + 2`.) -/
theorem qz_pow_four_le {N : ℕ} (hN : 1 ≤ N) : qz N ^ 4 ≤ (2 * (N : ℝ) + 1) / (2 * (N : ℝ) - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold qz
  rw [div_pow, div_le_div_iff₀ (pow_pos (by linarith) 4) (by linarith)]
  nlinarith [sq_nonneg (N : ℝ), mul_pos (by linarith : (0:ℝ) < 8 * N - 1) (by linarith : (0:ℝ) < 8 * N - 1)]

/-- **Telescoping**: for `1 ≤ a < b`, `(∏_{a<N<b} qz N)^4 ≤ (2b−1)/(2a+1)`. -/
theorem prod_qz_pow_four_le {a : ℕ} (ha : 1 ≤ a) : ∀ b : ℕ, a < b →
    (∏ N ∈ Finset.Ioo a b, qz N) ^ 4 ≤ (2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1) := by
  intro b hab
  induction b, Nat.succ_le_of_lt hab using Nat.le_induction with
  | base =>
    have : Finset.Ioo a (a + 1) = ∅ := by
      ext x; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [this, Finset.prod_empty]
    have : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
    rw [one_pow, le_div_iff₀ this]; push_cast; linarith
  | succ b hb ih =>
    have hab' : a < b := hb
    have hI : Finset.Ioo a (b + 1) = insert b (Finset.Ioo a b) := by
      ext x; simp [Finset.mem_Ioo, Finset.mem_insert]; omega
    have hbnot : b ∉ Finset.Ioo a b := by simp
    rw [hI, Finset.prod_insert hbnot, mul_pow]
    have hq := qz_pow_four_le (N := b) (by omega)
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
    have ha' : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
    have hd : (0 : ℝ) < 2 * (b : ℝ) - 1 := by linarith
    have hprod0 : 0 ≤ (∏ N ∈ Finset.Ioo a b, qz N) ^ 4 := by positivity
    calc qz b ^ 4 * (∏ N ∈ Finset.Ioo a b, qz N) ^ 4
        ≤ ((2 * (b : ℝ) + 1) / (2 * (b : ℝ) - 1)) * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) := by
          apply mul_le_mul hq (ih hab') hprod0 (by positivity)
      _ = (2 * ((b + 1 : ℕ) : ℝ) - 1) / (2 * (a : ℝ) + 1) := by
          push_cast; field_simp; ring

theorem one_le_prod_qz (a b : ℕ) (ha : 1 ≤ a) : 1 ≤ ∏ N ∈ Finset.Ioo a b, qz N := by
  calc (1 : ℝ) = ∏ N ∈ Finset.Ioo a b, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun N hN => qz_ge_one (by
        have := (Finset.mem_Ioo.mp hN).1; omega))



/-- big-`a` polynomial inequality -/
theorem big_poly {t : ℝ} (ht : 0 ≤ t) :
    (15 / 7 : ℝ) ^ 4 * (8 * (18 + t) + 1) ^ 4 ≤
      4 * (9 / 7 : ℝ) ^ 4 * (2 * (18 + t) + 1) * ((120 * (18 + t) - 161) / 7) ^ 3 := by
  have : 0 ≤ 4 * (9 / 7 : ℝ) ^ 4 * (2 * (18 + t) + 1) * ((120 * (18 + t) - 161) / 7) ^ 3 -
      (15 / 7 : ℝ) ^ 4 * (8 * (18 + t) + 1) ^ 4 := by
    ring_nf
    positivity
  linarith

/-- large `a`: the first branch holds for every admissible `b`. -/
theorem abint_big {a b : ℕ} (ha : 18 ≤ a) (hab : a < b) (F2 : 120 * a ≤ 56 * b + 154) :
    ((15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1)) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) ≤
      (9 / 7 : ℝ) ^ 4 := by
  have ha' : (18 : ℝ) ≤ a := by exact_mod_cast ha
  have hF2 : (120 * (a : ℝ) - 154) ≤ 56 * b := by
    have : (120 * a : ℕ) ≤ 56 * b + 154 := F2
    have h2 : ((120 * a : ℕ) : ℝ) ≤ ((56 * b + 154 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2; linarith
  set X : ℝ := 8 * (b : ℝ) - 1 with hX
  set X0 : ℝ := (120 * (a : ℝ) - 161) / 7 with hX0
  have hXX0 : X0 ≤ X := by rw [hX, hX0]; linarith
  have hX0pos : 0 < X0 := by rw [hX0]; linarith
  have hXpos : 0 < X := lt_of_lt_of_le hX0pos hXX0
  have hapos : (0 : ℝ) < 2 * a + 1 := by positivity
  have hb2 : 2 * (b : ℝ) - 1 ≤ X / 4 := by rw [hX]; linarith
  have hb2pos : 0 < 2 * (b : ℝ) - 1 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
    linarith
  -- polynomial inequality at X0
  have hpoly : (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 ≤ 4 * (9 / 7 : ℝ) ^ 4 * (2 * (a : ℝ) + 1) * X0 ^ 3 := by
    have := big_poly (t := (a : ℝ) - 18) (by linarith)
    have e : (18 : ℝ) + ((a : ℝ) - 18) = a := by ring
    rw [e] at this
    rw [hX0]; exact this
  have hX03 : X0 ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hX0pos.le hXX0 3
  have hmain : (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 * (2 * (b : ℝ) - 1) ≤
      (9 / 7 : ℝ) ^ 4 * (2 * (a : ℝ) + 1) * X ^ 4 := by
    have h1 : (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 * (2 * (b : ℝ) - 1) ≤
        (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 * (X / 4) :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    have h2 : (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 * (X / 4) ≤
        4 * (9 / 7 : ℝ) ^ 4 * (2 * (a : ℝ) + 1) * X ^ 3 * (X / 4) :=
      mul_le_mul_of_nonneg_right (hpoly.trans (by
        have := mul_le_mul_of_nonneg_left hX03 (by positivity : (0:ℝ) ≤ 4 * (9 / 7 : ℝ) ^ 4 * (2 * (a : ℝ) + 1))
        exact this)) (by positivity)
    nlinarith [h1, h2]
  rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
  have e : (15 / 7 : ℝ) / (1 : ℝ) = 15 / 7 := by norm_num
  calc ((15 / 7 : ℝ) * (8 * (a : ℝ) + 1)) ^ 4 * (2 * (b : ℝ) - 1)
      = (15 / 7 : ℝ) ^ 4 * (8 * (a : ℝ) + 1) ^ 4 * (2 * (b : ℝ) - 1) := by ring
    _ ≤ (9 / 7 : ℝ) ^ 4 * (2 * (a : ℝ) + 1) * X ^ 4 := hmain
    _ = (9 / 7 : ℝ) ^ 4 * (X ^ 4 * (2 * (a : ℝ) + 1)) := by ring



/-- small `a`: finite check; one of the two branches holds. -/
theorem abint_small {a b : ℕ} (ha : 1 ≤ a) (ha17 : a ≤ 17) (hab : a < b) (F1 : 56 * b < 120 * a + 22)
    (F2 : 120 * a ≤ 56 * b + 154) :
    ((15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1)) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) ≤
        (9 / 7 : ℝ) ^ 4 ∨
      (qz a * qz b) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) ≤ (9 / 7 : ℝ) ^ 4 := by
  interval_cases a <;>
  · have hb : b < 40 := by omega
    interval_cases b <;> first
      | (exfalso; omega)
      | (left; norm_num; done)
      | (right; norm_num [qz])


/-- The combined branch statement for a pair `(a, b)` of boundary zones. -/
theorem abint {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (F1 : 56 * b < 120 * a + 22) (F2 : 120 * a ≤ 56 * b + 154) :
    ((15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1)) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) ≤
        (9 / 7 : ℝ) ^ 4 ∨
      (qz a * qz b) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) ≤ (9 / 7 : ℝ) ^ 4 := by
  by_cases ha17 : a ≤ 17
  · exact abint_small ha ha17 hab F1 F2
  · exact Or.inl (abint_big (by omega) hab F2)

/-! ### The clipped zone ratio of a reading `x` on lap `N`, in the coordinate `R` and window `[1, 15/7]` -/

/-- `zr x N`: the clipped ratio of the lap-`N` zone `((8N−1)/x, (8N+1)/x)` of the reading `x` against the window
`[1, 15/7]` (floored at `1`). -/
noncomputable def zr (x : ℝ) (N : ℕ) : ℝ :=
  max 1 (min (15 / 7) ((8 * (N : ℝ) + 1) / x) / max 1 ((8 * (N : ℝ) - 1) / x))

theorem zr_ge_one (x : ℝ) (N : ℕ) : 1 ≤ zr x N := le_max_left _ _

theorem zr_eq_one_of_low {x : ℝ} {N : ℕ} (_hx : 0 < x) (h : (8 * (N : ℝ) + 1) / x ≤ 1) : zr x N = 1 := by
  unfold zr
  apply max_eq_left
  apply div_le_one_of_le₀
  · exact le_trans (min_le_right _ _) (h.trans (le_max_left _ _))
  · exact le_trans zero_le_one (le_max_left _ _)

theorem zr_eq_one_of_high {x : ℝ} {N : ℕ} (_hx : 0 < x) (h : 15 / 7 ≤ (8 * (N : ℝ) - 1) / x) : zr x N = 1 := by
  unfold zr
  apply max_eq_left
  apply div_le_one_of_le₀
  · exact le_trans (min_le_left _ _) (h.trans (le_max_right _ _))
  · exact le_trans zero_le_one (le_max_left _ _)

theorem zr_le_qz {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : 1 ≤ N) : zr x N ≤ qz N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu : 0 < (8 * (N : ℝ) - 1) / x := div_pos (by linarith) hx
  have hv : 0 < (8 * (N : ℝ) + 1) / x := div_pos (by linarith) hx
  have hq : (8 * (N : ℝ) + 1) / x / ((8 * (N : ℝ) - 1) / x) = qz N := by
    unfold qz; field_simp
  unfold zr
  apply max_le (qz_ge_one hN)
  rw [← hq]
  apply div_le_div₀ hv.le (min_le_right _ _) hu (le_max_right _ _)

theorem zr_le_v {x : ℝ} {N : ℕ} (hx : 0 < x) : zr x N ≤ max 1 ((8 * (N : ℝ) + 1) / x) := by
  unfold zr
  refine max_le_max le_rfl ?_
  calc min (15 / 7) ((8 * (N : ℝ) + 1) / x) / max 1 ((8 * (N : ℝ) - 1) / x)
      ≤ min (15 / 7) ((8 * (N : ℝ) + 1) / x) / 1 := by
        apply div_le_div_of_nonneg_left (le_min (by norm_num) (div_nonneg (by positivity) hx.le)) one_pos (le_max_left _ _)
    _ ≤ (8 * (N : ℝ) + 1) / x := by rw [div_one]; exact min_le_right _ _

theorem zr_le_Bu {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : 1 ≤ N) :
    zr x N ≤ max 1 (15 / 7 * x / (8 * (N : ℝ) - 1)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu : 0 < (8 * (N : ℝ) - 1) / x := div_pos (by linarith) hx
  unfold zr
  refine max_le_max le_rfl ?_
  have e : 15 / 7 * x / (8 * (N : ℝ) - 1) = 15 / 7 / ((8 * (N : ℝ) - 1) / x) := by
    field_simp
  rw [e]
  have hv : 0 < (8 * (N : ℝ) + 1) / x := div_pos (by linarith) hx
  exact div_le_div₀ (by norm_num) (min_le_left _ _) hu (le_max_right _ _)

theorem zr_eq_qz {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : 1 ≤ N) (h1 : 1 ≤ (8 * (N : ℝ) - 1) / x)
    (h2 : (8 * (N : ℝ) + 1) / x ≤ 15 / 7) : zr x N = qz N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : (8 * (N : ℝ) + 1) / x / ((8 * (N : ℝ) - 1) / x) = qz N := by
    unfold qz; field_simp
  unfold zr
  rw [min_eq_right h2, max_eq_right h1, hq]
  exact max_eq_right (qz_ge_one hN)

/-- The first zone that ends above `1` (lap `a`) and the last zone that starts below `15/7` (lap `b`) of the reading `x`. -/
theorem exists_ab {x : ℝ} (hx : 1 ≤ x) :
    ∃ a b : ℕ, 1 ≤ a ∧ 8 * (a : ℝ) - 7 ≤ x ∧ x < 8 * (a : ℝ) + 1 ∧ 15 / 7 * x ≤ 8 * (b : ℝ) + 7 ∧
      8 * (b : ℝ) - 1 < 15 / 7 * x := by
  have hy : 0 ≤ (x - 1) / 8 := by linarith
  have hw : 0 < (15 / 7 * x + 1) / 8 := by positivity
  refine ⟨⌊(x - 1) / 8⌋₊ + 1, ⌈(15 / 7 * x + 1) / 8⌉₊ - 1, by omega, ?_, ?_, ?_, ?_⟩
  · have := Nat.floor_le hy
    push_cast; linarith
  · have := Nat.lt_floor_add_one ((x - 1) / 8)
    push_cast; linarith
  · have hc : 1 ≤ ⌈(15 / 7 * x + 1) / 8⌉₊ := Nat.ceil_pos.mpr hw
    have := Nat.le_ceil ((15 / 7 * x + 1) / 8)
    have e : ((⌈(15 / 7 * x + 1) / 8⌉₊ - 1 : ℕ) : ℝ) = (⌈(15 / 7 * x + 1) / 8⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc]; simp
    rw [e]; linarith
  · have hc : 1 ≤ ⌈(15 / 7 * x + 1) / 8⌉₊ := Nat.ceil_pos.mpr hw
    have := Nat.ceil_lt_add_one hw.le
    have e : ((⌈(15 / 7 * x + 1) / 8⌉₊ - 1 : ℕ) : ℝ) = (⌈(15 / 7 * x + 1) / 8⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc]; simp
    rw [e]; linarith

/-- **The capacity bound.**  For a reading `x ≥ 1` the product of its clipped zone ratios against the window `[1, 15/7]` is
at most `9/7` (`K` any integer bound for the laps that start in the window).  Both boundary zones are handled by the
integer inequality `abint`; the interior zones telescope (`prod_qz_pow_four_le`).
[PROVISIONAL: covering] this bounds how much of the window one reading can shadow; it supports `Reach 3`. -/
theorem prod_zr_le {x : ℝ} (hx : 1 ≤ x) {K : ℕ} (hK : x * (15 / 7) / 8 + 1 / 8 ≤ K) :
    ∏ N ∈ Finset.Icc 1 K, zr x N ≤ 9 / 7 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨a, b, ha1, haL, haU, hbU, hbL⟩ := exists_ab hx
  have hbK : b ≤ K := by
    have h1 : (b : ℝ) < K := by linarith
    exact_mod_cast h1.le
  have hsub : Finset.Icc a b ⊆ Finset.Icc 1 K := Finset.Icc_subset_Icc ha1 hbK
  have hone : ∀ N ∈ Finset.Icc 1 K, N ∉ Finset.Icc a b → zr x N = 1 := by
    intro N hN hN'
    simp only [Finset.mem_Icc, not_and_or, not_le] at hN'
    rcases hN' with h | h
    · -- N < a
      apply zr_eq_one_of_low hx0
      rw [div_le_one hx0]
      have : (N : ℝ) + 1 ≤ a := by exact_mod_cast h
      linarith
    · -- b < N
      apply zr_eq_one_of_high hx0
      rw [le_div_iff₀ hx0]
      have : (b : ℝ) + 1 ≤ N := by exact_mod_cast h
      linarith
  rw [← Finset.prod_subset hsub hone]
  rcases lt_trichotomy a b with hab | hab | hab
  · -- the case a < b
    have hI : Finset.Icc a b = insert a (insert b (Finset.Ioo a b)) := by
      ext N; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]; omega
    have hbnot : b ∉ Finset.Ioo a b := by simp
    have hanot : a ∉ insert b (Finset.Ioo a b) := by
      simp only [Finset.mem_insert, Finset.mem_Ioo, not_or, not_and, not_lt]
      exact ⟨by omega, fun h => absurd h (by omega)⟩
    rw [hI, Finset.prod_insert hanot, Finset.prod_insert hbnot]
    have hint : ∏ N ∈ Finset.Ioo a b, zr x N = ∏ N ∈ Finset.Ioo a b, qz N := by
      apply Finset.prod_congr rfl
      intro N hN
      rw [Finset.mem_Ioo] at hN
      have hN1 : (a : ℝ) + 1 ≤ N := by exact_mod_cast hN.1
      have hN2 : (N : ℝ) + 1 ≤ b := by exact_mod_cast hN.2
      apply zr_eq_qz hx0 (by omega)
      · rw [le_div_iff₀ hx0]; linarith
      · rw [div_le_iff₀ hx0]; linarith
    rw [hint]
    have hIpow := prod_qz_pow_four_le ha1 b hab
    have hI1 := one_le_prod_qz a b ha1
    set I := ∏ N ∈ Finset.Ioo a b, qz N with hIdef
    have hF1 : 56 * b < 120 * a + 22 := by
      have : (56 * (b : ℝ)) < 120 * a + 22 := by linarith
      exact_mod_cast this
    have hF2 : 120 * a ≤ 56 * b + 154 := by
      have : (120 * (a : ℝ)) ≤ 56 * b + 154 := by linarith
      exact_mod_cast this
    have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hb1' : (2 : ℝ) ≤ b := by exact_mod_cast (by omega : 2 ≤ b)
    have hza := zr_ge_one x a
    have hzb := zr_ge_one x b
    have hdenb : 0 < 8 * (b : ℝ) - 1 := by linarith
    have hJ : 0 ≤ (2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1) := by
      apply div_nonneg <;> linarith
    -- the product P = zr a * (zr b * I)
    have hP : zr x a * (zr x b * I) ≤ 9 / 7 := by
      have hP4 : (zr x a * (zr x b * I)) ^ 4 ≤ (9 / 7 : ℝ) ^ 4 := by
        have hmul : (zr x a * (zr x b * I)) ^ 4 = (zr x a * zr x b) ^ 4 * I ^ 4 := by ring
        rw [hmul]
        rcases abint ha1 hab hF1 hF2 with h | h
        · -- first branch: both boundary zones clipped
          have hv : 1 ≤ (8 * (a : ℝ) + 1) / x := by rw [le_div_iff₀ hx0]; linarith
          have hBu : 1 ≤ 15 / 7 * x / (8 * (b : ℝ) - 1) := by rw [le_div_iff₀ hdenb]; linarith
          have h1 : zr x a ≤ (8 * (a : ℝ) + 1) / x := by
            have := zr_le_v (x := x) (N := a) hx0
            rwa [max_eq_right hv] at this
          have h2 : zr x b ≤ 15 / 7 * x / (8 * (b : ℝ) - 1) := by
            have := zr_le_Bu (x := x) (N := b) hx0 (by omega)
            rwa [max_eq_right hBu] at this
          have hT : zr x a * zr x b ≤ (15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1) := by
            calc zr x a * zr x b ≤ (8 * (a : ℝ) + 1) / x * (15 / 7 * x / (8 * (b : ℝ) - 1)) :=
                  mul_le_mul h1 h2 (le_trans zero_le_one hzb) (le_trans zero_le_one hv)
              _ = (15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1) := by field_simp
          calc (zr x a * zr x b) ^ 4 * I ^ 4
              ≤ ((15 / 7 : ℝ) * (8 * (a : ℝ) + 1) / (8 * (b : ℝ) - 1)) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) :=
                mul_le_mul (pow_le_pow_left₀ (by positivity) hT 4) hIpow (by positivity) (by positivity)
            _ ≤ _ := h
        · -- second branch: both boundary zones unclipped
          have hT : zr x a * zr x b ≤ qz a * qz b :=
            mul_le_mul (zr_le_qz hx0 ha1) (zr_le_qz hx0 (by omega)) (le_trans zero_le_one hzb)
              (le_trans zero_le_one (qz_ge_one ha1))
          calc (zr x a * zr x b) ^ 4 * I ^ 4
              ≤ (qz a * qz b) ^ 4 * ((2 * (b : ℝ) - 1) / (2 * (a : ℝ) + 1)) :=
                mul_le_mul (pow_le_pow_left₀ (by positivity) hT 4) hIpow (by positivity) (by positivity)
            _ ≤ _ := h
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hP4
    exact hP
  · -- a = b
    subst hab
    simp only [Finset.Icc_self, Finset.prod_singleton]
    exact (zr_le_qz hx0 ha1).trans (qz_le_nine_sevenths ha1)
  · -- b < a
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    norm_num

/-! ### From "no lonely instant in the window" to a product bound -/

/-- **A window with no lonely instant is covered by zones, so `B ≤ (9/7)^|E|`.**  If no instant of `[1/8, B/8]` is lonely
for `E` (readings `≥ 1`, `1 ≤ B ≤ 15/7`), the zones `((8N−1)/x, (8N+1)/x)`, `x ∈ E`, cover `[1, B]` in the coordinate
`R = 8t`; the finite covering lemma gives `B ≤` the product of the clipped zone ratios, and each reading contributes at most
`9/7` (`prod_zr_le`).  [PROVISIONAL: covering] a union bound in the scale-invariant measure `dR/R`; it supports `Reach 3`. -/
theorem prod_bound_of_no_lonely {E : Finset ℝ} (hE : ∀ x ∈ E, 1 ≤ x) {B : ℝ} (hB1 : 1 ≤ B) (hB : B ≤ 15 / 7)
    (hno : ∀ s : ℝ, 1 / 8 ≤ s → s ≤ B / 8 → ¬ LonelyAt E s) : B ≤ (9 / 7 : ℝ) ^ E.card := by
  -- a bound `K` on the laps
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ x ∈ E, x * (15 / 7) / 8 + 1 / 8 ≤ K := by
    refine ⟨⌈∑ x ∈ E, (x * (15 / 7) / 8 + 1 / 8)⌉₊, fun x hx => ?_⟩
    have h1 : x * (15 / 7) / 8 + 1 / 8 ≤ ∑ y ∈ E, (y * (15 / 7) / 8 + 1 / 8) :=
      Finset.single_le_sum (f := fun y => y * (15 / 7) / 8 + 1 / 8)
        (fun y hy => by have := hE y hy; positivity) hx
    exact h1.trans (Nat.le_ceil _)
  have hcov : ∀ R : ℝ, 1 ≤ R → R ≤ B → ∃ p ∈ E ×ˢ Finset.Icc 1 K,
      (fun p : ℝ × ℕ => (8 * (p.2 : ℝ) - 1) / p.1) p < R ∧ R < (fun p : ℝ × ℕ => (8 * (p.2 : ℝ) + 1) / p.1) p := by
    intro R hR1 hRB
    have hs1 : 1 / 8 ≤ R / 8 := by linarith
    have hs2 : R / 8 ≤ B / 8 := by linarith
    have hnl := hno (R / 8) hs1 hs2
    unfold LonelyAt at hnl
    push Not at hnl
    obtain ⟨x, hx, hw⟩ := hnl
    have hx1 := hE x hx
    have hx0 : 0 < x := by linarith
    have hw' : InWay x (R / 8) := hw
    have hlap1 : 1 ≤ lap x (R / 8) :=
      one_le_lap_of_bound (m := 1) one_pos hx1 (by simpa using hs1) hw'
    have hb := abs_lt.mp (abs_sub_lap_lt hw')
    set N : ℤ := lap x (R / 8) with hN
    obtain ⟨n, hn⟩ : ∃ n : ℕ, N = n := ⟨N.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hn1 : 1 ≤ n := by omega
    have hnR : (N : ℝ) = n := by rw [hn]; simp
    have hxR : x * (R / 8) ≤ x * (B / 8) := mul_le_mul_of_nonneg_left hs2 hx0.le
    have hnK : n ≤ K := by
      have h1 : (n : ℝ) < K := by
        have := hK x hx
        have h2 : x * (B / 8) ≤ x * (15 / 7) / 8 := by
          have : x * B ≤ x * (15 / 7) := mul_le_mul_of_nonneg_left hB hx0.le
          linarith
        rw [← hnR]; linarith
      exact_mod_cast h1.le
    refine ⟨(x, n), Finset.mem_product.mpr ⟨hx, Finset.mem_Icc.mpr ⟨hn1, hnK⟩⟩, ?_, ?_⟩
    · show (8 * (n : ℝ) - 1) / x < R
      rw [div_lt_iff₀ hx0]; rw [hnR] at hb; nlinarith [hb.1]
    · show R < (8 * (n : ℝ) + 1) / x
      rw [lt_div_iff₀ hx0]; rw [hnR] at hb; nlinarith [hb.2]
  -- [PROVISIONAL: covering] the finite covering lemma applied to the zones of the readings; supports `reach_union`
  -- (`Reach 3 (729/343)`), a covering step towards `Reach 5 6` and `Types.StrongGate`.
  have hcp := cover_prod (E ×ˢ Finset.Icc 1 K) (fun p : ℝ × ℕ => (8 * (p.2 : ℝ) - 1) / p.1)
    (fun p : ℝ × ℕ => (8 * (p.2 : ℝ) + 1) / p.1) 1 B one_pos hB1 hcov
  rw [div_one] at hcp
  refine hcp.trans ?_
  -- compare with `zr`
  have hle : ∏ p ∈ E ×ˢ Finset.Icc 1 K, max 1 (min B ((8 * (p.2 : ℝ) + 1) / p.1) / max 1 ((8 * (p.2 : ℝ) - 1) / p.1)) ≤
      ∏ p ∈ E ×ˢ Finset.Icc 1 K, zr p.1 p.2 := by
    refine Finset.prod_le_prod (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun p hp => ?_)
    unfold zr
    refine max_le_max le_rfl ?_
    exact div_le_div_of_nonneg_right (min_le_min_right _ hB) (le_trans zero_le_one (le_max_left _ _))
  refine hle.trans ?_
  rw [Finset.prod_product]
  calc ∏ x ∈ E, ∏ N ∈ Finset.Icc 1 K, zr x N ≤ ∏ x ∈ E, (9 / 7 : ℝ) :=
        Finset.prod_le_prod (fun x hx => Finset.prod_nonneg (fun N _ => le_trans zero_le_one (zr_ge_one x N)))
          (fun x hx => prod_zr_le (hE x hx) (hK x hx))
    _ = (9 / 7 : ℝ) ^ E.card := by rw [Finset.prod_const]

/-! ### Three readings -/

/-- `InWay` is open in the instant. -/
theorem inWay_open {d s : ℝ} (hd : 0 < d) (h : InWay d s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s' : ℝ, |s' - s| < δ → InWay d s' := by
  obtain ⟨k, hk⟩ := exists_near_int h
  have hpos : 0 < 1 / 8 - |d * s - k| := by linarith
  refine ⟨(1 / 8 - |d * s - k|) / d, div_pos hpos hd, fun s' hs' => ?_⟩
  unfold InWay
  refine lt_of_le_of_lt (distInt_le (d * s') k) ?_
  have h1 : |d * s' - k| ≤ |d * s - k| + d * |s' - s| := by
    calc |d * s' - k| = |(d * s - k) + d * (s' - s)| := by ring_nf
      _ ≤ |d * s - k| + |d * (s' - s)| := abs_add_le _ _
      _ = |d * s - k| + d * |s' - s| := by rw [abs_mul, abs_of_pos hd]
  have h2 : d * |s' - s| < 1 / 8 - |d * s - k| := by
    calc d * |s' - s| < d * ((1 / 8 - |d * s - k|) / d) := mul_lt_mul_of_pos_left hs' hd
      _ = 1 / 8 - |d * s - k| := by field_simp
  linarith

/-- **Scaling**: a reach statement for readings `≥ 1` gives it for readings `≥ m`. -/
theorem reach_of_unit {k : ℕ} {B : ℝ}
    (h : ∀ E : Finset ℝ, E.card ≤ k → (∀ x ∈ E, 1 ≤ x) → ∃ s, 1 / 8 ≤ s ∧ s ≤ B / 8 ∧ LonelyAt E s) :
    Reach k B := by
  intro E m hE hm hlow
  have hE' : (E.image (fun d => d / m)).card ≤ k := (Finset.card_image_le).trans hE
  have hlow' : ∀ y ∈ E.image (fun d => d / m), 1 ≤ y := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    rw [le_div_iff₀ hm]; linarith [hlow d hd]
  obtain ⟨s', hs1, hs2, hl⟩ := h _ hE' hlow'
  refine ⟨s' / m, ?_, ?_, ?_⟩
  · rw [show 1 / (8 * m) = (1 / 8) / m by field_simp]
    exact div_le_div_of_nonneg_right hs1 hm.le
  · rw [show B / (8 * m) = (B / 8) / m by field_simp]
    exact div_le_div_of_nonneg_right hs2 hm.le
  · intro d hd
    have := hl (d / m) (Finset.mem_image_of_mem _ hd)
    have e : d * (s' / m) = d / m * s' := by ring
    rw [e]; exact this

/-- **`k` readings, away from the supremum**: for `(9/7)^k < B ≤ 15/7`, any `k` readings `≥ 1` have a lonely instant in
`R ∈ [1, B]`.  Proof: otherwise `B ≤ (9/7)^k` by `prod_bound_of_no_lonely`.  The range `(9/7)^k < 15/7` is `k ≤ 3`
(`union_bound_range`). -/
theorem reach_union_unit_gt {k : ℕ} {B : ℝ} (hB0 : (9 / 7 : ℝ) ^ k < B) (hB : B ≤ 15 / 7) (E : Finset ℝ)
    (hE : E.card ≤ k) (hlow : ∀ x ∈ E, 1 ≤ x) : ∃ s, 1 / 8 ≤ s ∧ s ≤ B / 8 ∧ LonelyAt E s := by
  by_contra hcon
  push Not at hcon
  have hno : ∀ s : ℝ, 1 / 8 ≤ s → s ≤ B / 8 → ¬ LonelyAt E s := fun s h1 h2 hl => hcon s h1 h2 hl
  have hB1 : 1 ≤ B := le_trans (one_le_pow₀ (by norm_num)) hB0.le
  have h1 := prod_bound_of_no_lonely hlow hB1 hB hno
  have h3 : (9 / 7 : ℝ) ^ E.card ≤ (9 / 7) ^ k := pow_le_pow_right₀ (by norm_num) hE
  linarith

/-- **`k` readings, at the supremum**: if `(9/7)^k < 15/7`, any `k` readings `≥ 1` have a lonely instant in
`R ∈ [1, (9/7)^k]`.  The instants lonely for `E` form a closed set (`InWay` is open), so the infimum of the lonely instants
is lonely; it is `≤ B/8` for every `B > (9/7)^k` by `reach_union_unit_gt`. -/
theorem reach_union_unit {k : ℕ} (hk : (9 / 7 : ℝ) ^ k < 15 / 7) (E : Finset ℝ) (hE : E.card ≤ k)
    (hlow : ∀ x ∈ E, 1 ≤ x) : ∃ s, 1 / 8 ≤ s ∧ s ≤ (9 / 7 : ℝ) ^ k / 8 ∧ LonelyAt E s := by
  have hL : ∀ B : ℝ, (9 / 7 : ℝ) ^ k < B → B ≤ 15 / 7 → ∃ s, 1 / 8 ≤ s ∧ s ≤ B / 8 ∧ LonelyAt E s :=
    fun B h1 h2 => reach_union_unit_gt h1 h2 E hE hlow
  set L : Set ℝ := {s | 1 / 8 ≤ s ∧ LonelyAt E s} with hLdef
  have hne : L.Nonempty := by
    obtain ⟨s, h1, _, h3⟩ := hL (15 / 7) hk le_rfl
    exact ⟨s, h1, h3⟩
  have hbdd : BddBelow L := ⟨1 / 8, fun s hs => hs.1⟩
  set s0 := sInf L with hs0def
  have hs0le : ∀ B : ℝ, (9 / 7 : ℝ) ^ k < B → B ≤ 15 / 7 → s0 ≤ B / 8 := by
    intro B h1 h2
    obtain ⟨s, hs1, hs2, hs3⟩ := hL B h1 h2
    exact (csInf_le hbdd ⟨hs1, hs3⟩).trans hs2
  have hs0 : s0 ≤ (9 / 7 : ℝ) ^ k / 8 := by
    by_contra hcon
    push Not at hcon
    have hm : (9 / 7 : ℝ) ^ k < 8 * s0 := by linarith
    set B : ℝ := min (15 / 7) (((9 / 7 : ℝ) ^ k + 8 * s0) / 2) with hB
    have hB1 : (9 / 7 : ℝ) ^ k < B := lt_min hk (by linarith)
    have hB2 : B ≤ 15 / 7 := min_le_left _ _
    have hB3 : B < 8 * s0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have := hs0le B hB1 hB2
    linarith
  have hs0L : s0 ∈ L := by
    refine ⟨le_csInf hne (fun s hs => hs.1), ?_⟩
    intro d hd
    by_contra hnl
    have hw : InWay d s0 := not_le.mp hnl
    obtain ⟨δ, hδ, hopen⟩ := inWay_open (lt_of_lt_of_le one_pos (hlow d hd)) hw
    obtain ⟨s', hs'L, hs'lt⟩ := exists_lt_of_csInf_lt hne (show sInf L < s0 + δ by linarith)
    have hs'ge : s0 ≤ s' := csInf_le hbdd hs'L
    have hin := hopen s' (by rw [abs_lt]; constructor <;> linarith)
    exact (not_inWay_iff.mpr (hs'L.2 d hd)) hin
  exact ⟨s0, hs0L.1, hs0, hs0L.2⟩

/-- **The union bound reaches exactly `k ≤ 3`**: `(9/7)^3 = 729/343 < 15/7 < (9/7)^4`. -/
theorem union_bound_range : (9 / 7 : ℝ) ^ 3 < 15 / 7 ∧ (15 / 7 : ℝ) < (9 / 7) ^ 4 := by
  constructor <;> norm_num

/-- **The capacity bound `prod_zr_le` fails exactly past `15/7`**: for `15/7 < B ≤ 17/7` the reading `7` has clipped zone
ratios `9/7` (lap 1, zone `(1, 9/7)`) and `7B/15 > 1` (lap 2, zone `(15/7, B)`) against the window `[1, B]`, with product
`3B/5 > 9/7`.  So one reading can shadow more than `ln (9/7)` of a longer window, and the union bound of `reach_union`
stops at `15/7`. -/
theorem capacity_jump {B : ℝ} (h1 : 15 / 7 < B) (h2 : B ≤ 17 / 7) :
    max 1 (min B (9 / 7) / max 1 1) * max 1 (min B (17 / 7) / max 1 (15 / 7)) = 3 * B / 5 ∧ 9 / 7 < 3 * B / 5 := by
  have e1 : min B (9 / 7) = 9 / 7 := min_eq_right (by linarith)
  have e2 : min B (17 / 7) = B := min_eq_left h2
  have e3 : max (1 : ℝ) 1 = 1 := max_self 1
  have e4 : max (1 : ℝ) (15 / 7) = 15 / 7 := max_eq_right (by norm_num)
  rw [e1, e2, e3, e4]
  have e5 : max (1 : ℝ) (9 / 7 / 1) = 9 / 7 := by
    rw [div_one]; exact max_eq_right (by norm_num)
  have e6 : max (1 : ℝ) (B / (15 / 7)) = B / (15 / 7) :=
    max_eq_right (by rw [le_div_iff₀ (by norm_num)]; linarith)
  rw [e5, e6]
  constructor
  · ring
  · linarith

#print axioms capacity_jump

/-- **`Reach k ((9/7)^k)` for `(9/7)^k < 15/7`** (that is, `k = 0, 1, 2, 3`), and `(9/7)^k` is the exact supremum for
`k = 1, 2, 3` (`not_reach_one`, `not_reach_two`, `not_reach_three`).  The proof is a union bound in the measure `dR/R`:
each reading shadows at most `ln (9/7)` of a window `[1, B]` with `B ≤ 15/7` (`prod_zr_le`), so `k` readings shadow at most
`k ln (9/7)`.  It is not a cascade-chain argument.
[PROVISIONAL: covering] a covering statement; it supports `Reach 5 6` only through the chain of `Reach k` statements, and it
cannot reach four readings (`union_bound_range`, `not_reach_four_pure`). -/
theorem reach_union {k : ℕ} (hk : (9 / 7 : ℝ) ^ k < 15 / 7) : Reach k ((9 / 7 : ℝ) ^ k) :=
  reach_of_unit (fun E hE hlow => reach_union_unit hk E hE hlow)

theorem reach_union_gt {k : ℕ} {B : ℝ} (hB0 : (9 / 7 : ℝ) ^ k < B) (hB : B ≤ 15 / 7) : Reach k B :=
  reach_of_unit (fun E hE hlow => reach_union_unit_gt hB0 hB E hE hlow)

/-- **`Reach 3 (729/343)`**: three readings `≥ m` have a lonely instant in `R ∈ [1, 729/343]`; `729/343 = (9/7)^3` is the
exact supremum (`not_reach_three`). -/
theorem reach_three : Reach 3 (729 / 343) := by
  have h := reach_union (k := 3) (by norm_num)
  have e : ((9 / 7 : ℝ) ^ 3) = 729 / 343 := by norm_num
  rw [e] at h
  exact h

theorem reach_three_gt {B : ℝ} (hB0 : 729 / 343 < B) (hB : B ≤ 15 / 7) : Reach 3 B :=
  reach_union_gt (k := 3) (by norm_num; exact hB0) hB

/-! ### The small-readings regime (any `k`): only the first lap can enter the window -/

/-- **If every reading is at most `15/B`, only lap 1 can meet the window `[1, B]`, and `k` readings have a lonely instant
by `R = B` as soon as `B > (9/7)^k`.**  (The zone of lap `N ≥ 2` starts at `(8N−1)/x ≥ 15/x ≥ B`.)  So to exceed the pure lap-1
value `(9/7)^k` a reading must be able to reach its second lap inside the window, i.e. exceed `15/B`: for `k = 4`,
`B ≈ 2.74`, a reading above `5.49`; for `k = 5`, `B ≈ 3.52`, above `4.27`.  The extremal sets contain readings up to `7`.
[PROVISIONAL: covering] same union bound as `reach_union`, with the single zone `(7/x, 9/x)`. -/
theorem reach_small_unit {k : ℕ} {B : ℝ} (hB0 : (9 / 7 : ℝ) ^ k < B) (E : Finset ℝ) (hE : E.card ≤ k)
    (hband : ∀ x ∈ E, 1 ≤ x ∧ x * B ≤ 15) : ∃ s, 1 / 8 ≤ s ∧ s ≤ B / 8 ∧ LonelyAt E s := by
  by_contra hcon
  push Not at hcon
  have hB1 : 1 ≤ B := le_trans (one_le_pow₀ (by norm_num)) hB0.le
  have hcov : ∀ R : ℝ, 1 ≤ R → R ≤ B → ∃ x ∈ E, (fun x : ℝ => 7 / x) x < R ∧ R < (fun x : ℝ => 9 / x) x := by
    intro R hR1 hRB
    have hs1 : 1 / 8 ≤ R / 8 := by linarith
    have hs2 : R / 8 ≤ B / 8 := by linarith
    have hnl := hcon (R / 8) hs1 hs2
    unfold LonelyAt at hnl
    push Not at hnl
    obtain ⟨x, hx, hw⟩ := hnl
    have hx1 := (hband x hx).1
    have hxB := (hband x hx).2
    have hx0 : 0 < x := by linarith
    have hw' : InWay x (R / 8) := hw
    have hlap1 : 1 ≤ lap x (R / 8) :=
      one_le_lap_of_bound (m := 1) one_pos hx1 (by simpa using hs1) hw'
    have hb := abs_lt.mp (abs_sub_lap_lt hw')
    have hxR : x * R ≤ 15 := by nlinarith
    have hN2 : lap x (R / 8) < 2 := by
      have : ((lap x (R / 8) : ℤ) : ℝ) < 2 := by nlinarith [hb.2]
      exact_mod_cast this
    have hN1 : lap x (R / 8) = 1 := by omega
    rw [hN1] at hb
    push_cast at hb
    refine ⟨x, hx, ?_, ?_⟩
    · show 7 / x < R
      rw [div_lt_iff₀ hx0]; nlinarith [hb.1]
    · show R < 9 / x
      rw [lt_div_iff₀ hx0]; nlinarith [hb.2]
  -- [PROVISIONAL: covering] the finite covering lemma applied to the lap-1 zones; supports `reach_small`.
  have hcp := cover_prod E (fun x : ℝ => 7 / x) (fun x : ℝ => 9 / x) 1 B one_pos hB1 hcov
  rw [div_one] at hcp
  have hprod : ∏ x ∈ E, max 1 (min B (9 / x) / max 1 (7 / x)) ≤ ∏ _x ∈ E, (9 / 7 : ℝ) := by
    refine Finset.prod_le_prod (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun x hx => ?_)
    have hx0 : 0 < x := by linarith [(hband x hx).1]
    refine max_le (by norm_num) ?_
    have h7 : 0 < 7 / x := by positivity
    calc min B (9 / x) / max 1 (7 / x) ≤ (9 / x) / (7 / x) :=
          div_le_div₀ (by positivity) (min_le_right _ _) h7 (le_max_right _ _)
      _ = 9 / 7 := by field_simp
  rw [Finset.prod_const] at hprod
  have h3 : (9 / 7 : ℝ) ^ E.card ≤ (9 / 7) ^ k := pow_le_pow_right₀ (by norm_num) hE
  linarith

/-- The small-readings regime for readings `≥ m`: `Reach`-type statement with the band `m ≤ d ≤ 15m/B`. -/
theorem reach_small {k : ℕ} {B : ℝ} (hB0 : (9 / 7 : ℝ) ^ k < B) (E : Finset ℝ) (m : ℝ) (hE : E.card ≤ k)
    (hm : 0 < m) (hband : ∀ d ∈ E, m ≤ d ∧ d * B ≤ 15 * m) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ B / (8 * m) ∧ LonelyAt E s := by
  have hE' : (E.image (fun d => d / m)).card ≤ k := (Finset.card_image_le).trans hE
  have hband' : ∀ y ∈ E.image (fun d => d / m), 1 ≤ y ∧ y * B ≤ 15 := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hm]; linarith [(hband d hd).1]
    · rw [div_mul_eq_mul_div, div_le_iff₀ hm]; linarith [(hband d hd).2]
  obtain ⟨s', hs1, hs2, hl⟩ := reach_small_unit hB0 _ hE' hband'
  refine ⟨s' / m, ?_, ?_, ?_⟩
  · rw [show 1 / (8 * m) = (1 / 8) / m by field_simp]
    exact div_le_div_of_nonneg_right hs1 hm.le
  · rw [show B / (8 * m) = (B / 8) / m by field_simp]
    exact div_le_div_of_nonneg_right hs2 hm.le
  · intro d hd
    have := hl (d / m) (Finset.mem_image_of_mem _ hd)
    have e : d * (s' / m) = d / m * s' := by ring
    rw [e]; exact this

#print axioms max_one_div_mono
#print axioms cover_prod
#print axioms qz_ge_one
#print axioms qz_le_nine_sevenths
#print axioms qz_pow_four_le
#print axioms prod_qz_pow_four_le
#print axioms one_le_prod_qz
#print axioms big_poly
#print axioms abint_big
#print axioms abint_small
#print axioms abint
#print axioms zr_ge_one
#print axioms zr_eq_one_of_low
#print axioms zr_eq_one_of_high
#print axioms zr_le_qz
#print axioms zr_le_v
#print axioms zr_le_Bu
#print axioms zr_eq_qz
#print axioms exists_ab
#print axioms prod_zr_le
#print axioms prod_bound_of_no_lonely
#print axioms inWay_open
#print axioms reach_of_unit
#print axioms reach_union_unit_gt
#print axioms reach_union_unit
#print axioms union_bound_range
#print axioms reach_union
#print axioms reach_union_gt
#print axioms reach_three
#print axioms reach_three_gt
#print axioms reach_small_unit
#print axioms reach_small

/-! ## (8) Where it stalls: four and five readings -/

/-- **`Reach 4 (289/105)`** (OWED).  `289/105 ≈ 2.7524` is the supremum seen for four readings [OBS: float-steered search
plus the exact vertex of the linear programme of the chain with laps `1,1,1,1,2,2`; vertex readings
`7, 105/17, 245/51, 1715/459`; exact integer enumeration over `a/Q` for `Q ≤ 51` found no set above it].  It exceeds
`(9/7)^4 ≈ 2.7328` (`not_reach_four_pure`).  The union bound of section (7) cannot prove it: a single reading shadows
`ln (9/7 · 17/15)` of a window longer than `17/7`, and for large readings every reading shadows a quarter of the
log-line, so four readings meet the bound `1` exactly. -/
-- [PROVISIONAL: covering] a covering statement; supports `Reach 5 6` only through the chain of `Reach k` statements.
-- STANDING: OWED
def ReachFourSharp : Prop := Reach 4 (289 / 105)

/-- **`Reach 5 (2125/483)`** (OWED).  `2125/483 ≈ 4.3996` is the supremum seen for five readings [OBS: float-steered search
over 5·10^8 sets, the exact vertex of the linear programme of the twelve-move chain with laps
`1,1,1,1,2,2,2,2,3,3,2,3`, vertex readings `161/25, 7, 1449/289, 1127/289, 483/85`; exact enumeration over `a/Q` with
`Q ≤ 24` and readings `≤ 9`, or `Q ≤ 6` and readings `≤ 30`, found no set above `100/23 ≈ 4.348`].  It implies
`FiveReach` (`fiveReach_of_sharp`), with a margin of `6 − 2125/483 ≈ 1.6`. -/
-- [PROVISIONAL: covering] a covering statement; it supports `Types.StrongGate` through `fiveCarve_of_fiveReach`.
-- STANDING: OWED
def ReachFiveSharp : Prop := Reach 5 (2125 / 483)

/-- `Reach 5 (2125/483)` would give `FiveReach`. -/
theorem fiveReach_of_sharp (h : ReachFiveSharp) : FiveReach :=
  reach_mono_bound (by norm_num) h

#print axioms fiveReach_of_sharp

/-- Any reach bound `B ≤ 6` for five readings gives `FiveReach`. -/
theorem fiveReach_of_reach_five {B : ℝ} (hB : B ≤ 6) (h : Reach 5 B) : FiveReach :=
  reach_mono_bound hB h

#print axioms fiveReach_of_reach_five

end FiveReachStudy

end Fresh
