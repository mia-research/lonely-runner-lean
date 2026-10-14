import Mathlib
import Fresh.Framework

/-!
# Where the isolation goes: candidate statements (Task E, stage 1, STATEMENTS ONLY)

Written 2026-10-07.  Imports `Mathlib` and `Fresh.Framework` only; nothing from the existing `LonelyRunner` repo.
Every `Prop` here is either an object of the framework (`-- STANDING: DEFINITION`) or a claim that nothing in this
folder proves (`-- STANDING: OWED`).  The only proofs are four `example`s, kept because they decide a classification
question (whether a statement has content, and whether one statement implies another).

Owner sentences formalised (quoted from the brief):
  (O1) any deviation from the AP or grid "just displaces the isolation because we can show where and why it goes
       there";
  (O2) "the cascade converts any arrangement into ap/grid arrangements and a deviation";
  (O3) d_min takes care of transitions, the grid takes care of scale.
Record constraint (E230): naming the instant, a uniform formula, or a cap is a foreign shape.  No statement below has
a cap, covering, density, move count or length bound; the sequences of moves are quantified `∃ N`, with no bound.

Provenance (read, not imported; no proof copied):
  * `reading`, `gridIndex`, `deviation`: `LRC/Cascade/Reading.lean` `IdealReading`, `reading` (there `D` is an input;
    here `D = d_min` of the subject, as in log E301's correction: deviations `(y mod m)/m`, start `1/(8m)`).
  * `IsStartBlocker`, `StartBlockers`: log E427 ("start blockers are exactly slot 0, or slot 7 with ε > 0"), recorded
    there as [PROVED — arithmetic] (near-sharer); no Lean declaration in the repo was found under that name.
  * `CrossedEnteringEdge`, (d3): `LRC/Spec/SeparationN.lean` `transport`, `crossed_entering_edge`,
    `slower_obstruction_is_edge_push`; log E299 (`slower_clear_iff`, the "edge push").
  * `LandingIsFirstIsolation`, `CascadeFindsIsolation`: paper Theorems 11 and 12 (v9 §6), `Spec/Doors.lean`.
-/

open Classical

namespace Fresh.Where

/-! ## (i) The conversion: reference grid through `d_min` plus deviation, in the cascade's coordinates

Subject `k`, smallest disparity `m` (`IsDmin v k m`).  Reading `ρ_i = |v i − v k| / m`; grid index `q_i = ⌊ρ_i⌋`;
slot `q_i mod 8`; deviation `ε_i = frac ρ_i ∈ [0, 1)`.  State coordinate `R = 8·m·t`; at `R` the reading `ρ` sits
`R·ρ mod 8` eighths past the subject.  These are functions, not claims. -/

/-- The reading of runner `i` from subject `k` in units of `m` (= `d_min`): `ρ_i = |v i − v k| / m`. -/
noncomputable def reading (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℝ := |v i - v k| / m

/-- Grid index of the reading: `q_i = ⌊ρ_i⌋` (the reference grid of gap `d_min` through the subject). -/
noncomputable def gridIndex (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℤ := ⌊reading v k m i⌋

/-- Slot of the reading: `q_i mod 8`, in `{0, …, 7}`. -/
noncomputable def slot (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℤ := gridIndex v k m i % 8

/-- Deviation of the reading from its grid point: `ε_i = frac ρ_i ∈ [0, 1)`. -/
noncomputable def deviation (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℝ := Int.fract (reading v k m i)

/-- The cascade coordinate `R = 8·d_min·t`. -/
noncomputable def stateR (m t : ℝ) : ℝ := 8 * m * t

/-- The instant of a state: `t = R/(8·d_min)`.  `R = 1` is the bound `1/(8 d_min)`; `R = a` with `a` odd is the
grid's global isolation instant `a/(8 d_min)`. -/
noncomputable def instantOf (m R : ℝ) : ℝ := R / (8 * m)

/-- Position of a reading `ρ` at state `R`, in eighths of a lap, reduced to `[0, 8)`: `R·ρ mod 8`. -/
noncomputable def position (ρ R : ℝ) : ℝ := R * ρ - 8 * (⌊R * ρ / 8⌋ : ℝ)

/-- (O2) The conversion read as a decomposition of every disparity into grid part plus deviation.  Kept as an
`example` with its proof because it is content-free: it holds for every `v`, `k`, `i` and every `m > 0`.  Docstring
items: (a) formalises O2 in the cascade's units; (b) neither existence nor location: an identity; (c) no cap or
count. -/
example (v : Fin 8 → ℝ) (k i : Fin 8) (m : ℝ) (hm : 0 < m) :
    |v i - v k| = m * ((gridIndex v k m i : ℝ) + deviation v k m i) ∧
      0 ≤ deviation v k m i ∧ deviation v k m i < 1 := by
  refine ⟨?_, Int.fract_nonneg _, Int.fract_lt_one _⟩
  simp only [gridIndex, deviation, Int.floor_add_fract, reading]
  field_simp

/-- The Framework's `IsGridWithDeviation` holds for EVERY `v` (take `d = 1`, `idx j = j`, `e j = v j − v 0 − j`).
So "an arrangement is a grid plus a deviation" carries no information as a `Prop`; the content of O2 is in which grid
(gap `d_min`, through the subject) and in the coordinates `(slot, ε)` it produces.  This is why (i) is given as
functions, not as a claim. -/
example (v : Fin 8 → ℝ) : Fresh.IsGridWithDeviation v := by
  refine ⟨1, v 0, fun j => ((j : ℕ) : ℤ), fun j => v j - v 0 - ((j : ℕ) : ℝ), one_pos, ?_, ?_, ?_⟩
  · intro j j' h
    simp only at h
    have hj := j.isLt
    have hj' := j'.isLt
    apply Fin.ext
    omega
  · simp
  · intro j
    push_cast
    ring

/-- Faithfulness of the coordinates (O2, O3): reading `i` is out of the way at the instant of state `R` exactly when
its position at `R` lies in `[1, 7]` eighths.  (a) O2: the conversion is the cascade's own coordinate, not a proxy;
(b) neither existence nor location: a change of variables; (c) no cap or count.  Record: v9 §4 "Cascade coordinate"
("clear iff R·ρ_y mod 8 ∈ [1, 7]"), GL. -/
-- STANDING: OWED
def ClearIffPosition : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ R : ℝ, ∀ i, i ≠ k →
    (¬ Fresh.InWay |v i - v k| (instantOf m R) ↔
      1 ≤ position (reading v k m i) R ∧ position (reading v k m i) R ≤ 7)

/-- At the start `R = 1` the position of a reading is its slot plus its deviation: the grid point is the slot, the
deviation is the displacement from it.  (a) O2 and O3 (d_min sets the unit, the grid sets the slot); (b) neither: an
identity in the coordinates; (c) no cap or count. -/
-- STANDING: OWED
def PositionAtStart : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ i, i ≠ k →
    position (reading v k m i) 1 = (slot v k m i : ℝ) + deviation v k m i

/-! ## (ii) The start blockers at `R = 1` -/

/-- A start blocker: a reading of slot `0`, or of slot `7` with positive deviation.  An object (which readings the
conversion marks), not a claim. -/
-- STANDING: DEFINITION
def IsStartBlocker (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : Prop :=
  i ≠ k ∧ (slot v k m i = 0 ∨ (slot v k m i = 7 ∧ 0 < deviation v k m i))

/-- (ii) The runners in the way at the bound `t = 1/(8 d_min)` are exactly the start blockers.  Why, in the
conversion: at `R = 1` a reading sits `slot + ε` eighths out; the zone around the lap line is `(7, 9)`, i.e.
`[0, 1) ∪ (7, 8)` mod 8; slot `0` is inside for every `ε`, slot `7` is inside iff its deviation carried it past the
entering edge `7`.  (a) O1 (where the isolation is blocked at the start, and why: the deviation); (b) location shape
(it names the blockers), no existence quantifier; (c) no cap or count.  Record: [PROVED — arithmetic] (E427);
exact test 0 exceptions in 345,304 integer sets (E427), which is not a proof. -/
-- STANDING: OWED
def StartBlockers : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ i, i ≠ k →
    (Fresh.InWay |v i - v k| (1 / (8 * m)) ↔ IsStartBlocker v k m i)

/-! ## (iii) Candidate statements of the displacement -/

/-- The lap at which a start blocker next opens: `L = (q + 1) div 8` (slot `0`: `L = q/8`; slot `7`: `L = (q+1)/8`). -/
noncomputable def startLap (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℤ := (gridIndex v k m i + 1) / 8

/-- The state at which a start blocker next opens: `R = (8L + 1)/ρ`. -/
noncomputable def startOpeningR (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (i : Fin 8) : ℝ :=
  (8 * (startLap v k m i : ℝ) + 1) / reading v k m i

/-- The Framework's `nextOpening`, read in the conversion: a start blocker's next opening is the state
`(8L + 1)/ρ`.  (a) O1 ("where": the state the blocker sends the cascade to) and O3; (b) location shape; (c) no cap or
count. -/
-- STANDING: OWED
def StartOpening : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ i, IsStartBlocker v k m i →
    stateR m (Fresh.nextOpening |v i - v k| (1 / (8 * m))) = startOpeningR v k m i

/-- The displacement each start blocker imposes, in the deviation's own terms: slot `0` moves the state from `1` by
`(1 − ε)/ρ`, slot `7` by `(2 − ε)/ρ`.  This is the "why": the size of the push is set by the deviation `ε` and the
reading `ρ`, nothing else.  (a) O1 ("where and why"); (b) location shape; (c) no cap or count. -/
-- STANDING: OWED
def StartDisplacement : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ i, i ≠ k →
    (slot v k m i = 0 →
      startOpeningR v k m i - 1 = (1 - deviation v k m i) / reading v k m i) ∧
    (slot v k m i = 7 → 0 < deviation v k m i →
      startOpeningR v k m i - 1 = (2 - deviation v k m i) / reading v k m i)

/-- (d1) The first cascade move goes to the largest start opening among the start blockers, and fixes `R = 1` if there
is none.  This is `IsMove` at `t = 1/(8 d_min)` rewritten through (ii) and `StartOpening`; it adds nothing to
`IsMove` beyond the conversion [reasoned].  (a) O1 for the first step ("where": the state; "why": the blocker whose
deviation gives the largest push); (b) location shape: it characterises the successor, and asserts no existence of an
isolation; (c) no cap or count ("largest" is the maximum over at most seven readings in `IsMove` itself). -/
-- STANDING: OWED
def FirstMoveIsLargestStartOpening : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ t' : ℝ,
    (Fresh.IsMove (Fresh.disparitySet v k) (1 / (8 * m)) t' ↔
      ((∀ i, ¬ IsStartBlocker v k m i) ∧ t' = 1 / (8 * m)) ∨
      (∃ i, IsStartBlocker v k m i ∧ stateR m t' = startOpeningR v k m i ∧
        ∀ i', IsStartBlocker v k m i' → startOpeningR v k m i' ≤ stateR m t'))

/-- The cascade, started at `t₀`, reaches the fixed point `t⋆` after some finite number of moves.  No bound on the
number: `N` is existentially quantified. -/
-- STANDING: DEFINITION
def CascadeReaches (ds : Finset ℝ) (t₀ tStar : ℝ) : Prop :=
  ∃ (seq : ℕ → ℝ) (N : ℕ), seq 0 = t₀ ∧ (∀ n, n < N → Fresh.IsMove ds (seq n) (seq (n + 1))) ∧
    seq N = tStar ∧ Fresh.IsMove ds tStar tStar

/-- (d2) Displacement from a grid instant: from one of the grid's global isolation instants `a/(8 d_min)`,
`a ∈ {1, 3, 5, 7}`, the cascade reaches a landing in finitely many moves (no length cap).
(a) O1 read as "from the grid's isolation, the cascade carries it to a landing"; (b) EXISTENCE shape (∃ a landing,
∃ a number of moves); (c) no cap or count, but `∃ N` is the termination shape rule 7 bans as the shape of an
existence argument.
Comparison with (b) `Fresh.CascadeForm` by definitions: (b) → (d2) by `a = 1` (the `example` below).
(d2) → (b): a fixed point of `IsMove` has no runner in the way (a blocker's next opening is strictly later, since
every disparity is positive), so it is an isolation; then Theorem 13 (`doors_agree` in the existing repo, not in
Fresh) gives (b) [reasoned].  So (d2) is a restatement of (b), and of `LonelyRunnerEight`, not a "where" statement. -/
-- STANDING: OWED
def GridInstantDisplacement : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m →
    ∃ a ∈ ({1, 3, 5, 7} : Finset ℤ), ∃ tStar : ℝ,
      CascadeReaches (Fresh.disparitySet v k) ((a : ℝ) / (8 * m)) tStar

/-- (b) implies (d2), with `a = 1`: the classification evidence that (d2) is not stronger than (b). -/
example : Fresh.CascadeForm → GridInstantDisplacement := by
  intro h v hv k m hm
  obtain ⟨seq, h0, hmove, N, hN⟩ := h v hv k m hm
  refine ⟨1, by simp, seq N, seq, N, ?_, fun n _ => hmove n, rfl, ?_⟩
  · rw [h0]; push_cast; ring
  · have := hmove N
    rwa [hN] at this

/-- Location form of O1 ("where it goes"), with existence taken as a hypothesis: whenever the cascade from the bound
reaches a fixed point, that point is the FIRST isolation of the subject.  (a) O1, "where"; (b) LOCATION shape,
conditional; it asserts no existence; (c) no cap or count.  Record: Theorems 7 and 11 (v9 §4, §6). -/
-- STANDING: OWED
def LandingIsFirstIsolation : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ tStar : ℝ,
    CascadeReaches (Fresh.disparitySet v k) (1 / (8 * m)) tStar →
      IsLeast {t : ℝ | 0 < t ∧ Fresh.IsolatedAt v k t} tStar

/-- Converse location form: any isolation is preceded by a cascade landing (the cascade finds an isolation no later
than any given one).  (a) O1, "the cascade shows where"; (b) LOCATION shape relative to a given isolation; its `∃`
is conditional on an isolation, so it is not an existence claim for isolation; (c) no cap or count; the number of
moves is `∃ N` with no bound, derived (Theorem 12) from the given isolation, not assumed.  Record: Theorem 12. -/
-- STANDING: OWED
def CascadeFindsIsolation : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m → ∀ t : ℝ, 0 < t →
    Fresh.IsolatedAt v k t → ∃ tStar ≤ t, CascadeReaches (Fresh.disparitySet v k) (1 / (8 * m)) tStar

/-- A reading at disparity `d` crossed an entering edge `N − 1/8` of some zone between `t` and `t'`: it was at or
before the edge at `t` and past it at `t'`. -/
-- STANDING: DEFINITION
def CrossedEnteringEdge (d t t' : ℝ) : Prop :=
  ∃ N : ℤ, d * t ≤ (N : ℝ) - 1 / 8 ∧ (N : ℝ) - 1 / 8 < d * t'

/-- (d3), as worded in the brief (E299 open item): when a reading of slot `7` with positive deviation is present at
the start, every obstruction after the first move consists of readings carried over an entering edge during that
move.  (a) O1, "why it goes there": the next obstruction is made by the move itself; (b) location shape (positions
before and after one move), no existence; (c) no cap or count.  Special case in the record:
`SeparationN.transport` (one reading captured exactly at a lap line, every other clear).
Finding [reasoned, not formalised]: the slot-7 hypothesis is idle; see `EnteringEdgeEveryMove`. -/
-- STANDING: OWED
def EnteringEdgeSlotSeven : Prop :=
  ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ k m, Fresh.IsDmin v k m →
    (∃ i, i ≠ k ∧ slot v k m i = 7 ∧ 0 < deviation v k m i) →
    ∀ t₁ : ℝ, Fresh.IsMove (Fresh.disparitySet v k) (1 / (8 * m)) t₁ →
      ∀ j, j ≠ k → Fresh.InWay |v j - v k| t₁ → CrossedEnteringEdge |v j - v k| (1 / (8 * m)) t₁

/-- (d3) without the slot hypothesis, at every state: for positive disparities, every reading in the way after a
move crossed an entering edge during that move.  [reasoned]: if `d` was in zone `N` at `t₀`, then `t₁ ≥` its opening,
so `d t₁ ≥ N + 1/8` and it is now in a zone `N' ≥ N + 1`, whose entering edge `N' − 1/8 ≥ N + 7/8` exceeds `d t₀`;
if `d` was clear at `t₀` in `[N + 1/8, N + 7/8]` then, since `t₁ ≥ t₀`, again `N' ≥ N + 1` and
`d t₀ ≤ N + 7/8 ≤ N' − 1/8 < d t₁`.  So this follows from `IsMove` alone and implies `EnteringEdgeSlotSeven`; as a
"where" statement it says only that the cascade's obstructions are new arrivals, not where the next landing is.
(a) O1, "why"; (b) location shape; (c) no cap or count. -/
-- STANDING: OWED
def EnteringEdgeEveryMove : Prop :=
  ∀ (ds : Finset ℝ), (∀ d ∈ ds, 0 < d) → ∀ t₀ t₁ : ℝ, 0 < t₀ → Fresh.IsMove ds t₀ t₁ → t₁ ≠ t₀ →
    ∀ d ∈ ds, Fresh.InWay d t₁ → CrossedEnteringEdge d t₀ t₁

/-! ## Classification (the brief's closing list)

DEFINITIONS (objects, no claim): `reading`, `gridIndex`, `slot`, `deviation`, `stateR`, `instantOf`, `position`,
`startLap`, `startOpeningR` (functions); `IsStartBlocker`, `CascadeReaches`, `CrossedEnteringEdge` (`Prop`s tagged
DEFINITION).

CLAIMS (all OWED here):
  * Could be judged "where" statements (location shape, no existence of an isolation asserted):
    `StartBlockers` (ii), `StartOpening`, `StartDisplacement`, `FirstMoveIsLargestStartOpening` (d1),
    `LandingIsFirstIsolation`, `CascadeFindsIsolation` (location relative to a given isolation),
    `EnteringEdgeSlotSeven` (d3), `EnteringEdgeEveryMove`.
    Change-of-variable claims, neither shape: `ClearIffPosition`, `PositionAtStart`.
  * Existence statements: `GridInstantDisplacement` (d2), which is a restatement of `Fresh.CascadeForm` (b)
    [one direction by `example`, the other reasoned through Theorem 13], hence of `Fresh.LonelyRunnerEight`.
Every "where" statement above is either a property of one move (positions before and after `IsMove`) or is conditional
on the cascade reaching a fixed point.  None of them asserts that the displacement lands; that part is exactly (b).
-/

end Fresh.Where
