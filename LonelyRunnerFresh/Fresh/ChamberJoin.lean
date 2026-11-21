import Mathlib.Tactic
import Fresh.K6BandUnion

/-!
# ChamberJoin: bridge gamma -- the class-match predicate and the datasheet-to-bridge join

New file (2026-11-21); nothing existing is edited.  Imports `Fresh.K6BandUnion` (bridge
beta: `TupleLonely` / `Feasible` / `band_union50` / `band_union50_via_datasheet` /
`band_union50_subset` / `colDead50_imp`, over bridge alpha's `K6Comps`) and, through it,
`Fresh.ChamberDatasheet` (the per-class atoms `chds_i : ColDead50 A B`, all 7,797 classes).

## The class-match predicate (gamma's InClass)

A chamber class is the probe's dedupe key: (skeleton cells, kL, kR, cellL, cellR, a, b),
where (a, b) are the EXACT edges of the instrument's COMP-DEAD kill component for every
recorded tuple of the class (verified data-side: `experiments/n8/chambjoin_verify_v1.out`,
three-way match dump <-> datasheet <-> stream 7,797/7,797, and the exact K6 join
`(a,b) in k6_components(rho)` re-verified on every class representative).  `ChamberClass`
carries the record (kL, kR, the edges A B as rationals, the skeleton's per-position CLOSED
cell bounds); `InClass rho cls` says: `rho`'s K6 decomposition contains `(cls.A, cls.B)` as
an EXACT component and `rho` lies in the class's closed cell-box.  `InClassSub` is the
containment variant (some component of `rho` CONTAINS `[A, B]` -- the [1, 7]-clipping
shape for boundary components).

## The join theorem shapes (gamma's instantiation of beta)

* `join50` -- exact-component join: the datasheet atom at the real-cast edges + the
  component membership give `not TupleLonely rho s` for every tail `s` in [25, 50).
  Consumes beta's `band_union50_via_datasheet` verbatim; gamma's work is exactly the
  InClass wiring (the membership is `hIn.1`; the cell-box half is carried for the
  partition step and is not needed by beta, which has no hypothesis on the other
  components).
* `join50_sub` -- containment join: consumes beta's `band_union50_subset` +
  `colDead50_imp`.

## What is emitted here, honestly

Per class (first tranche, cap `400` of 7797 classes; order NO-ALIVE-ON-GRID first,
then -n_cases): the class record `cls_i`, the recorded representative `rho_i` (exact
rationals from the probe's own dump), the cast bridge `castAB_i`, the PROVED join
`inclass_i : InClass rho_i cls_i` (the exact component membership by KERNEL DECIDE -- a
mirror discrepancy would fail the compile -- and the cell-box by fin_cases), the per-class
gamma instance `chjoin_i` for an ARBITRARY tuple matching the class, and the recorded
representative's column death `dead_i` (atom + exact join + gamma, the full
datasheet-to-beta-to-gamma loop per recorded tuple).  Emitted here: 400 of 7797
classes (400 NO-ALIVE-ON-GRID, 0 GRID-TOO-COARSE, 0 SKELETON-UNPROBED).

## Honest scope (what gamma does NOT yet carry)

* The atoms are component-level (S2 scope) at the FIXED edges (A, B); the S1
  chamber-window-uniform claim (the two-line at the q-window endpoints) fires on ZERO of
  the 7,797 census classes -- verified, not assumed (see Fresh.ChamberDatasheet's header).
  Within a chamber the certifying component's edges vary with the readings
  (`a_t = (8kL+1)/rho_L`), and the far tuples of the chamber defeat the two-line: the
  deaths there are interlacing (the RUNNING INTERSECTION of the components' band unions).
* `InClass` is proved here only for the RECORDED representatives (kernel decide, one per
  class).  The partition step -- carrying the deaths to EVERY tuple of the cell-box -- is
  the remaining hyperplane-partition work: for a general cell-box tuple the class's
  component edges vary, and the match is not the exact-component join.  The consumption
  shape for that step is landed in `Fresh.K6Gamma` (`partition_principle`: the cover
  hypothesis `EXISTS cls in classes, InClass rho cls OR InClassSub rho cls` is exactly
  what the assembly needs; gamma dispatches it).  The probe's no-alive-on-grid evidence
  (6,569 classes) is the data-side support; no Lean proof of the cover is faked here.
* A [25,50)-column death is the conclusion everywhere (the atoms' window).  The unbounded
  closed-band form is `Fresh.K6Gamma.gamma_joinC` (consumes beta's `band_union`).

Data side: `experiments/n8/chambjoin_verify_v1.py` (+ `chambjoin_verify_v1.out`,
`chambjoin_classes_v1.json`); generator of this file: `chambjoin_lean_gen_v1.py`.
-/

set_option allowUnsafeReducibility true
attribute [local reducible] Rat.mul Rat.inv

namespace Fresh.ChamberJoin

/-! ## §1 The class-match definitions -/

/-- STANDING: DEFINITION -- a chamber class record: the certifying component's lap
indices (`kL` the L reading's lap / exit side, `kR` the R reading's lap / entry side),
its exact edges `A B : ℚ`, and the skeleton's per-position closed cell bounds
(the cell-box). -/
structure ChamberClass where
  /-- the L reading's lap (exit side of the certifying component) -/
  kL : ℕ
  /-- the R reading's lap (entry side of the certifying component) -/
  kR : ℕ
  /-- the certifying component's left edge (an exact K6 component of the recorded tuples) -/
  A : ℚ
  /-- the certifying component's right edge -/
  B : ℚ
  /-- per-position cell lower bound (closed box) -/
  lo : Fin 5 → ℚ
  /-- per-position cell upper bound (closed box) -/
  hi : Fin 5 → ℚ

/-- STANDING: DEFINITION -- the cell-box: every reading in its skeleton cell's closed
bounds. -/
def InBox (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  ∀ i : Fin 5, cls.lo i ≤ rho i ∧ rho i ≤ cls.hi i

/-- STANDING: DEFINITION -- gamma's class match: `rho`'s K6 decomposition contains the
class's certifying component `(A, B)` EXACTLY, and `rho` lies in the class's cell-box. -/
def InClass (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  (cls.A, cls.B) ∈ K6Comps rho ∧ InBox rho cls

/-- STANDING: DEFINITION -- the containment variant of the class match: some component of
`rho` CONTAINS the class's dead interval `[A, B]` (the [1, 7]-clipping shape; consumes
beta's `band_union50_subset`). -/
def InClassSub (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  ∃ q ∈ K6Comps rho, q.1 ≤ cls.A ∧ cls.B ≤ q.2 ∧ InBox rho cls

/-! ## §2 The join theorem shapes (gamma's instantiation of beta) -/

/-- **The join theorem shape (exact-component join, datasheet atom).**  The class atom at
the real-cast edges + the exact component membership (from `InClass`, `hIn.1`) give the
tuple's column death over [25, 50) -- beta's `band_union50_via_datasheet` verbatim; no
hypothesis on the other components, and the list may be empty (vacuous). -/
theorem join50 (rho : Fin 5 → ℚ) (cls : ChamberClass) (A B : ℝ)
    (hAB : ((cls.A : ℚ) : ℝ) = A ∧ ((cls.B : ℚ) : ℝ) = B)
    (hp : (cls.A, cls.B) ∈ K6Comps rho)
    (hcd : Fresh.ChamberDatasheet.ColDead50 A B)
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  Fresh.K6BandUnion.band_union50_via_datasheet rho cls.A cls.B A B hAB.1 hAB.2 hp hcd s hs h50

/-- **The containment join shape.**  A class atom whose interval `[A, B]` lies INSIDE some
component of `rho` kills the tuple over [25, 50) (the [1, 7]-clipping shape; consumes
beta's `band_union50_subset` via the real-to-rational transport `colDead50_imp`). -/
theorem join50_sub (rho : Fin 5 → ℚ) (cls : ChamberClass)
    (hp : ∃ q ∈ K6Comps rho, q.1 ≤ cls.A ∧ cls.B ≤ q.2)
    (hB1 : (1:ℚ) ≤ cls.B)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) : ¬ Fresh.K6BandUnion.TupleLonely rho s := by
  obtain ⟨q, hq, h1, h2⟩ := hp
  exact Fresh.K6BandUnion.band_union50_subset rho q hq cls.A cls.B ⟨h1, h2⟩ hB1
    (Fresh.K6BandUnion.colDead50_imp cls.A cls.B ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ) rfl rfl
      hcd) s hs h50

/-! ## §3 The per-class instances (the emitted join tranche)

One class record + representative + proved join + gamma instance + recorded death per
census class (the emission is capped only by compile budget; the order is
NO-ALIVE-ON-GRID first, then GRID-TOO-COARSE, then SKELETON-UNPROBED, then -n_cases).
The atom `chds_<i>` is `Fresh.ChamberDatasheet`'s own theorem at the same class index
(the datasheet's idx order equals this order -- verified data-side, all 7,797). -/

/-- jj#0 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_0 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 0 (exact rationals, the probe's own
case dump). -/
def rho_0 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 76/5]

theorem castAB_0 : ((cls_0.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_0.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_0]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_0`/`cls_0` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_0 : InClass rho_0 cls_0 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_0, rho_0] <;> norm_num⟩

/-- **gamma at class 0, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_0`
consumed through `join50`. -/
theorem chjoin_0 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_0) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_0 (85/76 : ℝ) (75/58 : ℝ) castAB_0 hIn.1 Fresh.ChamberDatasheet.chds_0 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 0's own tuple (atom `chds_0` + proved join `inclass_0` +
`chjoin_0`). -/
theorem dead_0 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_0 s :=
  chjoin_0 rho_0 s hs h50 inclass_0

/-- jj#1 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_1 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 1 (exact rationals, the probe's own
case dump). -/
def rho_1 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 77/5]

theorem castAB_1 : ((cls_1.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_1.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_1]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_1`/`cls_1` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_1 : InClass rho_1 cls_1 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_1, rho_1] <;> norm_num⟩

/-- **gamma at class 1, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_1`
consumed through `join50`. -/
theorem chjoin_1 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_1) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_1 (85/77 : ℝ) (75/58 : ℝ) castAB_1 hIn.1 Fresh.ChamberDatasheet.chds_1 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 1's own tuple (atom `chds_1` + proved join `inclass_1` +
`chjoin_1`). -/
theorem dead_1 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_1 s :=
  chjoin_1 rho_1 s hs h50 inclass_1

/-- jj#2 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_2 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 2 (exact rationals, the probe's own
case dump). -/
def rho_2 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 78/5]

theorem castAB_2 : ((cls_2.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_2.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_2]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_2`/`cls_2` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_2 : InClass rho_2 cls_2 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_2, rho_2] <;> norm_num⟩

/-- **gamma at class 2, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_2`
consumed through `join50`. -/
theorem chjoin_2 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_2) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_2 (85/78 : ℝ) (75/58 : ℝ) castAB_2 hIn.1 Fresh.ChamberDatasheet.chds_2 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 2's own tuple (atom `chds_2` + proved join `inclass_2` +
`chjoin_2`). -/
theorem dead_2 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_2 s :=
  chjoin_2 rho_2 s hs h50 inclass_2

/-- jj#3 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_3 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 3 (exact rationals, the probe's own
case dump). -/
def rho_3 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 79/5]

theorem castAB_3 : ((cls_3.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_3.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_3]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_3`/`cls_3` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_3 : InClass rho_3 cls_3 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_3, rho_3] <;> norm_num⟩

/-- **gamma at class 3, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_3`
consumed through `join50`. -/
theorem chjoin_3 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_3) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_3 (85/79 : ℝ) (75/58 : ℝ) castAB_3 hIn.1 Fresh.ChamberDatasheet.chds_3 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 3's own tuple (atom `chds_3` + proved join `inclass_3` +
`chjoin_3`). -/
theorem dead_3 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_3 s :=
  chjoin_3 rho_3 s hs h50 inclass_3

/-- jj#4 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_4 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 4 (exact rationals, the probe's own
case dump). -/
def rho_4 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 16]

theorem castAB_4 : ((cls_4.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_4.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_4]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_4`/`cls_4` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_4 : InClass rho_4 cls_4 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_4, rho_4] <;> norm_num⟩

/-- **gamma at class 4, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_4`
consumed through `join50`. -/
theorem chjoin_4 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_4) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_4 (17/16 : ℝ) (75/58 : ℝ) castAB_4 hIn.1 Fresh.ChamberDatasheet.chds_4 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 4's own tuple (atom `chds_4` + proved join `inclass_4` +
`chjoin_4`). -/
theorem dead_4 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_4 s :=
  chjoin_4 rho_4 s hs h50 inclass_4

/-- jj#5 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_5 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 5 (exact rationals, the probe's own
case dump). -/
def rho_5 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 81/5]

theorem castAB_5 : ((cls_5.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_5.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_5]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_5`/`cls_5` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_5 : InClass rho_5 cls_5 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_5, rho_5] <;> norm_num⟩

/-- **gamma at class 5, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_5`
consumed through `join50`. -/
theorem chjoin_5 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_5) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_5 (85/81 : ℝ) (75/58 : ℝ) castAB_5 hIn.1 Fresh.ChamberDatasheet.chds_5 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 5's own tuple (atom `chds_5` + proved join `inclass_5` +
`chjoin_5`). -/
theorem dead_5 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_5 s :=
  chjoin_5 rho_5 s hs h50 inclass_5

/-- jj#6 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_6 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 6 (exact rationals, the probe's own
case dump). -/
def rho_6 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 82/5]

theorem castAB_6 : ((cls_6.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_6.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_6]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_6`/`cls_6` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_6 : InClass rho_6 cls_6 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_6, rho_6] <;> norm_num⟩

/-- **gamma at class 6, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_6`
consumed through `join50`. -/
theorem chjoin_6 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_6) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_6 (85/82 : ℝ) (75/58 : ℝ) castAB_6 hIn.1 Fresh.ChamberDatasheet.chds_6 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 6's own tuple (atom `chds_6` + proved join `inclass_6` +
`chjoin_6`). -/
theorem dead_6 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_6 s :=
  chjoin_6 rho_6 s hs h50 inclass_6

/-- jj#7 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_7 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 7 (exact rationals, the probe's own
case dump). -/
def rho_7 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 83/5]

theorem castAB_7 : ((cls_7.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_7.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_7]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_7`/`cls_7` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_7 : InClass rho_7 cls_7 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_7, rho_7] <;> norm_num⟩

/-- **gamma at class 7, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_7`
consumed through `join50`. -/
theorem chjoin_7 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_7) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_7 (85/83 : ℝ) (75/58 : ℝ) castAB_7 hIn.1 Fresh.ChamberDatasheet.chds_7 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 7's own tuple (atom `chds_7` + proved join `inclass_7` +
`chjoin_7`). -/
theorem dead_7 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_7 s :=
  chjoin_7 rho_7 s hs h50 inclass_7

/-- jj#8 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/58 | D2 | 3864 cases | NO-ALIVE-ON-GRID -/
def cls_8 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 8 (exact rationals, the probe's own
case dump). -/
def rho_8 : Fin 5 → ℚ := ![1, 1, 9, 58/5, 84/5]

theorem castAB_8 : ((cls_8.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_8.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_8]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_8`/`cls_8` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_8 : InClass rho_8 cls_8 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_8, rho_8] <;> norm_num⟩

/-- **gamma at class 8, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_8`
consumed through `join50`. -/
theorem chjoin_8 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_8) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_8 (85/84 : ℝ) (75/58 : ℝ) castAB_8 hIn.1 Fresh.ChamberDatasheet.chds_8 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 8's own tuple (atom `chds_8` + proved join `inclass_8` +
`chjoin_8`). -/
theorem dead_8 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_8 s :=
  chjoin_8 rho_8 s hs h50 inclass_8

/-- jj#9 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3740 cases | NO-ALIVE-ON-GRID -/
def cls_9 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 9 (exact rationals, the probe's own
case dump). -/
def rho_9 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 15]

theorem castAB_9 : ((cls_9.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_9.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_9]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_9`/`cls_9` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_9 : InClass rho_9 cls_9 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_9, rho_9] <;> norm_num⟩

/-- **gamma at class 9, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_9`
consumed through `join50`. -/
theorem chjoin_9 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_9) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_9 (85/63 : ℝ) (23/15 : ℝ) castAB_9 hIn.1 Fresh.ChamberDatasheet.chds_9 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 9's own tuple (atom `chds_9` + proved join `inclass_9` +
`chjoin_9`). -/
theorem dead_9 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_9 s :=
  chjoin_9 rho_9 s hs h50 inclass_9

/-- jj#10 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3740 cases | NO-ALIVE-ON-GRID -/
def cls_10 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 10 (exact rationals, the probe's own
case dump). -/
def rho_10 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 15]

theorem castAB_10 : ((cls_10.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_10.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_10]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_10`/`cls_10` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_10 : InClass rho_10 cls_10 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_10, rho_10] <;> norm_num⟩

/-- **gamma at class 10, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_10`
consumed through `join50`. -/
theorem chjoin_10 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_10) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_10 (85/63 : ℝ) (23/15 : ℝ) castAB_10 hIn.1 Fresh.ChamberDatasheet.chds_10 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 10's own tuple (atom `chds_10` + proved join `inclass_10` +
`chjoin_10`). -/
theorem dead_10 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_10 s :=
  chjoin_10 rho_10 s hs h50 inclass_10

/-- jj#11 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3570 cases | NO-ALIVE-ON-GRID -/
def cls_11 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 11 (exact rationals, the probe's own
case dump). -/
def rho_11 : Fin 5 → ℚ := ![1, 1, 9, 63/5, 15]

theorem castAB_11 : ((cls_11.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_11.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_11]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_11`/`cls_11` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_11 : InClass rho_11 cls_11 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_11, rho_11] <;> norm_num⟩

/-- **gamma at class 11, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_11`
consumed through `join50`. -/
theorem chjoin_11 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_11) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_11 (85/63 : ℝ) (23/15 : ℝ) castAB_11 hIn.1 Fresh.ChamberDatasheet.chds_11 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 11's own tuple (atom `chds_11` + proved join `inclass_11` +
`chjoin_11`). -/
theorem dead_11 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_11 s :=
  chjoin_11 rho_11 s hs h50 inclass_11

/-- jj#12 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3570 cases | NO-ALIVE-ON-GRID -/
def cls_12 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 12 (exact rationals, the probe's own
case dump). -/
def rho_12 : Fin 5 → ℚ := ![1, 1, 9, 63/5, 15]

theorem castAB_12 : ((cls_12.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_12.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_12]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_12`/`cls_12` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_12 : InClass rho_12 cls_12 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_12, rho_12] <;> norm_num⟩

/-- **gamma at class 12, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_12`
consumed through `join50`. -/
theorem chjoin_12 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_12) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_12 (85/63 : ℝ) (23/15 : ℝ) castAB_12 hIn.1 Fresh.ChamberDatasheet.chds_12 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 12's own tuple (atom `chds_12` + proved join `inclass_12` +
`chjoin_12`). -/
theorem dead_12 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_12 s :=
  chjoin_12 rho_12 s hs h50 inclass_12

/-- jj#13 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 3520 cases | NO-ALIVE-ON-GRID -/
def cls_13 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 13 (exact rationals, the probe's own
case dump). -/
def rho_13 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 15]

theorem castAB_13 : ((cls_13.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_13.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_13]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_13`/`cls_13` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_13 : InClass rho_13 cls_13 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_13, rho_13] <;> norm_num⟩

/-- **gamma at class 13, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_13`
consumed through `join50`. -/
theorem chjoin_13 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_13) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_13 (85/64 : ℝ) (23/15 : ℝ) castAB_13 hIn.1 Fresh.ChamberDatasheet.chds_13 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 13's own tuple (atom `chds_13` + proved join `inclass_13` +
`chjoin_13`). -/
theorem dead_13 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_13 s :=
  chjoin_13 rho_13 s hs h50 inclass_13

/-- jj#14 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 3520 cases | NO-ALIVE-ON-GRID -/
def cls_14 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 14 (exact rationals, the probe's own
case dump). -/
def rho_14 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 15]

theorem castAB_14 : ((cls_14.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_14.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_14]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_14`/`cls_14` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_14 : InClass rho_14 cls_14 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_14, rho_14] <;> norm_num⟩

/-- **gamma at class 14, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_14`
consumed through `join50`. -/
theorem chjoin_14 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_14) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_14 (85/64 : ℝ) (23/15 : ℝ) castAB_14 hIn.1 Fresh.ChamberDatasheet.chds_14 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 14's own tuple (atom `chds_14` + proved join `inclass_14` +
`chjoin_14`). -/
theorem dead_14 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_14 s :=
  chjoin_14 rho_14 s hs h50 inclass_14

/-- jj#15 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 3465 cases | NO-ALIVE-ON-GRID -/
def cls_15 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 15 (exact rationals, the probe's own
case dump). -/
def rho_15 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 17]

theorem castAB_15 : ((cls_15.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_15.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_15]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_15`/`cls_15` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_15 : InClass rho_15 cls_15 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_15, rho_15] <;> norm_num⟩

/-- **gamma at class 15, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_15`
consumed through `join50`. -/
theorem chjoin_15 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_15) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_15 (85/72 : ℝ) (23/17 : ℝ) castAB_15 hIn.1 Fresh.ChamberDatasheet.chds_15 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 15's own tuple (atom `chds_15` + proved join `inclass_15` +
`chjoin_15`). -/
theorem dead_15 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_15 s :=
  chjoin_15 rho_15 s hs h50 inclass_15

/-- jj#16 | PPG1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 3465 cases | NO-ALIVE-ON-GRID -/
def cls_16 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 16 (exact rationals, the probe's own
case dump). -/
def rho_16 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 17]

theorem castAB_16 : ((cls_16.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_16.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_16]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_16`/`cls_16` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_16 : InClass rho_16 cls_16 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_16, rho_16] <;> norm_num⟩

/-- **gamma at class 16, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_16`
consumed through `join50`. -/
theorem chjoin_16 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_16) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_16 (85/72 : ℝ) (23/17 : ℝ) castAB_16 hIn.1 Fresh.ChamberDatasheet.chds_16 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 16's own tuple (atom `chds_16` + proved join `inclass_16` +
`chjoin_16`). -/
theorem dead_16 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_16 s :=
  chjoin_16 rho_16 s hs h50 inclass_16

/-- jj#17 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 3465 cases | NO-ALIVE-ON-GRID -/
def cls_17 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 17 (exact rationals, the probe's own
case dump). -/
def rho_17 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 17]

theorem castAB_17 : ((cls_17.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_17.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_17]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_17`/`cls_17` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_17 : InClass rho_17 cls_17 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_17, rho_17] <;> norm_num⟩

/-- **gamma at class 17, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_17`
consumed through `join50`. -/
theorem chjoin_17 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_17) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_17 (85/72 : ℝ) (23/17 : ℝ) castAB_17 hIn.1 Fresh.ChamberDatasheet.chds_17 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 17's own tuple (atom `chds_17` + proved join `inclass_17` +
`chjoin_17`). -/
theorem dead_17 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_17 s :=
  chjoin_17 rho_17 s hs h50 inclass_17

/-- jj#18 | PG1G1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 3465 cases | NO-ALIVE-ON-GRID -/
def cls_18 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 17], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 18 (exact rationals, the probe's own
case dump). -/
def rho_18 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 17]

theorem castAB_18 : ((cls_18.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_18.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_18]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_18`/`cls_18` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_18 : InClass rho_18 cls_18 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_18, rho_18] <;> norm_num⟩

/-- **gamma at class 18, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_18`
consumed through `join50`. -/
theorem chjoin_18 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_18) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_18 (85/72 : ℝ) (23/17 : ℝ) castAB_18 hIn.1 Fresh.ChamberDatasheet.chds_18 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 18's own tuple (atom `chds_18` + proved join `inclass_18` +
`chjoin_18`). -/
theorem dead_18 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_18 s :=
  chjoin_18 rho_18 s hs h50 inclass_18

/-- jj#19 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/74 | D2 | 3412 cases | NO-ALIVE-ON-GRID -/
def cls_19 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 19 (exact rationals, the probe's own
case dump). -/
def rho_19 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 74/5]

theorem castAB_19 : ((cls_19.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_19.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_19]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_19`/`cls_19` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_19 : InClass rho_19 cls_19 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_19, rho_19] <;> norm_num⟩

/-- **gamma at class 19, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_19`
consumed through `join50`. -/
theorem chjoin_19 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_19) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_19 (85/63 : ℝ) (115/74 : ℝ) castAB_19 hIn.1 Fresh.ChamberDatasheet.chds_19 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 19's own tuple (atom `chds_19` + proved join `inclass_19` +
`chjoin_19`). -/
theorem dead_19 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_19 s :=
  chjoin_19 rho_19 s hs h50 inclass_19

/-- jj#20 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 3360 cases | NO-ALIVE-ON-GRID -/
def cls_20 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 20 (exact rationals, the probe's own
case dump). -/
def rho_20 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 15]

theorem castAB_20 : ((cls_20.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_20.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_20]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_20`/`cls_20` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_20 : InClass rho_20 cls_20 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_20, rho_20] <;> norm_num⟩

/-- **gamma at class 20, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_20`
consumed through `join50`. -/
theorem chjoin_20 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_20) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_20 (85/64 : ℝ) (23/15 : ℝ) castAB_20 hIn.1 Fresh.ChamberDatasheet.chds_20 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 20's own tuple (atom `chds_20` + proved join `inclass_20` +
`chjoin_20`). -/
theorem dead_20 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_20 s :=
  chjoin_20 rho_20 s hs h50 inclass_20

/-- jj#21 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 3360 cases | NO-ALIVE-ON-GRID -/
def cls_21 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 21 (exact rationals, the probe's own
case dump). -/
def rho_21 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 15]

theorem castAB_21 : ((cls_21.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_21.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_21]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_21`/`cls_21` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_21 : InClass rho_21 cls_21 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_21, rho_21] <;> norm_num⟩

/-- **gamma at class 21, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_21`
consumed through `join50`. -/
theorem chjoin_21 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_21) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_21 (85/64 : ℝ) (23/15 : ℝ) castAB_21 hIn.1 Fresh.ChamberDatasheet.chds_21 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 21's own tuple (atom `chds_21` + proved join `inclass_21` +
`chjoin_21`). -/
theorem dead_21 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_21 s :=
  chjoin_21 rho_21 s hs h50 inclass_21

/-- jj#22 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/74 | D2 | 3300 cases | NO-ALIVE-ON-GRID -/
def cls_22 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 22 (exact rationals, the probe's own
case dump). -/
def rho_22 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 74/5]

theorem castAB_22 : ((cls_22.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_22.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_22]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_22`/`cls_22` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_22 : InClass rho_22 cls_22 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_22, rho_22] <;> norm_num⟩

/-- **gamma at class 22, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_22`
consumed through `join50`. -/
theorem chjoin_22 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_22) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_22 (85/64 : ℝ) (115/74 : ℝ) castAB_22 hIn.1 Fresh.ChamberDatasheet.chds_22 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 22's own tuple (atom `chds_22` + proved join `inclass_22` +
`chjoin_22`). -/
theorem dead_22 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_22 s :=
  chjoin_22 rho_22 s hs h50 inclass_22

/-- jj#23 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_23 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 23 (exact rationals, the probe's own
case dump). -/
def rho_23 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 76/5]

theorem castAB_23 : ((cls_23.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_23.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_23]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_23`/`cls_23` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_23 : InClass rho_23 cls_23 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_23, rho_23] <;> norm_num⟩

/-- **gamma at class 23, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_23`
consumed through `join50`. -/
theorem chjoin_23 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_23) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_23 (85/76 : ℝ) (25/19 : ℝ) castAB_23 hIn.1 Fresh.ChamberDatasheet.chds_23 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 23's own tuple (atom `chds_23` + proved join `inclass_23` +
`chjoin_23`). -/
theorem dead_23 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_23 s :=
  chjoin_23 rho_23 s hs h50 inclass_23

/-- jj#24 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_24 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 24 (exact rationals, the probe's own
case dump). -/
def rho_24 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 77/5]

theorem castAB_24 : ((cls_24.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_24.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_24]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_24`/`cls_24` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_24 : InClass rho_24 cls_24 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_24, rho_24] <;> norm_num⟩

/-- **gamma at class 24, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_24`
consumed through `join50`. -/
theorem chjoin_24 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_24) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_24 (85/77 : ℝ) (25/19 : ℝ) castAB_24 hIn.1 Fresh.ChamberDatasheet.chds_24 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 24's own tuple (atom `chds_24` + proved join `inclass_24` +
`chjoin_24`). -/
theorem dead_24 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_24 s :=
  chjoin_24 rho_24 s hs h50 inclass_24

/-- jj#25 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_25 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 25 (exact rationals, the probe's own
case dump). -/
def rho_25 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 78/5]

theorem castAB_25 : ((cls_25.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_25.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_25]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_25`/`cls_25` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_25 : InClass rho_25 cls_25 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_25, rho_25] <;> norm_num⟩

/-- **gamma at class 25, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_25`
consumed through `join50`. -/
theorem chjoin_25 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_25) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_25 (85/78 : ℝ) (25/19 : ℝ) castAB_25 hIn.1 Fresh.ChamberDatasheet.chds_25 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 25's own tuple (atom `chds_25` + proved join `inclass_25` +
`chjoin_25`). -/
theorem dead_25 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_25 s :=
  chjoin_25 rho_25 s hs h50 inclass_25

/-- jj#26 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_26 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 26 (exact rationals, the probe's own
case dump). -/
def rho_26 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 79/5]

theorem castAB_26 : ((cls_26.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_26.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_26]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_26`/`cls_26` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_26 : InClass rho_26 cls_26 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_26, rho_26] <;> norm_num⟩

/-- **gamma at class 26, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_26`
consumed through `join50`. -/
theorem chjoin_26 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_26) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_26 (85/79 : ℝ) (25/19 : ℝ) castAB_26 hIn.1 Fresh.ChamberDatasheet.chds_26 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 26's own tuple (atom `chds_26` + proved join `inclass_26` +
`chjoin_26`). -/
theorem dead_26 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_26 s :=
  chjoin_26 rho_26 s hs h50 inclass_26

/-- jj#27 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_27 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 27 (exact rationals, the probe's own
case dump). -/
def rho_27 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 16]

theorem castAB_27 : ((cls_27.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_27.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_27]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_27`/`cls_27` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_27 : InClass rho_27 cls_27 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_27, rho_27] <;> norm_num⟩

/-- **gamma at class 27, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_27`
consumed through `join50`. -/
theorem chjoin_27 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_27) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_27 (17/16 : ℝ) (25/19 : ℝ) castAB_27 hIn.1 Fresh.ChamberDatasheet.chds_27 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 27's own tuple (atom `chds_27` + proved join `inclass_27` +
`chjoin_27`). -/
theorem dead_27 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_27 s :=
  chjoin_27 rho_27 s hs h50 inclass_27

/-- jj#28 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_28 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 28 (exact rationals, the probe's own
case dump). -/
def rho_28 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 81/5]

theorem castAB_28 : ((cls_28.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_28.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_28]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_28`/`cls_28` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_28 : InClass rho_28 cls_28 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_28, rho_28] <;> norm_num⟩

/-- **gamma at class 28, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_28`
consumed through `join50`. -/
theorem chjoin_28 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_28) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_28 (85/81 : ℝ) (25/19 : ℝ) castAB_28 hIn.1 Fresh.ChamberDatasheet.chds_28 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 28's own tuple (atom `chds_28` + proved join `inclass_28` +
`chjoin_28`). -/
theorem dead_28 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_28 s :=
  chjoin_28 rho_28 s hs h50 inclass_28

/-- jj#29 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_29 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 29 (exact rationals, the probe's own
case dump). -/
def rho_29 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 82/5]

theorem castAB_29 : ((cls_29.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_29.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_29]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_29`/`cls_29` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_29 : InClass rho_29 cls_29 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_29, rho_29] <;> norm_num⟩

/-- **gamma at class 29, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_29`
consumed through `join50`. -/
theorem chjoin_29 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_29) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_29 (85/82 : ℝ) (25/19 : ℝ) castAB_29 hIn.1 Fresh.ChamberDatasheet.chds_29 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 29's own tuple (atom `chds_29` + proved join `inclass_29` +
`chjoin_29`). -/
theorem dead_29 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_29 s :=
  chjoin_29 rho_29 s hs h50 inclass_29

/-- jj#30 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=25/19 | D2 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_30 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 30 (exact rationals, the probe's own
case dump). -/
def rho_30 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 83/5]

theorem castAB_30 : ((cls_30.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_30.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_30]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_30`/`cls_30` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_30 : InClass rho_30 cls_30 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_30, rho_30] <;> norm_num⟩

/-- **gamma at class 30, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_30`
consumed through `join50`. -/
theorem chjoin_30 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_30) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_30 (85/83 : ℝ) (25/19 : ℝ) castAB_30 hIn.1 Fresh.ChamberDatasheet.chds_30 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 30's own tuple (atom `chds_30` + proved join `inclass_30` +
`chjoin_30`). -/
theorem dead_30 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_30 s :=
  chjoin_30 rho_30 s hs h50 inclass_30

/-- jj#31 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=25/19 | D1 | 3289 cases | NO-ALIVE-ON-GRID -/
def cls_31 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 31 (exact rationals, the probe's own
case dump). -/
def rho_31 : Fin 5 → ℚ := ![1, 1, 9, 57/5, 84/5]

theorem castAB_31 : ((cls_31.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_31.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_31]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_31`/`cls_31` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_31 : InClass rho_31 cls_31 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_31, rho_31] <;> norm_num⟩

/-- **gamma at class 31, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_31`
consumed through `join50`. -/
theorem chjoin_31 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_31) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_31 (85/84 : ℝ) (25/19 : ℝ) castAB_31 hIn.1 Fresh.ChamberDatasheet.chds_31 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 31's own tuple (atom `chds_31` + proved join `inclass_31` +
`chjoin_31`). -/
theorem dead_31 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_31 s :=
  chjoin_31 rho_31 s hs h50 inclass_31

/-- jj#32 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_32 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 32 (exact rationals, the probe's own
case dump). -/
def rho_32 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 83/5]

theorem castAB_32 : ((cls_32.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_32.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_32]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_32`/`cls_32` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_32 : InClass rho_32 cls_32 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_32, rho_32] <;> norm_num⟩

/-- **gamma at class 32, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_32`
consumed through `join50`. -/
theorem chjoin_32 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_32) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_32 (85/72 : ℝ) (115/83 : ℝ) castAB_32 hIn.1 Fresh.ChamberDatasheet.chds_32 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 32's own tuple (atom `chds_32` + proved join `inclass_32` +
`chjoin_32`). -/
theorem dead_32 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_32 s :=
  chjoin_32 rho_32 s hs h50 inclass_32

/-- jj#33 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_33 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 33 (exact rationals, the probe's own
case dump). -/
def rho_33 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 84/5]

theorem castAB_33 : ((cls_33.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_33.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_33]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_33`/`cls_33` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_33 : InClass rho_33 cls_33 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_33, rho_33] <;> norm_num⟩

/-- **gamma at class 33, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_33`
consumed through `join50`. -/
theorem chjoin_33 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_33) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_33 (85/72 : ℝ) (115/84 : ℝ) castAB_33 hIn.1 Fresh.ChamberDatasheet.chds_33 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 33's own tuple (atom `chds_33` + proved join `inclass_33` +
`chjoin_33`). -/
theorem dead_33 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_33 s :=
  chjoin_33 rho_33 s hs h50 inclass_33

/-- jj#34 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_34 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 34 (exact rationals, the probe's own
case dump). -/
def rho_34 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 17]

theorem castAB_34 : ((cls_34.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_34.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_34]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_34`/`cls_34` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_34 : InClass rho_34 cls_34 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_34, rho_34] <;> norm_num⟩

/-- **gamma at class 34, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_34`
consumed through `join50`. -/
theorem chjoin_34 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_34) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_34 (85/73 : ℝ) (23/17 : ℝ) castAB_34 hIn.1 Fresh.ChamberDatasheet.chds_34 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 34's own tuple (atom `chds_34` + proved join `inclass_34` +
`chjoin_34`). -/
theorem dead_34 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_34 s :=
  chjoin_34 rho_34 s hs h50 inclass_34

/-- jj#35 | PPG1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_35 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 35 (exact rationals, the probe's own
case dump). -/
def rho_35 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 17]

theorem castAB_35 : ((cls_35.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_35.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_35]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_35`/`cls_35` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_35 : InClass rho_35 cls_35 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_35, rho_35] <;> norm_num⟩

/-- **gamma at class 35, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_35`
consumed through `join50`. -/
theorem chjoin_35 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_35) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_35 (85/73 : ℝ) (23/17 : ℝ) castAB_35 hIn.1 Fresh.ChamberDatasheet.chds_35 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 35's own tuple (atom `chds_35` + proved join `inclass_35` +
`chjoin_35`). -/
theorem dead_35 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_35 s :=
  chjoin_35 rho_35 s hs h50 inclass_35

/-- jj#36 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_36 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 36 (exact rationals, the probe's own
case dump). -/
def rho_36 : Fin 5 → ℚ := ![1, 9, 73/5, 15, 17]

theorem castAB_36 : ((cls_36.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_36.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_36]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_36`/`cls_36` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_36 : InClass rho_36 cls_36 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_36, rho_36] <;> norm_num⟩

/-- **gamma at class 36, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_36`
consumed through `join50`. -/
theorem chjoin_36 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_36) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_36 (85/73 : ℝ) (23/17 : ℝ) castAB_36 hIn.1 Fresh.ChamberDatasheet.chds_36 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 36's own tuple (atom `chds_36` + proved join `inclass_36` +
`chjoin_36`). -/
theorem dead_36 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_36 s :=
  chjoin_36 rho_36 s hs h50 inclass_36

/-- jj#37 | PG1G1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 3234 cases | NO-ALIVE-ON-GRID -/
def cls_37 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 17], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 37 (exact rationals, the probe's own
case dump). -/
def rho_37 : Fin 5 → ℚ := ![1, 9, 73/5, 15, 17]

theorem castAB_37 : ((cls_37.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_37.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_37]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_37`/`cls_37` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_37 : InClass rho_37 cls_37 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_37, rho_37] <;> norm_num⟩

/-- **gamma at class 37, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_37`
consumed through `join50`. -/
theorem chjoin_37 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_37) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_37 (85/73 : ℝ) (23/17 : ℝ) castAB_37 hIn.1 Fresh.ChamberDatasheet.chds_37 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 37's own tuple (atom `chds_37` + proved join `inclass_37` +
`chjoin_37`). -/
theorem dead_37 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_37 s :=
  chjoin_37 rho_37 s hs h50 inclass_37

/-- jj#38 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/58 | D2 | 3220 cases | NO-ALIVE-ON-GRID -/
def cls_38 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 38 (exact rationals, the probe's own
case dump). -/
def rho_38 : Fin 5 → ℚ := ![1, 9, 58/5, 76/5, 76/5]

theorem castAB_38 : ((cls_38.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_38.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_38]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_38`/`cls_38` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_38 : InClass rho_38 cls_38 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_38, rho_38] <;> norm_num⟩

/-- **gamma at class 38, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_38`
consumed through `join50`. -/
theorem chjoin_38 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_38) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_38 (85/76 : ℝ) (75/58 : ℝ) castAB_38 hIn.1 Fresh.ChamberDatasheet.chds_38 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 38's own tuple (atom `chds_38` + proved join `inclass_38` +
`chjoin_38`). -/
theorem dead_38 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_38 s :=
  chjoin_38 rho_38 s hs h50 inclass_38

/-- jj#39 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/74 | D2 | 3150 cases | NO-ALIVE-ON-GRID -/
def cls_39 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 39 (exact rationals, the probe's own
case dump). -/
def rho_39 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 74/5]

theorem castAB_39 : ((cls_39.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_39.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_39]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_39`/`cls_39` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_39 : InClass rho_39 cls_39 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_39, rho_39] <;> norm_num⟩

/-- **gamma at class 39, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_39`
consumed through `join50`. -/
theorem chjoin_39 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_39) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_39 (85/64 : ℝ) (115/74 : ℝ) castAB_39 hIn.1 Fresh.ChamberDatasheet.chds_39 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 39's own tuple (atom `chds_39` + proved join `inclass_39` +
`chjoin_39`). -/
theorem dead_39 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_39 s :=
  chjoin_39 rho_39 s hs h50 inclass_39

/-- jj#40 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 3135 cases | NO-ALIVE-ON-GRID -/
def cls_40 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 40 (exact rationals, the probe's own
case dump). -/
def rho_40 : Fin 5 → ℚ := ![1, 7, 9, 13, 15]

theorem castAB_40 : ((cls_40.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_40.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_40]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_40`/`cls_40` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_40 : InClass rho_40 cls_40 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_40, rho_40] <;> norm_num⟩

/-- **gamma at class 40, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_40`
consumed through `join50`. -/
theorem chjoin_40 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_40) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_40 (17/13 : ℝ) (23/15 : ℝ) castAB_40 hIn.1 Fresh.ChamberDatasheet.chds_40 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 40's own tuple (atom `chds_40` + proved join `inclass_40` +
`chjoin_40`). -/
theorem dead_40 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_40 s :=
  chjoin_40 rho_40 s hs h50 inclass_40

/-- jj#41 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 3135 cases | NO-ALIVE-ON-GRID -/
def cls_41 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 41 (exact rationals, the probe's own
case dump). -/
def rho_41 : Fin 5 → ℚ := ![1, 7, 9, 13, 15]

theorem castAB_41 : ((cls_41.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_41.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_41]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_41`/`cls_41` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_41 : InClass rho_41 cls_41 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_41, rho_41] <;> norm_num⟩

/-- **gamma at class 41, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_41`
consumed through `join50`. -/
theorem chjoin_41 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_41) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_41 (17/13 : ℝ) (23/15 : ℝ) castAB_41 hIn.1 Fresh.ChamberDatasheet.chds_41 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 41's own tuple (atom `chds_41` + proved join `inclass_41` +
`chjoin_41`). -/
theorem dead_41 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_41 s :=
  chjoin_41 rho_41 s hs h50 inclass_41

/-- jj#42 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/73 | D2 | 3080 cases | NO-ALIVE-ON-GRID -/
def cls_42 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 42 (exact rationals, the probe's own
case dump). -/
def rho_42 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 73/5]

theorem castAB_42 : ((cls_42.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_42.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_42]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_42`/`cls_42` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_42 : InClass rho_42 cls_42 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_42, rho_42] <;> norm_num⟩

/-- **gamma at class 42, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_42`
consumed through `join50`. -/
theorem chjoin_42 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_42) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_42 (85/63 : ℝ) (115/73 : ℝ) castAB_42 hIn.1 Fresh.ChamberDatasheet.chds_42 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 42's own tuple (atom `chds_42` + proved join `inclass_42` +
`chjoin_42`). -/
theorem dead_42 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_42 s :=
  chjoin_42 rho_42 s hs h50 inclass_42

/-- jj#43 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3060 cases | NO-ALIVE-ON-GRID -/
def cls_43 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 43 (exact rationals, the probe's own
case dump). -/
def rho_43 : Fin 5 → ℚ := ![1, 9, 9, 63/5, 15]

theorem castAB_43 : ((cls_43.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_43.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_43]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_43`/`cls_43` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_43 : InClass rho_43 cls_43 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_43, rho_43] <;> norm_num⟩

/-- **gamma at class 43, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_43`
consumed through `join50`. -/
theorem chjoin_43 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_43) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_43 (85/63 : ℝ) (23/15 : ℝ) castAB_43 hIn.1 Fresh.ChamberDatasheet.chds_43 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 43's own tuple (atom `chds_43` + proved join `inclass_43` +
`chjoin_43`). -/
theorem dead_43 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_43 s :=
  chjoin_43 rho_43 s hs h50 inclass_43

/-- jj#44 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 3060 cases | NO-ALIVE-ON-GRID -/
def cls_44 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 44 (exact rationals, the probe's own
case dump). -/
def rho_44 : Fin 5 → ℚ := ![1, 9, 9, 63/5, 15]

theorem castAB_44 : ((cls_44.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_44.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_44]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_44`/`cls_44` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_44 : InClass rho_44 cls_44 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_44, rho_44] <;> norm_num⟩

/-- **gamma at class 44, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_44`
consumed through `join50`. -/
theorem chjoin_44 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_44) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_44 (85/63 : ℝ) (23/15 : ℝ) castAB_44 hIn.1 Fresh.ChamberDatasheet.chds_44 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 44's own tuple (atom `chds_44` + proved join `inclass_44` +
`chjoin_44`). -/
theorem dead_44 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_44 s :=
  chjoin_44 rho_44 s hs h50 inclass_44

/-- jj#45 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_45 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 45 (exact rationals, the probe's own
case dump). -/
def rho_45 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 76/5]

theorem castAB_45 : ((cls_45.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_45.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_45]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_45`/`cls_45` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_45 : InClass rho_45 cls_45 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_45, rho_45] <;> norm_num⟩

/-- **gamma at class 45, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_45`
consumed through `join50`. -/
theorem chjoin_45 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_45) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_45 (85/76 : ℝ) (75/56 : ℝ) castAB_45 hIn.1 Fresh.ChamberDatasheet.chds_45 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 45's own tuple (atom `chds_45` + proved join `inclass_45` +
`chjoin_45`). -/
theorem dead_45 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_45 s :=
  chjoin_45 rho_45 s hs h50 inclass_45

/-- jj#46 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_46 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 46 (exact rationals, the probe's own
case dump). -/
def rho_46 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 77/5]

theorem castAB_46 : ((cls_46.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_46.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_46]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_46`/`cls_46` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_46 : InClass rho_46 cls_46 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_46, rho_46] <;> norm_num⟩

/-- **gamma at class 46, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_46`
consumed through `join50`. -/
theorem chjoin_46 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_46) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_46 (85/77 : ℝ) (75/56 : ℝ) castAB_46 hIn.1 Fresh.ChamberDatasheet.chds_46 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 46's own tuple (atom `chds_46` + proved join `inclass_46` +
`chjoin_46`). -/
theorem dead_46 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_46 s :=
  chjoin_46 rho_46 s hs h50 inclass_46

/-- jj#47 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_47 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 47 (exact rationals, the probe's own
case dump). -/
def rho_47 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 78/5]

theorem castAB_47 : ((cls_47.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_47.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_47]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_47`/`cls_47` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_47 : InClass rho_47 cls_47 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_47, rho_47] <;> norm_num⟩

/-- **gamma at class 47, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_47`
consumed through `join50`. -/
theorem chjoin_47 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_47) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_47 (85/78 : ℝ) (75/56 : ℝ) castAB_47 hIn.1 Fresh.ChamberDatasheet.chds_47 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 47's own tuple (atom `chds_47` + proved join `inclass_47` +
`chjoin_47`). -/
theorem dead_47 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_47 s :=
  chjoin_47 rho_47 s hs h50 inclass_47

/-- jj#48 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_48 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 48 (exact rationals, the probe's own
case dump). -/
def rho_48 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 79/5]

theorem castAB_48 : ((cls_48.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_48.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_48]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_48`/`cls_48` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_48 : InClass rho_48 cls_48 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_48, rho_48] <;> norm_num⟩

/-- **gamma at class 48, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_48`
consumed through `join50`. -/
theorem chjoin_48 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_48) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_48 (85/79 : ℝ) (75/56 : ℝ) castAB_48 hIn.1 Fresh.ChamberDatasheet.chds_48 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 48's own tuple (atom `chds_48` + proved join `inclass_48` +
`chjoin_48`). -/
theorem dead_48 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_48 s :=
  chjoin_48 rho_48 s hs h50 inclass_48

/-- jj#49 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_49 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 49 (exact rationals, the probe's own
case dump). -/
def rho_49 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 16]

theorem castAB_49 : ((cls_49.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_49.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_49]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_49`/`cls_49` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_49 : InClass rho_49 cls_49 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_49, rho_49] <;> norm_num⟩

/-- **gamma at class 49, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_49`
consumed through `join50`. -/
theorem chjoin_49 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_49) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_49 (17/16 : ℝ) (75/56 : ℝ) castAB_49 hIn.1 Fresh.ChamberDatasheet.chds_49 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 49's own tuple (atom `chds_49` + proved join `inclass_49` +
`chjoin_49`). -/
theorem dead_49 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_49 s :=
  chjoin_49 rho_49 s hs h50 inclass_49

/-- jj#50 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/56 | D2 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_50 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 50 (exact rationals, the probe's own
case dump). -/
def rho_50 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 81/5]

theorem castAB_50 : ((cls_50.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_50.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_50]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_50`/`cls_50` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_50 : InClass rho_50 cls_50 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_50, rho_50] <;> norm_num⟩

/-- **gamma at class 50, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_50`
consumed through `join50`. -/
theorem chjoin_50 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_50) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_50 (85/81 : ℝ) (75/56 : ℝ) castAB_50 hIn.1 Fresh.ChamberDatasheet.chds_50 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 50's own tuple (atom `chds_50` + proved join `inclass_50` +
`chjoin_50`). -/
theorem dead_50 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_50 s :=
  chjoin_50 rho_50 s hs h50 inclass_50

/-- jj#51 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/56 | D1 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_51 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 51 (exact rationals, the probe's own
case dump). -/
def rho_51 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 82/5]

theorem castAB_51 : ((cls_51.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_51.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_51]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_51`/`cls_51` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_51 : InClass rho_51 cls_51 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_51, rho_51] <;> norm_num⟩

/-- **gamma at class 51, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_51`
consumed through `join50`. -/
theorem chjoin_51 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_51) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_51 (85/82 : ℝ) (75/56 : ℝ) castAB_51 hIn.1 Fresh.ChamberDatasheet.chds_51 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 51's own tuple (atom `chds_51` + proved join `inclass_51` +
`chjoin_51`). -/
theorem dead_51 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_51 s :=
  chjoin_51 rho_51 s hs h50 inclass_51

/-- jj#52 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/56 | D1 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_52 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 52 (exact rationals, the probe's own
case dump). -/
def rho_52 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 83/5]

theorem castAB_52 : ((cls_52.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_52.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_52]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_52`/`cls_52` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_52 : InClass rho_52 cls_52 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_52, rho_52] <;> norm_num⟩

/-- **gamma at class 52, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_52`
consumed through `join50`. -/
theorem chjoin_52 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_52) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_52 (85/83 : ℝ) (75/56 : ℝ) castAB_52 hIn.1 Fresh.ChamberDatasheet.chds_52 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 52's own tuple (atom `chds_52` + proved join `inclass_52` +
`chjoin_52`). -/
theorem dead_52 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_52 s :=
  chjoin_52 rho_52 s hs h50 inclass_52

/-- jj#53 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/56 | D1 | 3036 cases | NO-ALIVE-ON-GRID -/
def cls_53 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 53 (exact rationals, the probe's own
case dump). -/
def rho_53 : Fin 5 → ℚ := ![1, 1, 9, 56/5, 84/5]

theorem castAB_53 : ((cls_53.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_53.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_53]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_53`/`cls_53` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_53 : InClass rho_53 cls_53 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_53, rho_53] <;> norm_num⟩

/-- **gamma at class 53, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_53`
consumed through `join50`. -/
theorem chjoin_53 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_53) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_53 (85/84 : ℝ) (75/56 : ℝ) castAB_53 hIn.1 Fresh.ChamberDatasheet.chds_53 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 53's own tuple (atom `chds_53` + proved join `inclass_53` +
`chjoin_53`). -/
theorem dead_53 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_53 s :=
  chjoin_53 rho_53 s hs h50 inclass_53

/-- jj#54 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_54 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 54 (exact rationals, the probe's own
case dump). -/
def rho_54 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 83/5]

theorem castAB_54 : ((cls_54.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_54.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_54]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_54`/`cls_54` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_54 : InClass rho_54 cls_54 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_54, rho_54] <;> norm_num⟩

/-- **gamma at class 54, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_54`
consumed through `join50`. -/
theorem chjoin_54 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_54) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_54 (85/73 : ℝ) (115/83 : ℝ) castAB_54 hIn.1 Fresh.ChamberDatasheet.chds_54 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 54's own tuple (atom `chds_54` + proved join `inclass_54` +
`chjoin_54`). -/
theorem dead_54 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_54 s :=
  chjoin_54 rho_54 s hs h50 inclass_54

/-- jj#55 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_55 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 55 (exact rationals, the probe's own
case dump). -/
def rho_55 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 84/5]

theorem castAB_55 : ((cls_55.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_55.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_55]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_55`/`cls_55` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_55 : InClass rho_55 cls_55 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_55, rho_55] <;> norm_num⟩

/-- **gamma at class 55, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_55`
consumed through `join50`. -/
theorem chjoin_55 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_55) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_55 (85/73 : ℝ) (115/84 : ℝ) castAB_55 hIn.1 Fresh.ChamberDatasheet.chds_55 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 55's own tuple (atom `chds_55` + proved join `inclass_55` +
`chjoin_55`). -/
theorem dead_55 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_55 s :=
  chjoin_55 rho_55 s hs h50 inclass_55

/-- jj#56 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_56 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 56 (exact rationals, the probe's own
case dump). -/
def rho_56 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 17]

theorem castAB_56 : ((cls_56.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_56.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_56]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_56`/`cls_56` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_56 : InClass rho_56 cls_56 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_56, rho_56] <;> norm_num⟩

/-- **gamma at class 56, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_56`
consumed through `join50`. -/
theorem chjoin_56 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_56) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_56 (85/74 : ℝ) (23/17 : ℝ) castAB_56 hIn.1 Fresh.ChamberDatasheet.chds_56 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 56's own tuple (atom `chds_56` + proved join `inclass_56` +
`chjoin_56`). -/
theorem dead_56 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_56 s :=
  chjoin_56 rho_56 s hs h50 inclass_56

/-- jj#57 | PPG1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_57 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 57 (exact rationals, the probe's own
case dump). -/
def rho_57 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 17]

theorem castAB_57 : ((cls_57.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_57.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_57]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_57`/`cls_57` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_57 : InClass rho_57 cls_57 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_57, rho_57] <;> norm_num⟩

/-- **gamma at class 57, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_57`
consumed through `join50`. -/
theorem chjoin_57 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_57) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_57 (85/74 : ℝ) (23/17 : ℝ) castAB_57 hIn.1 Fresh.ChamberDatasheet.chds_57 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 57's own tuple (atom `chds_57` + proved join `inclass_57` +
`chjoin_57`). -/
theorem dead_57 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_57 s :=
  chjoin_57 rho_57 s hs h50 inclass_57

/-- jj#58 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_58 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 58 (exact rationals, the probe's own
case dump). -/
def rho_58 : Fin 5 → ℚ := ![1, 9, 74/5, 15, 17]

theorem castAB_58 : ((cls_58.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_58.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_58]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_58`/`cls_58` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_58 : InClass rho_58 cls_58 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_58, rho_58] <;> norm_num⟩

/-- **gamma at class 58, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_58`
consumed through `join50`. -/
theorem chjoin_58 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_58) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_58 (85/74 : ℝ) (23/17 : ℝ) castAB_58 hIn.1 Fresh.ChamberDatasheet.chds_58 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 58's own tuple (atom `chds_58` + proved join `inclass_58` +
`chjoin_58`). -/
theorem dead_58 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_58 s :=
  chjoin_58 rho_58 s hs h50 inclass_58

/-- jj#59 | PG1G1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 3003 cases | NO-ALIVE-ON-GRID -/
def cls_59 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 15, 17], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 59 (exact rationals, the probe's own
case dump). -/
def rho_59 : Fin 5 → ℚ := ![1, 9, 74/5, 15, 17]

theorem castAB_59 : ((cls_59.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_59.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_59]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_59`/`cls_59` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_59 : InClass rho_59 cls_59 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_59, rho_59] <;> norm_num⟩

/-- **gamma at class 59, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_59`
consumed through `join50`. -/
theorem chjoin_59 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_59) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_59 (85/74 : ℝ) (23/17 : ℝ) castAB_59 hIn.1 Fresh.ChamberDatasheet.chds_59 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 59's own tuple (atom `chds_59` + proved join `inclass_59` +
`chjoin_59`). -/
theorem dead_59 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_59 s :=
  chjoin_59 rho_59 s hs h50 inclass_59

/-- jj#60 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/73 | D2 | 2940 cases | NO-ALIVE-ON-GRID -/
def cls_60 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 60 (exact rationals, the probe's own
case dump). -/
def rho_60 : Fin 5 → ℚ := ![1, 1, 9, 63/5, 73/5]

theorem castAB_60 : ((cls_60.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_60.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_60]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_60`/`cls_60` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_60 : InClass rho_60 cls_60 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_60, rho_60] <;> norm_num⟩

/-- **gamma at class 60, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_60`
consumed through `join50`. -/
theorem chjoin_60 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_60) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_60 (85/63 : ℝ) (115/73 : ℝ) castAB_60 hIn.1 Fresh.ChamberDatasheet.chds_60 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 60's own tuple (atom `chds_60` + proved join `inclass_60` +
`chjoin_60`). -/
theorem dead_60 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_60 s :=
  chjoin_60 rho_60 s hs h50 inclass_60

/-- jj#61 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 2940 cases | NO-ALIVE-ON-GRID -/
def cls_61 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 61 (exact rationals, the probe's own
case dump). -/
def rho_61 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 84/5]

theorem castAB_61 : ((cls_61.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_61.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_61]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_61`/`cls_61` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_61 : InClass rho_61 cls_61 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_61, rho_61] <;> norm_num⟩

/-- **gamma at class 61, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_61`
consumed through `join50`. -/
theorem chjoin_61 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_61) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_61 (85/72 : ℝ) (115/84 : ℝ) castAB_61 hIn.1 Fresh.ChamberDatasheet.chds_61 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 61's own tuple (atom `chds_61` + proved join `inclass_61` +
`chjoin_61`). -/
theorem dead_61 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_61 s :=
  chjoin_61 rho_61 s hs h50 inclass_61

/-- jj#62 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/74 | D2 | 2926 cases | NO-ALIVE-ON-GRID -/
def cls_62 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 62 (exact rationals, the probe's own
case dump). -/
def rho_62 : Fin 5 → ℚ := ![1, 7, 9, 13, 74/5]

theorem castAB_62 : ((cls_62.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_62.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_62]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_62`/`cls_62` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_62 : InClass rho_62 cls_62 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_62, rho_62] <;> norm_num⟩

/-- **gamma at class 62, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_62`
consumed through `join50`. -/
theorem chjoin_62 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_62) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_62 (17/13 : ℝ) (115/74 : ℝ) castAB_62 hIn.1 Fresh.ChamberDatasheet.chds_62 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 62's own tuple (atom `chds_62` + proved join `inclass_62` +
`chjoin_62`). -/
theorem dead_62 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_62 s :=
  chjoin_62 rho_62 s hs h50 inclass_62

/-- jj#63 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2926 cases | NO-ALIVE-ON-GRID -/
def cls_63 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 63 (exact rationals, the probe's own
case dump). -/
def rho_63 : Fin 5 → ℚ := ![1, 7, 9, 66/5, 15]

theorem castAB_63 : ((cls_63.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_63.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_63]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_63`/`cls_63` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_63 : InClass rho_63 cls_63 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_63, rho_63] <;> norm_num⟩

/-- **gamma at class 63, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_63`
consumed through `join50`. -/
theorem chjoin_63 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_63) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_63 (85/66 : ℝ) (23/15 : ℝ) castAB_63 hIn.1 Fresh.ChamberDatasheet.chds_63 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 63's own tuple (atom `chds_63` + proved join `inclass_63` +
`chjoin_63`). -/
theorem dead_63 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_63 s :=
  chjoin_63 rho_63 s hs h50 inclass_63

/-- jj#64 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2926 cases | NO-ALIVE-ON-GRID -/
def cls_64 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 64 (exact rationals, the probe's own
case dump). -/
def rho_64 : Fin 5 → ℚ := ![1, 7, 9, 66/5, 15]

theorem castAB_64 : ((cls_64.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_64.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_64]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_64`/`cls_64` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_64 : InClass rho_64 cls_64 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_64, rho_64] <;> norm_num⟩

/-- **gamma at class 64, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_64`
consumed through `join50`. -/
theorem chjoin_64 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_64) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_64 (85/66 : ℝ) (23/15 : ℝ) castAB_64 hIn.1 Fresh.ChamberDatasheet.chds_64 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 64's own tuple (atom `chds_64` + proved join `inclass_64` +
`chjoin_64`). -/
theorem dead_64 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_64 s :=
  chjoin_64 rho_64 s hs h50 inclass_64

/-- jj#65 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/58 | D2 | 2898 cases | NO-ALIVE-ON-GRID -/
def cls_65 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 65 (exact rationals, the probe's own
case dump). -/
def rho_65 : Fin 5 → ℚ := ![1, 9, 58/5, 77/5, 77/5]

theorem castAB_65 : ((cls_65.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_65.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_65]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_65`/`cls_65` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_65 : InClass rho_65 cls_65 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_65, rho_65] <;> norm_num⟩

/-- **gamma at class 65, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_65`
consumed through `join50`. -/
theorem chjoin_65 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_65) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_65 (85/77 : ℝ) (75/58 : ℝ) castAB_65 hIn.1 Fresh.ChamberDatasheet.chds_65 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 65's own tuple (atom `chds_65` + proved join `inclass_65` +
`chjoin_65`). -/
theorem dead_65 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_65 s :=
  chjoin_65 rho_65 s hs h50 inclass_65

/-- jj#66 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/73 | D2 | 2860 cases | NO-ALIVE-ON-GRID -/
def cls_66 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 66 (exact rationals, the probe's own
case dump). -/
def rho_66 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 73/5]

theorem castAB_66 : ((cls_66.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_66.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_66]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_66`/`cls_66` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_66 : InClass rho_66 cls_66 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_66, rho_66] <;> norm_num⟩

/-- **gamma at class 66, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_66`
consumed through `join50`. -/
theorem chjoin_66 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_66) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_66 (85/64 : ℝ) (115/73 : ℝ) castAB_66 hIn.1 Fresh.ChamberDatasheet.chds_66 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 66's own tuple (atom `chds_66` + proved join `inclass_66` +
`chjoin_66`). -/
theorem dead_66 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_66 s :=
  chjoin_66 rho_66 s hs h50 inclass_66

/-- jj#67 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=25/19 | D2 | 2860 cases | NO-ALIVE-ON-GRID -/
def cls_67 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 67 (exact rationals, the probe's own
case dump). -/
def rho_67 : Fin 5 → ℚ := ![1, 9, 57/5, 76/5, 76/5]

theorem castAB_67 : ((cls_67.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_67.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_67]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_67`/`cls_67` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_67 : InClass rho_67 cls_67 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_67, rho_67] <;> norm_num⟩

/-- **gamma at class 67, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_67`
consumed through `join50`. -/
theorem chjoin_67 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_67) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_67 (85/76 : ℝ) (25/19 : ℝ) castAB_67 hIn.1 Fresh.ChamberDatasheet.chds_67 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 67's own tuple (atom `chds_67` + proved join `inclass_67` +
`chjoin_67`). -/
theorem dead_67 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_67 s :=
  chjoin_67 rho_67 s hs h50 inclass_67

/-- jj#68 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=25/17 | D2 | 2850 cases | NO-ALIVE-ON-GRID -/
def cls_68 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 68 (exact rationals, the probe's own
case dump). -/
def rho_68 : Fin 5 → ℚ := ![1, 1, 36/5, 9, 51/5]

theorem castAB_68 : ((cls_68.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_68.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_68]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_68`/`cls_68` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_68 : InClass rho_68 cls_68 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_68, rho_68] <;> norm_num⟩

/-- **gamma at class 68, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_68`
consumed through `join50`. -/
theorem chjoin_68 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_68) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_68 (5/4 : ℝ) (25/17 : ℝ) castAB_68 hIn.1 Fresh.ChamberDatasheet.chds_68 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 68's own tuple (atom `chds_68` + proved join `inclass_68` +
`chjoin_68`). -/
theorem dead_68 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_68 s :=
  chjoin_68 rho_68 s hs h50 inclass_68

/-- jj#69 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2850 cases | NO-ALIVE-ON-GRID -/
def cls_69 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 69 (exact rationals, the probe's own
case dump). -/
def rho_69 : Fin 5 → ℚ := ![1, 1, 9, 13, 15]

theorem castAB_69 : ((cls_69.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_69.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_69]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_69`/`cls_69` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_69 : InClass rho_69 cls_69 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_69, rho_69] <;> norm_num⟩

/-- **gamma at class 69, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_69`
consumed through `join50`. -/
theorem chjoin_69 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_69) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_69 (17/13 : ℝ) (23/15 : ℝ) castAB_69 hIn.1 Fresh.ChamberDatasheet.chds_69 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 69's own tuple (atom `chds_69` + proved join `inclass_69` +
`chjoin_69`). -/
theorem dead_69 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_69 s :=
  chjoin_69 rho_69 s hs h50 inclass_69

/-- jj#70 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2850 cases | NO-ALIVE-ON-GRID -/
def cls_70 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 70 (exact rationals, the probe's own
case dump). -/
def rho_70 : Fin 5 → ℚ := ![1, 1, 9, 13, 15]

theorem castAB_70 : ((cls_70.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_70.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_70]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_70`/`cls_70` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_70 : InClass rho_70 cls_70 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_70, rho_70] <;> norm_num⟩

/-- **gamma at class 70, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_70`
consumed through `join50`. -/
theorem chjoin_70 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_70) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_70 (17/13 : ℝ) (23/15 : ℝ) castAB_70 hIn.1 Fresh.ChamberDatasheet.chds_70 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 70's own tuple (atom `chds_70` + proved join `inclass_70` +
`chjoin_70`). -/
theorem dead_70 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_70 s :=
  chjoin_70 rho_70 s hs h50 inclass_70

/-- jj#71 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=25/17 | D2 | 2850 cases | NO-ALIVE-ON-GRID -/
def cls_71 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 71 (exact rationals, the probe's own
case dump). -/
def rho_71 : Fin 5 → ℚ := ![1, 36/5, 36/5, 9, 51/5]

theorem castAB_71 : ((cls_71.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_71.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_71]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_71`/`cls_71` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_71 : InClass rho_71 cls_71 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_71, rho_71] <;> norm_num⟩

/-- **gamma at class 71, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_71`
consumed through `join50`. -/
theorem chjoin_71 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_71) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_71 (5/4 : ℝ) (25/17 : ℝ) castAB_71 hIn.1 Fresh.ChamberDatasheet.chds_71 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 71's own tuple (atom `chds_71` + proved join `inclass_71` +
`chjoin_71`). -/
theorem dead_71 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_71 s :=
  chjoin_71 rho_71 s hs h50 inclass_71

/-- jj#72 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/83 | D2 | 2772 cases | NO-ALIVE-ON-GRID -/
def cls_72 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 72 (exact rationals, the probe's own
case dump). -/
def rho_72 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 83/5]

theorem castAB_72 : ((cls_72.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_72.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_72]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_72`/`cls_72` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_72 : InClass rho_72 cls_72 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_72, rho_72] <;> norm_num⟩

/-- **gamma at class 72, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_72`
consumed through `join50`. -/
theorem chjoin_72 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_72) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_72 (85/74 : ℝ) (115/83 : ℝ) castAB_72 hIn.1 Fresh.ChamberDatasheet.chds_72 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 72's own tuple (atom `chds_72` + proved join `inclass_72` +
`chjoin_72`). -/
theorem dead_72 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_72 s :=
  chjoin_72 rho_72 s hs h50 inclass_72

/-- jj#73 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/84 | D2 | 2772 cases | NO-ALIVE-ON-GRID -/
def cls_73 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 73 (exact rationals, the probe's own
case dump). -/
def rho_73 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 84/5]

theorem castAB_73 : ((cls_73.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_73.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_73]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_73`/`cls_73` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_73 : InClass rho_73 cls_73 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_73, rho_73] <;> norm_num⟩

/-- **gamma at class 73, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_73`
consumed through `join50`. -/
theorem chjoin_73 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_73) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_73 (85/74 : ℝ) (115/84 : ℝ) castAB_73 hIn.1 Fresh.ChamberDatasheet.chds_73 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 73's own tuple (atom `chds_73` + proved join `inclass_73` +
`chjoin_73`). -/
theorem dead_73 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_73 s :=
  chjoin_73 rho_73 s hs h50 inclass_73

/-- jj#74 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/58 | D2 | 2760 cases | NO-ALIVE-ON-GRID -/
def cls_74 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 74 (exact rationals, the probe's own
case dump). -/
def rho_74 : Fin 5 → ℚ := ![1, 1, 58/5, 76/5, 76/5]

theorem castAB_74 : ((cls_74.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_74.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_74]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_74`/`cls_74` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_74 : InClass rho_74 cls_74 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_74, rho_74] <;> norm_num⟩

/-- **gamma at class 74, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_74`
consumed through `join50`. -/
theorem chjoin_74 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_74) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_74 (85/76 : ℝ) (75/58 : ℝ) castAB_74 hIn.1 Fresh.ChamberDatasheet.chds_74 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 74's own tuple (atom `chds_74` + proved join `inclass_74` +
`chjoin_74`). -/
theorem dead_74 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_74 s :=
  chjoin_74 rho_74 s hs h50 inclass_74

/-- jj#75 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/73 | D2 | 2730 cases | NO-ALIVE-ON-GRID -/
def cls_75 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 75 (exact rationals, the probe's own
case dump). -/
def rho_75 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 73/5]

theorem castAB_75 : ((cls_75.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_75.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_75]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_75`/`cls_75` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_75 : InClass rho_75 cls_75 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_75, rho_75] <;> norm_num⟩

/-- **gamma at class 75, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_75`
consumed through `join50`. -/
theorem chjoin_75 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_75) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_75 (85/64 : ℝ) (115/73 : ℝ) castAB_75 hIn.1 Fresh.ChamberDatasheet.chds_75 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 75's own tuple (atom `chds_75` + proved join `inclass_75` +
`chjoin_75`). -/
theorem dead_75 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_75 s :=
  chjoin_75 rho_75 s hs h50 inclass_75

/-- jj#76 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/82 | D2 | 2730 cases | NO-ALIVE-ON-GRID -/
def cls_76 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 76 (exact rationals, the probe's own
case dump). -/
def rho_76 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 82/5]

theorem castAB_76 : ((cls_76.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_76.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_76]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_76`/`cls_76` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_76 : InClass rho_76 cls_76 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_76, rho_76] <;> norm_num⟩

/-- **gamma at class 76, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_76`
consumed through `join50`. -/
theorem chjoin_76 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_76) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_76 (85/72 : ℝ) (115/82 : ℝ) castAB_76 hIn.1 Fresh.ChamberDatasheet.chds_76 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 76's own tuple (atom `chds_76` + proved join `inclass_76` +
`chjoin_76`). -/
theorem dead_76 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_76 s :=
  chjoin_76 rho_76 s hs h50 inclass_76

/-- jj#77 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 2730 cases | NO-ALIVE-ON-GRID -/
def cls_77 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 77 (exact rationals, the probe's own
case dump). -/
def rho_77 : Fin 5 → ℚ := ![1, 9, 73/5, 15, 84/5]

theorem castAB_77 : ((cls_77.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_77.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_77]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_77`/`cls_77` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_77 : InClass rho_77 cls_77 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_77, rho_77] <;> norm_num⟩

/-- **gamma at class 77, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_77`
consumed through `join50`. -/
theorem chjoin_77 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_77) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_77 (85/73 : ℝ) (115/84 : ℝ) castAB_77 hIn.1 Fresh.ChamberDatasheet.chds_77 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 77's own tuple (atom `chds_77` + proved join `inclass_77` +
`chjoin_77`). -/
theorem dead_77 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_77 s :=
  chjoin_77 rho_77 s hs h50 inclass_77

/-- jj#78 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 2720 cases | NO-ALIVE-ON-GRID -/
def cls_78 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 78 (exact rationals, the probe's own
case dump). -/
def rho_78 : Fin 5 → ℚ := ![1, 9, 9, 64/5, 15]

theorem castAB_78 : ((cls_78.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_78.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_78]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_78`/`cls_78` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_78 : InClass rho_78 cls_78 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_78, rho_78] <;> norm_num⟩

/-- **gamma at class 78, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_78`
consumed through `join50`. -/
theorem chjoin_78 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_78) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_78 (85/64 : ℝ) (23/15 : ℝ) castAB_78 hIn.1 Fresh.ChamberDatasheet.chds_78 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 78's own tuple (atom `chds_78` + proved join `inclass_78` +
`chjoin_78`). -/
theorem dead_78 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_78 s :=
  chjoin_78 rho_78 s hs h50 inclass_78

/-- jj#79 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 2720 cases | NO-ALIVE-ON-GRID -/
def cls_79 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 79 (exact rationals, the probe's own
case dump). -/
def rho_79 : Fin 5 → ℚ := ![1, 9, 9, 64/5, 15]

theorem castAB_79 : ((cls_79.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_79.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_79]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_79`/`cls_79` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_79 : InClass rho_79 cls_79 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_79, rho_79] <;> norm_num⟩

/-- **gamma at class 79, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_79`
consumed through `join50`. -/
theorem chjoin_79 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_79) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_79 (85/64 : ℝ) (23/15 : ℝ) castAB_79 hIn.1 Fresh.ChamberDatasheet.chds_79 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 79's own tuple (atom `chds_79` + proved join `inclass_79` +
`chjoin_79`). -/
theorem dead_79 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_79 s :=
  chjoin_79 rho_79 s hs h50 inclass_79

/-- jj#80 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/74 | D2 | 2717 cases | NO-ALIVE-ON-GRID -/
def cls_80 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 80 (exact rationals, the probe's own
case dump). -/
def rho_80 : Fin 5 → ℚ := ![1, 7, 9, 66/5, 74/5]

theorem castAB_80 : ((cls_80.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_80.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_80]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_80`/`cls_80` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_80 : InClass rho_80 cls_80 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_80, rho_80] <;> norm_num⟩

/-- **gamma at class 80, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_80`
consumed through `join50`. -/
theorem chjoin_80 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_80) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_80 (85/66 : ℝ) (115/74 : ℝ) castAB_80 hIn.1 Fresh.ChamberDatasheet.chds_80 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 80's own tuple (atom `chds_80` + proved join `inclass_80` +
`chjoin_80`). -/
theorem dead_80 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_80 s :=
  chjoin_80 rho_80 s hs h50 inclass_80

/-- jj#81 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=3/2 | D2 | 2660 cases | NO-ALIVE-ON-GRID -/
def cls_81 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 81 (exact rationals, the probe's own
case dump). -/
def rho_81 : Fin 5 → ℚ := ![1, 1, 36/5, 9, 10]

theorem castAB_81 : ((cls_81.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_81.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_81]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_81`/`cls_81` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_81 : InClass rho_81 cls_81 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_81, rho_81] <;> norm_num⟩

/-- **gamma at class 81, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_81`
consumed through `join50`. -/
theorem chjoin_81 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_81) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_81 (5/4 : ℝ) (3/2 : ℝ) castAB_81 hIn.1 Fresh.ChamberDatasheet.chds_81 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 81's own tuple (atom `chds_81` + proved join `inclass_81` +
`chjoin_81`). -/
theorem dead_81 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_81 s :=
  chjoin_81 rho_81 s hs h50 inclass_81

/-- jj#82 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/74 | D2 | 2660 cases | NO-ALIVE-ON-GRID -/
def cls_82 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 82 (exact rationals, the probe's own
case dump). -/
def rho_82 : Fin 5 → ℚ := ![1, 1, 9, 13, 74/5]

theorem castAB_82 : ((cls_82.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_82.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_82]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_82`/`cls_82` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_82 : InClass rho_82 cls_82 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_82, rho_82] <;> norm_num⟩

/-- **gamma at class 82, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_82`
consumed through `join50`. -/
theorem chjoin_82 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_82) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_82 (17/13 : ℝ) (115/74 : ℝ) castAB_82 hIn.1 Fresh.ChamberDatasheet.chds_82 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 82's own tuple (atom `chds_82` + proved join `inclass_82` +
`chjoin_82`). -/
theorem dead_82 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_82 s :=
  chjoin_82 rho_82 s hs h50 inclass_82

/-- jj#83 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2660 cases | NO-ALIVE-ON-GRID -/
def cls_83 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 83 (exact rationals, the probe's own
case dump). -/
def rho_83 : Fin 5 → ℚ := ![1, 1, 9, 66/5, 15]

theorem castAB_83 : ((cls_83.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_83.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_83]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_83`/`cls_83` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_83 : InClass rho_83 cls_83 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_83, rho_83] <;> norm_num⟩

/-- **gamma at class 83, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_83`
consumed through `join50`. -/
theorem chjoin_83 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_83) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_83 (85/66 : ℝ) (23/15 : ℝ) castAB_83 hIn.1 Fresh.ChamberDatasheet.chds_83 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 83's own tuple (atom `chds_83` + proved join `inclass_83` +
`chjoin_83`). -/
theorem dead_83 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_83 s :=
  chjoin_83 rho_83 s hs h50 inclass_83

/-- jj#84 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2660 cases | NO-ALIVE-ON-GRID -/
def cls_84 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 84 (exact rationals, the probe's own
case dump). -/
def rho_84 : Fin 5 → ℚ := ![1, 1, 9, 66/5, 15]

theorem castAB_84 : ((cls_84.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_84.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_84]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_84`/`cls_84` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_84 : InClass rho_84 cls_84 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_84, rho_84] <;> norm_num⟩

/-- **gamma at class 84, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_84`
consumed through `join50`. -/
theorem chjoin_84 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_84) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_84 (85/66 : ℝ) (23/15 : ℝ) castAB_84 hIn.1 Fresh.ChamberDatasheet.chds_84 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 84's own tuple (atom `chds_84` + proved join `inclass_84` +
`chjoin_84`). -/
theorem dead_84 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_84 s :=
  chjoin_84 rho_84 s hs h50 inclass_84

/-- jj#85 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=3/2 | D2 | 2660 cases | NO-ALIVE-ON-GRID -/
def cls_85 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 85 (exact rationals, the probe's own
case dump). -/
def rho_85 : Fin 5 → ℚ := ![1, 36/5, 36/5, 9, 10]

theorem castAB_85 : ((cls_85.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_85.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_85]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_85`/`cls_85` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_85 : InClass rho_85 cls_85 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_85, rho_85] <;> norm_num⟩

/-- **gamma at class 85, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_85`
consumed through `join50`. -/
theorem chjoin_85 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_85) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_85 (5/4 : ℝ) (3/2 : ℝ) castAB_85 hIn.1 Fresh.ChamberDatasheet.chds_85 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 85's own tuple (atom `chds_85` + proved join `inclass_85` +
`chjoin_85`). -/
theorem dead_85 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_85 s :=
  chjoin_85 rho_85 s hs h50 inclass_85

/-- jj#86 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 2646 cases | NO-ALIVE-ON-GRID -/
def cls_86 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 86 (exact rationals, the probe's own
case dump). -/
def rho_86 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 83/5]

theorem castAB_86 : ((cls_86.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_86.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_86]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_86`/`cls_86` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_86 : InClass rho_86 cls_86 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_86, rho_86] <;> norm_num⟩

/-- **gamma at class 86, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_86`
consumed through `join50`. -/
theorem chjoin_86 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_86) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_86 (85/72 : ℝ) (115/83 : ℝ) castAB_86 hIn.1 Fresh.ChamberDatasheet.chds_86 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 86's own tuple (atom `chds_86` + proved join `inclass_86` +
`chjoin_86`). -/
theorem dead_86 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_86 s :=
  chjoin_86 rho_86 s hs h50 inclass_86

/-- jj#87 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/56 | D2 | 2640 cases | NO-ALIVE-ON-GRID -/
def cls_87 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 87 (exact rationals, the probe's own
case dump). -/
def rho_87 : Fin 5 → ℚ := ![1, 9, 56/5, 76/5, 76/5]

theorem castAB_87 : ((cls_87.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_87.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_87]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_87`/`cls_87` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_87 : InClass rho_87 cls_87 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_87, rho_87] <;> norm_num⟩

/-- **gamma at class 87, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_87`
consumed through `join50`. -/
theorem chjoin_87 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_87) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_87 (85/76 : ℝ) (75/56 : ℝ) castAB_87 hIn.1 Fresh.ChamberDatasheet.chds_87 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 87's own tuple (atom `chds_87` + proved join `inclass_87` +
`chjoin_87`). -/
theorem dead_87 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_87 s :=
  chjoin_87 rho_87 s hs h50 inclass_87

/-- jj#88 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/58 | D2 | 2576 cases | NO-ALIVE-ON-GRID -/
def cls_88 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 88 (exact rationals, the probe's own
case dump). -/
def rho_88 : Fin 5 → ℚ := ![1, 9, 58/5, 78/5, 78/5]

theorem castAB_88 : ((cls_88.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_88.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_88]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_88`/`cls_88` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_88 : InClass rho_88 cls_88 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_88, rho_88] <;> norm_num⟩

/-- **gamma at class 88, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_88`
consumed through `join50`. -/
theorem chjoin_88 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_88) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_88 (85/78 : ℝ) (75/58 : ℝ) castAB_88 hIn.1 Fresh.ChamberDatasheet.chds_88 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 88's own tuple (atom `chds_88` + proved join `inclass_88` +
`chjoin_88`). -/
theorem dead_88 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_88 s :=
  chjoin_88 rho_88 s hs h50 inclass_88

/-- jj#89 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=25/19 | D2 | 2574 cases | NO-ALIVE-ON-GRID -/
def cls_89 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 89 (exact rationals, the probe's own
case dump). -/
def rho_89 : Fin 5 → ℚ := ![1, 9, 57/5, 77/5, 77/5]

theorem castAB_89 : ((cls_89.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_89.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_89]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_89`/`cls_89` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_89 : InClass rho_89 cls_89 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_89, rho_89] <;> norm_num⟩

/-- **gamma at class 89, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_89`
consumed through `join50`. -/
theorem chjoin_89 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_89) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_89 (85/77 : ℝ) (25/19 : ℝ) castAB_89 hIn.1 Fresh.ChamberDatasheet.chds_89 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 89's own tuple (atom `chds_89` + proved join `inclass_89` +
`chjoin_89`). -/
theorem dead_89 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_89 s :=
  chjoin_89 rho_89 s hs h50 inclass_89

/-- jj#90 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=15/11 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_90 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 90 (exact rationals, the probe's own
case dump). -/
def rho_90 : Fin 5 → ℚ := ![1, 1, 9, 11, 76/5]

theorem castAB_90 : ((cls_90.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_90.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_90]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_90`/`cls_90` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_90 : InClass rho_90 cls_90 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_90, rho_90] <;> norm_num⟩

/-- **gamma at class 90, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_90`
consumed through `join50`. -/
theorem chjoin_90 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_90) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_90 (85/76 : ℝ) (15/11 : ℝ) castAB_90 hIn.1 Fresh.ChamberDatasheet.chds_90 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 90's own tuple (atom `chds_90` + proved join `inclass_90` +
`chjoin_90`). -/
theorem dead_90 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_90 s :=
  chjoin_90 rho_90 s hs h50 inclass_90

/-- jj#91 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=15/11 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_91 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 91 (exact rationals, the probe's own
case dump). -/
def rho_91 : Fin 5 → ℚ := ![1, 1, 9, 11, 77/5]

theorem castAB_91 : ((cls_91.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_91.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_91]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_91`/`cls_91` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_91 : InClass rho_91 cls_91 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_91, rho_91] <;> norm_num⟩

/-- **gamma at class 91, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_91`
consumed through `join50`. -/
theorem chjoin_91 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_91) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_91 (85/77 : ℝ) (15/11 : ℝ) castAB_91 hIn.1 Fresh.ChamberDatasheet.chds_91 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 91's own tuple (atom `chds_91` + proved join `inclass_91` +
`chjoin_91`). -/
theorem dead_91 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_91 s :=
  chjoin_91 rho_91 s hs h50 inclass_91

/-- jj#92 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=15/11 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_92 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 92 (exact rationals, the probe's own
case dump). -/
def rho_92 : Fin 5 → ℚ := ![1, 1, 9, 11, 78/5]

theorem castAB_92 : ((cls_92.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_92.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_92]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_92`/`cls_92` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_92 : InClass rho_92 cls_92 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_92, rho_92] <;> norm_num⟩

/-- **gamma at class 92, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_92`
consumed through `join50`. -/
theorem chjoin_92 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_92) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_92 (85/78 : ℝ) (15/11 : ℝ) castAB_92 hIn.1 Fresh.ChamberDatasheet.chds_92 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 92's own tuple (atom `chds_92` + proved join `inclass_92` +
`chjoin_92`). -/
theorem dead_92 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_92 s :=
  chjoin_92 rho_92 s hs h50 inclass_92

/-- jj#93 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=15/11 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_93 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 93 (exact rationals, the probe's own
case dump). -/
def rho_93 : Fin 5 → ℚ := ![1, 1, 9, 11, 79/5]

theorem castAB_93 : ((cls_93.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_93.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_93]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_93`/`cls_93` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_93 : InClass rho_93 cls_93 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_93, rho_93] <;> norm_num⟩

/-- **gamma at class 93, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_93`
consumed through `join50`. -/
theorem chjoin_93 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_93) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_93 (85/79 : ℝ) (15/11 : ℝ) castAB_93 hIn.1 Fresh.ChamberDatasheet.chds_93 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 93's own tuple (atom `chds_93` + proved join `inclass_93` +
`chjoin_93`). -/
theorem dead_93 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_93 s :=
  chjoin_93 rho_93 s hs h50 inclass_93

/-- jj#94 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=15/11 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_94 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 94 (exact rationals, the probe's own
case dump). -/
def rho_94 : Fin 5 → ℚ := ![1, 1, 9, 11, 16]

theorem castAB_94 : ((cls_94.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_94.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_94]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_94`/`cls_94` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_94 : InClass rho_94 cls_94 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_94, rho_94] <;> norm_num⟩

/-- **gamma at class 94, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_94`
consumed through `join50`. -/
theorem chjoin_94 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_94) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_94 (17/16 : ℝ) (15/11 : ℝ) castAB_94 hIn.1 Fresh.ChamberDatasheet.chds_94 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 94's own tuple (atom `chds_94` + proved join `inclass_94` +
`chjoin_94`). -/
theorem dead_94 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_94 s :=
  chjoin_94 rho_94 s hs h50 inclass_94

/-- jj#95 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=15/11 | D1 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_95 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 95 (exact rationals, the probe's own
case dump). -/
def rho_95 : Fin 5 → ℚ := ![1, 1, 9, 11, 81/5]

theorem castAB_95 : ((cls_95.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_95.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_95]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_95`/`cls_95` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_95 : InClass rho_95 cls_95 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_95, rho_95] <;> norm_num⟩

/-- **gamma at class 95, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_95`
consumed through `join50`. -/
theorem chjoin_95 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_95) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_95 (85/81 : ℝ) (15/11 : ℝ) castAB_95 hIn.1 Fresh.ChamberDatasheet.chds_95 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 95's own tuple (atom `chds_95` + proved join `inclass_95` +
`chjoin_95`). -/
theorem dead_95 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_95 s :=
  chjoin_95 rho_95 s hs h50 inclass_95

/-- jj#96 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=15/11 | D1 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_96 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 96 (exact rationals, the probe's own
case dump). -/
def rho_96 : Fin 5 → ℚ := ![1, 1, 9, 11, 82/5]

theorem castAB_96 : ((cls_96.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_96.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_96]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_96`/`cls_96` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_96 : InClass rho_96 cls_96 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_96, rho_96] <;> norm_num⟩

/-- **gamma at class 96, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_96`
consumed through `join50`. -/
theorem chjoin_96 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_96) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_96 (85/82 : ℝ) (15/11 : ℝ) castAB_96 hIn.1 Fresh.ChamberDatasheet.chds_96 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 96's own tuple (atom `chds_96` + proved join `inclass_96` +
`chjoin_96`). -/
theorem dead_96 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_96 s :=
  chjoin_96 rho_96 s hs h50 inclass_96

/-- jj#97 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=15/11 | D1 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_97 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 97 (exact rationals, the probe's own
case dump). -/
def rho_97 : Fin 5 → ℚ := ![1, 1, 9, 11, 83/5]

theorem castAB_97 : ((cls_97.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_97.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_97]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_97`/`cls_97` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_97 : InClass rho_97 cls_97 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_97, rho_97] <;> norm_num⟩

/-- **gamma at class 97, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_97`
consumed through `join50`. -/
theorem chjoin_97 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_97) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_97 (85/83 : ℝ) (15/11 : ℝ) castAB_97 hIn.1 Fresh.ChamberDatasheet.chds_97 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 97's own tuple (atom `chds_97` + proved join `inclass_97` +
`chjoin_97`). -/
theorem dead_97 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_97 s :=
  chjoin_97 rho_97 s hs h50 inclass_97

/-- jj#98 | PPG1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=15/11 | D1 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_98 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 98 (exact rationals, the probe's own
case dump). -/
def rho_98 : Fin 5 → ℚ := ![1, 1, 9, 11, 84/5]

theorem castAB_98 : ((cls_98.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_98.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_98]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_98`/`cls_98` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_98 : InClass rho_98 cls_98 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_98, rho_98] <;> norm_num⟩

/-- **gamma at class 98, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_98`
consumed through `join50`. -/
theorem chjoin_98 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_98) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_98 (85/84 : ℝ) (15/11 : ℝ) castAB_98 hIn.1 Fresh.ChamberDatasheet.chds_98 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 98's own tuple (atom `chds_98` + proved join `inclass_98` +
`chjoin_98`). -/
theorem dead_98 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_98 s :=
  chjoin_98 rho_98 s hs h50 inclass_98

/-- jj#99 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_99 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 99 (exact rationals, the probe's own
case dump). -/
def rho_99 : Fin 5 → ℚ := ![1, 1, 72/5, 15, 17]

theorem castAB_99 : ((cls_99.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_99.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_99]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_99`/`cls_99` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_99 : InClass rho_99 cls_99 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_99, rho_99] <;> norm_num⟩

/-- **gamma at class 99, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_99`
consumed through `join50`. -/
theorem chjoin_99 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_99) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_99 (85/72 : ℝ) (23/17 : ℝ) castAB_99 hIn.1 Fresh.ChamberDatasheet.chds_99 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 99's own tuple (atom `chds_99` + proved join `inclass_99` +
`chjoin_99`). -/
theorem dead_99 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_99 s :=
  chjoin_99 rho_99 s hs h50 inclass_99

/-- jj#100 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_100 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 100 (exact rationals, the probe's own
case dump). -/
def rho_100 : Fin 5 → ℚ := ![1, 1, 73/5, 15, 17]

theorem castAB_100 : ((cls_100.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_100.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_100]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_100`/`cls_100` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_100 : InClass rho_100 cls_100 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_100, rho_100] <;> norm_num⟩

/-- **gamma at class 100, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_100`
consumed through `join50`. -/
theorem chjoin_100 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_100) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_100 (85/73 : ℝ) (23/17 : ℝ) castAB_100 hIn.1 Fresh.ChamberDatasheet.chds_100 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 100's own tuple (atom `chds_100` + proved join `inclass_100` +
`chjoin_100`). -/
theorem dead_100 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_100 s :=
  chjoin_100 rho_100 s hs h50 inclass_100

/-- jj#101 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_101 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 101 (exact rationals, the probe's own
case dump). -/
def rho_101 : Fin 5 → ℚ := ![1, 1, 74/5, 15, 17]

theorem castAB_101 : ((cls_101.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_101.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_101]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_101`/`cls_101` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_101 : InClass rho_101 cls_101 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_101, rho_101] <;> norm_num⟩

/-- **gamma at class 101, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_101`
consumed through `join50`. -/
theorem chjoin_101 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_101) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_101 (85/74 : ℝ) (23/17 : ℝ) castAB_101 hIn.1 Fresh.ChamberDatasheet.chds_101 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 101's own tuple (atom `chds_101` + proved join `inclass_101` +
`chjoin_101`). -/
theorem dead_101 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_101 s :=
  chjoin_101 rho_101 s hs h50 inclass_101

/-- jj#102 | PPG1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_102 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 17], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 102 (exact rationals, the probe's own
case dump). -/
def rho_102 : Fin 5 → ℚ := ![1, 1, 72/5, 15, 17]

theorem castAB_102 : ((cls_102.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_102.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_102]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_102`/`cls_102` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_102 : InClass rho_102 cls_102 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_102, rho_102] <;> norm_num⟩

/-- **gamma at class 102, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_102`
consumed through `join50`. -/
theorem chjoin_102 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_102) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_102 (85/72 : ℝ) (23/17 : ℝ) castAB_102 hIn.1 Fresh.ChamberDatasheet.chds_102 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 102's own tuple (atom `chds_102` + proved join `inclass_102` +
`chjoin_102`). -/
theorem dead_102 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_102 s :=
  chjoin_102 rho_102 s hs h50 inclass_102

/-- jj#103 | PPG1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_103 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 17], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 103 (exact rationals, the probe's own
case dump). -/
def rho_103 : Fin 5 → ℚ := ![1, 1, 73/5, 15, 17]

theorem castAB_103 : ((cls_103.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_103.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_103]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_103`/`cls_103` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_103 : InClass rho_103 cls_103 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_103, rho_103] <;> norm_num⟩

/-- **gamma at class 103, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_103`
consumed through `join50`. -/
theorem chjoin_103 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_103) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_103 (85/73 : ℝ) (23/17 : ℝ) castAB_103 hIn.1 Fresh.ChamberDatasheet.chds_103 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 103's own tuple (atom `chds_103` + proved join `inclass_103` +
`chjoin_103`). -/
theorem dead_103 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_103 s :=
  chjoin_103 rho_103 s hs h50 inclass_103

/-- jj#104 | PPG1S2E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 2541 cases | NO-ALIVE-ON-GRID -/
def cls_104 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 9, 15, 17], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 104 (exact rationals, the probe's own
case dump). -/
def rho_104 : Fin 5 → ℚ := ![1, 1, 74/5, 15, 17]

theorem castAB_104 : ((cls_104.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_104.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_104]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_104`/`cls_104` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_104 : InClass rho_104 cls_104 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_104, rho_104] <;> norm_num⟩

/-- **gamma at class 104, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_104`
consumed through `join50`. -/
theorem chjoin_104 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_104) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_104 (85/74 : ℝ) (23/17 : ℝ) castAB_104 hIn.1 Fresh.ChamberDatasheet.chds_104 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 104's own tuple (atom `chds_104` + proved join `inclass_104` +
`chjoin_104`). -/
theorem dead_104 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_104 s :=
  chjoin_104 rho_104 s hs h50 inclass_104

/-- jj#105 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/56 | D2 | 2530 cases | NO-ALIVE-ON-GRID -/
def cls_105 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 105 (exact rationals, the probe's own
case dump). -/
def rho_105 : Fin 5 → ℚ := ![1, 1, 56/5, 76/5, 76/5]

theorem castAB_105 : ((cls_105.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_105.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_105]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_105`/`cls_105` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_105 : InClass rho_105 cls_105 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_105, rho_105] <;> norm_num⟩

/-- **gamma at class 105, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_105`
consumed through `join50`. -/
theorem chjoin_105 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_105) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_105 (85/76 : ℝ) (75/56 : ℝ) castAB_105 hIn.1 Fresh.ChamberDatasheet.chds_105 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 105's own tuple (atom `chds_105` + proved join `inclass_105` +
`chjoin_105`). -/
theorem dead_105 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_105 s :=
  chjoin_105 rho_105 s hs h50 inclass_105

/-- jj#106 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=25/19 | D2 | 2530 cases | NO-ALIVE-ON-GRID -/
def cls_106 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 106 (exact rationals, the probe's own
case dump). -/
def rho_106 : Fin 5 → ℚ := ![1, 1, 57/5, 76/5, 76/5]

theorem castAB_106 : ((cls_106.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_106.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_106]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_106`/`cls_106` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_106 : InClass rho_106 cls_106 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_106, rho_106] <;> norm_num⟩

/-- **gamma at class 106, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_106`
consumed through `join50`. -/
theorem chjoin_106 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_106) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_106 (85/76 : ℝ) (25/19 : ℝ) castAB_106 hIn.1 Fresh.ChamberDatasheet.chds_106 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 106's own tuple (atom `chds_106` + proved join `inclass_106` +
`chjoin_106`). -/
theorem dead_106 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_106 s :=
  chjoin_106 rho_106 s hs h50 inclass_106

/-- jj#107 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=23/16 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_107 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/16 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 107 (exact rationals, the probe's own
case dump). -/
def rho_107 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 16]

theorem castAB_107 : ((cls_107.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_107.B : ℚ) : ℝ) = (23/16 : ℝ) := by
  norm_num [cls_107]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_107`/`cls_107` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_107 : InClass rho_107 cls_107 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_107, rho_107] <;> norm_num⟩

/-- **gamma at class 107, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_107`
consumed through `join50`. -/
theorem chjoin_107 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_107) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_107 (85/72 : ℝ) (23/16 : ℝ) castAB_107 hIn.1 Fresh.ChamberDatasheet.chds_107 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 107's own tuple (atom `chds_107` + proved join `inclass_107` +
`chjoin_107`). -/
theorem dead_107 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_107 s :=
  chjoin_107 rho_107 s hs h50 inclass_107

/-- jj#108 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/81 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_108 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/81 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 108 (exact rationals, the probe's own
case dump). -/
def rho_108 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 81/5]

theorem castAB_108 : ((cls_108.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_108.B : ℚ) : ℝ) = (115/81 : ℝ) := by
  norm_num [cls_108]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_108`/`cls_108` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_108 : InClass rho_108 cls_108 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_108, rho_108] <;> norm_num⟩

/-- **gamma at class 108, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_108`
consumed through `join50`. -/
theorem chjoin_108 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_108) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_108 (85/72 : ℝ) (115/81 : ℝ) castAB_108 hIn.1 Fresh.ChamberDatasheet.chds_108 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 108's own tuple (atom `chds_108` + proved join `inclass_108` +
`chjoin_108`). -/
theorem dead_108 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_108 s :=
  chjoin_108 rho_108 s hs h50 inclass_108

/-- jj#109 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/82 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_109 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 109 (exact rationals, the probe's own
case dump). -/
def rho_109 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 82/5]

theorem castAB_109 : ((cls_109.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_109.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_109]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_109`/`cls_109` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_109 : InClass rho_109 cls_109 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_109, rho_109] <;> norm_num⟩

/-- **gamma at class 109, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_109`
consumed through `join50`. -/
theorem chjoin_109 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_109) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_109 (85/73 : ℝ) (115/82 : ℝ) castAB_109 hIn.1 Fresh.ChamberDatasheet.chds_109 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 109's own tuple (atom `chds_109` + proved join `inclass_109` +
`chjoin_109`). -/
theorem dead_109 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_109 s :=
  chjoin_109 rho_109 s hs h50 inclass_109

/-- jj#110 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_110 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 110 (exact rationals, the probe's own
case dump). -/
def rho_110 : Fin 5 → ℚ := ![1, 9, 9, 72/5, 17]

theorem castAB_110 : ((cls_110.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_110.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_110]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_110`/`cls_110` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_110 : InClass rho_110 cls_110 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_110, rho_110] <;> norm_num⟩

/-- **gamma at class 110, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_110`
consumed through `join50`. -/
theorem chjoin_110 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_110) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_110 (85/72 : ℝ) (23/17 : ℝ) castAB_110 hIn.1 Fresh.ChamberDatasheet.chds_110 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 110's own tuple (atom `chds_110` + proved join `inclass_110` +
`chjoin_110`). -/
theorem dead_110 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_110 s :=
  chjoin_110 rho_110 s hs h50 inclass_110

/-- jj#111 | PG1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_111 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 111 (exact rationals, the probe's own
case dump). -/
def rho_111 : Fin 5 → ℚ := ![1, 9, 9, 72/5, 17]

theorem castAB_111 : ((cls_111.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_111.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_111]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_111`/`cls_111` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_111 : InClass rho_111 cls_111 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_111, rho_111] <;> norm_num⟩

/-- **gamma at class 111, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_111`
consumed through `join50`. -/
theorem chjoin_111 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_111) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_111 (85/72 : ℝ) (23/17 : ℝ) castAB_111 hIn.1 Fresh.ChamberDatasheet.chds_111 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 111's own tuple (atom `chds_111` + proved join `inclass_111` +
`chjoin_111`). -/
theorem dead_111 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_111 s :=
  chjoin_111 rho_111 s hs h50 inclass_111

/-- jj#112 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/84 | D2 | 2520 cases | NO-ALIVE-ON-GRID -/
def cls_112 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 112 (exact rationals, the probe's own
case dump). -/
def rho_112 : Fin 5 → ℚ := ![1, 9, 74/5, 15, 84/5]

theorem castAB_112 : ((cls_112.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_112.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_112]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_112`/`cls_112` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_112 : InClass rho_112 cls_112 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_112, rho_112] <;> norm_num⟩

/-- **gamma at class 112, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_112`
consumed through `join50`. -/
theorem chjoin_112 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_112) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_112 (85/74 : ℝ) (115/84 : ℝ) castAB_112 hIn.1 Fresh.ChamberDatasheet.chds_112 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 112's own tuple (atom `chds_112` + proved join `inclass_112` +
`chjoin_112`). -/
theorem dead_112 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_112 s :=
  chjoin_112 rho_112 s hs h50 inclass_112

/-- jj#113 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/72 | D2 | 2508 cases | NO-ALIVE-ON-GRID -/
def cls_113 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 113 (exact rationals, the probe's own
case dump). -/
def rho_113 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 72/5]

theorem castAB_113 : ((cls_113.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_113.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_113]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_113`/`cls_113` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_113 : InClass rho_113 cls_113 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_113, rho_113] <;> norm_num⟩

/-- **gamma at class 113, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_113`
consumed through `join50`. -/
theorem chjoin_113 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_113) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_113 (85/63 : ℝ) (115/72 : ℝ) castAB_113 hIn.1 Fresh.ChamberDatasheet.chds_113 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 113's own tuple (atom `chds_113` + proved join `inclass_113` +
`chjoin_113`). -/
theorem dead_113 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_113 s :=
  chjoin_113 rho_113 s hs h50 inclass_113

/-- jj#114 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/73 | D2 | 2508 cases | NO-ALIVE-ON-GRID -/
def cls_114 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 114 (exact rationals, the probe's own
case dump). -/
def rho_114 : Fin 5 → ℚ := ![1, 7, 9, 13, 73/5]

theorem castAB_114 : ((cls_114.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_114.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_114]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_114`/`cls_114` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_114 : InClass rho_114 cls_114 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_114, rho_114] <;> norm_num⟩

/-- **gamma at class 114, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_114`
consumed through `join50`. -/
theorem chjoin_114 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_114) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_114 (17/13 : ℝ) (115/73 : ℝ) castAB_114 hIn.1 Fresh.ChamberDatasheet.chds_114 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 114's own tuple (atom `chds_114` + proved join `inclass_114` +
`chjoin_114`). -/
theorem dead_114 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_114 s :=
  chjoin_114 rho_114 s hs h50 inclass_114

/-- jj#115 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/58 | D2 | 2484 cases | NO-ALIVE-ON-GRID -/
def cls_115 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 115 (exact rationals, the probe's own
case dump). -/
def rho_115 : Fin 5 → ℚ := ![1, 1, 58/5, 77/5, 77/5]

theorem castAB_115 : ((cls_115.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_115.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_115]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_115`/`cls_115` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_115 : InClass rho_115 cls_115 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_115, rho_115] <;> norm_num⟩

/-- **gamma at class 115, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_115`
consumed through `join50`. -/
theorem chjoin_115 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_115) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_115 (85/77 : ℝ) (75/58 : ℝ) castAB_115 hIn.1 Fresh.ChamberDatasheet.chds_115 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 115's own tuple (atom `chds_115` + proved join `inclass_115` +
`chjoin_115`). -/
theorem dead_115 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_115 s :=
  chjoin_115 rho_115 s hs h50 inclass_115

/-- jj#116 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=25/17 | D2 | 2470 cases | NO-ALIVE-ON-GRID -/
def cls_116 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 116 (exact rationals, the probe's own
case dump). -/
def rho_116 : Fin 5 → ℚ := ![1, 1, 37/5, 9, 51/5]

theorem castAB_116 : ((cls_116.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_116.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_116]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_116`/`cls_116` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_116 : InClass rho_116 cls_116 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_116, rho_116] <;> norm_num⟩

/-- **gamma at class 116, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_116`
consumed through `join50`. -/
theorem chjoin_116 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_116) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_116 (45/37 : ℝ) (25/17 : ℝ) castAB_116 hIn.1 Fresh.ChamberDatasheet.chds_116 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 116's own tuple (atom `chds_116` + proved join `inclass_116` +
`chjoin_116`). -/
theorem dead_116 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_116 s :=
  chjoin_116 rho_116 s hs h50 inclass_116

/-- jj#117 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/74 | D2 | 2470 cases | NO-ALIVE-ON-GRID -/
def cls_117 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 117 (exact rationals, the probe's own
case dump). -/
def rho_117 : Fin 5 → ℚ := ![1, 1, 9, 66/5, 74/5]

theorem castAB_117 : ((cls_117.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_117.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_117]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_117`/`cls_117` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_117 : InClass rho_117 cls_117 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_117, rho_117] <;> norm_num⟩

/-- **gamma at class 117, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_117`
consumed through `join50`. -/
theorem chjoin_117 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_117) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_117 (85/66 : ℝ) (115/74 : ℝ) castAB_117 hIn.1 Fresh.ChamberDatasheet.chds_117 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 117's own tuple (atom `chds_117` + proved join `inclass_117` +
`chjoin_117`). -/
theorem dead_117 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_117 s :=
  chjoin_117 rho_117 s hs h50 inclass_117

/-- jj#118 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 2457 cases | NO-ALIVE-ON-GRID -/
def cls_118 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 118 (exact rationals, the probe's own
case dump). -/
def rho_118 : Fin 5 → ℚ := ![1, 9, 73/5, 15, 83/5]

theorem castAB_118 : ((cls_118.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_118.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_118]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_118`/`cls_118` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_118 : InClass rho_118 cls_118 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_118, rho_118] <;> norm_num⟩

/-- **gamma at class 118, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_118`
consumed through `join50`. -/
theorem chjoin_118 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_118) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_118 (85/73 : ℝ) (115/83 : ℝ) castAB_118 hIn.1 Fresh.ChamberDatasheet.chds_118 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 118's own tuple (atom `chds_118` + proved join `inclass_118` +
`chjoin_118`). -/
theorem dead_118 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_118 s :=
  chjoin_118 rho_118 s hs h50 inclass_118

/-- jj#119 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_119 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 119 (exact rationals, the probe's own
case dump). -/
def rho_119 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 76/5]

theorem castAB_119 : ((cls_119.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_119.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_119]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_119`/`cls_119` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_119 : InClass rho_119 cls_119 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_119, rho_119] <;> norm_num⟩

/-- **gamma at class 119, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_119`
consumed through `join50`. -/
theorem chjoin_119 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_119) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_119 (85/76 : ℝ) (75/58 : ℝ) castAB_119 hIn.1 Fresh.ChamberDatasheet.chds_119 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 119's own tuple (atom `chds_119` + proved join `inclass_119` +
`chjoin_119`). -/
theorem dead_119 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_119 s :=
  chjoin_119 rho_119 s hs h50 inclass_119

/-- jj#120 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_120 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 120 (exact rationals, the probe's own
case dump). -/
def rho_120 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 77/5]

theorem castAB_120 : ((cls_120.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_120.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_120]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_120`/`cls_120` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_120 : InClass rho_120 cls_120 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_120, rho_120] <;> norm_num⟩

/-- **gamma at class 120, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_120`
consumed through `join50`. -/
theorem chjoin_120 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_120) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_120 (85/77 : ℝ) (75/58 : ℝ) castAB_120 hIn.1 Fresh.ChamberDatasheet.chds_120 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 120's own tuple (atom `chds_120` + proved join `inclass_120` +
`chjoin_120`). -/
theorem dead_120 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_120 s :=
  chjoin_120 rho_120 s hs h50 inclass_120

/-- jj#121 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_121 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 121 (exact rationals, the probe's own
case dump). -/
def rho_121 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 78/5]

theorem castAB_121 : ((cls_121.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_121.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_121]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_121`/`cls_121` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_121 : InClass rho_121 cls_121 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_121, rho_121] <;> norm_num⟩

/-- **gamma at class 121, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_121`
consumed through `join50`. -/
theorem chjoin_121 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_121) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_121 (85/78 : ℝ) (75/58 : ℝ) castAB_121 hIn.1 Fresh.ChamberDatasheet.chds_121 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 121's own tuple (atom `chds_121` + proved join `inclass_121` +
`chjoin_121`). -/
theorem dead_121 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_121 s :=
  chjoin_121 rho_121 s hs h50 inclass_121

/-- jj#122 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_122 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 122 (exact rationals, the probe's own
case dump). -/
def rho_122 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 79/5]

theorem castAB_122 : ((cls_122.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_122.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_122]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_122`/`cls_122` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_122 : InClass rho_122 cls_122 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_122, rho_122] <;> norm_num⟩

/-- **gamma at class 122, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_122`
consumed through `join50`. -/
theorem chjoin_122 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_122) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_122 (85/79 : ℝ) (75/58 : ℝ) castAB_122 hIn.1 Fresh.ChamberDatasheet.chds_122 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 122's own tuple (atom `chds_122` + proved join `inclass_122` +
`chjoin_122`). -/
theorem dead_122 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_122 s :=
  chjoin_122 rho_122 s hs h50 inclass_122

/-- jj#123 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_123 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 123 (exact rationals, the probe's own
case dump). -/
def rho_123 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 16]

theorem castAB_123 : ((cls_123.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_123.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_123]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_123`/`cls_123` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_123 : InClass rho_123 cls_123 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_123, rho_123] <;> norm_num⟩

/-- **gamma at class 123, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_123`
consumed through `join50`. -/
theorem chjoin_123 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_123) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_123 (17/16 : ℝ) (75/58 : ℝ) castAB_123 hIn.1 Fresh.ChamberDatasheet.chds_123 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 123's own tuple (atom `chds_123` + proved join `inclass_123` +
`chjoin_123`). -/
theorem dead_123 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_123 s :=
  chjoin_123 rho_123 s hs h50 inclass_123

/-- jj#124 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_124 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 124 (exact rationals, the probe's own
case dump). -/
def rho_124 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 81/5]

theorem castAB_124 : ((cls_124.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_124.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_124]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_124`/`cls_124` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_124 : InClass rho_124 cls_124 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_124, rho_124] <;> norm_num⟩

/-- **gamma at class 124, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_124`
consumed through `join50`. -/
theorem chjoin_124 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_124) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_124 (85/81 : ℝ) (75/58 : ℝ) castAB_124 hIn.1 Fresh.ChamberDatasheet.chds_124 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 124's own tuple (atom `chds_124` + proved join `inclass_124` +
`chjoin_124`). -/
theorem dead_124 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_124 s :=
  chjoin_124 rho_124 s hs h50 inclass_124

/-- jj#125 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_125 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 125 (exact rationals, the probe's own
case dump). -/
def rho_125 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 82/5]

theorem castAB_125 : ((cls_125.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_125.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_125]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_125`/`cls_125` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_125 : InClass rho_125 cls_125 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_125, rho_125] <;> norm_num⟩

/-- **gamma at class 125, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_125`
consumed through `join50`. -/
theorem chjoin_125 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_125) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_125 (85/82 : ℝ) (75/58 : ℝ) castAB_125 hIn.1 Fresh.ChamberDatasheet.chds_125 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 125's own tuple (atom `chds_125` + proved join `inclass_125` +
`chjoin_125`). -/
theorem dead_125 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_125 s :=
  chjoin_125 rho_125 s hs h50 inclass_125

/-- jj#126 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_126 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 126 (exact rationals, the probe's own
case dump). -/
def rho_126 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 83/5]

theorem castAB_126 : ((cls_126.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_126.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_126]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_126`/`cls_126` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_126 : InClass rho_126 cls_126 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_126, rho_126] <;> norm_num⟩

/-- **gamma at class 126, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_126`
consumed through `join50`. -/
theorem chjoin_126 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_126) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_126 (85/83 : ℝ) (75/58 : ℝ) castAB_126 hIn.1 Fresh.ChamberDatasheet.chds_126 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 126's own tuple (atom `chds_126` + proved join `inclass_126` +
`chjoin_126`). -/
theorem dead_126 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_126 s :=
  chjoin_126 rho_126 s hs h50 inclass_126

/-- jj#127 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/58 | D2 | 2415 cases | NO-ALIVE-ON-GRID -/
def cls_127 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 127 (exact rationals, the probe's own
case dump). -/
def rho_127 : Fin 5 → ℚ := ![1, 9, 9, 58/5, 84/5]

theorem castAB_127 : ((cls_127.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_127.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_127]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_127`/`cls_127` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_127 : InClass rho_127 cls_127 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_127, rho_127] <;> norm_num⟩

/-- **gamma at class 127, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_127`
consumed through `join50`. -/
theorem chjoin_127 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_127) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_127 (85/84 : ℝ) (75/58 : ℝ) castAB_127 hIn.1 Fresh.ChamberDatasheet.chds_127 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 127's own tuple (atom `chds_127` + proved join `inclass_127` +
`chjoin_127`). -/
theorem dead_127 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_127 s :=
  chjoin_127 rho_127 s hs h50 inclass_127

/-- jj#128 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/74 | D2 | 2400 cases | NO-ALIVE-ON-GRID -/
def cls_128 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 128 (exact rationals, the probe's own
case dump). -/
def rho_128 : Fin 5 → ℚ := ![1, 9, 9, 64/5, 74/5]

theorem castAB_128 : ((cls_128.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_128.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_128]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_128`/`cls_128` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_128 : InClass rho_128 cls_128 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_128, rho_128] <;> norm_num⟩

/-- **gamma at class 128, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_128`
consumed through `join50`. -/
theorem chjoin_128 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_128) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_128 (85/64 : ℝ) (115/74 : ℝ) castAB_128 hIn.1 Fresh.ChamberDatasheet.chds_128 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 128's own tuple (atom `chds_128` + proved join `inclass_128` +
`chjoin_128`). -/
theorem dead_128 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_128 s :=
  chjoin_128 rho_128 s hs h50 inclass_128

/-- jj#129 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/56 | D2 | 2376 cases | NO-ALIVE-ON-GRID -/
def cls_129 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 129 (exact rationals, the probe's own
case dump). -/
def rho_129 : Fin 5 → ℚ := ![1, 9, 56/5, 77/5, 77/5]

theorem castAB_129 : ((cls_129.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_129.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_129]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_129`/`cls_129` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_129 : InClass rho_129 cls_129 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_129, rho_129] <;> norm_num⟩

/-- **gamma at class 129, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_129`
consumed through `join50`. -/
theorem chjoin_129 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_129) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_129 (85/77 : ℝ) (75/56 : ℝ) castAB_129 hIn.1 Fresh.ChamberDatasheet.chds_129 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 129's own tuple (atom `chds_129` + proved join `inclass_129` +
`chjoin_129`). -/
theorem dead_129 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_129 s :=
  chjoin_129 rho_129 s hs h50 inclass_129

/-- jj#130 | PPPS1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=75/44 | D1 | 2346 cases | NO-ALIVE-ON-GRID -/
def cls_130 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (75/44 : ℚ),
    lo := ![1, 1, 1, 7, 7], hi := ![7, 7, 7, 9, 9] }

/-- The recorded representative 5-tuple of class 130 (exact rationals, the probe's own
case dump). -/
def rho_130 : Fin 5 → ℚ := ![1, 1, 1, 7, 44/5]

theorem castAB_130 : ((cls_130.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_130.B : ℚ) : ℝ) = (75/44 : ℝ) := by
  norm_num [cls_130]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_130`/`cls_130` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_130 : InClass rho_130 cls_130 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_130, rho_130] <;> norm_num⟩

/-- **gamma at class 130, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_130`
consumed through `join50`. -/
theorem chjoin_130 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_130) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_130 (9/7 : ℝ) (75/44 : ℝ) castAB_130 hIn.1 Fresh.ChamberDatasheet.chds_130 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 130's own tuple (atom `chds_130` + proved join `inclass_130` +
`chjoin_130`). -/
theorem dead_130 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_130 s :=
  chjoin_130 rho_130 s hs h50 inclass_130

/-- jj#131 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/74 | D2 | 2342 cases | NO-ALIVE-ON-GRID -/
def cls_131 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 131 (exact rationals, the probe's own
case dump). -/
def rho_131 : Fin 5 → ℚ := ![1, 9, 63/5, 64/5, 74/5]

theorem castAB_131 : ((cls_131.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_131.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_131]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_131`/`cls_131` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_131 : InClass rho_131 cls_131 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_131, rho_131] <;> norm_num⟩

/-- **gamma at class 131, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_131`
consumed through `join50`. -/
theorem chjoin_131 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_131) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_131 (85/63 : ℝ) (115/74 : ℝ) castAB_131 hIn.1 Fresh.ChamberDatasheet.chds_131 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 131's own tuple (atom `chds_131` + proved join `inclass_131` +
`chjoin_131`). -/
theorem dead_131 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_131 s :=
  chjoin_131 rho_131 s hs h50 inclass_131

/-- jj#132 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=75/49 | D2 | 2340 cases | NO-ALIVE-ON-GRID -/
def cls_132 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 132 (exact rationals, the probe's own
case dump). -/
def rho_132 : Fin 5 → ℚ := ![1, 36/5, 36/5, 9, 49/5]

theorem castAB_132 : ((cls_132.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_132.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_132]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_132`/`cls_132` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_132 : InClass rho_132 cls_132 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_132, rho_132] <;> norm_num⟩

/-- **gamma at class 132, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_132`
consumed through `join50`. -/
theorem chjoin_132 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_132) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_132 (5/4 : ℝ) (75/49 : ℝ) castAB_132 hIn.1 Fresh.ChamberDatasheet.chds_132 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 132's own tuple (atom `chds_132` + proved join `inclass_132` +
`chjoin_132`). -/
theorem dead_132 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_132 s :=
  chjoin_132 rho_132 s hs h50 inclass_132

/-- jj#133 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/74 | D2 | 2334 cases | NO-ALIVE-ON-GRID -/
def cls_133 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 133 (exact rationals, the probe's own
case dump). -/
def rho_133 : Fin 5 → ℚ := ![1, 1, 63/5, 64/5, 74/5]

theorem castAB_133 : ((cls_133.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_133.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_133]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_133`/`cls_133` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_133 : InClass rho_133 cls_133 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_133, rho_133] <;> norm_num⟩

/-- **gamma at class 133, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_133`
consumed through `join50`. -/
theorem chjoin_133 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_133) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_133 (85/63 : ℝ) (115/74 : ℝ) castAB_133 hIn.1 Fresh.ChamberDatasheet.chds_133 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 133's own tuple (atom `chds_133` + proved join `inclass_133` +
`chjoin_133`). -/
theorem dead_133 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_133 s :=
  chjoin_133 rho_133 s hs h50 inclass_133

/-- jj#134 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/73 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_134 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 134 (exact rationals, the probe's own
case dump). -/
def rho_134 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 73/5]

theorem castAB_134 : ((cls_134.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_134.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_134]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_134`/`cls_134` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_134 : InClass rho_134 cls_134 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_134, rho_134] <;> norm_num⟩

/-- **gamma at class 134, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_134`
consumed through `join50`. -/
theorem chjoin_134 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_134) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_134 (85/63 : ℝ) (115/73 : ℝ) castAB_134 hIn.1 Fresh.ChamberDatasheet.chds_134 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 134's own tuple (atom `chds_134` + proved join `inclass_134` +
`chjoin_134`). -/
theorem dead_134 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_134 s :=
  chjoin_134 rho_134 s hs h50 inclass_134

/-- jj#135 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_135 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 135 (exact rationals, the probe's own
case dump). -/
def rho_135 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 15]

theorem castAB_135 : ((cls_135.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_135.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_135]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_135`/`cls_135` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_135 : InClass rho_135 cls_135 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_135, rho_135] <;> norm_num⟩

/-- **gamma at class 135, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_135`
consumed through `join50`. -/
theorem chjoin_135 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_135) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_135 (85/63 : ℝ) (23/15 : ℝ) castAB_135 hIn.1 Fresh.ChamberDatasheet.chds_135 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 135's own tuple (atom `chds_135` + proved join `inclass_135` +
`chjoin_135`). -/
theorem dead_135 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_135 s :=
  chjoin_135 rho_135 s hs h50 inclass_135

/-- jj#136 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/73 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_136 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 136 (exact rationals, the probe's own
case dump). -/
def rho_136 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 73/5]

theorem castAB_136 : ((cls_136.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_136.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_136]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_136`/`cls_136` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_136 : InClass rho_136 cls_136 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_136, rho_136] <;> norm_num⟩

/-- **gamma at class 136, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_136`
consumed through `join50`. -/
theorem chjoin_136 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_136) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_136 (85/64 : ℝ) (115/73 : ℝ) castAB_136 hIn.1 Fresh.ChamberDatasheet.chds_136 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 136's own tuple (atom `chds_136` + proved join `inclass_136` +
`chjoin_136`). -/
theorem dead_136 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_136 s :=
  chjoin_136 rho_136 s hs h50 inclass_136

/-- jj#137 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/74 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_137 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 137 (exact rationals, the probe's own
case dump). -/
def rho_137 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 74/5]

theorem castAB_137 : ((cls_137.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_137.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_137]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_137`/`cls_137` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_137 : InClass rho_137 cls_137 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_137, rho_137] <;> norm_num⟩

/-- **gamma at class 137, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_137`
consumed through `join50`. -/
theorem chjoin_137 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_137) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_137 (85/64 : ℝ) (115/74 : ℝ) castAB_137 hIn.1 Fresh.ChamberDatasheet.chds_137 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 137's own tuple (atom `chds_137` + proved join `inclass_137` +
`chjoin_137`). -/
theorem dead_137 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_137 s :=
  chjoin_137 rho_137 s hs h50 inclass_137

/-- jj#138 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_138 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 138 (exact rationals, the probe's own
case dump). -/
def rho_138 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 15]

theorem castAB_138 : ((cls_138.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_138.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_138]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_138`/`cls_138` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_138 : InClass rho_138 cls_138 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_138, rho_138] <;> norm_num⟩

/-- **gamma at class 138, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_138`
consumed through `join50`. -/
theorem chjoin_138 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_138) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_138 (85/64 : ℝ) (23/15 : ℝ) castAB_138 hIn.1 Fresh.ChamberDatasheet.chds_138 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 138's own tuple (atom `chds_138` + proved join `inclass_138` +
`chjoin_138`). -/
theorem dead_138 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_138 s :=
  chjoin_138 rho_138 s hs h50 inclass_138

/-- jj#139 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_139 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 139 (exact rationals, the probe's own
case dump). -/
def rho_139 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 15]

theorem castAB_139 : ((cls_139.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_139.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_139]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_139`/`cls_139` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_139 : InClass rho_139 cls_139 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_139, rho_139] <;> norm_num⟩

/-- **gamma at class 139, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_139`
consumed through `join50`. -/
theorem chjoin_139 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_139) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_139 (85/63 : ℝ) (23/15 : ℝ) castAB_139 hIn.1 Fresh.ChamberDatasheet.chds_139 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 139's own tuple (atom `chds_139` + proved join `inclass_139` +
`chjoin_139`). -/
theorem dead_139 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_139 s :=
  chjoin_139 rho_139 s hs h50 inclass_139

/-- jj#140 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/15 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_140 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 140 (exact rationals, the probe's own
case dump). -/
def rho_140 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 15]

theorem castAB_140 : ((cls_140.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_140.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_140]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_140`/`cls_140` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_140 : InClass rho_140 cls_140 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_140, rho_140] <;> norm_num⟩

/-- **gamma at class 140, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_140`
consumed through `join50`. -/
theorem chjoin_140 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_140) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_140 (85/64 : ℝ) (23/15 : ℝ) castAB_140 hIn.1 Fresh.ChamberDatasheet.chds_140 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 140's own tuple (atom `chds_140` + proved join `inclass_140` +
`chjoin_140`). -/
theorem dead_140 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_140 s :=
  chjoin_140 rho_140 s hs h50 inclass_140

/-- jj#141 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/79 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_141 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/79 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 141 (exact rationals, the probe's own
case dump). -/
def rho_141 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 79/5]

theorem castAB_141 : ((cls_141.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_141.B : ℚ) : ℝ) = (115/79 : ℝ) := by
  norm_num [cls_141]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_141`/`cls_141` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_141 : InClass rho_141 cls_141 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_141, rho_141] <;> norm_num⟩

/-- **gamma at class 141, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_141`
consumed through `join50`. -/
theorem chjoin_141 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_141) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_141 (85/72 : ℝ) (115/79 : ℝ) castAB_141 hIn.1 Fresh.ChamberDatasheet.chds_141 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 141's own tuple (atom `chds_141` + proved join `inclass_141` +
`chjoin_141`). -/
theorem dead_141 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_141 s :=
  chjoin_141 rho_141 s hs h50 inclass_141

/-- jj#142 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=23/16 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_142 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/16 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 142 (exact rationals, the probe's own
case dump). -/
def rho_142 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 16]

theorem castAB_142 : ((cls_142.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_142.B : ℚ) : ℝ) = (23/16 : ℝ) := by
  norm_num [cls_142]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_142`/`cls_142` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_142 : InClass rho_142 cls_142 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_142, rho_142] <;> norm_num⟩

/-- **gamma at class 142, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_142`
consumed through `join50`. -/
theorem chjoin_142 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_142) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_142 (85/73 : ℝ) (23/16 : ℝ) castAB_142 hIn.1 Fresh.ChamberDatasheet.chds_142 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 142's own tuple (atom `chds_142` + proved join `inclass_142` +
`chjoin_142`). -/
theorem dead_142 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_142 s :=
  chjoin_142 rho_142 s hs h50 inclass_142

/-- jj#143 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/81 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_143 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/81 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 143 (exact rationals, the probe's own
case dump). -/
def rho_143 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 81/5]

theorem castAB_143 : ((cls_143.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_143.B : ℚ) : ℝ) = (115/81 : ℝ) := by
  norm_num [cls_143]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_143`/`cls_143` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_143 : InClass rho_143 cls_143 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_143, rho_143] <;> norm_num⟩

/-- **gamma at class 143, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_143`
consumed through `join50`. -/
theorem chjoin_143 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_143) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_143 (85/73 : ℝ) (115/81 : ℝ) castAB_143 hIn.1 Fresh.ChamberDatasheet.chds_143 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 143's own tuple (atom `chds_143` + proved join `inclass_143` +
`chjoin_143`). -/
theorem dead_143 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_143 s :=
  chjoin_143 rho_143 s hs h50 inclass_143

/-- jj#144 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/82 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_144 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 144 (exact rationals, the probe's own
case dump). -/
def rho_144 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 82/5]

theorem castAB_144 : ((cls_144.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_144.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_144]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_144`/`cls_144` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_144 : InClass rho_144 cls_144 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_144, rho_144] <;> norm_num⟩

/-- **gamma at class 144, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_144`
consumed through `join50`. -/
theorem chjoin_144 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_144) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_144 (85/74 : ℝ) (115/82 : ℝ) castAB_144 hIn.1 Fresh.ChamberDatasheet.chds_144 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 144's own tuple (atom `chds_144` + proved join `inclass_144` +
`chjoin_144`). -/
theorem dead_144 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_144 s :=
  chjoin_144 rho_144 s hs h50 inclass_144

/-- jj#145 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_145 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 145 (exact rationals, the probe's own
case dump). -/
def rho_145 : Fin 5 → ℚ := ![1, 1, 72/5, 15, 84/5]

theorem castAB_145 : ((cls_145.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_145.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_145]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_145`/`cls_145` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_145 : InClass rho_145 cls_145 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_145, rho_145] <;> norm_num⟩

/-- **gamma at class 145, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_145`
consumed through `join50`. -/
theorem chjoin_145 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_145) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_145 (85/72 : ℝ) (115/84 : ℝ) castAB_145 hIn.1 Fresh.ChamberDatasheet.chds_145 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 145's own tuple (atom `chds_145` + proved join `inclass_145` +
`chjoin_145`). -/
theorem dead_145 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_145 s :=
  chjoin_145 rho_145 s hs h50 inclass_145

/-- jj#146 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_146 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 146 (exact rationals, the probe's own
case dump). -/
def rho_146 : Fin 5 → ℚ := ![1, 1, 73/5, 15, 84/5]

theorem castAB_146 : ((cls_146.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_146.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_146]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_146`/`cls_146` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_146 : InClass rho_146 cls_146 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_146, rho_146] <;> norm_num⟩

/-- **gamma at class 146, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_146`
consumed through `join50`. -/
theorem chjoin_146 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_146) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_146 (85/73 : ℝ) (115/84 : ℝ) castAB_146 hIn.1 Fresh.ChamberDatasheet.chds_146 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 146's own tuple (atom `chds_146` + proved join `inclass_146` +
`chjoin_146`). -/
theorem dead_146 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_146 s :=
  chjoin_146 rho_146 s hs h50 inclass_146

/-- jj#147 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/84 | D2 | 2310 cases | NO-ALIVE-ON-GRID -/
def cls_147 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 147 (exact rationals, the probe's own
case dump). -/
def rho_147 : Fin 5 → ℚ := ![1, 1, 74/5, 15, 84/5]

theorem castAB_147 : ((cls_147.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_147.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_147]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_147`/`cls_147` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_147 : InClass rho_147 cls_147 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_147, rho_147] <;> norm_num⟩

/-- **gamma at class 147, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_147`
consumed through `join50`. -/
theorem chjoin_147 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_147) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_147 (85/74 : ℝ) (115/84 : ℝ) castAB_147 hIn.1 Fresh.ChamberDatasheet.chds_147 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 147's own tuple (atom `chds_147` + proved join `inclass_147` +
`chjoin_147`). -/
theorem dead_147 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_147 s :=
  chjoin_147 rho_147 s hs h50 inclass_147

/-- jj#148 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_148 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 148 (exact rationals, the probe's own
case dump). -/
def rho_148 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 76/5]

theorem castAB_148 : ((cls_148.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_148.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_148]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_148`/`cls_148` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_148 : InClass rho_148 cls_148 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_148, rho_148] <;> norm_num⟩

/-- **gamma at class 148, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_148`
consumed through `join50`. -/
theorem chjoin_148 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_148) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_148 (85/76 : ℝ) (75/58 : ℝ) castAB_148 hIn.1 Fresh.ChamberDatasheet.chds_148 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 148's own tuple (atom `chds_148` + proved join `inclass_148` +
`chjoin_148`). -/
theorem dead_148 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_148 s :=
  chjoin_148 rho_148 s hs h50 inclass_148

/-- jj#149 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_149 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 149 (exact rationals, the probe's own
case dump). -/
def rho_149 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 77/5]

theorem castAB_149 : ((cls_149.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_149.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_149]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_149`/`cls_149` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_149 : InClass rho_149 cls_149 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_149, rho_149] <;> norm_num⟩

/-- **gamma at class 149, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_149`
consumed through `join50`. -/
theorem chjoin_149 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_149) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_149 (85/77 : ℝ) (75/58 : ℝ) castAB_149 hIn.1 Fresh.ChamberDatasheet.chds_149 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 149's own tuple (atom `chds_149` + proved join `inclass_149` +
`chjoin_149`). -/
theorem dead_149 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_149 s :=
  chjoin_149 rho_149 s hs h50 inclass_149

/-- jj#150 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_150 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 150 (exact rationals, the probe's own
case dump). -/
def rho_150 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 78/5]

theorem castAB_150 : ((cls_150.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_150.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_150]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_150`/`cls_150` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_150 : InClass rho_150 cls_150 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_150, rho_150] <;> norm_num⟩

/-- **gamma at class 150, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_150`
consumed through `join50`. -/
theorem chjoin_150 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_150) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_150 (85/78 : ℝ) (75/58 : ℝ) castAB_150 hIn.1 Fresh.ChamberDatasheet.chds_150 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 150's own tuple (atom `chds_150` + proved join `inclass_150` +
`chjoin_150`). -/
theorem dead_150 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_150 s :=
  chjoin_150 rho_150 s hs h50 inclass_150

/-- jj#151 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_151 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 151 (exact rationals, the probe's own
case dump). -/
def rho_151 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 79/5]

theorem castAB_151 : ((cls_151.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_151.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_151]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_151`/`cls_151` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_151 : InClass rho_151 cls_151 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_151, rho_151] <;> norm_num⟩

/-- **gamma at class 151, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_151`
consumed through `join50`. -/
theorem chjoin_151 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_151) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_151 (85/79 : ℝ) (75/58 : ℝ) castAB_151 hIn.1 Fresh.ChamberDatasheet.chds_151 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 151's own tuple (atom `chds_151` + proved join `inclass_151` +
`chjoin_151`). -/
theorem dead_151 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_151 s :=
  chjoin_151 rho_151 s hs h50 inclass_151

/-- jj#152 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_152 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 152 (exact rationals, the probe's own
case dump). -/
def rho_152 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 16]

theorem castAB_152 : ((cls_152.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_152.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_152]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_152`/`cls_152` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_152 : InClass rho_152 cls_152 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_152, rho_152] <;> norm_num⟩

/-- **gamma at class 152, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_152`
consumed through `join50`. -/
theorem chjoin_152 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_152) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_152 (17/16 : ℝ) (75/58 : ℝ) castAB_152 hIn.1 Fresh.ChamberDatasheet.chds_152 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 152's own tuple (atom `chds_152` + proved join `inclass_152` +
`chjoin_152`). -/
theorem dead_152 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_152 s :=
  chjoin_152 rho_152 s hs h50 inclass_152

/-- jj#153 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_153 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 153 (exact rationals, the probe's own
case dump). -/
def rho_153 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 81/5]

theorem castAB_153 : ((cls_153.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_153.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_153]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_153`/`cls_153` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_153 : InClass rho_153 cls_153 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_153, rho_153] <;> norm_num⟩

/-- **gamma at class 153, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_153`
consumed through `join50`. -/
theorem chjoin_153 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_153) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_153 (85/81 : ℝ) (75/58 : ℝ) castAB_153 hIn.1 Fresh.ChamberDatasheet.chds_153 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 153's own tuple (atom `chds_153` + proved join `inclass_153` +
`chjoin_153`). -/
theorem dead_153 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_153 s :=
  chjoin_153 rho_153 s hs h50 inclass_153

/-- jj#154 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_154 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 154 (exact rationals, the probe's own
case dump). -/
def rho_154 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 82/5]

theorem castAB_154 : ((cls_154.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_154.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_154]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_154`/`cls_154` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_154 : InClass rho_154 cls_154 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_154, rho_154] <;> norm_num⟩

/-- **gamma at class 154, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_154`
consumed through `join50`. -/
theorem chjoin_154 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_154) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_154 (85/82 : ℝ) (75/58 : ℝ) castAB_154 hIn.1 Fresh.ChamberDatasheet.chds_154 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 154's own tuple (atom `chds_154` + proved join `inclass_154` +
`chjoin_154`). -/
theorem dead_154 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_154 s :=
  chjoin_154 rho_154 s hs h50 inclass_154

/-- jj#155 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_155 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 155 (exact rationals, the probe's own
case dump). -/
def rho_155 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 83/5]

theorem castAB_155 : ((cls_155.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_155.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_155]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_155`/`cls_155` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_155 : InClass rho_155 cls_155 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_155, rho_155] <;> norm_num⟩

/-- **gamma at class 155, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_155`
consumed through `join50`. -/
theorem chjoin_155 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_155) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_155 (85/83 : ℝ) (75/58 : ℝ) castAB_155 hIn.1 Fresh.ChamberDatasheet.chds_155 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 155's own tuple (atom `chds_155` + proved join `inclass_155` +
`chjoin_155`). -/
theorem dead_155 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_155 s :=
  chjoin_155 rho_155 s hs h50 inclass_155

/-- jj#156 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/58 | D2 | 2300 cases | NO-ALIVE-ON-GRID -/
def cls_156 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 156 (exact rationals, the probe's own
case dump). -/
def rho_156 : Fin 5 → ℚ := ![1, 1, 1, 58/5, 84/5]

theorem castAB_156 : ((cls_156.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_156.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_156]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_156`/`cls_156` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_156 : InClass rho_156 cls_156 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_156, rho_156] <;> norm_num⟩

/-- **gamma at class 156, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_156`
consumed through `join50`. -/
theorem chjoin_156 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_156) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_156 (85/84 : ℝ) (75/58 : ℝ) castAB_156 hIn.1 Fresh.ChamberDatasheet.chds_156 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 156's own tuple (atom `chds_156` + proved join `inclass_156` +
`chjoin_156`). -/
theorem dead_156 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_156 s :=
  chjoin_156 rho_156 s hs h50 inclass_156

/-- jj#157 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/71 | D2 | 2299 cases | NO-ALIVE-ON-GRID -/
def cls_157 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 157 (exact rationals, the probe's own
case dump). -/
def rho_157 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 71/5]

theorem castAB_157 : ((cls_157.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_157.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_157]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_157`/`cls_157` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_157 : InClass rho_157 cls_157 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_157, rho_157] <;> norm_num⟩

/-- **gamma at class 157, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_157`
consumed through `join50`. -/
theorem chjoin_157 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_157) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_157 (85/63 : ℝ) (115/71 : ℝ) castAB_157 hIn.1 Fresh.ChamberDatasheet.chds_157 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 157's own tuple (atom `chds_157` + proved join `inclass_157` +
`chjoin_157`). -/
theorem dead_157 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_157 s :=
  chjoin_157 rho_157 s hs h50 inclass_157

/-- jj#158 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/72 | D2 | 2299 cases | NO-ALIVE-ON-GRID -/
def cls_158 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 158 (exact rationals, the probe's own
case dump). -/
def rho_158 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 72/5]

theorem castAB_158 : ((cls_158.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_158.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_158]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_158`/`cls_158` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_158 : InClass rho_158 cls_158 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_158, rho_158] <;> norm_num⟩

/-- **gamma at class 158, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_158`
consumed through `join50`. -/
theorem chjoin_158 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_158) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_158 (85/64 : ℝ) (115/72 : ℝ) castAB_158 hIn.1 Fresh.ChamberDatasheet.chds_158 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 158's own tuple (atom `chds_158` + proved join `inclass_158` +
`chjoin_158`). -/
theorem dead_158 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_158 s :=
  chjoin_158 rho_158 s hs h50 inclass_158

/-- jj#159 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/73 | D2 | 2299 cases | NO-ALIVE-ON-GRID -/
def cls_159 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 159 (exact rationals, the probe's own
case dump). -/
def rho_159 : Fin 5 → ℚ := ![1, 7, 9, 66/5, 73/5]

theorem castAB_159 : ((cls_159.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_159.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_159]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_159`/`cls_159` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_159 : InClass rho_159 cls_159 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_159, rho_159] <;> norm_num⟩

/-- **gamma at class 159, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_159`
consumed through `join50`. -/
theorem chjoin_159 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_159) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_159 (85/66 : ℝ) (115/73 : ℝ) castAB_159 hIn.1 Fresh.ChamberDatasheet.chds_159 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 159's own tuple (atom `chds_159` + proved join `inclass_159` +
`chjoin_159`). -/
theorem dead_159 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_159 s :=
  chjoin_159 rho_159 s hs h50 inclass_159

/-- jj#160 | PPS1S1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=75/44 | D1 | 2295 cases | NO-ALIVE-ON-GRID -/
def cls_160 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (75/44 : ℚ),
    lo := ![1, 1, 7, 7, 7], hi := ![7, 7, 9, 9, 9] }

/-- The recorded representative 5-tuple of class 160 (exact rationals, the probe's own
case dump). -/
def rho_160 : Fin 5 → ℚ := ![1, 1, 7, 7, 44/5]

theorem castAB_160 : ((cls_160.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_160.B : ℚ) : ℝ) = (75/44 : ℝ) := by
  norm_num [cls_160]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_160`/`cls_160` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_160 : InClass rho_160 cls_160 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_160, rho_160] <;> norm_num⟩

/-- **gamma at class 160, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_160`
consumed through `join50`. -/
theorem chjoin_160 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_160) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_160 (9/7 : ℝ) (75/44 : ℝ) castAB_160 hIn.1 Fresh.ChamberDatasheet.chds_160 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 160's own tuple (atom `chds_160` + proved join `inclass_160` +
`chjoin_160`). -/
theorem dead_160 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_160 s :=
  chjoin_160 rho_160 s hs h50 inclass_160

/-- jj#161 | PPG1S2S2 | kL=3 kR=4 | cL=G1 cR=E | a=5/3 b=31/17 | D2 | 2295 cases | NO-ALIVE-ON-GRID -/
def cls_161 : ChamberClass :=
  { kL := 3, kR := 4, A := (5/3 : ℚ), B := (31/17 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 161 (exact rationals, the probe's own
case dump). -/
def rho_161 : Fin 5 → ℚ := ![1, 28/5, 63/5, 15, 17]

theorem castAB_161 : ((cls_161.A : ℚ) : ℝ) = (5/3 : ℝ) ∧ ((cls_161.B : ℚ) : ℝ) = (31/17 : ℝ) := by
  norm_num [cls_161]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_161`/`cls_161` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_161 : InClass rho_161 cls_161 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_161, rho_161] <;> norm_num⟩

/-- **gamma at class 161, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_161`
consumed through `join50`. -/
theorem chjoin_161 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_161) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_161 (5/3 : ℝ) (31/17 : ℝ) castAB_161 hIn.1 Fresh.ChamberDatasheet.chds_161 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 161's own tuple (atom `chds_161` + proved join `inclass_161` +
`chjoin_161`). -/
theorem dead_161 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_161 s :=
  chjoin_161 rho_161 s hs h50 inclass_161

/-- jj#162 | PPG1S2E | kL=3 kR=4 | cL=G1 cR=E | a=5/3 b=31/17 | D2 | 2295 cases | NO-ALIVE-ON-GRID -/
def cls_162 : ChamberClass :=
  { kL := 3, kR := 4, A := (5/3 : ℚ), B := (31/17 : ℚ),
    lo := ![1, 1, 9, 15, 17], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 162 (exact rationals, the probe's own
case dump). -/
def rho_162 : Fin 5 → ℚ := ![1, 28/5, 63/5, 15, 17]

theorem castAB_162 : ((cls_162.A : ℚ) : ℝ) = (5/3 : ℝ) ∧ ((cls_162.B : ℚ) : ℝ) = (31/17 : ℝ) := by
  norm_num [cls_162]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_162`/`cls_162` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_162 : InClass rho_162 cls_162 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_162, rho_162] <;> norm_num⟩

/-- **gamma at class 162, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_162`
consumed through `join50`. -/
theorem chjoin_162 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_162) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_162 (5/3 : ℝ) (31/17 : ℝ) castAB_162 hIn.1 Fresh.ChamberDatasheet.chds_162 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 162's own tuple (atom `chds_162` + proved join `inclass_162` +
`chjoin_162`). -/
theorem dead_162 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_162 s :=
  chjoin_162 rho_162 s hs h50 inclass_162

/-- jj#163 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=25/19 | D2 | 2288 cases | NO-ALIVE-ON-GRID -/
def cls_163 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 163 (exact rationals, the probe's own
case dump). -/
def rho_163 : Fin 5 → ℚ := ![1, 9, 57/5, 78/5, 78/5]

theorem castAB_163 : ((cls_163.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_163.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_163]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_163`/`cls_163` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_163 : InClass rho_163 cls_163 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_163, rho_163] <;> norm_num⟩

/-- **gamma at class 163, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_163`
consumed through `join50`. -/
theorem chjoin_163 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_163) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_163 (85/78 : ℝ) (25/19 : ℝ) castAB_163 hIn.1 Fresh.ChamberDatasheet.chds_163 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 163's own tuple (atom `chds_163` + proved join `inclass_163` +
`chjoin_163`). -/
theorem dead_163 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_163 s :=
  chjoin_163 rho_163 s hs h50 inclass_163

/-- jj#164 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=3/2 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_164 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 164 (exact rationals, the probe's own
case dump). -/
def rho_164 : Fin 5 → ℚ := ![1, 1, 37/5, 9, 10]

theorem castAB_164 : ((cls_164.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_164.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_164]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_164`/`cls_164` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_164 : InClass rho_164 cls_164 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_164, rho_164] <;> norm_num⟩

/-- **gamma at class 164, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_164`
consumed through `join50`. -/
theorem chjoin_164 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_164) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_164 (45/37 : ℝ) (3/2 : ℝ) castAB_164 hIn.1 Fresh.ChamberDatasheet.chds_164 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 164's own tuple (atom `chds_164` + proved join `inclass_164` +
`chjoin_164`). -/
theorem dead_164 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_164 s :=
  chjoin_164 rho_164 s hs h50 inclass_164

/-- jj#165 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/72 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_165 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 165 (exact rationals, the probe's own
case dump). -/
def rho_165 : Fin 5 → ℚ := ![1, 1, 9, 63/5, 72/5]

theorem castAB_165 : ((cls_165.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_165.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_165]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_165`/`cls_165` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_165 : InClass rho_165 cls_165 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_165, rho_165] <;> norm_num⟩

/-- **gamma at class 165, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_165`
consumed through `join50`. -/
theorem chjoin_165 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_165) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_165 (85/63 : ℝ) (115/72 : ℝ) castAB_165 hIn.1 Fresh.ChamberDatasheet.chds_165 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 165's own tuple (atom `chds_165` + proved join `inclass_165` +
`chjoin_165`). -/
theorem dead_165 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_165 s :=
  chjoin_165 rho_165 s hs h50 inclass_165

/-- jj#166 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/73 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_166 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 166 (exact rationals, the probe's own
case dump). -/
def rho_166 : Fin 5 → ℚ := ![1, 1, 9, 13, 73/5]

theorem castAB_166 : ((cls_166.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_166.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_166]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_166`/`cls_166` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_166 : InClass rho_166 cls_166 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_166, rho_166] <;> norm_num⟩

/-- **gamma at class 166, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_166`
consumed through `join50`. -/
theorem chjoin_166 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_166) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_166 (17/13 : ℝ) (115/73 : ℝ) castAB_166 hIn.1 Fresh.ChamberDatasheet.chds_166 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 166's own tuple (atom `chds_166` + proved join `inclass_166` +
`chjoin_166`). -/
theorem dead_166 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_166 s :=
  chjoin_166 rho_166 s hs h50 inclass_166

/-- jj#167 | PS1G1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=25/17 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_167 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 167 (exact rationals, the probe's own
case dump). -/
def rho_167 : Fin 5 → ℚ := ![1, 36/5, 9, 9, 51/5]

theorem castAB_167 : ((cls_167.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_167.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_167]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_167`/`cls_167` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_167 : InClass rho_167 cls_167 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_167, rho_167] <;> norm_num⟩

/-- **gamma at class 167, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_167`
consumed through `join50`. -/
theorem chjoin_167 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_167) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_167 (5/4 : ℝ) (25/17 : ℝ) castAB_167 hIn.1 Fresh.ChamberDatasheet.chds_167 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 167's own tuple (atom `chds_167` + proved join `inclass_167` +
`chjoin_167`). -/
theorem dead_167 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_167 s :=
  chjoin_167 rho_167 s hs h50 inclass_167

/-- jj#168 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_168 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 168 (exact rationals, the probe's own
case dump). -/
def rho_168 : Fin 5 → ℚ := ![1, 9, 9, 13, 15]

theorem castAB_168 : ((cls_168.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_168.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_168]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_168`/`cls_168` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_168 : InClass rho_168 cls_168 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_168, rho_168] <;> norm_num⟩

/-- **gamma at class 168, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_168`
consumed through `join50`. -/
theorem chjoin_168 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_168) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_168 (17/13 : ℝ) (23/15 : ℝ) castAB_168 hIn.1 Fresh.ChamberDatasheet.chds_168 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 168's own tuple (atom `chds_168` + proved join `inclass_168` +
`chjoin_168`). -/
theorem dead_168 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_168 s :=
  chjoin_168 rho_168 s hs h50 inclass_168

/-- jj#169 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2280 cases | NO-ALIVE-ON-GRID -/
def cls_169 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 169 (exact rationals, the probe's own
case dump). -/
def rho_169 : Fin 5 → ℚ := ![1, 9, 9, 13, 15]

theorem castAB_169 : ((cls_169.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_169.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_169]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_169`/`cls_169` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_169 : InClass rho_169 cls_169 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_169, rho_169] <;> norm_num⟩

/-- **gamma at class 169, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_169`
consumed through `join50`. -/
theorem chjoin_169 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_169) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_169 (17/13 : ℝ) (23/15 : ℝ) castAB_169 hIn.1 Fresh.ChamberDatasheet.chds_169 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 169's own tuple (atom `chds_169` + proved join `inclass_169` +
`chjoin_169`). -/
theorem dead_169 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_169 s :=
  chjoin_169 rho_169 s hs h50 inclass_169

/-- jj#170 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/56 | D2 | 2277 cases | NO-ALIVE-ON-GRID -/
def cls_170 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 170 (exact rationals, the probe's own
case dump). -/
def rho_170 : Fin 5 → ℚ := ![1, 1, 56/5, 77/5, 77/5]

theorem castAB_170 : ((cls_170.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_170.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_170]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_170`/`cls_170` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_170 : InClass rho_170 cls_170 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_170, rho_170] <;> norm_num⟩

/-- **gamma at class 170, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_170`
consumed through `join50`. -/
theorem chjoin_170 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_170) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_170 (85/77 : ℝ) (75/56 : ℝ) castAB_170 hIn.1 Fresh.ChamberDatasheet.chds_170 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 170's own tuple (atom `chds_170` + proved join `inclass_170` +
`chjoin_170`). -/
theorem dead_170 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_170 s :=
  chjoin_170 rho_170 s hs h50 inclass_170

/-- jj#171 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=25/19 | D2 | 2277 cases | NO-ALIVE-ON-GRID -/
def cls_171 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 171 (exact rationals, the probe's own
case dump). -/
def rho_171 : Fin 5 → ℚ := ![1, 1, 57/5, 77/5, 77/5]

theorem castAB_171 : ((cls_171.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_171.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_171]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_171`/`cls_171` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_171 : InClass rho_171 cls_171 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_171, rho_171] <;> norm_num⟩

/-- **gamma at class 171, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_171`
consumed through `join50`. -/
theorem chjoin_171 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_171) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_171 (85/77 : ℝ) (25/19 : ℝ) castAB_171 hIn.1 Fresh.ChamberDatasheet.chds_171 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 171's own tuple (atom `chds_171` + proved join `inclass_171` +
`chjoin_171`). -/
theorem dead_171 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_171 s :=
  chjoin_171 rho_171 s hs h50 inclass_171

/-- jj#172 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/83 | D2 | 2268 cases | NO-ALIVE-ON-GRID -/
def cls_172 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 172 (exact rationals, the probe's own
case dump). -/
def rho_172 : Fin 5 → ℚ := ![1, 9, 74/5, 15, 83/5]

theorem castAB_172 : ((cls_172.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_172.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_172]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_172`/`cls_172` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_172 : InClass rho_172 cls_172 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_172, rho_172] <;> norm_num⟩

/-- **gamma at class 172, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_172`
consumed through `join50`. -/
theorem chjoin_172 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_172) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_172 (85/74 : ℝ) (115/83 : ℝ) castAB_172 hIn.1 Fresh.ChamberDatasheet.chds_172 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 172's own tuple (atom `chds_172` + proved join `inclass_172` +
`chjoin_172`). -/
theorem dead_172 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_172 s :=
  chjoin_172 rho_172 s hs h50 inclass_172

/-- jj#173 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/58 | D2 | 2254 cases | NO-ALIVE-ON-GRID -/
def cls_173 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 173 (exact rationals, the probe's own
case dump). -/
def rho_173 : Fin 5 → ℚ := ![1, 9, 58/5, 79/5, 79/5]

theorem castAB_173 : ((cls_173.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_173.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_173]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_173`/`cls_173` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_173 : InClass rho_173 cls_173 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_173, rho_173] <;> norm_num⟩

/-- **gamma at class 173, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_173`
consumed through `join50`. -/
theorem chjoin_173 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_173) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_173 (85/79 : ℝ) (75/58 : ℝ) castAB_173 hIn.1 Fresh.ChamberDatasheet.chds_173 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 173's own tuple (atom `chds_173` + proved join `inclass_173` +
`chjoin_173`). -/
theorem dead_173 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_173 s :=
  chjoin_173 rho_173 s hs h50 inclass_173

/-- jj#174 | PG1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2229 cases | NO-ALIVE-ON-GRID -/
def cls_174 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 174 (exact rationals, the probe's own
case dump). -/
def rho_174 : Fin 5 → ℚ := ![1, 9, 64/5, 74/5, 17]

theorem castAB_174 : ((cls_174.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_174.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_174]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_174`/`cls_174` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_174 : InClass rho_174 cls_174 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_174, rho_174] <;> norm_num⟩

/-- **gamma at class 174, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_174`
consumed through `join50`. -/
theorem chjoin_174 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_174) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_174 (25/17 : ℝ) (115/74 : ℝ) castAB_174 hIn.1 Fresh.ChamberDatasheet.chds_174 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 174's own tuple (atom `chds_174` + proved join `inclass_174` +
`chjoin_174`). -/
theorem dead_174 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_174 s :=
  chjoin_174 rho_174 s hs h50 inclass_174

/-- jj#175 | PG1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2229 cases | NO-ALIVE-ON-GRID -/
def cls_175 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 175 (exact rationals, the probe's own
case dump). -/
def rho_175 : Fin 5 → ℚ := ![1, 9, 64/5, 74/5, 17]

theorem castAB_175 : ((cls_175.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_175.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_175]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_175`/`cls_175` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_175 : InClass rho_175 cls_175 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_175, rho_175] <;> norm_num⟩

/-- **gamma at class 175, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_175`
consumed through `join50`. -/
theorem chjoin_175 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_175) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_175 (25/17 : ℝ) (115/74 : ℝ) castAB_175 hIn.1 Fresh.ChamberDatasheet.chds_175 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 175's own tuple (atom `chds_175` + proved join `inclass_175` +
`chjoin_175`). -/
theorem dead_175 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_175 s :=
  chjoin_175 rho_175 s hs h50 inclass_175

/-- jj#176 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=75/49 | D2 | 2223 cases | NO-ALIVE-ON-GRID -/
def cls_176 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 176 (exact rationals, the probe's own
case dump). -/
def rho_176 : Fin 5 → ℚ := ![1, 1, 36/5, 9, 49/5]

theorem castAB_176 : ((cls_176.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_176.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_176]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_176`/`cls_176` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_176 : InClass rho_176 cls_176 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_176, rho_176] <;> norm_num⟩

/-- **gamma at class 176, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_176`
consumed through `join50`. -/
theorem chjoin_176 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_176) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_176 (5/4 : ℝ) (75/49 : ℝ) castAB_176 hIn.1 Fresh.ChamberDatasheet.chds_176 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 176's own tuple (atom `chds_176` + proved join `inclass_176` +
`chjoin_176`). -/
theorem dead_176 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_176 s :=
  chjoin_176 rho_176 s hs h50 inclass_176

/-- jj#177 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=25/17 | D2 | 2223 cases | NO-ALIVE-ON-GRID -/
def cls_177 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 177 (exact rationals, the probe's own
case dump). -/
def rho_177 : Fin 5 → ℚ := ![1, 37/5, 37/5, 9, 51/5]

theorem castAB_177 : ((cls_177.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_177.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_177]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_177`/`cls_177` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_177 : InClass rho_177 cls_177 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_177, rho_177] <;> norm_num⟩

/-- **gamma at class 177, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_177`
consumed through `join50`. -/
theorem chjoin_177 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_177) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_177 (45/37 : ℝ) (25/17 : ℝ) castAB_177 hIn.1 Fresh.ChamberDatasheet.chds_177 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 177's own tuple (atom `chds_177` + proved join `inclass_177` +
`chjoin_177`). -/
theorem dead_177 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_177 s :=
  chjoin_177 rho_177 s hs h50 inclass_177

/-- jj#178 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/58 | D2 | 2208 cases | NO-ALIVE-ON-GRID -/
def cls_178 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 178 (exact rationals, the probe's own
case dump). -/
def rho_178 : Fin 5 → ℚ := ![1, 1, 58/5, 78/5, 78/5]

theorem castAB_178 : ((cls_178.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_178.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_178]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_178`/`cls_178` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_178 : InClass rho_178 cls_178 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_178, rho_178] <;> norm_num⟩

/-- **gamma at class 178, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_178`
consumed through `join50`. -/
theorem chjoin_178 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_178) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_178 (85/78 : ℝ) (75/58 : ℝ) castAB_178 hIn.1 Fresh.ChamberDatasheet.chds_178 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 178's own tuple (atom `chds_178` + proved join `inclass_178` +
`chjoin_178`). -/
theorem dead_178 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_178 s :=
  chjoin_178 rho_178 s hs h50 inclass_178

/-- jj#179 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_179 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 179 (exact rationals, the probe's own
case dump). -/
def rho_179 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 17]

theorem castAB_179 : ((cls_179.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_179.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_179]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_179`/`cls_179` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_179 : InClass rho_179 cls_179 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_179, rho_179] <;> norm_num⟩

/-- **gamma at class 179, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_179`
consumed through `join50`. -/
theorem chjoin_179 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_179) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_179 (85/72 : ℝ) (23/17 : ℝ) castAB_179 hIn.1 Fresh.ChamberDatasheet.chds_179 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 179's own tuple (atom `chds_179` + proved join `inclass_179` +
`chjoin_179`). -/
theorem dead_179 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_179 s :=
  chjoin_179 rho_179 s hs h50 inclass_179

/-- jj#180 | PS1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_180 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 180 (exact rationals, the probe's own
case dump). -/
def rho_180 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 17]

theorem castAB_180 : ((cls_180.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_180.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_180]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_180`/`cls_180` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_180 : InClass rho_180 cls_180 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_180, rho_180] <;> norm_num⟩

/-- **gamma at class 180, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_180`
consumed through `join50`. -/
theorem chjoin_180 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_180) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_180 (85/72 : ℝ) (23/17 : ℝ) castAB_180 hIn.1 Fresh.ChamberDatasheet.chds_180 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 180's own tuple (atom `chds_180` + proved join `inclass_180` +
`chjoin_180`). -/
theorem dead_180 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_180 s :=
  chjoin_180 rho_180 s hs h50 inclass_180

/-- jj#181 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_181 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 181 (exact rationals, the probe's own
case dump). -/
def rho_181 : Fin 5 → ℚ := ![1, 9, 9, 72/5, 83/5]

theorem castAB_181 : ((cls_181.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_181.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_181]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_181`/`cls_181` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_181 : InClass rho_181 cls_181 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_181, rho_181] <;> norm_num⟩

/-- **gamma at class 181, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_181`
consumed through `join50`. -/
theorem chjoin_181 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_181) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_181 (85/72 : ℝ) (115/83 : ℝ) castAB_181 hIn.1 Fresh.ChamberDatasheet.chds_181 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 181's own tuple (atom `chds_181` + proved join `inclass_181` +
`chjoin_181`). -/
theorem dead_181 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_181 s :=
  chjoin_181 rho_181 s hs h50 inclass_181

/-- jj#182 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_182 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 182 (exact rationals, the probe's own
case dump). -/
def rho_182 : Fin 5 → ℚ := ![1, 9, 9, 72/5, 84/5]

theorem castAB_182 : ((cls_182.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_182.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_182]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_182`/`cls_182` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_182 : InClass rho_182 cls_182 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_182, rho_182] <;> norm_num⟩

/-- **gamma at class 182, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_182`
consumed through `join50`. -/
theorem chjoin_182 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_182) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_182 (85/72 : ℝ) (115/84 : ℝ) castAB_182 hIn.1 Fresh.ChamberDatasheet.chds_182 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 182's own tuple (atom `chds_182` + proved join `inclass_182` +
`chjoin_182`). -/
theorem dead_182 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_182 s :=
  chjoin_182 rho_182 s hs h50 inclass_182

/-- jj#183 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_183 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 183 (exact rationals, the probe's own
case dump). -/
def rho_183 : Fin 5 → ℚ := ![1, 9, 9, 73/5, 17]

theorem castAB_183 : ((cls_183.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_183.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_183]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_183`/`cls_183` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_183 : InClass rho_183 cls_183 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_183, rho_183] <;> norm_num⟩

/-- **gamma at class 183, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_183`
consumed through `join50`. -/
theorem chjoin_183 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_183) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_183 (85/73 : ℝ) (23/17 : ℝ) castAB_183 hIn.1 Fresh.ChamberDatasheet.chds_183 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 183's own tuple (atom `chds_183` + proved join `inclass_183` +
`chjoin_183`). -/
theorem dead_183 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_183 s :=
  chjoin_183 rho_183 s hs h50 inclass_183

/-- jj#184 | PG1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2205 cases | NO-ALIVE-ON-GRID -/
def cls_184 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 184 (exact rationals, the probe's own
case dump). -/
def rho_184 : Fin 5 → ℚ := ![1, 9, 9, 73/5, 17]

theorem castAB_184 : ((cls_184.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_184.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_184]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_184`/`cls_184` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_184 : InClass rho_184 cls_184 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_184, rho_184] <;> norm_num⟩

/-- **gamma at class 184, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_184`
consumed through `join50`. -/
theorem chjoin_184 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_184) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_184 (85/73 : ℝ) (23/17 : ℝ) castAB_184 hIn.1 Fresh.ChamberDatasheet.chds_184 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 184's own tuple (atom `chds_184` + proved join `inclass_184` +
`chjoin_184`). -/
theorem dead_184 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_184 s :=
  chjoin_184 rho_184 s hs h50 inclass_184

/-- jj#185 | PPPS1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=75/43 | D1 | 2193 cases | NO-ALIVE-ON-GRID -/
def cls_185 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (75/43 : ℚ),
    lo := ![1, 1, 1, 7, 7], hi := ![7, 7, 7, 9, 9] }

/-- The recorded representative 5-tuple of class 185 (exact rationals, the probe's own
case dump). -/
def rho_185 : Fin 5 → ℚ := ![1, 1, 1, 7, 43/5]

theorem castAB_185 : ((cls_185.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_185.B : ℚ) : ℝ) = (75/43 : ℝ) := by
  norm_num [cls_185]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_185`/`cls_185` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_185 : InClass rho_185 cls_185 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_185, rho_185] <;> norm_num⟩

/-- **gamma at class 185, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_185`
consumed through `join50`. -/
theorem chjoin_185 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_185) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_185 (9/7 : ℝ) (75/43 : ℝ) castAB_185 hIn.1 Fresh.ChamberDatasheet.chds_185 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 185's own tuple (atom `chds_185` + proved join `inclass_185` +
`chjoin_185`). -/
theorem dead_185 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_185 s :=
  chjoin_185 rho_185 s hs h50 inclass_185

/-- jj#186 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2193 cases | NO-ALIVE-ON-GRID -/
def cls_186 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 186 (exact rationals, the probe's own
case dump). -/
def rho_186 : Fin 5 → ℚ := ![1, 7, 58/5, 74/5, 17]

theorem castAB_186 : ((cls_186.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_186.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_186]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_186`/`cls_186` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_186 : InClass rho_186 cls_186 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_186, rho_186] <;> norm_num⟩

/-- **gamma at class 186, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_186`
consumed through `join50`. -/
theorem chjoin_186 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_186) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_186 (25/17 : ℝ) (115/74 : ℝ) castAB_186 hIn.1 Fresh.ChamberDatasheet.chds_186 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 186's own tuple (atom `chds_186` + proved join `inclass_186` +
`chjoin_186`). -/
theorem dead_186 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_186 s :=
  chjoin_186 rho_186 s hs h50 inclass_186

/-- jj#187 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2193 cases | NO-ALIVE-ON-GRID -/
def cls_187 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 187 (exact rationals, the probe's own
case dump). -/
def rho_187 : Fin 5 → ℚ := ![1, 7, 58/5, 74/5, 17]

theorem castAB_187 : ((cls_187.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_187.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_187]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_187`/`cls_187` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_187 : InClass rho_187 cls_187 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_187, rho_187] <;> norm_num⟩

/-- **gamma at class 187, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_187`
consumed through `join50`. -/
theorem chjoin_187 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_187) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_187 (25/17 : ℝ) (115/74 : ℝ) castAB_187 hIn.1 Fresh.ChamberDatasheet.chds_187 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 187's own tuple (atom `chds_187` + proved join `inclass_187` +
`chjoin_187`). -/
theorem dead_187 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_187 s :=
  chjoin_187 rho_187 s hs h50 inclass_187

/-- jj#188 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2159 cases | NO-ALIVE-ON-GRID -/
def cls_188 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 188 (exact rationals, the probe's own
case dump). -/
def rho_188 : Fin 5 → ℚ := ![1, 7, 58/5, 73/5, 17]

theorem castAB_188 : ((cls_188.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_188.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_188]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_188`/`cls_188` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_188 : InClass rho_188 cls_188 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_188, rho_188] <;> norm_num⟩

/-- **gamma at class 188, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_188`
consumed through `join50`. -/
theorem chjoin_188 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_188) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_188 (25/17 : ℝ) (115/73 : ℝ) castAB_188 hIn.1 Fresh.ChamberDatasheet.chds_188 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 188's own tuple (atom `chds_188` + proved join `inclass_188` +
`chjoin_188`). -/
theorem dead_188 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_188 s :=
  chjoin_188 rho_188 s hs h50 inclass_188

/-- jj#189 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2159 cases | NO-ALIVE-ON-GRID -/
def cls_189 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 189 (exact rationals, the probe's own
case dump). -/
def rho_189 : Fin 5 → ℚ := ![1, 7, 58/5, 73/5, 17]

theorem castAB_189 : ((cls_189.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_189.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_189]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_189`/`cls_189` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_189 : InClass rho_189 cls_189 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_189, rho_189] <;> norm_num⟩

/-- **gamma at class 189, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_189`
consumed through `join50`. -/
theorem chjoin_189 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_189) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_189 (25/17 : ℝ) (115/73 : ℝ) castAB_189 hIn.1 Fresh.ChamberDatasheet.chds_189 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 189's own tuple (atom `chds_189` + proved join `inclass_189` +
`chjoin_189`). -/
theorem dead_189 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_189 s :=
  chjoin_189 rho_189 s hs h50 inclass_189

/-- jj#190 | PG1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2155 cases | NO-ALIVE-ON-GRID -/
def cls_190 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 190 (exact rationals, the probe's own
case dump). -/
def rho_190 : Fin 5 → ℚ := ![1, 9, 63/5, 73/5, 17]

theorem castAB_190 : ((cls_190.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_190.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_190]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_190`/`cls_190` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_190 : InClass rho_190 cls_190 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_190, rho_190] <;> norm_num⟩

/-- **gamma at class 190, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_190`
consumed through `join50`. -/
theorem chjoin_190 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_190) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_190 (25/17 : ℝ) (115/73 : ℝ) castAB_190 hIn.1 Fresh.ChamberDatasheet.chds_190 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 190's own tuple (atom `chds_190` + proved join `inclass_190` +
`chjoin_190`). -/
theorem dead_190 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_190 s :=
  chjoin_190 rho_190 s hs h50 inclass_190

/-- jj#191 | PG1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2155 cases | NO-ALIVE-ON-GRID -/
def cls_191 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 191 (exact rationals, the probe's own
case dump). -/
def rho_191 : Fin 5 → ℚ := ![1, 9, 63/5, 73/5, 17]

theorem castAB_191 : ((cls_191.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_191.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_191]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_191`/`cls_191` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_191 : InClass rho_191 cls_191 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_191, rho_191] <;> norm_num⟩

/-- **gamma at class 191, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_191`
consumed through `join50`. -/
theorem chjoin_191 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_191) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_191 (25/17 : ℝ) (115/73 : ℝ) castAB_191 hIn.1 Fresh.ChamberDatasheet.chds_191 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 191's own tuple (atom `chds_191` + proved join `inclass_191` +
`chjoin_191`). -/
theorem dead_191 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_191 s :=
  chjoin_191 rho_191 s hs h50 inclass_191

/-- jj#192 | PPG1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2148 cases | NO-ALIVE-ON-GRID -/
def cls_192 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 192 (exact rationals, the probe's own
case dump). -/
def rho_192 : Fin 5 → ℚ := ![1, 1, 64/5, 74/5, 17]

theorem castAB_192 : ((cls_192.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_192.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_192]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_192`/`cls_192` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_192 : InClass rho_192 cls_192 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_192, rho_192] <;> norm_num⟩

/-- **gamma at class 192, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_192`
consumed through `join50`. -/
theorem chjoin_192 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_192) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_192 (25/17 : ℝ) (115/74 : ℝ) castAB_192 hIn.1 Fresh.ChamberDatasheet.chds_192 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 192's own tuple (atom `chds_192` + proved join `inclass_192` +
`chjoin_192`). -/
theorem dead_192 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_192 s :=
  chjoin_192 rho_192 s hs h50 inclass_192

/-- jj#193 | PPG1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/74 | D2 | 2148 cases | NO-ALIVE-ON-GRID -/
def cls_193 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 193 (exact rationals, the probe's own
case dump). -/
def rho_193 : Fin 5 → ℚ := ![1, 1, 64/5, 74/5, 17]

theorem castAB_193 : ((cls_193.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_193.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_193]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_193`/`cls_193` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_193 : InClass rho_193 cls_193 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_193, rho_193] <;> norm_num⟩

/-- **gamma at class 193, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_193`
consumed through `join50`. -/
theorem chjoin_193 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_193) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_193 (25/17 : ℝ) (115/74 : ℝ) castAB_193 hIn.1 Fresh.ChamberDatasheet.chds_193 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 193's own tuple (atom `chds_193` + proved join `inclass_193` +
`chjoin_193`). -/
theorem dead_193 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_193 s :=
  chjoin_193 rho_193 s hs h50 inclass_193

/-- jj#194 | PPG1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2147 cases | NO-ALIVE-ON-GRID -/
def cls_194 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 194 (exact rationals, the probe's own
case dump). -/
def rho_194 : Fin 5 → ℚ := ![1, 1, 63/5, 73/5, 17]

theorem castAB_194 : ((cls_194.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_194.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_194]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_194`/`cls_194` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_194 : InClass rho_194 cls_194 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_194, rho_194] <;> norm_num⟩

/-- **gamma at class 194, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_194`
consumed through `join50`. -/
theorem chjoin_194 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_194) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_194 (25/17 : ℝ) (115/73 : ℝ) castAB_194 hIn.1 Fresh.ChamberDatasheet.chds_194 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 194's own tuple (atom `chds_194` + proved join `inclass_194` +
`chjoin_194`). -/
theorem dead_194 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_194 s :=
  chjoin_194 rho_194 s hs h50 inclass_194

/-- jj#195 | PPG1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/73 | D2 | 2147 cases | NO-ALIVE-ON-GRID -/
def cls_195 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 195 (exact rationals, the probe's own
case dump). -/
def rho_195 : Fin 5 → ℚ := ![1, 1, 63/5, 73/5, 17]

theorem castAB_195 : ((cls_195.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_195.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_195]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_195`/`cls_195` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_195 : InClass rho_195 cls_195 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_195, rho_195] <;> norm_num⟩

/-- **gamma at class 195, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_195`
consumed through `join50`. -/
theorem chjoin_195 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_195) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_195 (25/17 : ℝ) (115/73 : ℝ) castAB_195 hIn.1 Fresh.ChamberDatasheet.chds_195 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 195's own tuple (atom `chds_195` + proved join `inclass_195` +
`chjoin_195`). -/
theorem dead_195 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_195 s :=
  chjoin_195 rho_195 s hs h50 inclass_195

/-- jj#196 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/74 | D2 | 2139 cases | NO-ALIVE-ON-GRID -/
def cls_196 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 196 (exact rationals, the probe's own
case dump). -/
def rho_196 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 74/5]

theorem castAB_196 : ((cls_196.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_196.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_196]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_196`/`cls_196` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_196 : InClass rho_196 cls_196 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_196, rho_196] <;> norm_num⟩

/-- **gamma at class 196, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_196`
consumed through `join50`. -/
theorem chjoin_196 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_196) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_196 (85/63 : ℝ) (115/74 : ℝ) castAB_196 hIn.1 Fresh.ChamberDatasheet.chds_196 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 196's own tuple (atom `chds_196` + proved join `inclass_196` +
`chjoin_196`). -/
theorem dead_196 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_196 s :=
  chjoin_196 rho_196 s hs h50 inclass_196

/-- jj#197 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/56 | D2 | 2112 cases | NO-ALIVE-ON-GRID -/
def cls_197 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 197 (exact rationals, the probe's own
case dump). -/
def rho_197 : Fin 5 → ℚ := ![1, 9, 56/5, 78/5, 78/5]

theorem castAB_197 : ((cls_197.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_197.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_197]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_197`/`cls_197` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_197 : InClass rho_197 cls_197 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_197, rho_197] <;> norm_num⟩

/-- **gamma at class 197, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_197`
consumed through `join50`. -/
theorem chjoin_197 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_197) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_197 (85/78 : ℝ) (75/56 : ℝ) castAB_197 hIn.1 Fresh.ChamberDatasheet.chds_197 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 197's own tuple (atom `chds_197` + proved join `inclass_197` +
`chjoin_197`). -/
theorem dead_197 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_197 s :=
  chjoin_197 rho_197 s hs h50 inclass_197

/-- jj#198 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/79 | D2 | 2100 cases | NO-ALIVE-ON-GRID -/
def cls_198 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/79 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 198 (exact rationals, the probe's own
case dump). -/
def rho_198 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 79/5]

theorem castAB_198 : ((cls_198.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_198.B : ℚ) : ℝ) = (115/79 : ℝ) := by
  norm_num [cls_198]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_198`/`cls_198` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_198 : InClass rho_198 cls_198 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_198, rho_198] <;> norm_num⟩

/-- **gamma at class 198, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_198`
consumed through `join50`. -/
theorem chjoin_198 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_198) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_198 (85/73 : ℝ) (115/79 : ℝ) castAB_198 hIn.1 Fresh.ChamberDatasheet.chds_198 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 198's own tuple (atom `chds_198` + proved join `inclass_198` +
`chjoin_198`). -/
theorem dead_198 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_198 s :=
  chjoin_198 rho_198 s hs h50 inclass_198

/-- jj#199 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=23/16 | D2 | 2100 cases | NO-ALIVE-ON-GRID -/
def cls_199 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/16 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 199 (exact rationals, the probe's own
case dump). -/
def rho_199 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 16]

theorem castAB_199 : ((cls_199.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_199.B : ℚ) : ℝ) = (23/16 : ℝ) := by
  norm_num [cls_199]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_199`/`cls_199` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_199 : InClass rho_199 cls_199 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_199, rho_199] <;> norm_num⟩

/-- **gamma at class 199, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_199`
consumed through `join50`. -/
theorem chjoin_199 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_199) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_199 (85/74 : ℝ) (23/16 : ℝ) castAB_199 hIn.1 Fresh.ChamberDatasheet.chds_199 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 199's own tuple (atom `chds_199` + proved join `inclass_199` +
`chjoin_199`). -/
theorem dead_199 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_199 s :=
  chjoin_199 rho_199 s hs h50 inclass_199

/-- jj#200 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/81 | D2 | 2100 cases | NO-ALIVE-ON-GRID -/
def cls_200 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/81 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 200 (exact rationals, the probe's own
case dump). -/
def rho_200 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 81/5]

theorem castAB_200 : ((cls_200.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_200.B : ℚ) : ℝ) = (115/81 : ℝ) := by
  norm_num [cls_200]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_200`/`cls_200` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_200 : InClass rho_200 cls_200 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_200, rho_200] <;> norm_num⟩

/-- **gamma at class 200, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_200`
consumed through `join50`. -/
theorem chjoin_200 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_200) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_200 (85/74 : ℝ) (115/81 : ℝ) castAB_200 hIn.1 Fresh.ChamberDatasheet.chds_200 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 200's own tuple (atom `chds_200` + proved join `inclass_200` +
`chjoin_200`). -/
theorem dead_200 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_200 s :=
  chjoin_200 rho_200 s hs h50 inclass_200

/-- jj#201 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/73 | D2 | 2100 cases | NO-ALIVE-ON-GRID -/
def cls_201 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 201 (exact rationals, the probe's own
case dump). -/
def rho_201 : Fin 5 → ℚ := ![1, 9, 9, 63/5, 73/5]

theorem castAB_201 : ((cls_201.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_201.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_201]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_201`/`cls_201` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_201 : InClass rho_201 cls_201 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_201, rho_201] <;> norm_num⟩

/-- **gamma at class 201, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_201`
consumed through `join50`. -/
theorem chjoin_201 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_201) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_201 (85/63 : ℝ) (115/73 : ℝ) castAB_201 hIn.1 Fresh.ChamberDatasheet.chds_201 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 201's own tuple (atom `chds_201` + proved join `inclass_201` +
`chjoin_201`). -/
theorem dead_201 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_201 s :=
  chjoin_201 rho_201 s hs h50 inclass_201

/-- jj#202 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/71 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_202 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 202 (exact rationals, the probe's own
case dump). -/
def rho_202 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 71/5]

theorem castAB_202 : ((cls_202.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_202.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_202]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_202`/`cls_202` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_202 : InClass rho_202 cls_202 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_202, rho_202] <;> norm_num⟩

/-- **gamma at class 202, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_202`
consumed through `join50`. -/
theorem chjoin_202 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_202) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_202 (85/63 : ℝ) (115/71 : ℝ) castAB_202 hIn.1 Fresh.ChamberDatasheet.chds_202 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 202's own tuple (atom `chds_202` + proved join `inclass_202` +
`chjoin_202`). -/
theorem dead_202 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_202 s :=
  chjoin_202 rho_202 s hs h50 inclass_202

/-- jj#203 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/72 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_203 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 203 (exact rationals, the probe's own
case dump). -/
def rho_203 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 72/5]

theorem castAB_203 : ((cls_203.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_203.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_203]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_203`/`cls_203` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_203 : InClass rho_203 cls_203 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_203, rho_203] <;> norm_num⟩

/-- **gamma at class 203, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_203`
consumed through `join50`. -/
theorem chjoin_203 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_203) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_203 (85/63 : ℝ) (115/72 : ℝ) castAB_203 hIn.1 Fresh.ChamberDatasheet.chds_203 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 203's own tuple (atom `chds_203` + proved join `inclass_203` +
`chjoin_203`). -/
theorem dead_203 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_203 s :=
  chjoin_203 rho_203 s hs h50 inclass_203

/-- jj#204 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/71 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_204 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 204 (exact rationals, the probe's own
case dump). -/
def rho_204 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 71/5]

theorem castAB_204 : ((cls_204.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_204.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_204]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_204`/`cls_204` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_204 : InClass rho_204 cls_204 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_204, rho_204] <;> norm_num⟩

/-- **gamma at class 204, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_204`
consumed through `join50`. -/
theorem chjoin_204 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_204) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_204 (85/64 : ℝ) (115/71 : ℝ) castAB_204 hIn.1 Fresh.ChamberDatasheet.chds_204 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 204's own tuple (atom `chds_204` + proved join `inclass_204` +
`chjoin_204`). -/
theorem dead_204 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_204 s :=
  chjoin_204 rho_204 s hs h50 inclass_204

/-- jj#205 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/72 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_205 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 205 (exact rationals, the probe's own
case dump). -/
def rho_205 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 72/5]

theorem castAB_205 : ((cls_205.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_205.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_205]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_205`/`cls_205` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_205 : InClass rho_205 cls_205 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_205, rho_205] <;> norm_num⟩

/-- **gamma at class 205, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_205`
consumed through `join50`. -/
theorem chjoin_205 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_205) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_205 (85/64 : ℝ) (115/72 : ℝ) castAB_205 hIn.1 Fresh.ChamberDatasheet.chds_205 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 205's own tuple (atom `chds_205` + proved join `inclass_205` +
`chjoin_205`). -/
theorem dead_205 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_205 s :=
  chjoin_205 rho_205 s hs h50 inclass_205

/-- jj#206 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/73 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_206 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 206 (exact rationals, the probe's own
case dump). -/
def rho_206 : Fin 5 → ℚ := ![1, 1, 7, 13, 73/5]

theorem castAB_206 : ((cls_206.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_206.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_206]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_206`/`cls_206` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_206 : InClass rho_206 cls_206 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_206, rho_206] <;> norm_num⟩

/-- **gamma at class 206, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_206`
consumed through `join50`. -/
theorem chjoin_206 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_206) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_206 (17/13 : ℝ) (115/73 : ℝ) castAB_206 hIn.1 Fresh.ChamberDatasheet.chds_206 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 206's own tuple (atom `chds_206` + proved join `inclass_206` +
`chjoin_206`). -/
theorem dead_206 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_206 s :=
  chjoin_206 rho_206 s hs h50 inclass_206

/-- jj#207 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/74 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_207 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 207 (exact rationals, the probe's own
case dump). -/
def rho_207 : Fin 5 → ℚ := ![1, 1, 7, 13, 74/5]

theorem castAB_207 : ((cls_207.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_207.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_207]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_207`/`cls_207` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_207 : InClass rho_207 cls_207 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_207, rho_207] <;> norm_num⟩

/-- **gamma at class 207, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_207`
consumed through `join50`. -/
theorem chjoin_207 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_207) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_207 (17/13 : ℝ) (115/74 : ℝ) castAB_207 hIn.1 Fresh.ChamberDatasheet.chds_207 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 207's own tuple (atom `chds_207` + proved join `inclass_207` +
`chjoin_207`). -/
theorem dead_207 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_207 s :=
  chjoin_207 rho_207 s hs h50 inclass_207

/-- jj#208 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_208 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 208 (exact rationals, the probe's own
case dump). -/
def rho_208 : Fin 5 → ℚ := ![1, 1, 7, 13, 15]

theorem castAB_208 : ((cls_208.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_208.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_208]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_208`/`cls_208` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_208 : InClass rho_208 cls_208 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_208, rho_208] <;> norm_num⟩

/-- **gamma at class 208, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_208`
consumed through `join50`. -/
theorem chjoin_208 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_208) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_208 (17/13 : ℝ) (23/15 : ℝ) castAB_208 hIn.1 Fresh.ChamberDatasheet.chds_208 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 208's own tuple (atom `chds_208` + proved join `inclass_208` +
`chjoin_208`). -/
theorem dead_208 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_208 s :=
  chjoin_208 rho_208 s hs h50 inclass_208

/-- jj#209 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/73 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_209 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 209 (exact rationals, the probe's own
case dump). -/
def rho_209 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 73/5]

theorem castAB_209 : ((cls_209.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_209.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_209]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_209`/`cls_209` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_209 : InClass rho_209 cls_209 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_209, rho_209] <;> norm_num⟩

/-- **gamma at class 209, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_209`
consumed through `join50`. -/
theorem chjoin_209 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_209) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_209 (85/66 : ℝ) (115/73 : ℝ) castAB_209 hIn.1 Fresh.ChamberDatasheet.chds_209 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 209's own tuple (atom `chds_209` + proved join `inclass_209` +
`chjoin_209`). -/
theorem dead_209 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_209 s :=
  chjoin_209 rho_209 s hs h50 inclass_209

/-- jj#210 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/74 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_210 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 210 (exact rationals, the probe's own
case dump). -/
def rho_210 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 74/5]

theorem castAB_210 : ((cls_210.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_210.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_210]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_210`/`cls_210` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_210 : InClass rho_210 cls_210 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_210, rho_210] <;> norm_num⟩

/-- **gamma at class 210, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_210`
consumed through `join50`. -/
theorem chjoin_210 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_210) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_210 (85/66 : ℝ) (115/74 : ℝ) castAB_210 hIn.1 Fresh.ChamberDatasheet.chds_210 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 210's own tuple (atom `chds_210` + proved join `inclass_210` +
`chjoin_210`). -/
theorem dead_210 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_210 s :=
  chjoin_210 rho_210 s hs h50 inclass_210

/-- jj#211 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_211 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 211 (exact rationals, the probe's own
case dump). -/
def rho_211 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 15]

theorem castAB_211 : ((cls_211.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_211.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_211]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_211`/`cls_211` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_211 : InClass rho_211 cls_211 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_211, rho_211] <;> norm_num⟩

/-- **gamma at class 211, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_211`
consumed through `join50`. -/
theorem chjoin_211 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_211) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_211 (85/66 : ℝ) (23/15 : ℝ) castAB_211 hIn.1 Fresh.ChamberDatasheet.chds_211 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 211's own tuple (atom `chds_211` + proved join `inclass_211` +
`chjoin_211`). -/
theorem dead_211 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_211 s :=
  chjoin_211 rho_211 s hs h50 inclass_211

/-- jj#212 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/38 b=25/17 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_212 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/38 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 212 (exact rationals, the probe's own
case dump). -/
def rho_212 : Fin 5 → ℚ := ![1, 1, 38/5, 9, 51/5]

theorem castAB_212 : ((cls_212.A : ℚ) : ℝ) = (45/38 : ℝ) ∧ ((cls_212.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_212]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_212`/`cls_212` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_212 : InClass rho_212 cls_212 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_212, rho_212] <;> norm_num⟩

/-- **gamma at class 212, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_212`
consumed through `join50`. -/
theorem chjoin_212 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_212) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_212 (45/38 : ℝ) (25/17 : ℝ) castAB_212 hIn.1 Fresh.ChamberDatasheet.chds_212 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 212's own tuple (atom `chds_212` + proved join `inclass_212` +
`chjoin_212`). -/
theorem dead_212 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_212 s :=
  chjoin_212 rho_212 s hs h50 inclass_212

/-- jj#213 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/15 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_213 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 213 (exact rationals, the probe's own
case dump). -/
def rho_213 : Fin 5 → ℚ := ![1, 1, 7, 13, 15]

theorem castAB_213 : ((cls_213.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_213.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_213]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_213`/`cls_213` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_213 : InClass rho_213 cls_213 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_213, rho_213] <;> norm_num⟩

/-- **gamma at class 213, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_213`
consumed through `join50`. -/
theorem chjoin_213 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_213) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_213 (17/13 : ℝ) (23/15 : ℝ) castAB_213 hIn.1 Fresh.ChamberDatasheet.chds_213 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 213's own tuple (atom `chds_213` + proved join `inclass_213` +
`chjoin_213`). -/
theorem dead_213 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_213 s :=
  chjoin_213 rho_213 s hs h50 inclass_213

/-- jj#214 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_214 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 214 (exact rationals, the probe's own
case dump). -/
def rho_214 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 15]

theorem castAB_214 : ((cls_214.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_214.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_214]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_214`/`cls_214` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_214 : InClass rho_214 cls_214 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_214, rho_214] <;> norm_num⟩

/-- **gamma at class 214, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_214`
consumed through `join50`. -/
theorem chjoin_214 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_214) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_214 (85/66 : ℝ) (23/15 : ℝ) castAB_214 hIn.1 Fresh.ChamberDatasheet.chds_214 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 214's own tuple (atom `chds_214` + proved join `inclass_214` +
`chjoin_214`). -/
theorem dead_214 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_214 s :=
  chjoin_214 rho_214 s hs h50 inclass_214

/-- jj#215 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=115/71 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_215 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 215 (exact rationals, the probe's own
case dump). -/
def rho_215 : Fin 5 → ℚ := ![1, 1, 9, 63/5, 71/5]

theorem castAB_215 : ((cls_215.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_215.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_215]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_215`/`cls_215` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_215 : InClass rho_215 cls_215 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_215, rho_215] <;> norm_num⟩

/-- **gamma at class 215, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_215`
consumed through `join50`. -/
theorem chjoin_215 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_215) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_215 (85/63 : ℝ) (115/71 : ℝ) castAB_215 hIn.1 Fresh.ChamberDatasheet.chds_215 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 215's own tuple (atom `chds_215` + proved join `inclass_215` +
`chjoin_215`). -/
theorem dead_215 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_215 s :=
  chjoin_215 rho_215 s hs h50 inclass_215

/-- jj#216 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/72 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_216 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 216 (exact rationals, the probe's own
case dump). -/
def rho_216 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 72/5]

theorem castAB_216 : ((cls_216.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_216.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_216]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_216`/`cls_216` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_216 : InClass rho_216 cls_216 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_216, rho_216] <;> norm_num⟩

/-- **gamma at class 216, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_216`
consumed through `join50`. -/
theorem chjoin_216 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_216) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_216 (85/64 : ℝ) (115/72 : ℝ) castAB_216 hIn.1 Fresh.ChamberDatasheet.chds_216 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 216's own tuple (atom `chds_216` + proved join `inclass_216` +
`chjoin_216`). -/
theorem dead_216 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_216 s :=
  chjoin_216 rho_216 s hs h50 inclass_216

/-- jj#217 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/73 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_217 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 217 (exact rationals, the probe's own
case dump). -/
def rho_217 : Fin 5 → ℚ := ![1, 1, 9, 66/5, 73/5]

theorem castAB_217 : ((cls_217.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_217.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_217]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_217`/`cls_217` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_217 : InClass rho_217 cls_217 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_217, rho_217] <;> norm_num⟩

/-- **gamma at class 217, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_217`
consumed through `join50`. -/
theorem chjoin_217 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_217) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_217 (85/66 : ℝ) (115/73 : ℝ) castAB_217 hIn.1 Fresh.ChamberDatasheet.chds_217 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 217's own tuple (atom `chds_217` + proved join `inclass_217` +
`chjoin_217`). -/
theorem dead_217 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_217 s :=
  chjoin_217 rho_217 s hs h50 inclass_217

/-- jj#218 | PPG1G1S2 | kL=2 kR=2 | cL=G1 cR=G1 | a=17/15 b=25/17 | D1 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_218 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/15 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 218 (exact rationals, the probe's own
case dump). -/
def rho_218 : Fin 5 → ℚ := ![1, 1, 9, 51/5, 15]

theorem castAB_218 : ((cls_218.A : ℚ) : ℝ) = (17/15 : ℝ) ∧ ((cls_218.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_218]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_218`/`cls_218` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_218 : InClass rho_218 cls_218 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_218, rho_218] <;> norm_num⟩

/-- **gamma at class 218, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_218`
consumed through `join50`. -/
theorem chjoin_218 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_218) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_218 (17/15 : ℝ) (25/17 : ℝ) castAB_218 hIn.1 Fresh.ChamberDatasheet.chds_218 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 218's own tuple (atom `chds_218` + proved join `inclass_218` +
`chjoin_218`). -/
theorem dead_218 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_218 s :=
  chjoin_218 rho_218 s hs h50 inclass_218

/-- jj#219 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=17/14 b=115/76 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_219 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/14 : ℚ), B := (115/76 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 219 (exact rationals, the probe's own
case dump). -/
def rho_219 : Fin 5 → ℚ := ![1, 1, 9, 14, 76/5]

theorem castAB_219 : ((cls_219.A : ℚ) : ℝ) = (17/14 : ℝ) ∧ ((cls_219.B : ℚ) : ℝ) = (115/76 : ℝ) := by
  norm_num [cls_219]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_219`/`cls_219` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_219 : InClass rho_219 cls_219 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_219, rho_219] <;> norm_num⟩

/-- **gamma at class 219, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_219`
consumed through `join50`. -/
theorem chjoin_219 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_219) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_219 (17/14 : ℝ) (115/76 : ℝ) castAB_219 hIn.1 Fresh.ChamberDatasheet.chds_219 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 219's own tuple (atom `chds_219` + proved join `inclass_219` +
`chjoin_219`). -/
theorem dead_219 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_219 s :=
  chjoin_219 rho_219 s hs h50 inclass_219

/-- jj#220 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/71 b=115/77 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_220 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/71 : ℚ), B := (115/77 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 220 (exact rationals, the probe's own
case dump). -/
def rho_220 : Fin 5 → ℚ := ![1, 1, 9, 71/5, 77/5]

theorem castAB_220 : ((cls_220.A : ℚ) : ℝ) = (85/71 : ℝ) ∧ ((cls_220.B : ℚ) : ℝ) = (115/77 : ℝ) := by
  norm_num [cls_220]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_220`/`cls_220` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_220 : InClass rho_220 cls_220 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_220, rho_220] <;> norm_num⟩

/-- **gamma at class 220, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_220`
consumed through `join50`. -/
theorem chjoin_220 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_220) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_220 (85/71 : ℝ) (115/77 : ℝ) castAB_220 hIn.1 Fresh.ChamberDatasheet.chds_220 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 220's own tuple (atom `chds_220` + proved join `inclass_220` +
`chjoin_220`). -/
theorem dead_220 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_220 s :=
  chjoin_220 rho_220 s hs h50 inclass_220

/-- jj#221 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/71 | D2 | 2090 cases | NO-ALIVE-ON-GRID -/
def cls_221 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 221 (exact rationals, the probe's own
case dump). -/
def rho_221 : Fin 5 → ℚ := ![1, 7, 9, 64/5, 71/5]

theorem castAB_221 : ((cls_221.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_221.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_221]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_221`/`cls_221` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_221 : InClass rho_221 cls_221 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_221, rho_221] <;> norm_num⟩

/-- **gamma at class 221, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_221`
consumed through `join50`. -/
theorem chjoin_221 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_221) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_221 (85/64 : ℝ) (115/71 : ℝ) castAB_221 hIn.1 Fresh.ChamberDatasheet.chds_221 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 221's own tuple (atom `chds_221` + proved join `inclass_221` +
`chjoin_221`). -/
theorem dead_221 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_221 s :=
  chjoin_221 rho_221 s hs h50 inclass_221

/-- jj#222 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/82 | D2 | 2080 cases | NO-ALIVE-ON-GRID -/
def cls_222 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 222 (exact rationals, the probe's own
case dump). -/
def rho_222 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 82/5]

theorem castAB_222 : ((cls_222.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_222.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_222]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_222`/`cls_222` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_222 : InClass rho_222 cls_222 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_222, rho_222] <;> norm_num⟩

/-- **gamma at class 222, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_222`
consumed through `join50`. -/
theorem chjoin_222 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_222) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_222 (85/72 : ℝ) (115/82 : ℝ) castAB_222 hIn.1 Fresh.ChamberDatasheet.chds_222 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 222's own tuple (atom `chds_222` + proved join `inclass_222` +
`chjoin_222`). -/
theorem dead_222 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_222 s :=
  chjoin_222 rho_222 s hs h50 inclass_222

/-- jj#223 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=15/11 | D2 | 2079 cases | NO-ALIVE-ON-GRID -/
def cls_223 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 223 (exact rationals, the probe's own
case dump). -/
def rho_223 : Fin 5 → ℚ := ![1, 1, 11, 76/5, 76/5]

theorem castAB_223 : ((cls_223.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_223.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_223]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_223`/`cls_223` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_223 : InClass rho_223 cls_223 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_223, rho_223] <;> norm_num⟩

/-- **gamma at class 223, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_223`
consumed through `join50`. -/
theorem chjoin_223 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_223) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_223 (85/76 : ℝ) (15/11 : ℝ) castAB_223 hIn.1 Fresh.ChamberDatasheet.chds_223 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 223's own tuple (atom `chds_223` + proved join `inclass_223` +
`chjoin_223`). -/
theorem dead_223 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_223 s :=
  chjoin_223 rho_223 s hs h50 inclass_223

/-- jj#224 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 2079 cases | NO-ALIVE-ON-GRID -/
def cls_224 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 224 (exact rationals, the probe's own
case dump). -/
def rho_224 : Fin 5 → ℚ := ![1, 1, 72/5, 15, 83/5]

theorem castAB_224 : ((cls_224.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_224.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_224]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_224`/`cls_224` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_224 : InClass rho_224 cls_224 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_224, rho_224] <;> norm_num⟩

/-- **gamma at class 224, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_224`
consumed through `join50`. -/
theorem chjoin_224 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_224) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_224 (85/72 : ℝ) (115/83 : ℝ) castAB_224 hIn.1 Fresh.ChamberDatasheet.chds_224 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 224's own tuple (atom `chds_224` + proved join `inclass_224` +
`chjoin_224`). -/
theorem dead_224 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_224 s :=
  chjoin_224 rho_224 s hs h50 inclass_224

/-- jj#225 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 2079 cases | NO-ALIVE-ON-GRID -/
def cls_225 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 225 (exact rationals, the probe's own
case dump). -/
def rho_225 : Fin 5 → ℚ := ![1, 1, 73/5, 15, 83/5]

theorem castAB_225 : ((cls_225.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_225.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_225]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_225`/`cls_225` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_225 : InClass rho_225 cls_225 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_225, rho_225] <;> norm_num⟩

/-- **gamma at class 225, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_225`
consumed through `join50`. -/
theorem chjoin_225 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_225) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_225 (85/73 : ℝ) (115/83 : ℝ) castAB_225 hIn.1 Fresh.ChamberDatasheet.chds_225 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 225's own tuple (atom `chds_225` + proved join `inclass_225` +
`chjoin_225`). -/
theorem dead_225 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_225 s :=
  chjoin_225 rho_225 s hs h50 inclass_225

/-- jj#226 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/83 | D2 | 2079 cases | NO-ALIVE-ON-GRID -/
def cls_226 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 226 (exact rationals, the probe's own
case dump). -/
def rho_226 : Fin 5 → ℚ := ![1, 1, 74/5, 15, 83/5]

theorem castAB_226 : ((cls_226.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_226.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_226]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_226`/`cls_226` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_226 : InClass rho_226 cls_226 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_226, rho_226] <;> norm_num⟩

/-- **gamma at class 226, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_226`
consumed through `join50`. -/
theorem chjoin_226 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_226) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_226 (85/74 : ℝ) (115/83 : ℝ) castAB_226 hIn.1 Fresh.ChamberDatasheet.chds_226 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 226's own tuple (atom `chds_226` + proved join `inclass_226` +
`chjoin_226`). -/
theorem dead_226 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_226 s :=
  chjoin_226 rho_226 s hs h50 inclass_226

/-- jj#227 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=15/11 | D2 | 2079 cases | NO-ALIVE-ON-GRID -/
def cls_227 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 227 (exact rationals, the probe's own
case dump). -/
def rho_227 : Fin 5 → ℚ := ![1, 9, 11, 76/5, 76/5]

theorem castAB_227 : ((cls_227.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_227.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_227]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_227`/`cls_227` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_227 : InClass rho_227 cls_227 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_227, rho_227] <;> norm_num⟩

/-- **gamma at class 227, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_227`
consumed through `join50`. -/
theorem chjoin_227 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_227) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_227 (85/76 : ℝ) (15/11 : ℝ) castAB_227 hIn.1 Fresh.ChamberDatasheet.chds_227 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 227's own tuple (atom `chds_227` + proved join `inclass_227` +
`chjoin_227`). -/
theorem dead_227 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_227 s :=
  chjoin_227 rho_227 s hs h50 inclass_227

/-- jj#228 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 2068 cases | NO-ALIVE-ON-GRID -/
def cls_228 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 228 (exact rationals, the probe's own
case dump). -/
def rho_228 : Fin 5 → ℚ := ![1, 7, 58/5, 72/5, 17]

theorem castAB_228 : ((cls_228.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_228.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_228]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_228`/`cls_228` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_228 : InClass rho_228 cls_228 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_228, rho_228] <;> norm_num⟩

/-- **gamma at class 228, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_228`
consumed through `join50`. -/
theorem chjoin_228 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_228) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_228 (25/17 : ℝ) (115/72 : ℝ) castAB_228 hIn.1 Fresh.ChamberDatasheet.chds_228 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 228's own tuple (atom `chds_228` + proved join `inclass_228` +
`chjoin_228`). -/
theorem dead_228 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_228 s :=
  chjoin_228 rho_228 s hs h50 inclass_228

/-- jj#229 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 2068 cases | NO-ALIVE-ON-GRID -/
def cls_229 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 229 (exact rationals, the probe's own
case dump). -/
def rho_229 : Fin 5 → ℚ := ![1, 7, 58/5, 72/5, 17]

theorem castAB_229 : ((cls_229.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_229.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_229]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_229`/`cls_229` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_229 : InClass rho_229 cls_229 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_229, rho_229] <;> norm_num⟩

/-- **gamma at class 229, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_229`
consumed through `join50`. -/
theorem chjoin_229 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_229) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_229 (25/17 : ℝ) (115/72 : ℝ) castAB_229 hIn.1 Fresh.ChamberDatasheet.chds_229 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 229's own tuple (atom `chds_229` + proved join `inclass_229` +
`chjoin_229`). -/
theorem dead_229 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_229 s :=
  chjoin_229 rho_229 s hs h50 inclass_229

/-- jj#230 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/71 | D2 | 2060 cases | NO-ALIVE-ON-GRID -/
def cls_230 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 230 (exact rationals, the probe's own
case dump). -/
def rho_230 : Fin 5 → ℚ := ![1, 7, 58/5, 71/5, 17]

theorem castAB_230 : ((cls_230.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_230.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_230]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_230`/`cls_230` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_230 : InClass rho_230 cls_230 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_230, rho_230] <;> norm_num⟩

/-- **gamma at class 230, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_230`
consumed through `join50`. -/
theorem chjoin_230 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_230) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_230 (25/17 : ℝ) (115/71 : ℝ) castAB_230 hIn.1 Fresh.ChamberDatasheet.chds_230 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 230's own tuple (atom `chds_230` + proved join `inclass_230` +
`chjoin_230`). -/
theorem dead_230 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_230 s :=
  chjoin_230 rho_230 s hs h50 inclass_230

/-- jj#231 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/71 | D2 | 2060 cases | NO-ALIVE-ON-GRID -/
def cls_231 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 231 (exact rationals, the probe's own
case dump). -/
def rho_231 : Fin 5 → ℚ := ![1, 7, 58/5, 71/5, 17]

theorem castAB_231 : ((cls_231.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_231.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_231]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_231`/`cls_231` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_231 : InClass rho_231 cls_231 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_231, rho_231] <;> norm_num⟩

/-- **gamma at class 231, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_231`
consumed through `join50`. -/
theorem chjoin_231 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_231) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_231 (25/17 : ℝ) (115/71 : ℝ) castAB_231 hIn.1 Fresh.ChamberDatasheet.chds_231 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 231's own tuple (atom `chds_231` + proved join `inclass_231` +
`chjoin_231`). -/
theorem dead_231 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_231 s :=
  chjoin_231 rho_231 s hs h50 inclass_231

/-- jj#232 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 2058 cases | NO-ALIVE-ON-GRID -/
def cls_232 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 232 (exact rationals, the probe's own
case dump). -/
def rho_232 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 83/5]

theorem castAB_232 : ((cls_232.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_232.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_232]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_232`/`cls_232` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_232 : InClass rho_232 cls_232 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_232, rho_232] <;> norm_num⟩

/-- **gamma at class 232, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_232`
consumed through `join50`. -/
theorem chjoin_232 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_232) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_232 (85/72 : ℝ) (115/83 : ℝ) castAB_232 hIn.1 Fresh.ChamberDatasheet.chds_232 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 232's own tuple (atom `chds_232` + proved join `inclass_232` +
`chjoin_232`). -/
theorem dead_232 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_232 s :=
  chjoin_232 rho_232 s hs h50 inclass_232

/-- jj#233 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 2058 cases | NO-ALIVE-ON-GRID -/
def cls_233 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 233 (exact rationals, the probe's own
case dump). -/
def rho_233 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 84/5]

theorem castAB_233 : ((cls_233.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_233.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_233]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_233`/`cls_233` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_233 : InClass rho_233 cls_233 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_233, rho_233] <;> norm_num⟩

/-- **gamma at class 233, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_233`
consumed through `join50`. -/
theorem chjoin_233 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_233) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_233 (85/72 : ℝ) (115/84 : ℝ) castAB_233 hIn.1 Fresh.ChamberDatasheet.chds_233 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 233's own tuple (atom `chds_233` + proved join `inclass_233` +
`chjoin_233`). -/
theorem dead_233 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_233 s :=
  chjoin_233 rho_233 s hs h50 inclass_233

/-- jj#234 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2058 cases | NO-ALIVE-ON-GRID -/
def cls_234 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 234 (exact rationals, the probe's own
case dump). -/
def rho_234 : Fin 5 → ℚ := ![1, 39/5, 9, 73/5, 17]

theorem castAB_234 : ((cls_234.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_234.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_234]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_234`/`cls_234` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_234 : InClass rho_234 cls_234 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_234, rho_234] <;> norm_num⟩

/-- **gamma at class 234, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_234`
consumed through `join50`. -/
theorem chjoin_234 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_234) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_234 (85/73 : ℝ) (23/17 : ℝ) castAB_234 hIn.1 Fresh.ChamberDatasheet.chds_234 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 234's own tuple (atom `chds_234` + proved join `inclass_234` +
`chjoin_234`). -/
theorem dead_234 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_234 s :=
  chjoin_234 rho_234 s hs h50 inclass_234

/-- jj#235 | PS1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 2058 cases | NO-ALIVE-ON-GRID -/
def cls_235 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 235 (exact rationals, the probe's own
case dump). -/
def rho_235 : Fin 5 → ℚ := ![1, 39/5, 9, 73/5, 17]

theorem castAB_235 : ((cls_235.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_235.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_235]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_235`/`cls_235` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_235 : InClass rho_235 cls_235 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_235, rho_235] <;> norm_num⟩

/-- **gamma at class 235, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_235`
consumed through `join50`. -/
theorem chjoin_235 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_235) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_235 (85/73 : ℝ) (23/17 : ℝ) castAB_235 hIn.1 Fresh.ChamberDatasheet.chds_235 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 235's own tuple (atom `chds_235` + proved join `inclass_235` +
`chjoin_235`). -/
theorem dead_235 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_235 s :=
  chjoin_235 rho_235 s hs h50 inclass_235

/-- jj#236 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=3/2 | D2 | 2052 cases | NO-ALIVE-ON-GRID -/
def cls_236 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 236 (exact rationals, the probe's own
case dump). -/
def rho_236 : Fin 5 → ℚ := ![1, 37/5, 37/5, 9, 10]

theorem castAB_236 : ((cls_236.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_236.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_236]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_236`/`cls_236` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_236 : InClass rho_236 cls_236 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_236, rho_236] <;> norm_num⟩

/-- **gamma at class 236, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_236`
consumed through `join50`. -/
theorem chjoin_236 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_236) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_236 (45/37 : ℝ) (3/2 : ℝ) castAB_236 hIn.1 Fresh.ChamberDatasheet.chds_236 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 236's own tuple (atom `chds_236` + proved join `inclass_236` +
`chjoin_236`). -/
theorem dead_236 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_236 s :=
  chjoin_236 rho_236 s hs h50 inclass_236

/-- jj#237 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_237 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 237 (exact rationals, the probe's own
case dump). -/
def rho_237 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 76/5]

theorem castAB_237 : ((cls_237.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_237.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_237]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_237`/`cls_237` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_237 : InClass rho_237 cls_237 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_237, rho_237] <;> norm_num⟩

/-- **gamma at class 237, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_237`
consumed through `join50`. -/
theorem chjoin_237 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_237) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_237 (85/76 : ℝ) (75/56 : ℝ) castAB_237 hIn.1 Fresh.ChamberDatasheet.chds_237 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 237's own tuple (atom `chds_237` + proved join `inclass_237` +
`chjoin_237`). -/
theorem dead_237 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_237 s :=
  chjoin_237 rho_237 s hs h50 inclass_237

/-- jj#238 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_238 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 238 (exact rationals, the probe's own
case dump). -/
def rho_238 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 77/5]

theorem castAB_238 : ((cls_238.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_238.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_238]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_238`/`cls_238` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_238 : InClass rho_238 cls_238 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_238, rho_238] <;> norm_num⟩

/-- **gamma at class 238, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_238`
consumed through `join50`. -/
theorem chjoin_238 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_238) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_238 (85/77 : ℝ) (75/56 : ℝ) castAB_238 hIn.1 Fresh.ChamberDatasheet.chds_238 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 238's own tuple (atom `chds_238` + proved join `inclass_238` +
`chjoin_238`). -/
theorem dead_238 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_238 s :=
  chjoin_238 rho_238 s hs h50 inclass_238

/-- jj#239 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_239 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 239 (exact rationals, the probe's own
case dump). -/
def rho_239 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 78/5]

theorem castAB_239 : ((cls_239.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_239.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_239]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_239`/`cls_239` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_239 : InClass rho_239 cls_239 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_239, rho_239] <;> norm_num⟩

/-- **gamma at class 239, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_239`
consumed through `join50`. -/
theorem chjoin_239 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_239) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_239 (85/78 : ℝ) (75/56 : ℝ) castAB_239 hIn.1 Fresh.ChamberDatasheet.chds_239 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 239's own tuple (atom `chds_239` + proved join `inclass_239` +
`chjoin_239`). -/
theorem dead_239 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_239 s :=
  chjoin_239 rho_239 s hs h50 inclass_239

/-- jj#240 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_240 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 240 (exact rationals, the probe's own
case dump). -/
def rho_240 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 79/5]

theorem castAB_240 : ((cls_240.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_240.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_240]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_240`/`cls_240` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_240 : InClass rho_240 cls_240 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_240, rho_240] <;> norm_num⟩

/-- **gamma at class 240, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_240`
consumed through `join50`. -/
theorem chjoin_240 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_240) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_240 (85/79 : ℝ) (75/56 : ℝ) castAB_240 hIn.1 Fresh.ChamberDatasheet.chds_240 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 240's own tuple (atom `chds_240` + proved join `inclass_240` +
`chjoin_240`). -/
theorem dead_240 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_240 s :=
  chjoin_240 rho_240 s hs h50 inclass_240

/-- jj#241 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_241 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 241 (exact rationals, the probe's own
case dump). -/
def rho_241 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 16]

theorem castAB_241 : ((cls_241.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_241.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_241]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_241`/`cls_241` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_241 : InClass rho_241 cls_241 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_241, rho_241] <;> norm_num⟩

/-- **gamma at class 241, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_241`
consumed through `join50`. -/
theorem chjoin_241 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_241) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_241 (17/16 : ℝ) (75/56 : ℝ) castAB_241 hIn.1 Fresh.ChamberDatasheet.chds_241 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 241's own tuple (atom `chds_241` + proved join `inclass_241` +
`chjoin_241`). -/
theorem dead_241 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_241 s :=
  chjoin_241 rho_241 s hs h50 inclass_241

/-- jj#242 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_242 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 242 (exact rationals, the probe's own
case dump). -/
def rho_242 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 81/5]

theorem castAB_242 : ((cls_242.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_242.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_242]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_242`/`cls_242` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_242 : InClass rho_242 cls_242 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_242, rho_242] <;> norm_num⟩

/-- **gamma at class 242, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_242`
consumed through `join50`. -/
theorem chjoin_242 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_242) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_242 (85/81 : ℝ) (75/56 : ℝ) castAB_242 hIn.1 Fresh.ChamberDatasheet.chds_242 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 242's own tuple (atom `chds_242` + proved join `inclass_242` +
`chjoin_242`). -/
theorem dead_242 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_242 s :=
  chjoin_242 rho_242 s hs h50 inclass_242

/-- jj#243 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/56 | D1 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_243 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 243 (exact rationals, the probe's own
case dump). -/
def rho_243 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 82/5]

theorem castAB_243 : ((cls_243.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_243.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_243]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_243`/`cls_243` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_243 : InClass rho_243 cls_243 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_243, rho_243] <;> norm_num⟩

/-- **gamma at class 243, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_243`
consumed through `join50`. -/
theorem chjoin_243 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_243) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_243 (85/82 : ℝ) (75/56 : ℝ) castAB_243 hIn.1 Fresh.ChamberDatasheet.chds_243 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 243's own tuple (atom `chds_243` + proved join `inclass_243` +
`chjoin_243`). -/
theorem dead_243 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_243 s :=
  chjoin_243 rho_243 s hs h50 inclass_243

/-- jj#244 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/56 | D1 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_244 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 244 (exact rationals, the probe's own
case dump). -/
def rho_244 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 83/5]

theorem castAB_244 : ((cls_244.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_244.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_244]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_244`/`cls_244` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_244 : InClass rho_244 cls_244 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_244, rho_244] <;> norm_num⟩

/-- **gamma at class 244, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_244`
consumed through `join50`. -/
theorem chjoin_244 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_244) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_244 (85/83 : ℝ) (75/56 : ℝ) castAB_244 hIn.1 Fresh.ChamberDatasheet.chds_244 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 244's own tuple (atom `chds_244` + proved join `inclass_244` +
`chjoin_244`). -/
theorem dead_244 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_244 s :=
  chjoin_244 rho_244 s hs h50 inclass_244

/-- jj#245 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/56 | D1 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_245 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 245 (exact rationals, the probe's own
case dump). -/
def rho_245 : Fin 5 → ℚ := ![1, 1, 1, 56/5, 84/5]

theorem castAB_245 : ((cls_245.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_245.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_245]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_245`/`cls_245` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_245 : InClass rho_245 cls_245 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_245, rho_245] <;> norm_num⟩

/-- **gamma at class 245, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_245`
consumed through `join50`. -/
theorem chjoin_245 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_245) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_245 (85/84 : ℝ) (75/56 : ℝ) castAB_245 hIn.1 Fresh.ChamberDatasheet.chds_245 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 245's own tuple (atom `chds_245` + proved join `inclass_245` +
`chjoin_245`). -/
theorem dead_245 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_245 s :=
  chjoin_245 rho_245 s hs h50 inclass_245

/-- jj#246 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_246 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 246 (exact rationals, the probe's own
case dump). -/
def rho_246 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 76/5]

theorem castAB_246 : ((cls_246.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_246.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_246]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_246`/`cls_246` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_246 : InClass rho_246 cls_246 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_246, rho_246] <;> norm_num⟩

/-- **gamma at class 246, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_246`
consumed through `join50`. -/
theorem chjoin_246 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_246) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_246 (85/76 : ℝ) (25/19 : ℝ) castAB_246 hIn.1 Fresh.ChamberDatasheet.chds_246 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 246's own tuple (atom `chds_246` + proved join `inclass_246` +
`chjoin_246`). -/
theorem dead_246 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_246 s :=
  chjoin_246 rho_246 s hs h50 inclass_246

/-- jj#247 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_247 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 247 (exact rationals, the probe's own
case dump). -/
def rho_247 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 77/5]

theorem castAB_247 : ((cls_247.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_247.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_247]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_247`/`cls_247` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_247 : InClass rho_247 cls_247 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_247, rho_247] <;> norm_num⟩

/-- **gamma at class 247, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_247`
consumed through `join50`. -/
theorem chjoin_247 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_247) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_247 (85/77 : ℝ) (25/19 : ℝ) castAB_247 hIn.1 Fresh.ChamberDatasheet.chds_247 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 247's own tuple (atom `chds_247` + proved join `inclass_247` +
`chjoin_247`). -/
theorem dead_247 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_247 s :=
  chjoin_247 rho_247 s hs h50 inclass_247

/-- jj#248 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_248 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 248 (exact rationals, the probe's own
case dump). -/
def rho_248 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 78/5]

theorem castAB_248 : ((cls_248.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_248.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_248]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_248`/`cls_248` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_248 : InClass rho_248 cls_248 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_248, rho_248] <;> norm_num⟩

/-- **gamma at class 248, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_248`
consumed through `join50`. -/
theorem chjoin_248 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_248) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_248 (85/78 : ℝ) (25/19 : ℝ) castAB_248 hIn.1 Fresh.ChamberDatasheet.chds_248 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 248's own tuple (atom `chds_248` + proved join `inclass_248` +
`chjoin_248`). -/
theorem dead_248 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_248 s :=
  chjoin_248 rho_248 s hs h50 inclass_248

/-- jj#249 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_249 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 249 (exact rationals, the probe's own
case dump). -/
def rho_249 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 79/5]

theorem castAB_249 : ((cls_249.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_249.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_249]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_249`/`cls_249` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_249 : InClass rho_249 cls_249 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_249, rho_249] <;> norm_num⟩

/-- **gamma at class 249, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_249`
consumed through `join50`. -/
theorem chjoin_249 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_249) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_249 (85/79 : ℝ) (25/19 : ℝ) castAB_249 hIn.1 Fresh.ChamberDatasheet.chds_249 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 249's own tuple (atom `chds_249` + proved join `inclass_249` +
`chjoin_249`). -/
theorem dead_249 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_249 s :=
  chjoin_249 rho_249 s hs h50 inclass_249

/-- jj#250 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_250 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 250 (exact rationals, the probe's own
case dump). -/
def rho_250 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 16]

theorem castAB_250 : ((cls_250.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_250.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_250]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_250`/`cls_250` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_250 : InClass rho_250 cls_250 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_250, rho_250] <;> norm_num⟩

/-- **gamma at class 250, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_250`
consumed through `join50`. -/
theorem chjoin_250 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_250) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_250 (17/16 : ℝ) (25/19 : ℝ) castAB_250 hIn.1 Fresh.ChamberDatasheet.chds_250 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 250's own tuple (atom `chds_250` + proved join `inclass_250` +
`chjoin_250`). -/
theorem dead_250 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_250 s :=
  chjoin_250 rho_250 s hs h50 inclass_250

/-- jj#251 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_251 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 251 (exact rationals, the probe's own
case dump). -/
def rho_251 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 81/5]

theorem castAB_251 : ((cls_251.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_251.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_251]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_251`/`cls_251` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_251 : InClass rho_251 cls_251 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_251, rho_251] <;> norm_num⟩

/-- **gamma at class 251, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_251`
consumed through `join50`. -/
theorem chjoin_251 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_251) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_251 (85/81 : ℝ) (25/19 : ℝ) castAB_251 hIn.1 Fresh.ChamberDatasheet.chds_251 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 251's own tuple (atom `chds_251` + proved join `inclass_251` +
`chjoin_251`). -/
theorem dead_251 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_251 s :=
  chjoin_251 rho_251 s hs h50 inclass_251

/-- jj#252 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_252 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 252 (exact rationals, the probe's own
case dump). -/
def rho_252 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 82/5]

theorem castAB_252 : ((cls_252.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_252.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_252]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_252`/`cls_252` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_252 : InClass rho_252 cls_252 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_252, rho_252] <;> norm_num⟩

/-- **gamma at class 252, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_252`
consumed through `join50`. -/
theorem chjoin_252 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_252) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_252 (85/82 : ℝ) (25/19 : ℝ) castAB_252 hIn.1 Fresh.ChamberDatasheet.chds_252 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 252's own tuple (atom `chds_252` + proved join `inclass_252` +
`chjoin_252`). -/
theorem dead_252 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_252 s :=
  chjoin_252 rho_252 s hs h50 inclass_252

/-- jj#253 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_253 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 253 (exact rationals, the probe's own
case dump). -/
def rho_253 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 83/5]

theorem castAB_253 : ((cls_253.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_253.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_253]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_253`/`cls_253` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_253 : InClass rho_253 cls_253 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_253, rho_253] <;> norm_num⟩

/-- **gamma at class 253, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_253`
consumed through `join50`. -/
theorem chjoin_253 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_253) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_253 (85/83 : ℝ) (25/19 : ℝ) castAB_253 hIn.1 Fresh.ChamberDatasheet.chds_253 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 253's own tuple (atom `chds_253` + proved join `inclass_253` +
`chjoin_253`). -/
theorem dead_253 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_253 s :=
  chjoin_253 rho_253 s hs h50 inclass_253

/-- jj#254 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=25/19 | D1 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_254 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 254 (exact rationals, the probe's own
case dump). -/
def rho_254 : Fin 5 → ℚ := ![1, 1, 1, 57/5, 84/5]

theorem castAB_254 : ((cls_254.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_254.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_254]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_254`/`cls_254` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_254 : InClass rho_254 cls_254 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_254, rho_254] <;> norm_num⟩

/-- **gamma at class 254, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_254`
consumed through `join50`. -/
theorem chjoin_254 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_254) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_254 (85/84 : ℝ) (25/19 : ℝ) castAB_254 hIn.1 Fresh.ChamberDatasheet.chds_254 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 254's own tuple (atom `chds_254` + proved join `inclass_254` +
`chjoin_254`). -/
theorem dead_254 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_254 s :=
  chjoin_254 rho_254 s hs h50 inclass_254

/-- jj#255 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/56 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_255 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 255 (exact rationals, the probe's own
case dump). -/
def rho_255 : Fin 5 → ℚ := ![1, 1, 56/5, 78/5, 78/5]

theorem castAB_255 : ((cls_255.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_255.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_255]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_255`/`cls_255` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_255 : InClass rho_255 cls_255 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_255, rho_255] <;> norm_num⟩

/-- **gamma at class 255, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_255`
consumed through `join50`. -/
theorem chjoin_255 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_255) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_255 (85/78 : ℝ) (75/56 : ℝ) castAB_255 hIn.1 Fresh.ChamberDatasheet.chds_255 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 255's own tuple (atom `chds_255` + proved join `inclass_255` +
`chjoin_255`). -/
theorem dead_255 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_255 s :=
  chjoin_255 rho_255 s hs h50 inclass_255

/-- jj#256 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=25/19 | D2 | 2024 cases | NO-ALIVE-ON-GRID -/
def cls_256 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 256 (exact rationals, the probe's own
case dump). -/
def rho_256 : Fin 5 → ℚ := ![1, 1, 57/5, 78/5, 78/5]

theorem castAB_256 : ((cls_256.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_256.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_256]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_256`/`cls_256` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_256 : InClass rho_256 cls_256 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_256, rho_256] <;> norm_num⟩

/-- **gamma at class 256, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_256`
consumed through `join50`. -/
theorem chjoin_256 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_256) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_256 (85/78 : ℝ) (25/19 : ℝ) castAB_256 hIn.1 Fresh.ChamberDatasheet.chds_256 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 256's own tuple (atom `chds_256` + proved join `inclass_256` +
`chjoin_256`). -/
theorem dead_256 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_256 s :=
  chjoin_256 rho_256 s hs h50 inclass_256

/-- jj#257 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_257 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 257 (exact rationals, the probe's own
case dump). -/
def rho_257 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 76/5]

theorem castAB_257 : ((cls_257.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_257.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_257]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_257`/`cls_257` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_257 : InClass rho_257 cls_257 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_257, rho_257] <;> norm_num⟩

/-- **gamma at class 257, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_257`
consumed through `join50`. -/
theorem chjoin_257 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_257) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_257 (85/76 : ℝ) (25/19 : ℝ) castAB_257 hIn.1 Fresh.ChamberDatasheet.chds_257 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 257's own tuple (atom `chds_257` + proved join `inclass_257` +
`chjoin_257`). -/
theorem dead_257 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_257 s :=
  chjoin_257 rho_257 s hs h50 inclass_257

/-- jj#258 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_258 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 258 (exact rationals, the probe's own
case dump). -/
def rho_258 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 77/5]

theorem castAB_258 : ((cls_258.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_258.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_258]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_258`/`cls_258` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_258 : InClass rho_258 cls_258 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_258, rho_258] <;> norm_num⟩

/-- **gamma at class 258, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_258`
consumed through `join50`. -/
theorem chjoin_258 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_258) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_258 (85/77 : ℝ) (25/19 : ℝ) castAB_258 hIn.1 Fresh.ChamberDatasheet.chds_258 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 258's own tuple (atom `chds_258` + proved join `inclass_258` +
`chjoin_258`). -/
theorem dead_258 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_258 s :=
  chjoin_258 rho_258 s hs h50 inclass_258

/-- jj#259 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_259 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 259 (exact rationals, the probe's own
case dump). -/
def rho_259 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 78/5]

theorem castAB_259 : ((cls_259.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_259.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_259]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_259`/`cls_259` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_259 : InClass rho_259 cls_259 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_259, rho_259] <;> norm_num⟩

/-- **gamma at class 259, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_259`
consumed through `join50`. -/
theorem chjoin_259 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_259) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_259 (85/78 : ℝ) (25/19 : ℝ) castAB_259 hIn.1 Fresh.ChamberDatasheet.chds_259 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 259's own tuple (atom `chds_259` + proved join `inclass_259` +
`chjoin_259`). -/
theorem dead_259 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_259 s :=
  chjoin_259 rho_259 s hs h50 inclass_259

/-- jj#260 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_260 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 260 (exact rationals, the probe's own
case dump). -/
def rho_260 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 79/5]

theorem castAB_260 : ((cls_260.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_260.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_260]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_260`/`cls_260` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_260 : InClass rho_260 cls_260 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_260, rho_260] <;> norm_num⟩

/-- **gamma at class 260, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_260`
consumed through `join50`. -/
theorem chjoin_260 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_260) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_260 (85/79 : ℝ) (25/19 : ℝ) castAB_260 hIn.1 Fresh.ChamberDatasheet.chds_260 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 260's own tuple (atom `chds_260` + proved join `inclass_260` +
`chjoin_260`). -/
theorem dead_260 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_260 s :=
  chjoin_260 rho_260 s hs h50 inclass_260

/-- jj#261 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_261 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 261 (exact rationals, the probe's own
case dump). -/
def rho_261 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 16]

theorem castAB_261 : ((cls_261.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_261.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_261]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_261`/`cls_261` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_261 : InClass rho_261 cls_261 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_261, rho_261] <;> norm_num⟩

/-- **gamma at class 261, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_261`
consumed through `join50`. -/
theorem chjoin_261 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_261) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_261 (17/16 : ℝ) (25/19 : ℝ) castAB_261 hIn.1 Fresh.ChamberDatasheet.chds_261 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 261's own tuple (atom `chds_261` + proved join `inclass_261` +
`chjoin_261`). -/
theorem dead_261 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_261 s :=
  chjoin_261 rho_261 s hs h50 inclass_261

/-- jj#262 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_262 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 262 (exact rationals, the probe's own
case dump). -/
def rho_262 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 81/5]

theorem castAB_262 : ((cls_262.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_262.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_262]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_262`/`cls_262` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_262 : InClass rho_262 cls_262 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_262, rho_262] <;> norm_num⟩

/-- **gamma at class 262, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_262`
consumed through `join50`. -/
theorem chjoin_262 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_262) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_262 (85/81 : ℝ) (25/19 : ℝ) castAB_262 hIn.1 Fresh.ChamberDatasheet.chds_262 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 262's own tuple (atom `chds_262` + proved join `inclass_262` +
`chjoin_262`). -/
theorem dead_262 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_262 s :=
  chjoin_262 rho_262 s hs h50 inclass_262

/-- jj#263 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_263 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 263 (exact rationals, the probe's own
case dump). -/
def rho_263 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 82/5]

theorem castAB_263 : ((cls_263.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_263.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_263]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_263`/`cls_263` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_263 : InClass rho_263 cls_263 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_263, rho_263] <;> norm_num⟩

/-- **gamma at class 263, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_263`
consumed through `join50`. -/
theorem chjoin_263 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_263) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_263 (85/82 : ℝ) (25/19 : ℝ) castAB_263 hIn.1 Fresh.ChamberDatasheet.chds_263 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 263's own tuple (atom `chds_263` + proved join `inclass_263` +
`chjoin_263`). -/
theorem dead_263 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_263 s :=
  chjoin_263 rho_263 s hs h50 inclass_263

/-- jj#264 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_264 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 264 (exact rationals, the probe's own
case dump). -/
def rho_264 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 83/5]

theorem castAB_264 : ((cls_264.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_264.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_264]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_264`/`cls_264` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_264 : InClass rho_264 cls_264 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_264, rho_264] <;> norm_num⟩

/-- **gamma at class 264, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_264`
consumed through `join50`. -/
theorem chjoin_264 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_264) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_264 (85/83 : ℝ) (25/19 : ℝ) castAB_264 hIn.1 Fresh.ChamberDatasheet.chds_264 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 264's own tuple (atom `chds_264` + proved join `inclass_264` +
`chjoin_264`). -/
theorem dead_264 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_264 s :=
  chjoin_264 rho_264 s hs h50 inclass_264

/-- jj#265 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=25/19 | D1 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_265 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 265 (exact rationals, the probe's own
case dump). -/
def rho_265 : Fin 5 → ℚ := ![1, 9, 9, 57/5, 84/5]

theorem castAB_265 : ((cls_265.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_265.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_265]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_265`/`cls_265` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_265 : InClass rho_265 cls_265 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_265, rho_265] <;> norm_num⟩

/-- **gamma at class 265, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_265`
consumed through `join50`. -/
theorem chjoin_265 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_265) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_265 (85/84 : ℝ) (25/19 : ℝ) castAB_265 hIn.1 Fresh.ChamberDatasheet.chds_265 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 265's own tuple (atom `chds_265` + proved join `inclass_265` +
`chjoin_265`). -/
theorem dead_265 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_265 s :=
  chjoin_265 rho_265 s hs h50 inclass_265

/-- jj#266 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=25/19 | D2 | 2002 cases | NO-ALIVE-ON-GRID -/
def cls_266 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 266 (exact rationals, the probe's own
case dump). -/
def rho_266 : Fin 5 → ℚ := ![1, 9, 57/5, 79/5, 79/5]

theorem castAB_266 : ((cls_266.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_266.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_266]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_266`/`cls_266` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_266 : InClass rho_266 cls_266 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_266, rho_266] <;> norm_num⟩

/-- **gamma at class 266, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_266`
consumed through `join50`. -/
theorem chjoin_266 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_266) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_266 (85/79 : ℝ) (25/19 : ℝ) castAB_266 hIn.1 Fresh.ChamberDatasheet.chds_266 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 266's own tuple (atom `chds_266` + proved join `inclass_266` +
`chjoin_266`). -/
theorem dead_266 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_266 s :=
  chjoin_266 rho_266 s hs h50 inclass_266

/-- jj#267 | PS1G1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=3/2 | D2 | 1995 cases | NO-ALIVE-ON-GRID -/
def cls_267 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 267 (exact rationals, the probe's own
case dump). -/
def rho_267 : Fin 5 → ℚ := ![1, 36/5, 9, 9, 10]

theorem castAB_267 : ((cls_267.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_267.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_267]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_267`/`cls_267` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_267 : InClass rho_267 cls_267 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_267, rho_267] <;> norm_num⟩

/-- **gamma at class 267, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_267`
consumed through `join50`. -/
theorem chjoin_267 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_267) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_267 (5/4 : ℝ) (3/2 : ℝ) castAB_267 hIn.1 Fresh.ChamberDatasheet.chds_267 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 267's own tuple (atom `chds_267` + proved join `inclass_267` +
`chjoin_267`). -/
theorem dead_267 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_267 s :=
  chjoin_267 rho_267 s hs h50 inclass_267

/-- jj#268 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/74 | D2 | 1995 cases | NO-ALIVE-ON-GRID -/
def cls_268 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 268 (exact rationals, the probe's own
case dump). -/
def rho_268 : Fin 5 → ℚ := ![1, 9, 9, 13, 74/5]

theorem castAB_268 : ((cls_268.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_268.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_268]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_268`/`cls_268` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_268 : InClass rho_268 cls_268 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_268, rho_268] <;> norm_num⟩

/-- **gamma at class 268, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_268`
consumed through `join50`. -/
theorem chjoin_268 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_268) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_268 (17/13 : ℝ) (115/74 : ℝ) castAB_268 hIn.1 Fresh.ChamberDatasheet.chds_268 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 268's own tuple (atom `chds_268` + proved join `inclass_268` +
`chjoin_268`). -/
theorem dead_268 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_268 s :=
  chjoin_268 rho_268 s hs h50 inclass_268

/-- jj#269 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 1995 cases | NO-ALIVE-ON-GRID -/
def cls_269 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 269 (exact rationals, the probe's own
case dump). -/
def rho_269 : Fin 5 → ℚ := ![1, 9, 9, 66/5, 15]

theorem castAB_269 : ((cls_269.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_269.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_269]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_269`/`cls_269` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_269 : InClass rho_269 cls_269 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_269, rho_269] <;> norm_num⟩

/-- **gamma at class 269, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_269`
consumed through `join50`. -/
theorem chjoin_269 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_269) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_269 (85/66 : ℝ) (23/15 : ℝ) castAB_269 hIn.1 Fresh.ChamberDatasheet.chds_269 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 269's own tuple (atom `chds_269` + proved join `inclass_269` +
`chjoin_269`). -/
theorem dead_269 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_269 s :=
  chjoin_269 rho_269 s hs h50 inclass_269

/-- jj#270 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/15 | D2 | 1995 cases | NO-ALIVE-ON-GRID -/
def cls_270 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/15 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 270 (exact rationals, the probe's own
case dump). -/
def rho_270 : Fin 5 → ℚ := ![1, 9, 9, 66/5, 15]

theorem castAB_270 : ((cls_270.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_270.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_270]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_270`/`cls_270` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_270 : InClass rho_270 cls_270 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_270, rho_270] <;> norm_num⟩

/-- **gamma at class 270, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_270`
consumed through `join50`. -/
theorem chjoin_270 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_270) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_270 (85/66 : ℝ) (23/15 : ℝ) castAB_270 hIn.1 Fresh.ChamberDatasheet.chds_270 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 270's own tuple (atom `chds_270` + proved join `inclass_270` +
`chjoin_270`). -/
theorem dead_270 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_270 s :=
  chjoin_270 rho_270 s hs h50 inclass_270

/-- jj#271 | PPS1S1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=75/43 | D1 | 1989 cases | NO-ALIVE-ON-GRID -/
def cls_271 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (75/43 : ℚ),
    lo := ![1, 1, 7, 7, 7], hi := ![7, 7, 9, 9, 9] }

/-- The recorded representative 5-tuple of class 271 (exact rationals, the probe's own
case dump). -/
def rho_271 : Fin 5 → ℚ := ![1, 1, 7, 7, 43/5]

theorem castAB_271 : ((cls_271.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_271.B : ℚ) : ℝ) = (75/43 : ℝ) := by
  norm_num [cls_271]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_271`/`cls_271` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_271 : InClass rho_271 cls_271 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_271, rho_271] <;> norm_num⟩

/-- **gamma at class 271, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_271`
consumed through `join50`. -/
theorem chjoin_271 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_271) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_271 (9/7 : ℝ) (75/43 : ℝ) castAB_271 hIn.1 Fresh.ChamberDatasheet.chds_271 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 271's own tuple (atom `chds_271` + proved join `inclass_271` +
`chjoin_271`). -/
theorem dead_271 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_271 s :=
  chjoin_271 rho_271 s hs h50 inclass_271

/-- jj#272 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/72 | D2 | 1980 cases | NO-ALIVE-ON-GRID -/
def cls_272 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 272 (exact rationals, the probe's own
case dump). -/
def rho_272 : Fin 5 → ℚ := ![1, 7, 9, 13, 72/5]

theorem castAB_272 : ((cls_272.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_272.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_272]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_272`/`cls_272` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_272 : InClass rho_272 cls_272 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_272, rho_272] <;> norm_num⟩

/-- **gamma at class 272, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_272`
consumed through `join50`. -/
theorem chjoin_272 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_272) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_272 (17/13 : ℝ) (115/72 : ℝ) castAB_272 hIn.1 Fresh.ChamberDatasheet.chds_272 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 272's own tuple (atom `chds_272` + proved join `inclass_272` +
`chjoin_272`). -/
theorem dead_272 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_272 s :=
  chjoin_272 rho_272 s hs h50 inclass_272

/-- jj#273 | PPS1G1S2 | kL=2 kR=4 | cL=G1 cR=S2 | a=17/9 b=155/77 | D2 | 1977 cases | NO-ALIVE-ON-GRID -/
def cls_273 : ChamberClass :=
  { kL := 2, kR := 4, A := (17/9 : ℚ), B := (155/77 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 273 (exact rationals, the probe's own
case dump). -/
def rho_273 : Fin 5 → ℚ := ![1, 26/5, 7, 9, 77/5]

theorem castAB_273 : ((cls_273.A : ℚ) : ℝ) = (17/9 : ℝ) ∧ ((cls_273.B : ℚ) : ℝ) = (155/77 : ℝ) := by
  norm_num [cls_273]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_273`/`cls_273` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_273 : InClass rho_273 cls_273 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_273, rho_273] <;> norm_num⟩

/-- **gamma at class 273, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_273`
consumed through `join50`. -/
theorem chjoin_273 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_273) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_273 (17/9 : ℝ) (155/77 : ℝ) castAB_273 hIn.1 Fresh.ChamberDatasheet.chds_273 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 273's own tuple (atom `chds_273` + proved join `inclass_273` +
`chjoin_273`). -/
theorem dead_273 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_273 s :=
  chjoin_273 rho_273 s hs h50 inclass_273

/-- jj#274 | PPG1S2S2 | kL=3 kR=4 | cL=G1 cR=S2 | a=5/3 b=155/84 | D2 | 1964 cases | NO-ALIVE-ON-GRID -/
def cls_274 : ChamberClass :=
  { kL := 3, kR := 4, A := (5/3 : ℚ), B := (155/84 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 274 (exact rationals, the probe's own
case dump). -/
def rho_274 : Fin 5 → ℚ := ![1, 6, 52/5, 15, 84/5]

theorem castAB_274 : ((cls_274.A : ℚ) : ℝ) = (5/3 : ℝ) ∧ ((cls_274.B : ℚ) : ℝ) = (155/84 : ℝ) := by
  norm_num [cls_274]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_274`/`cls_274` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_274 : InClass rho_274 cls_274 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_274, rho_274] <;> norm_num⟩

/-- **gamma at class 274, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_274`
consumed through `join50`. -/
theorem chjoin_274 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_274) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_274 (5/3 : ℝ) (155/84 : ℝ) castAB_274 hIn.1 Fresh.ChamberDatasheet.chds_274 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 274's own tuple (atom `chds_274` + proved join `inclass_274` +
`chjoin_274`). -/
theorem dead_274 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_274 s :=
  chjoin_274 rho_274 s hs h50 inclass_274

/-- jj#275 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=23/14 | D2 | 1948 cases | NO-ALIVE-ON-GRID -/
def cls_275 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 275 (exact rationals, the probe's own
case dump). -/
def rho_275 : Fin 5 → ℚ := ![1, 7, 58/5, 14, 17]

theorem castAB_275 : ((cls_275.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_275.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_275]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_275`/`cls_275` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_275 : InClass rho_275 cls_275 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_275, rho_275] <;> norm_num⟩

/-- **gamma at class 275, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_275`
consumed through `join50`. -/
theorem chjoin_275 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_275) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_275 (25/17 : ℝ) (23/14 : ℝ) castAB_275 hIn.1 Fresh.ChamberDatasheet.chds_275 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 275's own tuple (atom `chds_275` + proved join `inclass_275` +
`chjoin_275`). -/
theorem dead_275 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_275 s :=
  chjoin_275 rho_275 s hs h50 inclass_275

/-- jj#276 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=23/14 | D2 | 1948 cases | NO-ALIVE-ON-GRID -/
def cls_276 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 276 (exact rationals, the probe's own
case dump). -/
def rho_276 : Fin 5 → ℚ := ![1, 7, 58/5, 14, 17]

theorem castAB_276 : ((cls_276.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_276.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_276]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_276`/`cls_276` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_276 : InClass rho_276 cls_276 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_276, rho_276] <;> norm_num⟩

/-- **gamma at class 276, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_276`
consumed through `join50`. -/
theorem chjoin_276 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_276) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_276 (25/17 : ℝ) (23/14 : ℝ) castAB_276 hIn.1 Fresh.ChamberDatasheet.chds_276 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 276's own tuple (atom `chds_276` + proved join `inclass_276` +
`chjoin_276`). -/
theorem dead_276 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_276 s :=
  chjoin_276 rho_276 s hs h50 inclass_276

/-- jj#277 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/14 | D2 | 1937 cases | NO-ALIVE-ON-GRID -/
def cls_277 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 277 (exact rationals, the probe's own
case dump). -/
def rho_277 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 14]

theorem castAB_277 : ((cls_277.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_277.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_277]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_277`/`cls_277` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_277 : InClass rho_277 cls_277 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_277, rho_277] <;> norm_num⟩

/-- **gamma at class 277, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_277`
consumed through `join50`. -/
theorem chjoin_277 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_277) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_277 (85/63 : ℝ) (23/14 : ℝ) castAB_277 hIn.1 Fresh.ChamberDatasheet.chds_277 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 277's own tuple (atom `chds_277` + proved join `inclass_277` +
`chjoin_277`). -/
theorem dead_277 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_277 s :=
  chjoin_277 rho_277 s hs h50 inclass_277

/-- jj#278 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=23/14 | D2 | 1937 cases | NO-ALIVE-ON-GRID -/
def cls_278 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 278 (exact rationals, the probe's own
case dump). -/
def rho_278 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 14]

theorem castAB_278 : ((cls_278.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_278.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_278]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_278`/`cls_278` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_278 : InClass rho_278 cls_278 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_278, rho_278] <;> norm_num⟩

/-- **gamma at class 278, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_278`
consumed through `join50`. -/
theorem chjoin_278 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_278) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_278 (85/64 : ℝ) (23/14 : ℝ) castAB_278 hIn.1 Fresh.ChamberDatasheet.chds_278 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 278's own tuple (atom `chds_278` + proved join `inclass_278` +
`chjoin_278`). -/
theorem dead_278 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_278 s :=
  chjoin_278 rho_278 s hs h50 inclass_278

/-- jj#279 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/58 | D2 | 1932 cases | NO-ALIVE-ON-GRID -/
def cls_279 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 279 (exact rationals, the probe's own
case dump). -/
def rho_279 : Fin 5 → ℚ := ![1, 1, 58/5, 79/5, 79/5]

theorem castAB_279 : ((cls_279.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_279.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_279]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_279`/`cls_279` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_279 : InClass rho_279 cls_279 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_279, rho_279] <;> norm_num⟩

/-- **gamma at class 279, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_279`
consumed through `join50`. -/
theorem chjoin_279 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_279) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_279 (85/79 : ℝ) (75/58 : ℝ) castAB_279 hIn.1 Fresh.ChamberDatasheet.chds_279 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 279's own tuple (atom `chds_279` + proved join `inclass_279` +
`chjoin_279`). -/
theorem dead_279 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_279 s :=
  chjoin_279 rho_279 s hs h50 inclass_279

/-- jj#280 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/58 | D2 | 1932 cases | NO-ALIVE-ON-GRID -/
def cls_280 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 280 (exact rationals, the probe's own
case dump). -/
def rho_280 : Fin 5 → ℚ := ![1, 9, 58/5, 16, 16]

theorem castAB_280 : ((cls_280.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_280.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_280]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_280`/`cls_280` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_280 : InClass rho_280 cls_280 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_280, rho_280] <;> norm_num⟩

/-- **gamma at class 280, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_280`
consumed through `join50`. -/
theorem chjoin_280 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_280) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_280 (17/16 : ℝ) (75/58 : ℝ) castAB_280 hIn.1 Fresh.ChamberDatasheet.chds_280 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 280's own tuple (atom `chds_280` + proved join `inclass_280` +
`chjoin_280`). -/
theorem dead_280 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_280 s :=
  chjoin_280 rho_280 s hs h50 inclass_280

/-- jj#281 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/82 | D2 | 1920 cases | NO-ALIVE-ON-GRID -/
def cls_281 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 281 (exact rationals, the probe's own
case dump). -/
def rho_281 : Fin 5 → ℚ := ![1, 9, 73/5, 15, 82/5]

theorem castAB_281 : ((cls_281.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_281.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_281]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_281`/`cls_281` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_281 : InClass rho_281 cls_281 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_281, rho_281] <;> norm_num⟩

/-- **gamma at class 281, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_281`
consumed through `join50`. -/
theorem chjoin_281 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_281) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_281 (85/73 : ℝ) (115/82 : ℝ) castAB_281 hIn.1 Fresh.ChamberDatasheet.chds_281 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 281's own tuple (atom `chds_281` + proved join `inclass_281` +
`chjoin_281`). -/
theorem dead_281 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_281 s :=
  chjoin_281 rho_281 s hs h50 inclass_281

/-- jj#282 | PPG1S2S2 | kL=3 kR=4 | cL=G1 cR=S2 | a=5/3 b=155/83 | D2 | 1913 cases | NO-ALIVE-ON-GRID -/
def cls_282 : ChamberClass :=
  { kL := 3, kR := 4, A := (5/3 : ℚ), B := (155/83 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 282 (exact rationals, the probe's own
case dump). -/
def rho_282 : Fin 5 → ℚ := ![1, 6, 52/5, 15, 83/5]

theorem castAB_282 : ((cls_282.A : ℚ) : ℝ) = (5/3 : ℝ) ∧ ((cls_282.B : ℚ) : ℝ) = (155/83 : ℝ) := by
  norm_num [cls_282]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_282`/`cls_282` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_282 : InClass rho_282 cls_282 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_282, rho_282] <;> norm_num⟩

/-- **gamma at class 282, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_282`
consumed through `join50`. -/
theorem chjoin_282 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_282) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_282 (5/3 : ℝ) (155/83 : ℝ) castAB_282 hIn.1 Fresh.ChamberDatasheet.chds_282 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 282's own tuple (atom `chds_282` + proved join `inclass_282` +
`chjoin_282`). -/
theorem dead_282 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_282 s :=
  chjoin_282 rho_282 s hs h50 inclass_282

/-- jj#283 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_283 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 283 (exact rationals, the probe's own
case dump). -/
def rho_283 : Fin 5 → ℚ := ![1, 39/5, 9, 73/5, 83/5]

theorem castAB_283 : ((cls_283.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_283.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_283]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_283`/`cls_283` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_283 : InClass rho_283 cls_283 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_283, rho_283] <;> norm_num⟩

/-- **gamma at class 283, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_283`
consumed through `join50`. -/
theorem chjoin_283 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_283) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_283 (85/73 : ℝ) (115/83 : ℝ) castAB_283 hIn.1 Fresh.ChamberDatasheet.chds_283 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 283's own tuple (atom `chds_283` + proved join `inclass_283` +
`chjoin_283`). -/
theorem dead_283 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_283 s :=
  chjoin_283 rho_283 s hs h50 inclass_283

/-- jj#284 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_284 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 284 (exact rationals, the probe's own
case dump). -/
def rho_284 : Fin 5 → ℚ := ![1, 39/5, 9, 73/5, 84/5]

theorem castAB_284 : ((cls_284.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_284.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_284]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_284`/`cls_284` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_284 : InClass rho_284 cls_284 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_284, rho_284] <;> norm_num⟩

/-- **gamma at class 284, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_284`
consumed through `join50`. -/
theorem chjoin_284 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_284) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_284 (85/73 : ℝ) (115/84 : ℝ) castAB_284 hIn.1 Fresh.ChamberDatasheet.chds_284 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 284's own tuple (atom `chds_284` + proved join `inclass_284` +
`chjoin_284`). -/
theorem dead_284 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_284 s :=
  chjoin_284 rho_284 s hs h50 inclass_284

/-- jj#285 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_285 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 285 (exact rationals, the probe's own
case dump). -/
def rho_285 : Fin 5 → ℚ := ![1, 9, 9, 73/5, 83/5]

theorem castAB_285 : ((cls_285.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_285.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_285]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_285`/`cls_285` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_285 : InClass rho_285 cls_285 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_285, rho_285] <;> norm_num⟩

/-- **gamma at class 285, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_285`
consumed through `join50`. -/
theorem chjoin_285 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_285) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_285 (85/73 : ℝ) (115/83 : ℝ) castAB_285 hIn.1 Fresh.ChamberDatasheet.chds_285 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 285's own tuple (atom `chds_285` + proved join `inclass_285` +
`chjoin_285`). -/
theorem dead_285 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_285 s :=
  chjoin_285 rho_285 s hs h50 inclass_285

/-- jj#286 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_286 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 286 (exact rationals, the probe's own
case dump). -/
def rho_286 : Fin 5 → ℚ := ![1, 9, 9, 73/5, 84/5]

theorem castAB_286 : ((cls_286.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_286.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_286]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_286`/`cls_286` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_286 : InClass rho_286 cls_286 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_286, rho_286] <;> norm_num⟩

/-- **gamma at class 286, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_286`
consumed through `join50`. -/
theorem chjoin_286 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_286) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_286 (85/73 : ℝ) (115/84 : ℝ) castAB_286 hIn.1 Fresh.ChamberDatasheet.chds_286 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 286's own tuple (atom `chds_286` + proved join `inclass_286` +
`chjoin_286`). -/
theorem dead_286 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_286 s :=
  chjoin_286 rho_286 s hs h50 inclass_286

/-- jj#287 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_287 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 287 (exact rationals, the probe's own
case dump). -/
def rho_287 : Fin 5 → ℚ := ![1, 9, 9, 74/5, 17]

theorem castAB_287 : ((cls_287.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_287.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_287]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_287`/`cls_287` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_287 : InClass rho_287 cls_287 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_287, rho_287] <;> norm_num⟩

/-- **gamma at class 287, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_287`
consumed through `join50`. -/
theorem chjoin_287 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_287) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_287 (85/74 : ℝ) (23/17 : ℝ) castAB_287 hIn.1 Fresh.ChamberDatasheet.chds_287 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 287's own tuple (atom `chds_287` + proved join `inclass_287` +
`chjoin_287`). -/
theorem dead_287 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_287 s :=
  chjoin_287 rho_287 s hs h50 inclass_287

/-- jj#288 | PG1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1911 cases | NO-ALIVE-ON-GRID -/
def cls_288 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 288 (exact rationals, the probe's own
case dump). -/
def rho_288 : Fin 5 → ℚ := ![1, 9, 9, 74/5, 17]

theorem castAB_288 : ((cls_288.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_288.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_288]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_288`/`cls_288` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_288 : InClass rho_288 cls_288 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_288, rho_288] <;> norm_num⟩

/-- **gamma at class 288, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_288`
consumed through `join50`. -/
theorem chjoin_288 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_288) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_288 (85/74 : ℝ) (23/17 : ℝ) castAB_288 hIn.1 Fresh.ChamberDatasheet.chds_288 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 288's own tuple (atom `chds_288` + proved join `inclass_288` +
`chjoin_288`). -/
theorem dead_288 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_288 s :=
  chjoin_288 rho_288 s hs h50 inclass_288

/-- jj#289 | PPS1S1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=3/2 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_289 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 7, 7, 9], hi := ![7, 7, 9, 9, 15] }

/-- The recorded representative 5-tuple of class 289 (exact rationals, the probe's own
case dump). -/
def rho_289 : Fin 5 → ℚ := ![1, 1, 36/5, 36/5, 10]

theorem castAB_289 : ((cls_289.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_289.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_289]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_289`/`cls_289` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_289 : InClass rho_289 cls_289 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_289, rho_289] <;> norm_num⟩

/-- **gamma at class 289, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_289`
consumed through `join50`. -/
theorem chjoin_289 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_289) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_289 (5/4 : ℝ) (3/2 : ℝ) castAB_289 hIn.1 Fresh.ChamberDatasheet.chds_289 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 289's own tuple (atom `chds_289` + proved join `inclass_289` +
`chjoin_289`). -/
theorem dead_289 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_289 s :=
  chjoin_289 rho_289 s hs h50 inclass_289

/-- jj#290 | PPS1S1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=25/17 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_290 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 7, 9], hi := ![7, 7, 9, 9, 15] }

/-- The recorded representative 5-tuple of class 290 (exact rationals, the probe's own
case dump). -/
def rho_290 : Fin 5 → ℚ := ![1, 1, 36/5, 36/5, 51/5]

theorem castAB_290 : ((cls_290.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_290.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_290]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_290`/`cls_290` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_290 : InClass rho_290 cls_290 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_290, rho_290] <;> norm_num⟩

/-- **gamma at class 290, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_290`
consumed through `join50`. -/
theorem chjoin_290 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_290) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_290 (5/4 : ℝ) (25/17 : ℝ) castAB_290 hIn.1 Fresh.ChamberDatasheet.chds_290 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 290's own tuple (atom `chds_290` + proved join `inclass_290` +
`chjoin_290`). -/
theorem dead_290 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_290 s :=
  chjoin_290 rho_290 s hs h50 inclass_290

/-- jj#291 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/38 b=3/2 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_291 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/38 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 291 (exact rationals, the probe's own
case dump). -/
def rho_291 : Fin 5 → ℚ := ![1, 1, 38/5, 9, 10]

theorem castAB_291 : ((cls_291.A : ℚ) : ℝ) = (45/38 : ℝ) ∧ ((cls_291.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_291]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_291`/`cls_291` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_291 : InClass rho_291 cls_291 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_291, rho_291] <;> norm_num⟩

/-- **gamma at class 291, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_291`
consumed through `join50`. -/
theorem chjoin_291 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_291) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_291 (45/38 : ℝ) (3/2 : ℝ) castAB_291 hIn.1 Fresh.ChamberDatasheet.chds_291 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 291's own tuple (atom `chds_291` + proved join `inclass_291` +
`chjoin_291`). -/
theorem dead_291 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_291 s :=
  chjoin_291 rho_291 s hs h50 inclass_291

/-- jj#292 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/71 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_292 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 292 (exact rationals, the probe's own
case dump). -/
def rho_292 : Fin 5 → ℚ := ![1, 1, 9, 64/5, 71/5]

theorem castAB_292 : ((cls_292.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_292.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_292]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_292`/`cls_292` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_292 : InClass rho_292 cls_292 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_292, rho_292] <;> norm_num⟩

/-- **gamma at class 292, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_292`
consumed through `join50`. -/
theorem chjoin_292 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_292) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_292 (85/64 : ℝ) (115/71 : ℝ) castAB_292 hIn.1 Fresh.ChamberDatasheet.chds_292 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 292's own tuple (atom `chds_292` + proved join `inclass_292` +
`chjoin_292`). -/
theorem dead_292 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_292 s :=
  chjoin_292 rho_292 s hs h50 inclass_292

/-- jj#293 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/71 b=115/76 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_293 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/71 : ℚ), B := (115/76 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 293 (exact rationals, the probe's own
case dump). -/
def rho_293 : Fin 5 → ℚ := ![1, 1, 9, 71/5, 76/5]

theorem castAB_293 : ((cls_293.A : ℚ) : ℝ) = (85/71 : ℝ) ∧ ((cls_293.B : ℚ) : ℝ) = (115/76 : ℝ) := by
  norm_num [cls_293]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_293`/`cls_293` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_293 : InClass rho_293 cls_293 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_293, rho_293] <;> norm_num⟩

/-- **gamma at class 293, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_293`
consumed through `join50`. -/
theorem chjoin_293 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_293) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_293 (85/71 : ℝ) (115/76 : ℝ) castAB_293 hIn.1 Fresh.ChamberDatasheet.chds_293 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 293's own tuple (atom `chds_293` + proved join `inclass_293` +
`chjoin_293`). -/
theorem dead_293 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_293 s :=
  chjoin_293 rho_293 s hs h50 inclass_293

/-- jj#294 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/77 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_294 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/77 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 294 (exact rationals, the probe's own
case dump). -/
def rho_294 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 77/5]

theorem castAB_294 : ((cls_294.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_294.B : ℚ) : ℝ) = (115/77 : ℝ) := by
  norm_num [cls_294]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_294`/`cls_294` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_294 : InClass rho_294 cls_294 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_294, rho_294] <;> norm_num⟩

/-- **gamma at class 294, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_294`
consumed through `join50`. -/
theorem chjoin_294 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_294) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_294 (85/72 : ℝ) (115/77 : ℝ) castAB_294 hIn.1 Fresh.ChamberDatasheet.chds_294 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 294's own tuple (atom `chds_294` + proved join `inclass_294` +
`chjoin_294`). -/
theorem dead_294 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_294 s :=
  chjoin_294 rho_294 s hs h50 inclass_294

/-- jj#295 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/78 | D2 | 1900 cases | NO-ALIVE-ON-GRID -/
def cls_295 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/78 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 295 (exact rationals, the probe's own
case dump). -/
def rho_295 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 78/5]

theorem castAB_295 : ((cls_295.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_295.B : ℚ) : ℝ) = (115/78 : ℝ) := by
  norm_num [cls_295]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_295`/`cls_295` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_295 : InClass rho_295 cls_295 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_295, rho_295] <;> norm_num⟩

/-- **gamma at class 295, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_295`
consumed through `join50`. -/
theorem chjoin_295 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_295) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_295 (85/72 : ℝ) (115/78 : ℝ) castAB_295 hIn.1 Fresh.ChamberDatasheet.chds_295 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 295's own tuple (atom `chds_295` + proved join `inclass_295` +
`chjoin_295`). -/
theorem dead_295 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_295 s :=
  chjoin_295 rho_295 s hs h50 inclass_295

/-- jj#296 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/79 | D2 | 1890 cases | NO-ALIVE-ON-GRID -/
def cls_296 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/79 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 296 (exact rationals, the probe's own
case dump). -/
def rho_296 : Fin 5 → ℚ := ![1, 1, 9, 74/5, 79/5]

theorem castAB_296 : ((cls_296.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_296.B : ℚ) : ℝ) = (115/79 : ℝ) := by
  norm_num [cls_296]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_296`/`cls_296` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_296 : InClass rho_296 cls_296 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_296, rho_296] <;> norm_num⟩

/-- **gamma at class 296, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_296`
consumed through `join50`. -/
theorem chjoin_296 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_296) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_296 (85/74 : ℝ) (115/79 : ℝ) castAB_296 hIn.1 Fresh.ChamberDatasheet.chds_296 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 296's own tuple (atom `chds_296` + proved join `inclass_296` +
`chjoin_296`). -/
theorem dead_296 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_296 s :=
  chjoin_296 rho_296 s hs h50 inclass_296

/-- jj#297 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/71 | D2 | 1881 cases | NO-ALIVE-ON-GRID -/
def cls_297 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 297 (exact rationals, the probe's own
case dump). -/
def rho_297 : Fin 5 → ℚ := ![1, 1, 7, 13, 71/5]

theorem castAB_297 : ((cls_297.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_297.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_297]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_297`/`cls_297` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_297 : InClass rho_297 cls_297 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_297, rho_297] <;> norm_num⟩

/-- **gamma at class 297, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_297`
consumed through `join50`. -/
theorem chjoin_297 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_297) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_297 (17/13 : ℝ) (115/71 : ℝ) castAB_297 hIn.1 Fresh.ChamberDatasheet.chds_297 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 297's own tuple (atom `chds_297` + proved join `inclass_297` +
`chjoin_297`). -/
theorem dead_297 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_297 s :=
  chjoin_297 rho_297 s hs h50 inclass_297

/-- jj#298 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/72 | D2 | 1881 cases | NO-ALIVE-ON-GRID -/
def cls_298 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 298 (exact rationals, the probe's own
case dump). -/
def rho_298 : Fin 5 → ℚ := ![1, 1, 7, 13, 72/5]

theorem castAB_298 : ((cls_298.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_298.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_298]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_298`/`cls_298` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_298 : InClass rho_298 cls_298 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_298, rho_298] <;> norm_num⟩

/-- **gamma at class 298, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_298`
consumed through `join50`. -/
theorem chjoin_298 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_298) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_298 (17/13 : ℝ) (115/72 : ℝ) castAB_298 hIn.1 Fresh.ChamberDatasheet.chds_298 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 298's own tuple (atom `chds_298` + proved join `inclass_298` +
`chjoin_298`). -/
theorem dead_298 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_298 s :=
  chjoin_298 rho_298 s hs h50 inclass_298

/-- jj#299 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/71 | D2 | 1881 cases | NO-ALIVE-ON-GRID -/
def cls_299 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 299 (exact rationals, the probe's own
case dump). -/
def rho_299 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 71/5]

theorem castAB_299 : ((cls_299.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_299.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_299]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_299`/`cls_299` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_299 : InClass rho_299 cls_299 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_299, rho_299] <;> norm_num⟩

/-- **gamma at class 299, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_299`
consumed through `join50`. -/
theorem chjoin_299 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_299) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_299 (85/66 : ℝ) (115/71 : ℝ) castAB_299 hIn.1 Fresh.ChamberDatasheet.chds_299 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 299's own tuple (atom `chds_299` + proved join `inclass_299` +
`chjoin_299`). -/
theorem dead_299 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_299 s :=
  chjoin_299 rho_299 s hs h50 inclass_299

/-- jj#300 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/72 | D2 | 1881 cases | NO-ALIVE-ON-GRID -/
def cls_300 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 300 (exact rationals, the probe's own
case dump). -/
def rho_300 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 72/5]

theorem castAB_300 : ((cls_300.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_300.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_300]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_300`/`cls_300` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_300 : InClass rho_300 cls_300 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_300, rho_300] <;> norm_num⟩

/-- **gamma at class 300, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_300`
consumed through `join50`. -/
theorem chjoin_300 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_300) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_300 (85/66 : ℝ) (115/72 : ℝ) castAB_300 hIn.1 Fresh.ChamberDatasheet.chds_300 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 300's own tuple (atom `chds_300` + proved join `inclass_300` +
`chjoin_300`). -/
theorem dead_300 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_300 s :=
  chjoin_300 rho_300 s hs h50 inclass_300

/-- jj#301 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=75/49 | D2 | 1881 cases | NO-ALIVE-ON-GRID -/
def cls_301 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 301 (exact rationals, the probe's own
case dump). -/
def rho_301 : Fin 5 → ℚ := ![1, 1, 37/5, 9, 49/5]

theorem castAB_301 : ((cls_301.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_301.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_301]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_301`/`cls_301` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_301 : InClass rho_301 cls_301 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_301, rho_301] <;> norm_num⟩

/-- **gamma at class 301, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_301`
consumed through `join50`. -/
theorem chjoin_301 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_301) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_301 (45/37 : ℝ) (75/49 : ℝ) castAB_301 hIn.1 Fresh.ChamberDatasheet.chds_301 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 301's own tuple (atom `chds_301` + proved join `inclass_301` +
`chjoin_301`). -/
theorem dead_301 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_301 s :=
  chjoin_301 rho_301 s hs h50 inclass_301

/-- jj#302 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=15/11 | D2 | 1848 cases | NO-ALIVE-ON-GRID -/
def cls_302 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 302 (exact rationals, the probe's own
case dump). -/
def rho_302 : Fin 5 → ℚ := ![1, 1, 11, 77/5, 77/5]

theorem castAB_302 : ((cls_302.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_302.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_302]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_302`/`cls_302` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_302 : InClass rho_302 cls_302 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_302, rho_302] <;> norm_num⟩

/-- **gamma at class 302, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_302`
consumed through `join50`. -/
theorem chjoin_302 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_302) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_302 (85/77 : ℝ) (15/11 : ℝ) castAB_302 hIn.1 Fresh.ChamberDatasheet.chds_302 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 302's own tuple (atom `chds_302` + proved join `inclass_302` +
`chjoin_302`). -/
theorem dead_302 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_302 s :=
  chjoin_302 rho_302 s hs h50 inclass_302

/-- jj#303 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=15/11 | D2 | 1848 cases | NO-ALIVE-ON-GRID -/
def cls_303 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 303 (exact rationals, the probe's own
case dump). -/
def rho_303 : Fin 5 → ℚ := ![1, 9, 11, 77/5, 77/5]

theorem castAB_303 : ((cls_303.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_303.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_303]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_303`/`cls_303` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_303 : InClass rho_303 cls_303 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_303, rho_303] <;> norm_num⟩

/-- **gamma at class 303, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_303`
consumed through `join50`. -/
theorem chjoin_303 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_303) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_303 (85/77 : ℝ) (15/11 : ℝ) castAB_303 hIn.1 Fresh.ChamberDatasheet.chds_303 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 303's own tuple (atom `chds_303` + proved join `inclass_303` +
`chjoin_303`). -/
theorem dead_303 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_303 s :=
  chjoin_303 rho_303 s hs h50 inclass_303

/-- jj#304 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/56 | D2 | 1848 cases | NO-ALIVE-ON-GRID -/
def cls_304 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 304 (exact rationals, the probe's own
case dump). -/
def rho_304 : Fin 5 → ℚ := ![1, 9, 56/5, 79/5, 79/5]

theorem castAB_304 : ((cls_304.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_304.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_304]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_304`/`cls_304` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_304 : InClass rho_304 cls_304 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_304, rho_304] <;> norm_num⟩

/-- **gamma at class 304, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_304`
consumed through `join50`. -/
theorem chjoin_304 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_304) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_304 (85/79 : ℝ) (75/56 : ℝ) castAB_304 hIn.1 Fresh.ChamberDatasheet.chds_304 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 304's own tuple (atom `chds_304` + proved join `inclass_304` +
`chjoin_304`). -/
theorem dead_304 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_304 s :=
  chjoin_304 rho_304 s hs h50 inclass_304

/-- jj#305 | PS1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=5/3 | D2 | 1845 cases | NO-ALIVE-ON-GRID -/
def cls_305 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (5/3 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 305 (exact rationals, the probe's own
case dump). -/
def rho_305 : Fin 5 → ℚ := ![1, 7, 58/5, 69/5, 17]

theorem castAB_305 : ((cls_305.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_305.B : ℚ) : ℝ) = (5/3 : ℝ) := by
  norm_num [cls_305]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_305`/`cls_305` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_305 : InClass rho_305 cls_305 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_305, rho_305] <;> norm_num⟩

/-- **gamma at class 305, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_305`
consumed through `join50`. -/
theorem chjoin_305 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_305) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_305 (25/17 : ℝ) (5/3 : ℝ) castAB_305 hIn.1 Fresh.ChamberDatasheet.chds_305 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 305's own tuple (atom `chds_305` + proved join `inclass_305` +
`chjoin_305`). -/
theorem dead_305 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_305 s :=
  chjoin_305 rho_305 s hs h50 inclass_305

/-- jj#306 | PS1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=5/3 | D2 | 1845 cases | NO-ALIVE-ON-GRID -/
def cls_306 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (5/3 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 306 (exact rationals, the probe's own
case dump). -/
def rho_306 : Fin 5 → ℚ := ![1, 7, 58/5, 69/5, 17]

theorem castAB_306 : ((cls_306.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_306.B : ℚ) : ℝ) = (5/3 : ℝ) := by
  norm_num [cls_306]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_306`/`cls_306` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_306 : InClass rho_306 cls_306 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_306, rho_306] <;> norm_num⟩

/-- **gamma at class 306, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_306`
consumed through `join50`. -/
theorem chjoin_306 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_306) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_306 (25/17 : ℝ) (5/3 : ℝ) castAB_306 hIn.1 Fresh.ChamberDatasheet.chds_306 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 306's own tuple (atom `chds_306` + proved join `inclass_306` +
`chjoin_306`). -/
theorem dead_306 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_306 s :=
  chjoin_306 rho_306 s hs h50 inclass_306

/-- jj#307 | PPS1G1S2 | kL=2 kR=4 | cL=G1 cR=S2 | a=17/9 b=155/76 | D2 | 1832 cases | NO-ALIVE-ON-GRID -/
def cls_307 : ChamberClass :=
  { kL := 2, kR := 4, A := (17/9 : ℚ), B := (155/76 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 307 (exact rationals, the probe's own
case dump). -/
def rho_307 : Fin 5 → ℚ := ![1, 26/5, 7, 9, 76/5]

theorem castAB_307 : ((cls_307.A : ℚ) : ℝ) = (17/9 : ℝ) ∧ ((cls_307.B : ℚ) : ℝ) = (155/76 : ℝ) := by
  norm_num [cls_307]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_307`/`cls_307` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_307 : InClass rho_307 cls_307 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_307, rho_307] <;> norm_num⟩

/-- **gamma at class 307, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_307`
consumed through `join50`. -/
theorem chjoin_307 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_307) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_307 (17/9 : ℝ) (155/76 : ℝ) castAB_307 hIn.1 Fresh.ChamberDatasheet.chds_307 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 307's own tuple (atom `chds_307` + proved join `inclass_307` +
`chjoin_307`). -/
theorem dead_307 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_307 s :=
  chjoin_307 rho_307 s hs h50 inclass_307

/-- jj#308 | PPG1G1G1 | kL=3 kR=4 | cL=G1 cR=G1 | a=125/67 b=31/15 | D2 | 1822 cases | NO-ALIVE-ON-GRID -/
def cls_308 : ChamberClass :=
  { kL := 3, kR := 4, A := (125/67 : ℚ), B := (31/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 308 (exact rationals, the probe's own
case dump). -/
def rho_308 : Fin 5 → ℚ := ![1, 27/5, 46/5, 67/5, 15]

theorem castAB_308 : ((cls_308.A : ℚ) : ℝ) = (125/67 : ℝ) ∧ ((cls_308.B : ℚ) : ℝ) = (31/15 : ℝ) := by
  norm_num [cls_308]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_308`/`cls_308` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_308 : InClass rho_308 cls_308 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_308, rho_308] <;> norm_num⟩

/-- **gamma at class 308, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_308`
consumed through `join50`. -/
theorem chjoin_308 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_308) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_308 (125/67 : ℝ) (31/15 : ℝ) castAB_308 hIn.1 Fresh.ChamberDatasheet.chds_308 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 308's own tuple (atom `chds_308` + proved join `inclass_308` +
`chjoin_308`). -/
theorem dead_308 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_308 s :=
  chjoin_308 rho_308 s hs h50 inclass_308

/-- jj#309 | PPG1G1S2 | kL=3 kR=4 | cL=G1 cR=G1 | a=125/67 b=31/15 | D2 | 1822 cases | NO-ALIVE-ON-GRID -/
def cls_309 : ChamberClass :=
  { kL := 3, kR := 4, A := (125/67 : ℚ), B := (31/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 309 (exact rationals, the probe's own
case dump). -/
def rho_309 : Fin 5 → ℚ := ![1, 27/5, 46/5, 67/5, 15]

theorem castAB_309 : ((cls_309.A : ℚ) : ℝ) = (125/67 : ℝ) ∧ ((cls_309.B : ℚ) : ℝ) = (31/15 : ℝ) := by
  norm_num [cls_309]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_309`/`cls_309` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_309 : InClass rho_309 cls_309 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_309, rho_309] <;> norm_num⟩

/-- **gamma at class 309, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_309`
consumed through `join50`. -/
theorem chjoin_309 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_309) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_309 (125/67 : ℝ) (31/15 : ℝ) castAB_309 hIn.1 Fresh.ChamberDatasheet.chds_309 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 309's own tuple (atom `chds_309` + proved join `inclass_309` +
`chjoin_309`). -/
theorem dead_309 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_309 s :=
  chjoin_309 rho_309 s hs h50 inclass_309

/-- jj#310 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/82 | D2 | 1820 cases | NO-ALIVE-ON-GRID -/
def cls_310 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 310 (exact rationals, the probe's own
case dump). -/
def rho_310 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 82/5]

theorem castAB_310 : ((cls_310.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_310.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_310]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_310`/`cls_310` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_310 : InClass rho_310 cls_310 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_310, rho_310] <;> norm_num⟩

/-- **gamma at class 310, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_310`
consumed through `join50`. -/
theorem chjoin_310 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_310) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_310 (85/72 : ℝ) (115/82 : ℝ) castAB_310 hIn.1 Fresh.ChamberDatasheet.chds_310 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 310's own tuple (atom `chds_310` + proved join `inclass_310` +
`chjoin_310`). -/
theorem dead_310 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_310 s :=
  chjoin_310 rho_310 s hs h50 inclass_310

/-- jj#311 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=115/73 | D2 | 1820 cases | NO-ALIVE-ON-GRID -/
def cls_311 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (115/73 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 311 (exact rationals, the probe's own
case dump). -/
def rho_311 : Fin 5 → ℚ := ![1, 9, 9, 64/5, 73/5]

theorem castAB_311 : ((cls_311.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_311.B : ℚ) : ℝ) = (115/73 : ℝ) := by
  norm_num [cls_311]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_311`/`cls_311` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_311 : InClass rho_311 cls_311 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_311, rho_311] <;> norm_num⟩

/-- **gamma at class 311, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_311`
consumed through `join50`. -/
theorem chjoin_311 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_311) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_311 (85/64 : ℝ) (115/73 : ℝ) castAB_311 hIn.1 Fresh.ChamberDatasheet.chds_311 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 311's own tuple (atom `chds_311` + proved join `inclass_311` +
`chjoin_311`). -/
theorem dead_311 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_311 s :=
  chjoin_311 rho_311 s hs h50 inclass_311

/-- jj#312 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/82 | D2 | 1820 cases | NO-ALIVE-ON-GRID -/
def cls_312 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 312 (exact rationals, the probe's own
case dump). -/
def rho_312 : Fin 5 → ℚ := ![1, 9, 9, 72/5, 82/5]

theorem castAB_312 : ((cls_312.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_312.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_312]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_312`/`cls_312` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_312 : InClass rho_312 cls_312 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_312, rho_312] <;> norm_num⟩

/-- **gamma at class 312, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_312`
consumed through `join50`. -/
theorem chjoin_312 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_312) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_312 (85/72 : ℝ) (115/82 : ℝ) castAB_312 hIn.1 Fresh.ChamberDatasheet.chds_312 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 312's own tuple (atom `chds_312` + proved join `inclass_312` +
`chjoin_312`). -/
theorem dead_312 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_312 s :=
  chjoin_312 rho_312 s hs h50 inclass_312

/-- jj#313 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=75/49 | D2 | 1782 cases | NO-ALIVE-ON-GRID -/
def cls_313 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 313 (exact rationals, the probe's own
case dump). -/
def rho_313 : Fin 5 → ℚ := ![1, 37/5, 37/5, 9, 49/5]

theorem castAB_313 : ((cls_313.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_313.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_313]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_313`/`cls_313` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_313 : InClass rho_313 cls_313 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_313, rho_313] <;> norm_num⟩

/-- **gamma at class 313, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_313`
consumed through `join50`. -/
theorem chjoin_313 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_313) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_313 (45/37 : ℝ) (75/49 : ℝ) castAB_313 hIn.1 Fresh.ChamberDatasheet.chds_313 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 313's own tuple (atom `chds_313` + proved join `inclass_313` +
`chjoin_313`). -/
theorem dead_313 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_313 s :=
  chjoin_313 rho_313 s hs h50 inclass_313

/-- jj#314 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/71 | D2 | 1782 cases | NO-ALIVE-ON-GRID -/
def cls_314 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/71 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 314 (exact rationals, the probe's own
case dump). -/
def rho_314 : Fin 5 → ℚ := ![1, 7, 9, 13, 71/5]

theorem castAB_314 : ((cls_314.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_314.B : ℚ) : ℝ) = (115/71 : ℝ) := by
  norm_num [cls_314]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_314`/`cls_314` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_314 : InClass rho_314 cls_314 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_314, rho_314] <;> norm_num⟩

/-- **gamma at class 314, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_314`
consumed through `join50`. -/
theorem chjoin_314 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_314) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_314 (17/13 : ℝ) (115/71 : ℝ) castAB_314 hIn.1 Fresh.ChamberDatasheet.chds_314 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 314's own tuple (atom `chds_314` + proved join `inclass_314` +
`chjoin_314`). -/
theorem dead_314 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_314 s :=
  chjoin_314 rho_314 s hs h50 inclass_314

/-- jj#315 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/72 | D2 | 1782 cases | NO-ALIVE-ON-GRID -/
def cls_315 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 315 (exact rationals, the probe's own
case dump). -/
def rho_315 : Fin 5 → ℚ := ![1, 7, 9, 66/5, 72/5]

theorem castAB_315 : ((cls_315.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_315.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_315]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_315`/`cls_315` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_315 : InClass rho_315 cls_315 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_315, rho_315] <;> norm_num⟩

/-- **gamma at class 315, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_315`
consumed through `join50`. -/
theorem chjoin_315 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_315) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_315 (85/66 : ℝ) (115/72 : ℝ) castAB_315 hIn.1 Fresh.ChamberDatasheet.chds_315 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 315's own tuple (atom `chds_315` + proved join `inclass_315` +
`chjoin_315`). -/
theorem dead_315 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_315 s :=
  chjoin_315 rho_315 s hs h50 inclass_315

/-- jj#316 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=15/11 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_316 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 316 (exact rationals, the probe's own
case dump). -/
def rho_316 : Fin 5 → ℚ := ![1, 1, 1, 11, 76/5]

theorem castAB_316 : ((cls_316.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_316.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_316]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_316`/`cls_316` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_316 : InClass rho_316 cls_316 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_316, rho_316] <;> norm_num⟩

/-- **gamma at class 316, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_316`
consumed through `join50`. -/
theorem chjoin_316 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_316) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_316 (85/76 : ℝ) (15/11 : ℝ) castAB_316 hIn.1 Fresh.ChamberDatasheet.chds_316 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 316's own tuple (atom `chds_316` + proved join `inclass_316` +
`chjoin_316`). -/
theorem dead_316 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_316 s :=
  chjoin_316 rho_316 s hs h50 inclass_316

/-- jj#317 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=15/11 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_317 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 317 (exact rationals, the probe's own
case dump). -/
def rho_317 : Fin 5 → ℚ := ![1, 1, 1, 11, 77/5]

theorem castAB_317 : ((cls_317.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_317.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_317]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_317`/`cls_317` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_317 : InClass rho_317 cls_317 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_317, rho_317] <;> norm_num⟩

/-- **gamma at class 317, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_317`
consumed through `join50`. -/
theorem chjoin_317 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_317) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_317 (85/77 : ℝ) (15/11 : ℝ) castAB_317 hIn.1 Fresh.ChamberDatasheet.chds_317 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 317's own tuple (atom `chds_317` + proved join `inclass_317` +
`chjoin_317`). -/
theorem dead_317 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_317 s :=
  chjoin_317 rho_317 s hs h50 inclass_317

/-- jj#318 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=15/11 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_318 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 318 (exact rationals, the probe's own
case dump). -/
def rho_318 : Fin 5 → ℚ := ![1, 1, 1, 11, 78/5]

theorem castAB_318 : ((cls_318.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_318.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_318]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_318`/`cls_318` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_318 : InClass rho_318 cls_318 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_318, rho_318] <;> norm_num⟩

/-- **gamma at class 318, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_318`
consumed through `join50`. -/
theorem chjoin_318 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_318) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_318 (85/78 : ℝ) (15/11 : ℝ) castAB_318 hIn.1 Fresh.ChamberDatasheet.chds_318 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 318's own tuple (atom `chds_318` + proved join `inclass_318` +
`chjoin_318`). -/
theorem dead_318 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_318 s :=
  chjoin_318 rho_318 s hs h50 inclass_318

/-- jj#319 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=15/11 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_319 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 319 (exact rationals, the probe's own
case dump). -/
def rho_319 : Fin 5 → ℚ := ![1, 1, 1, 11, 79/5]

theorem castAB_319 : ((cls_319.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_319.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_319]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_319`/`cls_319` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_319 : InClass rho_319 cls_319 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_319, rho_319] <;> norm_num⟩

/-- **gamma at class 319, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_319`
consumed through `join50`. -/
theorem chjoin_319 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_319) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_319 (85/79 : ℝ) (15/11 : ℝ) castAB_319 hIn.1 Fresh.ChamberDatasheet.chds_319 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 319's own tuple (atom `chds_319` + proved join `inclass_319` +
`chjoin_319`). -/
theorem dead_319 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_319 s :=
  chjoin_319 rho_319 s hs h50 inclass_319

/-- jj#320 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=15/11 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_320 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 320 (exact rationals, the probe's own
case dump). -/
def rho_320 : Fin 5 → ℚ := ![1, 1, 1, 11, 16]

theorem castAB_320 : ((cls_320.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_320.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_320]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_320`/`cls_320` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_320 : InClass rho_320 cls_320 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_320, rho_320] <;> norm_num⟩

/-- **gamma at class 320, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_320`
consumed through `join50`. -/
theorem chjoin_320 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_320) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_320 (17/16 : ℝ) (15/11 : ℝ) castAB_320 hIn.1 Fresh.ChamberDatasheet.chds_320 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 320's own tuple (atom `chds_320` + proved join `inclass_320` +
`chjoin_320`). -/
theorem dead_320 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_320 s :=
  chjoin_320 rho_320 s hs h50 inclass_320

/-- jj#321 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=15/11 | D1 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_321 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 321 (exact rationals, the probe's own
case dump). -/
def rho_321 : Fin 5 → ℚ := ![1, 1, 1, 11, 81/5]

theorem castAB_321 : ((cls_321.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_321.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_321]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_321`/`cls_321` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_321 : InClass rho_321 cls_321 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_321, rho_321] <;> norm_num⟩

/-- **gamma at class 321, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_321`
consumed through `join50`. -/
theorem chjoin_321 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_321) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_321 (85/81 : ℝ) (15/11 : ℝ) castAB_321 hIn.1 Fresh.ChamberDatasheet.chds_321 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 321's own tuple (atom `chds_321` + proved join `inclass_321` +
`chjoin_321`). -/
theorem dead_321 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_321 s :=
  chjoin_321 rho_321 s hs h50 inclass_321

/-- jj#322 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=15/11 | D1 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_322 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 322 (exact rationals, the probe's own
case dump). -/
def rho_322 : Fin 5 → ℚ := ![1, 1, 1, 11, 82/5]

theorem castAB_322 : ((cls_322.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_322.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_322]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_322`/`cls_322` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_322 : InClass rho_322 cls_322 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_322, rho_322] <;> norm_num⟩

/-- **gamma at class 322, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_322`
consumed through `join50`. -/
theorem chjoin_322 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_322) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_322 (85/82 : ℝ) (15/11 : ℝ) castAB_322 hIn.1 Fresh.ChamberDatasheet.chds_322 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 322's own tuple (atom `chds_322` + proved join `inclass_322` +
`chjoin_322`). -/
theorem dead_322 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_322 s :=
  chjoin_322 rho_322 s hs h50 inclass_322

/-- jj#323 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=15/11 | D1 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_323 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 323 (exact rationals, the probe's own
case dump). -/
def rho_323 : Fin 5 → ℚ := ![1, 1, 1, 11, 83/5]

theorem castAB_323 : ((cls_323.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_323.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_323]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_323`/`cls_323` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_323 : InClass rho_323 cls_323 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_323, rho_323] <;> norm_num⟩

/-- **gamma at class 323, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_323`
consumed through `join50`. -/
theorem chjoin_323 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_323) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_323 (85/83 : ℝ) (15/11 : ℝ) castAB_323 hIn.1 Fresh.ChamberDatasheet.chds_323 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 323's own tuple (atom `chds_323` + proved join `inclass_323` +
`chjoin_323`). -/
theorem dead_323 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_323 s :=
  chjoin_323 rho_323 s hs h50 inclass_323

/-- jj#324 | PPPG1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=15/11 | D1 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_324 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (15/11 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 324 (exact rationals, the probe's own
case dump). -/
def rho_324 : Fin 5 → ℚ := ![1, 1, 1, 11, 84/5]

theorem castAB_324 : ((cls_324.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_324.B : ℚ) : ℝ) = (15/11 : ℝ) := by
  norm_num [cls_324]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_324`/`cls_324` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_324 : InClass rho_324 cls_324 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_324, rho_324] <;> norm_num⟩

/-- **gamma at class 324, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_324`
consumed through `join50`. -/
theorem chjoin_324 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_324) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_324 (85/84 : ℝ) (15/11 : ℝ) castAB_324 hIn.1 Fresh.ChamberDatasheet.chds_324 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 324's own tuple (atom `chds_324` + proved join `inclass_324` +
`chjoin_324`). -/
theorem dead_324 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_324 s :=
  chjoin_324 rho_324 s hs h50 inclass_324

/-- jj#325 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_325 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 325 (exact rationals, the probe's own
case dump). -/
def rho_325 : Fin 5 → ℚ := ![1, 1, 1, 72/5, 83/5]

theorem castAB_325 : ((cls_325.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_325.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_325]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_325`/`cls_325` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_325 : InClass rho_325 cls_325 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_325, rho_325] <;> norm_num⟩

/-- **gamma at class 325, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_325`
consumed through `join50`. -/
theorem chjoin_325 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_325) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_325 (85/72 : ℝ) (115/83 : ℝ) castAB_325 hIn.1 Fresh.ChamberDatasheet.chds_325 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 325's own tuple (atom `chds_325` + proved join `inclass_325` +
`chjoin_325`). -/
theorem dead_325 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_325 s :=
  chjoin_325 rho_325 s hs h50 inclass_325

/-- jj#326 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_326 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 326 (exact rationals, the probe's own
case dump). -/
def rho_326 : Fin 5 → ℚ := ![1, 1, 1, 72/5, 84/5]

theorem castAB_326 : ((cls_326.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_326.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_326]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_326`/`cls_326` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_326 : InClass rho_326 cls_326 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_326, rho_326] <;> norm_num⟩

/-- **gamma at class 326, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_326`
consumed through `join50`. -/
theorem chjoin_326 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_326) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_326 (85/72 : ℝ) (115/84 : ℝ) castAB_326 hIn.1 Fresh.ChamberDatasheet.chds_326 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 326's own tuple (atom `chds_326` + proved join `inclass_326` +
`chjoin_326`). -/
theorem dead_326 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_326 s :=
  chjoin_326 rho_326 s hs h50 inclass_326

/-- jj#327 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_327 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 327 (exact rationals, the probe's own
case dump). -/
def rho_327 : Fin 5 → ℚ := ![1, 1, 1, 72/5, 17]

theorem castAB_327 : ((cls_327.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_327.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_327]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_327`/`cls_327` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_327 : InClass rho_327 cls_327 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_327, rho_327] <;> norm_num⟩

/-- **gamma at class 327, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_327`
consumed through `join50`. -/
theorem chjoin_327 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_327) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_327 (85/72 : ℝ) (23/17 : ℝ) castAB_327 hIn.1 Fresh.ChamberDatasheet.chds_327 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 327's own tuple (atom `chds_327` + proved join `inclass_327` +
`chjoin_327`). -/
theorem dead_327 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_327 s :=
  chjoin_327 rho_327 s hs h50 inclass_327

/-- jj#328 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_328 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 328 (exact rationals, the probe's own
case dump). -/
def rho_328 : Fin 5 → ℚ := ![1, 1, 1, 73/5, 83/5]

theorem castAB_328 : ((cls_328.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_328.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_328]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_328`/`cls_328` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_328 : InClass rho_328 cls_328 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_328, rho_328] <;> norm_num⟩

/-- **gamma at class 328, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_328`
consumed through `join50`. -/
theorem chjoin_328 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_328) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_328 (85/73 : ℝ) (115/83 : ℝ) castAB_328 hIn.1 Fresh.ChamberDatasheet.chds_328 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 328's own tuple (atom `chds_328` + proved join `inclass_328` +
`chjoin_328`). -/
theorem dead_328 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_328 s :=
  chjoin_328 rho_328 s hs h50 inclass_328

/-- jj#329 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_329 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 329 (exact rationals, the probe's own
case dump). -/
def rho_329 : Fin 5 → ℚ := ![1, 1, 1, 73/5, 84/5]

theorem castAB_329 : ((cls_329.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_329.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_329]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_329`/`cls_329` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_329 : InClass rho_329 cls_329 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_329, rho_329] <;> norm_num⟩

/-- **gamma at class 329, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_329`
consumed through `join50`. -/
theorem chjoin_329 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_329) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_329 (85/73 : ℝ) (115/84 : ℝ) castAB_329 hIn.1 Fresh.ChamberDatasheet.chds_329 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 329's own tuple (atom `chds_329` + proved join `inclass_329` +
`chjoin_329`). -/
theorem dead_329 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_329 s :=
  chjoin_329 rho_329 s hs h50 inclass_329

/-- jj#330 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_330 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 330 (exact rationals, the probe's own
case dump). -/
def rho_330 : Fin 5 → ℚ := ![1, 1, 1, 73/5, 17]

theorem castAB_330 : ((cls_330.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_330.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_330]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_330`/`cls_330` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_330 : InClass rho_330 cls_330 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_330, rho_330] <;> norm_num⟩

/-- **gamma at class 330, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_330`
consumed through `join50`. -/
theorem chjoin_330 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_330) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_330 (85/73 : ℝ) (23/17 : ℝ) castAB_330 hIn.1 Fresh.ChamberDatasheet.chds_330 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 330's own tuple (atom `chds_330` + proved join `inclass_330` +
`chjoin_330`). -/
theorem dead_330 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_330 s :=
  chjoin_330 rho_330 s hs h50 inclass_330

/-- jj#331 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/83 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_331 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 331 (exact rationals, the probe's own
case dump). -/
def rho_331 : Fin 5 → ℚ := ![1, 1, 1, 74/5, 83/5]

theorem castAB_331 : ((cls_331.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_331.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_331]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_331`/`cls_331` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_331 : InClass rho_331 cls_331 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_331, rho_331] <;> norm_num⟩

/-- **gamma at class 331, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_331`
consumed through `join50`. -/
theorem chjoin_331 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_331) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_331 (85/74 : ℝ) (115/83 : ℝ) castAB_331 hIn.1 Fresh.ChamberDatasheet.chds_331 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 331's own tuple (atom `chds_331` + proved join `inclass_331` +
`chjoin_331`). -/
theorem dead_331 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_331 s :=
  chjoin_331 rho_331 s hs h50 inclass_331

/-- jj#332 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/84 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_332 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 332 (exact rationals, the probe's own
case dump). -/
def rho_332 : Fin 5 → ℚ := ![1, 1, 1, 74/5, 84/5]

theorem castAB_332 : ((cls_332.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_332.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_332]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_332`/`cls_332` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_332 : InClass rho_332 cls_332 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_332, rho_332] <;> norm_num⟩

/-- **gamma at class 332, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_332`
consumed through `join50`. -/
theorem chjoin_332 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_332) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_332 (85/74 : ℝ) (115/84 : ℝ) castAB_332 hIn.1 Fresh.ChamberDatasheet.chds_332 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 332's own tuple (atom `chds_332` + proved join `inclass_332` +
`chjoin_332`). -/
theorem dead_332 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_332 s :=
  chjoin_332 rho_332 s hs h50 inclass_332

/-- jj#333 | PPPG1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_333 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 15], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 333 (exact rationals, the probe's own
case dump). -/
def rho_333 : Fin 5 → ℚ := ![1, 1, 1, 74/5, 17]

theorem castAB_333 : ((cls_333.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_333.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_333]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_333`/`cls_333` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_333 : InClass rho_333 cls_333 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_333, rho_333] <;> norm_num⟩

/-- **gamma at class 333, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_333`
consumed through `join50`. -/
theorem chjoin_333 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_333) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_333 (85/74 : ℝ) (23/17 : ℝ) castAB_333 hIn.1 Fresh.ChamberDatasheet.chds_333 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 333's own tuple (atom `chds_333` + proved join `inclass_333` +
`chjoin_333`). -/
theorem dead_333 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_333 s :=
  chjoin_333 rho_333 s hs h50 inclass_333

/-- jj#334 | PPPG1E | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_334 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 17], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 334 (exact rationals, the probe's own
case dump). -/
def rho_334 : Fin 5 → ℚ := ![1, 1, 1, 72/5, 17]

theorem castAB_334 : ((cls_334.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_334.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_334]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_334`/`cls_334` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_334 : InClass rho_334 cls_334 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_334, rho_334] <;> norm_num⟩

/-- **gamma at class 334, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_334`
consumed through `join50`. -/
theorem chjoin_334 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_334) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_334 (85/72 : ℝ) (23/17 : ℝ) castAB_334 hIn.1 Fresh.ChamberDatasheet.chds_334 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 334's own tuple (atom `chds_334` + proved join `inclass_334` +
`chjoin_334`). -/
theorem dead_334 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_334 s :=
  chjoin_334 rho_334 s hs h50 inclass_334

/-- jj#335 | PPPG1E | kL=2 kR=3 | cL=G1 cR=E | a=85/73 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_335 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 17], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 335 (exact rationals, the probe's own
case dump). -/
def rho_335 : Fin 5 → ℚ := ![1, 1, 1, 73/5, 17]

theorem castAB_335 : ((cls_335.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_335.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_335]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_335`/`cls_335` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_335 : InClass rho_335 cls_335 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_335, rho_335] <;> norm_num⟩

/-- **gamma at class 335, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_335`
consumed through `join50`. -/
theorem chjoin_335 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_335) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_335 (85/73 : ℝ) (23/17 : ℝ) castAB_335 hIn.1 Fresh.ChamberDatasheet.chds_335 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 335's own tuple (atom `chds_335` + proved join `inclass_335` +
`chjoin_335`). -/
theorem dead_335 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_335 s :=
  chjoin_335 rho_335 s hs h50 inclass_335

/-- jj#336 | PPPG1E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_336 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 1, 9, 17], hi := ![7, 7, 7, 15, 17] }

/-- The recorded representative 5-tuple of class 336 (exact rationals, the probe's own
case dump). -/
def rho_336 : Fin 5 → ℚ := ![1, 1, 1, 74/5, 17]

theorem castAB_336 : ((cls_336.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_336.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_336]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_336`/`cls_336` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_336 : InClass rho_336 cls_336 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_336, rho_336] <;> norm_num⟩

/-- **gamma at class 336, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_336`
consumed through `join50`. -/
theorem chjoin_336 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_336) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_336 (85/74 : ℝ) (23/17 : ℝ) castAB_336 hIn.1 Fresh.ChamberDatasheet.chds_336 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 336's own tuple (atom `chds_336` + proved join `inclass_336` +
`chjoin_336`). -/
theorem dead_336 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_336 s :=
  chjoin_336 rho_336 s hs h50 inclass_336

/-- jj#337 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/56 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_337 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 337 (exact rationals, the probe's own
case dump). -/
def rho_337 : Fin 5 → ℚ := ![1, 1, 56/5, 79/5, 79/5]

theorem castAB_337 : ((cls_337.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_337.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_337]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_337`/`cls_337` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_337 : InClass rho_337 cls_337 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_337, rho_337] <;> norm_num⟩

/-- **gamma at class 337, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_337`
consumed through `join50`. -/
theorem chjoin_337 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_337) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_337 (85/79 : ℝ) (75/56 : ℝ) castAB_337 hIn.1 Fresh.ChamberDatasheet.chds_337 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 337's own tuple (atom `chds_337` + proved join `inclass_337` +
`chjoin_337`). -/
theorem dead_337 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_337 s :=
  chjoin_337 rho_337 s hs h50 inclass_337

/-- jj#338 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=25/19 | D2 | 1771 cases | NO-ALIVE-ON-GRID -/
def cls_338 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 338 (exact rationals, the probe's own
case dump). -/
def rho_338 : Fin 5 → ℚ := ![1, 1, 57/5, 79/5, 79/5]

theorem castAB_338 : ((cls_338.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_338.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_338]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_338`/`cls_338` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_338 : InClass rho_338 cls_338 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_338, rho_338] <;> norm_num⟩

/-- **gamma at class 338, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_338`
consumed through `join50`. -/
theorem chjoin_338 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_338) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_338 (85/79 : ℝ) (25/19 : ℝ) castAB_338 hIn.1 Fresh.ChamberDatasheet.chds_338 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 338's own tuple (atom `chds_338` + proved join `inclass_338` +
`chjoin_338`). -/
theorem dead_338 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_338 s :=
  chjoin_338 rho_338 s hs h50 inclass_338

/-- jj#339 | PPPS1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=25/14 | D1 | 1768 cases | NO-ALIVE-ON-GRID -/
def cls_339 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (25/14 : ℚ),
    lo := ![1, 1, 1, 7, 7], hi := ![7, 7, 7, 9, 9] }

/-- The recorded representative 5-tuple of class 339 (exact rationals, the probe's own
case dump). -/
def rho_339 : Fin 5 → ℚ := ![1, 1, 1, 7, 42/5]

theorem castAB_339 : ((cls_339.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_339.B : ℚ) : ℝ) = (25/14 : ℝ) := by
  norm_num [cls_339]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_339`/`cls_339` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_339 : InClass rho_339 cls_339 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_339, rho_339] <;> norm_num⟩

/-- **gamma at class 339, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_339`
consumed through `join50`. -/
theorem chjoin_339 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_339) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_339 (9/7 : ℝ) (25/14 : ℝ) castAB_339 hIn.1 Fresh.ChamberDatasheet.chds_339 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 339's own tuple (atom `chds_339` + proved join `inclass_339` +
`chjoin_339`). -/
theorem dead_339 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_339 s :=
  chjoin_339 rho_339 s hs h50 inclass_339

/-- jj#340 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/62 b=115/68 | D2 | 1764 cases | NO-ALIVE-ON-GRID -/
def cls_340 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/62 : ℚ), B := (115/68 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 340 (exact rationals, the probe's own
case dump). -/
def rho_340 : Fin 5 → ℚ := ![1, 1, 7, 62/5, 68/5]

theorem castAB_340 : ((cls_340.A : ℚ) : ℝ) = (85/62 : ℝ) ∧ ((cls_340.B : ℚ) : ℝ) = (115/68 : ℝ) := by
  norm_num [cls_340]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_340`/`cls_340` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_340 : InClass rho_340 cls_340 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_340, rho_340] <;> norm_num⟩

/-- **gamma at class 340, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_340`
consumed through `join50`. -/
theorem chjoin_340 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_340) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_340 (85/62 : ℝ) (115/68 : ℝ) castAB_340 hIn.1 Fresh.ChamberDatasheet.chds_340 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 340's own tuple (atom `chds_340` + proved join `inclass_340` +
`chjoin_340`). -/
theorem dead_340 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_340 s :=
  chjoin_340 rho_340 s hs h50 inclass_340

/-- jj#341 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/82 | D2 | 1760 cases | NO-ALIVE-ON-GRID -/
def cls_341 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 341 (exact rationals, the probe's own
case dump). -/
def rho_341 : Fin 5 → ℚ := ![1, 9, 74/5, 15, 82/5]

theorem castAB_341 : ((cls_341.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_341.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_341]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_341`/`cls_341` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_341 : InClass rho_341 cls_341 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_341, rho_341] <;> norm_num⟩

/-- **gamma at class 341, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_341`
consumed through `join50`. -/
theorem chjoin_341 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_341) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_341 (85/74 : ℝ) (115/82 : ℝ) castAB_341 hIn.1 Fresh.ChamberDatasheet.chds_341 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 341's own tuple (atom `chds_341` + proved join `inclass_341` +
`chjoin_341`). -/
theorem dead_341 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_341 s :=
  chjoin_341 rho_341 s hs h50 inclass_341

/-- jj#342 | PPG1G1G1 | kL=3 kR=4 | cL=G1 cR=G1 | a=125/68 b=31/15 | D2 | 1734 cases | NO-ALIVE-ON-GRID -/
def cls_342 : ChamberClass :=
  { kL := 3, kR := 4, A := (125/68 : ℚ), B := (31/15 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 342 (exact rationals, the probe's own
case dump). -/
def rho_342 : Fin 5 → ℚ := ![1, 27/5, 47/5, 68/5, 15]

theorem castAB_342 : ((cls_342.A : ℚ) : ℝ) = (125/68 : ℝ) ∧ ((cls_342.B : ℚ) : ℝ) = (31/15 : ℝ) := by
  norm_num [cls_342]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_342`/`cls_342` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_342 : InClass rho_342 cls_342 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_342, rho_342] <;> norm_num⟩

/-- **gamma at class 342, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_342`
consumed through `join50`. -/
theorem chjoin_342 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_342) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_342 (125/68 : ℝ) (31/15 : ℝ) castAB_342 hIn.1 Fresh.ChamberDatasheet.chds_342 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 342's own tuple (atom `chds_342` + proved join `inclass_342` +
`chjoin_342`). -/
theorem dead_342 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_342 s :=
  chjoin_342 rho_342 s hs h50 inclass_342

/-- jj#343 | PPG1G1S2 | kL=3 kR=4 | cL=G1 cR=G1 | a=125/68 b=31/15 | D2 | 1734 cases | NO-ALIVE-ON-GRID -/
def cls_343 : ChamberClass :=
  { kL := 3, kR := 4, A := (125/68 : ℚ), B := (31/15 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 343 (exact rationals, the probe's own
case dump). -/
def rho_343 : Fin 5 → ℚ := ![1, 27/5, 47/5, 68/5, 15]

theorem castAB_343 : ((cls_343.A : ℚ) : ℝ) = (125/68 : ℝ) ∧ ((cls_343.B : ℚ) : ℝ) = (31/15 : ℝ) := by
  norm_num [cls_343]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_343`/`cls_343` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_343 : InClass rho_343 cls_343 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_343, rho_343] <;> norm_num⟩

/-- **gamma at class 343, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_343`
consumed through `join50`. -/
theorem chjoin_343 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_343) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_343 (125/68 : ℝ) (31/15 : ℝ) castAB_343 hIn.1 Fresh.ChamberDatasheet.chds_343 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 343's own tuple (atom `chds_343` + proved join `inclass_343` +
`chjoin_343`). -/
theorem dead_343 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_343 s :=
  chjoin_343 rho_343 s hs h50 inclass_343

/-- jj#344 | PS1G1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=25/17 | D2 | 1729 cases | NO-ALIVE-ON-GRID -/
def cls_344 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 344 (exact rationals, the probe's own
case dump). -/
def rho_344 : Fin 5 → ℚ := ![1, 37/5, 9, 9, 51/5]

theorem castAB_344 : ((cls_344.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_344.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_344]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_344`/`cls_344` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_344 : InClass rho_344 cls_344 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_344, rho_344] <;> norm_num⟩

/-- **gamma at class 344, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_344`
consumed through `join50`. -/
theorem chjoin_344 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_344) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_344 (45/37 : ℝ) (25/17 : ℝ) castAB_344 hIn.1 Fresh.ChamberDatasheet.chds_344 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 344's own tuple (atom `chds_344` + proved join `inclass_344` +
`chjoin_344`). -/
theorem dead_344 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_344 s :=
  chjoin_344 rho_344 s hs h50 inclass_344

/-- jj#345 | PG1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=115/74 | D2 | 1729 cases | NO-ALIVE-ON-GRID -/
def cls_345 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (115/74 : ℚ),
    lo := ![1, 9, 9, 9, 9], hi := ![7, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 345 (exact rationals, the probe's own
case dump). -/
def rho_345 : Fin 5 → ℚ := ![1, 9, 9, 66/5, 74/5]

theorem castAB_345 : ((cls_345.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_345.B : ℚ) : ℝ) = (115/74 : ℝ) := by
  norm_num [cls_345]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_345`/`cls_345` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_345 : InClass rho_345 cls_345 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_345, rho_345] <;> norm_num⟩

/-- **gamma at class 345, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_345`
consumed through `join50`. -/
theorem chjoin_345 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_345) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_345 (85/66 : ℝ) (115/74 : ℝ) castAB_345 hIn.1 Fresh.ChamberDatasheet.chds_345 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 345's own tuple (atom `chds_345` + proved join `inclass_345` +
`chjoin_345`). -/
theorem dead_345 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_345 s :=
  chjoin_345 rho_345 s hs h50 inclass_345

/-- jj#346 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=23/14 | D2 | 1728 cases | NO-ALIVE-ON-GRID -/
def cls_346 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 346 (exact rationals, the probe's own
case dump). -/
def rho_346 : Fin 5 → ℚ := ![1, 1, 7, 13, 14]

theorem castAB_346 : ((cls_346.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_346.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_346]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_346`/`cls_346` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_346 : InClass rho_346 cls_346 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_346, rho_346] <;> norm_num⟩

/-- **gamma at class 346, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_346`
consumed through `join50`. -/
theorem chjoin_346 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_346) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_346 (17/13 : ℝ) (23/14 : ℝ) castAB_346 hIn.1 Fresh.ChamberDatasheet.chds_346 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 346's own tuple (atom `chds_346` + proved join `inclass_346` +
`chjoin_346`). -/
theorem dead_346 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_346 s :=
  chjoin_346 rho_346 s hs h50 inclass_346

/-- jj#347 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/66 b=23/14 | D2 | 1728 cases | NO-ALIVE-ON-GRID -/
def cls_347 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/66 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 347 (exact rationals, the probe's own
case dump). -/
def rho_347 : Fin 5 → ℚ := ![1, 1, 7, 66/5, 14]

theorem castAB_347 : ((cls_347.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_347.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_347]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_347`/`cls_347` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_347 : InClass rho_347 cls_347 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_347, rho_347] <;> norm_num⟩

/-- **gamma at class 347, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_347`
consumed through `join50`. -/
theorem chjoin_347 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_347) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_347 (85/66 : ℝ) (23/14 : ℝ) castAB_347 hIn.1 Fresh.ChamberDatasheet.chds_347 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 347's own tuple (atom `chds_347` + proved join `inclass_347` +
`chjoin_347`). -/
theorem dead_347 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_347 s :=
  chjoin_347 rho_347 s hs h50 inclass_347

/-- jj#348 | PS1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/14 | D2 | 1728 cases | NO-ALIVE-ON-GRID -/
def cls_348 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/14 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 348 (exact rationals, the probe's own
case dump). -/
def rho_348 : Fin 5 → ℚ := ![1, 7, 9, 63/5, 14]

theorem castAB_348 : ((cls_348.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_348.B : ℚ) : ℝ) = (23/14 : ℝ) := by
  norm_num [cls_348]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_348`/`cls_348` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_348 : InClass rho_348 cls_348 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_348, rho_348] <;> norm_num⟩

/-- **gamma at class 348, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_348`
consumed through `join50`. -/
theorem chjoin_348 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_348) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_348 (85/63 : ℝ) (23/14 : ℝ) castAB_348 hIn.1 Fresh.ChamberDatasheet.chds_348 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 348's own tuple (atom `chds_348` + proved join `inclass_348` +
`chjoin_348`). -/
theorem dead_348 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_348 s :=
  chjoin_348 rho_348 s hs h50 inclass_348

/-- jj#349 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/76 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_349 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/76 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 349 (exact rationals, the probe's own
case dump). -/
def rho_349 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 76/5]

theorem castAB_349 : ((cls_349.A : ℚ) : ℝ) = (85/76 : ℝ) ∧ ((cls_349.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_349]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_349`/`cls_349` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_349 : InClass rho_349 cls_349 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_349, rho_349] <;> norm_num⟩

/-- **gamma at class 349, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_349`
consumed through `join50`. -/
theorem chjoin_349 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_349) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_349 (85/76 : ℝ) (75/56 : ℝ) castAB_349 hIn.1 Fresh.ChamberDatasheet.chds_349 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 349's own tuple (atom `chds_349` + proved join `inclass_349` +
`chjoin_349`). -/
theorem dead_349 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_349 s :=
  chjoin_349 rho_349 s hs h50 inclass_349

/-- jj#350 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/77 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_350 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/77 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 350 (exact rationals, the probe's own
case dump). -/
def rho_350 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 77/5]

theorem castAB_350 : ((cls_350.A : ℚ) : ℝ) = (85/77 : ℝ) ∧ ((cls_350.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_350]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_350`/`cls_350` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_350 : InClass rho_350 cls_350 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_350, rho_350] <;> norm_num⟩

/-- **gamma at class 350, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_350`
consumed through `join50`. -/
theorem chjoin_350 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_350) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_350 (85/77 : ℝ) (75/56 : ℝ) castAB_350 hIn.1 Fresh.ChamberDatasheet.chds_350 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 350's own tuple (atom `chds_350` + proved join `inclass_350` +
`chjoin_350`). -/
theorem dead_350 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_350 s :=
  chjoin_350 rho_350 s hs h50 inclass_350

/-- jj#351 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/78 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_351 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/78 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 351 (exact rationals, the probe's own
case dump). -/
def rho_351 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 78/5]

theorem castAB_351 : ((cls_351.A : ℚ) : ℝ) = (85/78 : ℝ) ∧ ((cls_351.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_351]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_351`/`cls_351` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_351 : InClass rho_351 cls_351 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_351, rho_351] <;> norm_num⟩

/-- **gamma at class 351, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_351`
consumed through `join50`. -/
theorem chjoin_351 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_351) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_351 (85/78 : ℝ) (75/56 : ℝ) castAB_351 hIn.1 Fresh.ChamberDatasheet.chds_351 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 351's own tuple (atom `chds_351` + proved join `inclass_351` +
`chjoin_351`). -/
theorem dead_351 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_351 s :=
  chjoin_351 rho_351 s hs h50 inclass_351

/-- jj#352 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/79 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_352 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/79 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 352 (exact rationals, the probe's own
case dump). -/
def rho_352 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 79/5]

theorem castAB_352 : ((cls_352.A : ℚ) : ℝ) = (85/79 : ℝ) ∧ ((cls_352.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_352]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_352`/`cls_352` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_352 : InClass rho_352 cls_352 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_352, rho_352] <;> norm_num⟩

/-- **gamma at class 352, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_352`
consumed through `join50`. -/
theorem chjoin_352 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_352) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_352 (85/79 : ℝ) (75/56 : ℝ) castAB_352 hIn.1 Fresh.ChamberDatasheet.chds_352 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 352's own tuple (atom `chds_352` + proved join `inclass_352` +
`chjoin_352`). -/
theorem dead_352 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_352 s :=
  chjoin_352 rho_352 s hs h50 inclass_352

/-- jj#353 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_353 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 353 (exact rationals, the probe's own
case dump). -/
def rho_353 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 16]

theorem castAB_353 : ((cls_353.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_353.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_353]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_353`/`cls_353` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_353 : InClass rho_353 cls_353 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_353, rho_353] <;> norm_num⟩

/-- **gamma at class 353, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_353`
consumed through `join50`. -/
theorem chjoin_353 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_353) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_353 (17/16 : ℝ) (75/56 : ℝ) castAB_353 hIn.1 Fresh.ChamberDatasheet.chds_353 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 353's own tuple (atom `chds_353` + proved join `inclass_353` +
`chjoin_353`). -/
theorem dead_353 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_353 s :=
  chjoin_353 rho_353 s hs h50 inclass_353

/-- jj#354 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/81 b=75/56 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_354 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/81 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 354 (exact rationals, the probe's own
case dump). -/
def rho_354 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 81/5]

theorem castAB_354 : ((cls_354.A : ℚ) : ℝ) = (85/81 : ℝ) ∧ ((cls_354.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_354]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_354`/`cls_354` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_354 : InClass rho_354 cls_354 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_354, rho_354] <;> norm_num⟩

/-- **gamma at class 354, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_354`
consumed through `join50`. -/
theorem chjoin_354 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_354) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_354 (85/81 : ℝ) (75/56 : ℝ) castAB_354 hIn.1 Fresh.ChamberDatasheet.chds_354 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 354's own tuple (atom `chds_354` + proved join `inclass_354` +
`chjoin_354`). -/
theorem dead_354 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_354 s :=
  chjoin_354 rho_354 s hs h50 inclass_354

/-- jj#355 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/82 b=75/56 | D1 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_355 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/82 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 355 (exact rationals, the probe's own
case dump). -/
def rho_355 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 82/5]

theorem castAB_355 : ((cls_355.A : ℚ) : ℝ) = (85/82 : ℝ) ∧ ((cls_355.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_355]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_355`/`cls_355` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_355 : InClass rho_355 cls_355 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_355, rho_355] <;> norm_num⟩

/-- **gamma at class 355, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_355`
consumed through `join50`. -/
theorem chjoin_355 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_355) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_355 (85/82 : ℝ) (75/56 : ℝ) castAB_355 hIn.1 Fresh.ChamberDatasheet.chds_355 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 355's own tuple (atom `chds_355` + proved join `inclass_355` +
`chjoin_355`). -/
theorem dead_355 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_355 s :=
  chjoin_355 rho_355 s hs h50 inclass_355

/-- jj#356 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/83 b=75/56 | D1 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_356 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/83 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 356 (exact rationals, the probe's own
case dump). -/
def rho_356 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 83/5]

theorem castAB_356 : ((cls_356.A : ℚ) : ℝ) = (85/83 : ℝ) ∧ ((cls_356.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_356]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_356`/`cls_356` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_356 : InClass rho_356 cls_356 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_356, rho_356] <;> norm_num⟩

/-- **gamma at class 356, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_356`
consumed through `join50`. -/
theorem chjoin_356 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_356) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_356 (85/83 : ℝ) (75/56 : ℝ) castAB_356 hIn.1 Fresh.ChamberDatasheet.chds_356 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 356's own tuple (atom `chds_356` + proved join `inclass_356` +
`chjoin_356`). -/
theorem dead_356 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_356 s :=
  chjoin_356 rho_356 s hs h50 inclass_356

/-- jj#357 | PG1G1G1S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=85/84 b=75/56 | D1 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_357 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/84 : ℚ), B := (75/56 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 357 (exact rationals, the probe's own
case dump). -/
def rho_357 : Fin 5 → ℚ := ![1, 9, 9, 56/5, 84/5]

theorem castAB_357 : ((cls_357.A : ℚ) : ℝ) = (85/84 : ℝ) ∧ ((cls_357.B : ℚ) : ℝ) = (75/56 : ℝ) := by
  norm_num [cls_357]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_357`/`cls_357` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_357 : InClass rho_357 cls_357 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_357, rho_357] <;> norm_num⟩

/-- **gamma at class 357, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_357`
consumed through `join50`. -/
theorem chjoin_357 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_357) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_357 (85/84 : ℝ) (75/56 : ℝ) castAB_357 hIn.1 Fresh.ChamberDatasheet.chds_357 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 357's own tuple (atom `chds_357` + proved join `inclass_357` +
`chjoin_357`). -/
theorem dead_357 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_357 s :=
  chjoin_357 rho_357 s hs h50 inclass_357

/-- jj#358 | PG1G1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=25/19 | D2 | 1716 cases | NO-ALIVE-ON-GRID -/
def cls_358 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (25/19 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 358 (exact rationals, the probe's own
case dump). -/
def rho_358 : Fin 5 → ℚ := ![1, 9, 57/5, 16, 16]

theorem castAB_358 : ((cls_358.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_358.B : ℚ) : ℝ) = (25/19 : ℝ) := by
  norm_num [cls_358]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_358`/`cls_358` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_358 : InClass rho_358 cls_358 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_358, rho_358] <;> norm_num⟩

/-- **gamma at class 358, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_358`
consumed through `join50`. -/
theorem chjoin_358 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_358) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_358 (17/16 : ℝ) (25/19 : ℝ) castAB_358 hIn.1 Fresh.ChamberDatasheet.chds_358 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 358's own tuple (atom `chds_358` + proved join `inclass_358` +
`chjoin_358`). -/
theorem dead_358 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_358 s :=
  chjoin_358 rho_358 s hs h50 inclass_358

/-- jj#359 | PPS1S1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=75/49 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_359 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 1, 7, 7, 9], hi := ![7, 7, 9, 9, 15] }

/-- The recorded representative 5-tuple of class 359 (exact rationals, the probe's own
case dump). -/
def rho_359 : Fin 5 → ℚ := ![1, 1, 36/5, 36/5, 49/5]

theorem castAB_359 : ((cls_359.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_359.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_359]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_359`/`cls_359` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_359 : InClass rho_359 cls_359 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_359, rho_359] <;> norm_num⟩

/-- **gamma at class 359, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_359`
consumed through `join50`. -/
theorem chjoin_359 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_359) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_359 (5/4 : ℝ) (75/49 : ℝ) castAB_359 hIn.1 Fresh.ChamberDatasheet.chds_359 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 359's own tuple (atom `chds_359` + proved join `inclass_359` +
`chjoin_359`). -/
theorem dead_359 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_359 s :=
  chjoin_359 rho_359 s hs h50 inclass_359

/-- jj#360 | PPS1S1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=3/2 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_360 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 7, 7, 9], hi := ![7, 7, 9, 9, 15] }

/-- The recorded representative 5-tuple of class 360 (exact rationals, the probe's own
case dump). -/
def rho_360 : Fin 5 → ℚ := ![1, 1, 37/5, 37/5, 10]

theorem castAB_360 : ((cls_360.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_360.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_360]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_360`/`cls_360` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_360 : InClass rho_360 cls_360 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_360, rho_360] <;> norm_num⟩

/-- **gamma at class 360, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_360`
consumed through `join50`. -/
theorem chjoin_360 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_360) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_360 (45/37 : ℝ) (3/2 : ℝ) castAB_360 hIn.1 Fresh.ChamberDatasheet.chds_360 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 360's own tuple (atom `chds_360` + proved join `inclass_360` +
`chjoin_360`). -/
theorem dead_360 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_360 s :=
  chjoin_360 rho_360 s hs h50 inclass_360

/-- jj#361 | PPS1S1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/37 b=25/17 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_361 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/37 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 7, 9], hi := ![7, 7, 9, 9, 15] }

/-- The recorded representative 5-tuple of class 361 (exact rationals, the probe's own
case dump). -/
def rho_361 : Fin 5 → ℚ := ![1, 1, 37/5, 37/5, 51/5]

theorem castAB_361 : ((cls_361.A : ℚ) : ℝ) = (45/37 : ℝ) ∧ ((cls_361.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_361]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_361`/`cls_361` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_361 : InClass rho_361 cls_361 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_361, rho_361] <;> norm_num⟩

/-- **gamma at class 361, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_361`
consumed through `join50`. -/
theorem chjoin_361 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_361) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_361 (45/37 : ℝ) (25/17 : ℝ) castAB_361 hIn.1 Fresh.ChamberDatasheet.chds_361 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 361's own tuple (atom `chds_361` + proved join `inclass_361` +
`chjoin_361`). -/
theorem dead_361 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_361 s :=
  chjoin_361 rho_361 s hs h50 inclass_361

/-- jj#362 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=5/3 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_362 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (5/3 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 362 (exact rationals, the probe's own
case dump). -/
def rho_362 : Fin 5 → ℚ := ![1, 1, 7, 63/5, 69/5]

theorem castAB_362 : ((cls_362.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_362.B : ℚ) : ℝ) = (5/3 : ℝ) := by
  norm_num [cls_362]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_362`/`cls_362` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_362 : InClass rho_362 cls_362 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_362, rho_362] <;> norm_num⟩

/-- **gamma at class 362, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_362`
consumed through `join50`. -/
theorem chjoin_362 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_362) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_362 (85/63 : ℝ) (5/3 : ℝ) castAB_362 hIn.1 Fresh.ChamberDatasheet.chds_362 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 362's own tuple (atom `chds_362` + proved join `inclass_362` +
`chjoin_362`). -/
theorem dead_362 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_362 s :=
  chjoin_362 rho_362 s hs h50 inclass_362

/-- jj#363 | PPS1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/64 b=5/3 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_363 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/64 : ℚ), B := (5/3 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 363 (exact rationals, the probe's own
case dump). -/
def rho_363 : Fin 5 → ℚ := ![1, 1, 7, 64/5, 69/5]

theorem castAB_363 : ((cls_363.A : ℚ) : ℝ) = (85/64 : ℝ) ∧ ((cls_363.B : ℚ) : ℝ) = (5/3 : ℝ) := by
  norm_num [cls_363]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_363`/`cls_363` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_363 : InClass rho_363 cls_363 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_363, rho_363] <;> norm_num⟩

/-- **gamma at class 363, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_363`
consumed through `join50`. -/
theorem chjoin_363 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_363) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_363 (85/64 : ℝ) (5/3 : ℝ) castAB_363 hIn.1 Fresh.ChamberDatasheet.chds_363 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 363's own tuple (atom `chds_363` + proved join `inclass_363` +
`chjoin_363`). -/
theorem dead_363 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_363 s :=
  chjoin_363 rho_363 s hs h50 inclass_363

/-- jj#364 | PPS1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=15/13 b=25/17 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_364 : ChamberClass :=
  { kL := 1, kR := 2, A := (15/13 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 1, 7, 9, 9], hi := ![7, 7, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 364 (exact rationals, the probe's own
case dump). -/
def rho_364 : Fin 5 → ℚ := ![1, 1, 39/5, 9, 51/5]

theorem castAB_364 : ((cls_364.A : ℚ) : ℝ) = (15/13 : ℝ) ∧ ((cls_364.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_364]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_364`/`cls_364` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_364 : InClass rho_364 cls_364 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_364, rho_364] <;> norm_num⟩

/-- **gamma at class 364, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_364`
consumed through `join50`. -/
theorem chjoin_364 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_364) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_364 (15/13 : ℝ) (25/17 : ℝ) castAB_364 hIn.1 Fresh.ChamberDatasheet.chds_364 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 364's own tuple (atom `chds_364` + proved join `inclass_364` +
`chjoin_364`). -/
theorem dead_364 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_364 s :=
  chjoin_364 rho_364 s hs h50 inclass_364

/-- jj#365 | PPG1G1G1 | kL=2 kR=2 | cL=G1 cR=G1 | a=85/73 b=3/2 | D1 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_365 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/73 : ℚ), B := (3/2 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 365 (exact rationals, the probe's own
case dump). -/
def rho_365 : Fin 5 → ℚ := ![1, 1, 9, 10, 73/5]

theorem castAB_365 : ((cls_365.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_365.B : ℚ) : ℝ) = (3/2 : ℝ) := by
  norm_num [cls_365]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_365`/`cls_365` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_365 : InClass rho_365 cls_365 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_365, rho_365] <;> norm_num⟩

/-- **gamma at class 365, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_365`
consumed through `join50`. -/
theorem chjoin_365 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_365) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_365 (85/73 : ℝ) (3/2 : ℝ) castAB_365 hIn.1 Fresh.ChamberDatasheet.chds_365 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 365's own tuple (atom `chds_365` + proved join `inclass_365` +
`chjoin_365`). -/
theorem dead_365 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_365 s :=
  chjoin_365 rho_365 s hs h50 inclass_365

/-- jj#366 | PPG1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=17/13 b=115/72 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_366 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/13 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 9, 9, 9], hi := ![7, 7, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 366 (exact rationals, the probe's own
case dump). -/
def rho_366 : Fin 5 → ℚ := ![1, 1, 9, 13, 72/5]

theorem castAB_366 : ((cls_366.A : ℚ) : ℝ) = (17/13 : ℝ) ∧ ((cls_366.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_366]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_366`/`cls_366` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_366 : InClass rho_366 cls_366 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_366, rho_366] <;> norm_num⟩

/-- **gamma at class 366, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_366`
consumed through `join50`. -/
theorem chjoin_366 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_366) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_366 (17/13 : ℝ) (115/72 : ℝ) castAB_366 hIn.1 Fresh.ChamberDatasheet.chds_366 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 366's own tuple (atom `chds_366` + proved join `inclass_366` +
`chjoin_366`). -/
theorem dead_366 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_366 s :=
  chjoin_366 rho_366 s hs h50 inclass_366

/-- jj#367 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/76 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_367 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/76 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 367 (exact rationals, the probe's own
case dump). -/
def rho_367 : Fin 5 → ℚ := ![1, 1, 9, 72/5, 76/5]

theorem castAB_367 : ((cls_367.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_367.B : ℚ) : ℝ) = (115/76 : ℝ) := by
  norm_num [cls_367]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_367`/`cls_367` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_367 : InClass rho_367 cls_367 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_367, rho_367] <;> norm_num⟩

/-- **gamma at class 367, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_367`
consumed through `join50`. -/
theorem chjoin_367 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_367) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_367 (85/72 : ℝ) (115/76 : ℝ) castAB_367 hIn.1 Fresh.ChamberDatasheet.chds_367 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 367's own tuple (atom `chds_367` + proved join `inclass_367` +
`chjoin_367`). -/
theorem dead_367 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_367 s :=
  chjoin_367 rho_367 s hs h50 inclass_367

/-- jj#368 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/77 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_368 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/77 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 368 (exact rationals, the probe's own
case dump). -/
def rho_368 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 77/5]

theorem castAB_368 : ((cls_368.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_368.B : ℚ) : ℝ) = (115/77 : ℝ) := by
  norm_num [cls_368]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_368`/`cls_368` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_368 : InClass rho_368 cls_368 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_368, rho_368] <;> norm_num⟩

/-- **gamma at class 368, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_368`
consumed through `join50`. -/
theorem chjoin_368 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_368) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_368 (85/73 : ℝ) (115/77 : ℝ) castAB_368 hIn.1 Fresh.ChamberDatasheet.chds_368 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 368's own tuple (atom `chds_368` + proved join `inclass_368` +
`chjoin_368`). -/
theorem dead_368 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_368 s :=
  chjoin_368 rho_368 s hs h50 inclass_368

/-- jj#369 | PPG1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/78 | D2 | 1710 cases | NO-ALIVE-ON-GRID -/
def cls_369 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/78 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 369 (exact rationals, the probe's own
case dump). -/
def rho_369 : Fin 5 → ℚ := ![1, 1, 9, 73/5, 78/5]

theorem castAB_369 : ((cls_369.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_369.B : ℚ) : ℝ) = (115/78 : ℝ) := by
  norm_num [cls_369]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_369`/`cls_369` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_369 : InClass rho_369 cls_369 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_369, rho_369] <;> norm_num⟩

/-- **gamma at class 369, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_369`
consumed through `join50`. -/
theorem chjoin_369 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_369) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_369 (85/73 : ℝ) (115/78 : ℝ) castAB_369 hIn.1 Fresh.ChamberDatasheet.chds_369 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 369's own tuple (atom `chds_369` + proved join `inclass_369` +
`chjoin_369`). -/
theorem dead_369 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_369 s :=
  chjoin_369 rho_369 s hs h50 inclass_369

/-- jj#370 | PG1G1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 1694 cases | NO-ALIVE-ON-GRID -/
def cls_370 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 370 (exact rationals, the probe's own
case dump). -/
def rho_370 : Fin 5 → ℚ := ![1, 9, 62/5, 72/5, 17]

theorem castAB_370 : ((cls_370.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_370.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_370]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_370`/`cls_370` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_370 : InClass rho_370 cls_370 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_370, rho_370] <;> norm_num⟩

/-- **gamma at class 370, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_370`
consumed through `join50`. -/
theorem chjoin_370 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_370) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_370 (25/17 : ℝ) (115/72 : ℝ) castAB_370 hIn.1 Fresh.ChamberDatasheet.chds_370 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 370's own tuple (atom `chds_370` + proved join `inclass_370` +
`chjoin_370`). -/
theorem dead_370 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_370 s :=
  chjoin_370 rho_370 s hs h50 inclass_370

/-- jj#371 | PG1G1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 1694 cases | NO-ALIVE-ON-GRID -/
def cls_371 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 9, 9, 9, 17], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 371 (exact rationals, the probe's own
case dump). -/
def rho_371 : Fin 5 → ℚ := ![1, 9, 62/5, 72/5, 17]

theorem castAB_371 : ((cls_371.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_371.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_371]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_371`/`cls_371` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_371 : InClass rho_371 cls_371 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_371, rho_371] <;> norm_num⟩

/-- **gamma at class 371, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_371`
consumed through `join50`. -/
theorem chjoin_371 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_371) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_371 (25/17 : ℝ) (115/72 : ℝ) castAB_371 hIn.1 Fresh.ChamberDatasheet.chds_371 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 371's own tuple (atom `chds_371` + proved join `inclass_371` +
`chjoin_371`). -/
theorem dead_371 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_371 s :=
  chjoin_371 rho_371 s hs h50 inclass_371

/-- jj#372 | S1G1G1G1G1 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 1683 cases | NO-ALIVE-ON-GRID -/
def cls_372 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![7, 9, 9, 9, 9], hi := ![9, 15, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 372 (exact rationals, the probe's own
case dump). -/
def rho_372 : Fin 5 → ℚ := ![7, 9, 9, 63/5, 15]

theorem castAB_372 : ((cls_372.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_372.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_372]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_372`/`cls_372` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_372 : InClass rho_372 cls_372 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_372, rho_372] <;> norm_num⟩

/-- **gamma at class 372, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_372`
consumed through `join50`. -/
theorem chjoin_372 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_372) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_372 (85/63 : ℝ) (23/15 : ℝ) castAB_372 hIn.1 Fresh.ChamberDatasheet.chds_372 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 372's own tuple (atom `chds_372` + proved join `inclass_372` +
`chjoin_372`). -/
theorem dead_372 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_372 s :=
  chjoin_372 rho_372 s hs h50 inclass_372

/-- jj#373 | S1G1G1G1S2 | kL=2 kR=3 | cL=G1 cR=G1 | a=85/63 b=23/15 | D2 | 1683 cases | NO-ALIVE-ON-GRID -/
def cls_373 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/63 : ℚ), B := (23/15 : ℚ),
    lo := ![7, 9, 9, 9, 15], hi := ![9, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 373 (exact rationals, the probe's own
case dump). -/
def rho_373 : Fin 5 → ℚ := ![7, 9, 9, 63/5, 15]

theorem castAB_373 : ((cls_373.A : ℚ) : ℝ) = (85/63 : ℝ) ∧ ((cls_373.B : ℚ) : ℝ) = (23/15 : ℝ) := by
  norm_num [cls_373]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_373`/`cls_373` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_373 : InClass rho_373 cls_373 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_373, rho_373] <;> norm_num⟩

/-- **gamma at class 373, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_373`
consumed through `join50`. -/
theorem chjoin_373 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_373) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_373 (85/63 : ℝ) (23/15 : ℝ) castAB_373 hIn.1 Fresh.ChamberDatasheet.chds_373 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 373's own tuple (atom `chds_373` + proved join `inclass_373` +
`chjoin_373`). -/
theorem dead_373 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_373 s :=
  chjoin_373 rho_373 s hs h50 inclass_373

/-- jj#374 | PPG1G1S2 | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 1682 cases | NO-ALIVE-ON-GRID -/
def cls_374 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 374 (exact rationals, the probe's own
case dump). -/
def rho_374 : Fin 5 → ℚ := ![1, 1, 62/5, 72/5, 17]

theorem castAB_374 : ((cls_374.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_374.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_374]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_374`/`cls_374` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_374 : InClass rho_374 cls_374 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_374, rho_374] <;> norm_num⟩

/-- **gamma at class 374, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_374`
consumed through `join50`. -/
theorem chjoin_374 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_374) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_374 (25/17 : ℝ) (115/72 : ℝ) castAB_374 hIn.1 Fresh.ChamberDatasheet.chds_374 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 374's own tuple (atom `chds_374` + proved join `inclass_374` +
`chjoin_374`). -/
theorem dead_374 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_374 s :=
  chjoin_374 rho_374 s hs h50 inclass_374

/-- jj#375 | PPG1G1E | kL=3 kR=3 | cL=E cR=G1 | a=25/17 b=115/72 | D2 | 1682 cases | NO-ALIVE-ON-GRID -/
def cls_375 : ChamberClass :=
  { kL := 3, kR := 3, A := (25/17 : ℚ), B := (115/72 : ℚ),
    lo := ![1, 1, 9, 9, 17], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 375 (exact rationals, the probe's own
case dump). -/
def rho_375 : Fin 5 → ℚ := ![1, 1, 62/5, 72/5, 17]

theorem castAB_375 : ((cls_375.A : ℚ) : ℝ) = (25/17 : ℝ) ∧ ((cls_375.B : ℚ) : ℝ) = (115/72 : ℝ) := by
  norm_num [cls_375]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_375`/`cls_375` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_375 : InClass rho_375 cls_375 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_375, rho_375] <;> norm_num⟩

/-- **gamma at class 375, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_375`
consumed through `join50`. -/
theorem chjoin_375 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_375) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_375 (25/17 : ℝ) (115/72 : ℝ) castAB_375 hIn.1 Fresh.ChamberDatasheet.chds_375 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 375's own tuple (atom `chds_375` + proved join `inclass_375` +
`chjoin_375`). -/
theorem dead_375 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_375 s :=
  chjoin_375 rho_375 s hs h50 inclass_375

/-- jj#376 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/82 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_376 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 376 (exact rationals, the probe's own
case dump). -/
def rho_376 : Fin 5 → ℚ := ![1, 1, 72/5, 15, 82/5]

theorem castAB_376 : ((cls_376.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_376.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_376]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_376`/`cls_376` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_376 : InClass rho_376 cls_376 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_376, rho_376] <;> norm_num⟩

/-- **gamma at class 376, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_376`
consumed through `join50`. -/
theorem chjoin_376 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_376) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_376 (85/72 : ℝ) (115/82 : ℝ) castAB_376 hIn.1 Fresh.ChamberDatasheet.chds_376 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 376's own tuple (atom `chds_376` + proved join `inclass_376` +
`chjoin_376`). -/
theorem dead_376 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_376 s :=
  chjoin_376 rho_376 s hs h50 inclass_376

/-- jj#377 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/82 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_377 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 377 (exact rationals, the probe's own
case dump). -/
def rho_377 : Fin 5 → ℚ := ![1, 1, 73/5, 15, 82/5]

theorem castAB_377 : ((cls_377.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_377.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_377]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_377`/`cls_377` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_377 : InClass rho_377 cls_377 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_377, rho_377] <;> norm_num⟩

/-- **gamma at class 377, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_377`
consumed through `join50`. -/
theorem chjoin_377 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_377) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_377 (85/73 : ℝ) (115/82 : ℝ) castAB_377 hIn.1 Fresh.ChamberDatasheet.chds_377 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 377's own tuple (atom `chds_377` + proved join `inclass_377` +
`chjoin_377`). -/
theorem dead_377 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_377 s :=
  chjoin_377 rho_377 s hs h50 inclass_377

/-- jj#378 | PPG1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/82 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_378 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 378 (exact rationals, the probe's own
case dump). -/
def rho_378 : Fin 5 → ℚ := ![1, 1, 74/5, 15, 82/5]

theorem castAB_378 : ((cls_378.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_378.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_378]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_378`/`cls_378` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_378 : InClass rho_378 cls_378 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_378, rho_378] <;> norm_num⟩

/-- **gamma at class 378, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_378`
consumed through `join50`. -/
theorem chjoin_378 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_378) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_378 (85/74 : ℝ) (115/82 : ℝ) castAB_378 hIn.1 Fresh.ChamberDatasheet.chds_378 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 378's own tuple (atom `chds_378` + proved join `inclass_378` +
`chjoin_378`). -/
theorem dead_378 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_378 s :=
  chjoin_378 rho_378 s hs h50 inclass_378

/-- jj#379 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=23/16 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_379 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/16 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 379 (exact rationals, the probe's own
case dump). -/
def rho_379 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 16]

theorem castAB_379 : ((cls_379.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_379.B : ℚ) : ℝ) = (23/16 : ℝ) := by
  norm_num [cls_379]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_379`/`cls_379` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_379 : InClass rho_379 cls_379 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_379, rho_379] <;> norm_num⟩

/-- **gamma at class 379, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_379`
consumed through `join50`. -/
theorem chjoin_379 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_379) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_379 (85/72 : ℝ) (23/16 : ℝ) castAB_379 hIn.1 Fresh.ChamberDatasheet.chds_379 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 379's own tuple (atom `chds_379` + proved join `inclass_379` +
`chjoin_379`). -/
theorem dead_379 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_379 s :=
  chjoin_379 rho_379 s hs h50 inclass_379

/-- jj#380 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/81 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_380 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/81 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 380 (exact rationals, the probe's own
case dump). -/
def rho_380 : Fin 5 → ℚ := ![1, 39/5, 9, 72/5, 81/5]

theorem castAB_380 : ((cls_380.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_380.B : ℚ) : ℝ) = (115/81 : ℝ) := by
  norm_num [cls_380]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_380`/`cls_380` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_380 : InClass rho_380 cls_380 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_380, rho_380] <;> norm_num⟩

/-- **gamma at class 380, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_380`
consumed through `join50`. -/
theorem chjoin_380 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_380) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_380 (85/72 : ℝ) (115/81 : ℝ) castAB_380 hIn.1 Fresh.ChamberDatasheet.chds_380 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 380's own tuple (atom `chds_380` + proved join `inclass_380` +
`chjoin_380`). -/
theorem dead_380 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_380 s :=
  chjoin_380 rho_380 s hs h50 inclass_380

/-- jj#381 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/82 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_381 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/82 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 381 (exact rationals, the probe's own
case dump). -/
def rho_381 : Fin 5 → ℚ := ![1, 39/5, 9, 73/5, 82/5]

theorem castAB_381 : ((cls_381.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_381.B : ℚ) : ℝ) = (115/82 : ℝ) := by
  norm_num [cls_381]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_381`/`cls_381` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_381 : InClass rho_381 cls_381 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_381, rho_381] <;> norm_num⟩

/-- **gamma at class 381, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_381`
consumed through `join50`. -/
theorem chjoin_381 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_381) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_381 (85/73 : ℝ) (115/82 : ℝ) castAB_381 hIn.1 Fresh.ChamberDatasheet.chds_381 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 381's own tuple (atom `chds_381` + proved join `inclass_381` +
`chjoin_381`). -/
theorem dead_381 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_381 s :=
  chjoin_381 rho_381 s hs h50 inclass_381

/-- jj#382 | PG1G1S2S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/81 | D2 | 1680 cases | NO-ALIVE-ON-GRID -/
def cls_382 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/81 : ℚ),
    lo := ![1, 9, 9, 15, 15], hi := ![7, 15, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 382 (exact rationals, the probe's own
case dump). -/
def rho_382 : Fin 5 → ℚ := ![1, 9, 72/5, 15, 81/5]

theorem castAB_382 : ((cls_382.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_382.B : ℚ) : ℝ) = (115/81 : ℝ) := by
  norm_num [cls_382]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_382`/`cls_382` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_382 : InClass rho_382 cls_382 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_382, rho_382] <;> norm_num⟩

/-- **gamma at class 382, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_382`
consumed through `join50`. -/
theorem chjoin_382 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_382) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_382 (85/72 : ℝ) (115/81 : ℝ) castAB_382 hIn.1 Fresh.ChamberDatasheet.chds_382 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 382's own tuple (atom `chds_382` + proved join `inclass_382` +
`chjoin_382`). -/
theorem dead_382 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_382 s :=
  chjoin_382 rho_382 s hs h50 inclass_382

/-- jj#383 | PS1S1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=45/38 b=25/17 | D2 | 1672 cases | NO-ALIVE-ON-GRID -/
def cls_383 : ChamberClass :=
  { kL := 1, kR := 2, A := (45/38 : ℚ), B := (25/17 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 383 (exact rationals, the probe's own
case dump). -/
def rho_383 : Fin 5 → ℚ := ![1, 38/5, 38/5, 9, 51/5]

theorem castAB_383 : ((cls_383.A : ℚ) : ℝ) = (45/38 : ℝ) ∧ ((cls_383.B : ℚ) : ℝ) = (25/17 : ℝ) := by
  norm_num [cls_383]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_383`/`cls_383` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_383 : InClass rho_383 cls_383 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_383, rho_383] <;> norm_num⟩

/-- **gamma at class 383, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_383`
consumed through `join50`. -/
theorem chjoin_383 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_383) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_383 (45/38 : ℝ) (25/17 : ℝ) castAB_383 hIn.1 Fresh.ChamberDatasheet.chds_383 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 383's own tuple (atom `chds_383` + proved join `inclass_383` +
`chjoin_383`). -/
theorem dead_383 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_383 s :=
  chjoin_383 rho_383 s hs h50 inclass_383

/-- jj#384 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=17/14 b=115/76 | D2 | 1672 cases | NO-ALIVE-ON-GRID -/
def cls_384 : ChamberClass :=
  { kL := 2, kR := 3, A := (17/14 : ℚ), B := (115/76 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 384 (exact rationals, the probe's own
case dump). -/
def rho_384 : Fin 5 → ℚ := ![1, 38/5, 9, 14, 76/5]

theorem castAB_384 : ((cls_384.A : ℚ) : ℝ) = (17/14 : ℝ) ∧ ((cls_384.B : ℚ) : ℝ) = (115/76 : ℝ) := by
  norm_num [cls_384]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_384`/`cls_384` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_384 : InClass rho_384 cls_384 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_384, rho_384] <;> norm_num⟩

/-- **gamma at class 384, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_384`
consumed through `join50`. -/
theorem chjoin_384 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_384) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_384 (17/14 : ℝ) (115/76 : ℝ) castAB_384 hIn.1 Fresh.ChamberDatasheet.chds_384 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 384's own tuple (atom `chds_384` + proved join `inclass_384` +
`chjoin_384`). -/
theorem dead_384 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_384 s :=
  chjoin_384 rho_384 s hs h50 inclass_384

/-- jj#385 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/71 b=115/77 | D2 | 1672 cases | NO-ALIVE-ON-GRID -/
def cls_385 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/71 : ℚ), B := (115/77 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 385 (exact rationals, the probe's own
case dump). -/
def rho_385 : Fin 5 → ℚ := ![1, 38/5, 9, 71/5, 77/5]

theorem castAB_385 : ((cls_385.A : ℚ) : ℝ) = (85/71 : ℝ) ∧ ((cls_385.B : ℚ) : ℝ) = (115/77 : ℝ) := by
  norm_num [cls_385]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_385`/`cls_385` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_385 : InClass rho_385 cls_385 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_385, rho_385] <;> norm_num⟩

/-- **gamma at class 385, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_385`
consumed through `join50`. -/
theorem chjoin_385 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_385) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_385 (85/71 : ℝ) (115/77 : ℝ) castAB_385 hIn.1 Fresh.ChamberDatasheet.chds_385 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 385's own tuple (atom `chds_385` + proved join `inclass_385` +
`chjoin_385`). -/
theorem dead_385 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_385 s :=
  chjoin_385 rho_385 s hs h50 inclass_385

/-- jj#386 | PPG1G1S2 | kL=2 kR=4 | cL=G1 cR=S2 | a=17/9 b=155/77 | D2 | 1666 cases | NO-ALIVE-ON-GRID -/
def cls_386 : ChamberClass :=
  { kL := 2, kR := 4, A := (17/9 : ℚ), B := (155/77 : ℚ),
    lo := ![1, 1, 9, 9, 15], hi := ![7, 7, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 386 (exact rationals, the probe's own
case dump). -/
def rho_386 : Fin 5 → ℚ := ![1, 27/5, 9, 67/5, 77/5]

theorem castAB_386 : ((cls_386.A : ℚ) : ℝ) = (17/9 : ℝ) ∧ ((cls_386.B : ℚ) : ℝ) = (155/77 : ℝ) := by
  norm_num [cls_386]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_386`/`cls_386` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_386 : InClass rho_386 cls_386 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_386, rho_386] <;> norm_num⟩

/-- **gamma at class 386, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_386`
consumed through `join50`. -/
theorem chjoin_386 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_386) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_386 (17/9 : ℝ) (155/77 : ℝ) castAB_386 hIn.1 Fresh.ChamberDatasheet.chds_386 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 386's own tuple (atom `chds_386` + proved join `inclass_386` +
`chjoin_386`). -/
theorem dead_386 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_386 s :=
  chjoin_386 rho_386 s hs h50 inclass_386

/-- jj#387 | PPG1S2S2 | kL=2 kR=2 | cL=S2 cR=G1 | a=17/16 b=75/58 | D2 | 1656 cases | NO-ALIVE-ON-GRID -/
def cls_387 : ChamberClass :=
  { kL := 2, kR := 2, A := (17/16 : ℚ), B := (75/58 : ℚ),
    lo := ![1, 1, 9, 15, 15], hi := ![7, 7, 15, 17, 17] }

/-- The recorded representative 5-tuple of class 387 (exact rationals, the probe's own
case dump). -/
def rho_387 : Fin 5 → ℚ := ![1, 1, 58/5, 16, 16]

theorem castAB_387 : ((cls_387.A : ℚ) : ℝ) = (17/16 : ℝ) ∧ ((cls_387.B : ℚ) : ℝ) = (75/58 : ℝ) := by
  norm_num [cls_387]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_387`/`cls_387` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_387 : InClass rho_387 cls_387 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_387, rho_387] <;> norm_num⟩

/-- **gamma at class 387, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_387`
consumed through `join50`. -/
theorem chjoin_387 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_387) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_387 (17/16 : ℝ) (75/58 : ℝ) castAB_387 hIn.1 Fresh.ChamberDatasheet.chds_387 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 387's own tuple (atom `chds_387` + proved join `inclass_387` +
`chjoin_387`). -/
theorem dead_387 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_387 s :=
  chjoin_387 rho_387 s hs h50 inclass_387

/-- jj#388 | PS1G1G1G1 | kL=1 kR=2 | cL=S1 cR=G1 | a=5/4 b=75/49 | D2 | 1638 cases | NO-ALIVE-ON-GRID -/
def cls_388 : ChamberClass :=
  { kL := 1, kR := 2, A := (5/4 : ℚ), B := (75/49 : ℚ),
    lo := ![1, 7, 9, 9, 9], hi := ![7, 9, 15, 15, 15] }

/-- The recorded representative 5-tuple of class 388 (exact rationals, the probe's own
case dump). -/
def rho_388 : Fin 5 → ℚ := ![1, 36/5, 9, 9, 49/5]

theorem castAB_388 : ((cls_388.A : ℚ) : ℝ) = (5/4 : ℝ) ∧ ((cls_388.B : ℚ) : ℝ) = (75/49 : ℝ) := by
  norm_num [cls_388]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_388`/`cls_388` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_388 : InClass rho_388 cls_388 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_388, rho_388] <;> norm_num⟩

/-- **gamma at class 388, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_388`
consumed through `join50`. -/
theorem chjoin_388 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_388) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_388 (5/4 : ℝ) (75/49 : ℝ) castAB_388 hIn.1 Fresh.ChamberDatasheet.chds_388 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 388's own tuple (atom `chds_388` + proved join `inclass_388` +
`chjoin_388`). -/
theorem dead_388 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_388 s :=
  chjoin_388 rho_388 s hs h50 inclass_388

/-- jj#389 | PS1G1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1638 cases | NO-ALIVE-ON-GRID -/
def cls_389 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 15], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 389 (exact rationals, the probe's own
case dump). -/
def rho_389 : Fin 5 → ℚ := ![1, 8, 9, 74/5, 17]

theorem castAB_389 : ((cls_389.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_389.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_389]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_389`/`cls_389` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_389 : InClass rho_389 cls_389 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_389, rho_389] <;> norm_num⟩

/-- **gamma at class 389, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_389`
consumed through `join50`. -/
theorem chjoin_389 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_389) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_389 (85/74 : ℝ) (23/17 : ℝ) castAB_389 hIn.1 Fresh.ChamberDatasheet.chds_389 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 389's own tuple (atom `chds_389` + proved join `inclass_389` +
`chjoin_389`). -/
theorem dead_389 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_389 s :=
  chjoin_389 rho_389 s hs h50 inclass_389

/-- jj#390 | PS1G1G1E | kL=2 kR=3 | cL=G1 cR=E | a=85/74 b=23/17 | D2 | 1638 cases | NO-ALIVE-ON-GRID -/
def cls_390 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 7, 9, 9, 17], hi := ![7, 9, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 390 (exact rationals, the probe's own
case dump). -/
def rho_390 : Fin 5 → ℚ := ![1, 8, 9, 74/5, 17]

theorem castAB_390 : ((cls_390.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_390.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_390]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_390`/`cls_390` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_390 : InClass rho_390 cls_390 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_390, rho_390] <;> norm_num⟩

/-- **gamma at class 390, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_390`
consumed through `join50`. -/
theorem chjoin_390 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_390) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_390 (85/74 : ℝ) (23/17 : ℝ) castAB_390 hIn.1 Fresh.ChamberDatasheet.chds_390 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 390's own tuple (atom `chds_390` + proved join `inclass_390` +
`chjoin_390`). -/
theorem dead_390 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_390 s :=
  chjoin_390 rho_390 s hs h50 inclass_390

/-- jj#391 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/83 | D2 | 1638 cases | NO-ALIVE-ON-GRID -/
def cls_391 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 391 (exact rationals, the probe's own
case dump). -/
def rho_391 : Fin 5 → ℚ := ![1, 9, 9, 74/5, 83/5]

theorem castAB_391 : ((cls_391.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_391.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_391]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_391`/`cls_391` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_391 : InClass rho_391 cls_391 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_391, rho_391] <;> norm_num⟩

/-- **gamma at class 391, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_391`
consumed through `join50`. -/
theorem chjoin_391 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_391) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_391 (85/74 : ℝ) (115/83 : ℝ) castAB_391 hIn.1 Fresh.ChamberDatasheet.chds_391 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 391's own tuple (atom `chds_391` + proved join `inclass_391` +
`chjoin_391`). -/
theorem dead_391 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_391 s :=
  chjoin_391 rho_391 s hs h50 inclass_391

/-- jj#392 | PG1G1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/74 b=115/84 | D2 | 1638 cases | NO-ALIVE-ON-GRID -/
def cls_392 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/74 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 9, 9, 9, 15], hi := ![7, 15, 15, 15, 17] }

/-- The recorded representative 5-tuple of class 392 (exact rationals, the probe's own
case dump). -/
def rho_392 : Fin 5 → ℚ := ![1, 9, 9, 74/5, 84/5]

theorem castAB_392 : ((cls_392.A : ℚ) : ℝ) = (85/74 : ℝ) ∧ ((cls_392.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_392]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_392`/`cls_392` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_392 : InClass rho_392 cls_392 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_392, rho_392] <;> norm_num⟩

/-- **gamma at class 392, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_392`
consumed through `join50`. -/
theorem chjoin_392 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_392) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_392 (85/74 : ℝ) (115/84 : ℝ) castAB_392 hIn.1 Fresh.ChamberDatasheet.chds_392 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 392's own tuple (atom `chds_392` + proved join `inclass_392` +
`chjoin_392`). -/
theorem dead_392 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_392 s :=
  chjoin_392 rho_392 s hs h50 inclass_392

/-- jj#393 | PPPS1S1 | kL=1 kR=2 | cL=P cR=S1 | a=9/7 b=75/41 | D1 | 1632 cases | NO-ALIVE-ON-GRID -/
def cls_393 : ChamberClass :=
  { kL := 1, kR := 2, A := (9/7 : ℚ), B := (75/41 : ℚ),
    lo := ![1, 1, 1, 7, 7], hi := ![7, 7, 7, 9, 9] }

/-- The recorded representative 5-tuple of class 393 (exact rationals, the probe's own
case dump). -/
def rho_393 : Fin 5 → ℚ := ![1, 1, 1, 7, 41/5]

theorem castAB_393 : ((cls_393.A : ℚ) : ℝ) = (9/7 : ℝ) ∧ ((cls_393.B : ℚ) : ℝ) = (75/41 : ℝ) := by
  norm_num [cls_393]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_393`/`cls_393` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_393 : InClass rho_393 cls_393 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_393, rho_393] <;> norm_num⟩

/-- **gamma at class 393, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_393`
consumed through `join50`. -/
theorem chjoin_393 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_393) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_393 (9/7 : ℝ) (75/41 : ℝ) castAB_393 hIn.1 Fresh.ChamberDatasheet.chds_393 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 393's own tuple (atom `chds_393` + proved join `inclass_393` +
`chjoin_393`). -/
theorem dead_393 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_393 s :=
  chjoin_393 rho_393 s hs h50 inclass_393

/-- jj#394 | PS1S1G1G1 | kL=2 kR=2 | cL=G1 cR=G1 | a=85/66 b=5/3 | D1 | 1630 cases | NO-ALIVE-ON-GRID -/
def cls_394 : ChamberClass :=
  { kL := 2, kR := 2, A := (85/66 : ℚ), B := (5/3 : ℚ),
    lo := ![1, 7, 7, 9, 9], hi := ![7, 9, 9, 15, 15] }

/-- The recorded representative 5-tuple of class 394 (exact rationals, the probe's own
case dump). -/
def rho_394 : Fin 5 → ℚ := ![1, 7, 7, 9, 66/5]

theorem castAB_394 : ((cls_394.A : ℚ) : ℝ) = (85/66 : ℝ) ∧ ((cls_394.B : ℚ) : ℝ) = (5/3 : ℝ) := by
  norm_num [cls_394]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_394`/`cls_394` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_394 : InClass rho_394 cls_394 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_394, rho_394] <;> norm_num⟩

/-- **gamma at class 394, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_394`
consumed through `join50`. -/
theorem chjoin_394 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_394) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_394 (85/66 : ℝ) (5/3 : ℝ) castAB_394 hIn.1 Fresh.ChamberDatasheet.chds_394 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 394's own tuple (atom `chds_394` + proved join `inclass_394` +
`chjoin_394`). -/
theorem dead_394 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_394 s :=
  chjoin_394 rho_394 s hs h50 inclass_394

/-- jj#395 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/83 | D2 | 1617 cases | NO-ALIVE-ON-GRID -/
def cls_395 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 395 (exact rationals, the probe's own
case dump). -/
def rho_395 : Fin 5 → ℚ := ![1, 1, 39/5, 72/5, 83/5]

theorem castAB_395 : ((cls_395.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_395.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_395]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_395`/`cls_395` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_395 : InClass rho_395 cls_395 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_395, rho_395] <;> norm_num⟩

/-- **gamma at class 395, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_395`
consumed through `join50`. -/
theorem chjoin_395 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_395) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_395 (85/72 : ℝ) (115/83 : ℝ) castAB_395 hIn.1 Fresh.ChamberDatasheet.chds_395 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 395's own tuple (atom `chds_395` + proved join `inclass_395` +
`chjoin_395`). -/
theorem dead_395 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_395 s :=
  chjoin_395 rho_395 s hs h50 inclass_395

/-- jj#396 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/72 b=115/84 | D2 | 1617 cases | NO-ALIVE-ON-GRID -/
def cls_396 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 396 (exact rationals, the probe's own
case dump). -/
def rho_396 : Fin 5 → ℚ := ![1, 1, 39/5, 72/5, 84/5]

theorem castAB_396 : ((cls_396.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_396.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_396]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_396`/`cls_396` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_396 : InClass rho_396 cls_396 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_396, rho_396] <;> norm_num⟩

/-- **gamma at class 396, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_396`
consumed through `join50`. -/
theorem chjoin_396 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_396) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_396 (85/72 : ℝ) (115/84 : ℝ) castAB_396 hIn.1 Fresh.ChamberDatasheet.chds_396 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 396's own tuple (atom `chds_396` + proved join `inclass_396` +
`chjoin_396`). -/
theorem dead_396 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_396 s :=
  chjoin_396 rho_396 s hs h50 inclass_396

/-- jj#397 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=E | a=85/72 b=23/17 | D2 | 1617 cases | NO-ALIVE-ON-GRID -/
def cls_397 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/72 : ℚ), B := (23/17 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 397 (exact rationals, the probe's own
case dump). -/
def rho_397 : Fin 5 → ℚ := ![1, 1, 39/5, 72/5, 17]

theorem castAB_397 : ((cls_397.A : ℚ) : ℝ) = (85/72 : ℝ) ∧ ((cls_397.B : ℚ) : ℝ) = (23/17 : ℝ) := by
  norm_num [cls_397]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_397`/`cls_397` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_397 : InClass rho_397 cls_397 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_397, rho_397] <;> norm_num⟩

/-- **gamma at class 397, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_397`
consumed through `join50`. -/
theorem chjoin_397 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_397) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_397 (85/72 : ℝ) (23/17 : ℝ) castAB_397 hIn.1 Fresh.ChamberDatasheet.chds_397 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 397's own tuple (atom `chds_397` + proved join `inclass_397` +
`chjoin_397`). -/
theorem dead_397 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_397 s :=
  chjoin_397 rho_397 s hs h50 inclass_397

/-- jj#398 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/83 | D2 | 1617 cases | NO-ALIVE-ON-GRID -/
def cls_398 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/83 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 398 (exact rationals, the probe's own
case dump). -/
def rho_398 : Fin 5 → ℚ := ![1, 1, 39/5, 73/5, 83/5]

theorem castAB_398 : ((cls_398.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_398.B : ℚ) : ℝ) = (115/83 : ℝ) := by
  norm_num [cls_398]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_398`/`cls_398` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_398 : InClass rho_398 cls_398 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_398, rho_398] <;> norm_num⟩

/-- **gamma at class 398, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_398`
consumed through `join50`. -/
theorem chjoin_398 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_398) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_398 (85/73 : ℝ) (115/83 : ℝ) castAB_398 hIn.1 Fresh.ChamberDatasheet.chds_398 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 398's own tuple (atom `chds_398` + proved join `inclass_398` +
`chjoin_398`). -/
theorem dead_398 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_398 s :=
  chjoin_398 rho_398 s hs h50 inclass_398

/-- jj#399 | PPS1G1S2 | kL=2 kR=3 | cL=G1 cR=S2 | a=85/73 b=115/84 | D2 | 1617 cases | NO-ALIVE-ON-GRID -/
def cls_399 : ChamberClass :=
  { kL := 2, kR := 3, A := (85/73 : ℚ), B := (115/84 : ℚ),
    lo := ![1, 1, 7, 9, 15], hi := ![7, 7, 9, 15, 17] }

/-- The recorded representative 5-tuple of class 399 (exact rationals, the probe's own
case dump). -/
def rho_399 : Fin 5 → ℚ := ![1, 1, 39/5, 73/5, 84/5]

theorem castAB_399 : ((cls_399.A : ℚ) : ℝ) = (85/73 : ℝ) ∧ ((cls_399.B : ℚ) : ℝ) = (115/84 : ℝ) := by
  norm_num [cls_399]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_399`/`cls_399` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_399 : InClass rho_399 cls_399 :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_399, rho_399] <;> norm_num⟩

/-- **gamma at class 399, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_399`
consumed through `join50`. -/
theorem chjoin_399 (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_399) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_399 (85/73 : ℝ) (115/84 : ℝ) castAB_399 hIn.1 Fresh.ChamberDatasheet.chds_399 s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class 399's own tuple (atom `chds_399` + proved join `inclass_399` +
`chjoin_399`). -/
theorem dead_399 (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_399 s :=
  chjoin_399 rho_399 s hs h50 inclass_399

/-! ## §4 The tranche as a list (the assembly's queryable cover data) -/

/-- The tranche's class records, in emission order (the cover candidates for the
partition step; `Fresh.K6Gamma.partition_principle` consumes a cover from such a list). -/
def trancheClasses : List ChamberClass :=
  [cls_0, cls_1, cls_2, cls_3, cls_4, cls_5, cls_6, cls_7, cls_8, cls_9, cls_10, cls_11, cls_12, cls_13, cls_14, cls_15, cls_16, cls_17, cls_18, cls_19, cls_20, cls_21, cls_22, cls_23, cls_24, cls_25, cls_26, cls_27, cls_28, cls_29, cls_30, cls_31, cls_32, cls_33, cls_34, cls_35, cls_36, cls_37, cls_38, cls_39, cls_40, cls_41, cls_42, cls_43, cls_44, cls_45, cls_46, cls_47, cls_48, cls_49, cls_50, cls_51, cls_52, cls_53, cls_54, cls_55, cls_56, cls_57, cls_58, cls_59, cls_60, cls_61, cls_62, cls_63, cls_64, cls_65, cls_66, cls_67, cls_68, cls_69, cls_70, cls_71, cls_72, cls_73, cls_74, cls_75, cls_76, cls_77, cls_78, cls_79, cls_80, cls_81, cls_82, cls_83, cls_84, cls_85, cls_86, cls_87, cls_88, cls_89, cls_90, cls_91, cls_92, cls_93, cls_94, cls_95, cls_96, cls_97, cls_98, cls_99, cls_100, cls_101, cls_102, cls_103, cls_104, cls_105, cls_106, cls_107, cls_108, cls_109, cls_110, cls_111, cls_112, cls_113, cls_114, cls_115, cls_116, cls_117, cls_118, cls_119, cls_120, cls_121, cls_122, cls_123, cls_124, cls_125, cls_126, cls_127, cls_128, cls_129, cls_130, cls_131, cls_132, cls_133, cls_134, cls_135, cls_136, cls_137, cls_138, cls_139, cls_140, cls_141, cls_142, cls_143, cls_144, cls_145, cls_146, cls_147, cls_148, cls_149, cls_150, cls_151, cls_152, cls_153, cls_154, cls_155, cls_156, cls_157, cls_158, cls_159, cls_160, cls_161, cls_162, cls_163, cls_164, cls_165, cls_166, cls_167, cls_168, cls_169, cls_170, cls_171, cls_172, cls_173, cls_174, cls_175, cls_176, cls_177, cls_178, cls_179, cls_180, cls_181, cls_182, cls_183, cls_184, cls_185, cls_186, cls_187, cls_188, cls_189, cls_190, cls_191, cls_192, cls_193, cls_194, cls_195, cls_196, cls_197, cls_198, cls_199, cls_200, cls_201, cls_202, cls_203, cls_204, cls_205, cls_206, cls_207, cls_208, cls_209, cls_210, cls_211, cls_212, cls_213, cls_214, cls_215, cls_216, cls_217, cls_218, cls_219, cls_220, cls_221, cls_222, cls_223, cls_224, cls_225, cls_226, cls_227, cls_228, cls_229, cls_230, cls_231, cls_232, cls_233, cls_234, cls_235, cls_236, cls_237, cls_238, cls_239, cls_240, cls_241, cls_242, cls_243, cls_244, cls_245, cls_246, cls_247, cls_248, cls_249, cls_250, cls_251, cls_252, cls_253, cls_254, cls_255, cls_256, cls_257, cls_258, cls_259, cls_260, cls_261, cls_262, cls_263, cls_264, cls_265, cls_266, cls_267, cls_268, cls_269, cls_270, cls_271, cls_272, cls_273, cls_274, cls_275, cls_276, cls_277, cls_278, cls_279, cls_280, cls_281, cls_282, cls_283, cls_284, cls_285, cls_286, cls_287, cls_288, cls_289, cls_290, cls_291, cls_292, cls_293, cls_294, cls_295, cls_296, cls_297, cls_298, cls_299, cls_300, cls_301, cls_302, cls_303, cls_304, cls_305, cls_306, cls_307, cls_308, cls_309, cls_310, cls_311, cls_312, cls_313, cls_314, cls_315, cls_316, cls_317, cls_318, cls_319, cls_320, cls_321, cls_322, cls_323, cls_324, cls_325, cls_326, cls_327, cls_328, cls_329, cls_330, cls_331, cls_332, cls_333, cls_334, cls_335, cls_336, cls_337, cls_338, cls_339, cls_340, cls_341, cls_342, cls_343, cls_344, cls_345, cls_346, cls_347, cls_348, cls_349, cls_350, cls_351, cls_352, cls_353, cls_354, cls_355, cls_356, cls_357, cls_358, cls_359, cls_360, cls_361, cls_362, cls_363, cls_364, cls_365, cls_366, cls_367, cls_368, cls_369, cls_370, cls_371, cls_372, cls_373, cls_374, cls_375, cls_376, cls_377, cls_378, cls_379, cls_380, cls_381, cls_382, cls_383, cls_384, cls_385, cls_386, cls_387, cls_388, cls_389, cls_390, cls_391, cls_392, cls_393, cls_394, cls_395, cls_396, cls_397, cls_398, cls_399]

/-- The tranche's recorded representative tuples, in emission order. -/
def trancheRhos : List (Fin 5 → ℚ) :=
  [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rho_25, rho_26, rho_27, rho_28, rho_29, rho_30, rho_31, rho_32, rho_33, rho_34, rho_35, rho_36, rho_37, rho_38, rho_39, rho_40, rho_41, rho_42, rho_43, rho_44, rho_45, rho_46, rho_47, rho_48, rho_49, rho_50, rho_51, rho_52, rho_53, rho_54, rho_55, rho_56, rho_57, rho_58, rho_59, rho_60, rho_61, rho_62, rho_63, rho_64, rho_65, rho_66, rho_67, rho_68, rho_69, rho_70, rho_71, rho_72, rho_73, rho_74, rho_75, rho_76, rho_77, rho_78, rho_79, rho_80, rho_81, rho_82, rho_83, rho_84, rho_85, rho_86, rho_87, rho_88, rho_89, rho_90, rho_91, rho_92, rho_93, rho_94, rho_95, rho_96, rho_97, rho_98, rho_99, rho_100, rho_101, rho_102, rho_103, rho_104, rho_105, rho_106, rho_107, rho_108, rho_109, rho_110, rho_111, rho_112, rho_113, rho_114, rho_115, rho_116, rho_117, rho_118, rho_119, rho_120, rho_121, rho_122, rho_123, rho_124, rho_125, rho_126, rho_127, rho_128, rho_129, rho_130, rho_131, rho_132, rho_133, rho_134, rho_135, rho_136, rho_137, rho_138, rho_139, rho_140, rho_141, rho_142, rho_143, rho_144, rho_145, rho_146, rho_147, rho_148, rho_149, rho_150, rho_151, rho_152, rho_153, rho_154, rho_155, rho_156, rho_157, rho_158, rho_159, rho_160, rho_161, rho_162, rho_163, rho_164, rho_165, rho_166, rho_167, rho_168, rho_169, rho_170, rho_171, rho_172, rho_173, rho_174, rho_175, rho_176, rho_177, rho_178, rho_179, rho_180, rho_181, rho_182, rho_183, rho_184, rho_185, rho_186, rho_187, rho_188, rho_189, rho_190, rho_191, rho_192, rho_193, rho_194, rho_195, rho_196, rho_197, rho_198, rho_199, rho_200, rho_201, rho_202, rho_203, rho_204, rho_205, rho_206, rho_207, rho_208, rho_209, rho_210, rho_211, rho_212, rho_213, rho_214, rho_215, rho_216, rho_217, rho_218, rho_219, rho_220, rho_221, rho_222, rho_223, rho_224, rho_225, rho_226, rho_227, rho_228, rho_229, rho_230, rho_231, rho_232, rho_233, rho_234, rho_235, rho_236, rho_237, rho_238, rho_239, rho_240, rho_241, rho_242, rho_243, rho_244, rho_245, rho_246, rho_247, rho_248, rho_249, rho_250, rho_251, rho_252, rho_253, rho_254, rho_255, rho_256, rho_257, rho_258, rho_259, rho_260, rho_261, rho_262, rho_263, rho_264, rho_265, rho_266, rho_267, rho_268, rho_269, rho_270, rho_271, rho_272, rho_273, rho_274, rho_275, rho_276, rho_277, rho_278, rho_279, rho_280, rho_281, rho_282, rho_283, rho_284, rho_285, rho_286, rho_287, rho_288, rho_289, rho_290, rho_291, rho_292, rho_293, rho_294, rho_295, rho_296, rho_297, rho_298, rho_299, rho_300, rho_301, rho_302, rho_303, rho_304, rho_305, rho_306, rho_307, rho_308, rho_309, rho_310, rho_311, rho_312, rho_313, rho_314, rho_315, rho_316, rho_317, rho_318, rho_319, rho_320, rho_321, rho_322, rho_323, rho_324, rho_325, rho_326, rho_327, rho_328, rho_329, rho_330, rho_331, rho_332, rho_333, rho_334, rho_335, rho_336, rho_337, rho_338, rho_339, rho_340, rho_341, rho_342, rho_343, rho_344, rho_345, rho_346, rho_347, rho_348, rho_349, rho_350, rho_351, rho_352, rho_353, rho_354, rho_355, rho_356, rho_357, rho_358, rho_359, rho_360, rho_361, rho_362, rho_363, rho_364, rho_365, rho_366, rho_367, rho_368, rho_369, rho_370, rho_371, rho_372, rho_373, rho_374, rho_375, rho_376, rho_377, rho_378, rho_379, rho_380, rho_381, rho_382, rho_383, rho_384, rho_385, rho_386, rho_387, rho_388, rho_389, rho_390, rho_391, rho_392, rho_393, rho_394, rho_395, rho_396, rho_397, rho_398, rho_399]

/-! ## §5 The axiom footprint -/

#print axioms Fresh.ChamberJoin.join50
#print axioms Fresh.ChamberJoin.join50_sub
#print axioms Fresh.ChamberJoin.inclass_0
#print axioms Fresh.ChamberJoin.chjoin_100
#print axioms Fresh.ChamberJoin.chjoin_200
#print axioms Fresh.ChamberJoin.chjoin_300
#print axioms Fresh.ChamberJoin.dead_399

end Fresh.ChamberJoin
