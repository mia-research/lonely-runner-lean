import Mathlib.Tactic
import Fresh.ChamberJoin

/-!
# K6Gamma: bridge gamma -- the composition theorem (class match + datasheet atom + beta)

New file (2026-11-21); nothing existing is edited.  Imports `Fresh.ChamberJoin` (the
InClass class-match definitions, the join theorem shapes, and the emitted per-class
instances over bridge beta's `TupleLonely` / `K6Comps` and the datasheet's `ColDead50`
atoms).

## What gamma is, and what was already there

The task's gamma: for a 5-tuple `rho` whose K6 decomposition contains a component matching
a datasheet class (the class's `(A, B)` edges equal the component's edges as rationals,
and `rho` lies in the class's cell-box), the class's certificate + beta conclude the
TUPLE's [25, 50) column is dead.  Reading beta (`Fresh.K6BandUnion`), the composed shape
`band_union50_via_datasheet` already IS the tuple-level conclusion: atom (`ColDead50 A B`
at the real-cast edges) + join (`(a, b) ∈ K6Comps rho` with the cast edges) gives
`¬ TupleLonely rho s` for every tail `s ∈ [25, 50)`, with NO hypothesis on the other
components (one empty factor empties the running intersection).  Gamma's work is exactly
the INSTANTIATION/WIRING: the class-match predicate `Fresh.ChamberJoin.InClass rho cls`
(closed here: exact component membership + cell-box), its first projection feeding the
join, and the atoms from `Fresh.ChamberDatasheet.chds_i` -- landed below as

* `gamma_join50` -- the general composition theorem (cast-form atom hypothesis);
* `gamma_is_via_datasheet` -- the rfl-separation showing gamma IS beta's
  `band_union50_via_datasheet` at the InClass membership (the confirmation, formal);
* `gamma_join50_lit` -- the literal-atom form consuming the datasheet's own emitted atoms
  (`chds_i : ColDead50 (A_lit : ℝ) (B_lit : ℝ)`) through the cast bridge;
* `gamma_joinC` -- the task's literal CLOSED-band UNBOUNDED form (`∀ s ≥ 25`, all laps
  `j ≥ 1`, bands `[(8j-1)/a, (8j+1)/b]`): the full-strength antecedent gives the unbounded
  conclusion via beta's `band_union` (the datasheet atoms are [25, 50)-windowed and do
  NOT feed this form -- the two band conventions differ at a band's right endpoint; see
  Fresh.K6BandUnion's honest scope notes);
* `gamma_join50_sub` -- the containment variant (`InClassSub`: some component of `rho`
  CONTAINS the dead interval -- the [1, 7]-clipping shape);
* `partition_principle` -- the assembly's wiring: given a LIST of classes, per-class
  atoms, and a COVER (`∃ cls ∈ classes, InClass rho cls ∨ InClassSub rho cls`), the
  tuple is dead over [25, 50).  The cover hypothesis is exactly the remaining
  hyperplane-partition step (STANDING: OWED -- see the honest scope note below); gamma
  dispatches it per class, so the assembly consumes nothing else.

## Honest scope (what gamma does NOT carry)

* The atoms are component-level (S2) at the FIXED edges `(A, B)`; the S1
  chamber-window-uniform two-line fires on ZERO of the 7,797 census classes (verified,
  not assumed; Fresh.ChamberDatasheet's header).  Within a chamber the certifying
  component's edges vary with the readings (`a_t = (8kL+1)/rho_L`), and the far tuples of
  the cell-box defeat the two-line -- the deaths there are interlacing (the running
  intersection of the components' band unions dies while no single component is dead).
* `InClass` is proved (kernel decide) only for the RECORDED representatives -- one per
  emitted class (`Fresh.ChamberJoin.inclass_i`), verified data-side for all 7,797 classes
  (`experiments/n8/chambjoin_verify_v1.out`: exact K6 join 7,797/7,797, closed cell-box
  7,797/7,797, per-key dedupe re-derived 7,797/7,797).  For a GENERAL cell-box tuple the
  match is not the exact-component join (the edges vary), so the cover hypothesis of
  `partition_principle` is open: that is the partition step, and no Lean proof of it is
  faked here.  The probe's no-alive-on-grid evidence (6,569 of 7,797 classes) is the
  data-side support for it.
* A [25, 50)-column death is the conclusion everywhere the datasheet atoms are consumed
  (their window); the unbounded form needs the full-strength antecedent (`gamma_joinC`).

-/

namespace Fresh.K6Gamma

/-! ## §1 The composition theorem (the InClass wiring of beta) -/

/-- **Bridge gamma (the composition).**  The class match `InClass rho cls` + the class's
datasheet atom at the real-cast edges + beta = the TUPLE's [25, 50) column is dead: no
tail `s ∈ [25, 50)` is lonely for `rho`.  No hypothesis on the other components; the
component list may even be empty (the membership hypothesis then fails). -/
theorem gamma_join50 (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (hIn : Fresh.ChamberJoin.InClass rho cls)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  Fresh.K6BandUnion.band_union50_via_datasheet rho cls.A cls.B ((cls.A : ℚ) : ℝ)
    ((cls.B : ℚ) : ℝ) rfl rfl hIn.1 hcd s hs h50

/-- **The formal confirmation**: gamma's composition IS beta's
`band_union50_via_datasheet` at the InClass membership -- the two terms are definitionally
equal (`rfl`); gamma's content is the class-match predicate and its wiring, not a new
band-union lemma. -/
theorem gamma_is_via_datasheet (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (hIn : Fresh.ChamberJoin.InClass rho cls)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    gamma_join50 rho cls hIn hcd s hs h50
      = Fresh.K6BandUnion.band_union50_via_datasheet rho cls.A cls.B ((cls.A : ℚ) : ℝ)
          ((cls.B : ℚ) : ℝ) rfl rfl hIn.1 hcd s hs h50 := rfl

/-- **The literal-atom form** (what the emitted instances consume): the datasheet's own
atom `ColDead50 A_lit B_lit` at the real-literal edges, bridged by the per-instance cast
theorem.  This is `Fresh.ChamberJoin.join50` restated as a gamma conclusion with the full
InClass antecedent. -/
theorem gamma_join50_lit (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (A B : ℝ) (hAB : ((cls.A : ℚ) : ℝ) = A ∧ ((cls.B : ℚ) : ℝ) = B)
    (hIn : Fresh.ChamberJoin.InClass rho cls)
    (hcd : Fresh.ChamberDatasheet.ColDead50 A B)
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  Fresh.ChamberJoin.join50 rho cls A B hAB hIn.1 hcd s hs h50

/-! ## §2 The task's literal form (closed bands, unbounded column) -/

/-- **Bridge gamma, the task's literal form.**  CLOSED bands `[(8j-1)/a, (8j+1)/b]`, laps
`j ≥ 1`, column UNBOUNDED above: exactly the stated antecedent (the matched component is
dead over every tail `s ≥ 25` at every positive lap) gives, for EVERY `s ≥ 25`, that some
component of `rho` is not a closed-band lonely window at `s` -- via beta's `band_union`
verbatim.  Note the datasheet's emitted atoms are [25, 50)-windowed right-open; they do
NOT feed this form (an atom of one convention consumes the matching conclusion only). -/
theorem gamma_joinC (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (hIn : Fresh.ChamberJoin.InClass rho cls)
    (hdead : ∀ s : ℚ, 25 ≤ s → ∀ j : ℕ, 1 ≤ j →
      ¬ Fresh.K6BandUnion.BandC (cls.A, cls.B) s j)
    (s : ℚ) (hs : (25:ℚ) ≤ s) :
    ¬ ∀ q ∈ K6Comps rho, Fresh.K6BandUnion.FeasibleC q s :=
  Fresh.K6BandUnion.band_union rho (cls.A, cls.B) hIn.1 hdead s hs

/-- The literal form's no-lonely-tail column statement (¬∃ form, unbounded). -/
theorem gamma_no_lonely_unbounded (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (hIn : Fresh.ChamberJoin.InClass rho cls)
    (hdead : ∀ s : ℚ, 25 ≤ s → ∀ j : ℕ, 1 ≤ j →
      ¬ Fresh.K6BandUnion.BandC (cls.A, cls.B) s j) :
    ¬ ∃ s : ℚ, 25 ≤ s ∧ ∀ q ∈ K6Comps rho, Fresh.K6BandUnion.FeasibleC q s :=
  fun ⟨s, hs, hall⟩ => gamma_joinC rho cls hIn hdead s hs hall

/-! ## §3 The containment variant -/

/-- **Bridge gamma, the containment variant.**  The class match in the `InClassSub` shape
(some component of `rho` CONTAINS the class's dead interval `[A, B]` -- the [1, 7]-clipping
shape for boundary components) + the class's atom + `1 ≤ B` kill the tuple over
[25, 50), via beta's `band_union50_subset` through the real-to-rational transport. -/
theorem gamma_join50_sub (rho : Fin 5 → ℚ) (cls : Fresh.ChamberJoin.ChamberClass)
    (hIn : Fresh.ChamberJoin.InClassSub rho cls)
    (hB1 : (1:ℚ) ≤ cls.B)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho s := by
  obtain ⟨q, hq, h1, h2, _⟩ := hIn
  exact Fresh.ChamberJoin.join50_sub rho cls ⟨q, hq, h1, h2⟩ hB1 hcd s hs h50

/-! ## §4 The assembly's wiring: the cover-dispatch principle

The middle-branch assembly consumes, per cell-box tuple, a COVER: some emitted class
matches the tuple (exactly, or by containment).  Given the cover, gamma does the rest.
The cover itself is the remaining hyperplane-partition step (STANDING: OWED -- the
recorded representatives ARE covered, one per emitted class, by the kernel-decided
`Fresh.ChamberJoin.inclass_i`; the general cell-box tuple is not yet carried). -/

/-- **The partition principle (gamma's dispatch).**  A list of chamber classes, per-class
datasheet atoms at the real-cast edges, `1 ≤ B` (containment needs the dead interval's
right edge at least 1 -- data-side true for all 7,797 census classes), and a COVER for
`rho` from the list kill the tuple's [25, 50) column.  This is the exact consumption
shape: the assembly's remaining obligation is precisely to establish the cover
hypothesis for every cell-box tuple (the hyperplane partition; no Lean proof faked). -/
theorem partition_principle (classes : List Fresh.ChamberJoin.ChamberClass)
    (hatom : ∀ cls ∈ classes,
      Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (hB1 : ∀ cls ∈ classes, (1:ℚ) ≤ cls.B)
    (rho : Fin 5 → ℚ)
    (hcover : ∃ cls ∈ classes,
      Fresh.ChamberJoin.InClass rho cls ∨ Fresh.ChamberJoin.InClassSub rho cls)
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho s := by
  obtain ⟨cls, hcls, hmatch⟩ := hcover
  rcases hmatch with hex | hsub
  · obtain ⟨hmem, hbox⟩ := hex
    exact gamma_join50 rho cls ⟨hmem, hbox⟩ (hatom cls hcls) s hs h50
  · obtain ⟨q, hq, h1, h2, _⟩ := hsub
    exact Fresh.ChamberJoin.join50_sub rho cls ⟨q, hq, h1, h2⟩ (hB1 cls hcls)
      (hatom cls hcls) s hs h50

/-! ## §5 Axiom footprints -/

#print axioms Fresh.K6Gamma.gamma_join50
#print axioms Fresh.K6Gamma.gamma_is_via_datasheet
#print axioms Fresh.K6Gamma.gamma_join50_lit
#print axioms Fresh.K6Gamma.gamma_joinC
#print axioms Fresh.K6Gamma.gamma_no_lonely_unbounded
#print axioms Fresh.K6Gamma.gamma_join50_sub
#print axioms Fresh.K6Gamma.partition_principle

end Fresh.K6Gamma
