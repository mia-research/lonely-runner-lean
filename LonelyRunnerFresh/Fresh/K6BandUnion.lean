import Mathlib.Tactic
import Fresh.K6Decomp
import Fresh.ChamberDatasheet

/-!
# K6BandUnion: bridge β — the band-union lemma (one column-dead K6 component kills the
tuple's lonely column)

New file (2026-11-21); nothing existing is edited.  Imports `Fresh.K6Decomp` (bridge α:
`ZonesOf` / `Merged` / `K6Comps` / `comps_lonely`, the covered/lonely characterisation)
and `Fresh.ChamberDatasheet` (the per-class certificates `chds_* : ColDead50 A B`).

## The lemma (Track T bridge piece β; E904's OWED register, E910's next step)

The middle-branch datasheet consumption needs: for the K6 components of a reading
5-tuple `rho : Fin 5 → ℚ`, if ONE component `p = (a, b)` is column-dead over the
[25, 50) column — no tail `s ≥ 25` lies in any lap-`j` band `[(8j-1)/a, (8j+1)/b)` of
`p` — then the WHOLE tuple has no lonely tail over the column: for every tail `s` in
the column at least one component of the tuple is NOT a lonely window at `s`.

Tuple-level loneliness is the running intersection of the components' feasible sets
(E865 Lemma E semantics: the tail `s` carves the tuple iff every K6 component lies in
a single `s`-tooth, i.e. `s` lies in every component's band union).  One empty factor
empties the intersection, so the proof is ∀-instantiation of the all-lonely hypothesis
at the dead component — the "one-liner GIVEN (α)" of E904 — plus the lap-0 boundary
case (a tail `s ≥ 25` never sits in lap 0 of a component with `1 ≤ b`, via
`comps_lonely` from α).  The other components' feasible sets are irrelevant; the
component list may even be empty (the dead-component membership hypothesis then fails,
so the lemma holds vacuously).

## What is proved here, honestly

* **General forms (arbitrary `rho`, arbitrary component membership):**
  * `band_union50` — datasheet convention (right-open bands, [25, 50) column, all
    laps): `ColDead p → p ∈ K6Comps rho → ¬ TupleLonely rho s` for `s ∈ [25, 50)`.
  * `band_union` — the task's literal form (CLOSED bands `[(8j-1)/a, (8j+1)/b]`,
    laps ≥ 1, column unbounded above): exactly the stated antecedent gives
    `¬(∀ q ∈ K6Comps rho, FeasibleC q s)` for EVERY `s ≥ 25` (stronger than the
    [25, 50) conclusion the task asks for).
  * `tuple_no_lonely50` / `exists_not_lonely50` — the no-lonely-ρ column statement as
    ¬∃ and as the literal "at least one component is not a lonely window at s".
  * `band_union50_subset` — the containment join: a dead interval `[A, B]` INSIDE some
    component's hull kills the tuple too (robust to the [1, 7] clipping of boundary
    components).
* **The ℝ datasheet wiring:** `band_union_R` consumes the datasheet's own atom
  `Fresh.ChamberDatasheet.ColDead50 ((p.1:ℚ):ℝ) ((p.2:ℚ):ℝ)` DIRECTLY (the ℝ band
  predicate is `CompLive` itself, so the all-lonely hypothesis instantiates into the
  atom definitionally; even lap 0 is covered since `ColDead50` quantifies over all
  laps), and `colDead50_imp` transports a real-edged atom to the ℚ convention by the
  standard unconditional cast lemmas.  `band_union50_via_datasheet` is the composed
  datasheet→β shape: atom + membership ⟹ the class's tuple-level column death.
* **Worked instance** (α's `rhoEx = ![2, 3, 4, 6, 8]`): the second component
  `(3/2, 7/4)` is column-dead over [25, ∞) (its lap-1 band `[14/3, 36/7]` lies
  entirely below 25 and every lap ≥ 2 band is empty: `14(8j-1) ≤ 12(8j+1)` forces
  `j ≤ 13/8`), and the tuple-level no-lonely conclusions are derived as literal
  theorems — including the full datasheet loop `rhoEx_no_lonely50_via_datasheet`
  (the `datasheet_D2` two-line atom at the real-cast edges ⟹ tuple dead over
  [25, 50)).

## The datasheet→β wiring note (per class; what the datasheet must supply)

To conclude a chamber class's column death over [25, 50) via the lemmas here, the
datasheet side supplies exactly three things:

1. **The atom** — already emitted for all 7,797 classes: `chds_k : ColDead50 A B`
   with the class's certifying component edges `A B : ℝ` (literal rationals).
2. **The tuple** — the class's reading 5-tuple as a `Fin 5 → ℚ` term (the chamber
   windows' rational literals).
3. **The join** — that the dead interval is a K6 component of that tuple, in one of
   the two proved shapes: `(a, b) ∈ K6Comps rho` with `(a:ℝ) = A`, `(b:ℝ) = B`
   (exact-component join; consume with `band_union50_via_datasheet`), or
   `q ∈ K6Comps rho` with `q.1 ≤ a`, `b ≤ q.2` (containment join; consume with
   `band_union50_subset` — this covers the [1, 7] clipping of boundary components,
   where the recorded edges are a sub-interval of the Lean component).  This join is
   the α↔datasheet correspondence and is data-side today; γ (the hyperplane-partition
   step) carries the recorded tuples to every cell-box tuple.

Nothing else is consumed: no hypothesis on the other components, no validity beyond
what α's `comps_lonely`/`walk_ge` give (`comp_snd_ge1` / `comp_fst_ge1` here), and the
component list may be empty (vacuous).

## Honest scope notes

* `TupleLonely` is the ∩-of-feasible-sets semantics per E865 Lemma E; the carve-iff
  itself (that this is exactly "the tuple carves at s") is instrument-side and is not
  re-proved here.
* The core is ℚ-tailed (α is ℚ); `band_union_R` gives the ℝ-tailed form that consumes
  the emitted atoms, with edges the ℚ casts of the component's endpoints.  An ℝ-tail
  K6 decomposition (ℝ `ZonesOf`/`K6Comps`) is γ's plumbing and is not attempted here.
  Symmetrically, a ℚ-tail death does NOT transport up to ℝ tails (an irrational tail
  is not a cast); the consumption direction is ℝ atom → ℚ tail, which is what the
  middle branch needs.
* The two band conventions differ exactly at a band's right endpoint `s = (8j+1)/b`:
  the datasheet's `CompLive` is right-open (the search's entry-side convention), the
  task's literal form is closed.  Both are landed; an atom of one convention consumes
  the matching conclusion only.
* The datasheet's emitted atoms are [25, 50)-windowed; the D2 template's proof in
  `Fresh.ChamberDatasheet` in fact kills over [25, ∞), so a D2 class could also feed
  the unbounded `band_union` after transporting the window — not needed for the
  middle-branch consumption, which is a [25, 50) column.

## Compiler quirks used (as in Fresh/K6Decomp.lean)

* `allowUnsafeReducibility` + local `Rat.mul`/`Rat.inv` reducibility so `decide`/
  `norm_num`/`linarith` evaluate ℚ division (elaboration-level only; the axiom
  footprint is unaffected, and no other file is touched).
* Explicit cast rewrites: `Rat.cast_div`/`Rat.cast_le` via `exact_mod_cast` for the
  ℚ→ℝ bridge (all unconditional in this Mathlib).
-/

set_option allowUnsafeReducibility true
attribute [local reducible] Rat.mul Rat.inv

namespace Fresh.K6BandUnion

/-! ## §1 Definitions (the bands and the running intersection) -/

/-- STANDING: DEFINITION -- the lap-`j` band of a K6 component `p = [p.1, p.2]`: the
set of tails `s` whose lap-`j` tooth covers the component's closed hull, in the
datasheet's `CompLive` convention (left-closed, right-open).  ℚ mirror of
`Fresh.ChamberDatasheet.CompLive`. -/
def Band (p : ℚ × ℚ) (s : ℚ) (j : ℕ) : Prop :=
  (8 * (j:ℚ) - 1) / p.1 ≤ s ∧ s < (8 * (j:ℚ) + 1) / p.2

/-- STANDING: DEFINITION -- the component `p` is a lonely window at tail `s`: some
lap's band catches `s` (the component's feasible set at `s`). -/
def Feasible (p : ℚ × ℚ) (s : ℚ) : Prop := ∃ j : ℕ, Band p s j

/-- STANDING: DEFINITION -- the tuple is all-lonely at tail `s`: the running
intersection of the components' feasible sets contains `s` (E865 Lemma E semantics:
every K6 component lies in a single `s`-tooth). -/
def TupleLonely (rho : Fin 5 → ℚ) (s : ℚ) : Prop := ∀ p ∈ K6Comps rho, Feasible p s

/-- STANDING: DEFINITION -- the component `p` is column-dead over the [25, 50) column:
no tail of the column lies in any band.  ℚ mirror of
`Fresh.ChamberDatasheet.ColDead50`. -/
def ColDead (p : ℚ × ℚ) : Prop := ∀ s : ℚ, 25 ≤ s → s < 50 → ∀ j : ℕ, ¬ Band p s j

/-- STANDING: DEFINITION -- the task's literal band: the CLOSED interval
`[(8j-1)/p.1, (8j+1)/p.2]`.  Differs from `Band` exactly at the band's right endpoint. -/
def BandC (p : ℚ × ℚ) (s : ℚ) (j : ℕ) : Prop :=
  (8 * (j:ℚ) - 1) / p.1 ≤ s ∧ s ≤ (8 * (j:ℚ) + 1) / p.2

/-- STANDING: DEFINITION -- closed-band loneliness. -/
def FeasibleC (p : ℚ × ℚ) (s : ℚ) : Prop := ∃ j : ℕ, BandC p s j

/-- STANDING: DEFINITION -- the ℝ band predicate at the ℚ casts of the component's
edges: literally `Fresh.ChamberDatasheet.CompLive` at those edges. -/
def BandR (p : ℚ × ℚ) (r : ℝ) (j : ℕ) : Prop :=
  (8 * (j:ℝ) - 1) / ((p.1 : ℚ) : ℝ) ≤ r ∧ r < (8 * (j:ℝ) + 1) / ((p.2 : ℚ) : ℝ)

/-- STANDING: DEFINITION -- ℝ-tailed tuple loneliness (the datasheet's column
semantics). -/
def TupleLonelyR (rho : Fin 5 → ℚ) (r : ℝ) : Prop :=
  ∀ q ∈ K6Comps rho, ∃ j : ℕ, BandR q r j

/-! ## §2 Component well-formedness from bridge α -/

/-- Every emitted walk component has `.1 ≤ .2` — for ANY start `cur` and ANY list; in
particular for the K6 components of any 5-tuple. -/
theorem walk_snd_ge : ∀ (L : List (ℚ × ℚ)) (cur : ℚ) (s : ℚ × ℚ),
    s ∈ K6Walk cur L → s.1 ≤ s.2 := by
  intro L
  induction L with
  | nil =>
    intro cur s hs
    rw [K6Walk_nil] at hs
    by_cases h7 : cur < 7
    · rw [if_pos h7] at hs
      simp at hs
      subst hs
      exact le_of_lt h7
    · rw [if_neg h7] at hs
      simp at hs
  | cons q rest ih =>
    intro cur s hs
    rw [K6Walk_cons] at hs
    rw [List.mem_append] at hs
    rcases hs with hs | hs
    · by_cases hcq : q.1 > cur
      · rw [if_pos hcq] at hs
        simp at hs
        subst hs
        exact le_of_lt hcq
      · rw [if_neg hcq] at hs
        simp at hs
    · exact ih (max cur q.2) s hs

theorem comp_fst_le_snd (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho) :
    p.1 ≤ p.2 :=
  walk_snd_ge (Merged (zonesAll rho)) 1 p (by simpa only [K6Comps] using hp)

theorem comp_fst_ge1 (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho) :
    1 ≤ p.1 :=
  walk_ge (Merged (zonesAll rho)) 1 p (by simpa only [K6Comps] using hp)

/-- The α-consumption: a genuine K6 component has `1 ≤ p.2` (`comps_lonely` at the
right endpoint, well-formed by `comp_fst_le_snd`). -/
theorem comp_snd_ge1 (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho) :
    1 ≤ p.2 :=
  (comps_lonely rho p.2 ⟨p, hp, comp_fst_le_snd rho p hp, le_refl _⟩).1

/-! ## §3 Lap-0 helpers -/

/-- Lap 0 of a component with `1 ≤ p.2` catches no tail above 1: a tail in lap 0
satisfies `s < 1/p.2 ≤ 1`. -/
theorem band0_lt1 {p : ℚ × ℚ} {s : ℚ} (hb1 : 1 ≤ p.2) (hB : Band p s 0) : s < 1 := by
  have hb0 : (0:ℚ) < p.2 := lt_of_lt_of_le (by norm_num : (0:ℚ) < 1) hb1
  obtain ⟨_, h2⟩ := hB
  have h8 : (8 * ((0:ℕ):ℚ) + 1 : ℚ) = 1 := by norm_num
  rw [h8] at h2
  have hle : (1:ℚ) / p.2 ≤ 1 := (div_le_one hb0).mpr hb1
  linarith

/-- Closed-band lap-0 variant. -/
theorem bandC0_le1 {p : ℚ × ℚ} {s : ℚ} (hb1 : 1 ≤ p.2) (hB : BandC p s 0) : s ≤ 1 := by
  have hb0 : (0:ℚ) < p.2 := lt_of_lt_of_le (by norm_num : (0:ℚ) < 1) hb1
  obtain ⟨_, h2⟩ := hB
  have h8 : (8 * ((0:ℕ):ℚ) + 1 : ℚ) = 1 := by norm_num
  rw [h8] at h2
  have hle : (1:ℚ) / p.2 ≤ 1 := (div_le_one hb0).mpr hb1
  linarith

/-! ## §4 The band-union lemmas (general list form) -/

/-- **Lemma β (band-union, datasheet convention).**  One column-dead component kills
the tuple's running intersection over the [25, 50) column: if `p ∈ K6Comps rho` is
`ColDead` (no tail of the column lies in any band of `p`), then for every tail
`s ∈ [25, 50)` at least one component of the tuple is not a lonely window at `s`.
No hypotheses on the other components; the list may be empty (then `hp` fails). -/
theorem band_union50 (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hdead : ColDead p) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ TupleLonely rho s := by
  intro hall
  obtain ⟨j, hB⟩ := hall p hp
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    linarith [band0_lt1 (comp_snd_ge1 rho p hp) hB, hs]
  · exact hdead s hs h50 j hB

/-- The no-lonely-ρ column statement (¬∃ form): the tuple's [25, 50) column is dead. -/
theorem tuple_no_lonely50 (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hdead : ColDead p) : ¬ ∃ s : ℚ, 25 ≤ s ∧ s < 50 ∧ TupleLonely rho s := by
  rintro ⟨s, hs, h50, hall⟩
  exact band_union50 rho p hp hdead s hs h50 hall

/-- The task's literal conclusion: for every tail of the column, at least one
component of the tuple is NOT a lonely window at it. -/
theorem exists_not_lonely50 (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hdead : ColDead p) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ∃ q ∈ K6Comps rho, ¬ Feasible q s := by
  by_contra hcon
  push Not at hcon
  exact band_union50 rho p hp hdead s hs h50 hcon

/-- **Lemma β (the task's literal form).**  CLOSED bands `[(8j-1)/a, (8j+1)/b]`, laps
`j ≥ 1`, column unbounded above: exactly the stated antecedent gives
`¬(∀ q ∈ K6Comps rho, FeasibleC q s)` for EVERY `s ≥ 25` — in particular over
[25, 50). -/
theorem band_union (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hdead : ∀ s : ℚ, 25 ≤ s → ∀ j : ℕ, 1 ≤ j → ¬ BandC p s j)
    (s : ℚ) (hs : (25:ℚ) ≤ s) :
    ¬ ∀ q ∈ K6Comps rho, FeasibleC q s := by
  intro hall
  obtain ⟨j, hB⟩ := hall p hp
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    linarith [bandC0_le1 (comp_snd_ge1 rho p hp) hB, hs]
  · exact hdead s hs j hj1 hB

/-- The task's literal antecedent gives the unbounded no-lonely-ρ column (¬∃ form). -/
theorem tuple_no_lonely_unbounded (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hdead : ∀ s : ℚ, 25 ≤ s → ∀ j : ℕ, 1 ≤ j → ¬ BandC p s j) :
    ¬ ∃ s : ℚ, 25 ≤ s ∧ ∀ q ∈ K6Comps rho, FeasibleC q s := by
  rintro ⟨s, hs, hall⟩
  exact band_union rho p hp hdead s hs hall

/-- **The containment join.**  A dead interval `[A, B]` INSIDE some component's hull
kills the tuple over the [25, 50) column (robust to the [1, 7] clipping of boundary
components, where the datasheet's recorded edges are a sub-interval of the Lean
component). -/
theorem band_union50_subset (rho : Fin 5 → ℚ) (q : ℚ × ℚ) (hq : q ∈ K6Comps rho)
    (A B : ℚ) (hcont : q.1 ≤ A ∧ B ≤ q.2) (hB1 : (1:ℚ) ≤ B)
    (hdead : ColDead (A, B)) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ TupleLonely rho s := by
  intro hall
  obtain ⟨j, hB⟩ := hall q hq
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    linarith [band0_lt1 (comp_snd_ge1 rho q hq) hB, hs]
  · have hjq : (1:ℚ) ≤ (j:ℚ) := Nat.cast_le.mpr hj1
    have hq1 : (1:ℚ) ≤ q.1 := comp_fst_ge1 rho q hq
    refine hdead s hs h50 j ⟨?_, ?_⟩
    · exact le_trans (div_le_div_of_nonneg_left
        (by linarith : (0:ℚ) ≤ 8 * (j:ℚ) - 1)
        (lt_of_lt_of_le (by norm_num : (0:ℚ) < 1) hq1) hcont.1) hB.1
    · exact lt_of_lt_of_le hB.2 (div_le_div_of_nonneg_left
        (by linarith : (0:ℚ) ≤ 8 * (j:ℚ) + 1)
        (lt_of_lt_of_le (by norm_num : (0:ℚ) < 1) hB1) hcont.2)

/-! ## §5 The datasheet wiring (ℝ) -/

/-- **The ℝ datasheet wiring (direct).**  The datasheet's own atom —
`Fresh.ChamberDatasheet.ColDead50` at the ℚ casts of the component's edges — kills the
ℝ-tailed tuple over the [25, 50) column.  The instantiation is definitional: `BandR`
IS `CompLive` at those edges, so the all-lonely hypothesis instantiates straight into
the atom; even lap 0 is covered (`ColDead50` quantifies over all laps). -/
theorem band_union_R (rho : Fin 5 → ℚ) (p : ℚ × ℚ) (hp : p ∈ K6Comps rho)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((p.1 : ℚ) : ℝ) ((p.2 : ℚ) : ℝ))
    (r : ℝ) (hr : (25:ℝ) ≤ r) (h50 : r < 50) :
    ¬ TupleLonelyR rho r := by
  intro hall
  obtain ⟨j, hB⟩ := hall p hp
  exact hcd r hr h50 j hB

/-- **The ℝ→ℚ transport.**  A real-edged datasheet atom gives the ℚ-convention column
death at the cast edges (the standard cast lemmas, all unconditional). -/
theorem colDead50_imp (a b : ℚ) (A B : ℝ) (hA : (a : ℝ) = A) (hB : (b : ℝ) = B)
    (hcd : Fresh.ChamberDatasheet.ColDead50 A B) :
    ColDead (a, b) := by
  intro s hs h50 j hBnd
  apply hcd ((s : ℚ) : ℝ) (by exact_mod_cast hs) (by exact_mod_cast h50) j
  constructor
  · rw [← hA]
    exact_mod_cast hBnd.1
  · rw [← hB]
    exact_mod_cast hBnd.2

/-- **The composed datasheet→β shape.**  Atom (`ColDead50 A B`) + join
(`(a, b) ∈ K6Comps rho` with the cast edges) ⟹ the class's column death over
[25, 50) at the tuple level. -/
theorem band_union50_via_datasheet (rho : Fin 5 → ℚ) (a b : ℚ) (A B : ℝ)
    (hA : (a : ℝ) = A) (hB : (b : ℝ) = B) (hp : (a, b) ∈ K6Comps rho)
    (hcd : Fresh.ChamberDatasheet.ColDead50 A B) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ TupleLonely rho s :=
  band_union50 rho (a, b) hp (colDead50_imp a b A B hA hB hcd) s hs h50

/-! ## §6 The worked instance (`rhoEx = ![2, 3, 4, 6, 8]`) -/

/-- The worked instance's SECOND K6 component (α's `compsEx`). -/
theorem pEx_mem : ((3/2 : ℚ), (7/4 : ℚ)) ∈ K6Comps rhoEx := by
  rw [compsEx]
  decide

/-- **The worked column-dead component (closed bands, unbounded, all laps).**
`(3/2, 7/4)`'s lap-1 band is `[14/3, 36/7]` (entirely below 25) and every lap ≥ 2
band is empty (`14(8j-1) ≤ 12(8j+1)` forces `j ≤ 13/8`), so no tail `s ≥ 25` lies in
any closed band — the task's literal column-death antecedent, at full strength. -/
theorem pEx_dead : ∀ s : ℚ, 25 ≤ s → ∀ j : ℕ,
    ¬ BandC ((3/2 : ℚ), (7/4 : ℚ)) s j := by
  intro s hs j hB
  obtain ⟨h1, h2⟩ := hB
  have h1' : (8 * (j:ℚ) - 1) / (3/2 : ℚ) ≤ s := h1
  have h2' : s ≤ (8 * (j:ℚ) + 1) / (7/4 : ℚ) := h2
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    norm_num at h2'
    linarith
  · have hjq : (1:ℚ) ≤ (j:ℚ) := Nat.cast_le.mpr hj1
    have e1 : (8 * (j:ℚ) - 1) ≤ s * (3/2 : ℚ) := (div_le_iff₀ (by norm_num)).mp h1'
    have e2 : s * (7/4 : ℚ) ≤ (8 * (j:ℚ) + 1) := (le_div_iff₀ (by norm_num)).mp h2'
    have e3 : (8 * (j:ℚ) - 1) * (7/4 : ℚ) ≤ s * (3/2 : ℚ) * (7/4 : ℚ) :=
      mul_le_mul_of_nonneg_right e1 (by norm_num)
    have e4 : (3/2 : ℚ) * (s * (7/4 : ℚ)) ≤ (3/2 : ℚ) * (8 * (j:ℚ) + 1) :=
      mul_le_mul_of_nonneg_left e2 (by norm_num)
    have e5 : (8 * (j:ℚ) - 1) * (7/4 : ℚ) ≤ (8 * (j:ℚ) + 1) * (3/2 : ℚ) := by
      linarith [e3, e4]
    have hjq2 : (j:ℚ) < 2 := by linarith
    have hj2 : j < 2 := by exact_mod_cast hjq2
    have hjz : j = 1 := by omega
    subst hjz
    norm_num at h2'
    linarith

/-- The worked component is column-dead over the [25, 50) column in the datasheet's
right-open convention (an open band is contained in the closed one). -/
theorem pEx_comp_ColDead : ColDead ((3/2 : ℚ), (7/4 : ℚ)) := by
  intro s hs h50 j hB
  obtain ⟨h1, h2⟩ := hB
  have h1' : (8 * (j:ℚ) - 1) / (3/2 : ℚ) ≤ s := h1
  have h2' : s < (8 * (j:ℚ) + 1) / (7/4 : ℚ) := h2
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    norm_num at h2'
    linarith
  · exact pEx_dead s hs j ⟨h1', le_of_lt h2'⟩

/-- The cast bridge for the worked component's edges. -/
theorem castEx_a : ((3/2 : ℚ) : ℝ) = (3/2 : ℝ) := by norm_num
theorem castEx_b : ((7/4 : ℚ) : ℝ) = (7/4 : ℝ) := by norm_num

/-- **The datasheet two-line fires on the worked component at its real-cast edges**
(`datasheet_D2` with `J = 1`: `a + b = 13/4 ≤ 4 = 8(J+1)(b-a)` and `9 ≤ 25b = 175/4`). -/
theorem pEx_real_atom :
    Fresh.ChamberDatasheet.ColDead50 ((3/2 : ℚ) : ℝ) ((7/4 : ℚ) : ℝ) := by
  rw [castEx_a, castEx_b]
  exact Fresh.ChamberDatasheet.datasheet_D2 (3/2 : ℝ) (7/4 : ℝ) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The derived no-lonely-ρ conclusion (datasheet convention, [25, 50)).** -/
theorem rhoEx_no_lonely50 : ∀ s : ℚ, 25 ≤ s → s < 50 → ¬ TupleLonely rhoEx s :=
  fun s hs h50 =>
    band_union50 rhoEx ((3/2 : ℚ), (7/4 : ℚ)) pEx_mem pEx_comp_ColDead s hs h50

/-- ¬∃ form: the worked tuple's [25, 50) column is dead. -/
theorem rhoEx_tuple_no_lonely50 :
    ¬ ∃ s : ℚ, 25 ≤ s ∧ s < 50 ∧ TupleLonely rhoEx s :=
  tuple_no_lonely50 rhoEx ((3/2 : ℚ), (7/4 : ℚ)) pEx_mem pEx_comp_ColDead

/-- The task's literal phrasing: for every tail in the column, at least one component
of the worked tuple is NOT a lonely window at it. -/
theorem rhoEx_exists_not_lonely : ∀ s : ℚ, 25 ≤ s → s < 50 →
    ∃ q ∈ K6Comps rhoEx, ¬ Feasible q s :=
  fun s hs h50 =>
    exists_not_lonely50 rhoEx ((3/2 : ℚ), (7/4 : ℚ)) pEx_mem pEx_comp_ColDead s hs h50

/-- Closed-band unbounded form (the task's literal antecedent, full strength). -/
theorem rhoEx_no_lonely_unbounded :
    ¬ ∃ s : ℚ, 25 ≤ s ∧ ∀ q ∈ K6Comps rhoEx, FeasibleC q s :=
  tuple_no_lonely_unbounded rhoEx ((3/2 : ℚ), (7/4 : ℚ)) pEx_mem
    (fun s hs j _ => pEx_dead s hs j)

theorem rhoEx_exists_not_lonelyC : ∀ s : ℚ, 25 ≤ s →
    ∃ q ∈ K6Comps rhoEx, ¬ FeasibleC q s := by
  intro s hs
  by_contra hcon
  push Not at hcon
  exact rhoEx_no_lonely_unbounded ⟨s, hs, hcon⟩

/-- ℝ-tailed datasheet form for the worked tuple. -/
theorem rhoEx_no_lonely_R : ∀ r : ℝ, 25 ≤ r → r < 50 → ¬ TupleLonelyR rhoEx r :=
  fun r hr h50 =>
    band_union_R rhoEx ((3/2 : ℚ), (7/4 : ℚ)) pEx_mem pEx_real_atom r hr h50

/-- **The full datasheet→β loop on the worked instance:** the `datasheet_D2` atom at
the real-cast edges ⟹ the tuple has no lonely tail over [25, 50). -/
theorem rhoEx_no_lonely50_via_datasheet :
    ∀ s : ℚ, 25 ≤ s → s < 50 → ¬ TupleLonely rhoEx s :=
  band_union50_via_datasheet rhoEx (3/2 : ℚ) (7/4 : ℚ) ((3/2 : ℚ) : ℝ) ((7/4 : ℚ) : ℝ)
    rfl rfl pEx_mem pEx_real_atom

/-! ## §7 Axiom footprints -/

#print axioms walk_snd_ge
#print axioms comp_fst_le_snd
#print axioms comp_fst_ge1
#print axioms comp_snd_ge1
#print axioms band0_lt1
#print axioms bandC0_le1
#print axioms band_union50
#print axioms tuple_no_lonely50
#print axioms exists_not_lonely50
#print axioms band_union
#print axioms tuple_no_lonely_unbounded
#print axioms band_union50_subset
#print axioms band_union_R
#print axioms colDead50_imp
#print axioms band_union50_via_datasheet
#print axioms pEx_mem
#print axioms pEx_dead
#print axioms pEx_comp_ColDead
#print axioms castEx_a
#print axioms castEx_b
#print axioms pEx_real_atom
#print axioms rhoEx_no_lonely50
#print axioms rhoEx_tuple_no_lonely50
#print axioms rhoEx_exists_not_lonely
#print axioms rhoEx_no_lonely_unbounded
#print axioms rhoEx_exists_not_lonelyC
#print axioms rhoEx_no_lonely_R
#print axioms rhoEx_no_lonely50_via_datasheet

end Fresh.K6BandUnion
