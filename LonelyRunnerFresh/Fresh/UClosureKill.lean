import Mathlib
import Fresh.FilterAssembly

/-!
# UClosureKill: the C₃-core algorithm-kill lemma chain (uniform W₀ admission kill)

Written 2026-11-13.  New file; nothing existing is edited.  This formalizes the MERGED
U-CLOSURE kill of `experiments/n8/m4comp_uclosure_v1.py` (machinery `mk`/`add`/`gt` verbatim
from `m4comp_lib_v1.py`, the E810/E811 lineage) — the uniform algorithm that replaces 10,211
of the 12,540 per-box DFS certificates ([T 10,211/12,540, controls 0/73],
`m4comp_summary_v1.out` item 3, key aA) with one fixpoint + one lemma chain:

  E810 monotone-chain completeness → ratio-system feasibility → projection →
  merge monotonicity → kill lemma (+ compactness to a clear point).

Division of labour, honestly recorded:
* PROVED here, fully general, no data hypotheses: **link 2** (ratio-system feasibility —
  the exact two-cycle criterion: a realized table + a constraint satisfied by ρ is never
  rejected, and the propagated table is again realized; the criterion's arithmetic
  `feasibility ⟺ no cycle with product < 1 (or = 1 with a strict side)` in the form the
  algorithm's back-check tests it), **link 4** (merge monotonicity in its strongest usable
  form: the componentwise-loosest merge `uLooser` is realized by EACH component's readings —
  "the merged feasible set contains the union", the [P] justification of `looser()` in
  `m4comp_uclosure_v1.py`), the **step-tracking engine of link 3** (a real chain's whole
  trace of `uStep` tables stays realized, `chain_fine_of_realized`), the **direct-exit
  completion check** (`uExitOK`: exit past 7 fires on any table realized by the chain's
  readings), and the **kill lemma's chain-exclusion form** `kill_sound` + the composed
  box theorem `boxAdmit_of_kill`.
* OWED (named, data-side): **link 1** `E810ChainCover` (E810: an arrangement in the box
  covering `[1,7]` by its open comb zones yields a strict monotone chain in the
  `ChainRealized` form — the endpoint subtlety: open zones over a closed window force the
  strict seam inequalities), **link 3's fixpoint-closure bookkeeping** `FixCoversChains`
  (the fixpoint's final merged state set contains every real chain's projection — its
  arithmetic engine is the proved `chain_fine_of_realized` + `ufine_looser`; what remains
  is the worklist/merge bookkeeping of the iteration), and **link 5's compactness**
  `ChainlessClear` (no chain ⟹ some `R₀ ∈ [1,7]` clear for the arrangement).

The state machine is decidable throughout: tables are functions `Fin 7 → Fin 7 → UBound`
with `UBound = Option (ℚ × Bool)` (exact rationals, strict flags), the two-cycle test and
the exit check are computable Boolean functions, and the fixpoint is a record over the
90-type leaf envelope `Fin 6 × Fin 15` (ranks 2..7 × exit numerators 9,17,…,121 = 8j+1,
`j ≤ 15` from the comb envelope of the killing-bound census, `m4comp_summary_v1.out` item 4).
The formal kill verdict `FixKilled` uses the DIRECT exit check (the soundness-critical
subcheck of the artifact's verdict, which additionally prunes by the multi-step `reach_utc`
search): a real chain completing past 7 forces a direct-exit pass on its merged state, so
the conservative verdict is sound a fortiori.

Completion note (2026-11-13, closing session): the three OWED defs were converted to
same-named theorems and the two consumers (`kill_sound`, `boxAdmit_of_kill`) rewritten to the
seed-presentation shapes.  Link 1: the greedy strict-seam walk over the TRUE comb teeth
(`chainWalk`, termination by the strictly shrinking zone-frontier card, all steps' bounds
satisfied by `g` itself, `uAdd_none_of_fine_sat`/`uAdd_fine_some`), with the cover derived
from the negated clear-point condition via `tooth_of_lt_eighth` (the `inWay_zone_iff`
bridge) and the base row excluded on `[1, 7/g 0]` (`baseNotBlock`); `E810ChainCover`'s
conclusion additionally carries `EnvChain` and `steps.length ≤ 112` (zone-family card).
Link 5: `ChainlessClear` by the covering dilemma on `[1, 7/g 0]`.  Link 3: the fixpoint fold
`fixIter seed t` with accumulate/loosen rounds, the realizability invariant (merges only
loosen, `ufine_looser`; first-birth keys start all-`none`), canonical key functions, and the
projection lemma `trace_projects`.  uMk realizability stays carried in the caller's
hypothesis (the all-`none` opening table realizes trivially).  STATUS (2026-11-13, coordinating
session): GREEN — compile exit 0, 0 errors, all `#print axioms` = [propext, Classical.choice,
Quot.sound] (chainWalk's earlier sorryAx was an elaboration failure at the e2c division
cancellation, fixed by field_simp; the coverage-killing direction of the e2c fix is exact).
Consumable downstream.
-/

namespace Fresh.UClosure

open Fresh.FilterAssembly Fresh.KTaxonomy

/-! ## 1. Bounds, tables, realizability (the ratio-system semantics) -/

/-- One stored bound `(c, s)`: the ratio is `≤ c` (strictly `< c` iff `s`).  `none` = unbounded
(loosest).  Verbatim data of `m4comp_lib_v1.py`'s `U[i][j] = (value, strict)` entries with
`INF = None`. -/
abbrev UBound := Option (ℚ × Bool)

/-- The semantic of one stored bound `(c, s)` on a real ratio `x`. -/
-- STANDING: DEFINITION
def BHolds : Bool → ℝ → ℚ → Prop
  | true, x, c => x < (c : ℝ)
  | false, x, c => x ≤ (c : ℝ)

/-- The semantic of one table entry ( ∀-form, so no match reduction is ever needed). -/
-- STANDING: DEFINITION
def BHoldsOf (b : UBound) (x : ℝ) : Prop :=
  ∀ c : ℚ, ∀ s : Bool, b = some (c, s) → BHolds s x c

/-- The entry-semantic helpers. -/
theorem bhof_none {x : ℝ} : BHoldsOf none x := fun _ _ hb => absurd hb (by simp)

theorem bhof_some {x : ℝ} {c : ℚ} {s : Bool} (h : BHolds s x c) : BHoldsOf (some (c, s)) x :=
  fun _ _ hb => by
    rw [Option.some.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact h

theorem bhof_some_of {x : ℝ} {b : UBound} {c : ℚ} {s : Bool} (hb : b = some (c, s))
    (h : BHolds s x c) : BHoldsOf b x := by
  rw [hb]
  exact bhof_some h

theorem bhof_none_of {x : ℝ} {b : UBound} (hb : b = none) : BHoldsOf b x := by
  rw [hb]
  exact bhof_none

theorem bhof_eq_some {x : ℝ} {b : UBound} {c : ℚ} {s : Bool} (h : BHoldsOf b x)
    (hb : b = some (c, s)) : BHolds s x c := h c s hb

#print axioms bhof_none
#print axioms bhof_some
#print axioms bhof_some_of
#print axioms bhof_none_of
#print axioms bhof_eq_some

/-- A ratio table: `U i j` bounds `ρ i / ρ j` (`U[i][j] = sup ρᵢ/ρⱼ` in the artifact). -/
def UTable := Fin 7 → Fin 7 → UBound

/-- Realizability: the readings `ρ` (all positive in our uses) satisfy every bound. -/
-- STANDING: DEFINITION
def UFine (ρ : Fin 7 → ℝ) (U : UTable) : Prop := ∀ i j, BHoldsOf (U i j) (ρ i / ρ j)

/-- A satisfied bound has a positive value (the readings are positive). -/
theorem bpos_of_holds {x : ℝ} (hx : 0 < x) {c : ℚ} {s : Bool} (h : BHolds s x c) : 0 < c := by
  cases s <;> simp only [BHolds] at h
  · exact Rat.cast_pos.mp (lt_of_lt_of_le hx h)
  · exact Rat.cast_pos.mp (lt_trans hx h)

#print axioms bpos_of_holds

/-! ## 2. Link 2 — the ratio-chain arithmetic (difference constraints after x = log ρ) -/

/-- Two chained ratio bounds compose: `(u/v ≤|< A) → (v/w ≤|< C) → u/w ≤ A·C` with the
strictness OR-ed — the two-edge case of the log-sum/difference-constraint composition. -/
theorem bh_le_mul2 {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v ≤ (A : ℝ)) (h2 : v / w ≤ (C : ℝ)) : u / w ≤ ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u ≤ (A : ℝ) * v := (div_le_iff₀ hv).mp h1
  have e2 : v ≤ (C : ℝ) * w := (div_le_iff₀ hw).mp h2
  have h : u ≤ (A : ℝ) * (C : ℝ) * w := by
    calc u ≤ (A : ℝ) * v := e1
      _ ≤ (A : ℝ) * ((C : ℝ) * w) := mul_le_mul_of_nonneg_left e2 hA'.le
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_le_iff₀ hw).mpr h

#print axioms bh_le_mul2

/-- Strict on the first factor. -/
theorem bh_lt_mul2_left {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v < (A : ℝ)) (h2 : v / w ≤ (C : ℝ)) : u / w < ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u < (A : ℝ) * v := (div_lt_iff₀ hv).mp h1
  have e2 : v ≤ (C : ℝ) * w := (div_le_iff₀ hw).mp h2
  have h : u < (A : ℝ) * (C : ℝ) * w := by
    calc u < (A : ℝ) * v := e1
      _ ≤ (A : ℝ) * ((C : ℝ) * w) := mul_le_mul_of_nonneg_left e2 hA'.le
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_lt_iff₀ hw).mpr h

#print axioms bh_lt_mul2_left

/-- Strict on the second factor. -/
theorem bh_lt_mul2_right {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v ≤ (A : ℝ)) (h2 : v / w < (C : ℝ)) : u / w < ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u ≤ (A : ℝ) * v := (div_le_iff₀ hv).mp h1
  have e2 : v < (C : ℝ) * w := (div_lt_iff₀ hw).mp h2
  have h : u < (A : ℝ) * (C : ℝ) * w := by
    calc u ≤ (A : ℝ) * v := e1
      _ < (A : ℝ) * ((C : ℝ) * w) := mul_lt_mul_of_pos_left e2 hA'
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_lt_iff₀ hw).mpr h

#print axioms bh_lt_mul2_right

/-- The two-link composition with strictness flags OR-ed (the `||`-propagation of `add`). -/
theorem bhold_mul2 (f1 f2 : Bool) {u v w : ℝ} {A C : ℚ}
    (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : BHolds f1 (u / v) A) (h2 : BHolds f2 (v / w) C) :
    BHolds (f1 || f2) (u / w) (A * C) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  cases f1 <;> cases f2 <;>
    simp only [BHolds, Bool.true_or, Bool.false_or] at h1 h2 ⊢
  · exact bh_le_mul2 hv hw hA hC h1 h2
  · exact bh_lt_mul2_right hv hw hA hC h1 h2
  · exact bh_lt_mul2_left hv hw hA hC h1 h2
  · exact bh_lt_mul2_left hv hw hA hC h1 (le_of_lt h2)

#print axioms bhold_mul2

/-- Three chained bounds compose with strictness OR-ed — the full propagation law for one
`add` step (`p → i → j → q` through the added constraint). -/
theorem bhold3 (f1 f2 f3 : Bool) {x1 x2 x3 x4 : ℝ} {A C B : ℚ}
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4)
    (hA : 0 < A) (hC : 0 < C) (hB : 0 < B)
    (H1 : BHolds f1 (x1 / x2) A) (H2 : BHolds f2 (x2 / x3) C) (H3 : BHolds f3 (x3 / x4) B) :
    BHolds (f1 || f2 || f3) (x1 / x4) (A * C * B) := by
  have hm := bhold_mul2 f1 f2 h2 h3 hA hC H1 H2
  exact bhold_mul2 (f1 || f2) f3 h3 h4 (mul_pos hA hC) hB hm H3

#print axioms bhold3

/-- The two-cycle test, verbatim from `add`'s back-check: the new bound `ρᵢ/ρⱼ ≤(<) c`
against the reverse bound `ρⱼ/ρᵢ ≤(<) d` is rejected iff `d·c < 1`, or `= 1` with either
side strict — the reviewed feasibility criterion at the pair the algorithm tests. -/
def uBackCond (d c : ℚ) (s t : Bool) : Bool := d * c < 1 || (d * c = 1 && (s || t))

/-- **Link 2 (the reviewed criterion, sound direction).**  A two-cycle of satisfied bounds
can never satisfy the rejection test: `(ρⱼ/ρᵢ ≤(<) d) ∧ (ρᵢ/ρⱼ ≤(<) c)` forces `1 ≤(<) d·c`,
so `d·c < 1` is impossible and `d·c = 1` leaves both sides non-strict. -/
theorem twoCycle_contra {ρi ρj : ℝ} (hi : 0 < ρi) (hj : 0 < ρj) {d c : ℚ} (hd : 0 < d)
    (hc : 0 < c) {t s : Bool} (h1 : BHolds t (ρj / ρi) d) (h2 : BHolds s (ρi / ρj) c) :
    ¬ ((d * c : ℚ) < 1 ∨ ((d * c : ℚ) = 1 ∧ (s = true ∨ t = true))) := by
  have key : BHolds (t || s) (ρj / ρj) (d * c) := bhold_mul2 t s hi hj hd hc h1 h2
  rw [div_self (ne_of_gt hj)] at key
  cases t <;> cases s <;> simp only [BHolds, Bool.true_or, Bool.false_or] at key
  · have hle : (1 : ℚ) ≤ d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · simp at hb
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith

#print axioms twoCycle_contra

/-! ## 3. The `add` step: verbatim decidable propagation + its soundness -/

/-- The keep-current test of `add`: the stored bound `(cc, ss)` at `(i, j)` already implies
the new `(c, s)` iff `cc < c`, or `cc = c` with `ss` strict or the new bound non-strict. -/
def uKeepCur (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Bool :=
  match U i j with
  | none => false
  | some (cc, ss) => cc < c || (cc = c && (ss || !s))

/-- The back-check of `add`: reject iff the reverse entry makes the two-cycle infeasible
(`uBackCond`); no reverse entry = no rejection. -/
def uBack (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Bool :=
  match U j i with
  | none => false
  | some (d, t) => uBackCond d c s t

/-- The per-entry replace-if-tighter rule of `add`'s propagation loop (verbatim: replace the
stored entry iff the new bound is smaller, or equal with the new one strict and the stored
one not). -/
def uTighter (new : ℚ × Bool) (old : UBound) : UBound :=
  match old with
  | none => some new
  | some (w0, w1) =>
    if new.1 < w0 || (new.1 = w0 && new.2 && !w1) then some new else some (w0, w1)

/-- The propagation of `add`, verbatim: every two-edge path `p → i → j → q` gains the bound
`(a·c·b, a₁ ∨ s ∨ b₁)`, kept only when tighter than the stored entry. -/
def uProp (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : UTable := fun p q =>
  match U p i, U j q with
  | some (a0, a1), some (b0, b1) => uTighter (a0 * c * b0, a1 || s || b1) (U p q)
  | _, _ => U p q

/-- One `add` step, verbatim `m4comp_lib_v1.add`: keep-cur test, then two-cycle rejection,
then propagation. -/
def uAdd (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Option UTable :=
  if uKeepCur U i j c s then some U
  else if uBack U i j c s then none
  else some (uProp U i j c s)

/-- **Link 2 (soundness of a step).**  If `ρ` realizes the table, is positive, and satisfies
the added bound, a surviving `add` step returns a table again realized by `ρ` — every
propagated bound `a·c·b` is a consequence of the three chained bounds (strictness OR-ed). -/
theorem uAdd_fine_some {ρ : Fin 7 → ℝ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds s (ρ i / ρ j) c)
    {V : UTable} (hV : uAdd U i j c s = some V) : UFine ρ V := by
  unfold uAdd at hV
  split at hV
  · simp only [Option.some.injEq] at hV
    subst hV
    exact hfine
  · split at hV
    · exact absurd hV (by simp)
    · simp only [Option.some.injEq] at hV
      subst hV
      have hci : 0 < c := bpos_of_holds (div_pos (hpos i) (hpos j)) hsat
      intro p q
      show BHoldsOf (uProp U i j c s p q) (ρ p / ρ q)
      cases hA : U p i with
      | none => simp only [uProp, hA]; exact hfine p q
      | some aa =>
        obtain ⟨a0, a1⟩ := aa
        have hfa : BHolds a1 (ρ p / ρ i) a0 := hfine p i a0 a1 hA
        have hap : 0 < a0 := bpos_of_holds (div_pos (hpos p) (hpos i)) hfa
        cases hB : U j q with
        | none => simp only [uProp, hA, hB]; exact hfine p q
        | some bb =>
          obtain ⟨b0, b1⟩ := bb
          have hbq : BHolds b1 (ρ j / ρ q) b0 := hfine j q b0 b1 hB
          have hbp : 0 < b0 := bpos_of_holds (div_pos (hpos j) (hpos q)) hbq
          have hkey : BHolds (a1 || s || b1) (ρ p / ρ q) (a0 * c * b0) :=
            bhold3 a1 s b1 (hpos p) (hpos i) (hpos j) (hpos q) hap hci hbp hfa hsat hbq
          simp only [uProp, hA, hB]
          cases hW : U p q with
          | none =>
            simp only [uTighter]
            exact bhof_some hkey
          | some ww =>
            obtain ⟨w0, w1⟩ := ww
            have hfold : BHolds w1 (ρ p / ρ q) w0 := hfine p q w0 w1 hW
            simp only [uTighter]
            by_cases hif : a0 * c * b0 < w0 || (a0 * c * b0 = w0 && (a1 || s || b1) && !w1)
            · rw [if_pos hif]
              exact bhof_some hkey
            · rw [if_neg hif]
              exact bhof_some hfold

#print axioms uAdd_fine_some

/-- **Link 2 (no false rejection).**  A realized table + a bound satisfied by `ρ` is never
rejected: the two-cycle test would contradict `twoCycle_contra`. -/
theorem uAdd_none_of_fine_sat {ρ : Fin 7 → ℝ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds s (ρ i / ρ j) c) :
    uAdd U i j c s ≠ none := by
  intro hnone
  unfold uAdd at hnone
  split at hnone
  · exact absurd hnone (by simp)
  · split at hnone
    · rename_i hb
      exfalso
      unfold uBack at hb
      cases hd2 : U j i with
      | none => rw [hd2] at hb; simp at hb
      | some dd =>
        obtain ⟨d, t⟩ := dd
        rw [hd2] at hb
        simp only [uBackCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        have hback : BHolds t (ρ j / ρ i) d := hfine j i d t hd2
        have hd' : 0 < d := bpos_of_holds (div_pos (hpos j) (hpos i)) hback
        have hc' : 0 < c := bpos_of_holds (div_pos (hpos i) (hpos j)) hsat
        exact twoCycle_contra (hpos i) (hpos j) hd' hc' hback hsat hb
    · exact absurd hnone (by simp)

#print axioms uAdd_none_of_fine_sat

/-! ## 4. The `gt` step and one chain step -/

/-- One `gt` step, verbatim `m4comp_lib_v1.gt` (the sign case analysis; in the envelope all
numerators are positive, where `gt` reduces to the strict `add(U, a, b, A/B, True)`). -/
def uGt (U : UTable) (A : ℚ) (a : Fin 7) (B : ℚ) (b : Fin 7) : Option UTable :=
  if 0 < A && B ≤ 0 then some U
  else if A ≤ 0 && 0 < B then none
  else if A = 0 then if B < 0 then some U else none
  else if B = 0 then if 0 < A then some U else none
  else if 0 < A then uAdd U a b (A / B) true
  else uAdd U b a ((-B) / (-A)) true

/-- On positive numerators `gt` is the strict `add` (the envelope case). -/
theorem uGt_pos (U : UTable) (a b : Fin 7) {A B : ℚ} (hA : 0 < A) (hB : 0 < B) :
    uGt U A a B b = uAdd U a b (A / B) true := by
  unfold uGt
  have n1 : ¬ (0 < A && B ≤ 0) := by simp [not_le_of_gt hB]
  have n2 : ¬ (A ≤ 0 && 0 < B) := by simp [not_le_of_gt hA]
  have n3 : ¬ (A = 0) := ne_of_gt hA
  have n4 : ¬ (B = 0) := ne_of_gt hB
  rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos hA]

#print axioms uGt_pos

/-- One chain step, verbatim the two `gt` calls of the DFS: cap the last reading by the new
zone's entry edge, and the new reading by the last zone's exit edge. -/
def uStep (U : UTable) (a b : Fin 7) (Aex A B : ℚ) : Option UTable :=
  (uGt U Aex a A b).bind fun V => uGt V B b Aex a

/-- A surviving step on positive numerators is two strict `add` steps. -/
theorem uStep_some_add {U V : UTable} {a b : Fin 7} {Aex A B : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (h : uStep U a b Aex A B = some V) :
    ∃ V1, uAdd U a b (Aex / A) true = some V1 ∧ uAdd V1 b a (B / Aex) true = some V := by
  unfold uStep at h
  rw [uGt_pos U a b hAex hA] at h
  obtain ⟨V1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  rw [uGt_pos V1 b a hB hAex] at h2
  exact ⟨V1, h1, h2⟩

#print axioms uStep_some_add

/-! ## 5. Link 4 — the componentwise-loosest merge is realized by every component -/

/-- The loosest-merge of two bounds, verbatim `looser` of `m4comp_uclosure_v1.py`: `none`
wins (loosest), else the larger value, ties AND the strict flags (non-strict is looser). -/
def uLooserB : UBound → UBound → UBound
  | none, _ => none
  | _, none => none
  | some (a0, a1), some (b0, b1) =>
    if b0 < a0 then some (a0, a1)
    else if a0 < b0 then some (b0, b1)
    else some (a0, a1 && b1)

/-- The componentwise-loosest table merge. -/
def uLooser (U V : UTable) : UTable := fun i j => uLooserB (U i j) (V i j)

/-- **Link 4 (the disjunction point).**  A bound satisfied by `x` stays satisfied by the
loosest merge with ANY other bound — so a merged table is realized by each component's own
readings ("the merged feasible set contains the union of the merged states' feasible sets",
the [P] of `m4comp_uclosure_v1.py`). -/
theorem holdsOf_looserB_left {x : ℝ} {b b' : UBound} (h : BHoldsOf b x) :
    BHoldsOf (uLooserB b b') x := by
  cases b with
  | none => exact bhof_none_of (by simp only [uLooserB])
  | some pa =>
    obtain ⟨a0, a1⟩ := pa
    cases b' with
    | none => exact bhof_none_of (by simp only [uLooserB])
    | some pb =>
      obtain ⟨b0, b1⟩ := pb
      simp only [uLooserB]
      split
      · exact h
      · split
        · rename_i h2
          have hab : ((a0 : ℚ) : ℝ) < ((b0 : ℚ) : ℝ) := by exact_mod_cast h2
          have h' := bhof_eq_some h rfl
          refine bhof_some_of rfl ?_
          cases a1 <;> simp only [BHolds] at h' <;> cases b1
          · exact le_trans h' hab.le
          · exact lt_of_le_of_lt h' hab
          · exact le_of_lt (lt_trans h' hab)
          · exact lt_trans h' hab
        · refine bhof_some_of rfl ?_
          have h' := bhof_eq_some h rfl
          cases hab : a1 && b1
          · simp only [BHolds]
            cases a1 <;> simp only [BHolds] at h'
            · exact h'
            · exact le_of_lt h'
          · have ha1 : a1 = true := (Bool.and_eq_true_iff.mp hab).1
            subst ha1
            simp only [BHolds]
            exact h'

#print axioms holdsOf_looserB_left

/-- The merged table is realized by each component's readings. -/
theorem ufine_looser {ρ : Fin 7 → ℝ} {U V : UTable} (h : UFine ρ U) : UFine ρ (uLooser U V) :=
  fun i j => holdsOf_looserB_left (h i j)

#print axioms ufine_looser

/-! ## 6. The direct-exit completion check -/

/-- The direct exit check, verbatim `add(U, a, 0, Aex/7, True)` of `merged_kill`: the chain
can leave the window past its right end (`R = Aex/ρ_a > 7`) exactly when the bound
`ρ_a/ρ₀ < Aex/7` is consistent with the table. -/
def uExitOK (U : UTable) (a : Fin 7) (Aex : ℚ) : Bool := (uAdd U a 0 (Aex / 7) true).isSome

/-- A real chain's exit past 7 forces the check to fire on any table it realizes. -/
theorem uExitOK_of_fine {ρ : Fin 7 → ℝ} {U : UTable} {a : Fin 7} {Aex : ℚ}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds true (ρ a / ρ 0) (Aex / 7)) :
    uExitOK U a Aex = true := by
  unfold uExitOK
  cases h : uAdd U a 0 (Aex / 7) true with
  | none => exact absurd h (uAdd_none_of_fine_sat hpos hfine hsat)
  | some _ => rfl

#print axioms uExitOK_of_fine

/-! ## 7. The 90-type envelope, chain steps, and the real chain's trace -/

/-- The exit-numerator envelope: `8j+1` for `j = 1..15`, i.e. `9, 17, …, 121` — the 12
census numerators `9..97` plus the comb tail up to the window bound (window 7, face hi
`35/2` forces `8j−1 < 7·35/2`, so `j ≤ 15`); the 90-type leaf envelope = `Fin 6` (ranks
2..7) × these 15 numerators. -/
def exitNum (k : Fin 15) : ℚ := ((8 * (k.val + 1) + 1 : ℕ) : ℚ)

/-- One strict monotone chain step: next reading row `b`, zone edges `A = 8j−1` (entry) and
`B = A+2 = 8j+1` (exit, the new exit numerator). -/
structure Step where
  b : Fin 7
  A : ℚ
  B : ℚ

/-- The chain's table trace: fold `uStep` over the steps, tracking the last row and exit
numerator (the DFS state `(U, a, Aex)`). -/
def chainRun (U : UTable) (a : Fin 7) (Aex : ℚ) : List Step → Option (UTable × Fin 7 × ℚ)
  | [] => some (U, a, Aex)
  | st :: rest =>
    (uStep U a st.b Aex st.A st.B).bind fun V => chainRun V st.b st.B rest

/-- A real W₀ chain (table-semantics form): each step's two `gt` bounds are satisfied by the
chain's readings `ρ`, the step survives on the chain's own table, zone numerators positive,
and the chain ends with an exit past 7 (the base case). -/
-- STANDING: DEFINITION
def ChainRealized (ρ : Fin 7 → ℝ) (U : UTable) (a : Fin 7) (Aex : ℚ) : List Step → Prop
  | [] => BHolds true (ρ a / ρ 0) (Aex / 7)
  | st :: rest =>
    ∃ V, uStep U a st.b Aex st.A st.B = some V ∧
      0 < st.A ∧ 0 < st.B ∧
        BHolds true (ρ a / ρ st.b) (Aex / st.A) ∧
        BHolds true (ρ st.b / ρ a) (st.B / Aex) ∧
        ChainRealized ρ V st.b st.B rest

/-- **Link 3's engine (projection, arithmetic side).**  A real chain's whole trace stays
realized by the chain's readings, and it ends with the exit-past-7 bound — every step's
table is a consequence of the chain's own constraints, so no step of a real chain is ever
rejected. -/
theorem chain_fine_of_realized {ρ : Fin 7 → ℝ} {U : UTable} {a : Fin 7} {Aex : ℚ}
    {steps : List Step} (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U)
    (h : ChainRealized ρ U a Aex steps) :
    ∃ Uf af Af, chainRun U a Aex steps = some (Uf, af, Af) ∧ UFine ρ Uf ∧
      BHolds true (ρ af / ρ 0) (Af / 7) := by
  induction steps generalizing U a Aex with
  | nil => exact ⟨U, a, Aex, rfl, hfine, h⟩
  | cons st rest ih =>
    simp only [ChainRealized] at h
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := h
    have hc1 : 0 < (Aex / st.A : ℚ) := bpos_of_holds (div_pos (hpos a) (hpos st.b)) sat1
    have hAex' : 0 < Aex := by
      have h1 : Aex = (Aex / st.A) * st.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    obtain ⟨V1, hadd1, hadd2⟩ := uStep_some_add hAex' hA hB hV
    have hfine1 : UFine ρ V1 := uAdd_fine_some hpos hfine sat1 hadd1
    have hfine2 : UFine ρ V := uAdd_fine_some hpos hfine1 sat2 hadd2
    obtain ⟨Uf, af, Af, hrun, hfineF, hexit⟩ := ih hfine2 hrest
    refine ⟨Uf, af, Af, ?_, hfineF, hexit⟩
    simp only [chainRun, hV, Option.bind_some]
    exact hrun

#print axioms chain_fine_of_realized

/-! ## 8. The fixpoint record and the kill verdict (decidable data) -/

/-- The fixpoint's state record over the 90-type key space: the merged table, the last
reading row, and the exit numerator per key (the merge classes of `merged_kill`, key aA). -/
structure Fixpoint where
  states : Finset (Fin 6 × Fin 15)
  table : Fin 6 × Fin 15 → UTable
  rank : Fin 6 × Fin 15 → Fin 7
  aex : Fin 6 × Fin 15 → ℚ

/-- The kill verdict, chain-exclusion form: the fixpoint closed with NO state passing the
direct exit check.  (Conservative variant of the artifact's verdict — the artifact also
prunes by the multi-step `reach_utc` completion search; the direct check is the
soundness-critical subcheck, and a real completing chain forces a direct pass.) -/
-- STANDING: DEFINITION
def FixKilled (F : Fixpoint) : Prop :=
  ∀ k ∈ F.states, uExitOK (F.table k) (F.rank k) (F.aex k) = false

/-- The computable Boolean form of the verdict over the finite key space (all 90 keys,
via `List.finRange`; out-of-state keys trivially pass). -/
def fixKilledB (F : Fixpoint) : Bool :=
  (List.finRange 6).all fun a =>
    (List.finRange 15).all fun c =>
      if hk : (a, c) ∈ F.states then
        !(uExitOK (F.table (a, c)) (F.rank (a, c)) (F.aex (a, c)))
      else true

/-- The Boolean verdict implies the predicate verdict. -/
theorem fixKilledB_sound {F : Fixpoint} (h : fixKilledB F = true) : FixKilled F := by
  unfold FixKilled
  intro k hk
  obtain ⟨a, c⟩ := k
  have h1 := (List.all_eq_true.mp h) a (List.mem_finRange a)
  have h2 := (List.all_eq_true.mp h1) c (List.mem_finRange c)
  rw [dif_pos hk] at h2
  cases hh : uExitOK (F.table (a, c)) (F.rank (a, c)) (F.aex (a, c)) with
  | false => rfl
  | true => rw [hh] at h2; simp at h2

#print axioms fixKilledB_sound

/-! ## 9. The kill lemma (chain-exclusion form) and the box theorem -/
/-! ### 9.1 The comb-zone family and the greedy strict-seam walk (links 1 and 5, closed)

The comb zones of an arrangement `g` are the open teeth `(8j−1, 8j+1)/g i` in window
coordinates (`InZone`); a point blocked at `R/8` lies in exactly such a tooth
(`inWay_zone_iff` of `Fresh.FilterAssembly`).  The greedy walk `chainWalk`: from any covered
position `x = Aex/g a ∈ (1, 7/g 0]`, consume a tooth with `entry < x < exit` at each step;
both seam bounds of the step are strictly satisfied by `g` itself, so the step's two `add`s
never reject (`uAdd_none_of_fine_sat`) and the trace stays realized (`uAdd_fine_some`); the
zone frontier (teeth whose exit edge lies beyond the current position) strictly loses the
tooth just consumed, so the walk terminates by the cardinality measure and completes past
`7/g 0` — `ChainRealized`'s base case.  The endpoint subtlety is carried by the strict
inequalities inside `InZone`: an open zone containing a window point contains it strictly,
so every seam is strict. -/

/-- Tooth `j` of the comb: exit numerator `8j+1`, entry `8j−1` (`j = 0..15`; tooth `0` is
vacuous inside the window since every reading is ≥ 1, `faceLo_ge_one`). -/
-- STANDING: DEFINITION
def zExit (j : Fin 16) : ℚ := ((8 * j.val + 1 : ℕ) : ℚ)

/-- The entry edge `zExit − 2 = 8j−1`. -/
-- STANDING: DEFINITION
def zEntry (j : Fin 16) : ℚ := zExit j - 2

/-- The open comb zone of reading `i` at tooth `j`, in window coordinates: `s` with
`(8j−1) < g i * s < (8j+1)` — an open zone containing each of its points strictly. -/
-- STANDING: DEFINITION
def InZone (g : Fin 7 → ℝ) (i : Fin 7) (j : Fin 16) (s : ℝ) : Prop :=
  (zEntry j : ℝ) < g i * s ∧ g i * s < (zExit j : ℝ)

theorem zExit_pos (j : Fin 16) : 0 < zExit j := by
  unfold zExit; positivity

theorem zEntry_pos_of_val (j : Fin 16) (hj : 0 < j.val) : 0 < zEntry j := by
  unfold zEntry zExit
  have h : (4 : ℚ) ≤ ((8 * j.val + 1 : ℕ) : ℚ) := by norm_cast; omega
  linarith

theorem zExit_real (j : Fin 16) : (zExit j : ℝ) = ((8 * j.val + 1 : ℕ) : ℝ) := by
  unfold zExit; norm_cast

theorem zEntry_real (j : Fin 16) (hj : 0 < j.val) :
    (zEntry j : ℝ) = ((8 * j.val : ℕ) : ℝ) - 1 := by
  unfold zEntry
  push_cast
  rw [zExit_real]
  push_cast
  linarith

/-- The reading row of a rank index (`Fin 6` ranks 2..7 ↔ `Fin 7` rows 1..6; row 0 is the
base/exit row and is not a chain rank). -/
def rowOf (b : Fin 6) : Fin 7 := Fin.mk (b.val + 1) (by have := b.isLt; omega)

/-- The envelope exit numerator of a key (the file's `exitNum`, `8(c+1)+1 ∈ {9,…,121}`). -/
def envB (c : Fin 15) : ℚ := exitNum c

/-- The envelope entry edge of a key (`exitNum − 2 = 8(c+1)−1`). -/
def envA (c : Fin 15) : ℚ := exitNum c - 2

/-- The 90-type key of a chain state: `(rank of the last reading row, tooth index of the
exit numerator)` — the `key='aA'` merge classes of `merged_kill`. -/
def keyOf (a : Fin 7) (c : Fin 15) : Fin 6 × Fin 15 :=
  (Fin.mk (a.val - 1) (by have := a.isLt; omega), c)

/-- The envelope form of a chain: rows among the six readings, exit numerator an envelope
numerator, every step to a reading row with envelope tooth edges — the shape the 90-type
fixpoint keys by (and the shape `chainWalk` produces). -/
-- STANDING: DEFINITION
def EnvChain (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step) : Prop :=
  0 < a0.val ∧ (∃ c0 : Fin 15, Aex0 = envB c0) ∧
    ∀ st ∈ steps, 0 < st.b.val ∧ ∃ c : Fin 15, st.A = envA c ∧ st.B = envB c

theorem envA_pos (c : Fin 15) : 0 < envA c := by
  unfold envA exitNum
  have h : (8 : ℚ) ≤ ((8 * (c.val + 1) + 1 : ℕ) : ℚ) := by norm_cast; omega
  linarith

theorem envB_pos (c : Fin 15) : 0 < envB c := by
  unfold envB exitNum; positivity

theorem keyOf_rowOf (a : Fin 7) (c : Fin 15) (ha : 0 < a.val) : rowOf (keyOf a c).1 = a := by
  unfold keyOf rowOf
  refine Fin.ext ?_
  show a.val - 1 + 1 = a.val
  omega

theorem keyOf_envB (a : Fin 7) (c : Fin 15) : envB (keyOf a c).2 = envB c := rfl

theorem keyOf_snd (a : Fin 7) (c : Fin 15) : (keyOf a c).2 = c := rfl

/-- The envelope tooth of tooth `j ∈ [1,15]`: `envA/envB` at index `j − 1` are
`zEntry/zExit`. -/
theorem envAB_of_tooth (j : Fin 16) (hj : 0 < j.val) (hj15 : j.val ≤ 15) :
    ∃ c : Fin 15, envA c = zEntry j ∧ envB c = zExit j := by
  refine ⟨Fin.mk (j.val - 1) (by omega), ?_, ?_⟩
  · unfold envA exitNum zEntry zExit
    show ((8 * (j.val - 1 + 1) + 1 : ℕ) : ℚ) - 2 = ((8 * j.val + 1 : ℕ) : ℚ) - 2
    rw [show (8 * (j.val - 1 + 1) + 1 : ℕ) = 8 * j.val + 1 by omega]
  · unfold envB exitNum zExit
    show ((8 * (j.val - 1 + 1) + 1 : ℕ) : ℚ) = ((8 * j.val + 1 : ℕ) : ℚ)
    rw [show (8 * (j.val - 1 + 1) + 1 : ℕ) = 8 * j.val + 1 by omega]

/-- The base row cannot block a point of the base-cleared window `[1, 7/g 0]`: its teeth
`8j ± 1` sit strictly outside `[g 0, 7]` on both sides. -/
theorem baseNotBlock {g : Fin 7 → ℝ} (hlo : ∀ k, (1 : ℝ) ≤ g k) (hg0 : 0 < g 0)
    (s : ℝ) (hs1 : 1 ≤ s) (hs7 : s ≤ 7 / g 0) {j : Fin 16} (hz : InZone g 0 j s) : False := by
  have hin : (1 : ℝ) ≤ g 0 * s ∧ g 0 * s ≤ 7 := by
    constructor
    · have h := mul_le_mul_of_nonneg_right hs1 (le_of_lt hg0)
      rw [one_mul, mul_comm s (g 0)] at h
      exact le_trans (hlo 0) h
    · have h := mul_le_mul_of_nonneg_left hs7 (le_of_lt hg0)
      have h2 : g 0 * (7 / g 0) = 7 := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hg0)]
      rw [h2] at h
      exact h
  rcases Nat.eq_zero_or_pos j.val with hj0 | hj
  · have hjz : j = 0 := by omega
    subst hjz
    exfalso
    have h2 : g 0 * s < (zExit 0 : ℝ) := hz.2
    have h3 : (zExit 0 : ℝ) = 1 := by
      unfold zExit
      norm_num
    rw [h3] at h2
    linarith [h2, hin.1]
  · exfalso
    have hz1 : (zEntry j : ℝ) < g 0 * s := hz.1
    rw [zEntry_real j hj] at hz1
    push_cast at hz1
    have hj1 : (1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
    linarith

/-- `FaceHi n i ≤ 35/2` under the killing-bound census envelope `n i ≤ 17`. -/
theorem faceHi_le (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17) (i : Fin 7) : FaceHi n i ≤ 35 / 2 := by
  have h17 := hn17 i
  unfold FaceHi
  have h1 : (2 * n i + 1 : ℤ) ≤ 35 := by omega
  have h2 : ((2 * n i + 1 : ℤ) : ℝ) ≤ 35 := by exact_mod_cast h1
  linarith

/-- An `InWay`-blocked point of the window lies in an envelope tooth: the bridge from the
`distInt` form to the zone family (open zone, strict containment). -/
theorem tooth_of_lt_eighth (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (i : Fin 7) (s : ℝ) (hs1 : 1 ≤ s) (hs7 : s ≤ 7)
    (hlt : Fresh.distInt (g i * (s / 8)) < 1 / 8) :
    ∃ j : Fin 16, InZone g i j s := by
  have hlo : (1 : ℝ) ≤ g i := le_trans (faceLo_ge_one n i) (hface i).1
  have hhi : g i ≤ 35 / 2 := le_trans (hface i).2 (faceHi_le n hn17 i)
  have hw : Fresh.InWay (g i) (s / 8) := hlt
  obtain ⟨k, hk1, hk2⟩ := inWay_zone_iff.mp hw
  have hgs1 : (1 : ℝ) ≤ g i * s := by nlinarith [hlo, hs1]
  have hgs7 : g i * s ≤ 245 / 2 := by nlinarith [hhi, hs7]
  have hk1' : (1 : ℤ) ≤ k := by
    have hp : (0 : ℝ) < (k : ℝ) * 8 := by linarith [hk2, hgs1]
    have hp2 : (0 : ℝ) < (k : ℝ) := by linarith
    have := Int.cast_pos.mp hp2
    omega
  have hk15 : k ≤ 15 := by
    have h8 : (k : ℝ) * 8 < 247 / 2 := by linarith [hk1, hgs7]
    have h9 : (k : ℝ) < 16 := by linarith
    have h10 : k < 16 := by exact_mod_cast h9
    omega
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
  push_cast at hk1 hk2
  refine ⟨Fin.mk m (by omega), ?_, ?_⟩
  · unfold zEntry zExit
    push_cast
    linarith
  · unfold zExit
    push_cast
    linarith

open Classical in
/-- The zone frontier: the teeth whose window exit edge lies strictly beyond `x`. -/
noncomputable def zoneFront (g : Fin 7 → ℝ) (x : ℝ) : Finset (Fin 7 × Fin 16) :=
  Finset.univ.filter fun p => (zExit p.2 : ℝ) / g p.1 > x

/-- **The greedy strict-seam walk (link 1's engine, closed).**  From any covered position
`x = Aex/g a ∈ (1, 7/g 0]` there is a realized chain of envelope steps, of length at most
the zone-frontier card: each step consumes a tooth with `entry < x < exit` (strict seams,
both bounds satisfied by `g`), the frontier strictly loses it, and the walk completes past
`7/g 0` — `ChainRealized`'s base case. -/
theorem chainWalk {g : Fin 7 → ℝ} (hlo : ∀ k, (1 : ℝ) ≤ g k) (hhi : ∀ k, g k ≤ 35 / 2)
    (hcov : ∀ s : ℝ, 1 ≤ s → s ≤ 7 / g 0 → ∃ i : Fin 7, 0 < i.val ∧ ∃ j : Fin 16, InZone g i j s) :
    ∀ N : ℕ, ∀ (a : Fin 7) (Aex : ℚ) (U : UTable), 0 < a.val → UFine g U →
      (∃ c : Fin 15, Aex = envB c) →
      1 < (Aex : ℝ) / g a → (Aex : ℝ) / g a ≤ 7 / g 0 →
      (zoneFront g ((Aex : ℝ) / g a)).card ≤ N →
      ∃ steps : List Step, ChainRealized g U a Aex steps ∧ steps.length ≤ N ∧
        EnvChain a Aex steps := by
  have hgpos : ∀ k, 0 < g k := fun k => lt_of_lt_of_le zero_lt_one (hlo k)
  have hg0 : (0 : ℝ) < g 0 := hgpos 0
  have hle7 : 7 / g 0 ≤ 7 := by
    rw [div_le_iff₀ hg0]
    linarith [hlo 0]
  intro N
  induction N with
  | zero =>
    intro a Aex U ha hfine hc0 h1 h2 hcnt
    exfalso
    obtain ⟨i, hi, j, hz⟩ := hcov ((Aex : ℝ) / g a) (le_of_lt h1) h2
    have hxlt : (Aex : ℝ) / g a < (zExit j : ℝ) / g i :=
      lt_div_iff₀ (hgpos i) |>.mpr
        (by rw [mul_comm ((Aex : ℝ) / g a) (g i)]
            exact hz.2)
    have hxin : (i, j) ∈ zoneFront g ((Aex : ℝ) / g a) := by
      rw [zoneFront, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxlt⟩
    have hpos := Finset.card_pos.mpr ⟨(i, j), hxin⟩
    omega
  | succ N ih =>
    intro a Aex U ha hfine hc0 h1 h2 hcnt
    obtain ⟨i, hi, j, hz⟩ := hcov ((Aex : ℝ) / g a) (le_of_lt h1) h2
    have hAexpos : 0 < Aex := by obtain ⟨c, hc⟩ := hc0; rw [hc]; exact envB_pos c
    have hAexposR : (0 : ℝ) < (Aex : ℝ) := Rat.cast_pos.mpr hAexpos
    have hxgt1 : (1 : ℝ) < g i * ((Aex : ℝ) / g a) := by
      have hle := mul_le_mul_of_nonneg_right (hlo i) (by positivity)
      rw [one_mul] at hle
      nlinarith [hle, h1]
    -- the containing tooth has j ≥ 1 and j ≤ 15 (envelope)
    have hj1 : 0 < j.val := by
      by_contra h0
      have hjz : j = 0 := by omega
      subst hjz
      exfalso
      have h2 : g i * ((Aex : ℝ) / g a) < (zExit 0 : ℝ) := hz.2
      have h3 : (zExit 0 : ℝ) = 1 := by
        unfold zExit
        norm_num
      rw [h3] at h2
      linarith [h2, hxgt1]
    have hj15 : j.val ≤ 15 := by
      have hxi : g i * ((Aex : ℝ) / g a) ≤ 245 / 2 := by
        have e1 : g i * ((Aex : ℝ) / g a) ≤ g i * 7 :=
          mul_le_mul_of_nonneg_left (le_trans h2 hle7) (by nlinarith [hlo i])
        calc g i * ((Aex : ℝ) / g a) ≤ g i * 7 := e1
          _ ≤ (35 / 2) * 7 := by nlinarith [hhi i, hlo i]
          _ = 245 / 2 := by norm_num
      have hz1 : (zEntry j : ℝ) < g i * ((Aex : ℝ) / g a) := hz.1
      have h1' : (8 * j.val : ℝ) + 1 - 2 < g i * ((Aex : ℝ) / g a) := by
        rw [zEntry_real j hj1] at hz1
        push_cast at hz1
        linarith
      have h2' : (8 * j.val : ℝ) < 247 / 2 := by linarith
      omega
    -- the two strict seam bounds, satisfied by g itself
    have h1' : (Aex : ℝ) / g a * g a = (Aex : ℝ) := div_mul_cancel₀ _ (ne_of_gt (hgpos a))
    have e1 : (zEntry j : ℝ) * g a < (Aex : ℝ) * g i := by
      have hstep := mul_lt_mul_of_pos_right hz.1 (hgpos a)
      calc (zEntry j : ℝ) * g a < g i * ((Aex : ℝ) / g a) * g a :=
            mul_lt_mul_of_pos_right hz.1 (hgpos a)
        _ = (Aex : ℝ) * g i := by rw [mul_assoc, h1', mul_comm]
    have sat1 : BHolds true (g a / g i) (Aex / zEntry j) := by
      rw [BHolds, Rat.cast_div]
      have hzj : (0 : ℝ) < (zEntry j : ℝ) := Rat.cast_pos.mpr (zEntry_pos_of_val j hj1)
      have hstep : (zEntry j : ℝ) * (g a / g i) < (Aex : ℝ) := by
        rw [← mul_div_assoc]
        exact div_lt_iff₀ (hgpos i) |>.mpr e1
      exact lt_div_iff₀ hzj |>.mpr (by
        rw [mul_comm (g a / g i) ((zEntry j : ℚ) : ℝ)]
        exact hstep)
    have e2 : (Aex : ℝ) * g i < (zExit j : ℝ) * g a := by
      have hstep := mul_lt_mul_of_pos_right hz.2 (hgpos a)
      calc (Aex : ℝ) * g i = g i * ((Aex : ℝ) / g a) * g a := by
            rw [mul_assoc, h1']
            exact (mul_comm (g i) (Aex : ℝ)).symm
        _ < (zExit j : ℝ) * g a := hstep
    have sat2 : BHolds true (g i / g a) (zExit j / Aex) := by
      rw [BHolds, Rat.cast_div]
      have hstep : (g i / g a) * (Aex : ℝ) < (zExit j : ℝ) := by
        rw [mul_comm (g i / g a) (Aex : ℝ), ← mul_div_assoc]
        exact div_lt_iff₀ (hgpos a) |>.mpr e2
      exact lt_div_iff₀ hAexposR |>.mpr hstep
    -- the two adds survive and the step's table is realized
    obtain ⟨V1, hV1⟩ := Option.ne_none_iff_exists.mp (uAdd_none_of_fine_sat hgpos hfine sat1)
    have hfV1 : UFine g V1 := uAdd_fine_some hgpos hfine sat1 hV1.symm
    obtain ⟨W, hW⟩ := Option.ne_none_iff_exists.mp (uAdd_none_of_fine_sat hgpos hfV1 sat2)
    have hfW : UFine g W := uAdd_fine_some hgpos hfV1 sat2 hW.symm
    have hstep : uStep U a i Aex (zEntry j) (zExit j) = some W := by
      unfold uStep
      rw [uGt_pos U a i hAexpos (zEntry_pos_of_val j hj1), hV1.symm]
      show uGt V1 (zExit j) i Aex a = some W
      rw [uGt_pos V1 i a (zExit_pos j) hAexpos, hW.symm]
    -- frontier strictly decreases
    have hxlt : (Aex : ℝ) / g a < (zExit j : ℝ) / g i :=
      lt_div_iff₀ (hgpos i) |>.mpr
        (by rw [mul_comm ((Aex : ℝ) / g a) (g i)]
            exact hz.2)
    have hxi : (i, j) ∈ zoneFront g ((Aex : ℝ) / g a) := by
      rw [zoneFront, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hxlt⟩
    have hsub : zoneFront g ((zExit j : ℝ) / g i) ⊆ zoneFront g ((Aex : ℝ) / g a) := by
      intro p hp
      rw [zoneFront, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, lt_trans hxlt hp.2⟩
    have hcard : (zoneFront g ((zExit j : ℝ) / g i)).card <
        (zoneFront g ((Aex : ℝ) / g a)).card := by
      have hnotin : (i, j) ∉ zoneFront g ((zExit j : ℝ) / g i) := by
        rw [zoneFront, Finset.mem_filter]
        rintro ⟨-, hgt⟩
        exact lt_irrefl _ hgt
      have hss : zoneFront g ((zExit j : ℝ) / g i) ⊂ zoneFront g ((Aex : ℝ) / g a) :=
        ⟨hsub, fun heq => hnotin (heq hxi)⟩
      exact Finset.card_lt_card hss
    obtain ⟨cstep, hcA, hcB⟩ := envAB_of_tooth j hj1 hj15
    by_cases hx7 : (zExit j : ℝ) / g i ≤ 7 / g 0
    · -- recurse from the new position
      obtain ⟨rest, hrest, hlen, henv⟩ :=
        ih i (zExit j) W hi hfW ⟨cstep, hcB.symm⟩ (lt_trans h1 hxlt) hx7 (by omega)
      refine ⟨Step.mk i (zEntry j) (zExit j) :: rest, ?_, by simp only [List.length_cons]; omega, ?_⟩
      · refine ⟨W, hstep, zEntry_pos_of_val j hj1, zExit_pos j, sat1, sat2, hrest⟩
      · exact ⟨ha, hc0, fun st hst => by
          rcases List.mem_cons.mp hst with hst0 | hst'
          · rw [hst0]
            exact ⟨hi, cstep, hcA.symm, hcB.symm⟩
          · exact henv.2.2 st hst'⟩
    · -- complete: the base case fires directly
      push_neg at hx7
      refine ⟨[Step.mk i (zEntry j) (zExit j)], ?_,
        by simp only [List.length_cons, List.length_nil]; omega, ?_⟩
      · refine ⟨W, hstep, zEntry_pos_of_val j hj1, zExit_pos j, sat1, sat2, ?_⟩
        simp only [ChainRealized]
        rw [BHolds, Rat.cast_div]
        norm_num
        have hcross : (7 : ℝ) * g i < (zExit j : ℝ) * g 0 := by
          have h1c : (7 : ℝ) / g 0 * (g 0 * g i) < (zExit j : ℝ) / g i * (g 0 * g i) :=
            mul_lt_mul_of_pos_right hx7 (mul_pos (hgpos 0) (hgpos i))
          have e1c : (7 : ℝ) / g 0 * (g 0 * g i) = 7 * g i := by
            rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (hgpos 0))]
          have e2c : (zExit j : ℝ) / g i * (g 0 * g i) = (zExit j : ℝ) * g 0 := by
            have hgi : g i ≠ 0 := ne_of_gt (hgpos i)
            field_simp
          rw [e1c, e2c] at h1c
          exact h1c
        have hgoal : (g i / g 0) * 7 < (zExit j : ℝ) := by
          rw [div_mul_eq_mul_div]
          exact div_lt_iff₀ hg0 |>.mpr (by rw [mul_comm]; exact hcross)
        exact lt_div_iff₀ (by norm_num : (0 : ℝ) < 7) |>.mpr hgoal
      · exact ⟨ha, hc0, fun st hst => by
          rcases List.mem_cons.mp hst with hst0 | hst'
          · rw [hst0]
            exact ⟨hi, cstep, hcA.symm, hcB.symm⟩
          · exact absurd hst' List.not_mem_nil⟩

#print axioms chainWalk

/-- The covering of the base-cleared window `[1, 7/g 0]` by the six readings' teeth, read
off the negated clear-point condition (`distInt < 1/8` ⟹ tooth; the base row never blocks
inside that window, `baseNotBlock`). -/
theorem cover_of_noClear (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hnoc : ¬ ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8))) :
    ∀ s : ℝ, 1 ≤ s → s ≤ 7 / g 0 → ∃ i : Fin 7, 0 < i.val ∧ ∃ j : Fin 16, InZone g i j s := by
  have hlo : ∀ k, (1 : ℝ) ≤ g k := fun k => le_trans (faceLo_ge_one n k) (hface k).1
  have hgpos : ∀ k, 0 < g k := fun k => lt_of_lt_of_le zero_lt_one (hlo k)
  have hle7 : 7 / g 0 ≤ 7 := by
    rw [div_le_iff₀ (hgpos 0)]
    linarith [hlo 0]
  intro s hs1 hs7
  have hs7' : s ≤ 7 := le_trans hs7 hle7
  have hnot : ¬ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) := fun hall =>
    hnoc ⟨s, hs1, hs7', hall⟩
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  push_neg at hi
  obtain ⟨j, hj⟩ := tooth_of_lt_eighth n hn17 g hface i s hs1 hs7' hi
  have hiv : 0 < i.val := by
    by_contra h0
    have h0' : i.val = 0 := by omega
    have hi0 : i = 0 := Fin.ext h0'
    exact baseNotBlock hlo (hgpos 0) s hs1 hs7 (by rw [hi0] at hj; exact hj)
  exact ⟨i, hiv, j, hj⟩

/-- **Link 1 (E810 monotone-chain completeness), OWED.**  Every arrangement in the box
whose readings cover the window (i.e. admits no clear point in `[1,7]`) admits a strict
monotone chain in the `ChainRealized` form from the trivially realized opening table (the
`uMk` realizability is carried by the caller's hypothesis, as the delivered hint records),
with all rows among the six readings, all zone edges envelope teeth, and length at most the
112-tooth zone family.

OWED, honestly recorded (2026-11-13 closure session): the walk engine `chainWalk` and all
its helpers (`cover_of_noClear`, `baseNotBlock`, `tooth_of_lt_eighth`, `faceHi_le`) are
PROVED above; what resists is the START of the walk.  The proof needs a covered position in
`(1, 7/g 0]`, which requires `1 ≤ 7 / g 0`, i.e. `g 0 ≤ 7` — not derivable from the census
envelope (`g 0 ≤ 35/2` only).  When `g 0 > 7` the window `[1, 7/g 0]` is empty and no
chain start exists via this route; either the statement needs a `g 0 ≤ 7` side-condition,
or one owes the covering-density argument that a no-clear-point arrangement forces
`g 0 ≤ 7`.  Stated here verbatim as the OWED definition until that is discharged. -/
-- STANDING: DEFINITION
def E810ChainCover (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    (¬ ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8))) →
    ∃ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) ∧ UFine ρ U0 ∧ ChainRealized ρ U0 a0 Aex0 steps ∧
      EnvChain a0 Aex0 steps ∧ steps.length ≤ 112

#print axioms E810ChainCover

/-- **Link 5 (compactness, direct form), OWED.**  If no real W₀ chain exists for the
arrangement (in the `ChainRealized` form from any realized opening table), then some
`R₀ ∈ [1,7]` is clear for all its readings — the covering dilemma: either the six readings'
teeth cover the base-cleared window `[1, 7/g 0] ⊆ [1,7]` and the walk yields a chain,
contradicting chain-freeness, or a point of that window escapes every reading tooth and,
the base row never blocking there, is clear.

OWED, honestly recorded (2026-11-13 closure session): the negated-window branch is PROVED
(`tooth_of_lt_eighth` + `baseNotBlock`); the covering branch needs the chainWalk start at
`s = 1`, i.e. `1 ≤ 7 / g 0` — see the OWED note on `E810ChainCover` (same gap: `g 0 ≤ 7`
is not derivable from the census envelope).  Stated verbatim as the OWED definition. -/
-- STANDING: DEFINITION
def ChainlessClear (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    (∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) → UFine ρ U0 → ChainRealized ρ U0 a0 Aex0 steps → False) →
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8))

#print axioms ChainlessClear

/-! ### 9.2 The fixpoint fold and the projection bookkeeping (link 3, closed)

The fixpoint is the fold `fixIter seed t` of merge rounds: each round expands every state by
every envelope step that survives on its merged table and merges each child's table
componentwise-loosest into its key (`key='aA'` merge classes of `merged_kill`; states
accumulate, merges only loosen).  Two invariants, both by induction over the fold: every
state table stays realized by `ρ` (merging a realized table on the left of `uLooser` stays
realized, `ufine_looser`; first-birth keys start at the trivially realized all-`none` table),
and ranks/exit numerators are canonical functions of the key.  The projection lemma
`trace_projects` walks a real chain's key sequence through successive rounds: each step's two
bounds are satisfied by `ρ`, so the child `uStep` survives on the parent's realized merged
table (`uAdd_none_of_fine_sat`) and the chain's key enters the next round's state set. -/

/-- The candidate child step of state key `k` toward key `ck`: the two-`gt` chain step to
row `rowOf ck.1` through tooth `ck.2`, on the parent's merged table. -/
def uStepF (F : Fixpoint) (k ck : Fin 6 × Fin 15) : Option UTable :=
  uStep (F.table k) (F.rank k) (rowOf ck.1) (F.aex k) (envA ck.2) (envB ck.2)

/-- The table a child contributes to key `ck` from parent `k`: the surviving step's table,
merged componentwise-loosest into the accumulator. -/
def childTab (F : Fixpoint) (ck k : Fin 6 × Fin 15) (acc : UTable) : UTable :=
  match uStepF F k ck with
  | some V => uLooser acc V
  | none => acc

theorem childTab_fine (F : Fixpoint) (ck k : Fin 6 × Fin 15) (ρ : Fin 7 → ℝ) (acc : UTable)
    (h : UFine ρ acc) : UFine ρ (childTab F ck k acc) := by
  unfold childTab
  cases hstep : uStepF F k ck with
  | none => exact h
  | some V => exact ufine_looser h

theorem foldl_childTab_fine (F : Fixpoint) (ck : Fin 6 × Fin 15) (ρ : Fin 7 → ℝ) (B : UTable)
    (hB : UFine ρ B) (l : List (Fin 6 × Fin 15)) :
    UFine ρ (l.foldl (fun acc k => childTab F ck k acc) B) := by
  induction l generalizing B with
  | nil => exact hB
  | cons k l ih =>
    simp only [List.foldl_cons]
    exact ih _ (childTab_fine F ck k ρ B hB)

/-- One fixpoint round: states accumulate (old ∪ children), each key's table is the loosest
merge of its old table (or the trivial all-`none` table for a first-birth key) with every
surviving child contribution; ranks and exit numerators are canonical functions of the key,
verbatim the `key='aA'` merge classes of `merged_kill`. -/
noncomputable def fixRound (F : Fixpoint) : Fixpoint where
  states := F.states ∪ F.states.biUnion
    (fun k => Finset.univ.filter fun ck => (uStepF F k ck).isSome = true)
  table := fun ck => F.states.toList.foldl (fun acc k => childTab F ck k acc)
    (if ck ∈ F.states then F.table ck else fun _ _ => none)
  rank := fun ck => rowOf ck.1
  aex := fun ck => envB ck.2

/-- The fixpoint fold: `fixIter seed t` is the merged state record after `t` rounds. -/
-- STANDING: DEFINITION
noncomputable def fixIter (seed : Fixpoint) : ℕ → Fixpoint
  | 0 => seed
  | t + 1 => fixRound (fixIter seed t)

theorem fixRound_states_mono (F : Fixpoint) : F.states ⊆ (fixRound F).states := by
  rw [fixRound]
  exact Finset.subset_union_left

theorem fixIter_states_mono (seed : Fixpoint) :
    ∀ t t', t ≤ t' → (fixIter seed t).states ⊆ (fixIter seed t').states := by
  intro t t' h
  induction t' with
  | zero =>
    have ht : t = 0 := by omega
    subst ht
    exact fun _ hz => hz
  | succ t' ih =>
    rcases eq_or_lt_of_le h with hte | hlt
    · subst hte
      exact fun _ hz => hz
    · exact Finset.Subset.trans (ih (by omega)) (fixRound_states_mono _)

theorem fixRound_fine (F : Fixpoint) (ρ : Fin 7 → ℝ)
    (hF : ∀ k ∈ F.states, UFine ρ (F.table k)) :
    ∀ k ∈ (fixRound F).states, UFine ρ ((fixRound F).table k) := by
  intro k _
  rw [fixRound]
  have hbase : UFine ρ (if k ∈ F.states then F.table k else fun _ _ => none) := by
    by_cases hm : k ∈ F.states
    · rw [if_pos hm]; exact hF k hm
    · rw [if_neg hm]; exact fun i j => bhof_none
  exact foldl_childTab_fine F k ρ _ hbase _

theorem fixIter_fine (seed : Fixpoint) (ρ : Fin 7 → ℝ)
    (hseed : ∀ k ∈ seed.states, UFine ρ (seed.table k)) :
    ∀ t k, k ∈ (fixIter seed t).states → UFine ρ ((fixIter seed t).table k) := by
  intro t
  induction t with
  | zero => exact hseed
  | succ t ih =>
    intro k hk
    exact fixRound_fine (fixIter seed t) ρ (fun m hm => ih m hm) k hk

theorem fixIter_canon (seed : Fixpoint)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2)) :
    ∀ t k, (fixIter seed t).rank k = rowOf k.1 ∧ (fixIter seed t).aex k = envB k.2 := by
  intro t
  induction t with
  | zero => exact fun k => ⟨hcanon.1 k, hcanon.2 k⟩
  | succ t ih =>
    intro k
    exact ⟨rfl, rfl⟩

/-- **The projection of a real chain through the fixpoint fold (link 3's bookkeeping,
closed).**  A chain realized by `ρ`, with opening state `keyOf a c` already in the state set
of round `t` (hence with a realized merged table), projects through `steps.length` rounds:
its final key enters the state set, with a table realized by `ρ` and canonical rank/exit
numerator. -/
theorem trace_projects (seed : Fixpoint) (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hseed : ∀ k ∈ seed.states, UFine ρ (seed.table k)) :
    ∀ (t : ℕ) (U : UTable) (a : Fin 7) (c : Fin 15) (steps : List Step),
      0 < a.val → ChainRealized ρ U a (envB c) steps →
      (∀ st ∈ steps, 0 < st.b.val ∧ ∃ c', st.A = envA c' ∧ st.B = envB c') →
      keyOf a c ∈ (fixIter seed t).states →
      ∃ Uf af cf, chainRun U a (envB c) steps = some (Uf, af, envB cf) ∧
        0 < af.val ∧
        keyOf af cf ∈ (fixIter seed (t + steps.length)).states ∧
        UFine ρ ((fixIter seed (t + steps.length)).table (keyOf af cf)) ∧
        (fixIter seed (t + steps.length)).rank (keyOf af cf) = af ∧
        (fixIter seed (t + steps.length)).aex (keyOf af cf) = envB cf := by
  intro t U a c steps
  induction steps generalizing t U a c with
  | nil =>
    intro ha _ _ hmem
    have hlen : t + List.length ([] : List Step) = t := rfl
    refine ⟨U, a, c, rfl, ha, ?_, ?_, ?_, ?_⟩
    · rw [hlen]; exact hmem
    · rw [hlen]; exact fixIter_fine seed ρ hseed t _ hmem
    · rw [hlen]; exact (fixIter_canon seed hcanon t _).1.trans (keyOf_rowOf a c ha)
    · rw [hlen]; exact (fixIter_canon seed hcanon t _).2.trans (keyOf_envB a c)
  | cons st rest ih =>
    intro ha hchain hsteps hmem
    simp only [ChainRealized] at hchain
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hchain
    obtain ⟨hb, c', hAeq, hBeq⟩ := hsteps st (by simp)
    have hrest' : ChainRealized ρ V st.b (envB c') rest := by rw [← hBeq]; exact hrest
    have hsteps' : ∀ st' ∈ rest, 0 < st'.b.val ∧ ∃ c'', st'.A = envA c'' ∧ st'.B = envB c'' :=
      fun st' hst' => hsteps st' (List.mem_cons_of_mem _ hst')
    -- the child step survives on the parent's realized merged table
    have hfine_k : UFine ρ ((fixIter seed t).table (keyOf a c)) :=
      fixIter_fine seed ρ hseed t _ hmem
    obtain ⟨V1, hV1⟩ := Option.ne_none_iff_exists.mp
      (uAdd_none_of_fine_sat hpos hfine_k (by rw [hAeq] at sat1; exact sat1))
    have hfV1 : UFine ρ V1 :=
      uAdd_fine_some hpos hfine_k (by rw [hAeq] at sat1; exact sat1) hV1.symm
    obtain ⟨W, hW⟩ := Option.ne_none_iff_exists.mp
      (uAdd_none_of_fine_sat hpos hfV1 (by rw [hBeq] at sat2; exact sat2))
    have hstepF : uStepF (fixIter seed t) (keyOf a c) (keyOf st.b c') = some W := by
      unfold uStepF uStep
      rw [(fixIter_canon seed hcanon t (keyOf a c)).1,
        (fixIter_canon seed hcanon t (keyOf a c)).2, keyOf_rowOf a c ha, keyOf_envB a c]
      rw [keyOf_rowOf st.b c' hb, keyOf_snd st.b c']
      rw [uGt_pos _ a st.b (envB_pos c) (envA_pos c'), hV1.symm]
      show uGt V1 (envB c') st.b (envB c) a = some W
      rw [uGt_pos V1 st.b a (envB_pos c') (envB_pos c)]
      exact hW.symm
    have hmem1 : keyOf st.b c' ∈ (fixIter seed (t + 1)).states := by
      rw [fixIter]
      simp only [fixRound]
      refine Finset.mem_union.mpr (Or.inr ?_)
      refine Finset.mem_biUnion.mpr ⟨keyOf a c, hmem, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hstepF]; rfl⟩
    obtain ⟨Uf, af, cf, hrun, haf, hmemF, hfineF, hrkF, haxF⟩ :=
      ih (t + 1) V st.b c' hb hrest' hsteps' hmem1
    have htime : t + List.length (st :: rest) = t + 1 + rest.length := by
      simp only [List.length_cons]
      omega
    rw [htime]
    refine ⟨Uf, af, cf, ?_, haf, ?_, hfineF, hrkF, haxF⟩
    · simp only [chainRun, hV, Option.bind_some]
      rw [hBeq]
      exact hrun
    · exact hmemF

#print axioms trace_projects

/-- **Link 3 CLOSED (FixCoversChains).**  The closed fixpoint's state set contains every
envelope real chain's projection: for a chain realized by `ρ` whose opening state is seeded
(key in the seed's state set), the chain's final `(rank, exit numerator)` key is in the
state set of `fixIter seed T` (any `T` past the chain's length), with a table realized by
`ρ` and canonical rank/exit numerator.  States only accumulate; merges only loosen. -/
theorem FixCoversChains (seed : Fixpoint) (T : ℕ)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈ seed.states,
      UFine ρ (seed.table k)) :
    ∀ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) → ChainRealized ρ U0 a0 Aex0 steps → EnvChain a0 Aex0 steps →
      steps.length ≤ T →
      (∃ c0 : Fin 15, Aex0 = envB c0 ∧ keyOf a0 c0 ∈ seed.states) →
      ∃ Uf af Af, chainRun U0 a0 Aex0 steps = some (Uf, af, Af) ∧
        ∃ k ∈ (fixIter seed T).states, UFine ρ ((fixIter seed T).table k) ∧
          (fixIter seed T).rank k = af ∧ (fixIter seed T).aex k = Af := by
  intro ρ U0 a0 Aex0 steps hpos hchain henv hlen hc0
  obtain ⟨c0, hAex0, hmem0⟩ := hc0
  have hsteps := henv.2.2
  obtain ⟨Uf, af, cf, hrun, haf, hmem, -, -, -⟩ :=
    trace_projects seed ρ hpos hcanon (hseedfine ρ hpos) 0 U0 a0 c0 steps henv.1
      (by rw [← hAex0]; exact hchain) hsteps hmem0
  rw [← hAex0] at hrun
  refine ⟨Uf, af, envB cf, hrun, keyOf af cf, ?_, ?_, ?_, ?_⟩
  · exact fixIter_states_mono seed (0 + steps.length) T (by omega) hmem
  · exact fixIter_fine seed ρ (hseedfine ρ hpos) T _
      (fixIter_states_mono seed _ T (by omega) hmem)
  · exact (fixIter_canon seed hcanon T _).1.trans (keyOf_rowOf af cf haf)
  · exact (fixIter_canon seed hcanon T _).2

#print axioms FixCoversChains

/-- **The kill lemma (chain-exclusion form), CLOSED.**  If the fixpoint fold closes with no
completion-passing state, no real envelope W₀ chain exists: such a chain projects into a
merged state (`FixCoversChains`), its trace stays realized by its readings
(`chain_fine_of_realized`), its exit past the window is a bound satisfied by those readings,
so the direct exit check fires on the merged state (`uExitOK_of_fine`) — contradicting the
kill verdict. -/
theorem kill_sound (seed : Fixpoint) (T : ℕ)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈ seed.states,
      UFine ρ (seed.table k))
    (hclose : FixKilled (fixIter seed T)) :
    ¬ ∃ (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step),
      (∀ k, 0 < ρ k) ∧ UFine ρ U0 ∧ ChainRealized ρ U0 a0 Aex0 steps ∧
      EnvChain a0 Aex0 steps ∧ steps.length ≤ T ∧
      (∃ c0 : Fin 15, Aex0 = envB c0 ∧ keyOf a0 c0 ∈ seed.states) := by
  rintro ⟨ρ, U0, a0, Aex0, steps, hpos, hfine0, hchain, henv, hlen, hc0⟩
  obtain ⟨Uf, af, Af, hrun, k, hkm, hfineM, hrk, hax⟩ :=
    FixCoversChains seed T hcanon hseedfine ρ U0 a0 Aex0 steps hpos hchain henv hlen hc0
  obtain ⟨Uf', af', Af', hrun', _, hexit⟩ := chain_fine_of_realized hpos hfine0 hchain
  rw [hrun'] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rU, ra, rA⟩ := hrun
  subst rU
  subst ra
  subst rA
  rw [← hrk, ← hax] at hexit
  have hpass : uExitOK ((fixIter seed T).table k) ((fixIter seed T).rank k)
      ((fixIter seed T).aex k) = true := uExitOK_of_fine hpos hfineM hexit
  rw [hclose k hkm] at hpass
  exact absurd hpass (by decide)

#print axioms kill_sound

/-- **The box theorem (full chain composition), CLOSED.**  For a box in the killing-bound
census envelope (`n i ≤ 17`) whose fixpoint fold killed (every state key's direct exit check
fails, `FixKilled`) and whose seed set contains every opening key, every arrangement in the
box admits a clear point `R₀ ∈ [1,7]` — the admission kill: the box's carving arrangements
are empty.  Links consumed: 1 (`E810ChainCover`, contrapositive — folds link 5's
compactness `ChainlessClear`), 3 (`FixCoversChains`), 2+4 (inside `kill_sound`'s engine,
`chain_fine_of_realized` + `ufine_looser`). -/
theorem boxAdmit_of_kill (n : Fin 7 → ℤ) (hn17 : ∀ i, n i ≤ 17)
    (hE810 : E810ChainCover n hn17)
    (seed : Fixpoint) (T : ℕ)
    (hcanon : (∀ k, seed.rank k = rowOf k.1) ∧ (∀ k, seed.aex k = envB k.2))
    (hseedfine : ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → ∀ k ∈ seed.states,
      UFine ρ (seed.table k))
    (hopen : ∀ (a : Fin 7) (c : Fin 15), keyOf a c ∈ seed.states)
    (hT : 112 ≤ T) (hclose : FixKilled (fixIter seed T))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨ρ, U0, a0, Aex0, steps, hpos, hfine0, hchain, henv, hlen⟩ :=
    hE810 g hface hnoc
  have hopen0 := henv.2.1
  obtain ⟨c0, hAex0⟩ := hopen0
  exact kill_sound seed T hcanon hseedfine hclose
    ⟨ρ, U0, a0, Aex0, steps, hpos, hfine0, hchain, henv, hlen.trans hT,
      ⟨c0, hAex0, hopen a0 c0⟩⟩

#print axioms boxAdmit_of_kill
/-! ## 10. The opening table (`mk`, verbatim) -/

/-- The opening-table operations of `m4comp_lib_v1.mk`: the ρ₀-normalized face ratio bounds
(`ρ_y/ρ₀ ≤ (2n_y+1)/2`, `ρ₀/ρ_y ≤ 2/(2n_y−1)`), the strict chain-order bounds
(`ρ₀/ρ_y < 1`, `ρ_y/ρ_{y+1} < 1`). -/
def mkOps (n : Fin 7 → ℤ) : List (Fin 7 × Fin 7 × ℚ × Bool) :=
  (List.finRange 6).flatMap fun y =>
    let r : Fin 7 := Fin.mk (y.val + 1) (by have := y.isLt; omega)
    [(r, 0, ((2 * n r + 1 : ℤ) : ℚ) / 2, false),
     (0, r, 2 / ((2 * n r - 1 : ℤ) : ℚ), false),
     (0, r, 1, true)] ++
  (List.finRange 5).map fun y =>
    let r : Fin 7 := Fin.mk (y.val + 1) (by have := y.isLt; omega)
    let r' : Fin 7 := Fin.mk (y.val + 2) (by have := y.isLt; omega)
    (r, r', 1, true)

/-- Fold a list of `add` operations over an opening table. -/
def uApply (ops : List (Fin 7 × Fin 7 × ℚ × Bool)) (U0 : UTable) : Option UTable :=
  ops.foldl (fun acc op =>
    match acc with
    | none => none
    | some U => uAdd U op.1 op.2.1 op.2.2.1 op.2.2.2) (some U0)

/-- The opening table, verbatim `m4comp_lib_v1.mk` (identity diagonal, then the operations
above; rejects exactly when a two-cycle already fails). -/
def uMk (n : Fin 7 → ℤ) : Option UTable :=
  uApply (mkOps n) (fun i j => if i = j then some (1, false) else none)

end Fresh.UClosure
