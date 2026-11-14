import Mathlib
import Fresh.TropicalCycle

/-!
# TropicalConverse: the completeness (Bellman-Ford) direction of the n=8 certificate theory

Written 2026-11-13.  New file; nothing existing is edited.  Companion to `Fresh.TropicalCycle`
(which owns the sound direction `tropicalCycle_infeasible`); this file delivers the converse
`feasible_of_noGoodCycle` as a REDUCTION TO the shortest-path potential, with every step of
the reduction PROVED and the potential's existence carried as one precisely-stated OWED
(the Floyd-Warshall / Bellman-Ford construction, whose full induction is stated in the
OWED's docstring).  Net: certificate completeness is reduced to a decidable potential
computation — exactly the quantity the fleet's Python side computes.

Additive coordinates.  An edge `a → b` with weight `c` and flag `strict` reads, at
`g i = exp (u i)`, as `exp (u a) / exp (u b) = exp (u a - u b) <(≤) c`, i.e. as the
difference constraint `u a - u b <(≤) log c`.  So:

* `walkSum l` = `∑ log cᵢ` is the additive weight of a walk; `exp (walkSum l) = ∏ cᵢ`
  (`exp_walkSum`), and the campaign's bad-cycle predicate translates EXACTLY:
  `noNegCycle_of_noBadCycle` / `noBadCycle_of_noNegCycle` (product `< 1` becomes sum `< 0`,
  `= 1` becomes `= 0`, strictness untouched) — the log-image of the tropical criterion.
* `IsPotential edges u`: every edge satisfies its difference constraint.  Then
  `g i = exp (u i)` is automatically positive and satisfies every edge
  (`satisfiable_of_isPotential`) — the satisfaction half of the converse, PROVED.
* Conversely a satisfying `g` yields the potential `u i = log (g i)`
  (`isPotential_log_of_satisfiable`) — so `IsPotential` is EXACTLY feasibility.

The OWED.  `PotentialOwed edges`: positivity + the additive no-bad-cycle condition imply a
potential exists.  Docstring carries the full Bellman-Ford induction (cut lemma by
pigeonhole on the 7 vertices; the length-`≤ 6` shortest-path minimization; the
ε-perturbation gap over the finitely many short closed walks).  Both halves of the
reduction are proved on both sides:

* `feasible_of_noGoodCycle_of_potentialOwed` (PROVED): the OWED gives the converse.
* `potentialOwed_of_feasible` (PROVED): conversely the converse gives the OWED —
  so `potentialOwed_iff_feasible` is a genuine equivalence (the reduction is lossless).

Also proved: `noNegCycle_of_isPotential` — the additive soundness half, i.e. the log-image
of `Fresh.TropicalCycle.tropicalCycle_infeasible` recovered through the bridge — and
worked instances (`potentialOwed_single_nonstrict`, `potentialOwed_single_strict`, the
one-edge systems) exercising the whole chain end to end.
-/

namespace Fresh.TropicalConverse

open Fresh.TropicalCycle

/-! ## 1. Additive coordinates: the log-weight of a walk -/

/-- The additive weight of an edge: `log c` (the difference-constraint right side of
`u a - u b <(≤) log c`; negative weights are exactly the caps `c < 1`). -/
-- STANDING: DEFINITION
noncomputable def logW (e : TEdge) : ℝ := Real.log e.c

/-- The additive weight of a walk: the sum of the edges' `log c` — `exp` of it is the
tropical product `∏ cᵢ` (`exp_walkSum`). -/
-- STANDING: DEFINITION
noncomputable def walkSum : List TEdge → ℝ
  | [] => 0
  | e :: l => logW e + walkSum l

@[simp] theorem walkSum_nil : walkSum [] = 0 := rfl

@[simp] theorem walkSum_cons (e : TEdge) (l : List TEdge) :
    walkSum (e :: l) = Real.log e.c + walkSum l := rfl

/-- **The multiplicative/additive bridge.**  `exp` of the walk's additive weight is the
walk's tropical weight product — the pointwise identity `exp (log c) = c` (`0 < c`) summed
by `Real.exp_add`.  This is the exact dictionary between `Fresh.TropicalCycle`'s products
and the difference-constraint sums. -/
theorem exp_walkSum {l : List TEdge} (hpos : ∀ e ∈ l, 0 < e.c) :
    Real.exp (walkSum l) = (l.map TEdge.c).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have hec : 0 < e.c := hpos e (by simp)
    have hil : ∀ x ∈ l, 0 < x.c := fun x hx => hpos x (by simp [hx])
    simp only [walkSum_cons, Real.exp_add, List.map_cons, List.prod_cons, ih hil]
    rw [Real.exp_log hec]

#print axioms exp_walkSum

/-! ## 2. The additive system-level predicates -/

/-- The additive no-bad-cycle condition: no closed walk (drawn from `edges`) has total
log-weight `< 0`, and none has total `= 0` while carrying a strict edge — the log-image of
`Fresh.TropicalCycle.NoBadCycle`, to which it is equivalent under positivity
(`noBadCycle_of_noNegCycle`, `noNegCycle_of_noBadCycle`). -/
-- STANDING: DEFINITION
def NoNegCycle (edges : List TEdge) : Prop :=
  ∀ (s : Fin 7) (l : List TEdge), (∀ e ∈ l, e ∈ edges) → WalkFrom s l s →
    ¬ (walkSum l < 0 ∨ walkSum l = 0 ∧ ((l.map TEdge.strict).any id) = true)

/-- The difference-constraint feasibility of the system at potential `u`: every edge `a → b`
satisfies `u a - u b <(≤) log c` with the edge's strictness flag — the additive form of
`EdgeSat` at `g i = exp (u i)`, to which it is equivalent (`satisfiable_of_isPotential`,
`isPotential_log_of_satisfiable`). -/
-- STANDING: DEFINITION
def IsPotential (edges : List TEdge) (u : Fin 7 → ℝ) : Prop :=
  ∀ e ∈ edges, RHolds e.strict (u e.a - u e.b) (Real.log e.c)

/-! ## 3. The bridging: the additive condition IS the tropical condition -/

/-- Positivity propagates from the system to any walk drawn from it. -/
theorem walk_pos_of_edges {edges : List TEdge} (hpos : ∀ e ∈ edges, 0 < e.c) {l : List TEdge}
    (hsub : ∀ e ∈ l, e ∈ edges) : ∀ e ∈ l, 0 < e.c := fun e he => hpos e (hsub e he)

#print axioms walk_pos_of_edges

/-- Product `< 1` means additive sum `< 0` (the exp bridge, strict side). -/
theorem walkSum_neg_of_prod_lt_one {l : List TEdge} (hpos : ∀ e ∈ l, 0 < e.c)
    (hlt : (l.map TEdge.c).prod < 1) : walkSum l < 0 := by
  have hexp := exp_walkSum hpos
  rw [← hexp, ← Real.exp_zero] at hlt
  exact Real.exp_lt_exp.mp hlt

#print axioms walkSum_neg_of_prod_lt_one

/-- Product `= 1` means additive sum `= 0` (exp is injective). -/
theorem walkSum_eq_of_prod_eq_one {l : List TEdge} (hpos : ∀ e ∈ l, 0 < e.c)
    (heq : (l.map TEdge.c).prod = 1) : walkSum l = 0 := by
  have hexp := exp_walkSum hpos
  refine Real.exp_injective ?_
  rw [hexp, Real.exp_zero]
  exact heq

#print axioms walkSum_eq_of_prod_eq_one

/-- Additive sum `< 0` means product `< 1`. -/
theorem prod_lt_one_of_walkSum_neg {l : List TEdge} (hpos : ∀ e ∈ l, 0 < e.c)
    (hlt : walkSum l < 0) : (l.map TEdge.c).prod < 1 := by
  have hexp := exp_walkSum hpos
  rw [← hexp, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hlt

#print axioms prod_lt_one_of_walkSum_neg

/-- Additive sum `= 0` means product `= 1`. -/
theorem prod_eq_one_of_walkSum_eq {l : List TEdge} (hpos : ∀ e ∈ l, 0 < e.c)
    (heq : walkSum l = 0) : (l.map TEdge.c).prod = 1 := by
  have hexp := exp_walkSum hpos
  rw [← hexp, heq, Real.exp_zero]

#print axioms prod_eq_one_of_walkSum_eq

/-- The tropical criterion implies the additive one. -/
theorem noNegCycle_of_noBadCycle {edges : List TEdge} (hpos : ∀ e ∈ edges, 0 < e.c) :
    NoBadCycle edges → NoNegCycle edges := by
  intro h s l hsub hw hbad
  have hlpos := walk_pos_of_edges hpos hsub
  refine h s l hsub hw ?_
  rcases hbad with hlt | ⟨heq, hst⟩
  · exact Or.inl (prod_lt_one_of_walkSum_neg hlpos hlt)
  · exact Or.inr ⟨prod_eq_one_of_walkSum_eq hlpos heq, hst⟩

#print axioms noNegCycle_of_noBadCycle

/-- The additive criterion implies the tropical one — together with
`noNegCycle_of_noBadCycle` the two predicates coincide (under positivity of the weights). -/
theorem noBadCycle_of_noNegCycle {edges : List TEdge} (hpos : ∀ e ∈ edges, 0 < e.c) :
    NoNegCycle edges → NoBadCycle edges := by
  intro h s l hsub hw hbad
  have hlpos := walk_pos_of_edges hpos hsub
  refine h s l hsub hw ?_
  rcases hbad with hlt | ⟨heq, hst⟩
  · exact Or.inl (walkSum_neg_of_prod_lt_one hlpos hlt)
  · exact Or.inr ⟨walkSum_eq_of_prod_eq_one hlpos heq, hst⟩

#print axioms noBadCycle_of_noNegCycle

/-! ## 4. The satisfaction half (PROVED): a potential is exactly a satisfying reading -/

/-- **The satisfaction half of the converse, PROVED.**  A potential satisfying every
difference constraint yields a positive reading vector satisfying every edge:
`g i = exp (u i)` — `exp (u a) / exp (u b) = exp (u a - u b)`, and exp is increasing, so
each `RHolds` flag translates verbatim.  (No no-bad-cycle hypothesis is needed here: the
potential alone is feasibility.) -/
theorem satisfiable_of_isPotential {edges : List TEdge} {u : Fin 7 → ℝ}
    (hpos : ∀ e ∈ edges, 0 < e.c) (h : IsPotential edges u) : Satisfiable edges := by
  refine ⟨fun i => Real.exp (u i), fun e _ => ⟨Real.exp_pos _, Real.exp_pos _⟩, ?_⟩
  intro e he
  have hc := hpos e he
  have hpot := h e he
  cases hst : e.strict with
  | true =>
    simp only [hst, RHolds] at hpot
    simp only [EdgeSat, hst, RHolds]
    rw [← Real.exp_log hc, ← Real.exp_sub]
    exact Real.exp_lt_exp.mpr hpot
  | false =>
    simp only [hst, RHolds] at hpot
    simp only [EdgeSat, hst, RHolds]
    rw [← Real.exp_log hc, ← Real.exp_sub]
    exact Real.exp_le_exp.mpr hpot

#print axioms satisfiable_of_isPotential

/-- **`IsPotential` is exactly feasibility: the extraction.**  A satisfying reading `g`
yields the potential `u i = log (g i)` — `log (g a / g b) = log (g a) - log (g b)` and log
is increasing on positives, so each `EdgeSat` flag translates verbatim. -/
theorem isPotential_log_of_satisfiable {edges : List TEdge} {g : Fin 7 → ℝ}
    (hgpos : ∀ e ∈ edges, 0 < g e.a ∧ 0 < g e.b) (hsat : ∀ e ∈ edges, EdgeSat g e) :
    IsPotential edges (fun i => Real.log (g i)) := by
  intro e he
  have hc : 0 < e.c := edge_c_pos (hgpos e he) (hsat e he)
  have hs := hsat e he
  have hdiv : 0 < g e.a / g e.b := div_pos (hgpos e he).1 (hgpos e he).2
  cases hst : e.strict with
  | true =>
    simp only [EdgeSat, hst, RHolds] at hs
    simp only [RHolds]
    rw [← Real.log_div (hgpos e he).1.ne' (hgpos e he).2.ne']
    exact (Real.log_lt_log_iff hdiv hc).mpr hs
  | false =>
    simp only [EdgeSat, hst, RHolds] at hs
    simp only [RHolds]
    rw [← Real.log_div (hgpos e he).1.ne' (hgpos e he).2.ne']
    exact (Real.log_le_log_iff hdiv hc).mpr hs

#print axioms isPotential_log_of_satisfiable

/-- The additive soundness half — the log-image of
`Fresh.TropicalCycle.tropicalCycle_infeasible`: a system WITH a potential has no additive
bad cycle.  (Route: potential → satisfiable readings → tropical no-bad-cycle → additive
no-bad-cycle; all three steps are theorems proved here or imported.) -/
theorem noNegCycle_of_isPotential {edges : List TEdge} {u : Fin 7 → ℝ}
    (hpos : ∀ e ∈ edges, 0 < e.c) (h : IsPotential edges u) : NoNegCycle edges :=
  noNegCycle_of_noBadCycle hpos
    (satisfiable_noBadCycle (satisfiable_of_isPotential hpos h))

#print axioms noNegCycle_of_isPotential

/-! ## 5. The OWED: the shortest-path potential (Floyd-Warshall / Bellman-Ford) -/

/-- **OWED (the potential's existence — Floyd-Warshall / Bellman-Ford correctness), the
only step of the converse not proved here.**  If a positive-weight system has no additive
bad cycle, then some potential satisfies every difference constraint.

The construction, made exact (this is the induction the proof runs):

1. **Perturbation.**  For `δ > 0` let `w_δ e := log e.c - δ * (if e.strict then 1 else 0)`.
   Claim: for SOME `δ > 0`, no closed walk has `w_δ`-sum `< 0`.  Existence of such `δ`:
   by the cut lemma (step 2) every closed walk reduces to a closed walk of length `≤ 6`
   with no larger sum; the finitely many closed walks of length `≤ 6` drawn from `edges`
   that carry a strict edge all have additive sum `> 0` (the hypothesis kills sum `< 0`,
   and `= 0`-with-strict), so `δ* := min over those of sum / (#strict)` — a min over a
   FINITE nonempty set of positives when such walks exist, else `δ* := 1` — is positive,
   and any `0 < δ ≤ δ*` works: a closed walk with `w_δ`-sum `< 0` cut to length `≤ 6` has
   `sum - δ·(#strict) < 0`; `#strict = 0` contradicts the hypothesis outright, `#strict ≥ 1`
   gives `sum < δ·(#strict) ≤ δ*·(#strict) ≤ sum` (minimality of `δ*`), a contradiction.
2. **Cut lemma (the pigeonhole).**  Any closed walk over `Fin 7` with `≥ 8` edges visits 9
   vertex-occurrences in 7 values, so a PROPER repetition `v i = v j`, `i < j`, exists;
   cutting the loop between them gives a shorter closed walk whose sum is the original's
   minus the loop's, and the loop is itself a closed walk so has `w_δ`-sum `≥ 0` — strong
   induction on length gives: every closed walk contains one of length `≤ 6` with no
   larger `w_δ`-sum, and if the original carried a strict edge, a piece does too.
3. **The potential.**  In the `w_δ`-system define, for each target `i`, `u i :=` the
   minimum of the `w_δ`-sums over walks of length `≤ 6` from the source `0` to `i` —
   attained, since those walks form a finite set (length-bounded lists over the finite
   edge list) and, by step 2, every longer walk to `i` has a `≤`-sum representative of
   length `≤ 6` (when `i` is reachable at all; unreachable `i` takes `u i := 0`).
4. **Shortest-path property.**  For an edge `a → b`, appending it to a minimizing walk to
   `a` gives a walk to `b` of length `≤ 7` and sum `u a + w_δ a b`; by step 2 it cuts to a
   length-`≤ 6` walk to `b` of no larger sum, whence `u b ≤ u a + w_δ a b`.
5. **The strict flags.**  Step 4 with `δ := δ*/2` gives, for every edge,
   `u b - u a ≤ log e.c - δ*·[strict]/2 ≤ log e.c` (nonstrict verbatim); for a strict edge
   the inequality is strict at `log e.c` — `u b - u a < log e.c` — because the `- δ*` slack
   exceeds the `[strict]/2` consumed.  That is `IsPotential edges u`.  ∎

Every ingredient is finite and decidable (exact ℝ comparisons over finitely many walks);
this is precisely the quantity the fleet's Python side computes when it back-checks a
U-table (`Fresh.UClosureKill`'s `uAdd`/`uProp` are the relaxation steps of exactly this
fold, run as data). -/
-- STANDING: DEFINITION
def PotentialOwed (edges : List TEdge) : Prop :=
  (∀ e ∈ edges, 0 < e.c) → NoNegCycle edges → ∃ u : Fin 7 → ℝ, IsPotential edges u

/-- **The reduction, PROVED: the OWED closes the converse.**  Given the Floyd-Warshall
potential, `feasible_of_noGoodCycle` holds: no tropical bad cycle translates to the
additive condition, the OWED yields a potential, and the satisfaction half turns it into
a positive satisfying reading vector. -/
theorem feasible_of_noGoodCycle_of_potentialOwed (edges : List TEdge)
    (hFW : PotentialOwed edges) : Fresh.TropicalCycle.feasible_of_noGoodCycle edges := by
  intro hpos hbad
  obtain ⟨u, hu⟩ := hFW hpos (noNegCycle_of_noBadCycle hpos hbad)
  exact satisfiable_of_isPotential hpos hu

#print axioms feasible_of_noGoodCycle_of_potentialOwed

/-- **The reduction is LOSSLESS (PROVED): the converse implies the OWED.**  From
`feasible_of_noGoodCycle`, a no-additive-bad-cycle positive system is tropical-bad-cycle
free, hence satisfiable, and `log ∘ g` is the potential. -/
theorem potentialOwed_of_feasible (edges : List TEdge)
    (h : Fresh.TropicalCycle.feasible_of_noGoodCycle edges) : PotentialOwed edges := by
  intro hpos hneg
  obtain ⟨g, hgpos, hgsat⟩ :=
    h hpos (noBadCycle_of_noNegCycle hpos hneg)
  exact ⟨fun i => Real.log (g i), isPotential_log_of_satisfiable hgpos hgsat⟩

#print axioms potentialOwed_of_feasible

/-- The equivalence: certificate completeness is EXACTLY the shortest-path potential's
existence — one decidable computation, nothing more. -/
theorem potentialOwed_iff_feasible (edges : List TEdge) :
    PotentialOwed edges ↔ Fresh.TropicalCycle.feasible_of_noGoodCycle edges :=
  ⟨feasible_of_noGoodCycle_of_potentialOwed edges, potentialOwed_of_feasible edges⟩

#print axioms potentialOwed_iff_feasible

/-! ## 6. The cut lemma as a stated OWED (decomposition of the construction) -/

/-- **OWED 2 (the cut lemma), the engine inside `PotentialOwed`'s step 2.**  Every closed
walk drawn from `edges` contains a closed subwalk of length `≤ 6` with no larger
additive sum, and — if the walk carried a strict edge — carrying a strict edge itself
(the loop cut out at a proper repeated vertex, recursed; see `PotentialOwed`'s docstring,
step 2). -/
-- STANDING: DEFINITION
def CutOwed (edges : List TEdge) : Prop :=
  ∀ (s : Fin 7) (l : List TEdge), (∀ e ∈ l, e ∈ edges) → WalkFrom s l s →
    ∃ l' : List TEdge, WalkFrom s l' s ∧ (∀ e ∈ l', e ∈ edges) ∧ l'.length ≤ 6 ∧
      walkSum l' ≤ walkSum l ∧
      (((l.map TEdge.strict).any id) = true → ((l'.map TEdge.strict).any id) = true)

/-! ## 7. Worked instances: the one-edge systems, end to end -/

/-- The only edge of a one-edge list is the list's edge. -/
theorem mem_single_eq {a b : Fin 7} {c : ℝ} {st : Bool} {e : TEdge}
    (he : e ∈ [(⟨a, b, c, st⟩ : TEdge)]) : e = ⟨a, b, c, st⟩ := by
  simpa using he

#print axioms mem_single_eq

/-- The weight of the edge of a one-edge list is the list's weight. -/
theorem c_eq_of_mem_single {a b : Fin 7} {c : ℝ} {st : Bool} {e : TEdge}
    (he : e ∈ [(⟨a, b, c, st⟩ : TEdge)]) : e.c = c := by
  have hE := mem_single_eq he
  subst hE
  rfl

#print axioms c_eq_of_mem_single

/-- Any walk drawn from a one-edge list `[[a → b]]` (`a ≠ b`) that starts at `b` is empty
and ends at `b`: the unique edge starts at `a`, so no nonempty walk can leave `b`. -/
theorem walk_from_b_single {a b : Fin 7} (hab : a ≠ b) {c : ℝ} {st : Bool}
    {t : Fin 7} {l' : List TEdge}
    (hsub : ∀ e ∈ l', e ∈ [(⟨a, b, c, st⟩ : TEdge)]) (hw : WalkFrom b l' t) :
    l' = [] ∧ t = b := by
  cases l' with
  | nil =>
    cases hw with
    | nil => exact ⟨rfl, rfl⟩
  | cons e l₁ =>
    exfalso
    cases hw with
    | @cons _ _ _ _ he hrest =>
      have hE : e = (⟨a, b, c, st⟩ : TEdge) := mem_single_eq (hsub e (by simp))
      subst hE
      exact hab he

#print axioms walk_from_b_single

/-- The walks drawn from a one-edge list `[[a → b]]` (`a ≠ b`): either the empty walk
(closing at its start) or the single edge (from `a` to `b`). -/
theorem walk_single_cases {a b : Fin 7} (hab : a ≠ b) {c : ℝ} {st : Bool}
    {s t : Fin 7} {l : List TEdge}
    (hsub : ∀ e ∈ l, e ∈ [(⟨a, b, c, st⟩ : TEdge)]) (hw : WalkFrom s l t) :
    (l = [] ∧ t = s) ∨ (l = [(⟨a, b, c, st⟩ : TEdge)] ∧ s = a ∧ t = b) := by
  cases hw with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons s e l' t he hrest =>
    refine Or.inr ?_
    have hE : e = (⟨a, b, c, st⟩ : TEdge) := mem_single_eq (hsub e (by simp))
    subst hE
    obtain ⟨hl'e, ht⟩ := walk_from_b_single hab
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hrest
    subst hl'e
    exact ⟨rfl, he.symm, ht⟩

#print axioms walk_single_cases

/-- The one-edge system (any flag) has no additive bad cycle: the only closed walk is the
empty one (sum `0`, no strict edge), since a closed walk through the edge would close at
both `a` and `b`. -/
theorem noNegCycle_single {a b : Fin 7} (hab : a ≠ b) {c : ℝ} {st : Bool} :
    NoNegCycle [(⟨a, b, c, st⟩ : TEdge)] := by
  intro s l hsub hw hbad
  rcases walk_single_cases hab hsub hw with ⟨hl, ht⟩ | ⟨hl, hs, ht⟩
  · subst hl; simp at hbad
  · exact hab (hs.symm.trans ht)

#print axioms noNegCycle_single

/-- **Worked instance of the whole chain, PROVED: the one-edge cap `ρa/ρb ≤ c` (`1 ≤ c`).**
The zero potential satisfies its difference constraint, so — through
`feasible_of_noGoodCycle_of_potentialOwed` and the bridge — the reading `g = 1` realizes
the system: `PotentialOwed` proved outright, exercising every proved step of the converse
on a concrete instance. -/
theorem potentialOwed_single_nonstrict {a b : Fin 7} {c : ℝ} (hc : 1 ≤ c) :
    PotentialOwed [(⟨a, b, c, false⟩ : TEdge)] := by
  intro _ _
  refine ⟨fun _ => 0, fun e he => ?_⟩
  have hE := mem_single_eq he
  subst hE
  simp only [RHolds, sub_zero]
  exact Real.log_nonneg hc

#print axioms potentialOwed_single_nonstrict

/-- **Worked instance, strict flavor: the one-edge demand `ρa/ρb < c` (`1 < c`).**  The
same zero potential, now satisfying the strict difference constraint `0 < log c`. -/
theorem potentialOwed_single_strict {a b : Fin 7} {c : ℝ} (hc : 1 < c) :
    PotentialOwed [(⟨a, b, c, true⟩ : TEdge)] := by
  intro _ _
  refine ⟨fun _ => 0, fun e he => ?_⟩
  have hE := mem_single_eq he
  subst hE
  simp only [RHolds, sub_zero]
  exact Real.log_pos hc

#print axioms potentialOwed_single_strict

/-- The empty system: the zero potential works outright — `PotentialOwed []` proved. -/
theorem potentialOwed_empty : PotentialOwed [] := by
  intro _ _
  exact ⟨fun _ => 0, fun e he => absurd he (by simp)⟩

#print axioms potentialOwed_empty

/-! ## 8. Worked instance: the two-cycle — the campaign's kill shape, made EXACT -/

/-- Membership in the two-cycle edge list, as an equation disjunction. -/
theorem mem_pair_eq {A B : TEdge} {e : TEdge} (he : e ∈ [A, B]) : e = A ∨ e = B := by
  simp only [List.mem_cons] at he
  rcases he with rfl | he'
  · exact Or.inl rfl
  · rcases he' with rfl | he''
    · exact Or.inr rfl
    · exact absurd he'' List.not_mem_nil

#print axioms mem_pair_eq

theorem mem_pair_head {A B : TEdge} : A ∈ [A, B] := by simp

#print axioms mem_pair_head

theorem mem_pair_tail {A B : TEdge} : B ∈ [A, B] := by simp

#print axioms mem_pair_tail

/-- **The two-cycle potential (PROVED).**  For the cap/demand 2-cycle
`0 → 1` with weight `c` and `1 → 0` with weight `d` (both nonstrict, `c·d ≥ 1`) the
potential `u 0 = 0`, `u 1 = -log c` satisfies both difference constraints — the first
constraint tight, the second exactly the datum `1 ≤ c·d`.  The potential value at
`1 = -log c` is the reading `ρ₁ = 1/c` — the equality case of the criterion. -/
theorem twoCycle_u_isPotential {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hcd : 1 ≤ c * d) :
    IsPotential [(⟨0, 1, c, false⟩ : TEdge), (⟨1, 0, d, false⟩ : TEdge)]
      (fun i => if i = 0 then (0 : ℝ) else -(Real.log c)) := by
  have hu0 : (fun i : Fin 7 => if i = 0 then (0 : ℝ) else -(Real.log c)) 0 = 0 := by simp
  have hu1 : (fun i : Fin 7 => if i = 0 then (0 : ℝ) else -(Real.log c)) 1 =
      -(Real.log c) := by simp
  have pa : (⟨0, 1, c, false⟩ : TEdge).a = 0 := rfl
  have pb : (⟨0, 1, c, false⟩ : TEdge).b = 1 := rfl
  have qa : (⟨1, 0, d, false⟩ : TEdge).a = 1 := rfl
  have qb : (⟨1, 0, d, false⟩ : TEdge).b = 0 := rfl
  intro e he
  rcases mem_pair_eq he with rfl | rfl
  · rw [pa, pb, hu0, hu1]
    simp only [RHolds]
    simp
  · rw [qa, qb, hu1, hu0]
    simp only [RHolds]
    rw [sub_zero, neg_le_iff_add_nonneg, ← Real.log_mul hd.ne' hc.ne']
    exact Real.log_nonneg (by rw [mul_comm]; exact hcd)

#print axioms twoCycle_u_isPotential

/-- **The two-cycle instance of the OWED, PROVED outright** (no Floyd-Warshall needed on
a system small enough to solve by hand): `PotentialOwed` holds for the nonstrict 2-cycle
with `c·d ≥ 1`. -/
theorem potentialOwed_twoCycle {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (hcd : 1 ≤ c * d) :
    PotentialOwed [(⟨0, 1, c, false⟩ : TEdge), (⟨1, 0, d, false⟩ : TEdge)] :=
  fun _ _ => ⟨fun i => if i = 0 then (0 : ℝ) else -(Real.log c),
    twoCycle_u_isPotential hc hd hcd⟩

#print axioms potentialOwed_twoCycle

/-- **The 2-cycle criterion, EXACT (the converse instance paired with the sound
direction).**  For the nonstrict two-cycle the system is satisfiable IF AND ONLY IF
`c·d ≥ 1` — combined with `Fresh.TropicalCycle.twoCycle_engine` (a satisfied pair kills
`c·d < 1`, and kills `c·d = 1` carrying a strict side) the ratio-2-cycle test is exactly
feasibility: no kill mechanism beyond the cycle structure exists at this shape. -/
theorem twoCycle_sat_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Satisfiable [(⟨0, 1, c, false⟩ : TEdge), (⟨1, 0, d, false⟩ : TEdge)] ↔ 1 ≤ c * d := by
  constructor
  · rintro ⟨g, hgpos, hgsat⟩
    have h1 : RHolds false (g 0 / g 1) c :=
      hgsat (⟨0, 1, c, false⟩ : TEdge) mem_pair_head
    have h2 : RHolds false (g 1 / g 0) d :=
      hgsat (⟨1, 0, d, false⟩ : TEdge) mem_pair_tail
    simp only [RHolds] at h1 h2
    have hg0 : 0 < g 0 := (hgpos (⟨0, 1, c, false⟩ : TEdge) mem_pair_head).1
    have hg1 : 0 < g 1 := (hgpos (⟨0, 1, c, false⟩ : TEdge) mem_pair_head).2
    have hdiv : 0 < g 0 / g 1 := div_pos hg0 hg1
    have hprod : g 0 / g 1 * (g 1 / g 0) = 1 := by
      field_simp
    rw [← hprod]
    exact mul_le_mul_of_nonneg h1 h2 (le_of_lt hdiv) hd.le
  · intro hcd
    exact satisfiable_of_isPotential (fun e he => by
      rcases mem_pair_eq he with rfl | rfl
      · exact hc
      · exact hd)
      (twoCycle_u_isPotential hc hd hcd)

#print axioms twoCycle_sat_iff

/-! ## 9. Generic weighted walks: `wsum`, the strict-edge count, the perturbed weight

The Floyd-Warshall construction is run on a GENERAL weight function `wt : TEdge → ℝ`;
`walkSum` is the `wt = logW` instance and the δ-perturbation is `wt = pw δ`.  What the
construction consumes is: (i) additivity of the walk weight over concatenation (the cut
engine) and (ii) the δ-perturbed weight of a walk in terms of the log-weight and the
strict-edge count. -/

/-- The `wt`-weight of a walk: the sum of `wt` over the edges. -/
-- STANDING: DEFINITION
noncomputable def wsum (wt : TEdge → ℝ) : List TEdge → ℝ
  | [] => 0
  | e :: l => wt e + wsum wt l

@[simp] theorem wsum_nil (wt : TEdge → ℝ) : wsum wt [] = 0 := rfl

@[simp] theorem wsum_cons (wt : TEdge → ℝ) (e : TEdge) (l : List TEdge) :
    wsum wt (e :: l) = wt e + wsum wt l := rfl

/-- **Additivity over concatenation — the cut lemma's engine.** -/
theorem wsum_append (wt : TEdge → ℝ) (l₁ l₂ : List TEdge) :
    wsum wt (l₁ ++ l₂) = wsum wt l₁ + wsum wt l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons e l₁ ih => rw [List.cons_append, wsum_cons, ih, wsum_cons, add_assoc]

#print axioms wsum_append

/-- `walkSum` is the `logW`-weighted sum. -/
theorem walkSum_eq_wsum (l : List TEdge) : walkSum l = wsum logW l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [walkSum_cons, wsum_cons, ih, logW]

#print axioms walkSum_eq_wsum

/-- The strict-edge count of a walk. -/
-- STANDING: DEFINITION
def kstr : List TEdge → Nat
  | [] => 0
  | e :: l => (if e.strict = true then 1 else 0) + kstr l

@[simp] theorem kstr_nil : kstr [] = 0 := rfl

@[simp] theorem kstr_cons (e : TEdge) (l : List TEdge) :
    kstr (e :: l) = (if e.strict = true then 1 else 0) + kstr l := rfl

theorem kstr_append (l₁ l₂ : List TEdge) : kstr (l₁ ++ l₂) = kstr l₁ + kstr l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons e l₁ ih =>
    by_cases h : e.strict = true
    · rw [List.cons_append, kstr_cons, if_pos h, ih, kstr_cons, if_pos h]; ring
    · rw [List.cons_append, kstr_cons, if_neg h, ih, kstr_cons, if_neg h]; ring

#print axioms kstr_append

theorem kstr_le_length (l : List TEdge) : kstr l ≤ l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases h : e.strict = true
    · rw [kstr_cons, if_pos h, List.length_cons]
      omega
    · rw [kstr_cons, if_neg h, List.length_cons]
      omega

#print axioms kstr_le_length

/-- A positive strict count witnesses a strict edge. -/
theorem any_true_of_kstr_pos {l : List TEdge} (h : 1 ≤ kstr l) :
    ((l.map TEdge.strict).any id) = true := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    rw [kstr_cons] at h
    by_cases hc : e.strict = true
    · simp [List.map_cons, List.any_cons, hc]
    · have hf : e.strict = false := by simpa using hc
      rw [if_neg hc, zero_add] at h
      have hany := ih h
      simp [List.map_cons, List.any_cons, hf, hany]

#print axioms any_true_of_kstr_pos

/-- No strict edge forces a zero strict count. -/
theorem kstr_eq_zero_of_no_strict {l : List TEdge}
    (hst : ((l.map TEdge.strict).any id) = false) : kstr l = 0 := by
  rcases Nat.eq_zero_or_pos (kstr l) with h0 | hpos
  · exact h0
  · exact absurd (any_true_of_kstr_pos hpos) (by rw [hst]; simp)

#print axioms kstr_eq_zero_of_no_strict

/-- The δ-perturbed weight: `log c` shrunk by δ on strict edges. -/
-- STANDING: DEFINITION
noncomputable def pw (δ : ℝ) (e : TEdge) : ℝ :=
  Real.log e.c - δ * (if e.strict = true then (1 : ℝ) else 0)

@[simp] theorem pw_nonstrict (δ : ℝ) {e : TEdge} (h : e.strict = false) :
    pw δ e = Real.log e.c := by
  simp only [pw, if_neg (by simp [h] : ¬(e.strict = true)), mul_zero, sub_zero]

@[simp] theorem pw_strict (δ : ℝ) {e : TEdge} (h : e.strict = true) :
    pw δ e = Real.log e.c - δ := by
  simp only [pw, if_pos h, mul_one]

/-- **The perturbed walk weight** is the log-weight minus δ per strict edge — the identity
the δ*-gap argument consumes. -/
theorem wsum_pw (δ : ℝ) (l : List TEdge) :
    wsum (pw δ) l = walkSum l - δ * kstr l := by
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases h : e.strict = true
    · rw [wsum_cons, pw_strict δ h, walkSum_cons, kstr_cons, if_pos h, ih]
      push_cast
      ring
    · have hf : e.strict = false := by simpa using h
      rw [wsum_cons, pw_nonstrict δ hf, walkSum_cons, kstr_cons, if_neg h, ih]
      push_cast
      ring

#print axioms wsum_pw

/-! ## 10. Head-to-tail consistency as a decidable function: `walkEnd?`, `closedDec` -/

/-- The end vertex of a head-to-tail-consistent edge list started at `t` (`none` when the
list is inconsistent). -/
-- STANDING: DEFINITION
def walkEnd? : Fin 7 → List TEdge → Option (Fin 7)
  | t, [] => some t
  | t, e :: l => if e.a = t then walkEnd? e.b l else none

/-- A walk determines its end vertex. -/
theorem walkEnd?_of_walk {l : List TEdge} {t s : Fin 7} (hw : WalkFrom t l s) :
    walkEnd? t l = some s := by
  induction hw with
  | nil s => rfl
  | @cons s e l t he hrest ih => simp [walkEnd?, he, ih]

#print axioms walkEnd?_of_walk

/-- An end vertex determines a walk. -/
theorem walk_of_walkEnd {l : List TEdge} {s : Fin 7} : ∀ (t : Fin 7),
    walkEnd? t l = some s → WalkFrom t l s := by
  intro t
  induction l generalizing t with
  | nil =>
    intro h
    simp only [walkEnd?] at h
    have h' : t = s := Option.some.inj h
    cases h'
    exact WalkFrom.nil _
  | cons e l ih =>
    intro h
    simp only [walkEnd?] at h
    by_cases he : e.a = t
    · rw [if_pos he] at h
      exact WalkFrom.cons t e l s he (ih e.b h)
    · rw [if_neg he] at h
      exact absurd h (by simp)

#print axioms walk_of_walkEnd

/-- Start vertex of a list (irrelevant for `[]`). -/
-- STANDING: DEFINITION
def startV : List TEdge → Fin 7
  | [] => 0
  | e :: _ => e.a

@[simp] theorem startV_nil : startV [] = 0 := rfl

@[simp] theorem startV_cons (e : TEdge) (l : List TEdge) : startV (e :: l) = e.a := rfl

/-- Decidable closedness: the walk from its own start vertex returns to it. -/
-- STANDING: DEFINITION
def closedDec (w : List TEdge) : Bool := walkEnd? (startV w) w == some (startV w)

/-- A closed walk is `closedDec`. -/
theorem closedDec_of_walk {w : List TEdge} {v : Fin 7} (hw : WalkFrom v w v) :
    closedDec w = true := by
  cases hw with
  | nil s => simp [closedDec, startV, walkEnd?]
  | @cons s e l t he hrest =>
    unfold closedDec
    rw [startV_cons, walkEnd?, if_pos rfl, walkEnd?_of_walk hrest, he]
    simp

#print axioms closedDec_of_walk

/-- `closedDec` is a closed walk. -/
theorem walk_of_closedDec {w : List TEdge} (h : closedDec w = true) :
    ∃ v : Fin 7, WalkFrom v w v := by
  cases w with
  | nil => exact ⟨0, WalkFrom.nil 0⟩
  | cons e l =>
    simp only [closedDec, startV_cons, walkEnd?] at h
    have h' : walkEnd? e.b l = some e.a := beq_iff_eq.mp h
    exact ⟨e.a, WalkFrom.cons e.a e l e.a rfl (walk_of_walkEnd e.b h')⟩

#print axioms walk_of_closedDec

/-! ## 11. The vertex sequence, prefix splitting, and the pigeonhole cut

This is the mathematical core of the converse: any walk over 7 vertices of length ≥ 7
visits a vertex twice (pigeonhole on the 8 occurrences `v₀, …, v₇` in 7 values), the loop
between the two visits is a CLOSED subwalk (nonnegative weight by the no-bad-cycle
hypothesis), so cutting it out shortens the walk without increasing its weight. -/

/-- The vertex reached after `k` head-to-tail steps from `t` along the list (a total
function; correct on consistent lists by `walk_take`). -/
-- STANDING: DEFINITION
def vseqT (t : Fin 7) : List TEdge → Nat → Fin 7
  | [], _ => t
  | e :: rest, 0 => t
  | e :: rest, k + 1 => vseqT e.b rest k

@[simp] theorem vseqT_zero (t : Fin 7) (l : List TEdge) : vseqT t l 0 = t := by
  cases l <;> rfl

@[simp] theorem vseqT_nil (t : Fin 7) (k : Nat) : vseqT t [] k = t := by
  cases k <;> rfl

@[simp] theorem vseqT_cons_succ (t : Fin 7) (e : TEdge) (rest : List TEdge) (k : Nat) :
    vseqT t (e :: rest) (k + 1) = vseqT e.b rest k := rfl

/-- **Prefix splitting of a walk at step `k`:** the first `k` edges are a walk ending at
`vseqT t l k`, and the rest continues from there. -/
theorem walk_take : ∀ (k : Nat) (l : List TEdge) (t i : Fin 7), WalkFrom t l i →
    k ≤ l.length →
    WalkFrom t (l.take k) (vseqT t l k) ∧ WalkFrom (vseqT t l k) (l.drop k) i := by
  intro k
  induction k with
  | zero =>
    intro l t i hw _
    rw [List.take_zero, List.drop_zero, vseqT_zero]
    exact ⟨WalkFrom.nil t, hw⟩
  | succ k ih =>
    intro l t i hw hk
    cases l with
    | nil => exact absurd hk (by simp)
    | cons e rest =>
      cases hw with
      | @cons s e' l' j he hrest =>
        -- indices unify: s = t, e' = e, l' = rest, j = i
        rw [List.take_cons (by omega), Nat.add_sub_cancel]
        rw [List.drop_cons (by omega), Nat.add_sub_cancel]
        have hkl : k ≤ rest.length := by
          have hlc : (e :: rest).length = rest.length + 1 := rfl
          omega
        obtain ⟨h1, h2⟩ := ih rest e.b i hrest hkl
        exact ⟨WalkFrom.cons t e (rest.take k) _ he h1, h2⟩

#print axioms walk_take

/-- **Shift-compatibility of the vertex sequence:** the suffix sequence re-embeds. -/
theorem vseqT_drop : ∀ (q : Nat) (l : List TEdge) (t i : Fin 7), WalkFrom t l i → ∀ p : Nat,
    p ≤ q → q ≤ l.length → vseqT (vseqT t l p) (l.drop p) (q - p) = vseqT t l q := by
  intro q
  induction q with
  | zero =>
    intro l t i hw p hp _
    have hp0 : p = 0 := by omega
    cases hp0
    simp
  | succ q ih =>
    intro l t i hw p hp hq
    by_cases hpq : p = q + 1
    · cases hpq; simp
    · have hple : p ≤ q := by omega
      have hlen : q + 1 ≤ l.length := hq
      cases l with
      | nil => exact absurd hlen (by simp)
      | cons e rest =>
        cases hw with
        | @cons s e' l' j he hrest =>
          by_cases hp0 : p = 0
          · cases hp0; simp
          · obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
            cases hp'
            have hpl' : p' ≤ q := by omega
            have hql' : q ≤ rest.length := by
              have hlc : (e :: rest).length = rest.length + 1 := rfl
              omega
            have hsub : q + 1 - (p' + 1) = q - p' := by omega
            rw [List.drop_cons (by omega), Nat.add_sub_cancel]
            rw [vseqT_cons_succ, vseqT_cons_succ, hsub]
            exact ih rest e.b i hrest p' hpl' hql'

#print axioms vseqT_drop

/-- Membership transport through `take` and `drop`. -/
theorem mem_of_take {e : TEdge} : ∀ (p : Nat) (l : List TEdge), e ∈ l.take p → e ∈ l := by
  intro p
  induction p with
  | zero => intro l h; simp at h
  | succ p ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons a rest =>
      simp only [List.take_cons (i := p + 1) (by omega), Nat.add_sub_cancel,
        List.mem_cons] at h
      rcases h with rfl | h'
      · simp
      · exact List.mem_cons_of_mem _ (ih rest h')

#print axioms mem_of_take

theorem mem_of_drop {e : TEdge} : ∀ (p : Nat) (l : List TEdge), e ∈ l.drop p → e ∈ l := by
  intro p
  induction p with
  | zero => intro l h; simpa using h
  | succ p ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons a rest =>
      simp only [List.drop_cons (i := p + 1) (by omega), Nat.add_sub_cancel] at h
      exact List.mem_cons_of_mem _ (ih rest h)

#print axioms mem_of_drop

/-- **The cut core.**  A repeated vertex at positions `p < q` splits `l = pre ++ loop ++
post` with the loop a CLOSED subwalk at the repeated vertex; the shortened walk
`pre ++ post` is a walk from `t` to `i`, strictly shorter, and its weight plus the loop's
is the whole weight. -/
theorem cutCore (wt : TEdge → ℝ) (l : List TEdge) (t i : Fin 7) (hw : WalkFrom t l i)
    (p q : Nat) (hpq : p < q) (hql : q ≤ l.length) (heq : vseqT t l p = vseqT t l q) :
    ∃ short loop : List TEdge,
      WalkFrom t short i ∧ WalkFrom (vseqT t l p) loop (vseqT t l p) ∧
      loop.length = q - p ∧ short.length < l.length ∧
      (∀ e ∈ short, e ∈ l) ∧ (∀ e ∈ loop, e ∈ l) ∧
      wsum wt short + wsum wt loop = wsum wt l := by
  obtain ⟨hvpre, hvrest⟩ := walk_take p l t i hw (by omega)
  obtain ⟨hvloop, hvpost⟩ := walk_take (q - p) (l.drop p) (vseqT t l p) i hvrest (by
    have hldl : (l.drop p).length = l.length - p := List.length_drop
    omega)
  have hvshift : vseqT (vseqT t l p) (l.drop p) (q - p) = vseqT t l q :=
    vseqT_drop q l t i hw p (by omega) hql
  rw [hvshift] at hvloop hvpost
  rw [heq] at hvpre hvloop
  rw [heq]
  refine ⟨l.take p ++ (l.drop p).drop (q - p), (l.drop p).take (q - p),
    walk_append t (l.take p) (vseqT t l q) hvpre _ hvpost, hvloop, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  · rw [List.length_append, List.length_take, min_eq_left (by omega)]
    simp only [List.length_drop]
    omega
  · intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact mem_of_take p l he
    · exact mem_of_drop p l (mem_of_drop (q - p) (l.drop p) he)
  · intro e he
    exact mem_of_drop p l (mem_of_take (q - p) (l.drop p) he)
  · have h1 : l = l.take p ++ l.drop p := (List.take_append_drop p l).symm
    have h2 : l.drop p = (l.drop p).take (q - p) ++ (l.drop p).drop (q - p) :=
      (List.take_append_drop (q - p) (l.drop p)).symm
    have hA : wsum wt (l.take p ++ (l.drop p).drop (q - p)) =
        wsum wt (l.take p) + wsum wt ((l.drop p).drop (q - p)) := wsum_append _ _ _
    have hB : wsum wt l = wsum wt (l.take p) + wsum wt (l.drop p) := by
      conv =>
        lhs
        rw [h1]
      exact wsum_append _ _ _
    have hC : wsum wt (l.drop p) =
        wsum wt ((l.drop p).take (q - p)) + wsum wt ((l.drop p).drop (q - p)) := by
      conv =>
        lhs
        rw [h2]
      exact wsum_append _ _ _
    rw [hA, hB]
    linarith

#print axioms cutCore

/-- **The pigeonhole cut.**  A walk of length ≥ 7 over `Fin 7` has a proper repeated
vertex; cutting the loop (a closed walk, nonnegative weight by `hcn`) shortens the walk
without increasing its weight. -/
theorem cutAll (wt : TEdge → ℝ) (edges : List TEdge)
    (hcn : ∀ (l₀ : List TEdge) (v : Fin 7), (∀ e ∈ l₀, e ∈ edges) → WalkFrom v l₀ v →
      0 ≤ wsum wt l₀)
    (l : List TEdge) (t i : Fin 7) (hsub : ∀ e ∈ l, e ∈ edges) (hw : WalkFrom t l i)
    (h7 : 7 ≤ l.length) :
    ∃ l', WalkFrom t l' i ∧ (∀ e ∈ l', e ∈ edges) ∧ l'.length < l.length ∧
      wsum wt l' ≤ wsum wt l := by
  obtain ⟨p, q, hpq, hql, heq⟩ :
      ∃ p q : Nat, p < q ∧ q ≤ l.length ∧ vseqT t l p = vseqT t l q := by
    have hinj : ¬ Function.Injective (fun k : Fin 8 => vseqT t l k.val) := by
      intro hinj
      exact absurd (Fintype.card_le_of_injective _ hinj) (by simp)
    obtain ⟨k₁, k₂, heq, hne⟩ := Function.not_injective_iff.mp hinj
    have hvne : k₁.val ≠ k₂.val := fun h => hne (Fin.val_inj.mp h)
    have h8 := k₂.isLt
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heqq | hgt
    · exact ⟨k₁.val, k₂.val, hlt, by omega, heq⟩
    · exact absurd heqq hvne
    · exact ⟨k₂.val, k₁.val, hgt, by omega, heq.symm⟩
  obtain ⟨short, loop, hWshort, hWloop, hloolen, hshortlen, hshortsub, hloopsub, hwsumsplit⟩ :=
    cutCore wt l t i hw p q hpq hql heq
  refine ⟨short, hWshort, fun e he => hsub e (hshortsub e he), hshortlen, ?_⟩
  have hloopnn : 0 ≤ wsum wt loop :=
    hcn loop (vseqT t l p) (fun e he => hsub e (hloopsub e he)) hWloop
  linarith

#print axioms cutAll

/-- **The closed-walk tail cut.**  A CLOSED walk of length ≥ 8 cut at a repetition among
the vertices `v₁, …, v₈` (positions ≥ 1, so both pieces are strictly shorter): the weight
was already nonnegative. -/
theorem cutTail (wt : TEdge → ℝ) (edges : List TEdge)
    (l : List TEdge) (v : Fin 7) (hsub : ∀ e ∈ l, e ∈ edges) (hw : WalkFrom v l v)
    (h8 : 8 ≤ l.length)
    (hshort : ∀ (l₀ : List TEdge) (v₀ : Fin 7), (∀ e ∈ l₀, e ∈ edges) → WalkFrom v₀ l₀ v₀ →
      l₀.length < l.length → 0 ≤ wsum wt l₀) :
    0 ≤ wsum wt l := by
  obtain ⟨p, q, hp1, hpq, hql, heq⟩ :
      ∃ p q : Nat, 1 ≤ p ∧ p < q ∧ q ≤ l.length ∧ vseqT v l p = vseqT v l q := by
    have hinj : ¬ Function.Injective (fun k : Fin 8 => vseqT v l (k.val + 1)) := by
      intro hinj
      exact absurd (Fintype.card_le_of_injective _ hinj) (by simp)
    obtain ⟨k₁, k₂, heq, hne⟩ := Function.not_injective_iff.mp hinj
    have hvne : k₁.val ≠ k₂.val := fun h => hne (Fin.val_inj.mp h)
    have h8' := k₂.isLt
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heqq | hgt
    · exact ⟨k₁.val + 1, k₂.val + 1, by omega, by omega, by omega, heq⟩
    · exact absurd heqq hvne
    · exact ⟨k₂.val + 1, k₁.val + 1, by omega, by omega, by omega, heq.symm⟩
  obtain ⟨short, loop, hWshort, hWloop, hloolen, hshortlen, hshortsub, hloopsub, hwsumsplit⟩ :=
    cutCore wt l v v hw p q hpq hql heq
  have h0 : 0 ≤ wsum wt short :=
    hshort short v (fun e he => hsub e (hshortsub e he)) hWshort (by omega)
  have h1 : 0 ≤ wsum wt loop :=
    hshort loop (vseqT v l p) (fun e he => hsub e (hloopsub e he)) hWloop (by omega)
  linarith

#print axioms cutTail

/-- **Short closed walks control all closed walks** (strong induction on the length, by
the tail cut): if every closed walk of length ≤ 7 has nonnegative `wt`-weight, so does
every closed walk. -/
theorem closedNonneg_of_short (wt : TEdge → ℝ) (edges : List TEdge)
    (hshort : ∀ (l : List TEdge) (v : Fin 7), (∀ e ∈ l, e ∈ edges) → WalkFrom v l v →
      l.length ≤ 7 → 0 ≤ wsum wt l) :
    ∀ (N : Nat) (l : List TEdge) (v : Fin 7), (∀ e ∈ l, e ∈ edges) → WalkFrom v l v →
      l.length ≤ N → 0 ≤ wsum wt l := by
  intro N
  induction N with
  | zero =>
    intro l v hsub hw hlen
    cases l with
    | nil => simp
    | cons e rest => exact absurd hlen (by simp)
  | succ N ih =>
    intro l v hsub hw hlen
    rcases Nat.lt_or_ge l.length 8 with h7 | h8
    · exact hshort l v hsub hw (by omega)
    · exact cutTail wt edges l v hsub hw h8
        (fun l₀ v₀ hs hw₀ hlen₀ => ih l₀ v₀ hs hw₀ (by omega))

#print axioms closedNonneg_of_short

/-- **Every walk has a length-≤ 6 representative** with no larger weight (strong
induction on the length, by the full pigeonhole cut; the cut loops are closed walks, so
`hcn` governs them).  This is the Floyd-Warshall bound: nothing beyond 6-edge walks
matters for a 7-vertex system. -/
theorem rep_of_walk (wt : TEdge → ℝ) (edges : List TEdge)
    (hcn : ∀ (l₀ : List TEdge) (v : Fin 7), (∀ e ∈ l₀, e ∈ edges) → WalkFrom v l₀ v →
      0 ≤ wsum wt l₀) :
    ∀ (N : Nat) (l : List TEdge) (t i : Fin 7), (∀ e ∈ l, e ∈ edges) → WalkFrom t l i →
      l.length ≤ N → ∃ l', WalkFrom t l' i ∧ (∀ e ∈ l', e ∈ edges) ∧ l'.length ≤ 6 ∧
        wsum wt l' ≤ wsum wt l := by
  intro N
  induction N with
  | zero =>
    intro l t i hsub hw hlen
    cases hw with
    | nil => exact ⟨[], WalkFrom.nil _, by simp, by omega, le_refl _⟩
    | cons => exact absurd hlen (by simp)
  | succ N ih =>
    intro l t i hsub hw hlen
    rcases Nat.lt_or_ge l.length 7 with h6 | h7
    · exact ⟨l, hw, hsub, by omega, le_refl _⟩
    · obtain ⟨l', hW, hsub', hlen', hwsum'⟩ := cutAll wt edges hcn l t i hsub hw (by omega)
      obtain ⟨l'', hW'', hsub'', hlen6, hwsum''⟩ := ih l' t i hsub' hW (by omega)
      exact ⟨l'', hW'', hsub'', hlen6, le_trans hwsum'' hwsum'⟩

#print axioms rep_of_walk

/-! ## 12. The perturbation gap: the δ* family and the existence of a good δ

The ε-perturbation of the docstring sketch, made exact: shrink every strict edge's
log-weight by δ.  The threshold δ* is the LEAST log-weight among the short (length ≤ 7)
closed walks carrying a strict edge — a finite family (`strictClosedShort`), each of whose
members has positive log-weight by the no-bad-cycle hypothesis — and δ := δ*/7 makes every
closed walk's perturbed weight nonnegative (the tail cut handles the long ones). -/

/-- All lists of length exactly `k` over `L`. -/
-- STANDING: DEFINITION
def allLists (L : List TEdge) : Nat → List (List TEdge)
  | 0 => [[]]
  | k + 1 => L.flatMap (fun e => (allLists L k).map (fun w => e :: w))

theorem mem_allLists {L : List TEdge} : ∀ (k : Nat) (w : List TEdge), w.length = k →
    (∀ e ∈ w, e ∈ L) → w ∈ allLists L k := by
  intro k
  induction k with
  | zero =>
    intro w hl _
    cases w with
    | nil => simp [allLists]
    | cons a rest => exact absurd hl (by simp)
  | succ k ih =>
    intro w hl hmem
    cases w with
    | nil => exact absurd hl (by simp)
    | cons e rest =>
      simp only [List.length_cons] at hl
      have hrest : rest.length = k := by omega
      have hem : e ∈ L := hmem e (by simp)
      have hrestmem : ∀ x ∈ rest, x ∈ L := fun x hx => hmem x (by simp [hx])
      simp only [allLists, List.mem_flatMap]
      exact ⟨e, hem, List.mem_map.mpr ⟨rest, ih rest hrest hrestmem, rfl⟩⟩

#print axioms mem_allLists

theorem allLists_spec {L : List TEdge} : ∀ (k : Nat) (w : List TEdge), w ∈ allLists L k →
    w.length = k ∧ ∀ e ∈ w, e ∈ L := by
  intro k
  induction k with
  | zero =>
    intro w hw
    simp only [allLists] at hw
    simp at hw
    cases hw
    exact ⟨rfl, by simp⟩
  | succ k ih =>
    intro w hw
    simp only [allLists, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨e, hem, w', hw'mem, hw'eq⟩ := hw
    obtain ⟨hl, hmem⟩ := ih w' hw'mem
    cases hw'eq
    refine ⟨by simp [hl], ?_⟩
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hem
    · exact hmem a ha

#print axioms allLists_spec

/-- All lists of length ≤ 7 over `L`. -/
-- STANDING: DEFINITION
def shortLists (L : List TEdge) : List (List TEdge) := (List.range 8).flatMap (allLists L)

theorem mem_shortLists {L : List TEdge} {w : List TEdge} :
    w ∈ shortLists L ↔ w.length ≤ 7 ∧ ∀ e ∈ w, e ∈ L := by
  constructor
  · intro hw
    simp only [shortLists, List.mem_flatMap] at hw
    obtain ⟨m, hm, hw'mem⟩ := hw
    obtain ⟨hl, hmem⟩ := allLists_spec m w hw'mem
    have hmr : m < 8 := List.mem_range.mp hm
    exact ⟨by omega, hmem⟩
  · intro ⟨hlen, hmem⟩
    exact List.mem_flatMap.mpr ⟨w.length, List.mem_range.mpr (by omega),
      mem_allLists w.length w rfl hmem⟩

#print axioms mem_shortLists

/-- The δ*-family: short closed walks over `L` carrying a strict edge. -/
-- STANDING: DEFINITION
def strictClosedShort (L : List TEdge) : List (List TEdge) :=
  (shortLists L).filter (fun w => closedDec w && ((w.map TEdge.strict).any id))

theorem mem_strictClosedShort {L : List TEdge} {w : List TEdge} :
    w ∈ strictClosedShort L ↔
      w.length ≤ 7 ∧ (∀ e ∈ w, e ∈ L) ∧ (∃ v : Fin 7, WalkFrom v w v) ∧
        ((w.map TEdge.strict).any id) = true := by
  unfold strictClosedShort
  rw [List.mem_filter]
  constructor
  · rintro ⟨hsl, hboth⟩
    obtain ⟨hcd, hst⟩ :=
      Bool.and_eq_true_iff.mp
        (show (closedDec w && ((w.map TEdge.strict).any id)) = true from hboth)
    obtain ⟨hlen, hmem⟩ := mem_shortLists.mp hsl
    exact ⟨hlen, hmem, walk_of_closedDec hcd, hst⟩
  · rintro ⟨hlen, hmem, ⟨v, hv⟩, hst⟩
    exact ⟨mem_shortLists.mpr ⟨hlen, hmem⟩,
      Bool.and_eq_true_iff.mpr ⟨closedDec_of_walk hv, hst⟩⟩

#print axioms mem_strictClosedShort

/-- Minimum of a list of reals with a default for the empty list. -/
-- STANDING: DEFINITION
noncomputable def listMin (d : ℝ) : List ℝ → ℝ
  | [] => d
  | x :: xs => min x (listMin d xs)

theorem listMin_le_mem (d : ℝ) : ∀ (xs : List ℝ) (x : ℝ), x ∈ xs → listMin d xs ≤ x := by
  intro xs
  induction xs with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons y xs ih =>
    intro x hx
    simp only [listMin]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih x hx')

#print axioms listMin_le_mem

theorem listMin_pos (d : ℝ) (hd : 0 < d) : ∀ xs : List ℝ, (∀ x ∈ xs, 0 < x) →
    0 < listMin d xs := by
  intro xs
  induction xs with
  | nil => simpa [listMin] using hd
  | cons y xs ih =>
    intro h
    have h1 : 0 < y := h y (by simp)
    have h2 : 0 < listMin d xs := ih (fun x hx => h x (by simp [hx]))
    simp only [listMin]
    exact lt_min_iff.mpr ⟨h1, h2⟩

#print axioms listMin_pos

/-- The perturbation threshold: the least log-weight among the short closed strict walks
(default 1 if there are none). -/
-- STANDING: DEFINITION
noncomputable def deltaStar (edges : List TEdge) : ℝ :=
  listMin 1 ((strictClosedShort edges).map walkSum)

theorem deltaStar_pos (edges : List TEdge) (hneg : NoNegCycle edges) :
    0 < deltaStar edges := by
  have hall : ∀ x ∈ (strictClosedShort edges).map walkSum, 0 < x := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := List.mem_map.mp hx
    obtain ⟨hlen, hmem, ⟨v, hv⟩, hst⟩ := mem_strictClosedShort.mp hw
    have hbad := hneg v w hmem hv
    have hposw : 0 < walkSum w := by
      by_cases hlt : walkSum w < 0
      · exact absurd (Or.inl hlt) hbad
      · by_cases heq : walkSum w = 0
        · exact absurd (Or.inr ⟨heq, hst⟩) hbad
        · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
    rw [← hwx]
    exact hposw
  exact listMin_pos 1 (by norm_num) _ hall

#print axioms deltaStar_pos

theorem deltaStar_le (edges : List TEdge) {w : List TEdge}
    (hw : w ∈ strictClosedShort edges) : deltaStar edges ≤ walkSum w :=
  listMin_le_mem 1 _ _ (List.mem_map_of_mem hw)

#print axioms deltaStar_le

/-- **A good perturbation exists** (the δ*/7 gap argument): some δ > 0 makes every closed
walk's perturbed weight nonnegative — the hypothesis the cut machinery consumes. -/
theorem exists_good_delta (edges : List TEdge) (hneg : NoNegCycle edges) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (l : List TEdge) (v : Fin 7), (∀ e ∈ l, e ∈ edges) →
      WalkFrom v l v → 0 ≤ wsum (pw δ) l := by
  have hposδ : 0 < deltaStar edges := deltaStar_pos edges hneg
  have hbase : ∀ (l : List TEdge) (v : Fin 7), (∀ e ∈ l, e ∈ edges) → WalkFrom v l v →
      l.length ≤ 7 → 0 ≤ wsum (pw (deltaStar edges / 7)) l := by
    intro l v hsub hw hlen
    have hkstr : kstr l ≤ 7 := le_trans (kstr_le_length l) (by omega)
    by_cases hst : ((l.map TEdge.strict).any id) = true
    · have hmemF : l ∈ strictClosedShort edges :=
        mem_strictClosedShort.mpr ⟨hlen, hsub, ⟨v, hw⟩, hst⟩
      have hws : deltaStar edges ≤ walkSum l := deltaStar_le edges hmemF
      have h1 : wsum (pw (deltaStar edges / 7)) l =
          walkSum l - (deltaStar edges / 7) * kstr l :=
        wsum_pw _ l
      have h2 : (deltaStar edges / 7) * kstr l ≤ deltaStar edges := by
        have hkc : (kstr l : ℝ) ≤ 7 := by exact_mod_cast hkstr
        have h7 : (deltaStar edges / 7) * 7 = deltaStar edges := by
          field_simp
        calc (deltaStar edges / 7) * kstr l
            ≤ (deltaStar edges / 7) * 7 :=
              mul_le_mul_of_nonneg_left hkc
                (le_of_lt (div_pos hposδ (by norm_num : (0 : ℝ) < 7)))
          _ = deltaStar edges := h7
      rw [h1]
      linarith
    · have hst' : ((l.map TEdge.strict).any id) = false := by simpa using hst
      have hk0 : kstr l = 0 := kstr_eq_zero_of_no_strict hst'
      have h1 : wsum (pw (deltaStar edges / 7)) l =
          walkSum l - (deltaStar edges / 7) * kstr l :=
        wsum_pw _ l
      have hws0 : 0 ≤ walkSum l := by
        have hnp : ¬ (walkSum l < 0) := fun hc => hneg v l hsub hw (Or.inl hc)
        exact not_lt.mp hnp
      rw [h1, hk0, Nat.cast_zero, mul_zero, sub_zero]
      exact hws0
  refine ⟨deltaStar edges / 7, div_pos hposδ (by norm_num : (0 : ℝ) < 7), ?_⟩
  intro l v hsub hw
  exact closedNonneg_of_short (pw (deltaStar edges / 7)) edges hbase (l.length) l v hsub hw
    (le_refl _)

#print axioms exists_good_delta

/-! ## 13. The Bellman-Fold: the shortest-path potential, and THE CONVERSE -/

/-- One relaxation round over the edge list (a min-fold into `j`). -/
-- STANDING: DEFINITION
noncomputable def relax (wt : TEdge → ℝ) (edges : List TEdge) (dd : Fin 7 → ℝ) (j : Fin 7) :
    ℝ :=
  (edges.filter (fun e => e.b = j)).foldl (fun acc e => min acc (dd e.a + wt e)) (dd j)

/-- The k-step Bellman-Fold values (virtual source: every vertex starts at 0). -/
-- STANDING: DEFINITION
noncomputable def dval (wt : TEdge → ℝ) (edges : List TEdge) : Nat → Fin 7 → ℝ
  | 0, _ => 0
  | k + 1, j => relax wt edges (dval wt edges k) j

theorem foldl_min_le_init (g : TEdge → ℝ) : ∀ (l : List TEdge) (init : ℝ),
    l.foldl (fun acc e => min acc (g e)) init ≤ init := by
  intro l
  induction l with
  | nil => intro init; exact le_refl _
  | cons e l ih =>
    intro init
    show l.foldl (fun acc e => min acc (g e)) (min init (g e)) ≤ init
    exact le_trans (ih _) (min_le_left _ _)

#print axioms foldl_min_le_init

theorem foldl_min_le_mem (g : TEdge → ℝ) : ∀ (l : List TEdge) (init : ℝ) (x : TEdge),
    x ∈ l → l.foldl (fun acc e => min acc (g e)) init ≤ g x := by
  intro l
  induction l with
  | nil => intro init x hx; exact absurd hx List.not_mem_nil
  | cons e l ih =>
    intro init x hx
    show l.foldl (fun acc e => min acc (g e)) (min init (g e)) ≤ g x
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (foldl_min_le_init g l _) (min_le_right _ _)
    · exact ih (min init (g e)) x hx'

#print axioms foldl_min_le_mem

theorem foldl_min_cases (g : TEdge → ℝ) : ∀ (l : List TEdge) (init : ℝ),
    l.foldl (fun acc e => min acc (g e)) init = init ∨
      ∃ x : TEdge, x ∈ l ∧ l.foldl (fun acc e => min acc (g e)) init = g x := by
  intro l
  induction l with
  | nil => intro init; exact Or.inl rfl
  | cons e l ih =>
    intro init
    show l.foldl (fun acc e => min acc (g e)) (min init (g e)) = init ∨
      ∃ x : TEdge, x ∈ e :: l ∧
        l.foldl (fun acc e => min acc (g e)) (min init (g e)) = g x
    rcases ih (min init (g e)) with h | ⟨x, hx, hval⟩
    · rcases le_total (g e) init with hle | hlt
      · exact Or.inr ⟨e, List.mem_cons_self,
          by rw [h, min_eq_right hle]⟩
      · exact Or.inl (by rw [h, min_eq_left hlt])
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hval⟩

#print axioms foldl_min_cases

theorem relax_le (wt : TEdge → ℝ) (edges : List TEdge) (dd : Fin 7 → ℝ) (j : Fin 7) :
    relax wt edges dd j ≤ dd j :=
  foldl_min_le_init (fun x => dd x.a + wt x) _ _

#print axioms relax_le

theorem relax_le_edge (wt : TEdge → ℝ) (edges : List TEdge) (dd : Fin 7 → ℝ) (e : TEdge)
    (he : e ∈ edges) : relax wt edges dd e.b ≤ dd e.a + wt e :=
  foldl_min_le_mem (fun x => dd x.a + wt x) _ _ e (List.mem_filter.mpr ⟨he, by simp⟩)

#print axioms relax_le_edge

theorem dval_mono (wt : TEdge → ℝ) (edges : List TEdge) (k : Nat) (j : Fin 7) :
    dval wt edges (k + 1) j ≤ dval wt edges k j :=
  relax_le wt edges (dval wt edges k) j

#print axioms dval_mono

theorem dval_anti (wt : TEdge → ℝ) (edges : List TEdge) : ∀ (n m : Nat) (j : Fin 7),
    m ≤ n → dval wt edges n j ≤ dval wt edges m j := by
  intro n
  induction n with
  | zero =>
    intro m j hmn
    have h0 : m = 0 := by omega
    cases h0
    exact le_refl _
  | succ n ih =>
    intro m j hmn
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact le_trans (dval_mono wt edges n j) (ih m j (by omega))
    · have h1 : m = n + 1 := by omega
      cases h1
      exact le_refl _

#print axioms dval_anti

/-- **Attainment:** each fold value is the weight of an actual short walk. -/
theorem dval_attain (wt : TEdge → ℝ) (edges : List TEdge) : ∀ (k : Nat) (j : Fin 7),
    ∃ (l : List TEdge) (t : Fin 7), WalkFrom t l j ∧ l.length ≤ k ∧
      (∀ e ∈ l, e ∈ edges) ∧ wsum wt l = dval wt edges k j := by
  intro k
  induction k with
  | zero =>
    intro j
    exact ⟨[], j, WalkFrom.nil j, le_refl _, by simp, rfl⟩
  | succ k ih =>
    intro j
    have hdef : dval wt edges (k + 1) j =
        (edges.filter (fun e => e.b = j)).foldl
          (fun acc e => min acc (dval wt edges k e.a + wt e)) (dval wt edges k j) := rfl
    rcases foldl_min_cases (fun x => dval wt edges k x.a + wt x)
        (edges.filter (fun e => e.b = j)) (dval wt edges k j) with h | ⟨x, hx, hval⟩
    · obtain ⟨l₀, t₀, hw₀, hlen₀, hsub₀, hws₀⟩ := ih j
      refine ⟨l₀, t₀, hw₀, le_trans hlen₀ (by omega), hsub₀, ?_⟩
      rw [hdef, h, hws₀]
    · obtain ⟨hxmem, hxb⟩ := List.mem_filter.mp hx
      have hxb' : x.b = j := by simpa using hxb
      obtain ⟨l₀, t₀, hw₀, hlen₀, hsub₀, hws₀⟩ := ih x.a
      have hwalkx : WalkFrom x.a [x] j :=
        WalkFrom.cons x.a x [] j rfl (by rw [hxb']; exact WalkFrom.nil j)
      have hlenx : (l₀ ++ [x]).length ≤ k + 1 := by
        rw [List.length_append, List.length_cons, List.length_nil]
        omega
      have hwsx : wsum wt (l₀ ++ [x]) = wsum wt l₀ + wt x := by
        rw [wsum_append, wsum_cons, wsum_nil]; ring
      refine ⟨l₀ ++ [x], t₀, walk_append t₀ l₀ x.a hw₀ [x] hwalkx, hlenx, ?_, ?_⟩
      · intro e he
        rw [List.mem_append] at he
        rcases he with he | he
        · exact hsub₀ e he
        · simp at he
          cases he
          exact hxmem
      · rw [hwsx, hws₀, hdef, hval]

#print axioms dval_attain

/-- **Last-edge extraction:** a nonempty walk ends with an actual edge into its target. -/
theorem walk_last {l : List TEdge} {t j : Fin 7} (hw : WalkFrom t l j) (hne : l ≠ []) :
    ∃ (pre : List TEdge) (e : TEdge), l = pre ++ [e] ∧ WalkFrom t pre e.a ∧ e.b = j := by
  induction hw with
  | nil s => exact absurd rfl hne
  | @cons s e l' j' he hrest ih =>
    cases l' with
    | nil =>
      refine ⟨[], e, by simp, ?_, ?_⟩
      · rw [he]
        exact WalkFrom.nil s
      · cases hrest
        rfl
    | cons e' rest' =>
      obtain ⟨pre', e'', hpe, hwp, he''b⟩ := ih (by simp)
      refine ⟨e :: pre', e'', ?_, WalkFrom.cons s e pre' e''.a he hwp, he''b⟩
      rw [hpe]
      simp [List.cons_append]

#print axioms walk_last

/-- **Upper semantics of the fold:** `dval k` is a lower bound for every walk of length
≤ k (the n-step Bellman-Ford fold, by induction on k with the last-edge extraction). -/
theorem dval_le_wsum (wt : TEdge → ℝ) (edges : List TEdge) : ∀ (k : Nat) (l : List TEdge)
    (t j : Fin 7), WalkFrom t l j → l.length ≤ k → (∀ e ∈ l, e ∈ edges) →
    dval wt edges k j ≤ wsum wt l := by
  intro k
  induction k with
  | zero =>
    intro l t j hw hlen _
    cases hw with
    | nil => exact le_refl (0 : ℝ)
    | cons => exact absurd hlen (by simp)
  | succ k ih =>
    intro l t j hw hlen hsub
    by_cases hl0 : l = []
    · subst hl0
      have h1 := dval_anti wt edges (k + 1) 0 j (by omega)
      have h2 : dval wt edges 0 j = 0 := rfl
      have h3 : wsum wt ([] : List TEdge) = 0 := wsum_nil wt
      linarith
    · obtain ⟨pre, e, hpe, hwpre, hebj⟩ := walk_last hw hl0
      have hprelen : pre.length ≤ k := by
        rw [hpe, List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      have hpresub : ∀ x ∈ pre, x ∈ edges := fun x hx => hsub x (by rw [hpe]; simp [hx])
      have hemem : e ∈ edges := hsub e (by rw [hpe]; simp)
      have h1 : dval wt edges (k + 1) j ≤ dval wt edges k e.a + wt e := by
        have h2 := relax_le_edge wt edges (dval wt edges k) e hemem
        rw [hebj] at h2
        exact h2
      have h2 : dval wt edges k e.a ≤ wsum wt pre := ih pre t e.a hwpre hprelen hpresub
      have h3 : wsum wt (pre ++ [e]) = wsum wt pre + wt e := by
        rw [wsum_append, wsum_cons, wsum_nil]; ring
      rw [hpe, h3]
      linarith

#print axioms dval_le_wsum

/-- **Stabilization at round 6:** the fold stops decreasing — the loop-cut content of the
whole construction (nothing beyond 6-edge walks matters on 7 vertices). -/
theorem dval_stab (wt : TEdge → ℝ) (edges : List TEdge)
    (hcn : ∀ (l₀ : List TEdge) (v : Fin 7), (∀ e ∈ l₀, e ∈ edges) → WalkFrom v l₀ v →
      0 ≤ wsum wt l₀)
    (j : Fin 7) : dval wt edges 6 j ≤ dval wt edges 7 j := by
  obtain ⟨l, t, hw, hlen, hsub, hws⟩ := dval_attain wt edges 7 j
  obtain ⟨l', hW', hsub', hlen6, hwsum'⟩ :=
    rep_of_walk wt edges hcn 7 l t j hsub hw hlen
  have h1 := dval_le_wsum wt edges 6 l' t j hW' hlen6 hsub'
  rw [hws] at hwsum'
  linarith

#print axioms dval_stab

/-- **THE CONVERSE, PROVED.**  No additive bad cycle + positive weights ⟹ a potential
exists: the δ-perturbed Bellman-Fold at round 7, negated.  The edge inequalities close by
relaxation at round 7 (`dval 7 e.b ≤ dval 6 e.a + pw δ e`) plus stabilization
(`dval 6 = dval 7`); the strictness is carried entirely by the perturbation
(`pw δ e = log e.c - δ < log e.c` on strict edges). -/
theorem isPotential_of_noNegCycle (edges : List TEdge) (hneg : NoNegCycle edges) :
    ∃ u : Fin 7 → ℝ, IsPotential edges u := by
  obtain ⟨δ, hδpos, hcn⟩ := exists_good_delta edges hneg
  have hedge : ∀ e ∈ edges,
      dval (pw δ) edges 7 e.b ≤ dval (pw δ) edges 7 e.a + pw δ e := by
    intro e he
    have h1 : dval (pw δ) edges 7 e.b ≤ dval (pw δ) edges 6 e.a + pw δ e :=
      relax_le_edge (pw δ) edges (dval (pw δ) edges 6) e he
    have h2 : dval (pw δ) edges 6 e.a = dval (pw δ) edges 7 e.a :=
      le_antisymm (dval_stab (pw δ) edges hcn e.a) (dval_mono (pw δ) edges 6 e.a)
    rw [h2] at h1
    exact h1
  refine ⟨fun i => -(dval (pw δ) edges 7 i), fun e he => ?_⟩
  have hkey : dval (pw δ) edges 7 e.b - dval (pw δ) edges 7 e.a ≤ pw δ e := by
    have hh := hedge e he
    linarith
  cases hst : e.strict with
  | false =>
    have hpf : pw δ e = Real.log e.c := pw_nonstrict δ hst
    simp only [RHolds]
    rw [hpf] at hkey
    linarith
  | true =>
    have hpf : pw δ e = Real.log e.c - δ := pw_strict δ hst
    simp only [RHolds]
    rw [hpf] at hkey
    linarith

#print axioms isPotential_of_noNegCycle

/-- **`PotentialOwed` DISCHARGED — the converse's potential-existence is a theorem.**
(The docstring's Floyd-Warshall sketch, proved: pigeonhole cut §11, δ*-gap §12,
Bellman-Fold stabilization §13.) -/
theorem potentialOwed_proved (edges : List TEdge) : PotentialOwed edges := by
  intro hpos hneg
  exact isPotential_of_noNegCycle edges hneg

#print axioms potentialOwed_proved

/-- **THE COMPLETENESS THEOREM.**  For a positive-weight edge system over the readings:
no bad cycle ⟹ satisfiable.  Combined with `Fresh.TropicalCycle.tropicalCycle_infeasible`
(the sound direction) the ratio-cycle criterion is EXACTLY the feasibility criterion —
every kill is a cycle instance, and nothing outside the cycle structure is ever needed. -/
theorem feasible_of_noGoodCycle_proved (edges : List TEdge) :
    Fresh.TropicalCycle.feasible_of_noGoodCycle edges :=
  feasible_of_noGoodCycle_of_potentialOwed edges (potentialOwed_proved edges)

#print axioms feasible_of_noGoodCycle_proved

end Fresh.TropicalConverse
