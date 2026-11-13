import Mathlib
import Fresh.FilterAssembly
import Fresh.JoinFamComposed
import Fresh.UClosureKill

/-!
# TropicalCycle: the unifying tropical-cycle conflict theorem of the n=8 campaign

Written 2026-11-13.  New file; nothing existing is edited.  One theorem that subsumes the
four separately-proved pieces of the conflict machinery as instances of a single law —
the campaign's E838 identification ("demanded-ratio products crossing 1") in its sharp
form.  The system: a finite list of edges `(a, b, c, strict)` over positive real readings
`g : Fin 7 → ℝ`, each edge demanding `ρa/ρb < c` (strict) or `ρa/ρb ≤ c`, i.e. a weighted
digraph on the seven readings.  Then:

* **`tropicalCycle_infeasible` (PROVED, forward/sound direction).**  If `g` satisfies every
  edge pointwise, the graph contains NO bad cycle: no head-to-tail closed walk of edges
  whose weight product is `< 1`, and none whose product is `= 1` while carrying a strict
  edge.  Proof: multiply the walk's edge inequalities — the readings telescope (each
  intermediate reading appears once as numerator, once as denominator) leaving
  `g s / g s = 1 <(≤) ∏ cᵢ` with strictness OR-ed along the walk; the flag logic gives the
  two cases.  The engine is `walk_telescope`, the cycle-closed generalization of
  `Fresh.JoinFamComposed.chain_real_compose` (which adds strictness flags to the n-step
  telescoping); the strictness composition `rholds_mul2` is the ℝ form of
  `Fresh.UClosure.bhold_mul2`.
* **`feasible_of_noGoodCycle` (OWED, converse/Bellman-Ford direction).**  If no bad cycle
  exists, some positive `g` satisfies every edge — the REVIEWED U-closure criterion's
  sufficiency half (infeasible ⟺ a cycle with product < 1, or = 1 with a strict side).
  Stated verbatim as the named OWED with the δ-perturbation sketch in its docstring: in
  log coordinates `u i = log g i` the system is a difference-constraint system
  (`u a − u b <(≤) log c`), feasible exactly when the constraint digraph has no negative
  cycle (the strictness handled by the ε-perturbation `c ↦ c·(1+ε)` on strict edges);
  a potential from the shortest-path distances gives `g i = exp(δ i)`.

Correspondence table (each existing lemma recovered as an instance):

| campaign lemma | cycle instance | cycle product | strict side |
|---|---|---|---|
| `Fresh.SpineSound.joinEdge_conflict` (n=1) | `joinEdge_conflict_as_instance`: 2-cycle `y → x` cap `C/D` (nonstrict) then `x → y` demand `A/B` (strict) | `AC/BD ≤ 1` from the datum `A·C ≤ B·D` | the demand edge |
| `Fresh.JoinFamComposed.composedCap_conflict` (n-step) | `composedCap_as_instance`: the cap chain `u → z₁ → … → w` plus demand edge `w → u` `A/B` (strict) — `capsToEdges` turns `ChainReal` into walk edges | `c₁⋯cₙ · A/B ≤ 1` from the composed datum `A·c₁⋯cₙ ≤ B` | the demand edge |
| `Fresh.UClosureKill.twoCycle_contra` (U-table feasibility) | `uClosure_twoCycle_as_instance`: the same 2-cycle at the back-checked pair | `d·c` | either stored flag (`s ∨ t`) |
| `Fresh.PinchCert` tangency (the pinch certificate) | `pinch_as_observation` (comment-level): the equality case `∏ = 1` with a strict side is exactly the tangency/pinch — on the plane `ρ₇/ρ₅ = (8a+1)/(8b+1)` (`PlaneH3`: `25ρ₇ = 89ρ₅`, `a = 11, b = 3`) the cycle product is exactly 1 and the strictness is consumed at the pinch point `R*`; the E838/E830 binding-path products (e.g. `86989/3565 = (129/15)(17/23)(17/31)(49/7)`, `midbound_plan_v1.out`) are cycle-weight products of the criterion | | |

The converse correspondence (noted, OWED): the U-table of `Fresh.UClosureKill` accumulates
tightest implied bounds — that is Bellman–Ford's shortest-path relaxation, i.e. the
converse direction's algorithm running as data; `kill_sound`'s chain-exclusion form is the
fixpoint of "no good cycle ⟹ feasible", so `feasible_of_noGoodCycle` is the semantic
statement behind link 2's reviewed criterion.
-/

namespace Fresh.TropicalCycle

open Fresh.UClosure (BHolds)

/-! ## 1. Edges, the strictness-flag semantics, and flag composition -/

/-- One constrained edge: reading `e.a` over reading `e.b` is bounded by the weight `e.c`,
strictly iff `e.strict` — the data `ρa/ρb <(≤) c` of the raw-edge/composed-cap/U-table
machinery. -/
structure TEdge where
  a : Fin 7
  b : Fin 7
  c : ℝ
  strict : Bool

/-- The real-valued strictness-flag semantic — the ℝ form of `Fresh.UClosure.BHolds`
(whose weights are rationals). -/
-- STANDING: DEFINITION
def RHolds : Bool → ℝ → ℝ → Prop
  | true, x, c => x < c
  | false, x, c => x ≤ c

/-- Edge satisfaction by the readings `g`. -/
-- STANDING: DEFINITION
def EdgeSat (g : Fin 7 → ℝ) (e : TEdge) : Prop := RHolds e.strict (g e.a / g e.b) e.c

/-- A satisfied edge has positive weight (the ratio is positive). -/
theorem edge_c_pos {g : Fin 7 → ℝ} {e : TEdge} (hend : 0 < g e.a ∧ 0 < g e.b)
    (h : EdgeSat g e) : 0 < e.c := by
  have hdiv : (0 : ℝ) < g e.a / g e.b := div_pos hend.1 hend.2
  cases hst : e.strict with
  | true =>
    simp only [EdgeSat, hst, RHolds] at h
    exact lt_trans hdiv h
  | false =>
    simp only [EdgeSat, hst, RHolds] at h
    exact lt_of_lt_of_le hdiv h

#print axioms edge_c_pos

/-- Two chained ratio bounds compose with the strictness flags OR-ed — the ℝ form of
`Fresh.UClosure.bhold_mul2`: `(u/v ≤(<) A) → (v/w ≤(<) C) → u/w ≤(<) A·C`. -/
theorem rholds_mul2 (f1 f2 : Bool) {u v w A C : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : RHolds f1 (u / v) A) (h2 : RHolds f2 (v / w) C) : RHolds (f1 || f2) (u / w) (A * C) := by
  cases f1 <;> cases f2 <;>
    simp only [RHolds, Bool.true_or, Bool.false_or] at h1 h2 ⊢
  · have e1 : u ≤ A * v := (div_le_iff₀ hv).mp h1
    have e2 : v ≤ C * w := (div_le_iff₀ hw).mp h2
    exact (div_le_iff₀ hw).mpr (by
      calc u ≤ A * v := e1
        _ ≤ A * (C * w) := mul_le_mul_of_nonneg_left e2 hA.le
        _ = A * C * w := by ring)
  · have e1 : u ≤ A * v := (div_le_iff₀ hv).mp h1
    have e2 : v < C * w := (div_lt_iff₀ hw).mp h2
    exact (div_lt_iff₀ hw).mpr (by
      calc u ≤ A * v := e1
        _ < A * (C * w) := mul_lt_mul_of_pos_left e2 hA
        _ = A * C * w := by ring)
  · have e1 : u < A * v := (div_lt_iff₀ hv).mp h1
    have e2 : v ≤ C * w := (div_le_iff₀ hw).mp h2
    exact (div_lt_iff₀ hw).mpr (by
      calc u < A * v := e1
        _ ≤ A * (C * w) := mul_le_mul_of_nonneg_left e2 hA.le
        _ = A * C * w := by ring)
  · have e1 : u < A * v := (div_lt_iff₀ hv).mp h1
    have e2 : v < C * w := (div_lt_iff₀ hw).mp h2
    exact (div_lt_iff₀ hw).mpr (by
      calc u < A * v := e1
        _ ≤ A * (C * w) := mul_le_mul_of_nonneg_left e2.le hA.le
        _ = A * C * w := by ring)

#print axioms rholds_mul2

/-! ## 2. Walks and the telescoping walk bound -/

/-- A head-to-tail walk of edges from `s` ending at `t`: consecutive edges share the
reading (`e.a = s` of the current step, `e.b` the start of the rest). -/
inductive WalkFrom : Fin 7 → List TEdge → Fin 7 → Prop
  | nil (s : Fin 7) : WalkFrom s [] s
  | cons (s : Fin 7) (e : TEdge) (l : List TEdge) (t : Fin 7)
      (he : e.a = s) (hrest : WalkFrom e.b l t) : WalkFrom s (e :: l) t

/-- Walks concatenate at the meeting reading. -/
theorem walk_append {t : Fin 7} :
    ∀ (s : Fin 7) (l : List TEdge) (m : Fin 7), WalkFrom s l m →
    ∀ (l' : List TEdge), WalkFrom m l' t → WalkFrom s (l ++ l') t := by
  intro s l m h1
  induction h1 with
  | nil s => intro l' h2; exact h2
  | @cons s e l m he hrest ih =>
    intro l' h2
    exact WalkFrom.cons s e (l ++ l') t he (ih l' h2)

#print axioms walk_append

/-- **The telescoping walk bound (the cycle telescope's engine).**  A walk of satisfied
edges from `s` to `t` bounds `g s / g t` by the PRODUCT of the weights, strictness OR-ed
along the walk, every weight positive — the readings telescope: each intermediate reading
appears once as a numerator, once as a denominator.  This is
`Fresh.JoinFamComposed.chain_real_compose` with strictness flags added (there the walk
hypotheses are `ChainReal`, all-caps nonstrict). -/
theorem walk_telescope {g : Fin 7 → ℝ} {s t : Fin 7} {l : List TEdge}
    (hw : WalkFrom s l t) (hsat : ∀ e ∈ l, EdgeSat g e)
    (hend : ∀ e ∈ l, 0 < g e.a ∧ 0 < g e.b) (hgs : 0 < g s) (hgt : 0 < g t) :
    (∀ e ∈ l, 0 < e.c) ∧ RHolds ((l.map TEdge.strict).any id) (g s / g t) ((l.map TEdge.c).prod) := by
  induction hw with
  | nil s =>
    refine ⟨fun e he => absurd he List.not_mem_nil, ?_⟩
    simp only [List.map_nil, List.any_nil, List.prod_nil, RHolds]
    rw [div_self (ne_of_gt hgs)]
  | @cons s e l t he hrest ih =>
    -- the step edge: satisfied, positive weight, positive far endpoint
    have hestat : EdgeSat g e := hsat e (by simp)
    have hec : 0 < e.c := edge_c_pos (hend e (by simp)) hestat
    have hvb : 0 < g e.b := (hend e (by simp)).2
    have h1 : RHolds e.strict (g s / g e.b) e.c := by
      rw [← he]
      exact hestat
    obtain ⟨hpos, hbound⟩ :=
      ih (fun x hx => hsat x (List.mem_cons_of_mem _ hx))
        (fun x hx => hend x (List.mem_cons_of_mem _ hx)) hvb hgt
    have hmap : ∀ a ∈ l.map TEdge.c, 0 < a := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact hpos x hx
    have hflag : (((e :: l).map TEdge.strict).any id) =
        (e.strict || ((l.map TEdge.strict).any id)) := by simp
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hec
      · exact hpos x hx
    · rw [hflag, List.map_cons, List.prod_cons]
      exact rholds_mul2 e.strict ((l.map TEdge.strict).any id) hvb hgt hec
        (List.prod_pos hmap) h1 hbound

#print axioms walk_telescope

/-! ## 3. The unifying theorem: satisfied systems have no bad cycle -/

/-- **The unifying conflict theorem (the tropical-cycle criterion, sound direction).**
For positive real readings `g` satisfying every edge of a head-to-tail closed walk
(a cycle in the induced weighted digraph on the readings), the cycle is NOT bad: its
weight product is not `< 1`, and it is not `= 1` while carrying a strict edge.
Equivalently (contrapositive, the form every conflict lemma consumes): a system of
strict/nonstrict ratio constraints `ρa/ρb <(≤) c` is INFEASIBLE as soon as the graph has
a cycle with weight product `< 1`, or `= 1` with at least one strict edge on it.

Proof: `walk_telescope` multiplies the walk's inequalities — the readings telescope
through the matching endpoints (`div_self` at the closed walk) leaving
`1 <(≤) ∏ cᵢ` with the strictness OR-ed; the flag cases close against the bad-cycle
disjunction. -/
theorem tropicalCycle_infeasible {g : Fin 7 → ℝ} {s : Fin 7} {l : List TEdge}
    (hw : WalkFrom s l s) (hsat : ∀ e ∈ l, EdgeSat g e)
    (hend : ∀ e ∈ l, 0 < g e.a ∧ 0 < g e.b) :
    ¬ ((l.map TEdge.c).prod < 1 ∨
        (l.map TEdge.c).prod = 1 ∧ ((l.map TEdge.strict).any id) = true) := by
  cases l with
  | nil =>
    intro hbad
    simp only [List.map_nil, List.prod_nil, List.any_nil] at hbad
    simp at hbad
  | cons e l' =>
    cases hw with
    | @cons s _ _ _ he hrest =>
      have hgs : (0 : ℝ) < g s := by
        rw [← he]
        exact (hend e (by simp)).1
      have hw' : WalkFrom s (e :: l') s := WalkFrom.cons s e l' s he hrest
      obtain ⟨hpos, hbound⟩ := walk_telescope hw' hsat hend hgs hgs
      rw [div_self (ne_of_gt hgs)] at hbound
      cases hf : (((e :: l') : List TEdge).map TEdge.strict).any id with
      | false =>
        simp only [hf, RHolds] at hbound
        intro hbad
        rcases hbad with h | ⟨heq, hst⟩
        · linarith
        · exact absurd hst (by decide)
      | true =>
        simp only [hf, RHolds] at hbound
        intro hbad
        rcases hbad with h | ⟨heq, hst⟩
        · linarith
        · linarith

#print axioms tropicalCycle_infeasible

/-! ## 4. The system-level packaging and the converse (OWED) -/

/-- A finite edge system is satisfiable when some positive reading vector realizes every
edge. -/
-- STANDING: DEFINITION
def Satisfiable (edges : List TEdge) : Prop :=
  ∃ g : Fin 7 → ℝ, (∀ e ∈ edges, 0 < g e.a ∧ 0 < g e.b) ∧ ∀ e ∈ edges, EdgeSat g e

/-- The system contains no bad cycle (the cycle quantifies over all head-to-tail closed
walks drawn from the edge list). -/
-- STANDING: DEFINITION
def NoBadCycle (edges : List TEdge) : Prop :=
  ∀ (s : Fin 7) (l : List TEdge), (∀ e ∈ l, e ∈ edges) → WalkFrom s l s →
    ¬ ((l.map TEdge.c).prod < 1 ∨
        (l.map TEdge.c).prod = 1 ∧ ((l.map TEdge.strict).any id) = true)

/-- The unifying theorem at the system level: a satisfiable system has no bad cycle —
restriction of `tropicalCycle_infeasible` along the sublist. -/
theorem satisfiable_noBadCycle {edges : List TEdge} (h : Satisfiable edges) :
    NoBadCycle edges := by
  obtain ⟨g, hend, hsat⟩ := h
  intro s l hsub hw
  exact tropicalCycle_infeasible hw (fun e he => hsat e (hsub e he))
    (fun e he => hend e (hsub e he))

#print axioms satisfiable_noBadCycle

/-- **The converse (Bellman-Ford / δ-perturbation direction), OWED.**  If an edge system
with positive weights has no bad cycle, it is satisfiable — the sufficiency half of the
REVIEWED U-closure feasibility criterion (`Fresh.UClosureKill`'s link 2:
feasible ⟺ no cycle with product < 1, or = 1 with a strict side).

Proof sketch (the standard difference-constraint argument, not formalized here):
substitute `u i = log (g i)`, turning `ρa/ρb <(≤) c` into the difference constraint
`u a − u b <(≤) log c` (with `log c < 0` — these are the "negative weights").  A
difference-constraint system over `Fin 7` is feasible iff its constraint digraph has no
negative cycle (the strict case by the ε-perturbation: shrink every strict edge's weight
to `log c − ε`, solve the nonstrict system via the no-negative-cycle potential `δ i` from
Bellman-Ford relaxation, then let `ε → 0`); set `g i = exp (δ i)`.  The U-table of
`Fresh.UClosureKill` accumulates exactly these tightest implied bounds — the algorithmic
shadow of this lemma (`uAdd`/`uProp` are Bellman-Ford relaxation steps), so the OWED is
the semantic statement behind link 2's back-check. -/
-- STANDING: DEFINITION
def feasible_of_noGoodCycle (edges : List TEdge) : Prop :=
  (∀ e ∈ edges, 0 < e.c) → NoBadCycle edges → Satisfiable edges

#print axioms feasible_of_noGoodCycle

/-! ## 5. Corollary (a): the raw-edge engine `joinEdge_conflict` as the 2-cycle instance -/

/-- **`Fresh.SpineSound.joinEdge_conflict` recovered as the 2-cycle instance of
`tropicalCycle_infeasible`.**  The demand edge `x → y` (`ρx/ρy < A/B`, strict) and the cap
edge `y → x` (`ρy/ρx ≤ C/D`, nonstrict) form a cycle at `y` with weight product
`(C/D)·(A/B) = AC/BD ≤ 1` (the datum `A·C ≤ B·D`) carrying the strict demand edge —
exactly a bad cycle, so the readings cannot realize both.  The telescoping cross-
multiplication of the original engine is the 2-edge case of `walk_telescope`. -/
theorem joinEdge_conflict_as_instance {e : Fresh.FilterAssembly.JoinEdge} {g : Fin 7 → ℝ}
    (hB : 0 < e.B) (hD : 0 < e.D) (hAC : e.A * e.C ≤ e.B * e.D)
    (hxpos : 0 < g e.x) (hypos : 0 < g e.y)
    (hdemand : g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ))
    (hcap : g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)) : False := by
  have hB' : (0 : ℝ) < (e.B : ℝ) := by exact_mod_cast hB
  have hD' : (0 : ℝ) < (e.D : ℝ) := by exact_mod_cast hD
  have hAC' : (e.A : ℝ) * (e.C : ℝ) ≤ (e.B : ℝ) * (e.D : ℝ) := by exact_mod_cast hAC
  have hcapSat : EdgeSat g ⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩ := hcap
  have hdemSat : EdgeSat g ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩ := hdemand
  have hw : WalkFrom e.y [⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩,
      ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩] e.y :=
    WalkFrom.cons e.y ⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩
      [⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩] e.y rfl
      (WalkFrom.cons e.x ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩ [] e.y rfl
        (WalkFrom.nil e.y))
  have hcontra := tropicalCycle_infeasible hw
    (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hcapSat
      · rcases hx with rfl | hx
        · exact hdemSat
        · exact absurd hx List.not_mem_nil)
    (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hypos, hxpos⟩
      · rcases hx with rfl | hx
        · exact ⟨hxpos, hypos⟩
        · exact absurd hx List.not_mem_nil)
  have hprod : ((([⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩,
      ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩] : List TEdge).map TEdge.c)).prod
      = (e.A : ℝ) * (e.C : ℝ) / ((e.B : ℝ) * (e.D : ℝ)) := by
    simp only [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil]
    ring
  have hle1 : ((([⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩,
      ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩] : List TEdge).map TEdge.c)).prod ≤ 1 := by
    rw [hprod]
    exact (div_le_iff₀ (mul_pos hB' hD')).mpr (by rw [one_mul]; exact hAC')
  have hstrict : ((([⟨e.y, e.x, (e.C : ℝ) / (e.D : ℝ), false⟩,
      ⟨e.x, e.y, (e.A : ℝ) / (e.B : ℝ), true⟩] : List TEdge).map TEdge.strict).any id)
      = true := by
    simp
  refine hcontra ?_
  rcases lt_or_eq_of_le hle1 with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hstrict⟩

#print axioms joinEdge_conflict_as_instance

/-! ## 6. Corollary (b): the composed-cap engine as the n-step cycle instance -/

/-- The edge list of a `ChainReal` cap chain started at `u`: one nonstrict edge per cap
`(z, c)`, the source tracked along the walk. -/
def capsToEdges : Fin 7 → List (Fin 7 × ℝ) → List TEdge
  | _, [] => []
  | u, p :: rest => ⟨u, p.1, p.2, false⟩ :: capsToEdges p.1 rest

@[simp] theorem capsToEdges_cons (u v : Fin 7) (c : ℝ) (l : List (Fin 7 × ℝ)) :
    capsToEdges u ((v, c) :: l) = ⟨u, v, c, false⟩ :: capsToEdges v l := rfl

@[simp] theorem capsToEdges_map_c (u : Fin 7) : ∀ l : List (Fin 7 × ℝ),
    (capsToEdges u l).map TEdge.c = l.map Prod.snd := by
  intro l
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨v, c⟩ := p
    simp [capsToEdges_cons, ih]

#print axioms capsToEdges_map_c

@[simp] theorem capsToEdges_map_strict (u : Fin 7) : ∀ l : List (Fin 7 × ℝ),
    ((capsToEdges u l).map TEdge.strict).any id = false := by
  intro l
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨v, c⟩ := p
    simp [capsToEdges_cons, ih]

#print axioms capsToEdges_map_strict

/-- The cap chain's edge list is a walk (the chain-endpoint bookkeeping). -/
theorem walk_capsToEdges {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : Fresh.JoinFamComposed.ChainReal g u caps w) :
    WalkFrom u (capsToEdges u caps) w := by
  induction h with
  | nil u _ => exact WalkFrom.nil u
  | cons u v c l w _ _ _ _ ih =>
    rw [capsToEdges_cons]
    exact WalkFrom.cons u ⟨u, v, c, false⟩ (capsToEdges v l) w rfl ih

#print axioms walk_capsToEdges

/-- Every edge of the cap chain's edge list is satisfied (the `ChainReal` semantics). -/
theorem capEdge_sat {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : Fresh.JoinFamComposed.ChainReal g u caps w) :
    ∀ x ∈ capsToEdges u caps, EdgeSat g x := by
  induction h with
  | nil u _ => intro x hx; exact absurd hx List.not_mem_nil
  | cons u v c l w hcap _ _ _ ih =>
    intro x hx
    rw [capsToEdges_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [EdgeSat, RHolds]
      exact hcap
    · exact ih x hx

#print axioms capEdge_sat

/-- Every edge of the cap chain's edge list has positive endpoint readings. -/
theorem capEdge_pos {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : Fresh.JoinFamComposed.ChainReal g u caps w) :
    ∀ x ∈ capsToEdges u caps, 0 < g x.a ∧ 0 < g x.b := by
  induction h with
  | nil u _ => intro x hx; exact absurd hx List.not_mem_nil
  | cons u v c l w _ hupos hvpos _ ih =>
    intro x hx
    rw [capsToEdges_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hupos, hvpos⟩
    · exact ih x hx

#print axioms capEdge_pos

/-- **`Fresh.JoinFamComposed.composedCap_conflict` recovered as the n-step cycle instance.**
The realized cap chain `ρu/ρz₁ ≤ c₁, …, ρzₙ/ρw ≤ cₙ` (the `ChainReal` walk) plus the word
demand `ρw/ρu < A/B` (strict) form a cycle at `u` through the intermediate readings with
weight product `c₁⋯cₙ · A/B ≤ 1` (the composed datum `A·c₁⋯cₙ ≤ B`) carrying the strict
demand edge — a bad cycle.  `chain_real_compose`'s telescoping is the walk bound; the
cycle closes it at `u`. -/
theorem composedCap_as_instance {g : Fin 7 → ℝ} {u w : Fin 7} {caps : List (Fin 7 × ℝ)}
    (hreal : Fresh.JoinFamComposed.ChainReal g u caps w)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hdemand : g w / g u < A / B)
    (hdatum : A * (caps.map Prod.snd).prod ≤ B) : False := by
  obtain ⟨hu, hwpos, -, -⟩ := Fresh.JoinFamComposed.chain_real_compose hreal
  have hdemSat : EdgeSat g ⟨w, u, A / B, true⟩ := hdemand
  have hwalk : WalkFrom u (capsToEdges u caps ++ [⟨w, u, A / B, true⟩]) u :=
    walk_append u (capsToEdges u caps) w (walk_capsToEdges hreal) [⟨w, u, A / B, true⟩]
      (WalkFrom.cons w ⟨w, u, A / B, true⟩ [] u rfl (WalkFrom.nil u))
  have hsat : ∀ x ∈ (capsToEdges u caps ++ [⟨w, u, A / B, true⟩] : List TEdge), EdgeSat g x := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact capEdge_sat hreal x hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hdemSat
      · exact absurd hx List.not_mem_nil
  have hend : ∀ x ∈ (capsToEdges u caps ++ [⟨w, u, A / B, true⟩] : List TEdge),
      0 < g x.a ∧ 0 < g x.b := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact capEdge_pos hreal x hx
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hwpos, hu⟩
      · exact absurd hx List.not_mem_nil
  have hcontra := tropicalCycle_infeasible hwalk hsat hend
  have hprod : ((capsToEdges u caps ++ [⟨w, u, A / B, true⟩] : List TEdge).map TEdge.c).prod
      = (caps.map Prod.snd).prod * (A / B) := by
    simp [List.map_append, List.prod_append, capsToEdges_map_c]
  have hle : ((capsToEdges u caps ++ [⟨w, u, A / B, true⟩] : List TEdge).map TEdge.c).prod
      ≤ 1 := by
    have key : (caps.map Prod.snd).prod * (A / B) = A * (caps.map Prod.snd).prod / B := by ring
    rw [hprod, key]
    exact (div_le_iff₀ hB).mpr (by rw [one_mul]; exact hdatum)
  have hstrict : (((capsToEdges u caps ++ [⟨w, u, A / B, true⟩] : List TEdge).map
      TEdge.strict).any id) = true := by
    simp
  refine hcontra ?_
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hstrict⟩

#print axioms composedCap_as_instance

/-! ## 7. Corollary (d): the U-table's two-cycle criterion is the same theorem -/

/-- **The 2-cycle engine (the tropical form of `Fresh.UClosure.twoCycle_contra`).**  Two
opposite edges at positive readings — `ρi/ρj ≤(<) c` and `ρj/ρi ≤(<) d` — are incompatible
exactly when `c·d < 1` or `= 1` with a strict side: the cycle at `i` through `j`. -/
theorem twoCycle_engine {ρi ρj : ℝ} (hi : (0 : ℝ) < ρi) (hj : (0 : ℝ) < ρj)
    {c d : ℝ} {s t : Bool}
    (hcap : RHolds s (ρi / ρj) c) (hdem : RHolds t (ρj / ρi) d) :
    ¬ ((c * d < 1) ∨ (c * d = 1 ∧ (s = true ∨ t = true))) := by
  have r0 : (fun k : Fin 7 => if k = 0 then ρi else ρj) 0 = ρi := by simp
  have r1 : (fun k : Fin 7 => if k = 0 then ρi else ρj) 1 = ρj := by simp
  have hw : WalkFrom 0 [⟨0, 1, c, s⟩, ⟨1, 0, d, t⟩] 0 :=
    WalkFrom.cons 0 ⟨0, 1, c, s⟩ [⟨1, 0, d, t⟩] 0 rfl
      (WalkFrom.cons 1 ⟨1, 0, d, t⟩ [] 0 rfl (WalkFrom.nil 0))
  have hsat : ∀ (x : TEdge), x ∈ ([⟨0, 1, c, s⟩, ⟨1, 0, d, t⟩] : List TEdge) →
      EdgeSat (fun k : Fin 7 => if k = 0 then ρi else ρj) x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · show RHolds s
        ((fun k : Fin 7 => if k = 0 then ρi else ρj) 0 /
          (fun k : Fin 7 => if k = 0 then ρi else ρj) 1) c
      rw [r0, r1]
      exact hcap
    · rcases hx with rfl | hx
      · show RHolds t
          ((fun k : Fin 7 => if k = 0 then ρi else ρj) 1 /
            (fun k : Fin 7 => if k = 0 then ρi else ρj) 0) d
        rw [r0, r1]
        exact hdem
      · exact absurd hx List.not_mem_nil
  have hend : ∀ (x : TEdge), x ∈ ([⟨0, 1, c, s⟩, ⟨1, 0, d, t⟩] : List TEdge) →
      0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) x.a ∧
        0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) x.b := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · show 0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) 0 ∧
        0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) 1
      rw [r0, r1]
      exact ⟨hi, hj⟩
    · rcases hx with rfl | hx
      · show 0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) 1 ∧
          0 < (fun k : Fin 7 => if k = 0 then ρi else ρj) 0
        rw [r0, r1]
        exact ⟨hj, hi⟩
      · exact absurd hx List.not_mem_nil
  have hcontra := tropicalCycle_infeasible hw hsat hend
  have hprod : ((([⟨0, 1, c, s⟩, ⟨1, 0, d, t⟩] : List TEdge).map TEdge.c)).prod = c * d := by
    simp
  have hflag : ((([⟨0, 1, c, s⟩, ⟨1, 0, d, t⟩] : List TEdge).map TEdge.strict).any id)
      = (s || t) := by
    simp
  rw [hprod, hflag] at hcontra
  simpa only [Bool.or_eq_true] using hcontra

#print axioms twoCycle_engine

/-- **`Fresh.UClosureKill.twoCycle_contra` recovered as the instance over the U-table's
implied bounds.**  The back-checked pair's stored bound `ρj/ρi ≤(<) d` and added bound
`ρi/ρj ≤(<) c` (rational weights) are the two cycle edges; the rejection test
`d·c < 1 ∨ d·c = 1 ∧ (s ∨ t)` is exactly the bad-cycle predicate.  (Correspondence, not
new mathematics: the U-table ACCUMULATES tightest implied bounds — `uAdd`/`uProp` are
Bellman-Ford relaxation steps — so the U-table closure is the converse direction's
algorithm running as data; `kill_sound` is its fixpoint form.) -/
theorem uClosure_twoCycle_as_instance {ρi ρj : ℝ} (hi : (0 : ℝ) < ρi) (hj : (0 : ℝ) < ρj)
    {d c : ℚ} (hd : 0 < d) (hc : 0 < c) {t s : Bool}
    (h1 : Fresh.UClosure.BHolds t (ρj / ρi) d) (h2 : Fresh.UClosure.BHolds s (ρi / ρj) c) :
    ¬ ((d * c : ℚ) < 1 ∨ ((d * c : ℚ) = 1 ∧ (s = true ∨ t = true))) := by
  have hc' : RHolds s (ρi / ρj) (c : ℝ) := by
    cases s <;> simp only [RHolds] <;> exact_mod_cast h2
  have hd' : RHolds t (ρj / ρi) (d : ℝ) := by
    cases t <;> simp only [RHolds] <;> exact_mod_cast h1
  have key := twoCycle_engine hi hj hc' hd'
  rintro (hlt | ⟨heq, hst⟩)
  · have h2' : ((d * c : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := Rat.cast_lt.mpr hlt
    rw [Rat.cast_mul, Rat.cast_one, mul_comm] at h2'
    exact key (Or.inl h2')
  · have h2' : ((d * c : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [Rat.cast_one]
      exact_mod_cast heq
    rw [Rat.cast_mul, Rat.cast_one, mul_comm] at h2'
    refine key (Or.inr ⟨h2', ?_⟩)
    cases hst with
    | inl h => rw [h]; simp
    | inr h => rw [h]; simp

#print axioms uClosure_twoCycle_as_instance

/-! ## 8. Corollary (c): the equality case is the tangency — the pinch observation

COMMENT-LEVEL corollary (`pinch_as_observation`; nothing to prove beyond the definition of
the bad cycle).  The criterion's equality case — cycle product EXACTLY 1 carrying a
strict edge — is the tangency (the pinch certificate's plane).  Concretely: on the
tangency plane of a lap pair `(a, b)`, `ρ₇/ρ₅ = (8a+1)/(8b+1)`
(`Fresh.PinchCert.TangentPlane`; the h₃ case `a = 11, b = 3` is `Fresh.PinchCert.PlaneH3`,
`25ρ₇ = 89ρ₅`), the exit-edge demand cycle through the two lap readings has product
exactly `(8a+1)/(8b+1) · (8b+1)/(8a+1) = 1` while one side is strict — so the two zones
die together at the pinch point `R* = (8b+1)/ρ₅ = (8a+1)/ρ₇` and nowhere else: the pinch
certificate's straddler mechanism is the criterion's boundary case, and the plane region
certificate `Fresh.PinchCert.pinchIntCert_of_dyadic_h3` is a decidable test of exactly the
`∏ = 1` strip.  The E838 "demanded-ratio products crossing 1" identification is this
theorem read from the data side; the composed binding-path products of the midbound
campaign (e.g. `86989/3565 = (129/15)(17/23)(17/31)(49/7)`, `midbound_plan_v1.out` line
30) are cycle-weight products in the criterion's sense — each is the `walk_telescope`
product of a binding path, and infeasibility fires exactly when such a product crosses 1
(strict side carried). -/

end Fresh.TropicalCycle
