# Master Problem 1 Branch Integration Note (v1)
**Date:** 2026-03-07  
**Purpose:** start the theorem-writing program for Master Problem 1 by formalizing the interior-exit partition used in `G4B-Branch-Closure`.

## 0) Scope
Work in the composite Gap-4 regime:
- composite `n >= 6`,
- Case-2 tuple `E` with `|E|=n-1`, `E_div != emptyset`, `gcd(E)=1`,
- `L > 2n`,
- one `B_div` component `C`,
- maximal obstruction run `R=[u,v] subset C`,
- interior exit `b_last := v`, `b_exit := next fiber in C`, with
  - `D(b_last)=0`,
  - `D(b_exit)>=1`.

Adopt the leave-based objects from `lrc_g4b_nonunit_z0_lemma_v1.md`:
- `Leave_e(b_exit) := B_e(b_last) \\ B_e(b_exit)`,
- `UnitLeave := {u : gcd(u,n)=1 and Leave_u(b_exit) != emptyset}`,
- `NuLeave := {e : gcd(e,n)>1 and Leave_e(b_exit) != emptyset}`.

## 1) Lemma MP1.1 — Any genuine interior exit has a causative leave

### Statement
For every genuine interior exit `b_last -> b_exit`, there exists at least one runner `e in E_non` such that

`Leave_e(b_exit) != emptyset`.

Equivalently:

`UnitLeave union NuLeave != emptyset`.

### Proof
Since `D(b_exit)>=1`, choose `r* in Z_n` with `r* notin U(b_exit)`.
Because `D(b_last)=0`, we have `U(b_last)=Z_n`, so `r* in U(b_last)`.
Hence there exists some runner `e in E_non` with

`r* in B_e(b_last)` and `r* notin B_e(b_exit)`.

Therefore `r* in Leave_e(b_exit)`, so `Leave_e(b_exit) != emptyset`.
Thus at least one of `UnitLeave`, `NuLeave` is non-empty. QED.

### Status
`PROVED` in the declared exit-local scope.

---

## 2) Lemma MP1.2 — Exhaustive interior exit partition

### Statement
Every genuine interior exit `b_last -> b_exit` falls into exactly one of the three classes:
- `unit_only`,
- `nu_only_pos`,
- `mixed`.

No fourth causative class is needed for theorem-grade branch integration.

### Proof
By Lemma MP1.1, `UnitLeave union NuLeave != emptyset`.
There are only three mutually exclusive possibilities for the pair of truth values

`(UnitLeave != emptyset, NuLeave != emptyset)`:

1. `(1,0)`  -> `unit_only`,
2. `(0,1)`  -> `nu_only_pos`,
3. `(1,1)`  -> `mixed`.

These classes are pairwise disjoint by definition and exhaustive because `(0,0)` is impossible by Lemma MP1.1. QED.

### Corollary
The earlier bookkeeping label `nu_only_empty` is not a genuine exit class for branch-integration purposes; it may occur as a candidate-screen artifact, but not as a causative class of a true safe-opening exit.

### Status
`PROVED` in the declared exit-local scope.

---

## 3) Routing consequence for `G4B`

With Lemma MP1.2 in hand, every interior exit belongs to one of:
- `nu_only_pos`, handled by `NZ0-Pure-Existential`,
- `unit_only`, routed to the unit branch,
- `mixed`, also routed to the unit branch (NZ0 not required).

### Lemma MP1.4 — Unit/mixed routing

Assume the existing unit-branch theorem package in the declared Gap-4 scope.
Then every interior exit with `UnitLeave != emptyset` is routed out of the NZ0 branch and into the unit branch.

Proof:
This is exactly `NZ0-Unit-Routing` from `lrc_g4b_nonunit_z0_lemma_v1.md`.
By Lemma MP1.2, such an exit is either `unit_only` or `mixed`; by `NZ0-Unit-Routing`, both classes are handled by the unit branch and require no separate non-unit existential witness. QED.

### Status
`PROVED-UNDER-H`.

So the event-local theorem burden for `G4B` reduces to:
1. cite the final `NZ0-Pure-Existential` theorem for `nu_only_pos`,
2. cite `NZ0-Unit-Routing` for `unit_only` and `mixed`,
3. isolate the remaining non-event blocker as the component safe-fiber budget.

This compresses the old `G4B` bottleneck:
- exit partition completeness is no longer open,
- genuine residual work is aggregation, not local event taxonomy.

---

## 4) Remaining open integration items

### MP1.6 — run-end coverage theorem

#### Statement
Let `R=[u,v]` be a maximal obstruction run in a `B_div` component `C`.
Then exactly one of the following holds:

1. `v = b_hi(C)` and the run is handled by the boundary branch;
2. `v < b_hi(C)` and the next fiber `b_exit` is an interior exit belonging to exactly one of
   `nu_only_pos`, `mixed`, `unit_only`.

Moreover, in case (2), the exit is theorem-controlled:
- `nu_only_pos` is handled by `NZ0-Pure-Existential`,
- `mixed` and `unit_only` are handled by `NZ0-Unit-Routing`.

So every maximal obstruction run ends at a theorem-controlled safe opening, except for the already-separated boundary-ending case.

#### Proof
If `v = b_hi(C)`, we are in the boundary branch by definition.
Otherwise `v < b_hi(C)` and, since `R` is maximal, the next fiber `b_exit` in `C` satisfies `D(b_exit)>=1`; thus `b_last := v` and `b_exit` form a genuine interior exit.

By Lemma MP1.2, this interior exit belongs to exactly one of
`nu_only_pos`, `mixed`, `unit_only`.
If it is `nu_only_pos`, the safe-opening conclusion is supplied by `NZ0-Pure-Existential`.
If `UnitLeave != emptyset`, the exit is `mixed` or `unit_only`, and the safe-opening conclusion is supplied by Lemma MP1.4 (`NZ0-Unit-Routing`).

Therefore every maximal obstruction run is covered by a theorem-controlled end mechanism: either the boundary branch or one of the three interior exit classes, each already linked to a safe-opening theorem. QED.

#### Status
`PROVED-UNDER-H`.

### MP1.7 — safe-fiber budget
Need a theorem-grade proof that the total safe fibers in `C` are at least `n` in the declared scope.

Once MP1.7 is in place, `G4B-Branch-Closure` becomes a short final deduction.

---

## 5) Artifact linkage
- Exit-local definitions and existential theorem:
  - `lrc_g4b_nonunit_z0_lemma_v1.md`
- Component cap target:
  - `lrc_gap4_complementarity_theorem_track_v1.md`
- Coset local engine:
  - `lrc_g4b_coset_essentiality_v1.md`
- Program-level checklist:
  - `lrc_master_problem1_checklist_v1.md`

## 6) Immediate next theorem-writing move
Isolate the exact theorem still missing for the safe-fiber budget.
