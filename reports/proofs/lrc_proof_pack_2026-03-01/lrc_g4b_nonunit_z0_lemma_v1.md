# G4B Non-Unit z=0 Lemma (Leave-Based) v2
Date: 2026-03-05
Status: OPEN-PROGRESS (finite-window certified; analytic existential core formalized)

## 0) Purpose
Replace the draft `Enter_e`-based NZ0 criterion with the correct `Leave_e` event object and isolate the theorem-grade analytic target for composite Gap-4.

This note does three things:
1. Corrects event-local objects and NZ0 checklist definitions.
2. States and proves a theorem-grade **existential** pure non-unit exit lemma.
3. Separates mixed exits into unit-branch routing (not NZ0 blocker).

---

## 1) Scope Lock (`S-G4B-NZ0`)

Work in Gap-4 composite regime:

1. `n >= 6` composite.
2. Case-2 tuple `E` with `|E| = n-1`, `E_div != emptyset`, `gcd(E)=1`.
3. `L > 2n`.
4. `B_div` component decomposition as in `lrc_gap4_complementarity_theorem_track_v1.md`.
5. Obstruction on `B_div` uses
   - `U(b) = union_{e in E_non} B_e(b)`,
   - `D(b) = n - |U(b)|`.

Let `R=[u,v]` be a maximal obstruction run in one `B_div` component with `v < b_hi` (interior end).
Define:
- `b_last := v` (last obstructed fiber, `D(b_last)=0`),
- `b_exit := next fiber in component` (first safe fiber, `D(b_exit)>=1`).

---

## 2) Correct Local Objects at Exit

For any runner `e`:

- `Leave_e(b_exit) := B_e(b_last) \\ B_e(b_exit)`
- `Enter_e(b_exit) := B_e(b_exit) \\ B_e(b_last)`
- `U_{-e}(b_exit) := union_{f in E_non, f!=e} B_f(b_exit)`

The event-local deficit witness is inherently a **leave** object at run exit.

---

## 3) Exit Partition (Causative)

Let `E_unit = {e in E_non : gcd(e,n)=1}` and `E_nu = E_non \\ E_unit`.

Define causative leave sets at `b_exit`:
- `UnitLeave := {u in E_unit : Leave_u(b_exit) != emptyset}`
- `NuLeave   := {e in E_nu   : Leave_e(b_exit) != emptyset}`

Use these event classes:
- `unit_only`: `UnitLeave != emptyset` and `NuLeave = emptyset`
- `nu_only_pos`: `UnitLeave = emptyset` and `NuLeave != emptyset`
- `mixed`: `UnitLeave != emptyset` and `NuLeave != emptyset`
- `nu_only_empty`: non-unit z=0 candidates exist but `NuLeave=emptyset`
- `other`: none of the above (out of NZ0 scope)

For NZ0, only `nu_only_pos` is in denominator.

---

## 4) Correct ELDC Criterion (`ELDC-LEAVE-NZ0`)

For runner `e` at an exit:

`ELDC-LEAVE(e,b_exit)` iff `exists r in Leave_e(b_exit)` with `r notin U_{-e}(b_exit)`.

Immediate implication:
- `ELDC-LEAVE(e,b_exit) => D(b_exit) >= 1`.

Proof: witness `r` is not covered by `e` (left) nor by others (`U_{-e}`), hence `r notin U(b_exit)`.

---

## 5) Theorem (Analytic Core): `NZ0-Pure-Existential`

### Statement

Assume an interior run exit `b_last -> b_exit` is `nu_only_pos`:
- `UnitLeave = emptyset`,
- `NuLeave != emptyset`,
- `D(b_last)=0`, `D(b_exit)>=1`.

Then there exists at least one non-unit runner `e in NuLeave` such that

`exists r in Leave_e(b_exit)` with `r notin U_{-e}(b_exit)`.

Equivalently: a causative non-unit leave witness always exists on pure non-unit exits.

### Proof

1. Since `D(b_exit)>=1`, choose `r*` with `r* notin U(b_exit)`.
2. Since `D(b_last)=0`, `r* in U(b_last)`.
3. Suppose `r*` was covered by some unit `u` at `b_last`. Because `UnitLeave=emptyset`,
   `B_u(b_last) subseteq B_u(b_exit)`, so `r* in B_u(b_exit) subseteq U(b_exit)`, contradiction.
4. Therefore `r*` is covered at `b_last` by at least one non-unit runner `e`.
5. As `r* notin U(b_exit)`, in particular `r* notin B_e(b_exit)`. With `r* in B_e(b_last)`, we get
   `r* in Leave_e(b_exit)`.
6. Also `r* notin U(b_exit)` implies `r* notin U_{-e}(b_exit)`.

So `ELDC-LEAVE(e,b_exit)` holds for that non-unit `e`. QED.

---

## 6) Mixed-Event Routing Lemma

### Statement (`NZ0-Unit-Routing`)

Assume an interior exit `b_last -> b_exit` in the declared Gap-4 scope and suppose

`UnitLeave != emptyset`.

Then the exit belongs to one of the two classes:
- `unit_only`,
- `mixed`.

In either case, the exit is **not** an NZ0 obligation. It is routed to the unit branch, and no separate non-unit existential witness is required for closure of that event.

Equivalently: the NZ0 theorem burden is restricted to the pure non-unit class `nu_only_pos`.

### Proof

By definition of the exit classes:
- if `UnitLeave != emptyset` and `NuLeave = emptyset`, the exit is `unit_only`;
- if `UnitLeave != emptyset` and `NuLeave != emptyset`, the exit is `mixed`.

So `UnitLeave != emptyset` implies the exit is in `unit_only union mixed`.
These classes are excluded from the NZ0 denominator by construction: the NZ0 denominator consists only of `nu_only_pos` exits together with `e in NuLeave`.

For `unit_only` and `mixed` exits, the required safe-opening conclusion is supplied by the unit-branch theorem machinery already recorded in the Gap-4 theorem track; therefore no additional non-unit existential witness is needed in the NZ0 branch. QED.

### Status

`PROVED-UNDER-H` relative to the existing unit-branch theorem package in the declared Gap-4 scope.

---

## 7) Certification Mapping

Finite-window certs should report two layers explicitly:

1. **Event layer** (interior exits): class counts (`unit_only`, `nu_only_pos`, `mixed`, ...).
2. **Denominator layer** (NZ0 cert): all `(exit,e)` candidate pairs with exit class `nu_only_pos` and `e in NuLeave`.

Current certified evidence (proof-pack v2):
- scope `n in {6,8}`,
- denominator `243` candidate pairs over `234` `nu_only_pos` exits,
- pass `243/243`, fail `0`.

This is `CERTIFIED-FINITE-WINDOW`, not theorem-grade for all `n`.

---

## 8) Updated NZ0 Checklist (`NZ0.C*`)

- `NZ0.C1` Event extraction:
  - extract maximal obstruction runs and interior exits `(b_last,b_exit)`.
- `NZ0.C2` Exit partition:
  - classify each interior exit using `UnitLeave/NuLeave`.
- `NZ0.C3` Leave-set correctness:
  - compute `Leave_e(b_exit)=B_e(b_last)\\B_e(b_exit)` exactly.
- `NZ0.C4` Background union correctness:
  - compute `U_{-e}(b_exit)` exactly.
- `NZ0.C5` Witness check:
  - denominator: all `(exit,e)` with class `nu_only_pos` and `e in NuLeave`.
  - require `exists r in Leave_e \\ U_{-e}`.
- `NZ0.C6` Implication check:
  - verify witness implies `D(b_exit)>=1`.
- `NZ0.C7` Boundary separation:
  - exclude `at_B_div_end` exits from NZ0.
- `NZ0.C8` Artifacts:
  - emit CSV with both event-layer and denominator-layer fields.

---

## 9) Status Mapping

- Finite-window cert pass on updated denominator => `CERTIFIED-FINITE-WINDOW`.
- Theorem-grade promotion requires extending §5 existential proof from scoped cert windows to declared global scope.
- After promotion + mixed routing integration, `G4B-COMP-CAP` can advance to `PROVED-UNDER-H` in declared scope.

---

## 10) Dependencies

- `lrc_gap4_complementarity_theorem_track_v1.md`
- `lrc_g4b_nonunit_z0_certifier_v1.py` (v2 all-candidates)
- `lrc_g4b_nonunit_z0_rows_v1.csv`
- `lrc_g4b_nonunit_z0_summary_v1.md`
