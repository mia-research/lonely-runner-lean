> **EXTENDED by `RESULT_eps_to_d_constraint_v2.md`** — v1 tested one map; v2 ran the frozen 31-map
> family + joint omnibus (both scan curves + OOS confirm) and reached a powered FAMILY-WIDE scoped null.
> v1's single-map verdict and the flap-vs-carry gate distinction below both stand.

# RESULT — pre-registered `eps`↔carry test: SCOPED NULL on the frozen maps; and the gate DISTINGUISHES flap-`eps` from carry-`ε`

**Date:** 2026-08-11. **Runs `PREREG_eps_to_d_constraint_v1.md` (frozen) verbatim.** Track 2a′.
**Artifact:** `scratchpad/eps_to_d_run_v1.py` + `scratchpad/eps_to_d_run_v1.log`. Exact int/Fraction
signal path; `check_no_float.sh` = OK; verdict is the integer permutation p-value.

## What was tested (the frozen pre-registered maps only)

Whether the public flap indicator `eps(x)` (function of `x` alone) supplies the d-containing LBE carry:
- **Primary** (two-key): `[eps(x(P_sum)) >= 1] == ε(d1,d2,j)`, `ε=[d1λ^j + d2λ^j >= m]`, on unforced
  ⟨φ⟩-orbit reps; matched control permutes the target within the same `j`-bin (preserves μ3/j forcing).
- **Gate**: `s<3/16 ⇒ ε=0` (carry `ε`).
- **Secondary** `M_c` (single-key): `eps(x([d]G)) == c(d) mod 3`, `c=((-1)^s d0 λ^j − d)/m`.

## Results — `[EMPIRICAL — SCOPED NULL; plant-fired, powered]`

Curves `y²=x³+7`, prime order: `p=547 (m=547)`, `p=907 (m=967)`, `p=1303 (m=1249)`; `d1∈{1,7,13}`;
`p=43 (m=31)` as underpowered plumbing. `B=2000` control draws.

| arm | outcome | evidence |
|---|---|---|
| **Primary `[eps≥1]==ε`** | **NULL** | `M_real ≤ ctrl[95%]` every curve/`d1`; `p_perm` all `> 0.05` (0.07–0.76) |
| **Gate `s<3/16⇒ε=0`** | **FAILS** (no partial payoff) | 21–93 violations per cell (carry `ε`) |
| **Secondary `M_c`** | **NULL** | `M_real = ctrl95` (71/71, 123/123, 155/155); `p_perm=1/1` |

**Plants all behave (verdict admissible):** positive plant `M=U` every curve (comparison pipeline
validated); negative plant within its control; gate-plant 0 violations; **powered** — `U−ctrl[95%] =
51…169 > 0`, so a true full identity (`M_real=U`) would have cleared control by a wide margin. `U` up
to 416 (two-key), 208 (single-key).

**Pre-committed conclusion (§9 row 4):** on the frozen maps, `eps`/`s` do **not** supply the carry
`ε`/`c`. Phrased conditionally: *the public flap `eps(x)` does not equal the LBE carry `ε` (primary),
nor gate it (`s<3/16` fails for `ε`), nor predict `c mod 3` (`M_c`), via the pre-registered maps
`[eps≥1]↔ε` and `eps↔c mod 3`, on `y²=x³+7` at `p∈{547,907,1303}`, `U≤416`, plant fired.*

## The positive by-product (a characterization, not a null)

The gate `s<3/16` **holds exactly for the flap indicator `eps`** (`RESULT_linchpin_s_gate_v2.md`, 0
violations, secp-scale) but **fails for the carry `ε`** (21–93 violations here). The same public
predicate separates the two objects. This is direct evidence that **the public Cap-Law flap `eps(x)`
is NOT the d-containing LBE carry `ε`** — which **falsifies, at this scope, the positive-ledger
assertion that "T2's carry `ε` IS the Cap-Law flap correction,"** and is consistent with XVI.C (the
carry contains `d`; the flap does not). Grade: `[VERIFIED — exact, scope p∈{43,547,907,1303}]`.

## Consequence for XVI.D (recorded straight)

The linchpin gate verified in `RESULT_linchpin_s_gate_v2.md` is a fact about the **public flap**, and
this run shows that flap is **not** the LBE carry. So **the XVI.D route, via `eps`/`s`, does NOT
de-circularize the ARSENAL tools 3/5/7** (they need the carry `c`/`ε`, which the public flap does not
supply) on the tested scope and maps. The linchpin's public-computability result stands; its hoped
payoff (supplying the d-carry) is not delivered by this route here.

## What this does NOT close (do not enlarge the null)

- **Only the frozen maps** `[eps≥1]↔ε`, `eps↔c mod 3`, and the `s<3/16` gate are tested. Other maps
  from the public flap data (`eps==2`, sign-aware flap, s-bands, sextant, joint feature tuple) are
  **untested** — being pre-registered as a corrected family in `PREREG_eps_to_d_constraint_v2` (an
  omnibus association test + a declared map list with Holm correction and fixed-OOS curves). Trying
  alternative maps post-hoc on THIS run would be map-fishing and is not done.
- **Larger `p`** untested (scope banner #5).
- **The OPEN_d2 known-bit-range → partial-carry route (T2c)** is a *different* composition (uses a
  public range constraint on `d0`, not `eps`) and is untouched by this run.

## Owed gates
`experiment-designer` already pre-registered v1 (this run). `citation-verifier` on the Cap-Law inputs
before any grade moves up. `compile-diff` if folded into a master. v2 map-family pre-registration in
progress.
