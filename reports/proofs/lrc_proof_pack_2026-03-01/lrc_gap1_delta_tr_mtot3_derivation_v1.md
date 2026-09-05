# Gap 1 Reduced `Delta_tr` Derivation on `m_tot<=3` Geometry (v1)
**Date:** 2026-03-03
**Canonical link:** `lrc_ap_grid_extremizer_theorem_sequence_v11.md` §17.19

## Purpose

Provide full derivation details for the reduced-geometry transition reserve used in §17.19,
without overclaiming closure.

## Scope

Prime `n`, one-divisible all-distinct template family, canonical bands `I_lo union I_hi`.
TM2 obstruction is already eliminated in this scope (`§17.16`), and fixed-signature
complexity satisfies `m_tot<=3` (`§17.17`).

## Reduced constants and exact reserve

Let `Pi_fix(I_tot)` be fixed-signature cells on `I_tot` and `m_tot=|Pi_fix(I_tot)|`.
Define

- `K_loc^sh := 2L0*m_tot`,
- `Delta_tr^sh := |I_tot|/n + K_loc^sh - C_bad(I_tot)`.

Then exactly:

`C_bad(I_tot) = |I_tot|/n + K_loc^sh - Delta_tr^sh`.

This is the reduced-geometry instance of `G1.H.prime.1`.

## Why `Delta_tr^sh >= 0`

From the cell cap in `§17.7`, each fixed-signature cell `C` satisfies

`C_bad(C) <= |C|/n + 2L0`.

Summing over `m_tot` cells:

`C_bad(I_tot) <= |I_tot|/n + 2L0*m_tot = |I_tot|/n + K_loc^sh`.

So by definition, `Delta_tr^sh >= 0`.

## Exact closure criterion and residual

Using `B_safe = |I_tot|-C_bad`:

`B_safe(I_tot) = ((n-1)/n)|I_tot| - K_loc^sh + Delta_tr^sh`.

Hence

`B_safe(I_tot) >= n-1`

iff

`Delta_tr^sh >= K_loc^sh - ( ((n-1)/n)|I_tot| - (n-1) )`.

Define residual

`Xi_tr := max(0, K_loc^sh - ( ((n-1)/n)|I_tot| - (n-1) ) - Delta_tr^sh )`.

Then

`B_safe(I_tot) >= n-1 - Xi_tr`.

So bounded-strip closure is equivalent to proving `Xi_tr=0` uniformly.

## Interpretation

This section does not close Gap 1 by itself. It converts the remaining burden into one explicit
quantity (`Xi_tr`) in the reduced `m_tot<=3` geometry and removes hidden premises.

## Support artifact

The support-only numerical check for this reduced formulation is recorded in:

- `lrc_gap1_delta_tr_mtot3_validation_v1.md`

That artifact is consistency evidence only and not a proof dependency.
