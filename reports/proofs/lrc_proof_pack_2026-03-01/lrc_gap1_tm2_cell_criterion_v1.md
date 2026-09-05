# Gap 1 TM2 Cell Criterion and Obstruction Class
**Date:** 2026-03-03

## Purpose

Record the exact cell-level criterion for TM 2-miss validity on canonical bands and define the
explicit obstruction class used by the G1.H occupancy route.

## Setting

- Prime `n`.
- One-divisible all-distinct template `F in F_n`.
- Admissible `M` with `gcd(M,nL0(F))=1`.
- Event-cell partition `Pi(F,M)` on `I_tot=I_lo union I_hi`.

For each cell `C in Pi(F,M)`:

- fixed signatures are constant,
- `U_fix(C)` is the fixed bad-`a` union,
- `R_fix(C)=Z_n \ U_fix(C)`,
- `r(C)=|R_fix(C)|`.

Define

`O_tm2(F,M) := { C in Pi(F,M) : r(C) != 2 }`.

## Exact criterion

1. Cell-level TM2 validity is exactly `r(C)=2`.
2. For fixed `(F,M)`, canonical-band TM2 validity on all cells is equivalent to
   `O_tm2(F,M)=empty`.
3. For template `F`, universal TM2 validity is equivalent to
   `(forall allowed M): O_tm2(F,M)=empty`.

So if TM2 fails, the precise obstruction object is `O_tm2(F,M)`; there is no hidden extra premise.

## Relation to G1.H

G1.H now includes an explicit obstruction surcharge

`E_tm2(F,M) = sum_{C in O_tm2(F,M)} |C|`

in the global bad-count inequality. This makes the remaining TM2 burden measurable and explicit.

## Scope

This note isolates structure; it does not prove `O_tm2(F,M)=empty` globally.
