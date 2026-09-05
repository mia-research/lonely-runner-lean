# RESULT: the registered D2 Lang-torsor realization is Frobenius-trivial

Date: 2026-08-09. Script: `d2_lang_rationality_gate_v1.py`.

## Gate question

The D2 preregistration starts from the D1 divisor class

`Q(P) = [P^+ - P^-]`,

on `C: w^4 = x^3 + 7`, where
`P^+ = (x_P, sqrt(y_P))` and `P^- = (x_P, -sqrt(y_P))`.
It then proposes applying the arithmetic Lang map `F - 1` before evaluating a
formal-group logarithm.

For every liftable D1 point in this construction, both `P^+` and `P^-` have
coordinates in `F_p`. Arithmetic Frobenius therefore fixes them term by term:

`F(P^+) = P^+` and `F(P^-) = P^-`.

Consequently,

`(F - 1)([P^+ - P^-]) = 0`

as a divisor class. This is an exact object-level obstruction, not a numerical
small-prime null.

## Exact run

| p | #E(F_p) | liftable points | Frobenius-fixed | Lang-zero |
|---:|---:|---:|---:|---:|
| 13 | 7 | 0 | 0 | 0 |
| 43 | 31 | 15 | 15 | 15 |
| 67 | 79 | 39 | 39 | 39 |
| 79 | 67 | 33 | 33 | 33 |
| 163 | 139 | 69 | 69 | 69 |
| 349 | 313 | 138 | 138 | 138 |
| 433 | 397 | 210 | 210 | 210 |

The script uses exhaustive integer enumeration of the affine points and exact
modular exponentiation. All rows satisfy the gate assertions.

## Consequence for the preregistered arms

Arms 0/A/B are **not scored** for this realization. There is no nonzero
Lang-twisted coordinate on which to measure convergence or public-coefficient
affinity. Reporting this as an affinity null would be incorrect: the proposed
input to the statistic is identically zero.

## What remains live

This does not disprove every possible D2 construction. It shows that the
registered construction cannot apply the arithmetic Lang map directly to the
`F_p`-rational D1 lift. A nontrivial follow-up would need to define, before
measurement, one of:

- a genuine `p`-adic Hensel lift into a specified formal-group kernel;
- a point over an explicit extension field with a specified Frobenius action;
- an explicit crystalline/Dieudonne-module map and its coordinate back to a
  point-local observable.

Until one of those maps is specified, there is no reproducible non-affine
point-local D2 statistic to run. The existing D1 non-affinity result remains
separate and unchanged.
