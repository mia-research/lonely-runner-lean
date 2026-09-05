# RESULT: the nontrivial extension-field Lang action is only `-2Q`

Date: 2026-08-09. Script: `d2_lang_antifrobenius_v1.py`.

## Corrected object

For the D1 cover `C: w^4 = x^3 + 7`, define

`Q(P) = [P^+ - P^-]`,

where `P^+ = (x_P, sqrt(y_P))` and `P^- = (x_P, -sqrt(y_P))`.

The original D2 realization used only the half for which `sqrt(y_P)` lies in
`F_p`. That half is Lang-trivial. The natural extension is to include the
other half over `F_{p^2}`.

## Exact Frobenius split

If `chi_2(y_P) = +1`, then `P^+` and `P^-` are individually fixed by
Frobenius, so

`F(Q(P)) = Q(P)` and `(F - 1)Q(P) = 0`.

If `chi_2(y_P) = -1`, Frobenius sends `sqrt(y_P)` to `-sqrt(y_P)`, hence swaps
the two points. Therefore

`F(Q(P)) = -Q(P)` and `(F - 1)Q(P) = -2Q(P)`.

This is exact before any Jacobian arithmetic or discrete logarithm.

| p | #E(F_p) | F_p-rational half | nonresidue half |
|---:|---:|---:|---:|
| 43 | 31 | 15 | 15 |
| 67 | 79 | 39 | 39 |
| 79 | 67 | 33 | 33 |
| 163 | 139 | 69 | 69 |
| 349 | 313 | 138 | 174 |
| 433 | 397 | 210 | 186 |

For the secp-relevant branch `p = 3 mod 4`, the counts are equal because
`P -> -P` flips the quadratic character of `y`. In the `p = 1 mod 4`
cross-checks, `chi_2(-1) = +1`, so equality is not forced. The Frobenius
classification itself is pointwise and exact in every row.

## Consequence

The extension-field repair does not produce a new nonlinear point-local
coordinate. It produces the piecewise group operation

`Q -> 0` or `Q -> -2Q`,

selected by the quadratic character of `y_P`. Any group logarithm on the same
cyclic component consequently transforms as

`ell(Q) -> 0` or `-2 ell(Q)`.

Thus it cannot turn the D1 non-affine scalar map into a public affine map. It
is a precise negative result about this repaired Lang realization, not a null
about all possible `A_new` correspondences.

## Where effort should go next

The remaining D2 object is genuinely sheaf/crystalline rather than a point map:
the Lang-torsor twist in `V(a)` must be studied through its Frobenius local
system or an explicitly defined Dieudonne-module coordinate. A new point-local
experiment would need a different correspondence, not another application of
`F - 1` to the D1 divisor.
