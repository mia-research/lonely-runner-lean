# Audit: independent joint-set `xy` run and control correction

Date: 2026-08-09. Scope: the two-point addition-coupled probe in
`joint_set_xy_probe_v1.py`. This is an audit record, not a new theorem and not an
ECDLP claim.

## What was run

The repository script was executed unchanged on its declared ladder:

| p | n | coupled x `max|B|/n` | coupled `xy` all legs | coupled `xy` on sum leg |
|---:|---:|---:|---:|---:|
| 127 | 127 | 2.818 | 3.987 | 3.507 |
| 349 | 313 | 3.544 | 3.761 | 3.568 |
| 733 | 691 | 3.871 | 3.692 | 4.373 |

The script's second printed column is the additional normalization by `n`. For
the coupled `xy`-all-leg channel those values were `0.0314`, `0.0120`, and
`0.00534`; for the sum-leg channel they were `0.0276`, `0.0114`, and `0.00633`.

The planted rank-1 control returned approximately `1.00`, `0.30`, `1.00`, and
`0.30` in its strong and weak versions at all three rows. The detector therefore
responded to the declared additive plant.

## Control defect found

The nominal factoring baseline is not literally factored in the repository
implementation. `Bmax` sets `fS[0] = 0` even when `bS = cS = 0`. Thus the
sum-leg factor is the constant function with the identity point removed, rather
than the constant function. This changes the baseline slightly because pairs
with `dP + dQ = 0` are removed.

I reran the baseline independently with `fS[0] = 1`, leaving the point-local
coupled channels unchanged:

| p | n | corrected factored baseline | corrected baseline / n | old baseline / n |
|---:|---:|---:|---:|---:|
| 127 | 127 | 4.364 | 0.03436 | 0.03439 |
| 349 | 313 | 5.040 | 0.01610 | 0.01623 |
| 733 | 691 | 6.705 | 0.00970 | 0.00967 |

The defect is small for these rows and does not reverse the observed ordering,
but the original baseline must not be described as an exact factorization
control without this qualification.

## Scoped reading

At `n = 127, 313, 691`, the tested point-local `x` and `xy` addition couplings
show no rank-1/additive spectral spike. Their normalized maxima decrease across
the ladder, while the planted additive control remains visible. This is a
scoped null for this statistic and this small-prime ladder.

It does not test:

- multiplicative or pairing-like bilinear structure;
- the GLV/lattice aperture channel;
- a transfer into `A_new`;
- the uniform geometric-monodromy explanation of the nonzero twists;
- secp-scale enumeration.

## A_new extension attempt

I attempted to extend the exact cyclotomic discriminant test to `p = 79` using
the repository verifier. The loader first reran the existing `p = 13, 43, 67`
cases and then stalled during the second square test at `p = 67`; it was
interrupted before reaching `p = 79`. No new `p = 79` claim is made.

The existing repository result remains the relevant scoped statement: the
nonzero twisted eigenvalue test is non-abelian at `p = 43, 67`, with a small
`p = 13` exception. Extending that result requires a more efficient exact
discriminant test or a bounded prime list, not a heuristic replacement.

## Next high-value test

The next genuinely new experiment should use a preregistered, non-affine
point-local readout that is explicitly tied to the `A_new` Lang-torsor twist,
rather than another complete-sum marginal. The two-point probe above is a
useful ordinary-curve control for additive coupling, but it cannot decide that
twisted bridge question by itself.
