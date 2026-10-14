# Reduce the arrangement first

No `dmin/dmax` estimates, time bound, or covering hypothesis is used here.

## Exactly six continuous factors

Sort the speeds: `w0 < w1 < ... < w7`. Put

`A = w0`, `D = (w7-w0)/7`, `xi = (wi-A)/D`.

Then **every** distinct-speed arrangement has the canonical form

`0 = x0 < x1 < x2 < x3 < x4 < x5 < x6 < x7 = 7`.

The permutation accounts for labels; `A` accounts for common drift; `D>0`
accounts for scale. A normalized time `tau` means physical time `tau/D`.
All pair separations are exactly preserved under that time conversion, for
every subject, not just the slowest one.

Thus `.00001,...,.00008` and `1000000,...,8000000` both reduce to `0,...,7`.
There are six real factors, not eight independent speeds plus arbitrary scale.

Equivalently use consecutive SPEED gaps:

`gi = x(i+1)-xi > 0`, for `i=0,...,6`, with `sum gi = 7`.

Choose `g0,...,g5 > 0` with sum less than seven; the final gap is forced to be
`g6 = 7-sum(g0,...,g5)`. Every pair disparity is a contiguous sum of these gaps.
The AP is simply `g0=...=g6=1`.

Or use AP deviations `ei=xi-i`: `e0=e7=0` and
`e(i+1)-ei > -1`. The six interior deviations are coupled by ordering, rather
than seven unrelated reading errors.

Speeding a runner past its neighbour changes its rank. Sorting removes the
redundant labelling, but does not identify different resulting gap vectors.
The input domain is bounded and finite-dimensional, still continuous.

## A finite symbolic reference-grid structure

At reference class `c in {1,3,5,7}`, normalized time is `c/8`, and a positive
pair separation in eighths is `c*(xj-xi)`, between zero and 49. Its integer grid
label therefore has only fifty possibilities. The residue mod 8 and whether
the position is exactly an integer determine clearance at that reference instant.
Equality flags are essential because distance exactly `1/8` counts as clear.

All reference changes lie on the affine walls

`xj-xi = q/c`, where `0 < q/c < 7`.

There are **90 distinct rational levels**: six integers, 14 additional thirds,
28 additional fifths, and 42 additional sevenths. In the six interior variables
the unique wall forms are

- `xi = level`: six coordinate forms;
- `xj-xi = level`: fifteen internal-pair forms.

The endpoint-to-endpoint difference is fixed. Walls from the top endpoint are
duplicates, since `7-level` is another level. Thus there are **1,890 distinct
reference hyperplanes**, not 1,890 arrangements. They define finitely many open
regions and boundary faces, with constant reference-grid decisions on each face.
This is a symbolic description, not an enumeration of speed configurations.

## What this reduction does and does not discard

Common drift, overall scale and runner labels are redundant and are removed
exactly. Individual whole-lap indices are not generally redundant when time
changes: readings 1 and 9 agree modulo eight at time `1/8`, but not at time `1/16`.
We therefore keep the six actual gap factors as the underlying state and use
the finite residue labels for the reference decisions only.

## Symbolic cascade in the same six factors

The six factors are fixed throughout a run; the cascade changes the time and
the grid readings, not the speed arrangement. For a chosen subject, write each
positive disparity as its appropriate contiguous gap sum `H_i`.

At setter `a`'s lap-`K` opening, reading `b` is captured on lap `L` exactly when

`(8L-1)*H_a < (8K+1)*H_b < (8L+1)*H_a`.

Since each `H` is a linear gap sum, these are **linear inequalities in the same
six factors** once the runner identities and laps are specified. No additional
independent continuous variables appear as the cascade grows. The exact capture
equivalence is already proved in `HandoffDriftN.captured_iff_linear`.

Thus the analytical task can be conducted using linear conditions on one fixed
six-factor domain. No claim is made yet that two arrangements
in the same reference cell have identical later cascade histories, or that the
four reference instants alone must isolate every subject. No lower bound on a
speed gap, upper bound on a disparity ratio, or bound on the witness time has
been assumed; those questions are deferred as requested.

## Lean and reproduction

`LRC/Spec/ArrangementShapeN.lean` proves sorting by a permutation, existence of
the normalized shape, exact isolation transport, positive gaps summing to seven,
determination by six interior coordinates, bounded reference labels, and an
**equivalence** between the original per-runner problem and this shape problem.

The finite hyperplane count is checked separately by exact rational symbolic
deduplication in the Python script; that count is not a Lean theorem.

```sh
python3 experiments/nN/redo/arrangement_shape_symbolic_v1.py --test
python3 experiments/nN/redo/arrangement_shape_symbolic_v1.py
lake build LonelyRunner.LRC.Spec.ArrangementShapeN
lake env lean experiments/nN/arrangement_shape_axioms_v1.lean
```
