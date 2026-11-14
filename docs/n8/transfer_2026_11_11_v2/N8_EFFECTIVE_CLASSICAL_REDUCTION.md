# Effective finite reduction for classical eight-runner isolation

The [cascade replay](N8_CASCADE_ANCHOR_REPLAY.md) develops a direct
cascade reduction for fixed slow cells and fast directions. It gives
an exact residue-class rule, with rational controls and checked Lean.

The classical reduction uses the seven positive integer disparities of a
chosen runner. The existing real-to-integer bridge returns to arbitrary
real arrangements and to the cascade termination statement.

## An explicit relation bound

Use the order-seven exact merge to obtain a phase (y) on a model
subtorus with each distance at least (1/7). At a point blocked at
(1/8), one coordinate has distance at least (1/56) from the
corresponding coordinate of (y).

On the unit circle, write (z=e^{2\pi i x}). Use the kernel with
Fourier expansion
[
K_N(x)=z^{-N}(1+z)^{2N}/4^N.
]
Its absolute value is at most one. At distance at least (1/56)
from zero, the chord lower bound gives
[
 |K_N(x)|\le (783/784)^N .
]
Take the product in seven coordinates and center it at the merged
phase (y). Its Fourier support lies in the cube ([-N,N]^7).
Since (y) lies on the model subtorus, averaging the translated
kernel there equals averaging the unshifted kernel. All unshifted
coefficients are nonnegative. The constant coefficient alone gives
a model average at least ((2N+1)^{-7}), by the central binomial
coefficient bound.

With (N=100352=784\cdot128), the model lower bound exceeds the
maximum on a blocked trajectory. The proof compares ( (783/784)^{784}
\le 1/2) and (2^{-128} < 200705^{-7}), both with exact arithmetic.
Consequently the model and a trajectory without strict clearance
differ on an exact relation from that explicit cube.

Take all cube relations that vanish on a given integer profile. Their
common rational kernel is a line if the profile has no strict witness.
Six independent rows suffice. The signed minors give an integer
representative, and the existing Hadamard estimate bounds its entries
by ((6\cdot100352)^6=47650086822417979408803447579869184). Dividing
by the gcd preserves this bound and rescales the witness time exactly.

## Which bounded types still need a proof

The older theorems `lonely_eight_or_residual` and
`lonely_eight_or_residual_open` already discharge many primitive sets
by common rational openings, separated blocks, and residue-count
criteria. `Fresh.ExactClassicalResidual` plugs the stronger of those
dispatchers into the explicit finite reduction. The remaining target is
a closed (1/8) witness for each positive primitive set within the
numerical bound that belongs to `OpenResidual`. That predicate retains
both the older `EightResidual` conditions and the surviving residue
conditions. It is a predicate on sets, so it removes ordering and scale
from the terminal obligation.

The numerical bound is far too large to make exhaustive checking
practical. The next research target is a shared witness for the
surviving residue classes. One available ingredient is the quotient
translate rule in `QUOTIENT_TRANSLATE_ENGINE_v1.md`. For readings
divisible by (q), it keeps a lower-order witness fixed under shifts
by (1/q). The remaining readings block dilated intervals of shifts.
The record already shows why counting their sizes alone can fail.
A sharper argument would use intersections or move the lower-order
witness through its clear interval.

A check from the corpus illustrates the importance of allowing the
modulus to vary. The profile ((1,2,32,33,34,35,61)) has no witness on
the (1/128) grid and clears at (33/256). Both were replayed exactly.
This example is already discharged by the older small-resolution rule
in the joined dispatch. The standalone one-multiple theorem in the
original Lean tree is another potential input. It settles every
unique multiple of eight that is not divisible by 32, independently
of the heights of the other readings.

## Lean entry points

- `explicit_character_test` in `ExplicitFourierKernel.lean` checks the cube.
- `explicit_bounded_representative` in `BoundedClassicalProfiles.lean` checks
  the numerical height bound using the earlier determinant estimate.
- `classical_eight_of_bounded_open_residual` in `ExactClassicalResidual.lean`
  discharges the exact merge with order seven and incorporates the
  older arithmetic dispatch. The portable checker builds the first
  two analytic modules. The final bridge uses the repository's
  lower-order and residue-dispatch modules.
