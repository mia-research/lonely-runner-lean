# A finite reduction for classical eight-runner isolation

The [effective classical reduction](N8_EFFECTIVE_CLASSICAL_REDUCTION.md) gives an explicit Fourier cube
and height bound. It incorporates the existing integer dispatch so the
remaining classical obligation is restricted to bounded primitive sets
that survive the arithmetic rules.

For the chosen runner, take the seven positive absolute disparities. The
classical target asks for a positive time with every distance to an integer at
least `1/8`. The older real-to-integer transfer
`LRC.OrderEightN.existenceAt8_of_nat` already reduces this unrestricted-time
target to positive integer disparities.

The new reduction takes the integer problem down to finitely many rational
lines. A positive integer profile either has a time with every distance
strictly greater than `1/8`, or is a positive multiple of one of finitely many
positive integer representatives.

## Why the number of types is finite

1. In a rational space of dimension at least two that contains a positive
   profile, take an integer parameter matrix. Its seven coordinate rows are
   nonzero and some pair is nonparallel. The exact merge in the older tree
   gives an integer direction whose seven evaluations stay nonzero and have
   a repeated absolute value. The checked order-seven theorem then gives
   a phase whose seven distances are at least `1/7`.
2. Use the product of the positive parts of the seven distances minus
   `1/8` as a continuous test function. A fixed-radius ball around the
   merged phase is uniformly clear. A finite cover of the ambient torus
   gives a common positive lower bound for the test function's average on
   every such parameter subgroup. A single finite Fourier approximation
   therefore works at every dimension.
3. For a positive integer profile, take **all** characters from that
   finite support that vanish on it. Their common rational kernel contains
   the profile. On the finite support, the kernel and the profile have the
   same vanishing characters, so the two averages of the test polynomial
   agree. If the kernel has dimension at least two, the merged-phase bound
   forces a strict witness on the profile. Thus a profile without a strict
   witness lies on a line. The finite support has finitely many subsets,
   and each resulting positive line needs one representative because
   scaling its rates rescales time exactly.

## The remaining obligation

`Fresh.ExactClassicalBridge` checks that certifying the finite family
implies classical isolation and termination of the existing cascade
for all positive real difference sets of size at most seven. The reduction
itself uses rational relations and unrestricted time. The separate
two-window claim still has its own obligations.

There is one closed arithmetic certificate for a representative `q`.
Choose a coordinate `b = q[j]` and an integer `0 ≤ k < b`. For every
coordinate `a = q[i]`, check

```text
b ≤ a*(8*k+1) mod (8*b) ≤ 7*b.
```

This is equivalent to a weak witness and gives time `(8*k+1)/(8*b)`.
The non-strict endpoints are essential. Exact rational interval
intersection over one period for `(1,2,3,4,5,6,7)`,
`(1,2,3,4,5,7,12)`, and `(1,4,5,6,7,11,13)` gave precisely
`1/8, 3/8, 5/8, 7/8`, each with minimum distance exactly `1/8`.

The qualitative construction below gives one representative per line.
The effective follow-up bounds the characters and the representative heights,
and restricts the terminal obligation to the older arithmetic residual.

## Lean entry points

- `Fresh.UniformPhaseAverage.uniform_phase_average` gives the common
  lower bound from a finite cover.
- `Fresh.ExactClassicalReduction.finite_integer_profiles` is the finite
  reduction, taking the strict merged phase with margin `1/7` as its only
  additional input.
- `Fresh.ExactClassicalBridge.classical_eight_of_finite_certificates`
  discharges that input using the existing exact merge and order-seven
  theorem, then connects the remaining finite obligation to the real
  target and the cascade.

The portable Lean checker builds the analytic reduction. The bridge
source accompanies it as a reference. To compile the bridge, use the
repository's lower-order Lean dependencies from `Fresh.Nv_RealEightN`
and `Fresh.DistIntFract`.
