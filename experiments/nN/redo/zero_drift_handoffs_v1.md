# Zero-drift returns: the other readings and the preservation requirement

## Requirement audit

`LRC.Spec.LonelyRunnerAt8` in `Spec/Target.lean` has the intended quantifiers:
for each runner, there exists its own positive isolation time. It does not require
a simultaneous global isolation event.

The existing deformation theorems do prove preservation on explicit regions:

- `APNbhd.ap_nbhd_exists`: every deviation has magnitude at most `1/32` of the AP gap.
- `GridNbhd.grid_nbhd_exists`: complete residues mod 8, `|e_i| <= rho`, and
  `2*rho*(14*W+21) <= 1`, with `W` bounding integer differences.
- `DoubledNbhd.dd_exists`: deviations at most `1/(512*(m+1))` for its doubled-slot family.

These hypotheses do not amount to preservation under arbitrary deviations. This
is a limit of the existing proofs, not evidence that larger deviations destroy
individual isolation. Writing an arrangement as a deviation and proving its
isolation survives the entire deformation remain different assertions.

The previous pair-drift formula also has a precursor already in the project:
`CoreDriftN.link_offset` and `link_persistence`. The useful new work here is tracing
what the other readings do at actual zero-drift returns and connecting the existing
off-lattice step theorem to repeated blocking roles.

## Targeted exact experiment

From the earlier boundary experiment, choose an observed repeated ordered pair
with lap advances `(r,s)`. Alter the receiving speed to make its ratio to the
source exactly `s/r`. All other speeds are retained; all arithmetic is rational.

- 446 distinct targets, deduplicated by original speeds, pair, and lap advances.
- 133 targets collide speeds and are excluded from the distinct-speed domain.
- 313 valid tests: the targeted pair is absent in 306 resulting cascades, occurs
  once in four, and genuinely returns at zero drift in three.
- All three surviving cases stop after 25 moves.
- Eight nearby source-to-resonance paths: 27 open cells and 35 boundary evaluations,
  with no unresolved intervals.
- A full straight deformation from `(1,2,3,4,5,6,7)` to a surviving resonance:
  33 open cells and 34 boundary evaluations, all terminating. This verifies that
  selected entire deformation, not a covering of all speed arrangements.

These counts are tests/paths, not a statistical distribution. Distinct resulting
speed-set counts and all exact traces are recorded separately in the JSON.

## The pair returns, but the remaining arrangement does not

One surviving example is

`(1, 23509/10000, 8103/2500, 52223/12500, 52223/10000, 57871/10000, 17184527/2310000)`.

Write the middle resonant pair as `4D,5D`, where `D=52223/50000`.
The handoff `5D -> 4D` occurs at moves 3 and 21 (zero-based), with capture depth
exactly `9/5` both times and elapsed time `P=1/D`. The two speeds advance exactly
five and four laps. The other five have nonintegral phase advances over `P`.

After the first pair exit, only the fastest reading blocks. After the second,
three different readings block: those at `23509/10000`, `8103/2500`, and
`57871/10000`. Thus the repeated pair is not a repeated global state.

The pair has six common clear windows in one period. All six are covered by the
other readings during the observed first return interval. In the next period,
the second window becomes partly uncovered. Its endpoints are

`[57/(40D), 47/(32D)]`.

Only `c=57871/10000` blocks any part of that second-period window. At its exit
`65/(8c)=81250/57871`, every reading is clear. The experiment checks all entrance
and exit events and their intervening intervals, not just window midpoints.

## General results formalized

`Spec/HandoffResonanceN.lean` proves:

1. If `d*P` is not an integer, a reading eventually vacates any prescribed blocking
   role at times `t+q*P`. This uses the existing `OneFree.exists_clear_step`.
2. If a role stays blocked at every such replay, `d*P` must be an integer. No fixed
   lap-increment assumption is needed.
3. A perpetual repeated schedule therefore puts every reading used in that
   schedule on the same time lattice. **This does not imply complete residues mod 8.**
4. Integral phase advance determines the later lap labels by an affine formula.
5. A continuous, scale-invariant region of the resonant family is isolated at
   `65/(8c)`: for readings `(m,p,q,4D,5D,c,f)`, it suffices that `c>0` and

   `9c <= 65m <= 15c`, `25c <= 65p <= 31c`, `33c <= 65q <= 39c`,
   `57c <= 325D`, `260D <= 47c`, `81c <= 65f <= 87c`.

All three survivors satisfy these inequalities exactly. This is a family theorem
on the resonance surface, not just three numerical examples. An exact example
instantiation is included in the Lean audit file.

## Remaining distinction

Zero drift of one pair does not protect the blocking roles of the other readings.
An off-lattice role must eventually change. But roles can be reassigned, the replay
period can change, or all participating readings can share a lattice. The statements
above do not yet prove those alternatives impossible for seven readings. In
particular, the hard integer-speed case already has a common period; integrality
alone does not settle it.

## Reproduction

```sh
python3 experiments/nN/redo/handoff_boundaries_v1.py --test
python3 experiments/nN/redo/zero_drift_handoffs_v1.py --test
python3 experiments/nN/redo/zero_drift_handoffs_v1.py
lake build LonelyRunner.LRC.Spec.HandoffResonanceN
lake env lean experiments/nN/handoff_resonance_axioms_v1.lean
```

The two Python suites contain nine tests, including independent opening search,
periodic pair-window checks, and an exact surviving-return regression. The complete
experiment is in `zero_drift_handoffs_v1.json`. The targeted build and axiom audit
do not replace the repository-wide Spec gate.
