# Finite-arrangement review — 3 October 2026

## Answer

There are genuine, exhaustive reductions already proved. In particular, the Lean skeleton reduces the remaining work to five named families. There is not yet a proved finite catalogue of isolation-producing mechanisms covering every member of those families. These are different claims: the first should be credited, and the second should not be assumed.

Scope: recent running-log work through E350, the arrangement/equivalence/finite-cover documents, key reduction and mechanism Lean statements, and diagnostic code. This is a source review with small exact-arithmetic checks, not a fresh full Spec build or an audit of every experiment.

## What really reduces “any”

1. **Exact normalisation.** `ArrangementShapeN.reduction_iff` removes translation, positive scale and labelling: every input is represented by `0 = x₀ < … < x₇ = 7`, with six continuous factors. This is exhaustive; it does not claim finitely many individual shapes.
2. **Finite reference categories.** The 1,890 walls are 21 distinct variable difference forms times 90 reference levels. They divide the entire normalised simplex into finitely many sign categories, including boundary faces. The count is walls, not arrangements. The rational-grid representative argument preserves this reference data. It does not preserve arbitrary later flank comparisons.
3. **Arithmetic residual reduction.** `OrderEightCasesN.lonelyRunnerAt8_iff_residual` leaves only the whole-number `EightResidual` family after the proved cases have been removed. Cardinality, positivity, primitive/common-factor reduction, divisibility and failed-case constraints are genuine restrictions, not just descriptions of arbitrary speeds. The integer parameters remain unbounded.
4. **An exhaustive finite list of outstanding families.** `Order8SkeletonN.lonelyRunnerAt8_of_arrangement_holes` has exactly five premises: `ArrBlockRule8 3 9`, `4 9`, `5 9`, `6 9`, and `ArrBoundedCovered8 9`. Separated fast blocks of one and two are already handled. The remaining four block sizes plus the non-separated family exhaust the unresolved alternatives in this route. These five premises are still obligations, not five proved isolation mechanisms. Searching their names found no other module discharging them.
5. **Uniform mechanisms already cover infinite families.** AP/grid neighbourhoods, fast-runner/pair rules, train-collapse and split-chain results, and the newer deadline/replacement lemmas all do this under explicit hypotheses. Arbitrarily large numerical parameters are compatible with one finite symbolic rule.

These reductions can be combined logically: only members of the five outstanding families that also evade the proved residual cases need new work. That combined classification is stronger than either description alone; it is not yet a finite solved mechanism catalogue.

## What the last two days added

- Exact residue and displacement formulas separate a genuine transformation from a merely similar-looking grid placement.
- Local deformation windows and replacement inequalities now carry all seven readings, rather than treating pair separation as sufficient for isolation.
- `MappedCascadeRulesN` proves the closer restriction and earlier-capture product bound with their hypotheses explicit. The late bound `26433/2209 < 12` is established when the two specified capture inequalities hold. The missing step is establishing which inputs supply those relationships, and covering inputs that do not.
- The map has identified useful opener/closer and lap/rank patterns. The 43 realised ordered opener/closer pairs are outcome classes; they do not prove that every input has an outcome.
- E347 corrected the leaf-only accounting: a path may stop at an internal node. E348 improves that accounting, but float-feasibility pruning and bounded spread remain limitations of the tree evidence. E349 is not a kernel-checked exhaustion of all arrangements.
- E350 rejects particular proposed path-word identifications in the tested window. It does not reject a finite family of symbolic isolation mechanisms, which need not reproduce identical paths.

## Exact diagnostic: one reference category, two paths

For subject 0, compare the normalised shapes

`(0, 99/100, 202/100, 301/100, 403/100, 301/60 ± 1/100000, 604/100, 7)`.

For every pair `i < j` and `a ∈ {1,3,5,7}`, the values

`(floor(a·(x_j−x_i)), isInteger(a·(x_j−x_i)))`

agree between the two shapes. Thus they have the same full reference-wall sign data, including equality information. Exact `Fraction` evaluation of `cascade_path_map_v1.path` gives:

- Minus: setters/laps `(7,1),(6,1),(5,1),(4,1),(7,2),(3,1)`; isolation at `t = 225/602`.
- Plus: the same six moves followed by `(5,2),(7,3),(2,1),(7,4),(5,3)`; isolation at `t = 937500/1505003`.

This disproves only the inference that a reference category determines its entire later cascade. It does not disprove a common symbolic proof covering both, or a finite refinement by the relevant flank inequalities. Adding a common positive speed makes these physical positive-speed arrangements without changing the check.

## Unbounded labels are not unbounded mechanism types

Consider positive physical speeds `(s,s+1,…,s+6,s+8K)`, with `s > 0` and integer `K ≥ 1`, and subject `s`.

At `t = 1/8`, the six disparities `1,…,6` are clear and disparity `8K` is captured. Its exit is

`t* = (8K+1)/(64K) = 1/8 + 1/(64K)`.

At that exit the six smaller readings lie in `[1/8, 27/32] ⊂ [1/8,7/8]`; the fast reading is `K+1/8`. Hence this single symbolic calculation isolates every member of the family. The lap `K` is unbounded, while `R = 8t* ≤ 9/8`.

Consequently E350's suggestion that a universal `R < 12` would itself cap lap labels needs correction: a spread bound is also needed. Conversely, the example supports the owner's distinction between infinitely many numerical instances and one mechanism. A finite list of literal histories is not required.

## What remains to establish

The missing finite-cover statement is: every residual input in the outstanding families satisfies the hypotheses of at least one member of a finite list of uniform mechanisms. Its input classification must not require an already-known lonely landing, and each mechanism must work throughout its stated parameter domain. Lap numbers and deviations may remain symbolic parameters.

The next useful analytical work is therefore to classify when the mapped earlier-capture inequalities hold, then derive alternative inequalities/mechanisms for their complement. It is not necessary to enumerate all real shapes, all lap labels, or all first-landing histories. Equally, the finite reference partition alone does not supply this missing classification.

No Lean source, shared running-log entry or existing experiment was changed by this review. No commits or pushes were made.
