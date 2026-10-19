# Shared merge and real-speed transfer: implementation

19 October 2026. Completed the first two recommendations from the streamlining review.

## Result

* `RealRowsN.lean` holds the shared parallelism, perpendicular avoidance, basis representation,
  and proportional-speed lemmas extracted from `RealFiveN`. Existing names and namespaces remain.
* `ExactMergeN.lean` holds the existing finite-cone argument for any number of rows, together with
  `merge_of_free`. The four-, five-, and six-row merge theorems retain their names and statements
  and are now direct specializations. Unused four-/five-row enumeration and blocker helpers were
  removed after checking that the library has no remaining consumers.
* `RealTransferN.existenceAtN_of_nat` proves, for every natural `n`, that integer existence at
  order `n + 3` and real existence at order `n + 2` imply real existence at order `n + 3`.
  The offset avoids unnecessary natural-subtraction side conditions and covers all orders ≥ 3.
* Real existence at five, six, classical seven, and conditional native seven is now a one-line
  application of that transfer. All existing existence/Lonely Runner theorem signatures remain.
* Orders three/four and the finite native certificate sources are unchanged.

The six original modules had 1,479 lines. Their replacements plus the three extracted/shared
modules have 734 lines: 745 fewer lines (50.4%). This is a source/proof-maintenance reduction;
it does not measure build-time improvement or reduce the finite enumeration.

The import order is now `ManyDirectionsN → RealRowsN → ExactMergeN → RealTransferN → RealFiveN`
(read arrows as “supports”), followed by the order-specific modules. The original namespaces
on extracted declarations preserve existing qualified references without a cycle.

## Validation

* Both real seven-runner streams build successfully (8,472 jobs).
* The explicit native order-seven build passes (8,672 jobs). Its six axiom reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`. The dependency audit traverses 112,252
  declarations and excludes the listed classical endpoints, BHK, and IntLRC/Barajas–Serra endpoints.
* `experiments/nN/native_seven/streamlining_audit.lean` checks the original real theorem
  statements through orders 3–7, both seven-runner streams, and the three specialized merge
  signatures. All 17 axiom reports use only the three standard axioms above; parsed results
  are in `streamlining-audit-results.json` alongside the audit.
* `git diff --check` passes. The new shared modules contain no `sorry`, `axiom` declaration,
  or `native_decide`.

Reproduce from the repository root (use two workers to limit certificate memory demand):

```sh
LEAN_NUM_THREADS=2 lake build LonelyRunner.LRC.Spec.OrderSevenNativeN LonelyRunner.LRC.Spec.RealSevenN
LEAN_NUM_THREADS=2 lake env lean experiments/nN/native_seven/native_audit.lean
LEAN_NUM_THREADS=2 lake env lean experiments/nN/native_seven/streamlining_audit.lean
```

## Remaining options

Checker/soundness consolidation and table-layout changes remain separate follow-up work.
They affect expensive certificate checks and require their own full-build performance comparison.
This change establishes the mathematical shared foundation first.
