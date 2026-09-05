# Assumptions: CLAIM-LRC-000049

1. Source integrity verified by SHA-256
   `b9309c757e407918777b7ae7311e104430430f6c05556be2e727e70779b8b3d7`.
2. `perfectMatch` is the ground-truth correctness indicator for residue detection
   (detectedResidues == expectedResidues as sets).
3. `maxError` in coprime_residue_verification is a grid-resolution metric, not a
   residue set detection error. Its variation with n is expected and does not
   contradict perfectMatch=true. This is the source of the partial metric_match
   flag (measurement_required_fixes: align_metric_definition).
4. The perturbation test operates on a fixed n (inferred as n=12 from context of
   10 trials per level); the specific n is not explicitly stated in the source JSON.
5. medianRuntime=0 reflects sub-millisecond execution; no precision timing claim
   is made for Test 3.
6. scalingExponent=null and rSquared=null indicate the complexity fitting was not
   executed in this run; no algebraic complexity bound is asserted.
7. Results cover n in {3..12} for Test 1 and n in {4..10} for Test 3; claims do
   not generalise beyond these ranges without further testing.
8. Jaccard similarity of 0 at perturbationLevel ≥ 1e-08 means detectedResidues
   and expectedResidues share no elements, indicating complete breakdown.
