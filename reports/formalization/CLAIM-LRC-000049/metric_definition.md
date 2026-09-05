# Metric Definitions: CLAIM-LRC-000049

## Test 1: coprime_residue_verification
- `expectedResidues`: set of integers coprime to n in {1..n-1}, i.e. {k : gcd(k,n)=1}.
- `detectedResidues`: set of residues identified by the LRC method.
- `perfectMatch`: true iff detectedResidues == expectedResidues (exact set equality).
- `gridUniform`: true iff the LRC grid is assessed as uniform for this n.
- `maxError`: maximum positional error on the grid; reflects grid-spacing resolution
  relative to phi_n and n. NOT a measure of residue detection accuracy.
  Varies with n due to grid granularity; large values (e.g. 0.25 for n=6) are
  expected and do not indicate detection failure. Requires metric definition
  alignment (dossier flag: measurement_required_fixes: align_metric_definition).
- `avgError`: mean positional grid error; same caveat as maxError.
- `isolationCount`: count of LRC isolation events for this n.

## Test 2: numerical_fragility
- `perturbationLevel`: magnitude of random perturbation applied to inputs.
- `jaccardSimilarity`: |detectedResidues ∩ expectedResidues| / |detectedResidues ∪
  expectedResidues| per trial; 1.0 = perfect match, 0.0 = no overlap.
- `medianJaccard`: median of jaccardSimilarity over 10 trials at each perturbation level.
- `perfectMatches`: count of trials with jaccardSimilarity = 1.0.
- `breakdownThreshold`: smallest perturbationLevel at which medianJaccard < 1.0
  and perfectMatches = 0; reported as 1e-08 in this dataset.

## Test 3: computational_complexity
- `avgBoundaryCount`: mean number of LRC boundary events over repeated runs for n.
- `medianRuntime`: median execution time in milliseconds; 0 indicates sub-ms.
- `scalingExponent`: fitted power-law exponent for boundaryCount vs n; null here.
- `rSquared`: goodness of fit for scaling model; null here (model not fitted).
