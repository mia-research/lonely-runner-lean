# Formalized Claim: CLAIM-LRC-000049

## Claim Type
Empirical multi-test validation claim (LRC coprime residue detection correctness,
numerical fragility threshold, and boundary count scaling).

## Domain
Dataset: `lrc_rigorous_validation_2025-09-24T12-45-35.json`
SHA-256: `b9309c757e407918777b7ae7311e104430430f6c05556be2e727e70779b8b3d7`
Three test suites: coprime_residue_verification (n=3..12),
numerical_fragility (perturbation sweep), computational_complexity (n=4..10).

## Formal Proposition

### Test 1: Coprime Residue Verification (n = 3..12)
For each n in {3, 4, 5, 6, 7, 8, 9, 10, 11, 12}, the LRC method detects exactly
the set of coprime residues mod n (i.e. detectedResidues == expectedResidues).

| n  | phi_n | perfectMatch | gridUniform | maxError    | isolationCount |
|----|-------|--------------|-------------|-------------|----------------|
| 3  | 2     | true         | true        | 1.11e-15    | 18             |
| 4  | 2     | true         | true        | 1.25e-01    | 28             |
| 5  | 4     | true         | true        | 1.00e-01    | 74             |
| 6  | 2     | true         | true        | 2.50e-01    | 80             |
| 7  | 6     | true         | true        | 7.14e-02    | 182            |
| 8  | 4     | true         | true        | 9.38e-02    | 288            |
| 9  | 6     | true         | true        | 7.41e-02    | 409            |
| 10 | 4     | true         | true        | 1.50e-01    | 500            |
| 11 | 10    | true         | true        | 4.55e-02    | 732            |
| 12 | 4     | true         | true        | 1.46e-01    | 848            |

Adjudicable statements (Test 1):
1. perfectMatch=true and gridUniform=true for all n in {3..12} (10/10 cases).
2. isolationCount is strictly increasing with n over this range: 18 → 848.
3. maxError is not a residue detection error; it reflects grid-spacing resolution
   and varies with phi_n (note: maxError for n=3 is machine-epsilon-level ~1e-15,
   while for n=6 it reaches 0.25 — see metric_definition for clarification).
   This is the source of the dossier's measurement_metric_match: partial flag.

### Test 2: Numerical Fragility (perturbation sweep, n=12 inferred)
| perturbationLevel | medianJaccard | perfectMatches |
|-------------------|---------------|----------------|
| 0                 | 1.0           | 10             |
| 1e-12             | 1.0           | 10             |
| 1e-10             | 1.0           | 9              |
| 1e-08             | 0.25          | 0              |
| 1e-06             | 0.0           | 0              |
| 1e-04             | 0.0           | 0              |

Adjudicable statements (Test 2):
4. The method sustains perfect or near-perfect residue detection (medianJaccard=1.0,
   perfectMatches ≥ 9) at perturbation levels ≤ 1e-10.
5. Structural breakdown occurs sharply at perturbationLevel = 1e-08
   (medianJaccard drops from 1.0 to 0.25, perfectMatches drops to 0).
6. The empirical breakdownThreshold is 1e-08, consistent with the reported sentinel.

### Test 3: Computational Complexity (n = 4..10)
| n  | avgBoundaryCount | medianRuntime (ms) |
|----|------------------|--------------------|
| 4  | 8                | 0                  |
| 5  | 15               | 0                  |
| 6  | 20               | 0                  |
| 7  | 32               | 0                  |
| 8  | 47               | 0                  |
| 9  | 61               | 0                  |
| 10 | 86               | 0                  |

Adjudicable statements (Test 3):
7. avgBoundaryCount increases monotonically with n over {4..10}: 8 → 86.
8. scalingExponent and rSquared are null (not fitted in this run); no algebraic
   complexity bound is claimed.
9. medianRuntime = 0 for all n, indicating sub-millisecond execution; timing
   resolution is insufficient to distinguish runtime differences in this corpus.

## Falsification Rule
- Test 1: Falsified if any n in {3..12} yields perfectMatch=false or gridUniform=false
  on recomputation from the same source (SHA-256 verified).
- Test 2: Falsified if medianJaccard < 1.0 at perturbationLevel ≤ 1e-10, or if
  breakdown does not occur by perturbationLevel = 1e-08.
- Test 3: Falsified if avgBoundaryCount is non-monotone over n in {4..10}.
