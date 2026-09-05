# phi_match Inconsistency Investigation
**Report ID:** INV-PHI-MATCH-001
**Cycle:** 005 (priority item from Cycle 004 scientific review)
**Date:** 2026-02-28
**Claims examined:** CLAIM-LRC-000044, CLAIM-LRC-000056

---

## Executive Summary

The `phi_match` column exists in two Cycle 004 datasets but is **not comparably defined**
across them. Investigation reveals three distinct findings:

1. **Mechanistic divergence** (structural): `unique_phases` in 000056 is computed FROM
   `isolation_count` — isolation events define phase boundaries. Only arithmetic sequences
   produce isolation events (isolation_count > 0) in this corpus. This is not a pipeline
   design choice; it is a mathematical consequence. Geometric and random sequences produce
   ZERO isolation events → unique_phases is undefined → phi_match cannot be computed.

2. **perturbed vs geometric/random asymmetry**: perturbed receives an explicit phi_match=NO
   (tested as a near-arithmetic candidate, fails because isolation_count=0). Geometric and
   random are not tested at all (phi_match='', outside scope of measurement).

3. **Data labeling bug** in CLAIM-LRC-000044: 2 arithmetic rows are incorrectly labeled
   `phi_match=true` despite detected_phases (3) ≠ phi (4). This is a pipeline error.

**Key geometric finding**: geometric sequences achieve detected_phases==phi(n) at 100% in
000044 (boundary traversal), yet produce ZERO isolation events in 000056. These two facts
are not contradictory — they measure different topological properties of the boundary set
(phase span vs phase isolation). This is a scientifically meaningful structural distinction.

---

## Dataset Profiles

### CLAIM-LRC-000044
**File:** `lrc_efficiency_runtime_validation.csv`
**Rows:** 384 (96 per family × 4 families)
**Families:** arithmetic, geometric, harmonic, quadratic
**phi_match column values:** `true` / `false` (lowercase strings)
**Phase column:** `detected_phases` (integer count of detected boundary phases)
**phi column:** `phi` (Euler totient φ(n))

### CLAIM-LRC-000056
**File:** `lrc_validation_large_1759239075705.csv`
**Rows:** 220,110
**Families:** arithmetic, geometric, perturbed, random
**phi_match column values:** `YES` / `NO` / `` (empty, not computed)
**Phase column:** `unique_phases` (string, integer or empty)
**phi column:** `phi_n`

---

## Finding 1: Definitional Divergence

### In CLAIM-LRC-000044
phi_match = `(detected_phases == phi(n))`

| Family     | phi_match=true | phi_match=false | Condition satisfied? |
|------------|----------------|-----------------|----------------------|
| arithmetic | 2              | 94              | No (see Bug below)  |
| geometric  | 96             | 0               | Yes, always          |
| harmonic   | 96             | 0               | Yes, always          |
| quadratic  | 96             | 0               | Yes, always          |

For non-arithmetic families, detected_phases == phi(n) in every row across all n tested
(n ∈ {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30}).
For arithmetic, detected_phases << phi(n) in all 96 rows (no row achieves full phi-phase
saturation). phi_match=true for arithmetic is therefore almost never reached.

**Scientific reading of 000044:** Arithmetic sequences underperform non-arithmetic
families in phase detection completeness (detected_phases vs phi(n)) while showing
comparable boundary_count. This is not a failure of the detector — it is a structural
property of arithmetic sequences at the tested parameter regime.

### In CLAIM-LRC-000056
phi_match = `(unique_phases == phi_n)` for arithmetic only; not applied to other families.

| Family     | phi_match | unique_phases | Notes                                          |
|------------|-----------|---------------|------------------------------------------------|
| arithmetic | YES (all) | == phi_n      | 55,000 rows, 100% rate                         |
| perturbed  | NO (all)  | '' (empty)    | Test applied, explicit negative                |
| geometric  | '' (N/A)  | '' (empty)    | Test not applied to this family                |
| random     | '' (N/A)  | '' (empty)    | Test not applied to this family                |

**Scientific reading of 000056:** For arithmetic sequences, the boundary method
reproduces exactly phi(n) unique phases in every trial (unique_phases == phi_n,
55,000/55,000 rows). The perturbed family (arithmetic with noise) fails this condition
universally — perturbation disrupts phi(n)-phase structure. Geometric and random
families are not tested for phi_match (the phi(n)-phase property is not expected and
not claimed for these families).

### Key Divergence
The two datasets are testing **different claims about different families**:
- 000044 asks: can the detector find as many phases as phi(n) predicts, across all speed families?
- 000056 asks: do arithmetic sequences produce exactly phi(n) unique phases?

In 000044, arithmetic FAILS to reach phi(n) phases (the detector finds fewer). In 000056,
arithmetic SUCCEEDS at producing phi(n) unique phases. These are not contradictory: they
measure different aspects. The column name `phi_match` is reused across pipelines with
different definitions — this is a **pipeline column-name collision**, not a scientific paradox.

---

## Finding 2: Data Labeling Bug in CLAIM-LRC-000044

**The bug:** 2 arithmetic rows have `phi_match=true` despite `detected_phases ≠ phi`.

```
n=5, phi=4, detected_phases=3, phi_match=true, seed=1, boundary_count=100018
n=5, phi=4, detected_phases=3, phi_match=true, seed=3, boundary_count=100019
```

Both rows: detected_phases = 3, phi(5) = 4. Since 3 ≠ 4, phi_match should be `false`.

No other arithmetic row has phi_match=true. No other family has this inconsistency.
The anomaly is isolated to n=5, seeds 1 and 3 in the arithmetic family.

**Severity:** Low impact on 000044 adjudicated statements (the claim does not directly
adjudicate arithmetic phi_match rates). However, it indicates a pipeline condition check
that has a boundary error at n=5 for certain seeds.

**Recommended action:** Flag to pipeline owner for correction in next data generation run.
Label: `PIPELINE-BUG-PHI-MATCH-000044-ARITH-n5`.

---

## Corrective Actions Taken

### CLAIM-LRC-000056 formal_claim.md
- **Corrected** the phi_match table to reflect the three-way structure:
  arithmetic=YES, perturbed=NO, geometric/random=N/A (not measured).
- **Replaced** Statement 2 with Statements 2a and 2b, distinguishing between
  perturbed (explicit NO) and geometric/random (not computed).
- **Added** Correction Note documenting the previous error.

### CLAIM-LRC-000056 assumptions.md
- **Corrected** Assumption 2 to specify that phi_match is only computed for
  arithmetic and perturbed families; geometric/random have empty columns.
- **Corrected** Assumption 3 to note unique_phases is only non-empty for arithmetic.

---

## Implications for Adjudicated Vote (CLAIM-LRC-000056)

The Cycle 004 vote (Gemini: approve_with_caveats, promote) was based on the incorrect
formalization. The core finding — arithmetic family exclusively produces phi(n) unique
phases — is **confirmed and unaffected** by this correction. However:

- The framing of "non-arithmetic phi_match_rate=0.0" overstated the scope: geometric
  and random were never tested for phi_match, so rate=0.0 is not the right summary.
- The corrected finding is more nuanced: perturbed IS tested and explicitly fails;
  geometric/random are outside the measurement scope.

**Impact on vote:** The approve_with_caveats outcome remains appropriate. The correction
strengthens the "with caveats" qualifier: the phi_match result is specific to arithmetic
and perturbed; non-arithmetic-non-perturbed families are not adjudicable on this metric.

---

## Finding 3: The Geometric Topology Gap

In 000056, the perfect bijection holds across all 220,110 rows:

```
isolation_count > 0  ↔  unique_phases non-empty  ↔  first_isolation non-empty
```

| Family     | isolation>0 | unique_phases | phi_match | Mechanism           |
|------------|-------------|---------------|-----------|---------------------|
| arithmetic | True (all)  | non-empty     | YES       | isolation → phases  |
| geometric  | False (all) | empty         | '' (N/A)  | no isolation events |
| perturbed  | False (all) | empty         | NO        | explicitly tested   |
| random     | False (all) | empty         | '' (N/A)  | no isolation events |

`unique_phases` is derived from isolated boundary points. Without isolation events, the
phase count cannot be extracted, and phi_match is undefined by construction.

**Geometric boundary topology in 000056**: geometric sequences produce substantially MORE
boundary crossings than arithmetic (mean bc: 47–1230 vs 27–358 across n=5..15) but produce
NO isolated boundary points. This implies geometric boundary structures are **connected**
(no gaps between consecutive boundary events) — the boundary set spans many regions but
never separates into the isolated clusters that arithmetic sequences produce.

**Cross-dataset observation**: in 000044, geometric achieves detected_phases==phi(n) at
100% rate via boundary traversal (a connected-region counting algorithm). In 000056, the
isolation-based unique_phases measurement cannot be applied to geometric. Both findings are
consistent: geometric has phi(n) connected phase regions but zero isolated phase boundaries.
The two datasets reveal complementary facets of geometric boundary topology.

**Implication for 000056 adjudication**: the phi_match finding for arithmetic is stronger
than previously framed. It is not merely that arithmetic passes the phi_match test while
others fail — it is that arithmetic is the ONLY family that produces isolation events at
all, which is the precondition for unique_phases to be measurable. This makes the
arithmetic phi(n)-phase structure a genuinely distinctive property of arithmetic sequences,
not just a test result.

## Finding 4: Arithmetic Phase Coverage Ceiling in 000044 — Candidate Cycle 005 Claim

**Dataset:** CLAIM-LRC-000044 (`lrc_efficiency_runtime_validation.csv`, 96 arithmetic rows)

### The finding

In 94 of 96 arithmetic rows, `detected_phases` does not exceed `floor(phi(n) / 2)`.
Two rows (n=5, seeds 1 and 3) have dp=3 which exceeds floor(4/2)=2.

**Methodological note (reviewer P2):** These 2 rows are NOT excluded because their dp
values are corrupted — dp=3 is the observed measured value. The phi_match labeling bug
in these rows (phi_match=true when it should be false, since 3≠4) is a labeling error
in a different column. The dp=3 measurement itself is real data. Consequently, the
ceiling is correctly characterized as a **near-ceiling** (94/96 rows), not a hard ceiling.
The coincidence that the dp-ceiling violations and the phi_match labeling bug are the
SAME rows suggests the pipeline may have evaluated phi_match with a non-standard condition
at n=5 (seeds 1,3) that both produced dp=3 and erroneously set phi_match=true, but this
is speculative without base/delta access.

| Family     | detected_phases / phi(n) | behaviour                       |
|------------|--------------------------|----------------------------------|
| geometric  | 1.000 (all 96 rows)      | always full coverage             |
| harmonic   | 1.000 (all 96 rows)      | always full coverage             |
| quadratic  | 1.000 (all 96 rows)      | always full coverage             |
| arithmetic | ≤ 0.500 in 94/96 rows    | near phi/2 ceiling, 2 exceptions |

The 2 rows exceeding floor(phi/2) (dp=3 > floor(4/2)=2) are the same 2 phi_match-bug rows.
Full arithmetic row counts: 94 at or below floor(phi/2), 2 above.

### Coverage profile by phi_n

The "achieves phi/2?" column indicates whether floor(phi_n/2) is reached in at least
one valid seed across all n in the group. For phi_n=8 this is group-level; see note below.

| phi_n | n values (excl n=5 bug seeds) | all dp vals | max dp | floor(phi/2) | achieves phi/2?       |
|-------|-------------------------------|-------------|--------|--------------|------------------------|
| 4     | 5(seeds 0,2,4,5), 8, 10, 12  | {1, 2}      | 2      | 2            | Yes (n=8,10,12 only)  |
| 6     | 7                             | {2, 3}      | 3      | 3            | Yes (n=7, stochastic) |
| 8     | 15, 16, 20, 30                | {2, 3, 4}   | 4      | 4            | Yes (n=20 only, 1 seed)|
| 10    | 11                            | {5}         | 5      | 5            | Yes (deterministic)   |
| 12    | 13                            | {5}         | 5      | 6            | No (one short)        |
| 16    | 17                            | {4, 5, 6}   | 6      | 8            | No                    |
| 18    | 19                            | {5, 6, 7}   | 7      | 9            | No                    |
| 20    | 25                            | {5, 6, 7}   | 7      | 10           | No                    |
| 22    | 23                            | {6, 7}      | 7      | 11           | No                    |
| 28    | 29                            | {5, 6}      | 6      | 14           | No                    |

**n values that achieve exactly floor(phi_n/2) in at least one valid seed:**
n ∈ {7, 8, 10, 11, 12, 20} — confirmed by row-level inspection.

Detail for phi_n=8 group (reviewer P2b correction): among n={15,16,20,30}, the max dp=4
comes exclusively from n=20 seed 2 (dp=4=floor(8/2)). n=15 (dp=3 in all seeds, deterministic),
n=16 (dp=2 or 3, never 4), and n=30 (dp=2, deterministic) do NOT individually achieve phi/2.
The "Yes" in the table is group-level, driven entirely by n=20.

For phi_n ≤ 10: at least one n achieves floor(phi_n/2) in some seed.
For phi_n ≥ 12: no n achieves floor(phi_n/2); coverage declines as phi_n grows.

**Note on n=5 (phi_n=4):** Valid n=5 rows (seeds 0,2,4,5) have dp=1 (25% coverage),
far below phi/2=2. n=5 is the only phi_n=4 arithmetic case failing to reach phi/2 in ANY
valid seed — the composite phi_n=4 cases (n=8,10,12) all achieve dp=2 deterministically.
Whether primeness of n=5 is the causal factor cannot be determined without base/delta data.

### Scientific interpretation

The contrast is stark:
- Non-arithmetic sequences: boundary traversal finds **all** phi(n) phases (100% coverage)
- Arithmetic sequences: boundary traversal finds **at most half** phi(n) phases (~50%
  ceiling for small phi_n, declining to <25% at phi_n=28)

This is consistent with — and complements — the 000056 finding. In 000056, arithmetic
produces phase-ISOLATED boundary events (unique, enumerable phase clusters). In 000044,
the boundary traversal finds fewer phase regions for arithmetic. The two observations
together suggest arithmetic boundary structure is denser and more isolated per phase,
while non-arithmetic boundary structure is spread uniformly across all phi(n) phases
but without isolation gaps.

### Sub-finding 4a: Determinism of detected_phases across seeds

For some n values, `detected_phases` is identical across all 6 seeds (deterministic);
for others it varies (stochastic). This is not explained by boundary_count: n=16 has
bc and iso that are nearly identical across seeds (<0.01% range) yet dp varies between
2 and 3. The seed affects the detection algorithm's starting condition, not the boundary
structure itself.

**Deterministic n** (dp same for all 6 seeds): {8, 10, 11, 12, 13, 15, 30}
**Stochastic n** (dp varies): {5, 7, 16, 17, 19, 20, 23, 25, 29}

Properties tested and found NOT to fully explain the split:

| Property                   | Rule violated by                     |
|----------------------------|--------------------------------------|
| Prime vs composite         | n=11, 13 (prime, deterministic)      |
| phi/n ratio                | n=10 (det) vs n=20 (non-det), both 0.4 |
| phi_n value                | n=8 phi_n=4 (det) vs n=5 phi_n=4 (non-det) |
| Squarefreeness             | n=8=2³, n=12=2²·3 are non-squarefree but deterministic |
| Boundary count             | n=16 bc≈1.2M (non-det) > n=13 bc≈780K (det) |

The closest partial rule: **all squarefree composites are deterministic** (10, 15, 30),
but the rule breaks in both directions (8 and 12 are non-squarefree yet deterministic;
16 and 20 are non-squarefree and non-deterministic).

**The n=5 specific case:** n=5 (prime, phi_n=4) is the only phi_n=4 case failing to
reach dp=1 even in best seeds (valid seeds all give dp=1, max 25% coverage). All
composite phi_n=4 cases (n=8,10,12) give dp=2 deterministically (50% coverage). The
factor separating n=5 from n=8,10,12 is unknown from this dataset — the seed-to-speed-
sequence mapping is not stored in the CSV (no base/delta columns in 000044).

**Open sub-question:** What number-theoretic property of n (beyond phi_n, prime/composite,
squarefreeness, phi/n) determines whether the boundary traversal algorithm produces a
deterministic detected_phases count? And why does n=5 systematically detect fewer phases
than composite n with the same phi_n? This requires either: (a) access to the speed-
sequence parameterization for each seed, or (b) new data with the base/delta columns
exposed, or (c) a theoretical analysis of the detection algorithm.

### Caveats for adjudication

- Sample size: 94 valid arithmetic rows (96 total, 2 with real dp violations), ≤6 seeds per n value — weak statistical power
- n range: 16 discrete values {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30} only — does the ceiling hold at untested integers and beyond n=30?
- The phi/2 ceiling is an empirical observation from this corpus; no proof is offered
- The declining coverage at large phi_n may reflect algorithm limits, not arithmetic structure
- Determinism vs stochasticity is unresolved — 6 seeds is insufficient to confirm true
  stochasticity vs just insufficient sampling of a narrow discrete distribution

### Candidate Cycle 005 Claim

**Proposed claim (CLAIM-LRC-000044-EXT-001):**
> In CLAIM-LRC-000044 (`lrc_efficiency_runtime_validation.csv`), boundary traversal
> detects `floor(phi(n)/2)` phases or fewer for arithmetic sequences in 94 of 96 rows,
> across the 16 discrete tested values n ∈ {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30}.
> Two rows (n=5, seeds 1 and 3, dp=3 > floor(4/2)=2) exceed this bound; these are the
> same rows carrying the phi_match labeling error. Non-arithmetic families (geometric,
> harmonic, quadratic) achieve `detected_phases = phi(n)` in all 288 rows. The arithmetic
> near-ceiling of phi/2 is exact in at least one valid seed for phi_n ≤ 10 (specifically
> n ∈ {7,8,10,11,12,20}) and falls below phi/2 for phi_n ≥ 12, reaching 21% at phi_n=28
> (n=29). NOTE: Only 16 discrete n values were tested; the claim does not generalize to
> all integers in 5..30 or beyond n=30 without additional data.

**Required for promotion:** additional n values (n>30), replication across more seeds,
and a theoretical account of the phi/2 ceiling.

---

## Finding 5: Wave/Interference Patterns — Meta-Analysis (2026-02-28)

**Question:** Does efficiency (isolation_count/boundary_count) for arithmetic sequences exhibit
wave-like or periodic interference patterns across n values? Are there analogous meta-patterns
across all families?

### 5.1 Universal Boundary Count Law

The most prominent meta-pattern across ALL speed families in CLAIM-LRC-000044 is:

**bc ≈ 5000 × n(n-1)**

| Family     | n ≤ 25 max deviation | n=29 ratio | n=30 ratio | Notes                              |
|------------|---------------------|------------|------------|-------------------------------------|
| arithmetic | <0.017%             | +0.256%    | +0.297%    | slight break at n=29,30             |
| geometric  | <0.016%             | −0.015%    | −0.014%    | closest conformance to formula      |
| harmonic   | <0.110%             | −0.053%    | −0.056%    | minor deviations                    |
| quadratic  | up to 1.40%         | +1.898%    | +2.050%    | substantial deviations at large n   |

Arithmetic and geometric are the most precisely conforming (ratio 0.9999–1.0003 for n≤25).
Quadratic deviates increasingly with n, flagging a qualitatively different boundary generation
mechanism at large n. This law is NOT wave-like; it is a combinatorial pairwise constraint:
each of the n(n-1) ordered walker pairs contributes approximately 5000 boundary crossings,
independent of speed family (for arithmetic/geometric/harmonic).

### 5.2 Arithmetic Efficiency: Non-Monotone, No Periodic Wave

Efficiency = isolation_count / boundary_count. Non-arithmetic families have efficiency
≈0.92–1.00 monotonically increasing to ≈1.0 by n≥17. Arithmetic shows complex behavior:

| n  | phi | efficiency | delta     | direction |
|----|-----|------------|-----------|-----------|
|  5 |   4 |    0.1802  |           |           |
|  7 |   6 |    0.1527  |  −0.0275  | ↓         |
|  8 |   4 |    0.1219  |  −0.0307  | ↓         |
| 10 |   4 |    0.1084  |  −0.0135  | ↓ (global min) |
| 11 |  10 |    0.1507  |  +0.0423  | ↑         |
| 12 |   4 |    0.2075  |  +0.0569  | ↑         |
| 13 |  12 |    0.2424  |  +0.0349  | ↑         |
| 15 |   8 |    0.2808  |  +0.0384  | ↑ (local max) |
| 16 |   8 |    0.2354  |  −0.0453  | ↓ (local dip) |
| 17 |  16 |    0.2458  |  +0.0103  | ↑         |
| 19 |  18 |    0.2416  |  −0.0042  | ↓         |
| 20 |   8 |    0.2416  |  ≈0.0000  | →         |
| 23 |  22 |    0.2847  |  +0.0431  | ↑         |
| 25 |  20 |    0.2898  |  +0.0050  | ↑         |
| 29 |  28 |    0.4179  |  +0.1282  | ↑ (large jump) |
| 30 |   8 |    0.4441  |  +0.0262  | ↑         |

Structural features:
1. **Global minimum at n=10** (eff=0.1084): four consecutive decreases n=5→10
2. **Recovery n=10→15**: four consecutive increases to local maximum (eff=0.2808)
3. **Local dip at n=16** (eff=0.2354, −0.045 from n=15): most notable local anomaly;
   coincides with the determinism anomaly (Sub-finding 4a) where n=16 has near-identical
   bc/iso across seeds but varying dp — suggesting the local dip reflects an algorithmic
   transition state, not a mathematical oscillation
4. **Large jump at n=29** (+0.128): coincides with the bc formula break-point for
   arithmetic (n=29 shows +0.256% deviation from 5000·n(n-1)), possibly related to
   a sequence-generation boundary at the n=29 parameter

### 5.3 Periodicity Analysis: No Wave Detected

n mod {4, 6, 8, 12} residue analysis of arithmetic efficiency:

| mod | residue | n values            | efficiency values                         | range  |
|-----|---------|---------------------|-------------------------------------------|--------|
| 6   | 5       | {5,11,17,23,29}     | {0.180, 0.151, 0.246, 0.285, 0.418}      | 0.267  |
| 6   | 2       | {8,20}              | {0.122, 0.242}                            | 0.120  |
| 6   | 0       | {12,30}             | {0.208, 0.444}                            | 0.236  |
| 4   | 2       | {10,30}             | {0.108, 0.444}                            | 0.336  |
| 4   | 0       | {8,12,16,20}        | {0.122, 0.208, 0.235, 0.242}              | 0.120  |

No residue class shows a consistent efficiency value. The same phi/n ratio can give
different efficiencies (n=10 and n=20 both have phi/n=0.4 but efficiencies 0.108 vs 0.242).
No wave period P ∈ {4,6,8,12} is supported by the data.

### 5.4 Conclusion: No Wave; Universal Law is the Meta-Pattern

**The bc = 5000·n(n-1) law is the true meta-pattern** — a universal combinatorial constraint
explaining boundary generation across speed families. It is NOT wave-like.

**Arithmetic efficiency non-monotonicity is NOT periodic.** The U-shaped minimum at n=10,
the local dip at n=16, and the large jump at n=29 are isolated structural features, each
with a plausible mechanistic correlate (determinism anomaly at n=16; bc formula break at
n=29). They do not constitute oscillatory or wave-like behavior.

**Recommendation:** The existing data rules out simple periodic wave patterns. Extensive
new wave-testing is NOT indicated. The targeted data requests already noted (expose
base/delta columns, generate n∈{31..50}, test squarefreeness hypothesis) are sufficient
to explain the remaining structural anomalies.

---

## Finding 6: Isolation Laws in 000056 — Two Exact Formulas (2026-02-28)

**Dataset:** CLAIM-LRC-000056 (`lrc_validation_large_1759239075705.csv`)
**Scope:** All 55,000 arithmetic rows (n ∈ {5..15}, 5,000 rows per n)

This finding extends the 000056 investigation beyond the phi_match scope.
The 000056 dataset exposes `base`, `delta`, `alpha`, `ratio`, `seed` for each row — the
actual parameters of each arithmetic speed sequence. This enables new quantitative laws.

### 6.1 First Isolation Time: fi = 1/(n·delta) — EXACT

For all 55,000 arithmetic rows:

```
first_isolation = 1 / (n × delta)
```

**Verification:**
- Rows with first_isolation > 0: 55,000 (all arithmetic rows)
- Mean relative error vs 1/(n·delta): 2.92e-14
- Max relative error: 5.12e-13
- Rows with error > 1e-9: 0
- Rows with error > 1e-6: 0

This is NOT an approximation — the formula holds to floating-point precision (machine
epsilon ~2.2e-16 for float64; the observed errors of ~5e-13 are 2-3 ULPs from exact).

**Interpretation:** For n walkers with speeds base, base+delta, ..., base+(n-1)·delta on
a unit-circle, the first isolation event occurs at t = 1/(n·delta) — exactly the time at
which adjacent walkers have separated by 1/n of the circle. This is the fundamental
period of the arithmetic speed sequence.

**Falsification:** Any arithmetic row with |first_isolation - 1/(n·delta)| > 1e-9
(relative) would falsify this claim.

### 6.2 Isolation Count Lower Bound: iso ≥ phi(n) — EXACT

For all 55,000 arithmetic rows, `isolation_count >= phi_n` with zero exceptions:

```
isolation_count ≥ phi(n)    [for all arithmetic sequences in this corpus]
```

| n  | phi(n) | min_iso | min_iso = phi(n)? |
|----|--------|---------|-------------------|
| 5  | 4      | 4       | ✓ (tight)         |
| 6  | 2      | 2       | ✓ (tight)         |
| 7  | 6      | 9       | No (min > phi)    |
| 8  | 4      | 4       | ✓ (tight)         |
| 9  | 6      | 6       | ✓ (tight)         |
| 10 | 4      | 5       | No (min > phi)    |
| 11 | 10     | 13      | No (min > phi)    |
| 12 | 4      | 4       | ✓ (tight)         |
| 13 | 12     | 16      | No (min > phi)    |
| 14 | 6      | 18      | No (min > phi)    |
| 15 | 8      | 23      | No (min > phi)    |

The lower bound iso ≥ phi(n) is **tight** for n ∈ {5,6,8,9,12} (min_iso = phi(n)
exactly) and strictly exceeded for other n. This is consistent with unique_phases = phi(n)
for all rows: you need at least one isolation event per unique phase to observe it.

**Combined with unique_phases = phi(n) (always exact):**
```
unique_phases = phi(n)  ≤  isolation_count
```
i.e., distinct phases ≤ isolation events, as expected geometrically.

### 6.3 Isolation Count Mode: iso_mode = 3·phi(n) — Holds for 8/11 n Values

The most frequent isolation count in the 5,000-row parameter sweep for each n is:

| n  | phi | 3·phi | iso_mode | mode=3·phi? | mode_count |
|----|-----|-------|----------|-------------|------------|
| 5  | 4   | 12    | 12       | ✓           | 3313/5000  |
| 6  | 2   | 6     | 6        | ✓           | 3913/5000  |
| 7  | 6   | 18    | 18       | ✓           | 2623/5000  |
| 8  | 4   | 12    | 12       | ✓           | 2767/5000  |
| 9  | 6   | 18    | 18       | ✓           | 2786/5000  |
| 10 | 4   | 12    | 12       | ✓           | 2396/5000  |
| 11 | 10  | 30    | 32       | ✗ (off +2)  | 1339/5000  |
| 12 | 4   | 12    | 12       | ✓           | 2146/5000  |
| 13 | 12  | 36    | 40       | ✗ (off +4)  | 1168/5000  |
| 14 | 6   | 18    | 20       | ✗ (off +2)  | 2126/5000  |
| 15 | 8   | 24    | 24       | ✓           | 1408/5000  |

The mode equals 3·phi(n) in 8 of 11 tested n values. The breaking cases (n=11, 13, 14)
all have mode slightly above 3·phi(n). No countercase has mode BELOW 3·phi(n).

**Excess analysis:** median(iso - phi(n)) = 2·phi(n) holds exactly for n ∈ {5..10, 12},
implying median_iso = phi(n) + 2·phi(n) = 3·phi(n) for these n values.

**Caveats:** The 3·phi(n) law breaks for n=11,13 (both prime with large phi) and n=14.
Without n > 15 data or a theoretical account, the breaking condition cannot be characterized
from this corpus. iso divisibility by phi(n) does NOT always hold.

### 6.4 bc Law Does Not Transfer from 000044 to 000056

The bc = 5000·n(n-1) law (Finding 5) does not hold in 000056. The two datasets operate in
different simulation regimes:
- **000044** (discrete time): bc ≈ 5000 × n(n-1); the 5000 factor is the step count
- **000056** (continuous time): bc/n(n-1) ≈ 1.4–1.7 (varies with n and delta)

In 000056, the bc/n(n-1) median grows from 1.333 at n=6 to 1.659 at n=14. No simple
formula fits bc across the delta parameter space; it depends on the phase alignment of
the specific (base, delta) configuration.

**Scientific implication:** bc = 5000·n(n-1) is an experimental design artifact of 000044
(5000 discrete steps × n(n-1) ordered pairs). It is not a universal mathematical law.
The 000056 bc structure is richer and parameter-dependent.

### 6.5 Candidate Claims

**CLAIM-LRC-000056-EXT-001 (FORMALIZABLE):**
> For all arithmetic rows in `lrc_validation_large_1759239075705.csv` (55,000 rows,
> n ∈ {5..15}): (1) `first_isolation = 1/(n·delta)` exactly (max relative error
> 5.12e-13); (2) `isolation_count ≥ phi(n)` without exception; (3) the most frequent
> isolation count across the 5,000-row parameter sweep for each n is 3·phi(n) for 8 of
> 11 tested n values (breaking for n=11,13,14).

**Required for promotion:** n ∈ {16..30} to test whether the 3·phi(n) mode law recovers
or continues to fail; theoretical account of fi = 1/(n·delta).

---

## Infrastructure Note: Stale Absolute Paths (P3)

Multiple legacy files contain stale absolute paths of the form
`/Users/trentpalelei/Desktop/Desktop - Trent's MacBook Pro/Math Ex/...`
which do not resolve under the current canonical root
`/Users/trentpalelei/Desktop/Math Ex/`.

Affected artifacts (historical records — do not modify):
- `reports/dossiers/cycle_002_promoted_index.csv` — all 27 dossier_path and artifact_dir entries
- `logs/run_log.jsonl` — all prompt_ref entries in cycle_004 events (corrected in cycle_004_step05)

Cycle 004 step 05 already noted: "Corrected shadow-root dossier paths to canonical root."
These are historical records. Downstream automation should use the canonical root
`/Users/trentpalelei/Desktop/Math Ex/` and ignore the stale paths in historical CSV/JSONL files.
No path fix to investigation reports or formalization packages is required.

---

## Recommendations for Cycle 005

1. **Pipeline fix:** Correct the phi_match=true labeling for arithmetic n=5, seeds 1
   and 3 in `lrc_efficiency_runtime_validation.csv`.

2. **Column naming:** Rename phi_match to something more specific across pipelines:
   - In 000044 context: `phase_count_match` (detected_phases == phi(n))
   - In 000056 context: `unique_phases_match` (unique_phases == phi_n)

3. **000056 re-queue:** Re-submit CLAIM-LRC-000056 to quorum with the corrected
   formalization package. The corrected claim is adjudicable and the arithmetic finding
   is strong.

4. **Cross-dataset clarification:** Document in the pipeline's column registry that
   phi_match is computed only for families where the phi(n)-phase hypothesis applies.
   Empty-string values must be distinguished from explicit NO values in all reports.

5. **New data generation for CLAIM-LRC-000044-EXT-001:** Generate arithmetic rows for
   n ∈ {31..50}, 10+ seeds each, to test whether the phi/2 ceiling holds and whether
   coverage continues to decline. Include n=5 at more seeds to resolve the prime-vs-
   composite divergence at phi_n=4.

6. **Expose seed-to-sequence mapping in 000044:** Re-run with base/delta columns exposed
   (as in 000056) to explain why n=5 consistently gives dp=1 while composite n=8,10,12
   give dp=2, and why seeds 1,3 at n=5 produce the bug dp=3. Without this, the n=5
   anomaly cannot be explained from data alone.

7. **Test the squarefreeness hypothesis:** Generate composite n values: n=21=3×7 (squarefree),
   n=35=5×7 (squarefree), n=36=4×9=2²×3² (non-squarefree), n=45=9×5=3²×5 (non-squarefree).
   If squarefree composites are always deterministic and non-squarefree are not (except
   2-powers and 2²×odd), this would be a strong structural signal.

---

## Verification Queries

To reproduce the phi_match value inventory in 000056:
```python
import csv, collections
path = "lrc_validation_large_1759239075705.csv"
counts = collections.Counter()
with open(path, newline='') as f:
    for row in csv.DictReader(f):
        counts[(row['family'], row['phi_match'])] += 1
# Expected: (arithmetic,YES)=55000, (perturbed,NO)=55110, (geometric,'')=55000, (random,'')=55000
```

To reproduce the bug in 000044:
```python
import csv
path = "lrc_efficiency_runtime_validation.csv"
for row in csv.DictReader(open(path, newline='')):
    if row['family']=='arithmetic' and row['phi_match'].lower()=='true':
        print(row['n'], row['phi'], row['detected_phases'], row['seed'])
# Expected: n=5, phi=4, detected_phases=3, seeds 1 and 3
```

---

## Finding 7: Prime-n Exception Analysis — Why Law 3 Fails at n=11, 13, 14 (2026-02-28)

**Source:** `lrc_validation_large_1759239075705.csv`, arithmetic rows only, n ∈ {9..15}.
**Context:** CLAIM-LRC-000056-EXT-001 Law 3 (`mode(iso|n) = 3·phi_n`) holds for 8/11 n values;
exceptions at n=11, 13, 14. This finding investigates the mechanistic cause.

### 7.1 Root Cause: iso=3·phi_n Frequency Falls Below a Competing Value

For each n, the global mode equals 3·phi_n **if and only if** iso=3·phi_n is the single most
frequent iso value across all 5,000 arithmetic rows for that n. The exceptions occur because
another iso value accumulates more counts:

| n  | phi | 3·phi | #(iso=3·phi) | #(mode) | mode | iso=3·phi rank |
|----|-----|-------|-------------|---------|------|---------------|
| 9  | 6   | 18    | 2786 (55.7%)| 2786    | 18   | 1st ✓         |
| 10 | 4   | 12    | 2396 (47.9%)| 2396    | 12   | 1st ✓         |
| 11 | 10  | 30    | 1017 (20.3%)| 1339    | 32   | 2nd ✗         |
| 12 | 4   | 12    | 2146 (42.9%)| 2146    | 12   | 1st ✓         |
| 13 | 12  | 36    | 755 (15.1%) | 1168    | 40   | 3rd ✗         |
| 14 | 6   | 18    | 995 (19.9%) | 2126    | 20   | 2nd ✗         |
| 15 | 8   | 24    | 1408 (28.2%)| 1408    | 24   | 1st ✓         |

**Conformity threshold:** n=15 conforms at 28.2%; n=14 fails at 19.9%. Despite the exceptions,
iso=3·phi_n remains in the **top 3** most frequent values for all seven n values.

### 7.2 Per-Delta Mode Alignment

With 20 distinct delta values per n, the fraction of delta values where the per-delta mode
equals 3·phi_n determines global conformity:

| n  | phi | 3·phi | deltas with mode=3·phi | fraction | global mode |
|----|-----|-------|----------------------|----------|------------|
| 9  | 6   | 18    | 15/20                | 75%      | 18 ✓       |
| 10 | 4   | 12    | 10/20                | 50%      | 12 ✓       |
| 11 | 10  | 30    | 5/20                 | 25%      | 32 ✗       |
| 12 | 4   | 12    | 9/20                 | 45%      | 12 ✓       |
| 13 | 12  | 36    | 6/20                 | 30%      | 40 ✗       |
| 14 | 6   | 18    | 4/20                 | 20%      | 20 ✗       |
| 15 | 8   | 24    | 8/20                 | 40%      | 24 ✓       |

At no delta value is the per-delta mode strictly below 3·phi_n for n=14: all 20 delta
values have min(iso) = 3·phi_n = 18 and mode ∈ {18, 20, 22}. The distribution for n=14
is bounded below by 3·phi_n — the mode is simply 3·phi_n + 2 in most cases.

### 7.3 n=14 Sub-Law: iso ≥ 3·phi_n for All Rows

For all 5,000 arithmetic rows with n=14, `isolation_count ≥ 18 = 3·phi(14)`.
This is a tighter lower bound than the universal Law 2 (`iso ≥ phi_n`) for this specific n.
No other n ∈ {9..15} satisfies this property (n=9: min=6=phi; n=10: min=5; n=15: min=23).

**Note:** This n=14 sub-law is an observation on 5,000 rows only and is not claimed to hold
beyond the tested parameter range.

### 7.4 Distribution Character by Exception Type

- **n=14**: Unimodal distribution supported on [18, 38], bounded below by 3·phi=18.
  Mode consistently near 20=3·phi+2 across most delta values.
- **n=13**: Unimodal but centered above 3·phi=36. Mode ranges 36–42 by delta;
  at most delta values min(iso) ≥ 36=3·phi.
- **n=11**: Bimodal distribution — a small "low-iso" cluster at iso≈14 (appearing at
  delta ∈ {0.14, 0.16, 0.18, 0.32, 0.36}) and a large "high-iso" cluster centered near
  30–36. The low-iso cluster accounts for ~8% of n=11 rows and depresses the iso=3·phi
  frequency, while the high-iso cluster pushes the global mode to 32 > 3·phi=30.

### 7.5 Primality Assessment

Two of three exceptions are prime (n=11, n=13); one is composite (n=14 = 2×7).
Two conforming n values are prime within {9..15}: none (n=11 and n=13 are the only primes).
**Conclusion: primality alone does not explain the exception.** n=14 (composite) fails, and
there are no primes among the conforming n ∈ {9,10,12,15} to serve as a counter-example.
The exception pattern appears correlated with `phi_n` being large relative to `n`:
- n=11: phi/n = 10/11 ≈ 0.909 (high)
- n=13: phi/n = 12/13 ≈ 0.923 (high)
- n=14: phi/n = 6/14 ≈ 0.429 (not high — composite, semi-prime)
This rules out a simple phi/n threshold as the driver.

### 7.6 Conclusion

Law 3 exceptions at n=11, 13, 14 are explained by **delta-specific distribution shifts** that
reduce the global frequency of iso=3·phi below a competing value. The mode law is not a sharp
structural threshold — it is a distributional dominance condition that breaks when the iso
distribution is either (a) bimodal with a low-iso cluster (n=11), (b) systematically elevated
above 3·phi (n=13), or (c) bounded below by 3·phi with the peak at 3·phi+2 (n=14).

**Recommendation for CLAIM-LRC-000056-EXT-001:** Law 3 is valid as stated for 8/11 n values.
A potential refinement — "mode(iso|n) = 3·phi_n OR iso ≥ 3·phi_n for all rows" — could capture
the n=14 sub-law as a separate observation. Law 3 does NOT need revision for n=11 or n=13.

---

## Finding 8: Unified Metric Harness — Formal Quantification of phi_match Collision (2026-02-28)

**Source files:**
- 000044: `lrc_efficiency_runtime_validation.csv` (SHA-256: 23ffbf...)
- 000056: `lrc_validation_large_1759239075705.csv` (SHA-256: 99b30d...)
**Harness outputs:** `/reports/harness/lrc_unified_metric_harness_*.{md,csv}`

### 8.1 Shared (family, n, seed) Grid — 8 rows (arithmetic, seed=0)

The harness identified 8 rows that can be directly compared across both datasets:
all arithmetic, n ∈ {5,7,8,10,11,12,13,15}, seed=0.

| family     | n  | detected_phases_44 | phi | unique_phases_56 | phi | phase_count_match | unique_phases_match | disagree? |
|------------|----|--------------------|-----|-----------------|-----|------------------|--------------------|----|
| arithmetic | 5  | 1                  | 4   | 4               | 4   | False            | True               | ✗  |
| arithmetic | 7  | 2                  | 6   | 6               | 6   | False            | True               | ✗  |
| arithmetic | 8  | 2                  | 4   | 4               | 4   | False            | True               | ✗  |
| arithmetic | 10 | 2                  | 4   | 4               | 4   | False            | True               | ✗  |
| arithmetic | 11 | 5                  | 10  | 10              | 10  | False            | True               | ✗  |
| arithmetic | 12 | 2                  | 4   | 4               | 4   | False            | True               | ✗  |
| arithmetic | 13 | 5                  | 12  | 12              | 12  | False            | True               | ✗  |
| arithmetic | 15 | 3                  | 8   | 8               | 8   | False            | True               | ✗  |

**Result: 8/8 rows disagree.** `phase_count_match` (000044) = False for all; `unique_phases_match`
(000056) = True for all. This is not a contradiction — it formalizes the column-name collision:
- 000044 `detected_phases`: counts phases found by **boundary traversal**. Arithmetic sequences
  achieve only 25–50% of phi(n) phases via this method (e.g., n=5: 1/4, n=7: 2/6, n=11: 5/10).
- 000056 `unique_phases`: counts phases defined by **isolation events**. Arithmetic sequences
  achieve 100% of phi(n) phases via this method for all 40,000 measured rows.

### 8.2 Shared (family, n) Grid — 16 cells

| family     | n  | phase_rate_44 | unique_rate_56 | measured_56 | interpretation            |
|------------|----|---------------|----------------|-------------|--------------------------|
| arithmetic | *  | 0.000         | 1.000          | 5000 each   | rates_disagree (all 8 n) |
| geometric  | *  | 1.000         | N/A            | 0 each      | unique_not_measured_in_56 |

Family-level totals on shared n values (n ∈ {5,7,8,10,11,12,13,15}):
- **Arithmetic**: 000044 phase_true = 0/48 rows; 000056 unique_true = 40,000/40,000 rows.
- **Geometric**: 000044 phase_true = 48/48 rows; 000056 unique_phases not measured (N/A for all 40,000 rows).

### 8.3 Scientific Conclusion (formal restatement of INV-PHI-MATCH-001)

The harness provides machine-verifiable confirmation of the phi_match column-name collision:

| Measurement | Method | Arithmetic | Geometric |
|---|---|---|---|
| `phase_count_match` (000044) | Boundary traversal | 0% match phi(n) | 100% match phi(n) |
| `unique_phases_match` (000056) | Isolation events | 100% match phi(n) | Not measured |

These two measurements are **topologically complementary**, not contradictory:
- Geometric boundary is **connected** → traversal reaches all phi(n) phases, isolation never occurs.
- Arithmetic boundary is **phase-isolated** → isolation events produce exactly phi(n) unique phases,
  but the traversal-based detector finds only a fraction (phase-ceiling finding, Finding 4).

**Cross-dataset isolation count for the 8 shared rows:**
n=5: 12 (=3·phi ✓), n=7: 20 (≠18=3·phi; specific delta/seed), n=8: 12 (=3·phi ✓),
n=10: 12 (=3·phi ✓), n=11: 32 (exception n), n=12: 12 (=3·phi ✓), n=13: 42 (exception n),
n=15: 30 (above 24=3·phi; specific seed). Law 3 observations in Finding 6 are consistent.

---

## Finding 9: n=6 Exhaustive Integer-Speed Search — No Counterexample to max_v=50 (2026-02-28)

**Search result:** `/reports/harness/lrc_search_v50_result.txt`
**Method:** Exact exhaustive search over gcd-normalized integer 6-tuples (v_1,...,v_6) with
all v_i ≤ 50, gcd(v_1,...,v_6) = 1.

### 9.1 Summary

| Parameter          | Value       |
|-------------------|-------------|
| n                  | 6           |
| max_v              | 50          |
| tested_tuples      | 2,061,046   |
| total_runner_checks| 12,366,276  |
| counterexample     | **None**    |
| completed_jobs     | 46/46       |
| elapsed            | 1045.34 s   |

### 9.2 Interpretation

Over 2 million integer speed tuples for n=6 walkers, with individual speeds up to 50,
no configuration was found that violates the LRC isolation property. This is a strong
empirical confirmation that the LRC conjecture holds for n=6 in the bounded integer domain.

The search is **exhaustive** within the stated bounds: every gcd-normalized integer 6-tuple
with max component ≤ 50 was checked. For comparison, C(50, 6) = 15,890,700 total 6-subsets
of {1..50}; the 2,061,046 tested tuples represent the gcd=1 primitive subset (~13%).

### 9.3 Boundary of the Result

This result does NOT establish:
- Absence of a counterexample for non-integer speeds (continuous speed vectors)
- Absence of a counterexample for max_v > 50 integer speeds
- Absence of a counterexample for n > 6

### 9.4 Next Step: Adversarial Real-Speed Search

The highest-value next run is the **adversarial real-speed threshold search near 1/6** —
the critical speed ratio where the conjecture's isolation condition is marginally satisfied
for n=6. This continuous search uses optimization + high-precision boundary/event verification
to probe whether a real-valued near-threshold configuration can defeat isolation. This is
orthogonal to the integer exhaustive search (which confirmed no integer counterexample);
the real-speed search targets the harder continuous domain.
