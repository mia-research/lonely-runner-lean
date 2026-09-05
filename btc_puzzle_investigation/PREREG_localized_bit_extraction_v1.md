# PRE-REGISTRATION — Localized Bit Extraction from Single-Point Geometry (v1)

**Status:** PRE-DATA. Written before any measurement. No data has been collected.
**Date:** 2026-07-20
**Binding on:** any run reporting results for the "local DLP-free feature -> scalar bit" question.
**Deviations:** any departure from this file must be listed in
`PREREG_localized_bit_extraction_v1_DEVIATIONS.md`. A deviation is not necessarily wrong —
it is necessarily disclosed.

---

## 0. OBJECT

**The object measured:** the joint distribution, over the group `E(F_p)` of prime order `n`, of
the pair

```
( F(P_d) , T(d) )        d = 1 .. n-1,   P_d = [d]G = (x_d, y_d)
```

where `F` is a local, DLP-free function of the affine coordinates of a **single** point (plus, in
family E, of points obtained from `P_d` by a fixed number of group operations), and `T` is a
function of the scalar `d` alone.

This is the object, not a proxy: the question "does a local geometric feature of `P_d` carry
information about `d`" is exactly the question "is `F(P_d)` statistically dependent on `T(d)`".
The map `d -> P_d` is a bijection, so the joint distribution is a well-defined finite object,
computed exhaustively (not sampled) for each `p` in scope.

**Tautology check (Constraint 1).** Feature and target are disjointly constructed **by
construction and by mechanism**:

- `F` takes as input only a tuple of field elements `(x, y)` (and, for family E, coordinates of
  `P_{d+1}-P_d`, `P_{d+2}-P_d`, `P_{2d}` — computed by group operations on `P_d` and `G`, never
  from `d`).
- `T` takes as input only the integer `d`.
- **Mechanical enforcement, mandatory:** the feature stage is executed on the point array with the
  index vector withheld. Implementation: build `pts = [(x_d, y_d) for d in 1..n-1]`, then compute
  `feat = [F(pt) for pt in pts]` inside a function whose signature accepts only `pts` and whose
  body is asserted (by test) to be **permutation-equivariant**: for a random permutation `pi`,
  `F_stage(pi(pts)) == pi(F_stage(pts))` must hold exactly. A function that could read `d` cannot
  pass this test. This assertion is a **run-blocking precondition**; if it fails the run aborts and
  reports no numbers.

This is the specific defense against the prior `r = v - w` vs `w` failure (spurious MI `z ~ +5000`
invisible to a shuffle control). That artifact arose because feature and target shared an
algebraic component. Here no component of `d` enters `F` by any path, and the equivariance
assertion is the decidable witness.

**Family E caveat, stated now:** `P_{2d}` is `[2]P_d`, a local group operation on the point; it
does not use `d`. `P_{d+1} - P_d = G` is **constant** and therefore carries zero information by
construction — it is retained in the grid only as an internal degenerate control that must produce
`G = 0` on every target (see §4b). `P_{d+2} - P_d = [2]G` likewise. **Pre-committed:** these two
constant cells are the *forced-null* rows; if either shows significance the pipeline is broken and
the entire run is void.

---

## 1. STATISTIC

Exactly one per-cell statistic, named now.

For a cell `(F, T)` with feature alphabet of size `a` and target alphabet of size `b`, form the
exact integer contingency table `N_ij = #{ d in 1..n-1 : F(P_d)=i, T(d)=j }`, with
`N = n-1`, row sums `N_i.`, column sums `N_.j`.

**Primary statistic — pooled likelihood-ratio (G-test):**

```
G(F,T) = 2 * sum_{i,j, N_ij>0}  N_ij * ln( N_ij * N / (N_i. * N_.j) )
```

Null distribution: `G ~ chi2` with `df = (a-1)(b-1)`.
Reported as a two-sided tail probability `P_cell = Pr[chi2_df >= G]`.

`G` is pooled over all `a*b` cells of the table and over all `N` scalars. It is **not** a
max-over-cells: a max of noisy per-cell deviations is upward-biased and low-power, and is
prohibited by this spec. Per-cell residuals may be *displayed* for characterization but may never
be used as a test statistic.

**Secondary statistic — family omnibus (diffuse leakage, aimed at "a little everywhere"):**

```
G_family = sum over all K enumerated cells of G(F,T)
df_family = sum over all K cells of df(F,T)
```

compared to `chi2_{df_family}`. This is a single pooled number that has power against many small
dependencies which individually miss the family-wise threshold. It is reported unconditionally
alongside the per-cell results.

**Directional/structural readout (mandatory, not a test):** for every cell reported at any
significance level, the run must also emit the **standardized residual matrix**
`R_ij = (N_ij - N_i.N_.j/N) / sqrt(N_i.N_.j/N)` and name the leading structure (which feature
value pairs with which target value, and whether the pattern is `mu6`-equivariant, sextant-indexed,
or flap/core-split). A magnitude alone is not an output. See §9.

---

## 2. NULL CONSTRUCTION (matched control)

Two nulls. Both preserve **both marginals exactly** (Constraint 3: high bits of `d` have skewed
marginals because `n` is not a power of two; skew is preserved because the target vector is never
altered).

### 2a. Matched null — group-automorphism relabeling (PRIMARY)

For a uniformly random `t` in `2..n-1`, pair

```
( F(P_{t*d mod n}) , T(d) )        d = 1..n-1
```

**Preserves:** the entire point set `{P_d}`, every geometric law of the curve, the exact multiset
of feature values, every within-feature structure (sextant statistics, flap/core proportions,
`mu6` orbit structure, character distributions), and the exact target marginal.
**Destroys:** only the specific pairing between the geometric feature and the *particular*
scalar labeling — i.e. exactly the hypothesis under test.

This is the correct matched null for this readout because `d -> t*d` is an automorphism of the
scalar group inducing a bijection of `E(F_p)`; it cannot destroy any symmetry that the feature has
by definition. (This is the fix for the prior "6-7 sigma soft shadow" failure, where a plain
shuffle destroyed a symmetry the readout possessed by definition.)

**Caveat pre-stated:** any dependence that is invariant under `d -> t*d` for all `t` survives this
null and is therefore **invisible** to it. Such dependence is exactly a statement about the feature
marginal alone, not about `d`; it is out of scope for the leakage question and is separately
reported by §4b.

### 2b. Secondary null — full permutation shuffle

Uniform random permutation of the feature vector against the untouched target vector. Preserves
both marginals exactly, destroys all pairing. Retained **only** as a cross-check on the chi2
calibration of `G`; it is *not* the matched control and no verdict rests on it alone.

### 2c. Calibration requirement

For each `p` in scope: 200 draws of null 2a and 200 of null 2b. The empirical distribution of `G`
per cell must match `chi2_df` with Kolmogorov-Smirnov `p > 0.01`. If calibration fails for a cell,
that cell's `P_cell` is replaced by the **empirical** null quantile from 2000 draws of null 2a, and
this substitution is disclosed per cell. Cells with expected count `< 5` in more than 20% of table
entries are **dropped from the family before the run** (criterion fixed now, applied to marginals
which are computable without any feature/target pairing) and listed explicitly; this is a
pre-registered filter, not a post-hoc one. Any filtering after the pairing is computed is
prohibited.

---

## 3. PLANT CONTROL AND POWER

**Plant construction.** For a target `T` with alphabet `b`, and effect size `e`, build a synthetic
feature

```
F_plant(d) = T(d)                     with probability (1+e*(b-1)/... )   -- binary case below
```

Concretely, for **binary** `T` (all bit_k, Hamming-parity, and the m=3,5,7 residues binarized as
`[T(d)=0]`), the planted feature is

```
F_plant(d) = T(d)         with probability (1+e)/2
           = 1 - T(d)     with probability (1-e)/2
```

independently per `d`, using a seeded CSPRNG. For alphabet `b > 2`, agree with `T(d)` with
probability `1/b + e*(b-1)/b`, else uniform on the other `b-1` values.

The plant is inserted as an **additional row of the same pipeline** — identical table
construction, identical `G`, identical family-wise correction — so that whatever suppresses a real
signal also suppresses the plant.

**Ladder (fixed now):**

```
e in { 0.500, 0.250, 0.100, 0.050, 0.020, 0.010, 0.005, 0.002, 0.001, 0.0005 }
```

30 independent plant replicates per `(e, p)`. **Detected** at level `e` means: the planted cell
clears the family-wise threshold of §4 in >= 27 of 30 replicates (>= 90%).

**Power readout.** `e_min(p)` := the smallest ladder `e` detected at `p`. This number is the
experiment's power and **must be printed adjacent to every null statement in every output
document**, together with `p` and `n`. A null without `e_min` attached is, by this pre-registration,
not a result.

**Analytic expectation (stated now, not a substitute for the measurement).** For binary/binary,
`G ~= N * e^2`. With `N ~ 10^5` and a family-wise chi2_1 threshold near 20, this predicts
`e_min ~ sqrt(20/10^5) ~ 0.014`. The *reported* power is the empirical ladder value, not this
estimate. If the empirical `e_min` exceeds 3x this estimate, the pipeline is treated as attenuating
and the run is flagged for repair before any null is reported.

**Hard rule (Constraint 2).** If the plant does not fire at the top of the ladder (`e = 0.5`), the
null is uninformative and **no null conclusion may be drawn** — full stop. The output in that case
is "pipeline defect", not "no leakage".

---

## 4. FAMILY, GRID, AND MULTIPLE-COMPARISON RULE

### 4a. The grid is enumerated and frozen here

**Features (`F`), by family:**

| id | family | feature | alphabet a |
|---|---|---|---|
| A1 | A | `eps(x_d)` flap class | 3 |
| A2 | A | signed flap `sigma(x_d)` in {-1,0,+1} | 3 |
| A3 | A | flap indicator `[sigma != 0]` | 2 |
| A4 | A | sextant index of `eis(x_d)` | 6 |
| A5 | A | normalized cap distance `|u-v|` binned at the 1/2 threshold (reduced coords) | 2 |
| A6 | A | `|u-v|` quartile bin | 4 |
| A7 | A | norm defect `enorm(eis(x_d))/p` quartile bin | 4 |
| A8 | A | `u mod 2` | 2 |
| A9 | A | `v mod 2` | 2 |
| A10 | A | `(u - v) mod 3` | 3 |
| B1 | B | `chi2(y_d)` (quadratic character) | 2 |
| B2 | B | `chi2(x_d)` | 2 |
| B3 | B | `chi3(x_d)` (cubic character, p = 1 mod 3) | 3 |
| B4 | B | `sign(y_d) = [y_d < p/2]` | 2 |
| B5 | B | `y_d mod 2` | 2 |
| B6 | B | `x_d mod 2` | 2 |
| B7 | B | `x_d mod 6` | 6 |
| B8 | B | `sign(x_d) = [x_d < p/2]` | 2 |
| C1 | C | `mu3` orbit position of `x_d` under `x -> beta*x` | 3 |
| C2 | C | `mu6` orbit position (`mu3` x `y -> -y`) | 6 |
| C3 | C | `mu6` orbit canonical-representative sextant | 6 |
| D1 | D | `sigma(x_d) * chi2(y_d)` | 5 (values -1,0,1 x sign, collapsed) |
| D2 | D | `chi2(y_d)` restricted to flap (`sigma != 0`), else "n/a" | 3 |
| D3 | D | `chi2(y_d)` restricted to core (`sigma = 0`), else "n/a" | 3 |
| D4 | D | joint `(eps, chi2(y))` | 6 |
| E1 | E | `eps(x)` of `P_{2d}` | 3 |
| E2 | E | `chi2(y)` of `P_{2d}` | 2 |
| E3 | E | sextant of `eis(x)` of `P_{2d}` | 6 |
| E4 | E | joint `(eps(x_d), eps(x_{2d}))` | 9 |
| E5 | E | `eps(x)` of `P_{d+1} - P_d` | 3 | **FORCED-NULL (constant)** |
| E6 | E | `eps(x)` of `P_{d+2} - P_d` | 3 | **FORCED-NULL (constant)** |

**Targets (`T`):**

| id | target | alphabet b |
|---|---|---|
| T-b`k` | `bit_k(d)`, `k = 0 .. floor(log2 n)` (17 targets at `n ~ 10^5`) | 2 |
| T-m3 | `d mod 3` | 3 |
| T-m5 | `d mod 5` | 5 |
| T-m7 | `d mod 7` | 7 |
| T-hw | `HammingWeight(d) mod 2` | 2 |
| T-w2 | low 2-bit window `d mod 4` | 4 |
| T-w3 | low 3-bit window `d mod 8` | 8 |
| T-w2h | 2-bit window at bits (k0,k0+1), `k0 = floor(log2 n)/2` | 4 |
| T-w3h | 3-bit window at bits (k0,k0+1,k0+2) | 8 |

**Family size:** `K = 30 features x 25 targets = 750` cells at `n ~ 10^5` (the count of `bit_k`
targets varies with `p`; the exact `K` for each `p` is computed from `n` alone, before pairing, and
printed). The two FORCED-NULL feature rows are counted in `K`.

**No cell may be added, removed, or re-binned after the pairing is computed.** Binning rules above
(quartiles, thresholds) are defined on the feature marginal only, which is target-independent.

### 4b. Additional forced rows (control rows that must behave)

- **Must-fire rows:** the plant ladder (§3).
- **Must-not-fire rows:** E5, E6 (constant features); plus a **random-feature row** (uniform random
  labels with the same marginal as A1) for each target.
- **Marginal-only row:** feature marginals reported alone, to identify dependence invisible to
  null 2a (§2a caveat).

If a must-not-fire row fires, the run is **void** and reports no verdicts.

### 4c. Family-wise rule (fixed now)

**Holm-Bonferroni** at family-wise error rate **alpha = 0.01**, applied across all `K` cells for a
given prime `p`, treating each `p` as its own family. Equivalently, sort `P_(1) <= ... <= P_(K)`
and reject `P_(i)` while `P_(i) <= 0.01 / (K - i + 1)`.

**Secondary reporting (not a verdict):** Benjamini-Hochberg at FDR = 0.05 is computed and printed
for characterization. A BH-only hit is labeled **SUGGESTIVE** and is routed to §5 replication; it
is never called a finding on its own.

**Omnibus:** `G_family` vs `chi2_{df_family}` at alpha = 0.01, a single separate test.

---

## 5. OUT-OF-SAMPLE REPLICATION RULE

No cell is **named** until it replicates. (Constraint 5; two prior chance patterns died here.)

**Discovery set:** `p_0` = the largest prime-order curve produced by
`prime_order_curve(lo,hi)` with `p = 1 mod 3` and `n < 10^5`, with generator `G_0` = the first
generator returned.

**Replication set, fixed now:** four further primes `p_1..p_4` with `p = 1 mod 3`, prime `n`, drawn
from disjoint decades (`~10^2`, `~10^3`, `~10^4`, `~10^5`), and **two distinct generators each**
(`G` and `[s]G` for a fixed `s = 7`), giving **8 independent replication runs**.

**Replication criterion (all three required):**
1. the same `(F, T)` cell attains `P_cell < 0.01` **uncorrected** in **>= 7 of 8** replication runs;
2. the **sign/structure** of the leading standardized residual `R_ij` agrees across all replicates
   in which it fires (same feature-value <-> target-value pairing, up to the relabeling induced by
   the curve);
3. the effect size (Cramer's V) does not drop below `e_min(p)/2` in any firing replicate.

Failing (1) => **chance pattern, not named.** Failing (2) or (3) => **ABSTAIN** on that cell, and
it is listed as an open arm, not a closed one.

**Prime-ladder scaling arm.** For any cell passing replication, plot Cramer's V against `p` across
all 5 primes. **An exponent may be fit only if >= 6 distinct primes fire**, and never from fewer.
(This rule exists because a prior drill fit `|delta| ~ p^-0.36` from three points, two of which had
orbits of `n = 146` and `n = 3353`.) A minimum orbit size of `n >= 5000` is required for any point
entering a scaling plot; primes below that contribute to replication counting only.

---

## 6. SCOPE

- Curve: `y^2 = x^3 + 7` over `F_p`, `p = 1 mod 3`, `#E(F_p) = n` prime.
- Primes: five, spanning `~10^2` to `~10^5`; `n < ~10^5`.
- Scalars: **exhaustive**, `d = 1 .. n-1` (not sampled).
- Generators: 2 per prime (`G`, `[7]G`).
- Features: the 30 enumerated in §4a. Targets: the 25 enumerated in §4a.
- Nulls: 200 draws each of 2a and 2b per prime; 2000 for empirical-quantile fallback.
- Plants: 10 ladder values x 30 replicates x 5 primes.
- `beta` calibration: `int1_frame_operator_v1.build(p)` calibrates `beta` from a **single hardcoded
  probe X = 12345** and is known to have failed at `p = 823`. **Mandatory override:** the caller
  re-derives `beta` by majority vote over >= 1000 random probes `X` and asserts the vote is
  unanimous-or-better-than-99%; a failed assertion aborts that prime, and the prime is reported as
  aborted (never silently dropped).

**Every number this run produces inherits this scope and may never be stated without it.**

---

## 7. EXACTNESS

- All field arithmetic, point arithmetic, lattice reduction, `eis`, `eps`, `enorm`, sextant index,
  characters, and all contingency counts: **exact integer / `Fraction`**. No floats in the signal
  path.
- `|u - v|` normalized threshold and quartile bins: computed as exact `Fraction` comparisons
  against the reduced basis, not floating comparisons.
- Characters `chi2`, `chi3`: exact modular exponentiation, values in `{-1,0,1}` / cube roots as
  exact residues.
- **Float carve-out (analytic size only, no key material in path):** the logarithm in `G`, the
  chi2 tail probability, Cramer's V, and the KS calibration statistic. These consume exact integer
  counts and produce a reported size only; no branch of the feature or target computation depends
  on them. `G` is additionally recomputed in `Fraction`-exact form up to the `ln` call for a
  cross-check on the 20 largest cells.

---

## 8. FALSIFICATION

The hypothesis under test is: **some enumerated local DLP-free feature of `P_d` is statistically
dependent on some enumerated function of `d`, at `p <= 10^5`.**

It is abandoned **for this grid and scope** if: the plant fires at `e_min <= 0.02` at every prime
(pipeline demonstrably sensitive), the must-not-fire rows stay silent, and **no** cell clears Holm
at any prime **and** `G_family` does not clear alpha = 0.01 at any prime **and** no BH-suggestive
cell survives §5 replication.

That outcome is written as a **bounded, scoped statement** (§10, cell N1) — never as "there is no
leakage".

---

## 9. STRUCTURE CLAUSE (a bound is not a verdict)

If nothing fires, the run must additionally report, for each feature family, **where the effect
would have to live to be invisible here**:

- the `mu6`-isotypic decomposition of the feature vector, and which isotypic components the
  enumerated targets project onto — a dependence supported entirely on an isotype orthogonal to
  every enumerated target is **not tested by this grid**;
- whether the residual matrix `R_ij`, though not significant, has a consistent **sign pattern**
  across primes (reported as a characterization, with no p-value);
- the subspace of scalar functions `T` **not** covered by the enumerated 25 (e.g. high-bit windows
  above `k0+2`, non-binary Hamming statistics, multiplicative-order-indexed functions).

"Signal" and "nothing" are not the only permitted outputs. Abstention with a named subspace is a
permitted and expected output.

---

## 10. PRE-COMMITTED OUTCOME TABLE (written before data)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| **P0** | Plant does **not** fire at `e = 0.5` | **PIPELINE DEFECT.** No null and no positive may be reported. Repair, then re-run. The run produces no verdict of any kind. |
| **P1** | Any must-not-fire row (E5, E6, random-feature) clears Holm | **RUN VOID.** Report the defect; no cell verdicts. |
| **P2** | Permutation-equivariance assertion fails | **RUN ABORTED** before statistics. Report abort; no numbers. |
| **P3** | `beta` majority vote non-unanimous at a prime | That prime **aborted and reported as aborted**; other primes proceed; family `K` recomputed per surviving prime. |
| **N1** | Plant fires at `e_min`; no cell clears Holm at any prime; `G_family` not significant; no BH-suggestive cell replicates | **SCOPED BOUNDED NULL:** "Across the 30 enumerated local DLP-free features x 25 enumerated scalar targets, on 5 prime-order curves `y^2=x^3+7` with `p = 1 mod 3`, `n < 10^5`, exhaustive over all `d`, no feature-target dependence was detected at family-wise alpha = 0.01. The detection floor was `e_min = <value>` per prime (agreement bias), i.e. dependencies with per-sample bias below `e_min` are not excluded." **This may not be written as "there is no leakage" and may not be generalized beyond `p <= 10^5` or beyond the enumerated grid.** §9 structure clause mandatory. |
| **N2** | As N1, but `G_family` **is** significant while no single cell clears Holm | **DIFFUSE-DEPENDENCE SIGNAL, not localized.** Report `G_family`, its df, and the top-20 cells by `G` as *characterization only*. Pre-committed next step: replicate `G_family` on the 8 out-of-sample runs; if it replicates in >= 7/8, name it as a diffuse effect and hand it to a new pre-registration aimed at the specific isotype carrying it. Do **not** name any individual cell. |
| **H1** | >= 1 cell clears Holm at the discovery prime, and passes all three §5 replication criteria | **NAMED FINDING, scoped.** Report the cell, `R_ij` structure, symmetry type, Cramer's V per prime, `e_min` per prime, and the scaling arm **only if >= 6 primes fire with `n >= 5000`**. Conclusion is stated as a scoped structural law for `p <= 10^5`; extrapolation to `2^256` is **explicitly forbidden** by this file (see §11). |
| **H2** | >= 1 cell clears Holm at discovery but fires in `< 7/8` replicates | **CHANCE PATTERN. Not named.** Reported as "did not replicate", with the discovery statistic printed. No mechanism may be proposed. |
| **H3** | Cell replicates in `>= 7/8` but residual structure (criterion 2) is inconsistent across primes | **ABSTAIN.** Listed as an OPEN ARM with the inconsistency described. Explicitly **not** a closure of that arm. Routed to a follow-up pre-registration. |
| **H4** | Cell replicates but Cramer's V falls below `e_min/2` in a firing replicate | **ABSTAIN** (criterion 3). Open arm; power-limited at the smaller primes. Pre-committed next step: extend the prime ladder upward, not re-analyze the existing data. |
| **H5** | Only a FORCED-NULL-adjacent family-E cell (E1-E4) fires | Treated exactly as H1/H2/H3 per its replication behavior. `P_{2d}` is a legitimate local feature; no special discount. |
| **S1** | A cell is BH-suggestive only (never clears Holm) and replicates `>= 7/8` | **SUGGESTIVE, OPEN ARM.** Named as a candidate, not a finding. Requires a new pre-registration with the cell as its single pre-specified target before it may be called a finding. |
| **S2** | Marginal-only row shows structure invisible to null 2a | Reported as a **feature-marginal law** (a statement about the curve's point geometry), explicitly **not** scalar leakage. Handed to the structural programme, not this one. |

**Nothing outside this table may be reported as a conclusion.** Post-hoc statistics computed on
this data go under a heading literally titled `EXPLORATORY (NOT PRE-REGISTERED)` and may not
override a fired outcome cell.

---

## 11. SCOPE / POWER LIMITATION — INCLUDING THE 2^256 GAP

This experiment measures `p <= ~10^5`. The target of ultimate interest is `p ~ 2^256`. The
following is committed **before** data:

1. **What this experiment has power against.** With `N = n-1 ~ 10^5` exhaustive samples and a
   Holm threshold at alpha = 0.01 over `K ~ 750` cells, the binary-cell detection floor is
   approximately `e ~ sqrt(chi2_1(0.01/750) / N) ~ 1.4 x 10^-2` in agreement bias (empirical
   `e_min` from §3 supersedes this estimate). It therefore has power against **scale-free**
   dependencies — laws whose per-sample bias does not shrink with `p` — and against slowly
   decaying laws over the measured decade range.

2. **What this experiment has NO power against.** Any dependence suppressed by square-root
   cancellation — the regime that Weil-type and Kohel-Shparlinski-type character-sum bounds
   describe, where a normalized bias behaves like `O(p^-1/2)` — has, at `p ~ 2^256`, a per-sample
   bias of order `2^-128`. Detecting a bias `e` requires `~ e^-2` samples; at `e ~ 2^-128` that is
   `~ 2^256` samples, i.e. the entire group. **This experiment has, by construction, zero power
   against square-root-suppressed leakage at cryptographic scale, and a positive result at
   `p <= 10^5` is fully consistent with total undetectability at `2^256` if the effect decays like
   `p^-1/2`.**

3. **The only permitted bridge.** Extrapolation to `2^256` is licensed **only** by an exponent fit
   from `>= 6` primes with `n >= 5000` (§5), and even then is reported as an extrapolation with its
   confidence interval and the explicit statement that no measurement above `10^5` was made.
   A fit from fewer points is prohibited by this file regardless of how clean it looks.

4. **A null here is a null at `10^5`.** It is not evidence about `2^256` in either direction. It
   bounds the size of scale-free leakage in the enumerated grid at the measured primes, and
   nothing more.

---

## 12. WHAT THIS EXPERIMENT DOES NOT TEST

Explicit, so that no result may be read as covering these:

1. **Non-local features.** Anything requiring more than O(1) group operations from `P_d`, any
   feature of a set of points, any feature indexed by the discrete log.
2. **Features outside the 30 enumerated.** In particular: higher-degree isogeny/lift invariants,
   formal-group / p-adic expansions, division-polynomial values, pairing-derived quantities,
   L-function or class-number invariants, and any `x`-only feature at modulus not in `{2,3,6}`.
3. **Targets outside the 25 enumerated.** High-bit windows above `k0+2`, full Hamming weight (only
   its parity is tested), NAF/wNAF digit statistics, continued-fraction or lattice-based functions
   of `d`, and `d mod m` for `m` not in `{3,5,7}` (and not a power of 2 via the window targets).
4. **Curves other than `y^2 = x^3 + 7`**, non-prime `n`, `p = 2 mod 3`, or non-prime-order
   subgroups. Nothing here speaks to composite-order or twist behavior.
5. **secp256k1 itself.** No measurement is made at `p ~ 2^256` (§11).
6. **Joint/multivariate feature combinations** beyond the four explicitly enumerated joints
   (D1-D4, E4). A dependence carried only by a 3-way or higher interaction is untested.
7. **Any generation-side / PRNG question.** Out of scope by project policy and by construction:
   `d` here ranges over the full group exhaustively, not over any key-generation distribution.
8. **Dependence invariant under `d -> t*d`** — invisible to the matched null 2a by design (§2a),
   reported separately as a feature-marginal law (outcome S2), never as scalar leakage.
9. **Cryptographic security claims of any kind.** Neither a null nor a positive here constitutes a
   statement about ECDLP hardness.

---

## 13. RUN CHECKLIST (all must be logged in the output)

- [ ] permutation-equivariance assertion PASSED (§0)
- [ ] `beta` majority vote >= 99% at every non-aborted prime (§6)
- [ ] `K` printed per prime, computed pre-pairing (§4a)
- [ ] dropped-cell list (expected-count rule) printed pre-pairing (§2c)
- [ ] null 2a and 2b calibration KS `p` per cell (§2c)
- [ ] plant ladder table; `e_min(p)` per prime (§3)
- [ ] must-not-fire rows: E5, E6, random-feature — all silent (§4b)
- [ ] Holm results; BH results labeled SUGGESTIVE (§4c)
- [ ] `G_family`, `df_family`, tail probability (§1)
- [ ] standardized residual structure for every reported cell (§1, §9)
- [ ] §9 structure clause emitted if nothing fires
- [ ] every stated number carries `(p, n, e_min)` (§6, §3)
- [ ] outcome cell from §10 named explicitly; conclusion copied verbatim from that cell
