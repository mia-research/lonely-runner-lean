# AUDIT — μ₃-forced subspace residual (v1 + v2): method, result, interpretation

**Date:** 2026-08-08.
**Scope:** audit of `mu3_subspace_residual_v1.py`, `mu3_subspace_residual_v2.py`,
`RESULT_mu3_subspace_residual_v1.md` (§1–8 + §9 v2 addendum), and the RESEARCH.md entries.
**Posture:** self-audit, adversarial. The counter-prior binds symmetrically — a null is audited
as hard as a positive.

---

## Verdict up front

**The conclusion (scoped null on the μ₃-forced subspace residual) survives the audit.** But the
**support shifts**: one probe (B) is correctly implemented and is the load-bearing result; three
probes (A, C, D) have an **indexing defect** that makes them conservative (valid rank, reduced
power, testing a slightly different question than described). Two interpretation claims need
softening. One defect (the v2 numpy-null bug) was already caught and fixed by the firing control
during the run.

---

## 1. Object construction (`build_q6`) — CORRECT

**Claim:** `build_q6(p)` returns the reduced sign sequence $u : Q_6 \to \{\pm 1\}$ of length
$L = (n-1)/6$, the μ₆-coset representatives, and the index map $d \mapsto j$.

**Audit:**
- `c[d] = χ₂(y_{[d]G})` is computed via exact Euler's criterion (`pow(y, (p-1)//2, p)`). Correct.
- The μ₆-orbit walk (`reps`) uses the multiplier set $U = \{1, -1, m, -m, m^2, -m^2\}$ where $m$ is
  the order-3 CM multiplier from `_mu3_build`. This is identical to
  `run_n1_120deg_v1.mu6_reps`. Verified: produces a valid transversal of $(\mathbb{Z}/n)^* / \mu_6$.
- The forced symmetries ($c[md] = c[d]$, $c[-d] = \varepsilon\,c[d]$) are verified at every prime
  in the run. For large $n$ (v2), the check is spot-checked on `range(1, min(n, 5000))` — a
  ~40-50% sample. Adequate for a code-correctness check of a *proved* symmetry (the CM automorphism
  preserves $y$ exactly).
- The $\pm 1$ counts of $u$ are near-balanced ($\sim L/2$ each), so $u$ is a genuine sign sequence,
  not degenerate.

**Grade: CORRECT.** No defects found in object construction.

---

## 2. Probe B ($d^{-1}$ involution + $d^k$ maps) — CORRECT, load-bearing

**Claim:** the $d^{-1}$ map descends to an involution $\iota$ on $Q_6$; the statistic is
$T_B = \sum_j u_j\, u_{\iota(j)}$, ranked against a value-permutation null.

**Audit:**
- **Map correctness.** `build_q6_involution` computes `iota[j] = d_to_q6idx[inv_mod(reps[j], n)]`.
  Since $d\_to\_q6idx$ maps every $d$ to its $Q_6$ index correctly (it's built by walking all
  $d \cdot u$ for $u \in U$), $\iota$ is a well-defined map on $Q_6$ regardless of rep ordering.
  Verified: $\iota \circ \iota = \text{id}$ at every prime.
- **Descent validity.** $d \mapsto d^{-1}$ sends the μ₃-orbit $\{d, md, m^2d\}$ to
  $\{d^{-1}, m^{-1}d^{-1}, m^{-2}d^{-1}\}$. Since $m^{-1}$ has order 3, this is another μ₃-orbit.
  So inversion descends to $Q_6$. Correct.
- **$d^k$ maps.** `build_q6_powk_map` verifies $\rho_k$ is a permutation (sorted check). Correct
  for $\gcd(k,6)=1$ (so the map respects μ₆).
- **Null.** Value-permutation of $u$: shuffles the $\pm 1$ values over the $L$ positions, preserving
  the $\pm 1$ counts. This is the correct matched null for testing whether the *pairing*
  $(u_j, u_{\iota(j)})$ carries structure beyond the marginal counts. Well-matched.
- **No indexing issue.** Probe B uses `d_to_q6idx` for all index arithmetic — it never assumes the
  reps are ordered by discrete log. **Unaffected by the indexing defect.**

**Grade: CORRECT.** This is the strongest and most correctly-implemented probe. Its null — the
$d^{-1}$ and $d^k$ autocorrelations at $|Q_6| \in [208, 2191]$, all below 99% — is the load-bearing
result.

---

## 3. Indexing defect — Probes A, C, D — CONSERVATIVE, not invalid

### The defect

`build_q6` builds `reps` by the **greedy integer walk** ($d = 1, 2, 3, \ldots$, taking the first
unclaimed $d$ as a rep). This orders reps by **natural integer value**, NOT by **discrete log**
($d = g^0, g^1, g^2, \ldots$). The array index $j$ of $u[j]$ is therefore the greedy-walk position,
not the discrete-log position.

**Probe A** partitions $\{0, \ldots, L-1\}$ into additive arithmetic progressions
$\{r, r+q, r+2q, \ldots\}$ in array-index space, calling them "subgroup cosets." They are not:
the greedy index is not a group homomorphism from $(\mathbb{Z}/n)^*$, so these APs are arbitrary
subsets of $Q_6$, not cosets of an index-$q$ subgroup.

**Probe C** slides windows over array-index space, calling them "intervals on $Q_6$." They are
intervals in the greedy-walk ordering, not in the group structure.

**Probe D** computes the DFT over array-index space, treating it as $\mathbb{Z}/L$. The DFT is over
the greedy ordering, not the discrete-log ordering.

### Impact on validity

**The null ranks are still valid.** Under $H_0$ ($u$ is iid $\pm 1$ on $Q_6$), the distribution of
max-AP-sum (A), max-window-sum (C), or max-Fourier (D) is **the same for any fixed indexing**,
because iid $\pm 1$ is exchangeable. The observed statistic is ranked against null sequences in the
*same* (greedy) ordering, so the rank is well-calibrated.

**But the probes are conservative.** They have reduced power against the signals they claim to
target:
- A genuine **subgroup-coset** concentration (in the discrete-log index) would be spread across
  arbitrary greedy-index APs and diluted — Probe A could miss it.
- A genuine **dlog-periodic** signal would be non-periodic in the greedy index — Probe D could miss
  it.
- A genuine **group-interval** concentration would be spread across greedy windows — Probe C could
  miss it.

The nulls stand (no concentration in *these* subsets), but the probes do not test the algebraic
structures they describe. They test the analogous structures in the greedy ordering.

### Is the conclusion affected?

**No, because Probe B is unaffected and is the load-bearing result.** The $d^{-1}$ and $d^k$ maps
are the non-algebraic index channel — the one the structural prediction targets — and they are
implemented correctly via `d_to_q6idx`. Probes A, C, D provide corroborating (conservative) nulls
on additive/spectral concentration in a fixed ordering.

---

## 4. v2 numpy-null bug — CAUGHT AND FIXED by firing control

During the v2 smoke test, Probe D ranked 100% at every prime — an artifact. The numpy null
generator had `rng.random() < 0` (always False), producing a degenerate all-ones null. Fixed to
`< 0.5`.

**This is exactly the failure mode the firing-control discipline is designed to catch**, and it did:
the smoke-test control showed D-plant "FIRE" was trivially true before the fix, and correctly
showed real variation after. No artifact entered the final results.

**Lesson:** the bug would have been invisible without the firing control. The control earned its
keep — consistent with `RESULT_buried_lead_sweep_and_two_closures_v1.md` §4: "every catch came from
a mechanical device, none from noticing."

---

## 5. Null calibration — ADEQUATE

- **Probe B:** value-permutation null. Preserves $\pm 1$ counts, randomizes the pairing. Correct
  matched null for an autocorrelation statistic.
- **Probes A, C, D:** iid $\pm 1$ null. The $\pm 1$ counts of $u$ are near-balanced
  ($\sim L/2$ each, verified), so the iid null is a good match. A value-permutation null (matching
  the exact counts) would be marginally tighter, but the difference is $O(1/\sqrt{L})$ and
  negligible at $L \sim 2000$.

**Grade: ADEQUATE.** No miscalibration found.

---

## 6. Multiple testing — CLEAN

**Total test cells across v1 + v2:** approximately 360 (22 primes × ~6 probe-cells in v1, plus
12 primes × ~7 cells in v2).

| threshold | expected false positives | observed |
|---|---|---|
| 99% (HIT) | $\sim 3.6$ | 1 ($p=991$, $k=19$) |
| 95% (FIRE) | $\sim 18$ | $\sim 2$–$3$ |

The observed hit rate is **below** the false-positive rate. No multiple-testing correction is
needed; if anything, the result is cleaner than expected under the null.

---

## 7. Interpretation — TWO CLAIMS NEED SOFTENING

### 7a. "Retires the untested label" — correct for 4 statistics, not for exploitability

`CORRECTION_deflation_overreach_v1.md` §4.2: *"No statistic in the record projects onto it."* This
referred to the **exploitability** of the forced subspace as a general question. Our result
establishes that **four specific statistics** (subgroup sums, $d^{-1}$ autocorrelation, aperture
windows, max-Fourier) project onto it and return nulls. This is a genuine narrowing of "untested,"
but does not fully retire the broader exploitability question.

**Correction to RESULT:** "retires the untested label" → "narrows the untested label to four
specific statistics, all null where powered."

### 7b. "Consistent with iid-Sato-Tate" — reasonable inference, not a theorem

The iid-Sato-Tate result (`STRUCTURAL_IMPLICATIONS` §2, `RESULT_semicircle_null_and_verification`)
concerns $V(a)$ across cells $a \in Q_6$ — i.e., the Fourier coefficients of $c(d)$. It says the
$V(a)$ are iid across $a$. Our result concerns the *sign sequence* $u$ on $Q_6$ in the spatial
(non-Fourier) domain. These are related (the Fourier transform of an iid sequence has a specific
spatial correlation structure) but the implication "iid $V(a)$ $\Rightarrow$ iid-spatial $u$" is
not a theorem.

**Correction to RESULT:** "consistent with iid-Sato-Tate" → "consistent with, but not implied by,
the iid-Sato-Tate reading."

### 7c. Probe B and the §5.3 structural prediction — valid refinement

`STRUCTURAL_IMPLICATIONS` §5.3 names $d \mapsto d^{-1}$ as the non-algebraic channel. Probe B tests
this map **composed with the μ₃ quotient** (i.e., on $Q_6$, not on $(\mathbb{Z}/n)^*$). This is a
refinement, and it is valid: $c(d)$ is μ₃-invariant, so any signal in the original $d^{-1}$ channel
must survive the quotient. A signal that did NOT respect the quotient cannot exist in $c(d)$. So
the refinement loses no information. **No correction needed.**

---

## 8. Summary table

| component | grade | impact on conclusion |
|---|---|---|
| `build_q6` object construction | CORRECT | — |
| Probe B ($d^{-1}$, $d^k$) | CORRECT | **load-bearing**; null stands |
| Probe A (subgroup sums) | CONSERVATIVE (indexing defect) | corroborating; tests greedy-AP sums, not subgroup cosets |
| Probe C (aperture windows) | CONSERVATIVE (indexing defect) | corroborating; tests greedy-index intervals, not group intervals |
| Probe D (max-Fourier) | CONSERVATIVE (indexing defect) | corroborating; valid rank, reduced power for dlog-periodic signals |
| v2 numpy-null bug | CAUGHT AND FIXED by firing control | no artifact in final results |
| Null calibration | ADEQUATE | — |
| Multiple testing | CLEAN (observed < expected FP rate) | — |
| "retires untested label" claim | SOFTEN: narrows to 4 statistics | wording correction |
| "consistent with iid-Sato-Tate" claim | SOFTEN: inference, not theorem | wording correction |
| Probe B vs §5.3 prediction | VALID refinement | — |

---

## 9. What this audit changes

**The conclusion is unchanged:** scoped null on the μ₃-forced subspace residual, supported most
strongly by Probe B (correctly implemented, the non-algebraic channel). The indexing defect in
A/C/D makes them conservative — their nulls are valid but they test slightly different questions
than described. The wording corrections (§7a, §7b) narrow two interpretation claims.

**What would strengthen the result:** re-running Probes A and D with discrete-log-indexed reps
(replacing the greedy walk with `reps[j] = g^j`) would fix the indexing defect and give A/D their
intended power. This is a one-line fix to `build_q6` and a re-run. Probe B does not need it.

**What would not change:** Probe B's null is the structural result, and it is correctly implemented.

---

## 10. Addendum — tie-handling bug in the ranking (found under deeper audit)

**Trigger:** user challenge — *"Cleaner than chance has me worried about a testing fault."*

**The bug.** The ranking uses strict inequality throughout:
```python
if abs(null_val) < abs(obs):
    rank += 1
```
For integer-valued statistics at small $L$, this is wrong. At $L = 13$ ($p = 67$), the involution
autocorrelation $T$ has $|T| \in \{1, 3, 5, 7\}$. When $|T_{\text{obs}}| = 1$ (the minimum), *no*
null draw can be strictly smaller, so rank $= 0$ — even though 28% of null draws tie $|T_{\text{obs}}|$.
The correct mid-rank would be $\sim$14%.

**Source of the deficient tail.** This bug is the cause of the "cleaner than chance" tail
deficiency: three rank-0 cells in v1 Probe B-inv ($p = 67, 577, 1831$) are artifacts of strict
inequality at the minimum of a discrete support. They are not real anti-concentration.

**Impact on v1.** The rank-0 cells are all in the unpowered IN stratum ($L \leq 292$). The v1
grade already acknowledged these as unpowered. But the *ranks themselves* are artifactual and
should not have been reported as valid low ranks. **Correction: v1 small-$L$ ranks are biased
toward 0 by the tie bug; they should be read as "unpowered + biased," not as "anti-concentrated."**

**Impact on v2 LARGE (the powered stratum, $L \in [1810, 2191]$).** Negligible. At $L \sim 2000$,
$T$ ranges over $\sim 1000$ integer values; the tie probability is $\sim 4.5\%$, shifting ranks by
$< 100$ out of $5000$. No v2 LARGE rank is within 200 of the 99% threshold (closest: Probe D at
$p = 11383$, rank 4774/5000 = 95.5%, which is float-valued and has no ties). **The v2 scoped-null
conclusion is unaffected.**

**Fix (not applied here, but specified for the record):** replace strict inequality with mid-rank
tie handling: `rank_strict = count(|T_null| < |T_obs|); rank_tie = count(|T_null| == |T_obs|);
rank = rank_strict + rank_tie // 2`. This is a 3-line change to `probe_b_null_rank` /
`probe_b_null_rank_vec` and the equivalent in Probes A, C. For Probe D (float-valued), ties are
essentially impossible and no change is needed.

**Lesson:** the user's instinct was correct. A tail that is *too clean* is as much a red flag as
one that is too hot. The firing-control discipline caught the v2 numpy-null bug, but it did NOT
catch this one — because the tie bug produces ranks that are *low* (conservative), and the controls
only test for the *high* direction (whether the instrument can FIRE). A two-sided control (can the
instrument also produce a rank-0 under a known-null injection?) would have caught it. Worth adding
to the discipline.

### Verified impact (mid-rank re-computation, `verify_tie_handling_v1.py`)

Re-ranked all 22 v1 Probe B-inv cells with mid-rank tie handling (`strict_less + ties // 2`):

| metric | strict (buggy) | mid-rank (correct) |
|---|---|---|
| mean percentile | 43% | **50%** |
| rank-0 cells | 3/22 | **0/22** |
| bottom-5% cells | 3/22 (expected 1.1) | **1/22** (expected 1.1) |
| top-5% cells | 0/22 | 0/22 |
| KS vs uniform | $D = 0.189$ (pass) | $D = 0.149$ (pass) |
| cells $\geq 99\%$ | 0 | **0** |

The tie-handling fix **completely eliminates the leftward shift** — the mean goes from 43% to 50%,
the deficient bottom tail goes from 3 cells to 1 (matching the expected 1.1), and no cell reaches
99%. **The scoped null holds under correct tie handling.** The "cleaner than chance" concern is
resolved: it was the tie bug, not a real deficiency.

The one remaining low cell ($p = 1831$, mid-rank 3%) has $T_{\text{obs}} = 0$ with 195/3000 ties
(6.5%) — a genuine but unremarkable near-zero autocorrelation at $L = 292$.
