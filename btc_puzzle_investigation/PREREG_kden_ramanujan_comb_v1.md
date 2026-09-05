# PRE-REGISTRATION — `k_den` Ramanujan-comb law (band best-approximation denominator)

**Status: SPEC ONLY. FROZEN before any level-set, run-count, endpoint table, or spectrum is
computed for any configuration in the confirmatory set. Decidable artifact.**
**Date 2026-07-23. Designed context-isolated by `experiment-designer`.**
Implementation target: `kden_ramanujan_comb_v1.py`. Source object: `band_residual(off, A, M)` in
`lift_band_spectral_v1.py`. Prior input (NOT re-verified here): `lift_band_joint_findings_v1.md` Part 2.

---

## 0. OBJECT

### 0.1 The object, named exactly

For a band exponent `bexp`, set `A = 2**(bexp-1)`; for a Farey cap `M`; for each integer offset
`off ∈ [0, A)`:

```
k_den(off; A, M) = argmin_{1 <= den <= M} | den*off - k(den,off)*A |,
      k(den,off)  = (2*den*off + A) // (2*A)      # nearest integer to den*off/A, ties round UP
      argmin ties broken to the SMALLEST den       # source: strict `e < best_e` in band_residual
```

Writing `θ = off/A ∈ [0,1)`, `|den*off − k*A| = A * ‖den·θ‖` where `‖·‖` is distance to the nearest
integer. So `k_den` is the **best-approximation-of-the-second-kind denominator of `θ` capped at `M`**.

**The object under test is the family of level sets**
```
L_q  =  { off ∈ [0,A) : k_den(off; A, M) = q },     q = 1..M
```
as subsets of the cyclic group `ℤ/A` — their **cardinality, their decomposition into maximal runs,
and the POSITIONS of those runs**. Not a spectrum, not a summary statistic: the level sets themselves.

`k_den` depends only on `(off, A, M)`. **No elliptic curve is involved.** The prior result's
"three curves (n = 2089, 8293, 33151)" axis is, for this object, purely the `A` axis; the curve
entered only through the constraint `2A ≤ n`. This is recorded as a scope correction, not a finding.

### 0.2 Hypothesis being pre-registered (Ramanujan comb)

**HYP-G (geometric premise).** `L_q` is, up to the `M`-cap and integer discretization, a disjoint
union of **exactly `φ(q)` intervals of `ℤ/A`, one centred on each fraction `j/q` with
`gcd(j,q) = 1`, `0 <= j < q`.**

**HYP-S (spectral consequence).** With `1_{L_q}` written as `Σ_{j prim} 1_{interval at jA/q}` and
**assuming all `φ(q)` intervals of a given `q` share a common width `w̄_q`**, the Fourier transform
factorizes through the Ramanujan sum
```
c_q(f) = Σ_{gcd(j,q)=1} exp(2πi j f / q) = μ(q/g)·φ(q)/φ(q/g),      g = gcd(q,f)
```
giving `k̂_den(f) ≈ Σ_q q · Ŵ(w̄_q, f) · c_q(f)`, hence a power spectrum built from a Ramanujan comb.

### 0.3 Tautology / forcing declarations (made BEFORE the run, discarded BY NAME)

- **T-1 (TAUTOLOGY — banned implementation).** Any "prediction" of `L_q` that, for each `off`,
  minimizes `|d*off − k*A|` over `d ≤ M` is a re-implementation of `band_residual`. Agreement then
  measures code equivalence and carries **zero** information about HYP-G. **The prediction module
  MUST derive interval endpoints in closed form from `(A, M, q, j)` only (§2.2), emit the endpoint
  table to disk, and hash it, BEFORE `k_den` is computed for that configuration.** Enforcement in §8.
- **F-1 (FORCED — statistic discarded).** If HYP-G is confirmed **off-by-off** (test H2b, §2.3), then
  the observed sequence *is* the predicted step function, so the predicted power spectrum equals the
  observed power spectrum **identically** and any correlation between them is `ρ = 1` by construction.
  **The statistic "correlation between the exact-geometry predicted spectrum and the observed
  spectrum" is therefore DISCARDED as forced and will not be computed or reported.** What survives is
  the *equal-width Ramanujan factorization* (H3, §2.4), which HYP-G does **not** force.
- **F-2 (FORCED cells excluded from tallies).** `q = 1` and `q = 2` have `φ(q) = 1`; any non-empty
  level set trivially yields one circular run, so these cells carry no information about `φ`. They are
  **excluded from every informative count**. `q = 1` additionally always contains `off = 0` (`e = 0`
  at `den = 1`), which is forced.
- **F-3 (INVARIANCE — banned null).** A cyclic rotation of the sequence leaves `|FFT|` **exactly**
  invariant. Rotation is therefore a zero-power null and **must not be used**.
- **T-2 (partially tautological control).** The **count** identity `#runs(L_q) = φ(q)` is *not*
  discriminating against the matched null of §3 (block-permutation preserves run counts exactly).
  Counts discriminate only against "wrong-centre-set" alternatives (§4 W1/W3). **The load-bearing
  discriminator against random placement is the run POSITION prediction (H2b), not the count (H2a).**
  H2a is reported as a coarse summary; H2b is the headline.

### 0.4 Derivation used to build the prediction (stated now, so it is not fitted later)

Write `θ = (j + η)/q`, `q ∤ d`, `u_d = (d·j) mod q ∈ {1..q−1}`. Then `‖qθ‖ = |η|` and
`‖dθ‖ = (1/q)·min(|u_d + dη|, |q − u_d − dη|)` for small `|η|`. Requiring `q` to win gives, in exact
rationals,

```
η_right(q,j) = min over d in [1,M], q ∤ d, of :  u_d/(q−d)   (only if d < q)
                                                 (q−u_d)/(q+d)
ξ_left (q,j) = min over d in [1,M], q ∤ d, of :  u_d/(q+d)
                                                 (q−u_d)/(q−d) (only if d < q)
```
Denominators `d = m·q` (`m ≥ 2`) give `‖dθ‖ = m|η| > |η|`: never binding. Since `u_d ≥ 1` and
`q − u_d ≥ 1`, both bounds are `≥ 1/(q+M)`, so each interval has half-width in `off` units
`≥ A/(q(q+M))`.

**Consequences fixed now:**
- `SAFE(q)` ⟺ `q(q+M) <= A` ⟹ interval length `≥ 2` ⟹ contains an integer `off` ⟹ non-empty run.
  `Q_safe = { q <= M : q(q+M) <= A }`.
- Two intervals of the same `q` are separated in `off` by `≈ A/q ≥ 1`, so runs never merge.
- Any `off` with `k_den(off) = q` satisfies `‖qθ‖ ≤ 1/(M+1)` (Dirichlet), hence lies within
  `1/(q(M+1))` of some `j/q`; and `gcd(j,q) = g > 1` would make `q/g` win. So `L_q` is *contained in*
  the union of the `φ(q)` primitive neighbourhoods. **HYP-G's containment direction is derivable.**

**Honesty statement, made before the run:** given §0.4, HYP-G is close to a theorem, and its
empirical check is therefore in part a code-correctness check. **The non-forced content of this
experiment is (i) the exact `off`-level endpoint positions across 8 fresh configurations, (ii) the
deficiency pattern `φ(q) − r̂_q` on unsafe `q` (which §0.4 predicts but does not trivially give), and
(iii) H3, whether the *equal-width Ramanujan factorization* actually governs the spectrum.** If H2b
confirms, the correct write-up says "the geometric premise is verified exactly at 8 configurations
and follows from the Dirichlet/three-distance argument in §0.4" — **not** "we discovered a law."

---

## 1. SCOPE (fixed now; every number produced inherits it and may never be stated without it)

### 1.1 Configuration sets

**SEEN / EXPLORATORY (in-sample; reported in a separate section; NEVER counted in any confirmatory
tally, never used to set a threshold, an exponent, or `F_max`):**

| id | bexp | A | M | note |
|---|---|---|---|---|
| S1 | 11 | 1024 | 32 | prior run, excess 5.4×, top \|f\|=12 |
| S2 | 13 | 4096 | 48 | prior run, excess 12.2×, top \|f\|=24 |
| S3 | 15 | 16384 | 64 | prior run, excess 28.0×, top \|f\|=24 |

**CONFIRMATORY set C (8 fresh configurations; no `(bexp, M)` shared with S1–S3; `bexp` and `M`
fully crossed so that neither the top-mode prediction nor the excess can be confounded with `M`):**

| id | bexp | `A = 2^(bexp−1)` | M | M factorization | M type | `Q_safe` | `F_max = min(2M², A/2)` |
|---|---|---|---|---|---|---|---|
| W1 | 17 | 65536 | 31 | 31 | **prime** | 1..31 | 1922 |
| W2 | 17 | 65536 | 36 | 2²·3² | **highly composite** | 1..36 | 2592 |
| W3 | 19 | 262144 | 41 | 41 | **prime** | 1..41 | 3362 |
| W4 | 19 | 262144 | 60 | 2²·3·5 | **highly composite** | 1..60 | 7200 |
| T1 | 12 | 2048 | 43 | 43 | **prime** | 1..28 | 1024 |
| T2 | 12 | 2048 | 45 | 3²·5 | composite | 1..28 | 1024 |
| T3 | 14 | 8192 | 101 | 101 | **prime** | 1..53 | 4096 |
| T4 | 14 | 8192 | 100 | 2²·5² | **highly composite** | 1..53 | 4096 |

- **W-block (`WIDE`):** `Q_safe = [1,M]` — every `q` predicted non-deficient. Tests the pure `φ(q)`
  count and the endpoint law.
- **T-block (`TIGHT`, `A < 2M²`):** `Q_safe ⊊ [1,M]` — the discretization deficiency is predicted to
  bite for `q > max Q_safe`. This is the non-trivial part of §0.4 and it is **out-of-sample** (the
  seen configs S1/S2 sat in this regime; S3 did not).
- **Prime/composite `M` contrasts at fixed `bexp`, pre-committed:** (W1,W2), (W3,W4), (T1,T2),
  (T3,T4). **T3/T4 (`M = 101` vs `100`) are adjacent** — the sharpest available contrast.
- **Pre-committed discriminating prediction:** the model of §0.2 says the comb depends on `M` only
  through the *cutoff* `q ≤ M`, so `M = 100` and `M = 101` must give nearly identical predicted top
  modes and nearly identical `R²_ram`. The competing "`M`'s own factorization drives the top mode"
  alternative predicts a visible difference across each pair. **This contrast is decided by the run,
  not by later reading.**

### 1.2 Fixed parameters
`kmax = 16` (legacy low-frequency mass, for comparability with S1–S3 only). `F_max` per table above.
`B = 999` matched-null draws. `α* = 1/60` (§5). Seeds: null RNG `seed = 20260723 + config_index`.
Everything else in §1.1. **Nothing in this section may be changed after any confirmatory number is
seen; a change is a disclosed deviation in `PREREG_kden_ramanujan_comb_v1_DEVIATIONS.md`.**

---

## 2. STATISTICS

Ordering: **H2b is PRIMARY** (object-level, exact integer, no float anywhere). H2a is a coarse
summary. H3 is the spectral arm and is subordinate to the H2b branch (§6).

### 2.1 Run extraction (exact integer, definition fixed now)
Treat `off ∈ [0,A)` as `ℤ/A`. A **maximal circular run** is a maximal cyclically-consecutive block of
offsets with equal `k_den`. If `k_den(0) = k_den(A−1)` the first and last linear blocks are joined
into **one** circular run. `r_q` := number of maximal circular runs with value `q`. Degenerate case
(one value occupying all of `ℤ/A`) counts as one run.

### 2.2 Prediction module (built and hashed BEFORE `k_den` is computed)
`predict_levelsets(A, M) -> endpoint_table`. For each `q ∈ [1,M]` and each `j ∈ [0,q)` with
`gcd(j,q) = 1`:
1. compute `η_right`, `ξ_left` as exact `Fraction`s by the §0.4 minima over `d ∈ [1,M]`, `q ∤ d`
   (integer cross-multiplication for every comparison; no float);
2. convert to `off` bounds via `η = (q*off − j*A)/A`, giving exact rational bounds on `off`;
3. take the integer candidates in the closed rational range; for the **at most 2 boundary integers at
   each end**, decide membership by evaluating the full constraint set over `d ∈ [1,M]` with the
   correct strictness (**strict** for `d < q`, **non-strict** for `d > q`, matching the source
   tie-break). Mark these offsets `boundary_decided = True`;
4. emit rows `(q, j, off_lo, off_hi, width, boundary_decided_flags)`;
5. **assert** no two predicted intervals overlap and no two intervals of the same `q` are adjacent.
   An assertion failure is a **derivation bug ⇒ HALT, fix, re-freeze the table, disclose** — it is
   NOT a finding and must not be reported as one.
Cost is `O(M · Σ_q φ(q))` and **never references any `off` outside a predicted interval**.
`r̂_q` := number of predicted intervals of `q` containing at least one integer `off`.

### 2.3 **H2b — PRIMARY. Exact off-by-off set identity.**
```
mismatch(config) = #{ off in [0,A) : k_den(off) != predicted_value(off) }
```
where `predicted_value(off) = q` if `off` lies in a predicted `q`-interval and `0` (unassigned)
otherwise. Exact integer. Reported alongside:
- `mismatch_interior` = mismatches at offsets NOT flagged `boundary_decided`;
- `mismatch_boundary` = mismatches at flagged offsets;
- per-`q` and per-`(q,j)` breakdown of every mismatch (individually listed, never summarized to a
  tag count).
**Informative unit (pre-committed):** the interiors of an interval are forced by contiguity, so the
informative content is the **number of predicted intervals `Σ_q r̂_q` and their `2·Σ_q r̂_q` endpoint
positions**, NOT the `A` offsets. Expected order `Σ_{q≤M} φ(q) ≈ 0.304·M²`; across C this is
≈ 9.6·10³ interval-position predictions (exact count emitted by the run). Boundary-decided offsets
are **excluded from the informative count** (§0.3 T-1: their decision reuses the constraint
machinery).

### 2.4 **H2a — count identity (coarse summary).**
For every `config` and every `q`: compare `r_q` (observed) to `r̂_q` (predicted) and to `φ(q)`.
Two sub-claims, both exact integers:
- **H2a-safe:** `r_q = φ(q)` for all `q ∈ Q_safe`.
- **H2a-tight:** `r_q = r̂_q` for **all** `q ∈ [1,M]`, including `q ∉ Q_safe` where `r̂_q < φ(q)` is
  predicted. **This is the out-of-sample deficiency prediction and is the non-trivial half of H2a.**
**Informative cell counts (computed now, from `φ` only, no data):**
`#{q ∈ Q_safe : φ(q) ≥ 2}` = W1 29, W2 34, W3 39, W4 58, T1 26, T2 26, T3 51, T4 51 → **314
informative safe cells**; unsafe cells `q ∈ [1,M] \ Q_safe` = T1 15, T2 17, T3 48, T4 47 → **127
informative deficiency cells**. `q ∈ {1,2}` (16 cells) excluded as forced (§0.3 F-2). W-block
contributes **zero** deficiency cells by design; this is disclosed, not discovered.

### 2.5 **H3 — spectral arm: does the EQUAL-WIDTH Ramanujan factorization govern?**
Not forced by H2b (§0.3 F-1). Define, from the *predicted* geometry only:
```
w̄_q     = mean predicted width of the q-intervals (exact Fraction, then float for the transform)
RAM(f)  = | Σ_{q=1..M} q · Ŵ(w̄_q, f) · c_q(f) |²      # equal-width Ramanujan comb
FLAT(f) = Σ_{q=1..M} q² · Ŵ(w̄_q, f)² · φ(q)           # incoherent / random-centre model, same widths
P_obs(f)= |FFT(k_den − mean)|²
```
`Ŵ(w,f) = sin(π f w / A)/(π f / A)` (Dirichlet kernel of a width-`w` window).
**Primary H3 statistic (one number per config, pooled across `f`, no max-over-cells):**
```
R2_ram(config) = 1 − Σ_f (log P_obs(f) − log RAM(f) − c)² / Σ_f (log P_obs(f) − mean_f)²
```
over `f ∈ [1, F_max]`, with `c` the single additive constant that minimizes the numerator
(an overall scale, the only free parameter — declared now, one parameter, fitted only as a scale).
`R2_flat` identically with `FLAT` in place of `RAM`. `ΔR2 = R2_ram − R2_flat`.
**Pooled confirmatory statistic:** `S_ram = Σ_{c ∈ C} R2_ram(c)` — a single number over the 8
configurations, ranked against the matched null of §3.

### 2.6 SECONDARY / CHARACTERIZATION statistics (pre-committed, reported with scope, no evidential
weight claimed if H2b confirms — see §6 branch A)
- **H3-HC.** "Highly composite with respect to `M`" is defined **now** as: `f` lies in the top decile
  of `D_M(f) = Σ_{q ≤ M, q | f} φ(q)` over `f ∈ [1, F_max]`. Statistic:
  `Δ_HC = mean_{f ∈ HC} log(P_obs(f)) − mean_{f ∉ HC} log(P_obs(f))`, ranked vs §3 Null-1.
- **H3-top.** The set `TOP3_pred` = three largest `RAM(f)` over `f ∈ [1,F_max]`, **emitted and hashed
  before `P_obs` is computed**. Point prediction: `argmax_f P_obs(f)/floor(f) ∈ TOP3_pred`. Recorded
  as a per-config hit/miss (8 cells). Disclosed: `argmax` over many `f` is upward-biased and
  low-power (this is why the prior "top mode 12/24/24" readout is demoted to secondary here).
- **H3-legacy.** Low-frequency excess `lf(kmax=16)/lf_floor` reproduced with the legacy Null-0, for
  comparability with S1–S3 only. Not confirmatory.
- **H3-resid.** If `S_ram` does not fire: decompose the residual `log P_obs − log RAM` against combs
  restricted to sub-families of `q` (`q` odd; `q | A`; `q` prime; `q` squarefree) and report which
  sub-family, if any, carries the residual. **This is the "effect lives in a subspace we are not
  projecting onto" branch and it is pre-registered, not improvised.**

---

## 3. MATCHED CONTROL (nulls)

- **Null-1 — PRIMARY MATCHED NULL: run-block cyclic permutation.** Decompose the observed sequence
  into its maximal circular runs `(value_i, length_i)`; apply a uniform random permutation to the run
  order; concatenate around `ℤ/A`.
  - **PRESERVES exactly:** the `k_den` value multiset; the run-length multiset; the pairing of each
    run's value with its length; piecewise-constancy; the number of runs per value `r_q`; total
    length `A`.
  - **DESTROYS only:** the arithmetic (Farey) *placement* of the runs — precisely the content of
    HYP-G. Structure surviving this null cannot be credited to piecewise-constancy.
  - **Note (checked at design time):** because the level sets tile `ℤ/A` exactly, "place `r̂_q`
    intervals of the observed widths at uniformly random non-overlapping centres" is *identical* to
    Null-1. There is therefore **one** hard matched null, not two.
- **Null-0 — LEGACY WEAK NULL: value shuffle** (`shuffle_floor` in `lift_band_spectral_v1.py`).
  Preserves the value multiset only; destroys piecewise-constancy as well as placement. Retained
  **solely** to reproduce the S1–S3 excess numbers on a comparable footing. **No confirmatory
  conclusion rests on Null-0.**
- **BANNED:** cyclic rotation (§0.3 F-3, `|FFT|`-invariant, zero power).
- `B = 999` draws of Null-1 per configuration; the pooled statistic `S_ram` is ranked against
  `B` draws of the **joint** null (one Null-1 realization per configuration per draw, summed), giving
  one integer-rank p-value `p = (1 + #{b : S_b ≥ S_obs})/(B+1)`.

---

## 4. PLANTED CONTROLS (must fire, or the arm is VOID)

### 4.1 For H2b/H2a (deterministic arm) — wrong-prediction controls
The comparator must be shown able to REPORT MISMATCH. Three deliberately wrong prediction tables,
run through the identical comparator on every configuration in C:
- **W1-plant:** drop the coprimality filter — intervals at *all* `j ∈ [0,q)` (predicts `q` intervals,
  not `φ(q)`).
- **W2-plant:** centres at `(2j+1)A/(2q)` (half-shifted).
- **W3-plant:** widths scaled by `1/2` (endpoints wrong, centres right).
**Requirement: each must produce `mismatch > 0` on every configuration in C.** If any wrong
prediction "matches", the comparator is broken ⇒ **VOID the whole H2 arm**, debug, re-run.
*(W3-plant is the one that specifically proves the comparator is sensitive to endpoints, not only to
centres — without it, H2b would be no stronger than H2a.)*

### 4.2 For H3 (spectral arm) — planted comb, with a power sweep
- **PC-comb (must fire).** Build a synthetic sequence `k̃` from a comb restricted to
  `Q_plant = {7, 11, 13}` (intervals at primitive `j/q` for `q ∈ Q_plant` only, uniform widths,
  remaining offsets filled with value 0). Run the full H3 pipeline against the `RAM` model built
  from `Q_plant`. **Requirement: `R2_ram(synthetic) ≥ 0.80` and its Null-1 rank `p ≤ 1/60`.**
  Failure ⇒ **H3 arm VOID** (the spectral readout cannot see a comb it was handed).
- **PC-comb-α (power calibration, gives the §5 number).** Mix: with probability `α` keep the planted
  comb value at an offset, with probability `1−α` replace it by a value drawn from the Null-1
  ensemble. Sweep `α ∈ {1} ∪ {2^{-k} : k = 1..8}`, 100 repetitions each. **Report the smallest `α`
  at which `S_ram`'s Null-1 rank fires with empirical power ≥ 0.8. That `α` is the H3 detection
  floor and must be printed with every H3 null.**
- **PC-neg (false-positive gate).** Run the entire H3 pipeline on 100 pure Null-1 realizations.
  **Requirement: empirical firing rate ≤ 2·α* = 1/30.** If it exceeds this, the null is
  miscalibrated ⇒ VOID H3.

---

## 5. POWER

### 5.1 H2b / H2a (deterministic — power is coverage, not a probability)
The comparison is an exact integer identity over every offset. **A hypothesis violated at even one
offset in the confirmatory set is detected with probability 1.** The honest power statement is
therefore coverage:
- offsets covered: `Σ_C A = 2·65536 + 2·262144 + 2·2048 + 2·8192 = 675840`;
- intervals covered: `Σ_C Σ_{q≤M} φ(q) ≈ 9.6·10³` (exact count emitted by the run);
- informative cells: **314** safe-count cells + **127** deficiency cells + `2·Σ r̂_q ≈ 1.9·10⁴`
  endpoint positions.
**What this power statement does NOT cover:** `bexp ∉ {12,14,17,19}`, `M ∉ {31,36,41,43,45,60,100,
101}`, `M > 101`, non-power-of-two `A`, and the regime `A ≫ M²` beyond `bexp = 19`. Any null must be
stated inside those bounds.

### 5.2 H3 (spectral)
- Analytic reference: with `F_max` frequencies, the Spearman/Pearson-scale sampling SD of a
  correlation-type statistic is `≈ 1/√(F_max − 1)`; at the smallest `F_max = 1024` (T1/T2) that is
  `0.0313`, so a per-config correlation `≥ 0.11` is detectable at `α* = 1/60`, power 0.8
  (`(z_{1/60,2-sided}=2.394 + z_{0.8}=0.842)·0.0313 = 0.101`). At `F_max = 7200` (W4) the floor is
  `0.038`.
- **The operative number is empirical: the smallest firing `α` from PC-comb-α (§4.2), which MUST be
  reported with any H3 null.** No H3 bound may be stated without it.
- Multiplicity: statistical cells requiring a threshold = **3** (`S_ram`, `Δ_HC` pooled, `H3-top` hit
  count). `α* = 0.05/3 = 1/60`. `B = 999` ⇒ min attainable `p = 1/1000 < 1/60` ✓.
- H2b/H2a consume no `α` (deterministic).

---

## 6. FALSIFICATION (written before the run)

**HYP-G (the Ramanujan-comb geometric premise) is KILLED if, on at least one configuration in C:**
```
mismatch_interior > 0
```
i.e. at least one offset **not** flagged `boundary_decided` has `k_den(off) ≠ predicted_value(off)`
— equivalently, `L_q` is not the predicted union of primitive-`j/q`-centred intervals. Concretely
this is realized by any of: (a) an offset with `k_den = q` whose nearest `q`-denominator fraction has
`gcd(j,q) > 1`; (b) an offset with `k_den = q` outside every predicted `q`-interval; (c) an offset
inside a predicted `q`-interval with `k_den ≠ q`; (d) `r_q ≠ r̂_q` for any `q`.
Every such offset is listed individually with its `(q, j)`.

**Graded reading, fixed now:**
- `mismatch = 0` ⇒ HYP-G **confirmed exactly** at that configuration.
- `mismatch_interior = 0` and `mismatch_boundary > 0` ⇒ HYP-G confirmed up to the endpoint
  strictness rule; the discrepancy is a **tie-break/strictness disclosure**, reported as a deviation
  with the exact offsets, not as a falsification and not as a confirmation of a different law.
- `mismatch_interior > 0` ⇒ **HYP-G FALSIFIED at that configuration.** Required output: the
  *structure* of the excess — is it a whole `q`-class? a contiguous region? only `q ∉ Q_safe`? only
  `q | A`? — never the bare count.

**HYP-S (the equal-width Ramanujan factorization) is KILLED if:** PC-comb fired, PC-neg passed, and
`S_ram` does not fire at `α* = 1/60`, **or** `R2_ram < 0.30` on a majority of C while `ΔR2 ≤ 0`.
Required output in that case: H3-resid (§2.6) — which `q`-sub-family carries the residual — plus the
scoped magnitude bound with the PC-comb-α floor.

**A configuration is never dropped.** All 8 in C are reported whatever they show. If a configuration
cannot be computed (assertion halt, resource limit), that is a disclosed deviation naming the
configuration, not a silent filter.

---

## 7. PRE-COMMITTED OUTCOME TABLE

The H3 arm's evidential status depends on the H2b branch. **Both branches are written now.**

### Branch A — H2b confirms (`mismatch_interior = 0` on all 8 configs)
Then the sequence is pinned exactly, and **every spectral quantity becomes a derived mathematical
property of a known step function, not empirical evidence.** Pre-committed wording and cells:

| Cell | Outcome | Pre-committed conclusion |
|---|---|---|
| H2b | `mismatch = 0`, all 8 | **HYP-G VERIFIED EXACTLY** over 675840 offsets / ~9.6·10³ intervals / 8 fresh `(bexp,M)` configs, and it **follows from the Dirichlet + three-distance argument of §0.4**. Grade `[VERIFIED + derivable]`. Write-up must say "verified, and derivable" — **not** "discovered". Scope §5.1 stated on every number. |
| H2b | `mismatch_boundary > 0` only | As above **plus** a named disclosure of the tie-break/strictness rule that differs, with the exact offsets listed. |
| H2a-safe | `r_q = φ(q)`, 314/314 safe cells | Count law holds. **Explicitly note (§0.3 T-2) that the count alone does not discriminate Farey placement**; the discrimination is H2b. |
| H2a-tight | `r_q = r̂_q`, 127/127 deficiency cells | The `M`-cap discretization deficiency is predicted correctly out-of-sample. This is the non-trivial half. |
| H2a-tight | any deficiency cell wrong | The §0.4 width bound is not tight at the `M`-cap. **Report the exact `q` and the observed vs predicted width, and derive the corrected bound.** A sharper law, not a null. |
| H3 (all) | any | **CHARACTERIZATION ONLY.** Report `R2_ram`, `ΔR2`, `TOP3_pred` hits, `Δ_HC`, legacy excess — each with config scope — and state in the same sentence: *"given the exact geometry (H2b), these are derived properties of a determined sequence; the Null-1 p-values quantify how far the Farey placement is from random placement, which H2b already establishes."* No `p` from this arm may be presented as independent evidence. |
| H3-top | `M=100` vs `M=101` top modes agree | The comb depends on `M` only through the cutoff, as the model says. Records that the S1–S3 "stable top \|f\| = 12/24/24" is a cutoff effect, not an `M`-factorization effect. |
| H3-top | `M=100` vs `M=101` top modes differ | The cutoff model is incomplete; **`M`'s factorization enters**. Report the difference and the mechanism candidate. Next probe: sweep `M` over a consecutive run at fixed `bexp`. |
| any PC (§4.1) | fails to mismatch | **VOID the H2 arm.** Comparator broken. Debug, re-run, disclose. No verdict. |

### Branch B — H2b fails (`mismatch_interior > 0` on ≥1 config)
Then H3 recovers full evidential status (F-1 no longer applies).

| Cell | Outcome | Pre-committed conclusion |
|---|---|---|
| H2b | interior mismatch | **HYP-G FALSIFIED at the named configs.** Report the structure of the excess (per `q`, per `j`, contiguity, `Q_safe` membership). The failure locus **is** the finding. Then: is the true level set a comb with a *different* centre set? Fit nothing — enumerate the observed run centres and test them against candidate arithmetic centre-sets pre-listed here: `{j/q : gcd=1}` (failed), `{j/q : all j}`, `{j/q' : q' | q}`, Stern–Brocot mediant positions. |
| H3 `S_ram` | fires (`p ≤ 1/60`), PC-comb fired | The equal-width Ramanujan factorization governs the spectrum **even though** the exact geometry differs. Report `R2_ram`, `ΔR2`, scope, and the PC-comb-α floor. |
| H3 `S_ram` | null, PC-comb fired, PC-neg passed | **SCOPED MAGNITUDE BOUND:** the equal-width Ramanujan comb explains at most `R2_ram` of the log-spectrum over `f ∈ [1,F_max]` at these 8 configs, detection floor `α_min` from PC-comb-α, power 0.8, `α* = 1/60`. **NOT** "no comb structure": run H3-resid and report which `q`-sub-family carries the residual, and note that the low-frequency excess (H3-legacy) is a *magnitude* that lives in some symmetry type not yet projected onto. |
| H3 `S_ram` | null, PC-comb did NOT fire | **VOID.** The null is uninformative. Fix the readout; report nothing. |
| PC-neg | firing rate > 1/30 | **VOID H3.** Null-1 miscalibrated. |

### Cells common to both branches
| Cell | Outcome | Pre-committed conclusion |
|---|---|---|
| H3-legacy | excess reproduced on C | The S1–S3 "5.4× → 12.2× → 28.0× growing with curve size" is re-expressed on the `A` axis with `M` decoupled: report excess as a function of `A` at fixed `M` and of `M` at fixed `A`, separately. The prior three-config trend was `bexp`/`M`/`n` **three-way confounded**; that is stated as a scope correction on the prior result, not as a refutation of it. |
| H3-legacy | excess NOT reproduced | Report the discrepancy against S1–S3 with both configs' full parameters. Do not widen either result. |

---

## 8. EXACTNESS (repo rule: `btc_puzzle_investigation/CLAUDE.md`)

- **`check_no_float.sh` must pass on `kden_ramanujan_comb_v1.py` before any confirmatory number is
  produced.** Gate; failure ⇒ halt.
- **Signal path — 100% `int` / `fractions.Fraction`:** `k_den` (as in `band_residual`: `//`, `%`,
  `abs`, no division); run extraction; `r_q`; `φ(q)`; `gcd`; all §0.4 endpoint minima (rational
  comparisons by integer cross-multiplication, `Fraction` only); `mismatch` counting; every
  wrong-prediction control; every count in §2.3/§2.4.
  **The PRIMARY test (H2b/H2a) contains no float at all.**
- **Named float carve-out (H3 only):** `numpy.fft`, `log`, `sin` in `Ŵ`, `R2_ram`. Justification:
  (i) monotone analytic statistics ranked against the integer-defined Null-1 permutation ensemble,
  per the repo carve-out; (ii) no key material exists in this experiment — the largest value in the
  transform is `k_den ≤ M ≤ 101 < 2⁷` over a sequence of length `≤ 2¹⁸`, so the FFT's dynamic range
  is `≲ 2²⁵`, far inside a 53-bit mantissa; the transform loses no bit of the exact input.
  `w̄_q` is computed as an exact `Fraction` and converted to float only inside `Ŵ`.
- **Banned in the H3 decision path:** the `+1e-18` epsilon guards used in
  `lift_band_spectral_v1.py`'s `profile`/`shuffle_floor`. Ratios may be printed for reporting; **no
  threshold may be applied to a float-guarded ratio.** All decisions are integer ranks.
- **Ordering enforcement (anti-T-1):** for each configuration, `predict_levelsets(A, M)` runs first,
  writes `endpoints_<id>.tsv`, and its SHA-256 is appended to `kden_endpoint_hashes.txt`. Only then
  is `k_den` computed. The hash file is committed before the comparison step. `TOP3_pred` is emitted
  and hashed in the same step, before `P_obs` exists.

---

## 9. WHAT MAY NOT BE CONCLUDED

- No result here may be stated without its `(bexp, M)` configuration. "The `k_den` spectrum is a
  Ramanujan comb" is not a permissible sentence; "at `(bexp,M) ∈ C` (§1.1), ..." is.
- A null in H3 is a **magnitude bound with the PC-comb-α floor and the §5.2 power number**. The words
  *closed*, *no structure*, *generic*, *benign*, *tautological*, *at the floor* are audit triggers and
  are banned as verdicts.
- Confirmation of H2b does **not** license any statement about the curve, the lift, `derr`, or the
  `d`-side: `k_den` is pure band arithmetic (§0.1). The prior finding's overlap/whiteness results are
  outside this spec's scope and are neither confirmed nor extended here.
- Tallies must be reported as `informative_hits / informative_cells` using the §2.3/§2.4 counts, with
  `q ∈ {1,2}` and boundary-decided offsets excluded. A raw `675840/675840` is **forbidden**.
