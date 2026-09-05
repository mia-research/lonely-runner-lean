# RESULT — Localized Bit Extraction battery (v1)

**Spec:** `PREREG_localized_bit_extraction_v1.md` (written pre-data) + `PREREG_localized_bit_extraction_v1_DEVIATIONS.md`.
**Code:** `lbe_harness_v1.py`, `lbe_run_v1.py`. **Raw:** `lbe_results_v1.pkl`, `lbe_run_v1.log`.
**Date:** 2026-07-20.

> **SCOPE BANNER.** Everything below was measured at `p = 127 … 100003` (`n ≤ 99667`), exhaustive
> over all `d`. Nothing here was measured at `p ≈ 2²⁵⁶` — a gap of ~239 binary orders of magnitude.
> **No statement in this document has any power against structure at cryptographic scale.**

---

## 1. Question and design

Does any **local, DLP-free** feature of the single point `P_d = [d]G` carry information about the
scalar `d`? Curve `y² = x³ + 7 / F_p`, `p ≡ 1 mod 3`, `#E = n` prime; 5 primes; exhaustive `d`.

Feature stage sees only the point; target stage sees only the scalar (**disjoint construction** —
the defense against the `r = v−w` vs `w` tautology class, enforced mechanically by a
permutation-equivariance gate, not by a shuffle control). Statistic: pooled `G`-test per cell,
Holm–Bonferroni at FWER 0.01 over the frozen grid, plus a family omnibus. Matched null: the
group-automorphism relabel `F(P_{t·d}) ↔ T(d)`.

---

## 2. Controls — all behaved (run is valid)

| control | requirement | result |
|---|---|---|
| plant ladder (**must fire**) | detect at some `e` | fires at every prime; `e_min` below |
| `E5`,`E6` forced-null (**must not fire**) | silent | silent at all 5 primes |
| random-feature row (**must not fire**) | silent | silent at all 5 primes (min `P` ≫ `α/K`) |
| `β` majority vote (≥1000 probes, ≥99%) | unanimous | **1.0000** at all 5 primes |
| permutation-equivariance gate | pass | pass |

**Measured power (`e_min`, agreement bias):**

| `p` | 127 | 1051 | 10477 | 46261 | 100003 |
|---|---|---|---|---|---|
| `n` | 127 | 1093 | 10639 | 46549 | 99667 |
| `e_min` | 0.50 | 0.25 | 0.10 | 0.05 | **0.02** |

Analytic expectation `√(20/N)` gives 0.40 / 0.135 / 0.043 / 0.021 / 0.014 — measured `e_min` is
consistently ~1.4× the estimate, well inside the 3× attenuation flag. **The pipeline is sensitive
and the floor is known.**

---

## 3. Primary result — outcome **N1** (scoped bounded null)

- **Holm rejections at the discovery prime (`p=100003`): 0.**
- One Holm rejection at `p=127` (`A10_uv_mod3 × T-w3`) — the weakest prime (`e_min = 0.5`, 85% of
  cells failing χ² calibration). It fires at **1 of 5** primes ⇒ **outcome H2, chance pattern, not
  named**, no mechanism proposed.
- **No cell reaches the replication criterion** (amended to ≥4/5 primes by deviation D1). The
  maximum is 2/5, reached by two cells, and **both fail residual-structure consistency**:
  - `B4_sign_y × T-b0` — fires at `p=46261` (`P=0.0051`) and `p=100003` (`P=0.0089`), but the
    leading standardized residual has **opposite sign** at the two firing primes (`+1` / `−1`).
  - `C1_mu3pos × T-m7` — fires at `p=127`, `p=1051`; the leading residual cell **moves**
    (`(2,4) → (1,4) → (2,3) → (0,0) → (0,2)`).
- Observed 2 cells firing ≥2/5 against 0.58 expected under naive chance — but see §4: the effective
  per-cell rate is ~3× the nominal, which puts the chance expectation **above** 2.

### Pre-committed conclusion (verbatim from prereg cell N1, with the measured floor filled in)

> Across the 30 enumerated local DLP-free features × 25 enumerated scalar targets, on 5 prime-order
> curves `y² = x³ + 7` with `p ≡ 1 mod 3`, `n < 10⁵`, exhaustive over all `d`, no feature–target
> dependence was detected at family-wise `α = 0.01`. The detection floor was `e_min = 0.02`
> (agreement bias) at `p = 100003`, degrading to `0.50` at `p = 127`; **dependencies with per-sample
> bias below `e_min` are not excluded.**

**This may not be written as "there is no leakage" and may not be generalized beyond `p ≤ 10⁵` or
beyond the enumerated grid.**

---

## 4. A calibration finding that changes how the family is read

The χ²-based p-values show a **consistent 2–4× excess** of cells below the nominal 0.01, at every
prime — the signature one would naively read as diffuse structure, and the reason the family omnibus
`G_family` reached `P = 5.6e−05` at `p=1051` and `P = 0.0105` at `p=100003`.

It is an artifact. The **assumption-free matched-null integer rank** (`emp_p`, null 2a, no χ²
assumption — the statistic this project's numerical-integrity rule prefers) shows **no excess at any
prime**:

| `p` | 127 | 1051 | 10477 | 46261 | 100003 |
|---|---|---|---|---|---|
| χ² raw, ratio to chance | 3.81 | 3.63 | 2.35 | 3.36 | 2.97 |
| χ² Bartlett-corrected | 2.38 | 3.45 | 1.76 | 3.90 | 1.29 |
| **empirical rank** | **0.48** | **1.54** | **0.29** | **0.54** | **0.39** |

Four of five are **below** 1. 340–487 of the 775 cells fail the KS calibration check against
`chi2_df`, and the Bartlett rescaling **does not repair it**.

**Consequences.** (a) The omnibus "significance" is not corroborated and the diffuse-dependence arm
(outcome N2) is **not** entered — but it is **ABSTAINED, not closed**: the empirical rank resolves
only to `emp_p ≈ 0.005–0.012` (200/80 draws) and therefore cannot test the family-wise level `1e−5`
at all. (b) Any future run on this grid must report the empirical rank; χ² Holm alone would have
produced a false positive here.

---

## 5. Object-level structural results (positive, independent of the null)

1. **Cap Law verified exactly at 5 primes.** `flap ⟺ 2|A₁+s·A₂| > |DET|` matches `ε ≠ 0` on
   **126/126, 1092/1092, 10638/10638, 46548/46548, 99666/99666** points.
   **Unforced content:** the basis-orientation constant `s ∈ {±1}` is calibrated per prime, so each
   prime spends **1 bit**; the unforced agreement is `(p−1) − 1` bits, not `p−1`. Without that bit
   the naive `|u−v|` reading agrees on only ~49% of points at half the primes, where the two flap
   sets are **disjoint** (see D2).
2. **Core density → ¾.** Measured 0.7619, 0.7802, 0.7535, 0.7449, **0.7488** — consistent with the
   `¾ : ⅛ : ⅛` spine law (P12) at every prime, converging with `n`.
3. **`P_d^{[7]G} = P_{7d}^{G}` exactly** — the identity that makes the prereg's two-generator
   replication arm a matched-null draw rather than an independent replicate (deviation D1). Any
   design that replicates a scalar-leakage claim "across generators" is testing the wrong thing.
4. **A forced exact symmetry, correctly not named.** In the exploratory μ6 orbit-rank tables
   (§6), column 0 ≡ column 2 entry-by-entry at every prime. It is **forced**: orbits pair as
   `O ↔ −O`, `x(−P) = x(P)` holds, and negation reverses the scalar ranks, so
   `c_σ = c_{σ∘(0 2)}` identically (verified: all 6 permutation classes, 364 orbits, 0 self-negative).
   **Zero information.** Logged because it is exactly the kind of exact-looking zero that the
   count-only-unforced-hits rule exists to catch.

---

## 6. EXPLORATORY (NOT PRE-REGISTERED)

The §9 structure clause names the gap in the frozen grid: every enumerated target is an
**additive/digit** function of `d` (bits, windows, residues, Hamming parity), while the μ6 action on
scalars is **multiplicative** (`d → λd`, `d → −d`). No pre-registered cell pairs a μ6-adapted
feature with a μ6-adapted target — a symmetry-mismatched grid, which is the configuration this
project's drill protocol warns manufactures zeros.

So one symmetry-matched pair was run post-hoc: feature = rank of `x_d` among the x-coordinates of
its GLV orbit `{d, λd, λ²d}` (computable from `P` alone); target = rank of `d` among those scalars
(needs `d`). Two different orderings of the same 3-element orbit, so not tautological.

| `p` | 1051 | 10477 | 46261 |
|---|---|---|---|
| `emp_p` (400 matched-null draws) | 0.122 | 0.027 | **0.928** |
| Cramér's V | 0.073 | 0.033 | 0.002 |

Inconsistent across primes and **null at the highest-power prime**. Under this project's rules this
is a candidate that did not survive out-of-sample retest — **not** a finding, and **not** a closure
of the μ6-matched direction, which remains untested at `n > 5·10⁴`.

---

## 7. What this experiment does NOT test

Single-point features only (no joint/multi-point readouts); 2-way dependence only (no 3-way or
higher interaction); the enumerated 30×25 grid only; `y²=x³+7` with `p ≡ 1 mod 3` only; `p ≤ 10⁵`
only. Untested scalar subspaces named explicitly: high-bit windows above `k0+2`, non-binary Hamming
statistics, multiplicative-order-indexed functions, and any μ6-adapted target beyond the single
exploratory probe of §6. Nothing here bears on secp256k1 itself, on generation-side questions, or on
any ECDLP security claim.

**The 2²⁵⁶ gap, restated.** A leak of size `O(p^{−1/2})` corresponds to a bias `~2^{−128}` at
cryptographic scale and would require `~2^{256}` samples to see. A positive at `10⁵` would be fully
consistent with total undetectability at `2²⁵⁶`; the null obtained here is evidence about `2²⁵⁶` in
**neither direction**.

---

## 8. Open arms after this run (none closed)

1. **Diffuse dependence at the family-wise level** — ABSTAINED, not closed; the empirical rank
   cannot resolve below `~5e−3`. Next step: more null draws, not re-analysis of this data.
2. **μ6-matched feature/target pairs** — one probe, inconsistent, null at the largest prime. Needs
   its own pre-registration and `n > 5·10⁴`.
3. **Joint / multi-point readouts** — entirely outside this grid; this is where the `0.93` joint
   `(x,y)` shadow lives, and nothing here speaks to it.
4. **Every scale above `10⁵`.**
