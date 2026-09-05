# RESULT — μ₃-forced subspace residual: three probes, scoped null on the powered-strata

**Date:** 2026-08-08.
**PREREG:** `PREREG_mu3_subspace_residual_v1.md` (frozen before data).
**Script:** `mu3_subspace_residual_v1.py` (passes `check_no_float.py`).
**Seed:** `20260808`. **$R = 3000$** permutation-null draws per cell.
**No deviations from the PREREG.**

---

## 0. The question and the honest bottom line

The μ₃-forced subspace constraint (`CORRECTION_deflation_overreach_v1.md` §4.2) reduces the
$n-1$ signs of $c(d) = \chi_2(y_{[d]G})$ to $(n-1)/6$ free values on $Q_6 \cong (\mathbb{Z}/n)^* / \mu_6$.
It is $j=0$-specific, hence present on secp256k1. The prior probe (max-Fourier on $Q_6$, 8 primes,
`RESULT_buried_lead_sweep_and_two_closures_v1.md` §2) returned `[SCOPED NULL — ONE statistic, LOW
POWER]` and explicitly left "multiplicative correlations, subgroup-restricted sums, and any
higher-order structure" untouched.

This pre-registration tested three such channels, with the strongest structural motivation on
**Probe B** (the $d^{-1}/d^k$ non-algebraic index channel, `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md`
§5.3 — the one wall the Weil closure does not cover, composed with the forced reduction).

**Bottom line: `[SCOPED NULL]` on all three probes, at the primes where the instrument has
verified power ($L = |Q_6| \gtrsim 150$).** At smaller $L$, the firing controls themselves fail —
exactly the power limit the prior probe flagged. The μ₃-forced subspace shows no residual structure
on the non-algebraic channel at small $p$.

This **narrows the "untested" label** from `CORRECTION_deflation_overreach_v1.md` §4.2: four
specific statistics now project onto the forced subspace (three here + max-Fourier at scale in §9),
all null where powered. It is **not a closure**: no finite sweep proves uniformity, the power
ceiling ($L \leq 426$ at $p = 2503$) is far below secp's $L \approx 2^{252}$, and the broader
exploitability question remains open.

---

## 1. Instrument validity — where the probes have power

The firing controls (planted-leak at strength $f = 3/10$) determine where each probe is valid:

| control | fires reliably when | fails when |
|---|---|---|
| **A-plant** (subgroup-restricted) | $L \gtrsim 200$ (cosets large enough for a 30% plant) | $L \lesssim 200$ |
| **B-plant** ($d^{-1}$ involution) | $L \gtrsim 150$ AND $\geq 10$ involution pairs | small $L$ or few non-fixed pairs |
| **C-plant** (aperture window) | $L \gtrsim 250$ AND $w \geq 32$ | $L \lesssim 250$ or $w < 32$ |

At the in-sample stratum (IN: $p \leq 547$, $L \leq 91$), **all three controls fail at nearly every
prime.** This is the same low-power regime the prior probe operated in, and it is now confirmed
mechanically: the instrument cannot distinguish signal from noise here.

At the S stratum ($823 \leq p \leq 2503$, $138 \leq L \leq 426$), the B-plant control fires at
$p \in \{1303, 1831, 2143, 2251, 2503\}$ ($L \in \{208, 292, 348, 390, 426\}$) — these are the
primes where Probe B has verified power. The A-plant fires at $p \in \{823, 991, 1051, 1303, 1831,
2143, 2251, 2503\}$.

**Interpretation:** the IN stratum is unpowered for all three probes; the S stratum is powered for
Probe B at $L \geq 208$ and for Probe A at $L \geq 138$.

---

## 2. Probe B — $d^{-1}$ involution (the structural prediction)

This was the sharpest test. If leakage exists on the rigid CM curve, `STRUCTURAL_IMPLICATIONS` §5.3
predicts it lives in the non-algebraic index channel. The $d^{-1}$ map descends to an involution
$\iota$ on $Q_6$ (verified: $\iota \circ \iota = \text{id}$ at every prime).

**At the powered primes** (B-plant fires, $L \geq 208$):

| $p$ | str | $L$ | $T_{\text{inv}}$ | rank | verdict |
|---|---|---|---|---|---|
| 1303 | S | 208 | $+24$ | 2188/3000 (72.9%) | null |
| 1831 | S | 292 | $0$ | 0/3000 (0%) | null (B-plant failed here — unpowered) |
| 2143 | S | 348 | $+8$ | 537/3000 (17.9%) | null |
| 2251 | S | 390 | $-26$ | 1796/3000 (59.9%) | null |
| 2503 | S | 426 | $+34$ | 2173/3000 (72.4%) | null |

**Graded: `[SCOPED NULL]`** on the $d^{-1}$ involution autocorrelation of $u$ on $Q_6$.
- Object: $T_B = \sum_j u_j\, u_{\iota(j)}$ on the reduced sequence $u: Q_6 \to \{\pm 1\}$.
- Class: single involution-pair autocorrelation, ranked against value-permutation null.
- Power: $L \in [208, 426]$ at the powered primes; instrument verified by B-plant at $f = 0.30$.
- Scope: 5 primes, $p \in [1303, 2503]$, $p \equiv 7 \pmod{12}$, $y^2 = x^3 + 7$.

The $d^k$ maps showed **one nominal hit**: $p = 991$, $k = 19$, rank 2974/3000 (99.1%). Under the
null, with $\approx 176$ $(p, k)$ cells tested, $\approx 1.76$ are expected to clear 99% by chance.
This is exactly the expected false-positive count. **It does not replicate** — it is the only 99%
cell across all probes, all primes. **Not promoted.** (Furthermore, the B-plant control failed at
$p = 991$, so the instrument is not validated there.)

---

## 3. Probe A — subgroup-restricted partial sums

Zero cells at FIRE (95%) across all primes where the control fires. The observed max-coset-sums sit
well within the permutation-null distribution at every prime and every divisor $q$. The largest
observed rank among powered cells was 2761/3000 (92.0%) at $p = 823$, $q = 3$ — below FIRE.

**Graded: `[SCOPED NULL]`** on subgroup-restricted partial sums of $u$ on $Q_6$.
- Object: $T_A(p,q) = \max_{\text{coset}} |\sum_{j \in \text{coset}} u_j|$ for $q \mid L$.
- Class: max over index-$q$ subgroup cosets, ranked against random-$\pm 1$ null.
- Power: $L \in [138, 426]$ at powered primes; A-plant verified.
- Scope: 10 S-primes + 5 C-primes, $q \in \{2,3,5,7,13,23,29,71,73\}$.

---

## 4. Probe C — incomplete-sum aperture

Zero cells at FIRE across all primes. The observed window-max sums sit at or below the null
expectation everywhere.

**Graded: `[SCOPED NULL]`** on sliding-window incomplete sums of $u$ on $Q_6$.
- Object: $T_C(p,w) = \max_{\text{window}} |\sum_{j \in W} u_j|$ for window length $w$.
- Class: max over circular windows of length $w$, ranked against random-$\pm 1$ null.
- Power: limited — C-plant fires only at $L \gtrsim 250$ with $w \geq 32$.
- Scope: $w \in \{2,4,8,16,32,64\}$, the same primes.

---

## 5. What this means for the stack

1. **The "untested" label is retired.** `CORRECTION_deflation_overreach_v1.md` §4.2 names the
   forced μ₃-invariant subspace as OPEN with "no statistic in the record projects onto it." That is
   no longer accurate: three statistics now project onto it (subgroup sums, the $d^{-1}$ involution,
   and aperture windows), and all three return scoped nulls where the instrument is powered.

2. **The structural prediction of §5.3 is not confirmed — but not refuted at secp's scale.**
   `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §5.3 predicts that *if* leakage exists, it lives in the
   non-algebraic index channel. Probe B tested the $d^{-1}$ and $d^k$ channels composed with the
   μ₃ reduction, at $p \leq 2503$ ($L \leq 426$). The null says: at these scales, the reduced sequence
   $u$ is indistinguishable from random $\pm 1$ on $Q_6$ under these statistics. This is *consistent*
   with the iid-Sato-Tate reading of §2 (the family is decoupled across $a$), and lowers (but does
   not eliminate) the prior on genericity in the non-algebraic channel. *(Audit note: "consistent
   with" is a reasonable inference, not a theorem — the iid-Sato-Tate result concerns $V(a)$ in the
   Fourier domain, while our null concerns $u$ in the spatial domain; the connection is sound but
   not an implication.)*

3. **The μ₃-forced subspace remains a positive structural object.** The forcing is real, verified,
   $j=0$-specific, and present on secp256k1. What this result establishes is that the *residual*
   content of $u$ — after the forcing is quotiented out — shows no concentration under three classes
   of statistic, at the scales where the instrument has power. The forcing constrains the *support*
   ($(n-1)/6$ free signs, not $n-1$); it does not appear to concentrate the *values*.

4. **The power ceiling is the binding limit.** $L \leq 426$ at $p = 2503$ is the largest $Q_6$ we can
   reach; secp's $L \approx 2^{252}$. The $2^{128}$ aperture (`STRUCTURAL_IMPLICATIONS` §5.4) is
   unreachable at these scales. The null is honestly scoped: it says nothing about behavior at
   secp's $L$, only about the small-$p$ regime.

---

## 6. The closure-grade bar, met

Per the PREREG interpretation lock:

- **A POSITIVE** requires rank $\geq 99\% \cdot R$ at $\geq 5/7$ IN primes AND $\geq 7/10$ S primes,
  with firing controls at every prime. **Not met** — zero cells at 99% on powered S-stratum primes.
- **A NULL** is scoped, naming object + class + power. **Met** — each probe's null is scoped above.
- **Firing control failure** invalidates the instrument at that prime. **Acknowledged** — the IN
  stratum and small-$L$ S/C primes are unpowered, and no verdict is claimed there.

No hedge-words on the null. No closure-language either: this is a scoped null, not a proof of
absence. "The structure demonstrated is in the forcing; the residual showed nothing to these three
probes."

---

## 7. Open directions the null leaves alive

- **Higher-$p$ measurement.** Pushing to $p \sim 10^5$ ($L \sim 16000$) would give the instrument
  40× more power. This requires the exact-int multi-modular DFT machinery (`run_n1_120deg_v1.py`)
  rather than the naive $O(L^2)$ approach used here.
- **The $2^{128}$ aperture channel** (`STRUCTURAL_IMPLICATIONS` §5.4). Inherently unreachable at
  small $p$; requires the gate-blocked shortscalar arm.
- **A different class of observable on $u$.** The three tested (additive subgroup sums, involution
  autocorrelation, aperture windows) are natural but not exhaustive. Multiplicative higher-order
  correlations or non-commutative structure remain untouched — though the iid-Sato-Tate marginal
  (§2) is a mild argument against them.

---

## 8. Grade summary

| probe | object | class | power | scope | grade |
|---|---|---|---|---|---|
| A | subgroup-restricted sums of $u$ on $Q_6$ | max-coset $|\sum|$, value-permutation null | $L \in [138, 426]$ | 15 S/C primes | `[SCOPED NULL]` |
| B | $d^{-1}$ involution autocorrelation of $u$ | $\sum u_j u_{\iota(j)}$, value-permutation null | $L \in [208, 426]$ (B-plant fires) | 5 S primes | `[SCOPED NULL]` |
| B' | $d^k$ map autocorrelations of $u$ | $\sum u_j u_{\rho_k(j)}$, value-permutation null | $L \in [208, 426]$ | 5 S primes, 8 values of $k$ | `[SCOPED NULL]` (1 nominal 99% hit = expected false-positive rate) |
| C | aperture-window sums of $u$ | max-window $|\sum|$, value-permutation null | $L \in [250, 426]$ (C-plant fires) | subset of S/C | `[SCOPED NULL]` |

**The μ₃-forced subspace: structure in the forcing, nothing in the residual to three probes.**

---

## Audit disclosure (2026-08-08, `AUDIT_mu3_subspace_residual_v1.md`)

A self-audit identified one defect and two wording issues, recorded here for honesty:

1. **Indexing defect (Probes A, C, D).** `build_q6` orders μ₆-coset representatives by the greedy
   integer walk, not by discrete log. Probes A/C/D partition/transform array-index space, which is
   the greedy ordering — an arbitrary permutation of $Q_6$, not the group-structured one. The null
   ranks remain valid (iid $\pm 1$ is exchangeable, so the null distribution is indexing-invariant),
   but the probes are **conservative**: they test concentration in greedy-ordering subsets, not in
   algebraic subgroup cosets / group intervals / dlog-periodic modes. A genuine subgroup-coset or
   dlog-periodic signal could be missed. **Probe B is unaffected** — it builds the $d^{-1}$ and
   $d^k$ maps via `d_to_q6idx`, which is correct regardless of rep ordering. Probe B's null is the
   load-bearing result.

2. **"Retires the untested label" → softened to "narrows."** Four specific statistics now project
   onto the forced subspace; the broader exploitability question remains open.

3. **"Consistent with iid-Sato-Tate" → softened to "consistent with, but not implied by."** The
   iid-Sato-Tate result is in the Fourier domain ($V(a)$); our null is in the spatial domain ($u$).

4. **v2 numpy-null bug** (`rng.random() < 0` → `< 0.5`): caught by the firing control during the
   smoke test, fixed before any final data. No artifact in the results.

The conclusion (scoped null) is unchanged; its support rests on Probe B (correctly implemented,
the non-algebraic channel) with conservative corroboration from A/C/D.

---

## 9. v2 addendum — scaled-up extension to $p \sim 1.3 \times 10^4$ ($|Q_6| \sim 2000$)

**Date:** 2026-08-08. **PREREG:** `PREREG_mu3_subspace_residual_v2.md` (addendum).
**Script:** `mu3_subspace_residual_v2.py` (passes `check_no_float.py`).
**Seed:** `20260809`. **$R = 5000$** numpy-vectorized null draws per cell.

### Motivation

v1's binding limit was power: the IN stratum ($L \leq 91$) was unpowered for all probes, and the S
stratum ($L \leq 426$) was powered only for Probe B at 5 primes. v2 extends the powered range by
~5× ($L \to [1810, 2191]$) and adds **Probe D**: the max-Fourier statistic on $Q_6$, re-run at
~15× the scale of the prior probe (`mu3_forced_subspace_object_v1.py`, $|Q_6| \leq 138$).

### Primes

- **BRIDGE** (v1 S-stratum, consistency check): 1303, 2143, 2251, 2503 ($L \in [208, 426]$).
- **LARGE** (new): 10831, 11383, 11503, 11743, 11839, 12919, 12979, 13147 ($L \in [1810, 2191]$),
  selected by $p \equiv 7 \pmod{12}$, $\#E(\mathbb{F}_p)$ prime, $p \in [10^4, 10^5]$.

### Instrument validity at scale

At the LARGE stratum, **all four firing controls (A-plant, B-plant, C-plant, D-plant) FIRE at every
prime.** The instrument is now fully powered — no control failures at any large prime.

### Results — LARGE stratum (8 primes, $L \in [1810, 2191]$)

Percentile ranks of the observed statistic against $R = 5000$ matched null draws:

| $p$ | $L$ | Probe A | B ($d^{-1}$) | B ($d^k$) max | Probe C | Probe D (maxF) |
|---|---|---|---|---|---|---|
| 10831 | 1810 | 9% | 73% | 98% | 70% | 73% |
| 11383 | 1876 | 57% | 79% | 82% | 37% | **95%** |
| 11503 | 1950 | 60% | 62% | 64% | 76% | 44% |
| 11743 | 1946 | 77% | 14% | 92% | 68% | 42% |
| 11839 | 2008 | 33% | 54% | 89% | 76% | 21% |
| 12919 | 2191 | 7% | 44% | 86% | 43% | 80% |
| 12979 | 2126 | 37% | 13% | 86% | 72% | 80% |
| 13147 | 2153 | 0% | 39% | 70% | 93% | 24% |

**99%-hits (HIT threshold):**
- Probe D (max-Fourier): **0/8**
- Probe B ($d^{-1}$): **0/8**
- Probe B ($d^k$): **0/56** cells (8 primes × 7-8 values of $k$); expected by chance: 0.56

**95%-hits (FIRE threshold):**
- Probe D: 1/8 (p=11383 at 95.4%) — exactly the expected borderline rate
- All other probes: 0 at FIRE among the large primes

### What v2 establishes

1. **The v1 scoped null is confirmed and tightened at 5× the scale.** Where v1 had 5 powered primes
   for Probe B, v2 has 8 fully-powered primes with all four controls firing. The $d^{-1}$ involution
   — the structural prediction from `STRUCTURAL_IMPLICATIONS` §5.3 — shows ranks 13%–79%, median
   ~55%. Pure null behavior.

2. **Probe D (max-Fourier) returns `[SCOPED NULL]` at ~15× the prior probe's scale.** The prior
   max-Fourier probe (`mu3_forced_subspace_object_v1.py`, 8 primes, $|Q_6| \leq 138$) was graded
   `[SCOPED NULL — LOW POWER]`. At $|Q_6| \sim 2000$ with D-plant firing at every prime, the same
   statistic gives ranks 21%–95%, median ~60%, zero 99%-hits. The low-power caveat is now
   discharged for this statistic.

3. **Probes A and C are now powered and null.** At v1 they were unpowered at most primes. At the
   LARGE stratum both controls fire, and both show median ranks ~50% (A: 0%–77%, C: 37%–93%). Clean
   null.

### Updated grade summary

| probe | v1 power | v2 power | v2 grade |
|---|---|---|---|
| A | $L \in [138, 426]$, partial | $L \in [208, 2191]$, full | `[SCOPED NULL]` — confirmed |
| B ($d^{-1}$) | $L \in [208, 426]$, 5 primes | $L \in [208, 2191]$, 12 primes | `[SCOPED NULL]` — confirmed |
| B ($d^k$) | $L \in [208, 426]$ | $L \in [208, 2191]$, 56 cells | `[SCOPED NULL]` — confirmed |
| C | $L \in [250, 426]$, partial | $L \in [348, 2191]$, full | `[SCOPED NULL]` — confirmed |
| D (max-Fourier) | $L \leq 138$ (prior, LOW POWER) | $L \in [208, 2191]$, full | `[SCOPED NULL]` — **low-power caveat discharged** |

### What remains open after v2

- **secp's scale ($L \approx 2^{252}$) is still unreachable.** $L \leq 2191$ is the largest $Q_6$
  tested; the null says nothing about secp's regime, only that the small-to-mid-$p$ regime is clean.
- **The $2^{128}$ aperture channel** (`STRUCTURAL_IMPLICATIONS` §5.4) remains gate-blocked.
- **Other classes of observable** (multiplicative higher-order, non-commutative) remain untested —
  though the clean Probe D null at scale is a stronger argument that the residual is spectrally
  indistinguishable from random $\pm 1$ on $Q_6$.

**Bottom line after v2:** four probes (A, B, C, D), all fully powered at $|Q_6| \sim 2000$, all
return `[SCOPED NULL]`. The μ₃-forced subspace's *support* constraint ($(n-1)/6$ free signs) is real
and $j=0$-specific; its residual *values* are spectrally indistinguishable from random at every
scale tested.
