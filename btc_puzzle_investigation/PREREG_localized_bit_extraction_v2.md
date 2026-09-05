# PRE-REGISTRATION — Localized Bit Extraction v2: Deficit-Frequency Fingerprinting & Phase Accumulation

**Status:** PRE-DATA. Written before any measurement. No data has been collected.
**Date:** 2026-08-07
**Binding on:** any run reporting results for the "deficit-frequency fingerprinting" or "phase accumulation" LBE questions.
**Predecessor:** `PREREG_localized_bit_extraction_v1.md` (v1 battery, outcome N1, scoped bounded null).
**Deviations:** any departure from this file must be listed in
`PREREG_localized_bit_extraction_v2_DEVIATIONS.md`.

---

## 0. MOTIVATION AND RELATION TO PRIOR WORK

### 0a. What v1 tested and what it left open

v1 (30 features × 25 targets × 5 primes, exhaustive) found no feature–target dependence at FWER 0.01. Detection floor $e_{\min} = 0.02$ at $p \approx 10^5$. All features were **single-frequency, single-point, additive/digit** functions of the coordinates. The $\mu_6$-adapted target space was not covered (all targets were additive; $\mu_6$ acts multiplicatively).

The sub-Rayleigh deficit (N7, $Z = -13.99$, 7/7 primes negative) is the one surviving anomaly after v1. It lives **below the $\ell^2$ surface** — the deficit is in $\text{mean}|U|$ while $\sum_{b,c}|U|^2$ is identical for the character and every random target. v1's readouts were all above the $\ell^2$ layer.

### 0b. The structural conjecture

The row-budget result (v3, Stouffer $Z = +66.87$, 10/10 positive) established that the DLP character produces **more near-zero rows** $|U(a,b,c)|$ than symmetry-matched nulls at every prime. The deficit is carried by an $\sim$8% excess in the low tail ($|U|/\sqrt{\text{mean}|U|^2} < 0.10$). The per-frequency budget $\sum_a |U(a,b,c)|^2 = n(n-1)$ is the conservation law behind this excess (row-budget mechanism, F11 confirmed).

**The untested question:** Is the *identity* of which rows are in the low tail partially determined by the scalar $d$? If the deficit comes from per-frequency cancellation that depends on the $d$-dependent phase structure of the character, then the **pattern** of near-zero rows across $(b,c)$ at fixed $a$ could serve as a fingerprint of the scalar.

This v2 tests that conjecture directly. It is the first LBE design that operates **below the $\ell^2$ layer** — in the phase pattern and coherent accumulation over deficit-carrying frequencies.

### 0c. Why this is not covered by v1

v1's features are functions of $(x_d, y_d)$ alone, evaluated once per point. v2's readouts evaluate $(x_d, y_d)$ at a **pre-computed frequency set** — the deficit-carrying $(b,c)$ — and aggregate over many frequencies. The frequency set is a property of the **group structure** (computed from the public curve, not from $d$), so the readout remains single-point computable. But the aggregation across $\sim p$ frequencies is the new ingredient: it is the first non-unitary readout in the LBE programme.

---

## 1. OBJECT

**The object measured:** the joint distribution, over the group $E(\mathbb{F}_p)$ of prime order $n$, of the pair

$$
(B_d, \tau(d)) \qquad d = 1, \ldots, n-1, \quad P_d = [d]G = (x_d, y_d)
$$

where $B$ is a function of $(x_d, y_d)$ evaluated at a **public, pre-computed frequency set** $D$ (the deficit-carrying frequencies, determined from the curve alone, not from $d$), and $\tau$ is a function of the scalar $d$ alone.

Two arms, each with its own readout $B$:

- **Arm A (deficit-frequency fingerprinting):** $B_d$ is the *count* of deficit-carrying frequencies at which the single-point phase $e_p(b x_d + c y_d)$ falls in the deficit-consistent phase regime.
- **Arm B (coherent phase accumulation):** $B_d$ is the *coherent sum* of single-point phases over the deficit-carrying frequencies, optimized over alignment angles.

Both arms use the same frequency set $D$ and the same targets. Both are single-point computable: $D$ is pre-computed from the public curve (it depends on the group structure, not on $d$), and $B_d$ evaluates the public point $(x_d, y_d)$ at $D$.

### Tautology check (Constraint 1)

Feature and target are **disjointly constructed by mechanism**:

- $B$ takes as input only $(x, y)$ and the public frequency set $D$ (which is a function of the curve parameters $p, G, \beta$ — not of $d$).
- $\tau$ takes as input only the integer $d$.
- The frequency set $D$ is computed **once per curve** before any feature computation, from the character sum structure of the group (specifically: the deficit-carrying $(b,c)$ at fixed $a$). It is the same for every $d$.
- **Mechanical enforcement (mandatory):** the feature stage receives only the point array `pts = [(x_d, y_d) for d in 1..n-1]` and the pre-computed frequency set $D$. It must be **permutation-equivariant**: for a random permutation $\pi$, $F_\text{stage}(\pi(\text{pts}), D) = \pi(F_\text{stage}(\text{pts}, D))$ must hold exactly. A function that reads $d$ cannot pass this test. **Run-blocking precondition.**

### What this is NOT testing

- This is NOT a character-sum test (it does not compute $U(a,b,c)$ or any group-wide sum in the signal path).
- This is NOT a DLP computation (the scalar $d$ enters only through the target $\tau(d)$).
- The frequency set $D$ is NOT optimized for individual $d$ — it is fixed per curve from the public structure.

---

## 2. THE FREQUENCY SET $D$

### 2a. Definition

Fix a DLP frequency $a_0 \in \{1, \ldots, (n-1)/2\}$. For the $(b,c)$ sweep, define:

$$
U(a_0, b, c) = \sum_{P \in E(\mathbb{F}_p)} e_p(b x_P + c y_P) \cdot e_n(a_0 \cdot d(P))
$$

Compute $|U(a_0, b, c)|$ for all $(b, c) \in \mathbb{F}_p \times \mathbb{F}_p$. Normalize: $r(b,c) = |U(a_0,b,c)| / \sqrt{\frac{1}{p^2}\sum_{b',c'} |U(a_0,b',c')|^2}$.

The **deficit-frequency set** $D_\rho$ is:

$$
D_\rho = \{(b,c) : r(b,c) < \rho\}
$$

for threshold $\rho \in \{0.05, 0.10, 0.15\}$.

This is a group-wide computation (computed once per curve before the LBE stage). The set $D_\rho$ depends on the curve, the generator, and $a_0$ — not on any individual scalar $d$.

**Scope of $D$:** At $p \sim 10^4$, $|D_{0.10}| \approx 0.08 \times p^2 \approx 8000$ frequencies. At $p \sim 10^5$, $|D_{0.10}| \approx 8 \times 10^5$.

### 2b. Computational reality

At $p \geq 5000$, the full $(b,c)$ sweep is $O(p^3)$ and may be intractable. The following fallback is pre-committed:

- **If $p \leq 5000$:** compute $D_\rho$ from the full $(b,c)$ sweep.
- **If $p > 5000$:** compute $D_\rho$ from a **random subsample** of $(b,c)$ of size $M = \min(p^2, 10^5)$, drawn uniformly from $\mathbb{F}_p \times \mathbb{F}_p$ with a fixed seed. Report $M$ and the seed. This subsample is the same for every $d$ and every null draw — it is part of the public frequency set, not of the feature stage.

### 2c. DLP frequency $a_0$ selection

$a_0 = 1$ (the orbit-representative character). This is the most-studied frequency in the programme and is where the deficit has been measured consistently.

**Secondary arm (exploratory, not pre-registered for verdict):** $a_0$ drawn uniformly from $\{1, \ldots, (n-1)/2\}$ with a fixed seed. Run identically but results reported under EXPLORATORY.

---

## 3. ARM A — DEFICIT-FREQUENCY FINGERPRINTING

### 3a. Readout definition

For each point $P_d = (x_d, y_d)$ and each frequency $(b,c) \in D_\rho$, compute the **single-point phase contribution**:

$$
\phi_d(b,c) = \text{Im}\left[e_p(b x_d + c y_d)\right] = \sin\left(\frac{2\pi}{p}(b x_d + c y_d)\right)
$$

Define the **deficit-phase count**:

$$
B^{\text{A}}_d(\rho) = \frac{1}{|D_\rho|} \sum_{(b,c) \in D_\rho} \mathbb{1}[\phi_d(b,c) \in [-\epsilon, +\epsilon]]
$$

for alignment tolerance $\epsilon \in \{0.1, 0.2, 0.5\}$ (three readout variants).

**Interpretation:** At the deficit-carrying frequencies, the full character sum is near zero. If this cancellation is $d$-dependent, then at those specific $(b,c)$, the single-point phase contribution should be **more likely** to be near zero (the cancellation direction) for some values of $d$ and not others. $B^{\text{A}}_d$ counts how often the single-point phase is consistent with the deficit direction.

**Binning for G-test:** $B^{\text{A}}_d$ is a continuous quantity in $[0, 1]$. Binned into $a = 4$ equiprobable quartiles (computed from the feature marginal alone, pre-pairing).

### 3b. Invariance analysis

$B^{\text{A}}_d$ is **not** even in $d$ (because $\phi_d(b,c)$ involves $y_d$, and $y_{-d} = -y_d$ changes the phase). It is not $\mu_6$-equivariant (the $\mu_6$ action on $d$ is multiplicative, the phase is additive in $d$). The group-automorphism null $d \to t \cdot d$ preserves all of its invariances.

**Caution pre-stated:** $\phi_d(b,c)$ involves $y_d$, which changes sign under negation. But $\sin$ is odd, so $\phi_{-d}(b,c) = \sin(2\pi(b x_d - c y_d)/p) \neq \phi_d(b,c)$ in general. The readout is genuinely sensitive to the full point $(x_d, y_d)$, not just to the orbit $\{P_d, P_{-d}\}$.

---

## 4. ARM B — COHERENT PHASE ACCUMULATION

### 4a. Readout definition

For each point $P_d = (x_d, y_d)$, compute the **coherent accumulation** over the deficit-frequency set:

$$
S_d(\rho, \alpha) = \left|\sum_{(b,c) \in D_\rho} e^{i \alpha} \cdot e_p(b x_d + c y_d)\right|
$$

swept over alignment angles $\alpha \in \{0, \pi/4, \pi/2, 3\pi/4, \pi\}$ (5 variants).

Define:

$$
B^{\text{B}}_d(\rho) = \max_{\alpha} S_d(\rho, \alpha) / |D_\rho|
$$

**Interpretation:** This is the maximum coherent sum of single-point phase contributions over the deficit-carrying frequencies, normalized by the number of frequencies. For a uniformly random phase sequence, $S_d / |D_\rho| \sim 1/\sqrt{|D_\rho|}$ (by CLT). If the deficit creates a coherent phase structure at certain frequencies, the coherent accumulation will exceed this noise floor.

**Binning for G-test:** $B^{\text{B}}_d$ is binned into $a = 4$ equiprobable quartiles (computed from the feature marginal alone, pre-pairing).

### 4b. Why this is non-unitary

The deficit lives in $\ell^1$ (mean of normalized magnitudes) while $\ell^2$ is pinned by Parseval. Coherent accumulation is the natural $\ell^1$ readout — it sums the phases directly, without any $\ell^2$ (energy) constraint. This is explicitly non-unitary: no Fourier basis change can concentrate the deficit because the deficit is below the $\ell^2$ surface.

### 4c. Invariance analysis

Same as Arm A: $B^{\text{B}}_d$ is not even in $d$ (because $y_{-d} = -y_d$ breaks the coherence pattern). The group-automorphism null preserves its invariances.

---

## 5. TARGETS

| id | target | alphabet $b$ | $\mu_6$ adaptation? |
|---|---|---|---|
| T-r3 | $\text{rank}_3(d)$ — rank of $d$ within its $\mu_3$ orbit $\{d, \lambda d, \lambda^2 d\}$ | 3 | **Yes** |
| T-r6 | $\text{rank}_6(d)$ — rank of $d$ within its $\mu_6$ orbit $\{d, \lambda d, \lambda^2 d, -d, -\lambda d, -\lambda^2 d\}$ | 6 | **Yes** |
| T-m3 | $d \bmod 3$ | 3 | Partially (multiplicative) |
| T-m7 | $d \bmod 7$ | 7 | No (but 7 is coprime to 6, so orbits are preserved) |
| T-orb | $\mu_6$ orbit index of $d$ (which of the $(n-1)/6$ orbits contains $d$) | $(n-1)/6$ | **Yes** |

**Why these targets:** v1 used only additive/digit targets against $\mu_6$-adapted features — a symmetry mismatch that manufactures zeros (§6 of v1 RESULT). v2 corrects this by using multiplicatively adapted targets. T-r3 and T-r6 are the direct $\mu_6$-adapted targets. T-m3 and T-m7 are residues coprime to 6 (so they respect orbit structure). T-orb is the full orbit index — the most $\mu_6$-specific target.

**T-orb caveat:** alphabet size $(n-1)/6$ grows with $p$. At $n \sim 10^5$, $b \sim 17000$. Many contingency-table cells will have expected count $< 5$. Pre-registered filter: cells with $> 20\%$ sparse entries are dropped from the Holm family (but retained in the omnibus). The primary verdict rests on T-r3 and T-r6 (alphabet 3 and 6).

**NO bit targets.** Bit extraction targets ($d \bmod 2$, Hamming parity, bit windows) are deliberately excluded. They are even in $d$ for x-based readouts (the v1/v2 failure mode) and are not $\mu_6$-adapted. Any future arm testing bit targets must use a $\{d, n-d\}$-orbit-matched null and justify the choice in its own PREREG.

---

## 6. NULL CONSTRUCTION

### 6a. Matched null — group-automorphism relabel (PRIMARY)

For a uniformly random $t \in \{2, \ldots, n-1\}$, pair

$$
(B_{t \cdot d \bmod n}, \tau(d)) \qquad d = 1, \ldots, n-1
$$

**Preserves:** the entire point set $\{P_d\}$, every geometric law of the curve, the exact frequency set $D_\rho$, the exact multiset of feature values (since $D_\rho$ is the same for all $d$ and $t \cdot d$), and the exact target marginal.
**Destroys:** only the specific pairing between the phase fingerprint and the particular scalar labeling.

**Invariance check:** Both readouts $B^{\text{A}}_d$ and $B^{\text{B}}_d$ are functions of $(x_d, y_d)$ evaluated at a public frequency set. The map $d \to t \cdot d$ sends $P_d \to P_{t \cdot d}$, which is a bijection of $E(\mathbb{F}_p)$. The frequency set $D_\rho$ is curve-dependent, not $d$-dependent. Therefore the null preserves every invariance of the readout. This is the same null as v1 §2a, extended to the frequency-set context.

**Caveat pre-stated (from v1 §2a):** any dependence invariant under $d \to t \cdot d$ for all $t$ survives this null and is invisible to it. Such dependence is a statement about the feature marginal alone, not about $d$; reported separately as a feature-marginal law (outcome S2).

### 6b. Secondary null — $\mu_6$-orbit-matched relabel

For a uniformly random $t \in \{2, \ldots, n-1\}$ with $\text{gcd}(t, 6) = 1$ (so $t$ preserves $\mu_6$ orbit structure), pair

$$
(B_{t \cdot d \bmod n}, \tau(d)) \qquad d = 1, \ldots, n-1
$$

This null preserves $\mu_6$ orbit structure in addition to everything preserved by 6a. It is **less powerful** than 6a (it preserves more structure), but it provides a specificity check: if a result fires against 6a but not 6b, the dependence is carried by the $\mu_6$-breaking channel, which is the interesting one.

**Used for characterization only, not as a primary verdict.** 200 draws per prime.

### 6c. Calibration requirement

For each $p$ in scope: 200 draws of null 6a and 200 of the secondary null 6b. The empirical distribution of $G$ per cell must match $\chi^2_\text{df}$ with Kolmogorov–Smirnov $p > 0.01$. If calibration fails, the cell's $P_\text{cell}$ is replaced by the empirical null quantile from 2000 draws of 6a, and disclosed per cell. Cells with $> 20\%$ sparse entries (expected count $< 5$) are dropped from the Holm family pre-pairing and listed explicitly.

---

## 7. STATISTIC

Same as v1 §1:

**Primary statistic — pooled likelihood-ratio (G-test):**

$$
G(F,T) = 2 \sum_{i,j,\, N_{ij}>0} N_{ij} \ln\!\left(\frac{N_{ij} \cdot N}{N_{i\cdot} \cdot N_{\cdot j}}\right)
$$

Null distribution: $G \sim \chi^2$ with $\text{df} = (a-1)(b-1)$.
Reported as two-sided tail probability $P_\text{cell} = \Pr[\chi^2_\text{df} \geq G]$.

**Family omnibus:**

$$
G_\text{family} = \sum_\text{cells} G(F,T), \quad \text{df}_\text{family} = \sum_\text{cells} \text{df}(F,T)
$$

**Standardized residual matrix** $R_{ij} = (N_{ij} - N_{i\cdot} N_{\cdot j}/N) / \sqrt{N_{i\cdot} N_{\cdot j}/N}$ mandatory for every reported cell.

---

## 8. PLANT CONTROL AND POWER

### 8a. Plant construction

For each target $\tau$ with alphabet $b$ and effect size $e$, build a synthetic feature

$$
F_\text{plant}(d) = \tau(d) \quad \text{with prob. } \frac{1}{b} + \frac{e(b-1)}{b}, \quad \text{else uniform on other } b-1 \text{ values}
$$

independently per $d$, using a seeded CSPRNG. The plant is inserted as an additional row of the same pipeline.

**Ladder (fixed now):**

$$
e \in \{0.500, 0.250, 0.100, 0.050, 0.020, 0.010, 0.005, 0.002, 0.001\}
$$

30 independent plant replicates per $(e, p)$.

### 8b. Power readout

$e_\text{min}(p)$ := smallest ladder $e$ detected $\geq$ 27/30 replicates at $p$.

**Must be printed adjacent to every null statement.**

**Analytic expectation (not a substitute for measurement):** For binary/binary, $G \approx N \cdot e^2$. With $N = n - 1 \sim 10^5$ and Holm threshold near $\chi^2_1(0.01/K)$ for $K \sim 100$ cells, predicts $e_\text{min} \sim 0.01$–$0.02$. The coherent accumulation readout (Arm B) could have higher power if the deficit creates genuine coherent structure, because the readout aggregates over $|D_\rho| \sim 0.08 p^2$ frequencies.

### 8c. Hard rule (Constraint 2)

If the plant does not fire at $e = 0.5$, the null is uninformative and **no null conclusion may be drawn** — output is "pipeline defect", not "no leakage".

---

## 9. GRID AND MULTIPLE-COMPARISON RULE

### 9a. The grid is enumerated and frozen here

**Features (F), by arm and parameter:**

| id | arm | parameter | description | alphabet $a$ |
|---|---|---|---|---|
| A-05-01 | A | $\rho=0.05, \epsilon=0.1$ | deficit-phase count, tight threshold, tight tolerance | 4 |
| A-05-02 | A | $\rho=0.05, \epsilon=0.2$ | deficit-phase count, tight threshold, medium tolerance | 4 |
| A-05-03 | A | $\rho=0.05, \epsilon=0.5$ | deficit-phase count, tight threshold, wide tolerance | 4 |
| A-10-01 | A | $\rho=0.10, \epsilon=0.1$ | deficit-phase count, standard threshold, tight tolerance | 4 |
| A-10-02 | A | $\rho=0.10, \epsilon=0.2$ | deficit-phase count, standard threshold, medium tolerance | 4 |
| A-10-03 | A | $\rho=0.10, \epsilon=0.5$ | deficit-phase count, standard threshold, wide tolerance | 4 |
| A-15-01 | A | $\rho=0.15, \epsilon=0.1$ | deficit-phase count, loose threshold, tight tolerance | 4 |
| A-15-02 | A | $\rho=0.15, \epsilon=0.2$ | deficit-phase count, loose threshold, medium tolerance | 4 |
| A-15-03 | A | $\rho=0.15, \epsilon=0.5$ | deficit-phase count, loose threshold, wide tolerance | 4 |
| B-05 | B | $\rho=0.05$ | coherent accumulation, tight threshold | 4 |
| B-10 | B | $\rho=0.10$ | coherent accumulation, standard threshold | 4 |
| B-15 | B | $\rho=0.15$ | coherent accumulation, loose threshold | 4 |

**12 features × 5 targets = 60 cells** (T-orb excluded from Holm due to large alphabet; retained in omnibus).

With T-orb: $12 \times 6 = 72$ total cells. After sparse-cell filter, expected Holm family $K \leq 60$.

**Targets (T):** as enumerated in §5 (T-r3, T-r6, T-m3, T-m7, T-orb).

**No cell may be added, removed, or re-binned after the pairing is computed.**

### 9b. Control rows (must behave)

- **Must-fire rows:** the plant ladder (§8).
- **Must-not-fire rows:**
  - **Random-feature row:** uniform random labels with the same marginal as A-10-02, for each target. This is the forced null — it must give $z \approx 0$.
  - **Constant-frequency-set row:** $B_d$ computed with $D_\rho$ replaced by a random frequency set of the same size (not the deficit-carrying set). If this fires, the signal is in the frequency-set selection, not the deficit — a non-LBE effect.
- **Marginal-only row:** feature marginals reported alone.

If a must-not-fire row fires, the run is **void**.

### 9c. Family-wise rule

**Holm–Bonferroni** at FWER $\alpha = 0.01$, applied across all $K$ cells for a given prime $p$.

**Secondary:** Benjamini–Hochberg at FDR $= 0.05$, labeled **SUGGESTIVE**.

**Omnibus:** $G_\text{family}$ vs $\chi^2_{\text{df}_\text{family}}$ at $\alpha = 0.01$.

---

## 10. OUT-OF-SAMPLE REPLICATION RULE

No cell is **named** until it replicates (Constraint 5; two prior chance patterns died in v1).

**Discovery set:** $p_0$ = the largest prime-order curve with $p = 1 \bmod 3$, $n$ prime, $n < 10^5$.

**Replication set:** four further primes with $p = 1 \bmod 3$, prime $n$, from disjoint decades ($\sim 10^2, \sim 10^3, \sim 10^4, \sim 10^5$). **Two distinct generators each** ($G$ and $[s]G$ for $s = 7$), giving 8 independent replication runs.

**Note from v1 deviation D1:** $P_d^{[7]G} = P_{7d}^G$ exactly (proved in v1 §5.3), so the two-generator arm is **not** an independent replicate — it is a matched-null draw. The replication count is therefore **4 primes, 4 runs** (one per prime, one generator). The second generator is retained as a **control consistency check** (the result must be statistically compatible, not an independent test).

**Replication criterion (all three required):**
1. Same $(F, T)$ cell attains $P_\text{cell} < 0.01$ uncorrected in $\geq$ 4/4 replication runs.
2. Sign/structure of the leading standardized residual $R_{ij}$ agrees across all firing replicates.
3. Effect size (Cramér's V) does not drop below $e_\text{min}(p)/2$ in any firing replicate.

---

## 11. SCOPE

- **Curve:** $y^2 = x^3 + 7$ over $\mathbb{F}_p$, $p = 1 \bmod 3$, $\#E(\mathbb{F}_p) = n$ prime.
- **Primes:** five, spanning $\sim 10^2$ to $\sim 10^5$; $n < 10^5$.
- **Scalars:** exhaustive, $d = 1, \ldots, n-1$.
- **DLP frequency:** $a_0 = 1$ (primary); additional $a_0$ values are exploratory only.
- **Deficit thresholds:** $\rho \in \{0.05, 0.10, 0.15\}$.
- **Phase tolerances (Arm A):** $\epsilon \in \{0.1, 0.2, 0.5\}$.
- **Alignment angles (Arm B):** $\alpha \in \{0, \pi/4, \pi/2, 3\pi/4, \pi\}$.
- **Nulls:** 200 draws each of 6a and 6b per prime; 2000 for empirical-quantile fallback.
- **Plants:** 9 ladder values × 30 replicates × 5 primes.
- **$\beta$ calibration:** same as v1 §6 — majority vote over $\geq 1000$ random probes, $\geq 99\%$ unanimity required.

**Every number this run produces inherits this scope.**

---

## 12. EXACTNESS

- All field arithmetic, point arithmetic, characters, phase computation: **exact integer / `Fraction`**. No floats in the signal path.
- $e_p(b x + c y) = \exp(2\pi i \cdot (b x + c y) / p)$: computed as exact rational cosine and sine using modular arithmetic, then converted to float **only at the aggregation stage** ($\sum \sin(\cdot)$, $\sum \cos(\cdot)$). The per-frequency phase is exact before aggregation.
- **Float carve-out (analytic size only):** the logarithm in $G$, the $\chi^2$ tail probability, Cramér's V, and the KS calibration statistic. These consume exact integer counts and produce a reported size only.

---

## 13. FALSIFICATION

**Hypothesis:** some deficit-frequency readout (Arm A or B) carries information about a $\mu_6$-adapted function of $d$, at $p \leq 10^5$.

Abandoned for this grid and scope if: the plant fires at $e_\text{min}$ (pipeline sensitive), the must-not-fire rows stay silent, and no cell clears Holm at any prime, **and** $G_\text{family}$ does not clear $\alpha = 0.01$ at any prime, **and** no BH-suggestive cell survives §10 replication.

---

## 14. STRUCTURE CLAUSE

If nothing fires, report for each arm:

- The $\mu_6$-isotypic decomposition of the readout vector, and which isotypic components the enumerated targets project onto.
- Whether the residual matrix $R_{ij}$ has a consistent sign pattern across primes.
- The subspace of scalar functions $\tau$ not covered (e.g., $\text{rank}_6$ variants, cross-orbit functions, non-cyclic-6 targets).

---

## 15. PRE-COMMITTED OUTCOME TABLE

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| **P0** | Plant does not fire at $e = 0.5$ | **PIPELINE DEFECT.** No null, no positive. |
| **P1** | Any must-not-fire row clears Holm | **RUN VOID.** No cell verdicts. |
| **P2** | Permutation-equivariance assertion fails | **RUN ABORTED.** No numbers. |
| **P3** | $\beta$ majority vote non-unanimous | That prime aborted; others proceed. |
| **N1** | Plant fires; no cell clears Holm; $G_\text{family}$ not significant; no BH cell replicates | **SCOPED BOUNDED NULL:** "Across 12 deficit-frequency readouts × 5 $\mu_6$-adapted targets, on 5 prime-order curves $y^2=x^3+7$ with $p \equiv 1 \bmod 3$, $n < 10^5$, exhaustive over all $d$, no feature–target dependence was detected at FWER 0.01. Detection floor $e_\text{min} = \langle\text{value}\rangle$. Dependencies below $e_\text{min}$ are not excluded." **Not generalizable beyond the enumerated grid.** |
| **N2** | As N1, but $G_\text{family}$ significant while no single cell clears Holm | **DIFFUSE SIGNAL.** Report $G_\text{family}$ as characterization. Route to replication; do not name individual cells. |
| **H1** | Cell clears Holm at discovery prime and passes all three §10 replication criteria | **NAMED FINDING, scoped.** Report cell, $R_{ij}$ structure, Cramér's V per prime, $e_\text{min}$. Scoped to $p \leq 10^5$; extrapolation to $2^{256}$ **explicitly forbidden** (§16). |
| **H2** | Cell clears Holm at discovery but replicates in $< 4/4$ | **CHANCE PATTERN.** Not named. |
| **H3** | Cell replicates but residual structure inconsistent | **ABSTAIN.** Open arm. |
| **H4** | Cell replicates but Cramér's V drops below $e_\text{min}/2$ | **ABSTAIN.** Power-limited. |
| **S1** | BH-suggestive only, replicates $\geq 4/4$ | **SUGGESTIVE, OPEN ARM.** Requires new PREREG. |
| **S2** | Marginal-only row shows structure invisible to null | **Feature-marginal law**, not scalar leakage. Routed to structural programme. |

**Nothing outside this table may be reported as a conclusion.**

---

## 16. SCOPE / POWER LIMITATION — THE $2^{256}$ GAP

Identical in structure to v1 §11:

1. **Power at measured scale.** With $N = n - 1 \sim 10^5$ exhaustive samples, $K \leq 60$ cells, and Holm at FWER 0.01, binary-cell detection floor $e_\text{min} \sim 0.01$–$0.02$ in agreement bias. Arm B's coherent accumulation over $|D_\rho| \sim 8000$ frequencies could amplify a per-frequency bias of $O(1/\sqrt{|D|})$ by $\sqrt{|D|}$, giving an aggregate readout with $O(1)$ bias if the deficit structure is fully coherent — but this is the optimistic conjecture under test, not an assumption.

2. **No power against $O(p^{-1/2})$ leakage.** At $p \sim 2^{256}$, per-sample bias $O(2^{-128})$, requiring $O(2^{256})$ samples. A positive at $10^5$ is fully consistent with undetectability at $2^{256}$.

3. **Extrapolation licensed only** by exponent fit from $\geq 6$ primes with $n \geq 5000$. Fit from fewer points prohibited.

4. **A null here is a null at $10^5$.** Not evidence about $2^{256}$ in either direction.

---

## 17. WHAT THIS EXPERIMENT DOES NOT TEST

1. **Features using the group-wide sum** $U(a,b,c)$ as a direct input. The deficit-frequency set $D_\rho$ is pre-computed from $U$, but $B_d$ never accesses $U$ — it uses only the single-point phase $e_p(b x_d + c y_d)$ evaluated at $D$.
2. **Features outside the 12 enumerated.** In particular: higher-degree readouts beyond linear phase, p-adic or formal-group readouts, division-polynomial values, pairing-derived quantities.
3. **Targets outside the 5 enumerated.** Bit targets, Hamming weight, NAF statistics, high-bit windows are deliberately excluded (see §5).
4. **Curves other than $y^2 = x^3 + 7$**, non-prime $n$, $p = 2 \bmod 3$.
5. **secp256k1 itself** ($p \sim 2^{256}$).
6. **DLP frequencies other than $a_0 = 1$** (exploratory only).
7. **Dependence invariant under $d \to t \cdot d$** — invisible to the matched null (§6a caveat).
8. **ECDLP security claims.**

---

## 18. RUN CHECKLIST

- [ ] permutation-equivariance assertion PASSED (§1)
- [ ] $\beta$ majority vote $\geq 99\%$ at every non-aborted prime (§11)
- [ ] deficit-frequency set $D_\rho$ computed and hashed; $|D_\rho|$ printed per $(p, \rho)$ (§2)
- [ ] subsample flag and $M$/seed printed if $p > 5000$ (§2b)
- [ ] $K$ printed per prime, computed pre-pairing (§9a)
- [ ] dropped-cell list (sparse-entry filter) printed pre-pairing (§6c)
- [ ] null 6a and 6b calibration KS $p$ per cell (§6c)
- [ ] plant ladder table; $e_\text{min}(p)$ per prime (§8)
- [ ] must-not-fire rows: random-feature, constant-frequency-set — both silent (§9b)
- [ ] Holm results; BH results labeled SUGGESTIVE (§9c)
- [ ] $G_\text{family}$, $\text{df}_\text{family}$, tail probability (§7)
- [ ] standardized residual structure for every reported cell (§7, §14)
- [ ] §14 structure clause emitted if nothing fires
- [ ] every stated number carries $(p, n, e_\text{min}, |D_\rho|)$
- [ ] outcome cell from §15 named explicitly
- [ ] Arm A and Arm B reported **separately** — a positive in one arm does not license a claim in the other

---

## 19. COMPUTATIONAL PRACTICALITY

### 19a. Cost of the deficit-frequency set

The $(b,c)$ sweep at $a_0 = 1$ costs $O(p^3)$ (for each $(b,c)$, sum over $n \sim p$ points). At $p = 10^4$, this is $\sim 10^{12}$ operations — **intractable**. At $p = 10^3$, it is $\sim 10^9$ — feasible but slow.

**Fallback (§2b):** random subsample of $(b,c)$ of size $M = 10^5$. This makes the $D_\rho$ computation $O(M \cdot n) \approx 10^{10}$ at $p = 10^5$ — feasible in Sage.

### 19b. Cost of the feature stage

For each $d$ and each $(b,c) \in D_\rho$: one evaluation of $\sin(2\pi(b x_d + c y_d)/p)$ — $O(1)$ per frequency, $O(|D_\rho|)$ per point, $O(n \cdot |D_\rho|)$ per prime.

At $p = 10^4$, $|D_{0.10}| \approx 8000$, $n \approx 10^4$: $\sim 8 \times 10^7$ evaluations. Feasible.
At $p = 10^5$, $|D_{0.10}| \approx 8 \times 10^5$, $n \approx 10^5$: $\sim 8 \times 10^{10}$ evaluations. **Intractable** without subsampling.

**Pre-committed subsample for the feature stage:** if $n \cdot |D_\rho| > 10^8$, subsample $D_\rho$ to $M_\text{feat} = 10^8 / n$ frequencies (minimum 1000), drawn uniformly from $D_\rho$ with a fixed seed. Report $M_\text{feat}$ and the seed.

### 19c. Prime selection

Given the computational constraints, the five primes should be:

| tier | $p$ range | $n$ range | $|D_{0.10}|$ (approx) | feasible? |
|---|---|---|---|---|
| 1 | $\sim 10^2$ | $\sim 10^2$ | $\sim 80$ | Yes (full) |
| 2 | $\sim 10^3$ | $\sim 10^3$ | $\sim 800$ | Yes (full) |
| 3 | $\sim 5000$ | $\sim 5000$ | $\sim 2000$ | Yes (full) |
| 4 | $\sim 20000$ | $\sim 20000$ | $\sim 32000$ | Marginal (subsample $D$) |
| 5 | $\sim 50000$ | $\sim 50000$ | $\sim 200000$ | Subsample required |

The exact primes are determined by `prime_order_curve(lo, hi)` with $p = 1 \bmod 3$, $n$ prime, selecting the largest $n$ in each tier.

---

## 20. RELATION TO THE THERMODYNAMIC / STRUCTURAL LENS (investigation mode note)

The deficit is a **spectral budget drain**: weight that "should" be in the DLP harmonics is absorbed into the low tail. The row-budget mechanism is the conservation law ($\sum_a |U|^2 = n(n-1)$) that forces this drain — a genuine extremal/variat ional structure. The conjecture under test is that this drain is **not uniform across scalars** — that some values of $d$ contribute more to the drain than others, creating a $d$-dependent fingerprint in the low-tail pattern.

This is the natural LBE question to ask of the deficit: not "is there a leak?" (too vague) but "does the deficit's structural mechanism (per-frequency conservation) distribute its burden non-uniformly across scalars?"

**Written in purist register for any published artifact.** The lens language above is investigation-mode only.
