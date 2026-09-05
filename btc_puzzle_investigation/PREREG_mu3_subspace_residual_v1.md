# PREREG — μ₃-forced subspace residual, three probes on the non-algebraic channels

**Date:** 2026-08-08.
**Frozen BEFORE data.** Any deviation is filed in `PREREG_mu3_subspace_residual_v1_DEVIATIONS.md`.
**Object under test:** the reduced sign sequence $u : Q_6 \to \{\pm 1\}$ of
`CORRECTION_deflation_overreach_v1.md` §4.2, where $Q_6 \cong (\mathbb{Z}/n)^* / \mu_6$
has $|Q_6| = (n-1)/6$, built by `mu3_forced_subspace_object_v1.py:build(p)`.

---

## 0. Why this pre-registration exists

The μ₃-forced subspace constraint ($c(m\cdot d)=c(d)$ for $m$ of order 3, $c(-d)=\varepsilon\,c(d)$,
hence $(n-1)$ signs $\to$ $(n-1)/6$ free) is the clearest "smoothed away" object in the
Eisenstein/Cap-Law stack. It survived a double-correction. It is $j=0$-specific, hence on secp256k1.
It has been probed by exactly **one** statistic: max-Fourier concentration of $u$ over $Q_6$,
graded `[SCOPED NULL — ONE statistic, LOW POWER]` (`RESULT_buried_lead_sweep_and_two_closures_v1.md` §2).

That result's own closing line: *"This does NOT close the residual. Multiplicative correlations,
subgroup-restricted sums, and any higher-order structure are untouched."*

This pre-registration tests three channels the existing probe did not touch. The structural
prediction that motivates them is from `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §5.3: **IF
leakage exists on a rigid CM curve, it lives in the non-algebraic index channel** ($d\mapsto d^{-1}$,
$d\mapsto d^k$) — the one wall the Weil closure does not cover. Probe B tests exactly that channel,
composed with the forced μ₃ reduction.

---

## 1. The object, stated once

For $E: y^2 = x^3 + 7$ over $\mathbb{F}_p$ with $\#E(\mathbb{F}_p)=n$ prime:
- $c(d) := \chi_2(y_{[d]G}) \in \{\pm 1\}$ for $d \in \{1,\ldots,n-1\}$.
- Forced symmetries (verified, not assumed, at every prime):
  - $\mu_3$: $c(m\cdot d) = c(d)$, $m \in (\mathbb{Z}/n)^*$ of order 3 (the CM endomorphism).
  - negation: $c(-d) = \varepsilon\cdot c(d)$, $\varepsilon = \chi_2(-1)$.
- Reduced object: $u : Q_6 \to \{\pm 1\}$ with $|Q_6| = L := (n-1)/6$, the free content.
- $Q_6$ is cyclic of order $L$ (quotient of the cyclic group $(\mathbb{Z}/n)^*$ by the order-6
  subgroup $\mu_6$).

---

## 2. The three probes

All signal paths are exact-integer (Legendre symbols, discrete logs, index arithmetic). Float
appears ONLY inside a monotone statistic (the transform magnitude or correlation value), which is
ranked against a matched permutation null. **No float threshold decides anything.** The verdict is
an integer rank in every case.

### Probe A — Subgroup-restricted partial sums on $Q_6$

**Statistic.** For each small prime $q$ dividing $L = |Q_6|$ with $2 \leq q \leq \min(L/2,\, 200)$:
partition $Q_6$ into $q$ cosets of its unique subgroup $H_q$ of index $q$ (each coset has $L/q$
elements). Compute
$$T_A(p, q) \;=\; \max_{\text{coset } C}\;\Bigl|\sum_{j \in C} u_j\Bigr|.$$
For iid $\pm 1$ the expected max over $q$ cosets of $L/q$ signs is $\approx \sqrt{2(L/q)\ln q}$.

**Null.** $R = 3000$ random $\pm 1$ sequences of length $L$, same coset structure; rank the observed
$T_A$ among the null maxima.

**Firing control (MUST fire before any cell is trusted).** Plant a coset-aligned bias: pick the
first coset $C_0$, set $u_j = +1$ for a fraction $f$ of $j \in C_0$ (forced), randomize the rest.
At $f=0.30$ the planted $T_A$ must rank $\geq 0.95\cdot R$ (FIRE). At $f=0$ (pure random target)
the planted $T_A$ must rank in $[0.2 R,\, 0.8 R]$ (FLAT).

**Why this probe.** The max-Fourier probe tested global concentration over all of $Q_6$. A
subgroup-restricted sum tests whether concentration lives in a *named algebraic sub-structure*
(cosets of $H_q$), which is the natural home of a class-field-theoretic signal.

### Probe B — The $d^{-1}$ involution on $Q_6$ (the structural prediction)

**The map.** Since $m^{-1}$ has order 3, the inversion $d \mapsto d^{-1} \pmod{n}$ sends each
μ₃-orbit to another μ₃-orbit, hence descends to a well-defined involution $\iota: Q_6 \to Q_6$.

**Statistic.** The inversion-autocorrelation of $u$:
$$T_B(p) \;=\; \sum_{j \in Q_6} u_j \cdot u_{\iota(j)}.$$
For iid $\pm 1$ paired by a fixed involution, $\mathbb{E}[T_B] = 0$, $\text{Var}(T_B) = L$.

**Extension.** Also compute $T_B^{(k)}(p) = \sum_j u_j \cdot u_{\rho_k(j)}$ where $\rho_k$ is the
map $j \mapsto j^k$ on $Q_6$ written multiplicatively (admissible odd $k$ with $k \equiv \pm 1
\pmod 6$, $3 \leq k \leq 25$). These are the non-algebraic index maps of §5.3 restricted to $Q_6$.

**Null.** Permute the values $\{u_j\}$ uniformly at random over the $L$ positions of $Q_6$
(preserving the multiset, hence the forced $\pm 1$ counts); $R = 3000$ permutations; rank the
observed $T_B$ (and each $T_B^{(k)}$) among the null.

**Firing control.** Plant an inversion-aligned signal: for a fraction $f=0.30$ of orbits
$\{j,\iota(j)\}$, set $u_j = u_{\iota(j)}$ (aligned); randomize the rest. Planted $T_B$ must rank
$\geq 0.95 R$ (FIRE). A pure-random permutation must rank in $[0.2R, 0.8R]$ (FLAT).

**Why this probe.** This is the single channel that the Weil closure does NOT cover
(`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §5.3), composed with the forced μ₃ reduction. It is the
sharpest untested structural prediction in the stack.

### Probe C — Incomplete-sum concentration at controlled aperture

**Statistic.** For each aperture $w \in \{2, 4, 8, 16, 32, \min(L/4, 64)\}$ (interval lengths on
$Q_6$ in its cyclic order), slide a window of length $w$ across $Q_6$ and compute
$$T_C(p, w) \;=\; \max_{\text{window } W}\;\Bigl|\sum_{j \in W} u_j\Bigr|.$$
For iid $\pm 1$, $\mathbb{E}[\max_W |\sum_W u_j|] \approx \sqrt{2 w \ln L}$.

**Null.** $R = 3000$ random $\pm 1$ sequences of length $L$; rank observed $T_C$.

**Firing control.** Plant a window-aligned bias at $f=0.30$; must FIRE. Random target must FLAT.

**Why this probe.** §5.4 of the structural implications identifies the $2^{128}$ aperture as the
puzzle's native scale (where complete-sum bounds go vacuous). Probe C tests whether the 3× forced
reduction changes the *effective* aperture behavior at small-$p$ analogues of that scale.

---

## 3. Primes (frozen strata, reused from `run_n1_120deg_v1.py:183-185`)

| stratum | primes | role |
|---|---|---|
| IN (in-sample) | 43, 67, 79, 127, 163, 211, 547 | discovery (the 7 used by the original 120° freeze) |
| S (out-of-sample) | 823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503 | OOS retest |
| C (control, $p\equiv 1\bmod 4$) | 577, 733, 1237, 1249, 1669 | $\varepsilon = +1$ control (negation symmetry changes character) |

Nothing at secp's $p \approx 2^{256}$. **Scale banner:** every measurement is at small $p \leq 2503$;
only algebraic proofs reach secp. This pre-registration is a measurement, not a proof.

A prime enters the run only if $\#E(\mathbb{F}_p) = n$ is prime and $6 \mid (n-1)$ (so $Q_6$ is
integral-dimensional). Skips are logged.

---

## 4. Interpretation lock (pre-committed verdict → grade map)

Binding reading rules, frozen before data. No hedge-words on a positive; no closure-language on a
null.

| outcome | verdict | grade |
|---|---|---|
| A probe's observed statistic ranks $\geq 0.99 R$ at $\geq 5/7$ IN primes AND $\geq 7/10$ S primes, firing control FIREs at every prime, random control FLATs | **POSITIVE — replicated** | `[VERIFIED — OOS]` on the object + class named by that probe |
| A probe ranks $\geq 0.99 R$ at $\geq 5/7$ IN but NOT replicated on S | **POSITIVE — unreplicated** | `[VERIFIED — IN-sample only]`; OOS owed |
| A probe ranks $\geq 0.99 R$ at $< 5/7$ IN primes | **NULL — scoped** | `[SCOPED NULL]` naming object + class + power |
| Firing control FAILS at any prime | **NO VERDICT** | instrument invalid; halt and file deviation |

**Closure-grade bar (asymmetric):**
- A **POSITIVE** is a structural anomaly demanding a mechanism. It is NOT a break, NOT a leak
  verdict. It is a conjecture-grade signal to be promoted only by a separate pre-registered
  mechanism test.
- A **NULL** is scoped: it names the object ($u$ on $Q_6$), the class of observable (the specific
  statistic), and the power ($|Q_6| = 5 \to \sim 400$). It does NOT close the μ₃-forced subspace
  as a source of structure — no finite sweep proves uniformity. It retires the "untested" label
  only.

**Language rule:** "secure", "closure", "proven hard", "unbreakable", "dead end", "wall" are
forbidden. A null is reported as "scoped null on [object, class, power]", not as "no structure."

---

## 5. What is deliberately NOT tested here

- **Complete-sum Fourier concentration** — already done (`mu3_forced_subspace_object_v1.py`,
  `[SCOPED NULL]`). Not repeated.
- **$V(a)$ for $a \in Q_6$** — this is Claim F (`[PROVED]`); $V(ma) = V(a)$ is already known.
- **Extension-field moments** — `STRUCTURAL_IMPLICATIONS` §2 proves these are polynomial in $V_1$;
  closed by algebra.
- **Anything at secp's scale** — the scale banner forbids it; this is a small-$p$ measurement.

---

## 6. Reproducibility

- Script: `mu3_subspace_residual_v1.py` (to be written; passes `check_no_float.py`).
- RNG seed: `20260808`, frozen here.
- $R = 3000$ null draws per cell.
- Builds on: `mu3_forced_subspace_object_v1.py:build(p)` (unchanged), `audit_n1_vsign_v2_core`
  (unchanged), `jclass_e2_relation_probe_v1` (unchanged).
- Deviations, if any: `PREREG_mu3_subspace_residual_v1_DEVIATIONS.md`.
