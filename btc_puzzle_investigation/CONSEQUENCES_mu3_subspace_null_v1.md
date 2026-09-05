# CONSEQUENCES — intersections of the μ₃-subspace null with the broader programme

**Date:** 2026-08-08.
**Scope:** careful, sourced analysis of what the μ₃-forced subspace null (v1+v2,
`RESULT_mu3_subspace_residual_v1.md`) actually implies for six adjacent results in the stack.
**Method:** each intersection states the precise object of the adjacent result (sourced), states
the precise object of our null, and asks whether they are the same object, a DFT-dual pair, or
structurally separate — then draws the narrowest honest consequence.
**Posture:** resisting both overclaim and underclaim.

---

## The two objects, stated once

- **Our null** concerns the *spatial* sequence $u : Q_6 \to \{\pm 1\}$, the reduced sign sequence
  $c(d) = \chi_2(y_{[d]G})$ after quotienting the forced $\mu_3$-invariance ($c(md) = c(d)$) and
  negation ($c(-d) = \varepsilon\,c(d)$). $|Q_6| = L = (n-1)/6$.
- **The spectral object** of the broader programme is $V(a) = \sum_d c(d)\,e_n(ad)$, the DFT of $c$,
  equivalently the twisted character sum; its normalized form is $u(a) = V(a)/(2i\sqrt{p}) \in [-1,1]$.

These are a **DFT pair** on $(\mathbb{Z}/n)^*$, but iid-ness in one domain does not imply iid-ness
in the other. This is the load-bearing distinction for most of what follows.

---

## 1. The iid-Sato-Tate result — complementary nulls, not an implication

**Adjacent result** (`RESULT_semicircle_null_and_verification_v1.md`, `RESULT_monodromy_sato_tane_at_scale_v1.md`):
$u(a) = V(a)/(2i\sqrt{p})$ across cells $a \in Q_6$ has (i) the Sato–Tate marginal
$(2/\pi)\sqrt{1-u^2}$ `[VERIFIED, p=100003, 49833 cells]` and (ii) level statistics (spacing KS,
$\Sigma^2$, tail, small-ball) consistent with **iid** semicircle, not GUE-rigid
`[EXPLORATORY, OOS-retested, 17+15 primes]`.

**Relationship.** The Sato–Tate result is about the *spectral* domain ($V(a)$ across cells). Our
null is about the *spatial* domain ($u$ on $Q_6$). These are DFT-dual. iid-spectral does **not**
imply iid-spatial: the periodogram of white noise has a specific correlation structure in the
original domain. So neither null implies the other.

**Consequence (the cleanest positive one).** The two nulls are **complementary and convergent**.
The Sato–Tate result says the $\mu_3$-trivial spectral sector (where $V(a) \neq 0$, by Claim F) has
iid semicircle marginals with no detected 2-point coupling. Our null says the $\mu_3$-trivial
spatial sector (the reduced $u$) has no detected concentration under four classes of statistic. Two
independent nulls on DFT-dual views of the same sector, both clean. This convergence is the
strongest (still scoped, not proved) statement available: the $\mu_3$-trivial sector is generic in
both domains at the scales tested.

**What it is NOT.** Not a proof of genericity, and not an implication in either direction. The
Sato–Tate scope limitation is explicit (`RESULT_semicircle_null` L50–51: "does not test
correlations that leave every order statistic intact").

---

## 2. The separation thesis — mild support, plus a nuance the thesis must address

**Adjacent result** (`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §0, L180): the "separation theorem"
— polylog-computable $\Leftrightarrow$ $\pi$-inert $\Leftrightarrow$ $d$-inert; $d$-carrying
$\Rightarrow$ DLP-locked — is explicitly an **organizing conjecture**, not a theorem.

**Relationship.** The $\mu_3$-forcing *is* polylog-computable ($m$ is the CM multiplier, derived
from $\pi$). It constrains the *support* of $c(d)$: $n-1$ signs $\to$ $(n-1)/6$ free. Our null says
the *residual* (after quotienting) is generic.

**Consequence — mild support.** The null is consistent with the thesis: the $\pi$-determined
forcing imposes a symmetry, and the residual carries no detectable value-information about $d$.
This is the direction the thesis predicts. But it does not prove the thesis (which concerns *all*
polylog invariants, not four statistics).

**The nuance that must be made explicit.** The forcing $c(md) = c(d)$ *is* a statement *about* $d$ —
it links the sign at index $d$ to the sign at index $md$. Under a strict reading of "$\pi$-inert =
independent of $d$," the forcing would be a counterexample (it depends on $d$ via this relation).
The correct distinction, which the thesis must make if formalized: **the forcing is
structure-about-$d$ (a relation among $c$-values at different $d$), not value-of-$d$ (it does not
let you compute $c(d)$ from $\pi$).** The separation thesis is about value-leakage; the forcing is
structure. `STRUCTURAL_IMPLICATIONS` §0 does not currently draw this distinction explicitly. It
should, because the forcing is a non-trivial $\pi$-determined constraint that IS about $d$.

---

## 3. The FLD class-number identity — no intersection (different objects)

**Adjacent result** (`POSITIVE_FINDINGS_MASTER_v6.md` Part X, M11): $|\text{FLD}(p)| = 6\,h(-p)$ at
$p \equiv 19 \pmod{24}$, `[EMPIRICAL, exact match]`, not proved (modulo lemma L1, verified 86/86).

**Relationship — structurally separate.** Sourced precisely:
- $\text{FLD}(p) = \sum_{x \in \mathbb{F}_p} \sigma(x)\,\chi_2(x)$ — a **field-level** sum over
  field elements $x$, pairing the flap-sign $\sigma(x)$ (from the Eisenstein lift) with
  $\chi_2(x)$ (Legendre symbol of the field element).
- Our object: $c(d) = \chi_2(y_{[d]G})$ — a **curve-level** evaluation of $\chi_2$ at the
  $y$-coordinate of curve points indexed by discrete log.

These are different objects. $\chi_2(x)$ in FLD is the Legendre symbol of a field element; the
$\chi_2$ in $c(d)$ is the Legendre symbol of $y_P$ where $y_P^2 = x_P^3 + B$ — a different function
on a different domain. The master file establishes **no bridge** between FLD and $c(d)$ (verified by
reading Part X in full: the only curve-level $\sigma$-statistic is M13's
$\sum_{P \neq O} \sigma(x_P) = C$, which uses $\sigma(x_P)$, not $c(d)$).

**Consequence: none.** The two programmes (the $\sigma \times \chi_2$ field-pairing in Part X, and
the $V(a)/c(d)$ twist programme in Parts VII/XI) are structurally independent. Our null does not
confirm, constrain, or touch FLD. This is a negative result about intersection — stated plainly so
nobody infers a connection that isn't there.

---

## 4. The phase cap $S_y \leq 2$ — consistent, no new constraint

**Adjacent result** (`RESULT_n1_phase_cap_v3.md`, `[VERIFIED — OOS, 120 primes]`; now also provable
via `RESULT_26_PROVED_weil_restriction_v1.md`): $\max_{a \neq 0} |V(a)|/\sqrt{p} \leq 2$,
$N_{\text{viol}} = 0$, range $[1.986, 2.000]$. Tightness ($S_y \to 2$?) is R-INDET.

**Relationship.** The cap bounds $|V(a)|$ — the spectral magnitudes. Our Probe D (max-Fourier on
$u$) tests whether the *reduced spatial* sequence has an unusually large spectral coefficient. If
$c(d)$ had a strong periodic component, $V(a)$ would be large at that frequency; Probe D found no
such concentration.

**Consequence.** The null is *consistent* with the cap and points in the same direction (no spectral
concentration). But:
- The cap is about $|V(a)|$ on $(\mathbb{Z}/n)^*$; Probe D is about the DFT of $u$ on $Q_6$.
  Different normalizations.
- The cap is now `[PROVED]` via #26 (the agent's cross-reference confirms #26 supersedes the v3
  cap file's open-link status). Our null adds nothing to a proved result.
- Probe D does not address the open tightness question ($S_y \to 2$?).

**No new constraint.** Honest.

---

## 5. The $2^{128}$ aperture channel — UNTOUCHED (the most important honest gap)

**Adjacent result** (`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §5.3–5.4): the residual attack
surface, after the Weil closure localizes all algebraic-index correlations to $O(\sqrt{p})$, lives
in the **non-algebraic** index maps ($d \mapsto d^{-1}$, $d \mapsto d^k$), at the **$2^{128}$
scale** where complete-sum bounds go vacuous ($\sqrt{n} \approx 2^{128}$, the puzzle's native
dyadic-interval boundary).

**Relationship — our Probe B IS a genuine test of the non-algebraic channel, but at the wrong
scale.** Probe B tests the $d^{-1}$ involution autocorrelation of $u$ on $Q_6$. The composition
$d^{-1} \bmod \mu_6$ is still non-algebraic (not induced by a curve endomorphism), so this is a
genuine test of the §5.3 residual channel. **But:**
- At our largest $p \approx 1.3 \times 10^4$, $\sqrt{p} \approx 114$. Our windows (Probe C) and our
  $Q_6$ length ($L \leq 2191$) are **far below** the $2^{128}$ scale. We are testing the
  below-aperture-wall regime, where complete-sum bounds hold and we *expect* no concentration.
- Probe C (the aperture test) is doubly weak: it has the indexing defect (tests greedy-ordering
  windows, not dyadic-$d$ intervals) AND operates below the wall.

**Consequence: the $2^{128}$ aperture channel is genuinely untouched by our work.** This is the
central prediction of the structural framing — the one place leakage could live — and we cannot
reach it at small $p$. This is not a failure of the null; it is a scope limitation that must be
stated plainly. The null says: *at small $p$, the non-algebraic channel is clean.* It says nothing
about the regime where the complete-sum bounds go vacuous.

---

## 6. The 120° rigidity (#26) as the *only* spectral constraint — a scoped underclaim

**Adjacent result** (`RESULT_26_PROVED_weil_restriction_v1.md`, `[PROVED]`): the 120° lock
$e_2 = e_1^2 - \chi_2(-1)\,p$ holds for every odd-$n$ curve, every $p > 3$. The theorem is
**solely about the eigenvalue locus / $V_1$/$V_2$ collapse** — it explicitly disclaims any statement
about $c(d)$ spatially or about the $\mu_3$-forced subspace (L168–174).

**Relationship.** The 120° law is a spectral constraint (it pins the eigenvalue configuration).
Our null says: beyond this constraint, the $\mu_3$-trivial spatial sector has no detectable
additional structure.

**Consequence (an underclaim worth stating precisely).** The 120° rigidity is the only spectral
constraint on the $\mu_3$-trivial sector that survives at the scales we tested ($|Q_6| \leq 2191$).
Any *additional* spectral constraint (beyond the $e_2$ relation and Claim F's sector restriction) is
below our detection threshold. This is a meaningful scoped statement — it narrows the mechanism
space — but it is a finite-collection-of-statistics argument, not a proof that no further
constraint exists.

---

## 7. A tension resolved: does the null weaken the §5.3 prediction?

**The worry.** §5.3 predicts "IF leakage exists, it lives in the non-algebraic channel." Our Probe B
tested that channel and found nothing. Does this make the prediction less likely?

**Resolution: no, and the reasoning matters.** The §5.3 prediction is **conditional** ("if leakage
exists, it is here"), not an assertion that leakage exists. Our null says the condition is not met
at small $p$ under these statistics. These are compatible. The prediction is not weakened; it is
untested at the scale where it would bite ($2^{128}$).

There is a subtler point worth holding: the §5.3 prediction comes from the Weil closure (all
algebraic-index correlations are $O(\sqrt{p})$, so the residual *must* be non-algebraic). Our Probe B
tests the non-algebraic channel *after* the $\mu_3$ quotient. The quotient is by an algebraic
subgroup ($\mu_6$, the CM automorphisms). The composition "non-algebraic map $\circ$ algebraic
quotient" is still non-algebraic — so Probe B is a genuine test of the §5.3 residual, not a
diversion into an algebraic channel. The test is valid; it is just underpowered at the scale that
matters.

---

## Summary table

| intersection | precise relationship | consequence | grade |
|---|---|---|---|
| iid-Sato-Tate | DFT-dual domains; neither implies the other | complementary convergence on the $\mu_3$-trivial sector | scoped, positive |
| separation thesis | forcing is $\pi$-determined structure-about-$d$ | mild support; thesis must distinguish structure from value | conjecture-level |
| FLD class number | different objects (field $\sigma\chi_2$ vs curve $\chi_2(y)$) | **no intersection** | negative |
| phase cap $S_y \leq 2$ | cap on spectral magnitudes; now proved via #26 | consistent; no new constraint | — |
| $2^{128}$ aperture | Probe B tests the right channel at the wrong scale | **untouched** — the honest gap | open |
| 120° rigidity (#26) | the proved spectral constraint; disclaims $c(d)$ | #26 is the only spectral constraint surviving at our scale | scoped underclaim |

---

## The one sentence that matters

The null is a clean, well-powered scoped statement about the $\mu_3$-trivial sector at small $p$ —
consistent with the iid-Sato-Tate marginal and with the proved 120° rigidity, structurally
independent of the FLD class-number programme, and **silent on the one channel ($2^{128}$ aperture)
where the structural framing predicts any residual leakage would live.**

---

## Addendum (2026-08-08): the silence is shallower than §5 stated — corrected inventory

A deeper audit of the shortscalar / incomplete-sum prior work (`AUDIT` via Explore agent,
2026-08-08) found that §5 above **overstated the silence**. The $2^{128}$ aperture channel is not
wholly untested. Three tiers of coverage exist:

### Tier 1 — already tested (§5 was wrong to call these silent)

| test | object | scale | result | source |
|---|---|---|---|---|
| untwisted incomplete sum $\sum_{i<W} \chi_2(x_{[d_0+i]G})$ | $\chi_2(x)$, untwisted ($a=0$), dyadic-$d$ | secp, $W=256$, $M=200$ | null on Var, max, lag-1; power floor $\sim 3\%$ | `RESULT_incomplete_sum_2p128_firstorder_v1.md` |
| R-CONTIG $\sum_{s \in I} \chi_k(x([s]G))$ | $\chi_2/\chi_3/\chi_6(x)$, untwisted, contiguous $I$ | $L=5000$, $k \in \{40,...,200\}$ | firm bound $\varepsilon^* = 6.70\%$, no closure | `RESULT_shortscalar_sum_stageA_v2.md` |
| orbit-level inv/pow-$k$ | $c(r) \cdot c(f(r))$ at orbit level | $p \sim 10^4$, 18 primes | scoped null; pooled inv tilt closed as candidate | `RESULT_cside_nonalgebraic_correlation_v1.md`, `RESULT_cside_pooled_tilt_settlement_v1.md` |

### Tier 2 — genuinely untested (the real gaps)

| gap | what's missing | why it matters |
|---|---|---|
| **interval-restricted $R_{\text{inv}}(I) = \sum_{d \in I} c(d)\,c(d^{-1})$** | no code; pointwise version exists (Tier 3) but is not interval-restricted | composition of the non-algebraic channel ($d^{-1}$) with the aperture (contiguous $I$) — the structurally predicted object |
| **additive-twist incomplete sum $V(a,I) = \sum_{d \in I} c(d)\,e_n(ad)$** | no code anywhere; all incomplete sums on file are untwisted ($a=0$) | connects the aperture question to the $V(a)$ eigenvalue machinery and the proved #26 cap |
| **GLV/lattice incomplete sums** over $\{z \in \mathbb{Z}[\omega] : N(z) < B\}$ | gate-blocked (3× frame-gate failure) + harness unbuilt | the lattice-geometry aperture arm |

### Tier 3 — the unrun runnable (highest-leverage immediate action)

**`pointwise_inversion_2p128_item5_v1.py`** is written, fully controlled (C-BALANCE, C-DUP, C-FIX,
C-NULLSD, C-PLANT), uses gmpy2 Jacobian arithmetic + batch inversion, and tests the §5.3 prediction
($d^{-1}$ non-algebraic channel) **at secp scale** ($d \in [2^{k-1}, 2^k)$ for $k \in \{128, 135,
160\}$). It computes $S = \sum_i \chi_2(x_{[d_i]G}) \cdot \chi_2(x_{[d_i^{-1}]G})$ against a
permutation null. **No RESULT file exists.** It appears written but never run/recorded.

This is the single highest-leverage action available: it directly tests whether the silence breaks
at $2^{128}$ on the exact channel §5.3 names. Dependencies (gmpy2, numpy) are present.

### Corrected consequence for §5

The null is silent on the *interval-restricted, additive-twist* versions of the aperture channel
(Tier 2). It is **not** silent on the broader question of whether the $d^{-1}$ channel carries
signal at secp — that has a pointwise test written but unrun (Tier 3), and an orbit-level scoped
null at small $p$ (Tier 1d). The most honest statement: the §5.3 prediction has been *partially*
tested (untwisted aperture: null; orbit-level $d^{-1}$: null), with the *pointwise secp-scale
$d^{-1}$* test written but unrun, and the *interval-restricted* and *additive-twist* versions
genuinely new.

---

## Final addendum (2026-08-08): the pointwise secp-scale $d^{-1}$ test — RUN, scoped null

The Tier 3 script `pointwise_inversion_2p128_item5_v1.py` was run (discovery seed 20260801) and
OOS-replicated (5 fresh seeds). Result: `[SCOPED NULL — OOS-retested, secp scale]`
(`RESULT_pointwise_inversion_2p128_v1.md`).

The discovery run produced a single-seed lead at $k = 160$ ($S = 416$, $p = 6/2001 = 0.003$,
$\sim 2.95\sigma$, Bonferroni-adj $p \approx 0.012$). This is exactly the kind of lead the
counter-prior says to test, not dismiss. **5/5 OOS seeds failed to replicate** (all within
$1.7\sigma$, pooled mean $\approx 0$). The lead is closed as a false positive — same pattern as
`pow7` and `inv`.

**The $d^{-1}$ non-algebraic channel is now nulled at three scales:**
1. $|Q_6| \leq 2191$ (reduced sequence, `RESULT_mu3_subspace_residual_v1.md`)
2. $p \sim 10^4$ (orbit-level, `RESULT_cside_nonalgebraic_correlation_v1.md`)
3. secp $2^{128}$ (pointwise, dyadic-$d$ sampling, `RESULT_pointwise_inversion_2p128_v1.md`)

Power floor: C-PLANT detects coherent $d^{-1}$ correlation $\geq 5\%$ reliably, $\geq 2\%$
marginally. A sub-$2\%$ signal at secp scale is below detection.

**What remains genuinely untested (the real silence):**
- the *interval-restricted* $R_{\text{inv}}(I) = \sum_{d \in I} c(d)\,c(d^{-1})$ over a contiguous
  dyadic-$d$ interval (no code; the pointwise version samples $M$ random $d$, which is structurally
  different from restricting to a contiguous block near the aperture wall)
- the *additive-twist* incomplete sum $V(a,I) = \sum_{d \in I} c(d)\,e_n(ad)$ over dyadic intervals
  (no code anywhere)
- the GLV/lattice aperture arm (gate-blocked + harness unbuilt)

---

## Final resolution (2026-08-08): the two genuinely-untested gaps — NOW TESTED, scoped null

Probes E and F (`PREREG_aperture_probes_v1.md`, `RESULT_aperture_probes_v1.md`) tested exactly the
two objects above at secp scale:

**Probe E** — interval-restricted inversion autocorrelation $S_E(I) = \sum_{d \in I}
\chi_k(w_{[d]G}) \cdot \chi_k(w_{[d^{-1}]G})$ over contiguous dyadic-$d$ intervals ($W = 2000$,
$M_{\text{int}} = 50$), both $\chi_2(x)$ and $\chi_2(y)$, $k \in \{128, 160\}$. **Result:
`[SCOPED NULL — OOS-retested, secp]`.** 20 cells (4 arms × 4 seeds), 2 at FIRE (95%), 0 at HIT
(99%), no replication — consistent with expected false-positive rate ($\lambda = 1.0$). Power floor:
excludes coherent inversion correlation $\geq 5\%$ reliably, $\geq 2\%$ marginally.

**Probe F** — additive-twist incomplete sum $V(a,I) = \sum_{d \in I} c(d)\,e_n(ad)$ over dyadic
intervals ($W = 2000$, $K = 200$ twist params). **Result: `[SCOPED NULL — OOS-retested, secp]`.**
One FIRE cell at seed 17 (95%), not at HIT, not replicated. Power floor: excludes single-frequency
concentration $\geq 5\%$.

**The $d^{-1}$ non-algebraic channel is now nulled at four scales:**

| scale | test | result |
|---|---|---|
| reduced $Q_6$, $|Q_6| \leq 2191$ | Probe B, `mu3_subspace_residual_v1/v2.py` | scoped null |
| orbit-level, $p \sim 10^4$ | `cside_orbitlevel_v1.py`, `cside_nonalgebraic_correlation_v1.py` | scoped null |
| secp $2^{128}$, pointwise | `pointwise_inversion_2p128_item5_v1.py` | scoped null, OOS-retested |
| secp $2^{128}$, interval-restricted | Probe E, `aperture_probes_v1.py` | scoped null, OOS-retested |

**The additive-twist aperture channel** ($V(a,I)$, the genuinely-new object connecting the aperture
to the $V(a)$ eigenvalue machinery) is now scoped-null at $W = 2000$, $K = 200$.

**The one genuinely remaining gap:** the GLV/lattice aperture arm (gate-blocked, harness unbuilt) —
the lattice-geometry analogue of the curve-native incomplete sums tested here. And the theoretical
possibility of structure at $W$ closer to the Pólya-Vinogradov wall ($\sim 2^{135}$ at secp —
unreachable). At $W = 2000$ both the $d^{-1}$ interval channel and the $V(a,I)$ twisted channel are
clean.
