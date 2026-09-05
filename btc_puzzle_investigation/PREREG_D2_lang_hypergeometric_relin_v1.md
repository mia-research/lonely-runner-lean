# PREREG — D2 Lang-torsor / hypergeometric formal-group re-linearization of the D1 signal

**File:** `PREREG_D2_lang_hypergeometric_relin_v1.md`  **Date:** 2026-07-20  **Status:** PRE-RUN. No affinity statistic on a re-linearized object computed. No arm scored.

**Scope, up front.** Enumerable model curves `E : y^2 = x^3 + 7` over small `F_p` (`p ≡ 1 mod 6`, prime order `n`, up to a few thousand). The A_new dlog is easy only because A_new is small on the model. **Nothing transfers to `p = 2^256 − 2^32 − 977`**; there the whole enumeration is impossible.

---

## 0. WHAT THIS RUN IS AND IS NOT MEASURING (DPI relocation)

- **NOT an information statistic.** By the `[PROVED]` DPI (`RESULT_formal_group_shadow_order2_v2.md` §I.2), any deterministic re-linearization `ℓ~ = g(ℓ)` cannot increase `I(d;·)`, min-entropy leakage, or `max_g P[g(·)=d]`. Information about `d` is capped by what `ℓ(d)` already carries; the twist cannot raise it. Reporting an information rise as a success would be uninformative (§II.4: zero attribution power).
- **IS an affinity / basis-readability statistic.** §I.2 states the uncovered quantities that CAN rise under post-processing: fixed-basis correlation and coarsened MI. Re-linearization's only possible effect is to move the fixed information into an **affine-readable** basis. The statistic is therefore the affinity/linearity of `d ↦ ℓ~(d)` **in a coordinate computable from `P` alone**, with publicly-computable coefficients — never an information quantity.
- **The spent-input note.** The easy A_new dlog already yields `ℓ(d)`; it is not the lever. The lever under test is solely the re-linearization.

---

## 1. OBJECT

- **D1 signal (input, given):** `ℓ(d) = dlog_{A_new}(Q([d]G))`, `Q(P)=[P^+]−[P^-]`, liftable `d` (`y_P` a QR), from `d1_supersingular_lift_v3.Qdiv/dlog`. Non-affine in `d` (§2 A1).
- **Hypergeometric template:** the formal-group logarithm `L(T)`, `T=−x/y`, whose coefficients are the hypergeometric-type series of the formal group of `E`/`A_new`. `L` linearizes the formal group law where it converges — the **kernel of reduction `E_1(Q_p)`** (`v(z)≥1`), NOT `E(F_p)` (§2 A4).
- **D2 = Lang-torsor twist:** the Lang isogeny `L_F : x ↦ F(x)·x^{-1}` (additive on the formal/Dieudonné side; a homomorphism). D2 applies `L_F` (or its inverse torsor selection) to carry `ℓ(d)` into the domain where `L` converges, yielding the re-linearized coordinate `ℓ~(d)`.
- **The well-posedness question this run must answer first (Arm 0):** does `ℓ~(d)` actually land in a domain where the hypergeometric `L` converges / linearizes? Candidate domains, pre-committed: (i) the p-adic kernel of reduction via a Teichmüller/Hensel lift of `P_d`; (ii) the Dieudonné module / crystalline Frobenius of supersingular `A_new` (where `√p·ζ` rigidity lives). The run reports the convergence profile (à la §I.4) of `L` on the twisted coordinate in each candidate domain. If neither converges, the affinity arms are reported as null-of-domain, not run.

---

## 2. FORCED / ANCHOR FACTS — contribute ZERO evidence

- **A1 — D1 non-affine `[PROVED]`:** `0/666` additivity, `0/339` affine triples, controls fired. The baseline the twist must move. Reproduce once.
- **A2 — DPI `[PROVED]` (§I.2):** information quantities cannot increase under the twist. Report `I(d;ℓ~) ≤ I(d;ℓ)` as a sanity readout; forced, zero evidence; a rise here would signal a bug, not a break.
- **A3 — GLV covariance `[PROVED]` (§I.3):** `R^(k)([λ]P)=β R^(k)(P)`; a μ₆-equivariant readout is constant on the orbit `{±d,±λd,±λ²d}`, so separating `d` within an orbit **requires a component outside that equivariance**. Any affinity that is μ₆-equivariant is orbit-constant and cannot be a per-`d` handle — checked and marked forced.
- **A4 — no `F_p` filtration `[VERIFIED-INSTANCE]` (§I.4):** `L(T)` terms do not decrease over `F_p`; convergence needs `E_1(Q_p)`. This is why Arm 0 exists.

---

## 3. STATISTICS (frozen)

Liftable `d` only. All decisions rank/permutation (float carve-out §7). Exact arithmetic per directory rule.

### ARM 0 — domain check (gate for Arms A/B)
Convergence profile of `L` on `ℓ~` in each candidate domain (i, ii): term magnitudes vs order (as §I.4). Report whether a filtration/convergence exists. No pass/fail; a "no domain converges" result routes to the §8 domain-null row.

### ARM A — affinity magnitude (characterization, NO pass/fail)
Best-affine-fit residual profile and additivity hit-rate of `d ↦ ℓ~(d)`, **in the converging coordinate**, vs the A1 baseline (`0/666`). Report the magnitude of any move toward affinity (per `feedback_negative_bias_enlarge_nulls`, non-affinity is a bounded magnitude, not "nothing").

### ARM B — is the affinity a PUBLIC handle? (the operative test)
Affinity is a handle only if `ℓ~(d) = a·d + b` with `a,b` **computable from public curve params**, not fitted to the sample `d`-labels. Statistic: additivity/affine-fit quality of `ℓ~` scored against the **strong automorphism null** — relabel via `φ_s : P ↦ [s]P`, `s ∈ (Z/n)^*` random, `R≥500`, comparing the true labeling against geometry-preserving relabelings. If affinity appears only because it was fitted to sample labels, the null reproduces it; a public-coefficient affinity makes `s=1` extreme. `{d,n−d}` (`s=−1`) recorded as forced-symmetry readout only.

---

## 4. TAUTOLOGY / DPI GUARD (code-level)

- **Feature computed from `P` only.** `ℓ~`'s implementation has signature reading `(xP, yP, p, public_twist_data)`; `inspect.signature` asserts the arg set excludes `d` and any `d`-indexed array. Violation aborts.
- **No information laundering.** Any information quantity (`I`, min-entropy, guessing prob) is printed under an `A2-forced / zero-attribution` label and may never appear in a §8 conclusion. Only affinity-basis statistics (Arms A/B) are evidential.
- **Public-coefficient requirement (Arm B).** The affine coefficients `a,b` must be produced by a function of public params (curve, `p`, twist data), asserted to not read the sample `(d,ℓ~)` pairs. A fit that reads sample labels is scored ONLY as the null baseline.

---

## 5. CONTROLS (all must fire; no verdict if any fails)

- **C1 — planted affine (Arm A/B MUST detect).** Inject a synthetic signal that IS affine in `d` with public coefficients; Arm B must read `s=1` extreme vs the strong null. If C1 fails, no result.
- **C2 — D1 baseline.** Reproduce A1 (`best_affine` → non-affine, `0/666`-class) on ≥2 primes.
- **C3 — DPI sanity (A2).** `I(d;ℓ~) ≤ I(d;ℓ)` at ≥2 primes (forced; a violation = bug).
- **C4 — GLV-equivariance readout (A3).** Confirm the orbit-constancy of any equivariant component; forced.
- **C5 — convergence normalization (Arm 0).** On a curve where `L` is known to converge (a genuine `E_1(Q_p)` point), the profile must show decrease — pins the Arm-0 readout.

---

## 6. POWER & SCOPE

- Model primes `p ≡ 1 mod 6`, prime `n`, up to a few thousand; `m` computed per prime, m=1 curves selected (m=1 is `[EMPIRICAL]`, not analytic; does not reach secp). Liftable `d ≈ (n−1)/2`.
- **Arm B power:** `R≥500` → p-value resolution ≤ 0.002; smallest detectable public-affinity ≈ the strong-null spread (printed, not assumed).
- **Arm 0/A power:** report convergence/affinity magnitude with sampling spread.
- **Scope:** model-only; the hypergeometric linearization is a p-adic/Dieudonné object and its transfer to the F_p-signal is exactly Arm 0's question; `2^256` unreachable. No transfer.

---

## 7. FLOAT / EXACTNESS CARVE-OUT

Divisor/Jacobian and group arithmetic exact (Sage). The hypergeometric series `L` and the Lang/Teichmüller lift computed as exact `p`-adics / rationals to a stated, fixed truncation and precision (no IEEE floats in the signal path, per directory rule). All Arm-A/B decisions are rank/permutation; only Arm-0 convergence readouts and C3 use magnitude, none as a threshold on the data.

---

## 8. PRE-COMMITTED OUTCOME TABLE (no dismissal language)

| Case (from printed output) | Reported as |
|---|---|
| Arm 0: a domain converges; Arm B: affinity with public coefficients extreme vs strong null | "The Lang/hypergeometric twist re-linearizes `ℓ(d)` into a public-coefficient affine coordinate in domain [i/ii] on these model primes: magnitude `X`, power `Y`, scope model-only. Next probe: stability across `p`, and whether the coefficients are curve-generic. Not a transfer to `2^256`." |
| Arm 0: converges; Arm A shows affinity BUT Arm B in-band vs strong null (fit to sample only) | "The apparent affinity is reproduced by geometry-preserving relabeling — fitted to sample labels, not a public-coefficient handle. A bounded property in the tested coordinate, not a per-`d` inversion; other twists/domains untested." |
| Arm 0: converges; Arm A: no move from the `0/666` baseline | "Under this twist the signal's non-affinity persists at magnitude `X` (power `Y`); the re-linearization does not increase affine-readability in domain [i/ii] on these primes. Conditional on method+sample+floor; other Lang selections, truncation orders, and the Dieudonné domain remain untested." |
| Arm 0: no candidate domain converges | "The hypergeometric `L` does not converge on the twisted F_p-signal in domains (i,ii) at the tested precision (per §I.4 for `F_p`); the linearization template is not realized here. This bounds the tested realization, not the template — the crystalline/Dieudonné construction is the untested next object." |
| C1 fails | **No result reported.** Debug; re-run. |

---

## 9. OUTPUT TYPE (pre-committed)

A **bounded characterization** of affinity/basis-readability, anchored on the DPI (information capped, A2) and the D1 non-affine baseline (A1). Never a verdict about ECDLP, extraction, security, or a "gate." Information quantities are forced/zero-attribution. A persistent non-affinity is a bounded magnitude in the tested coordinate — the object the Dieudonné-domain construction targets — not "no leak."

---

## Files this run will produce
- `d2_lang_hypergeometric_relin_v1.py` (reuses `d1_supersingular_lift_v3`, `formal_log_order2_shadow_v1`, `mu4_eigenvalue_individual_v1`; ≤ ~300 lines).
- `d2_lang_hypergeometric_relin_v1.log` — every §8 row decidable from it.
- `RESULT_d2_lang_hypergeometric_relin_v1.md` — characterization + bounds.
- `PREREG_D2_lang_hypergeometric_relin_v1_DEVIATIONS.md`.
