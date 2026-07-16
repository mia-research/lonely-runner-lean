# Findings v22 — the two owed transfer-spectrum items (v18 scope): resolved, one attribution corrected

**Date:** 2026-07-17 · `conservation_spectrum_v2.py`. Item #3 — the two "SCOPE (do not re-dismiss)"
residuals from v18's self-audit: (a) the x-cell transfer `|λ₂|~1.8×` prefactor was *attributed to
μ₆ without checking the eigenvector* (prior attempt mis-labeled by scalar-d → artifact); (b) the
joint soft-mode test used **y-parity only**, not a general y-readout.

**Diagnostic discipline (earned this run):** the valid soft-mode test is the **absolute `|λ₂|` and
its decay with n** (thermal ⇒ `~1/√n`; a soft mode ⇒ `|λ₂|` bounded away from 0), plus a
**multi-shuffle z-score** (real vs shuffle mean±std). Two nulls were rejected mid-run:
- the **shuffle *ratio*** `real/shuffle` **inflates** when the shuffle floor collapses (a 2-state
  balanced label → shuffle `|λ₂|→0`): it flagged y-half at a spurious **79×**;
- the **cyclic-rotation null is tautological** — `np.roll` preserves every transition except one
  wrap point, so `real/cyclic ≈ 1` for *any* label. Discarded.
(Same family as the v17 shuffle-mismatch phantom; [[feedback_test_on_both_sets_2026_07_12]].)

---

## (a) The x-cell λ₂ mode is NOT the μ₆ charge — v18's attribution corrected

Reproduces v18 exactly (K4 lift-cell transfer under `P→P+G`): `|λ₂| = 0.391 → 0.250 → 0.150`
(p=433,1051,2503), **decaying `~1/√n`**; multi-shuffle **z = 6.8, 8.1, 7.6** (a *real*
above-floor correlation, stable in strength). Mechanism: the addition map `P→P+G` is deterministic,
so consecutive lift-cells are correlated — a genuine short-range correlation that **thermalizes at
the `1/√n` rate ⇒ NOT a persistent soft mode.** (No metastable trap; security-relevant conclusion
unchanged.)

**Eigenvector identity `[EMPIRICAL]`:** pull `λ₂`'s eigenvector back to `φ(x)=v₂[cell(x)]` and test
μ₃-covariance under the **exact** β-action on x-coords (μ₆ acts on x only as μ₃=⟨β⟩; `[−1]` fixes x):
`A = Σ_x φ(βx)·conj(φ(x)) / Σ_x|φ(x)|²`. Calibration: the Perron (constant) eigenvector gives
`|A|=1.000, arg=0°`. The **λ₂ eigenvector gives `|A| ≈ 0.25` (not ≈1), `arg ≈ 0°`** at all three
primes ⇒ **it is NOT a pure μ₃/μ₆ character mode.** So v18's "the `~1.8×` prefactor is the μ₆
conserved charge" is **downgraded**: the mode is a thermally-decaying lift-geometry step
correlation, not a symmetry charge.

**Honest limitation:** a *full* μ₃-isotypic decomposition of the mode is obstructed — the
axis-aligned cell partition (and the available `build`/`reduced_basis` lift machinery) is **not
μ₃-adapted**: attempts to build a clean μ₃-covariant angular label failed the exactness check
(`angle(βx)=angle(x)+120°` held 0/1278 at p=2503; sextant `s+2` likewise). So the mode's precise
μ₃ content is not cleanly pinnable here — but two facts are robust: it is **not a pure μ₆ charge**,
and it **decays thermally** (no soft spot).

---

## (b) No soft mode in ANY general y-readout — v18's y-parity-only check extended and earned

Absolute `|λ₂|` (multi-shuffle z in parentheses), p = 433 / 1051 / 2503:

| y-readout | p=433 | p=1051 | p=2503 | verdict |
|---|---|---|---|---|
| y-cell K4 | 0.096 (0.2) | 0.029 (−1.2) | 0.042 (1.2) | floor — thermal |
| y mod 6 | 0.135 (0.6) | 0.135 (3.4) | 0.065 (1.9) | decays, z non-persistent |
| y mod 7 | 0.157 (0.6) | 0.064 (−0.8) | 0.061 (1.5) | floor — thermal |
| y-half (sign) | 0.063 (0.4) | 0.019 (−0.2) | 0.031 (2.0) | floor — thermal (the "79×" phantom) |
| x-cell × y-half | 0.297 (0.0) | 0.235 (4.1) | 0.121 (0.2) | decays, z non-persistent |

Every y-readout has **`|λ₂|` decaying with n and z-scores that are modest and non-persistent**
(fluctuating 0–4, never a stable high z with flat `|λ₂|`). **No persistent soft mode / approximate
conservation law in any general y-readout.** The joint `x-cell × y-half` just inherits (diluted) the
x-cell short-range correlation and decays. This **earns** v18's "no soft mode beyond μ₆" on the
general-y-readout channel, not only y-parity.

---

## Verdict & grades (locked)

- **(a)** x-cell `λ₂` eigenvector is **not the μ₆ charge** `[EMPIRICAL, p≤2503]` — v18's attribution
  corrected to "thermally-decaying lift-geometry correlation." Full μ₃-isotypic identity **not
  cleanly resolvable** with the non-μ₃-adapted lift basis (stated, not hidden).
- **(b)** **no soft mode beyond μ₆ in general y-readouts** `[EMPIRICAL, p≤2503, multi-shuffle null]`
  — extends v18 (y-parity) to y-cell / y mod m / y-half / joint.
- **Net:** the security picture is unchanged (no metastable soft spot — checked more thoroughly);
  one v18 claim (μ₆-attribution) is corrected; both v18 "un-shut" scope items are closed. Two null
  artifacts caught (shuffle-ratio collapse; cyclic-roll tautology).
- **Scope:** `p≤2503`; secp's `p≈2²⁵⁶` untested; the μ₆-identity of the x-cell mode is
  under-determined by the available lift partition. An empirical thermal result is scoped, not a
  proof of asymptotic mixing.

## Files
Engine: `conservation_spectrum_v2.py` (labels exact-int; eigenvalues/vectors spectral display, no
key in path — carve-out per `glv_closure_verification_v1.py`). Prior: `conservation_spectrum_v1.py`,
`masked_structure_findings_v18.md` (the thermodynamic lens + the two scope residuals).
