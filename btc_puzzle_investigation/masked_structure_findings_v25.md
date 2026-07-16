# Findings v25 — re-examination of v22 (items a/b): two things I had dismissed/skipped, corrected

**Date:** 2026-07-17 · re-run of `conservation_spectrum_v2.py` machinery. Prompted by the challenge
"are you sure you didn't dismiss something?" — audited v22's items (a) and (b) with the same rigor
I'd give a positive. **Two honest errors found and corrected. The security conclusion (no persistent
soft mode; barrier computational) survives and is now better supported.**

---

## Correction 1 — (a) the μ₃-isotypic split is EXACT, not "obstructed" (v22 was wrong)

v22 said a clean μ₃-isotypic decomposition of the λ₂ eigenvector was "obstructed because the cell/lift
basis isn't μ₃-adapted." **That was wrong** — `cell(βx)` is exactly computable, so the isotypic
decomposition of the pullback `φ(x)=v₂[cell(x)]` is exact:
`w_k = ‖P_kφ‖²/‖φ‖²`, `P_kφ(x)=(1/3)Σ_j ζ^{-kj}φ(β^j x)` (ζ=e^{2πi/3}); `w₀`=μ₃-invariant,
`w₁+w₂`=μ₃-covariant.

| mode | p=433 | p=1051 | p=2503 |
|---|---|---|---|
| **λ₂** covariant `w₁+w₂` | 0.48 | 0.45 | 0.54 |
| **λ₃** covariant `w₁+w₂` | 0.60 | 0.83 | 0.85 |

(`w₁=w₂` always, as required for a real observable.) So **the μ₃-covariant content is real and
substantial** — λ₂ is ≈50/50 invariant/covariant (stable), and λ₃ is *predominantly* μ₃-covariant,
growing to **85%** as p increases. **Neither v18's "the mode IS the μ₆ charge" nor v22's
over-correction "NOT the μ₆ charge" is right.** The precise statement: the top transfer modes carry
substantial, quantified μ₃-covariant weight (distributed across λ₂ and λ₃), but no single mode is a
*pure* μ₃ character — and all decay thermally. v18's intuition had real support; v22 under-resolved
it by falsely claiming the test was obstructed.

## Correction 2 — (b) the two strongest y-objects were SKIPPED (now tested; conclusion holds)

v22 tested y-cell / y mod 6/7 / y-half / x-cell×y-half but **skipped σ·s_y** (the object v15/v16
flagged as "the genuinely new one" — flap-sign × y-sign, CM-derived, outside closure) **and the fine
joint `x-cell × y-cell`.** Those turn out to be the *strongest-correlated* labels:

| label | \|λ₂\| n=397→7879 | `\|λ₂\|·√n / base` (flat = 1/√n; >1 flat = soft mode) |
|---|---|---|
| **x-cell × y-cell K4** (richest joint) | 0.450, 0.324, 0.198, 0.126, 0.098 | 1.00, 1.20, 1.12, 1.00, **0.97** |
| **σ·s_y** ("genuinely new") | 0.219, 0.100, 0.058, 0.039, 0.033 | 1.00, 0.76, 0.68, 0.63, **0.68** |
| x-cell K4 (reference) | 0.391, …, 0.079 | 1.00 → 0.90 |

Across **n=397→7879 (20×)**: the joint label decays as a **clean 1/√n** (ratio stays ≈1.0, reaching
0.098 with no plateau); **σ·s_y decays FASTER than 1/√n**. The joint label's high z-score (z=6.4 at
p=1051) reflects a *real* short-range correlation (the deterministic P→P+G map on the joint (x,y)
cell), but its `|λ₂|→0` at the thermal rate rules out a persistent soft mode. **So even the richest,
previously-skipped objects confirm: no metastable soft mode.** Extrapolating the clean 1/√n law to
secp `n≈2²⁵⁶` gives `|λ₂|~2⁻¹²⁸` — negligible.

---

## Net (honest)
- **v22's item (a) statement is corrected:** the isotypic split is exact and shows substantial μ₃-
  covariant content (λ₂≈48%, λ₃→85%), not "obstructed." `[EMPIRICAL, p≤2503]`
- **v22's item (b) is completed and confirmed:** σ·s_y and the fine joint label — the strongest
  labels, wrongly skipped — decay 1/√n (joint) or faster (σ·s_y) over n=397→7879. **No persistent
  soft mode in any y-readout, including the "genuinely new" σ·s_y.** `[EMPIRICAL, p≤7879]`
- **Security conclusion unchanged:** no metastable soft spot; barrier stays computational.
- **Method lesson (again):** "obstructed" and "skipped-because-small" are dismissals in disguise —
  the exact test was available (Correction 1) and the skipped objects were the important ones
  (Correction 2). Test the flagged object; compute the exact decomposition. (Prompted by external
  challenge — the audit-the-negative discipline working.)

## Files
Re-run of `conservation_spectrum_v2.py` internals (isotypic decomposition + σ, σ·s_y, fine joint
labels, decay to n=7879). Supersedes the (a)/(b) *characterizations* in
`masked_structure_findings_v22.md` (which stays as the original record; the no-soft-mode headline is
unchanged, its two sub-claims are refined here).
