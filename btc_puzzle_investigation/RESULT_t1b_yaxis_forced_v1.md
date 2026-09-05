# RESULT — the y-axis sub-Rayleigh (k≈1) is FULLY FORCED: U(a,0,c) is exactly real (d↔−d), zero off-line residual. Redirects, does not close.

**Date:** 2026-08-11. **`[VERIFIED — exact structural, 3 curves; mechanism NAMED]`** (gate-free; a
decidable dimensionality fact, not a matched-null verdict). Follows `RESULT_t1b_tail_geometry_v1.md`
(sub-Rayleigh localized to the b=0 axis). **Artifact:** `scratchpad/t1b_yaxis_dim_v1.py`.

## Finding
For the y-only sum `U(a,0,c)=Σ_d e_p(c·y_d)e_n(ad)`, the (Re,Im) scatter over `a≠0` has principal
variance ratio **λ2/λ1 = 0.0000 exactly** (p=547,1303,2089) — U collapses onto a single line, with
**no off-line residual** (not a weak null; exactly zero). The x-only axis contrasts at λ2/λ1 ≈ 0.92–0.97
(2-D isotropic Rayleigh).

**Named mechanism (dissolution = positive; a named symmetry, not an asserted one):** `y_{−d}=−y_d`,
`x_{−d}=x_d` ⇒ the sequence `f(d)=e_p(c·y_d)` is conjugate-symmetric (`f(−d)=conj f(d)`) ⇒ its DFT
`U(a,0,c)` is **exactly real** for every `a`. A real (1-D) quantity has magnitude tail `~ε` (k≈1) by
force. So the y-axis sub-Rayleigh exponent is a forced geometric consequence, not new leverage in the
MAGNITUDE channel.

## What this redirects (NOT a closure — scope kept)
- **The MAGNITUDE channel on the b=0 axis is forced (dead end).** Don't fit its exponent as if it were
  free.
- **The FREE part on the y-axis is the SIGN of the real `U(a,0,c)`** (and its ordering over `a`) — this
  is the free variable there and it is UNTESTED. A leak on the y-axis, if any, lives in the sign
  pattern, not the magnitude.
- **The −13.99σ deficit is NOT explained by this (CHECK 2).** It survived a value-multiset
  (shape-preserving) matched null, which already controls for the 1-D magnitude; the forced real-ness
  therefore does not account for it. Relation is the owed T1b.1 — outcome not pre-judged.
- The x-only axis and the c=±b diagonal remain 2-D Rayleigh in magnitude; the diagonal's live probe is
  the phase test (T1a).

## Next (owed / gate-pending)
- **y-axis SIGN channel:** does the sign sequence of the real `U(a,0,c)` carry structure beyond a
  matched control? (pre-register — the free variable the forced magnitude was hiding).
- **T1a** (diagonal phase), **T1b.1** (deficit vs correct-shape null) — via `PREREG_cbpm_phase_deficit_v2`
  (in the gate now).
- Corrects the framing of `RESULT_t1b0_tail_exponent_v1.md` / `RESULT_t1b_tail_geometry_v1.md`: the
  y-axis exponent is forced; the residual is exactly zero.
