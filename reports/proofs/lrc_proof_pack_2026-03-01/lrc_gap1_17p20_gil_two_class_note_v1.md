# Gap-1 Section 17.20 Draft Direction (GIL + Two-Class Residue Law)
**Date:** 2026-03-03  
**Status:** Support-validated drafting note (not yet promoted theorem text)

## Purpose

Record a corrected Route-A direction for Gap 1 that is consistent with current residual data and
is directly citeable in Section 17.20 drafting.

## Empirical Support Snapshot

From `lrc_gap1_gil_two_class_probe_summary_v1.md`:

- residual rows analyzed (`Xi_tr>0`): `92`
- GIL lower-band formula match: `92/92`
- strong gap-diversity claim (`distinct_gaps>=n-2`) holds: `0/92`
- `x0_non_danger >= phi(n)`: `92/92`
- `Bsafe_non_danger >= phi(n)`: `91/92` (single outlier at `n=7`, `fixed=(2,3,4,6)`, `M=17`)
- residual templates scanned: `91`
- two-bad-class templates: `69`
- among those, complementary classes: `69/69`
- among those, predicted two-class law match (`M mod n in {+c,-c}`): `69/69`

Interpretation:

- The low-band inverse-structure mechanism is real and stable in-window.
- The prior strong gap-diversity requirement is too strong for current residual rows.
- A global `x0`-weighted theorem route remains viable and is better aligned with observed mass distribution.

## Corrected Lemma Package for Section 17.20

1. **Lemma GIL-LB (quasi-lower miss-set formula).**
   For `E_fixed = {1,...,n-1} \ {s1,s2}` in the quasi-lower band,
   `R_fix = {-s1^{-1}, -s2^{-1}} (mod n)`.

2. **Lemma GIL-2C (two-class complementary low-band badness law).**
   Define `c = (s2^{-1} - s1^{-1})^{-1} (mod n)`.
   In two-class templates, low-band badness occurs only on `M mod n in {+c,-c}`.
   (Empirical support in current residual-template windows: `69/69` two-class matches.)

3. **Negative result (for pruning).**
   Do not require the strong claim “at least `n-2` distinct gap values across frozen-fixed sub-bands”; it fails on current residual rows.

4. **Weighted global target (recommended theorem direction).**
   Prove a global lower bound on `x0` over `B_div` that:
   - extracts non-dangerous-region mass analytically, and
   - controls dangerous-region contribution with explicit reserve terms,
   avoiding dependence on the disproved strong gap-diversity condition.

## Proposed Section 17.20 Skeleton

1. `GIL-LB`: exact lower-band miss-set identity.
2. `GIL-2C`: complementary two-class badness law (`\pm c`) in low-band regime.
3. `GTMS-x0`: global weighted sum over frozen-fixed cells on `B_div`.
4. `Danger Reserve`: explicit upper bound for dangerous-cell loss and lower bound for retained `x0` mass.
5. `GlobClose-x0`: conclude `x0(E) >= phi(n)` on the bounded strip, then rebind to Gap-1 closure route.

## Citable Artifacts

- Script: `lrc_gap1_gil_two_class_probe_v1.py`
- Residual-row output: `lrc_gap1_gil_two_class_probe_rows_v1.csv`
- Template-level output: `lrc_gap1_gil_two_class_probe_templates_v1.csv`
- Summary: `lrc_gap1_gil_two_class_probe_summary_v1.md`

These artifacts are support diagnostics and should be used to guide theorem drafting, not as proof substitutes.
