# RESULT v2 — the frozen 31-map FAMILY does not supply the d-side carry: powered, pre-registered SCOPED NULL

**Date:** 2026-08-11. **Runs `PREREG_eps_to_d_constraint_v2.md` (frozen family) verbatim.** Track 2a″.
**Extends `RESULT_eps_to_d_constraint_v1.md`** (v1 tested one map; this tests the whole declared family).
**Artifact:** `scratchpad/eps_to_d_family_v2.py` + `scratchpad/eps_to_d_family_v2.log`. Signal path exact
int; the only float is the `gstat` G-statistic (ranked against an integer-count permutation null — the
permitted carve-out); verdict is the integer permutation p-value.

## What was tested (frozen before the run)

Do any of the public x-covariants — `eps∈{0,1,2}`, signed flap `sg∈{−1,0,+1}`, `s`-band, `sextant`,
`χ2(y)` — predict the d-side carry beyond the matched within-`j` control?
- **(I) Omnibus** (multiplicity-free): joint feature `J=(eps, sign(sg), s-band)` vs target, per `j`-strata,
  one permutation p-value. Two omnibus tests: carry `[d1λ^j+d2λ^j≥m]` and `c mod 3`.
- **(II) 31 declared maps**, Holm–Bonferroni over the frozen count (`χ2(y)`×{`c mod2`,`sign c`} tagged
  parity-suspect).
- **OOS protocol fixed before looking:** scan {p=547, 907}; confirm any hit on {1303, 1669, 2089}.

## Results — `[EMPIRICAL — FAMILY-WIDE SCOPED NULL; plant-fired, powered]`

| arm | outcome |
|---|---|
| **Carry omnibus** | null on 5/6 scan configs; the one flicker (p=907, d1=13, p=12/3001≈0.004) **died OOS** — confirm p = 0.55, 0.84, 0.20 on {1303,1669,2089}, Holm/3 survive-all = **False** → **discarded** per §9 |
| **c-mod3 omnibus** | null both curves (p = 1/1) |
| **31 maps, Holm** | survivors: **NONE** on both scan curves |
| **Plants** | positive `pos_ok=True` (`G_pos` = 23–140 ≫ control); negative `G_neg = 0.00`; gate-plant 0 |
| **Power** | full-map z = 11.0 (p=547) … 14.7 (p=907), up to 21.8 on confirm curves; `U` = 182–714 |

**Pre-committed conclusion (§9 row "both omnibus non-sig AND all 31 maps Holm-null"):** no map in the
frozen family — nor the joint-feature omnibus — predicts the carry `ε` or the `c`-derived targets
(`c mod3/2`, `[c≠0]`, `sign c`) beyond the matched control, on `y²=x³+7` at `p∈{547,907}` (flicker
OOS-checked on {1303,1669,2089}), `U` up to 322 (714 on confirm), full-map power z≥11, plants fired.
Part-(2) payoff (bits saved on `d2`) = **0 by corollary** of the null identity.

**The drill protocol worked:** the sole in-sample omnibus flicker was chased OOS (not dismissed a
priori) and failed to replicate — the correct non-suppressing handling of a scan hit.

## The standing positive (kept foregrounded, not buried under the null)

The `s<3/16` gate **holds exactly for the public flap `eps`** (`RESULT_linchpin_s_gate_v2.md`,
secp-scale) but **fails for the carry `ε`** (v1, 21–93 violations). The same public predicate separates
the two objects. Together with this family-wide null, the record now supports:
**the public Cap-Law flap covariants of `x` are NOT the d-side carry, and no simple or joint (omnibus)
map over them recovers it** — falsifying, at this scope, the ledger's "T2's `ε` IS the Cap-Law flap
correction," consistent with XVI.C. `[VERIFIED — exact gate distinction; EMPIRICAL — family null]`.

## Scope — what is NOT closed (the null is not enlarged)

- Only these **five covariants** and the frozen 31 maps + one 27-cell omnibus collapse are tested. Other
  public functions of `x` (higher-order, multi-point, non-`μ6`-covariant raw bits) are untested.
- **Larger `p`** untested beyond the confirm curves (scope banner #5); this is enumerable-`p`, no secp
  transfer of the null (a null does not inherit scale the way an exact identity does).
- **The OPEN_d2 known-bit-range → partial-carry route (T2c)** is a *different composition* — it uses a
  public range constraint on `d0`, not these flap covariants — and is untouched by this run.
- **The Track-1 objects** (the `c=±b` phase probe on the −13.99σ deficit) are a different object entirely.

## Consequence recorded straight

The XVI.D linchpin's public-computability fact stands (a public flap bit exists), but neither that bit
nor the wider public flap-family supplies the d-carry the ARSENAL tools 3/5/7 consume — so **this route
does not de-circularize the ARSENAL** at the tested scope. The hoped payoff is not delivered here; the
non-circular route still open on the d-carry is T2c (known-range), a separate test.

## Owed gates
`experiment-designer` pre-registered v2 (this run). `citation-verifier` on the Cap-Law inputs before any
grade moves up. `compile-diff` if folded into a master.
