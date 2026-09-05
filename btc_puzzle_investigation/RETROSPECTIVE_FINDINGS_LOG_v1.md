# RETROSPECTIVE — executed findings log (v1)

Running record of the interpretation-phase suppression audit
(`RETROSPECTIVE_suppression_audit_v1.md`). Each entry: the suspect, what the trace found, the grade.
**Symmetric only in the reporting sense** — a suspect that turns out already-handled is recorded as such
(a clean result stated plainly is valid); this is NOT the "symmetric rigor" reflex, and it does not
deflate the live positives.

---

## EX-1 — S2, the sub-Rayleigh deficit → **REAL anomaly, demoted at consolidation** `[AUDIT — confirmed]`
Full writeup: `RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`.
- The joint-(x,y) shadow's one real separating statistic (l¹ mean|U|) shows a sub-Rayleigh deficit:
  `Z=−13.99` pooled, 7/7 primes, every character, survives the matched null, mechanism-open.
- Demoted three ways in master v4: (D1) caveated by a control that is *forced* non-separating (pinned l²);
  (D2) a completed run still listed "NOT YET RUN"; (D3) absent from the master's frontier ledger.
- **Re-test COMPLETE** (`RESULT_subrayleigh_deficit_scaling_v1.md`, frozen prereg SHA `93c9547…`,
  30 primes 151→12043): **replication gate PASS** (Stouffer −71.8, 30/30 negative); **level-1
  PERSISTENT, decisively** — slope −0.034±0.061, whole 2σ band shallower than 1/log p, every decay law
  excluded; **level-2 const-vs-1/log p ABSTAIN** (curvature k2 z=+12 opposes const, contradiction guard).
  **The deficit does NOT fade — it is a persistent model-range structural property, NOT the finite-size
  artifact it could have been (sharp contrast with S1). Signal recovered.** Model scale only; no crypto
  transfer. Mechanism still open.

## EX-2 — S1, the ½-saturation → **FALSE SUSPECT: resolved, and into a sharper law** `[not a demotion]`
- `n1_saturation_residual_v1` (2026-07-30) accounts for both halves:
  - **Mechanism:** the CM 120° lock `α₂/α₁=ζ₃` ⇒ `|1+ζ₃|=1` ⇒ only **2 of 4** eigenvalues carry weight
    ⇒ ceiling `2√p = ½·4√p`. So `½ = 2/4` exactly (`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1`,
    2026-07-26).
  - **Numeric:** the `0.470→½` shortfall is the finite-size deficit of a max over `L≈p/6` semicircle
    draws; the **null's own slope is −0.663 vs the predicted −2/3**, across `p∈[127,6199]` (49× range),
    no drift. The residual (data slightly closer to the cap) was OOS-killed as discovery-sample
    double-counting (4/7 on fresh primes).
- This is *dissolution into a sharper law* — the good outcome, kept as a positive. **No signal recovery
  owed here.**
- **Only open piece:** the 120° lock is verified at 22 primes, **not proved** — the Kronecker/
  Stickelberger target. That is a `[PROVED]`-grade math task, not a leak-hunt.

## EX-3 — S3, Route 3 (cover transfer) → **OPEN but UNWORKED; documentation disciplined** `[priority call]`
- After retraction #26 reversed the "χ₂(y)-supersingular is bound-irrelevant / not-ECDLP" dismissal,
  Route 3 (cover transfer into `Jac(C)`, genus 3, GHS/Weil-descent family) was correctly reinstated OPEN.
- The corpus handles it *correctly in prose*: "genuinely open at the algorithmic level," "NOT a proof
  over the cover family," "a better genus/field trade-off is NOT excluded" (`mu6_cohomology_supersingular_v1/v2`).
- But it is **only ever status-declared, never worked** — no RESULT file attempts the genus-3 index-calc
  trade-off on the secp cover family, while the *structure* side (D2 Lang-torsor, the A_new
  supersingularity proof via the Cartier route) is heavily pursued (D2: 34 mentions).
- **Reading:** this is the asymmetry the reframe targets — the *reduction-construction* avenue parked
  while the *structural characterization* advances. Not a false closure (the prose is honest), but a
  standing OPEN that the bias would keep parked. **Whether to invest is a user priority call**, not a
  measurement.

---

## EX-4 — S4, the E3 real-key anomaly → **real-but-weak; thoroughly worked; largely OUT OF SCOPE** `[not a recovery]`
- The effect is real (p≈0.03–0.04, pre-registered reject, reproduced) but **Bonferroni-non-sig** (1 of ~7
  statistics) and **N=82 is fixed** ("won't become strong under any repetitions").
- My original half-truth-demotion read was **right and independently corrected**: `CORRECTION_e3_…_v1`
  (2026-07-31) withdrew the "curve fingerprint, not a d-fingerprint" headline — it is a **key-set × curve
  INTERACTION**. Spectral decomposition (`RESULT_spectral_decomp_v1`) already checked for a hidden
  orthogonal coherent mode: none (effect is purely rank-1/all-ones; σ_max at 6.5th pct = mild ~1.5σ
  "constraint", not a coherent mode).
- **BUT** that correction's own status block then ruled the whole E3-with-MT-null construction **out of
  scope**: the null is the known-MT19937 pool, so the estimand is "do real keys differ from a known
  *generator*?" — a generator test whatever the curve. Sound. Tell: **"check the null's provenance before
  the curve's."**
- **Audit outputs (not a signal recovery):** (1) confirmed the demotion read; (2) **fixed a live
  re-suppression hazard** — the withdrawn headline was still sitting uncorrected in the primary RESULT
  file and nearly pulled me into re-dismissing it; banner added 2026-08-04. The **only** in-scope residual
  is group-law E3 (Frontier #29) with a **curve-intrinsic** null (not the MT pool), but it inherits the
  N=82 ceiling. **Recommend not spending the re-test budget here** unless the group-law object is wanted
  for its own sake.

## EX-5 — S5, the pow7 pooled tilt → **WASH: the AND-gate demotion was CORRECT** `[calibration result]`
- The suspicion: the K=2 OOS AND-gate had structurally low power vs a homogeneous sub-detection effect,
  so its "not reproduced" might have been a suppression.
- The fair test (`RESULT_cside_replication_v1`, frozen prereg SHA `c53dced7…`, 30 fresh disjoint primes,
  **80% power** at the claimed density, all Gate-0 controls PASS — firing Z=−7.21, negative unbiased,
  pow5/11/13 null): pow7 **Z_pool = −0.923** (expected −2.826 if real), p_fresh=0.178 → **WASH**. The
  original −2.73 over 28 primes was a subsample fluctuation.
- **The audit hypothesis is refuted; the original demotion was right.** This is the retrospective's own
  calibration: a suspected-suppressed lead, given the fully-powered fair test the mandate calls for
  (false positives welcome), **washed**. S2 recovered (real); S5 washed (correctly demoted). The audit
  produces both outcomes — it is not manufacturing recoveries. Honest near-boundary + power scope in the
  RESULT §3 (any residual is ≤⅓ the claimed size, which this design can't separate from noise). Channel
  not closed (2¹²⁸ shortscalar untouched).

## SYSTEMIC — master v4 is ~2 weeks stale, in the suppressive direction `[AUDIT — confirmed, actionable]`
Master v4 is dated **2026-07-20**. At least three items moved after it and it does not reflect them:
| item | master v4 says | actual (post-07-20) |
|---|---|---|
| N1 ½-saturation | "the one measured anomaly with no account… OPEN" | mechanism on file 07-26; finite-size confirmed 07-30 (EX-2) |
| joint-shadow freq-support (§XI.1) | "set up… NOT YET RUN" | ran 07-20 (`harmonic_support_pattern`): Rayleigh, no split |
| sub-Rayleigh deficit (Frontier #17) | absent from the ledger | real −13.99σ, tracked only in ADDENDUM_2 (EX-1) |

The current consolidated view is fragmented across master v4 + ADDENDUM_1 + ADDENDUM_2 + PROJECT_SUMMARY,
and the flagship (v4) understates resolved items and drops a live one. **This is the documented
H3→H4→master degradation pattern recurring** ([[feedback_verify_external_critiques]]).
**Action owed: a master v5 refresh** that (a) restores the sub-Rayleigh deficit as a live frontier,
(b) updates N1 to resolved-with-scope, (c) re-words the M14 caveat (forced control, not a bound on the
lead), (d) folds the ADDENDUM content back in. A `compile-diff` gate is mandatory before promoting v5.

## Queue (unchanged order, top-down)
S2 re-test (in flight) → S4 (E3 real-key, constructed-MT + sibling stats) → S5 (pow7 pooled-not-AND OOS)
→ S6/S7/S8 → the systematic Q1 "perfect-null" census of Appendix A.
