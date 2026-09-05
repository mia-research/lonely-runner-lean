# NOTE — Menu Move 2 (finite-monodromy → N7 mechanism): premise REFUTED by the at-scale marginal

**Date:** 2026-08-24
**Author:** ZCode (Claude). Follow-on to `ANALYSIS_supervisor_intersection_menu_triage_v1.md`,
applying the user's "test the idea, not the method" instruction to Move 2.
**Grade:** `[VERIFIED-scope — named mechanism refuted by an on-disk at-scale artifact]`, model
primes p ≤ 1e5. **N7 itself stays OPEN** (Do-Not-Close #2/#8); this kills ONE candidate mechanism.

## The idea (Move 2)
"P32 establishes the monodromy of the relevant family is **finite** (Klein-four × ℤ/3). Finite
monodromy ⟹ V₁(a) is **arithmetic, not Sato–Tate** — a discrete, algebraically-weighted trace
distribution. Compute the character table of that order-12 group and derive the N7 sub-Rayleigh
deficit profile; a match upgrades N7 from anomaly to forced consequence. Purely symbolic, no new data."

## Test of the idea (object-identity gate, then the data)

**(1) Object-identity — the two monodromies are DISTINCT, per the ledger's own record.**
- N7's mechanism *is* the a-family monodromy: Do-Not-Close #2 names "the distribution of the traces
  V₁(a) as a varies … the sub-Rayleigh deficit's mechanism."
- P32's finite Klein-four × ℤ/3 is the **E[2]-descent** monodromy that proves the *uniformity of the
  e₂ identity* (N8). N8 states verbatim: **"the a-family monodromy (#28) is a distinct open object."**
- So the move's core step — identify P32's finite group with the group governing V₁(a) — is exactly
  the identification the master records as NOT established. It is a "true fact about object A applied
  to object B" (CLAUDE.md analytical-closure warning).

**(2) The data settles the a-family monodromy AGAINST finite — and against the idea's prediction.**
`RESULT_monodromy_sato_tane_at_scale_v1.md` (49,833 cells at p=100003, `[VERIFIED — at scale]`):
- line 48: **"Not finite monodromy … the marginal is continuous at scale … Finite monodromy gives an
  atomic trace distribution in the limit (Chebotarev over finitely many conjugacy classes); the
  observed continuous semicircle EXCLUDES it."** Max dev from the semicircle 8.4e-4.
- The L-mono GKR capstone (`RESULT_lmono_gkr_argument_v1.md`, same session) reaches the same object
  from the group side: **G_geom⁰ = SL₂** (connected, infinite), G_arith = SL₂·μ₃·{±1}; the finite
  horn of Larsen's Alternative is killed by that same at-scale continuity.
- The 2-point level statistics were already run **NULL** (`RESULT_semicircle_null_and_verification_v1`,
  reported at line 61 of the at-scale result): spacing KS / number-variance / small-ball are
  **iid Sato–Tate, NOT GUE-rigid**.

**Conclusion.** The a-family monodromy is SL₂-continuous, not the finite order-12 group. The
character-table computation the move proposes would predict an **atomic** V₁(a) distribution — a
prediction the on-disk at-scale marginal (continuous semicircle to 8.4e-4) **already falsifies**.
The method is cheap and correct; the idea it serves is refuted by data already certified. This is a
category error of the object-identity kind the triage flagged, now resolved against the move.

## What is NOT concluded (suppression-bias guard)
- **N7 is not closed.** Stouffer −71.80, 30/30 primes, one-directional, persistent [151,12043],
  FADES-falsified — all stand. Do-Not-Close #2/#8 unchanged.
- What is killed is a **named mechanism** (finite monodromy ⇒ atomic distribution), which the
  anomaly-drill protocol explicitly licenses. The result also **sharpens** the real open question:
  the deficit is a sub-leading effect on a *continuous* SL₂ semicircle whose 2-point statistics are
  *iid* (not rigid) — so N7 is a fine correction on top of Sato–Tate, not a discrete-vs-continuous
  distributional signature. Any future N7 mechanism must be compatible with the semicircle+iid facts.

## Fold status
Fold-worthy for the eventual v15/addendum alongside the N16 discharge and the H-5 cofactor result
(`RESULT_h5_cofactor_artifact_v1.md`). Triggers the `compile-diff` gate. Not folded here.
