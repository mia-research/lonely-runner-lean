> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v18 (delta successor to v17: loss restoration from the v12→v14 reorg + external-review flag on the two bias-direction null-conversions)

**Date:** 2026-08-27
**Author:** Claude (Opus 4.8). Requested by the user after a v12→v17 loss + deflation review.
**Predecessor:** `POSITIVE_FINDINGS_MASTER_v17.md` (delta over v16/v15/**v14** = the Full Corpus Revision).
**Motivating audit:** `AUDIT_v12_to_v17_loss_and_deflation_review_v1.md` (this session), which ran the
`compile-diff` gate over the **full** v12 → v17+ADDENDUM_1–4 span — not the immediate-predecessor hop
each in-house delta audited. That span is why these losses were invisible: they occurred at the
**v12→v13/v14 reorganization**, and every later delta (v15→v16, v16→v17) diffs only its immediate
predecessor, so a v12-era drop is structurally unseeable to them.

**What v18 is.** A **delta successor**, not a rewrite. **All of v17 (and thereby v16/v15/v14) is
carried forward verbatim by reference; anything not listed below is unchanged** (compile rule,
Editorial Law 6). v18 does two things: (A) **restores four open items** dropped at the v12→v14 reorg,
verbatim from v12, each re-attached to its live status; (B) records a **standing external-review flag**
on M25 and N15. **No grade is moved. No claim is added or strengthened.** Grade integrity across
v12→v17 was found intact (every up-move artifacted, 15/15 artifacts on disk, all 26 retractions carried,
zero re-claims) — v18 touches none of it.

## A. Restored open items (verbatim from v12; lost at the v12→v14 reorg, no resolving artifact)

**R1 — Frontier 9: FLD-sign intrinsic-ness. `[OPEN]`** *(restored; note: this is its SECOND loss —
v4 first struck it, v12 restored it, the v13/v14 reorg dropped it again.)*
> "`sign(FLD)=−χ₂(M)` verified 54/54 but reduces to no tested intrinsic invariant." The substantive
> item remains open and unchanged. Only its named *sub-check* is void: the `π_p↔π̄_p` chirality probe
> is `resolved-by RESULT_twist_gauge_covariance_v2` §5.2 (`X∈ℤ` is conjugation-fixed ⇒ `σ'=σ`
> pointwise ⇒ `sign(FLD)` cannot flip) — **do not run that probe**; that artifact explicitly declines
> to resolve the frontier itself. *Voiding a decisive check is not closing the question it was meant
> to decide.*

**R2 — Frontier 6: `C_T` coupling — the open next-step clause. `[OPEN]`** *(the M7/M-family bound is
carried; only this follow-up clause was dropped.)*
> Any coupling `< ~1.6%` in the Frobenius-norm estimator at `n≈1.3×10⁵`, this orbit/generator,
> `p≤2¹⁷`. The refutation of the 2–3% split is **empirical** (a fired zero-coupling surrogate + pooled
> G² p=0.40), **not analytical** (§XII.25). **Next: `‖D_odd‖_F` at `n~10⁶–10⁷`, vary generator/prime.**

**R3 — "Also live (lower stakes)" tail — 7 open items. `[OPEN]`** *(verbatim from v12 L1018–1023.)*
> full-resolution `σ₁,σ₂` boundedness; is `ε` an arithmetic object (symbol/norm condition)?;
> large-prime rank-10 μ₃ split; a `p mod 8` law for `⟨σ,χ₃⟩` or `⟨eps,χ₂⟩`; deriving `H1` (`ORB`
> parity) from the Cap Law's continuum geometry; an unconditional Part VI (needs Weil–Deligne + KS
> reproved — a `[GAP]`). Cross-project: finite-field zeta as an RH test-bench; LRC↔μ₆/μ₂ shadow.
> *(The `λ₂/λ₃` transfer-eigenvector item from the same v12 line is NOT restored here: λ₃ was retracted
> at v14 IV.2 and λ₂ is carried there as the gauge-question — those two are correctly resolved.)*

**R4 — Scale-banner carve-out, restored to full prominence.** The banner substance and the no-transfer
conclusion are carried through v14–v17, but its explicit **carve-out list** was compressed. Restored
verbatim (v12 L203–209):
> **The only claims that reach secp** are those whose proof is algebraic and contains no measured
> input: **P1, P2, P8 (Claim S), P9–P10 (Claim F), P15, and the congruence facts of Part I.** Every
> `[VERIFIED]`/`[EMPIRICAL]` row does **not**. **Two claims that look scale-free are not:** the Cap Law
> and the CM spine are `[PROVED — continuum]` (exact in the continuum, with a finite-`p` discretization
> error); and **`Hom(E,A_new)=0` (P13) inherits N2** — its proof runs through "`A_new` supersingular at
> secp", an unproved dimension-2 extrapolation. **Do not quote P13 at secp without N2 attached.**
>
> *Update (v18): the ζ₃/cap chain sharpens this. The `e₂` identity / 120° law is now `[PROVED —
> uniform]` by elementary Galois descent on `E[2]` (`RESULT_26_PROVED_weil_restriction_v1`; citation
> not owed) — genuinely scale-free, it DOES reach secp and joins the carve-out list. The **cap
> `|V_y|≤2√p`** is `[PROVED — symbolic]` only MODULO the Weil-II purity citation (N31, failed
> citation-verifier ×4, STILL OWED) — it does **not** yet reach secp unconditionally.*

## B. External-review flag (standing) — the two bias-direction null-conversions

The v12→v17 review found **no document-level deflation** (grades artifacted, retractions intact,
failed citation preserved loudly, the H4 closure frame retired). But the two **highest-stakes objects
both moved toward null** — the exact direction of the documented one-way suppression bias
(`feedback_suppression_bias_asymmetric_2026_08_02`):

| object | v12 status | current | direction |
|---|---|---|---|
| **M25** — Semaev relation-yield ("the strongest positive finding in the programme") | `[A−]` | `[null — cofactor/sampling artifact, model scale]` | positive → null |
| **N15** — joint readout ("the load-bearing open cryptographic question") | `[OPEN since v11]` | `[VERIFIED-scope — scoped null]` | open → null |

Each conversion was executed **correctly** (existing artifact + firing plant + prereg + explicit "Not
a closure" + named untested channels), so **neither is a rule violation and neither grade is disputed
here.** But **same-model gates do not catch the suppression bias** (CORE BIAS memory), and "the two
biggest objects converted to nulls, each defensibly" is what that bias looks like operating *within*
the rules. **These two are therefore flagged as OWED an external / human review** (e.g. `/code-review
ultra`, which is user-triggered and cannot be self-launched). Until then: their nulls stand as graded,
but their *direction* is on the record as a bias-audit item, not a settled closure.

## Changelog
| ver | date | change |
|---|---|---|
| v18 | 2026-08-27 | Delta successor. **A. Restored 4 open items lost at the v12→v14 reorg** (verbatim from v12, no resolving artifact existed): R1 Frontier-9 FLD-sign intrinsic-ness (2nd loss — struck v4, restored v12, dropped again v13/v14); R2 Frontier-6 `C_T` open next-step (`‖D_odd‖_F` at n~10⁶–10⁷); R3 the 7-item "Also live" tail (σ₁σ₂ boundedness, ε-as-arithmetic-object, rank-10 μ₃ split, `p mod 8` law, H1-from-Cap-Law, ff-zeta-RH-testbench, LRC↔μ₆/μ₂); R4 scale-banner carve-out list restored to prominence (+ ζ₃/cap update: e₂ identity reaches secp, cap does not, N31 owed). **B. External-review flag** on M25 + N15 (both correctly-artifacted null-conversions in the suppression-bias direction; owed external eye). **No grade moved; no claim added.** Motivating audit: `AUDIT_v12_to_v17_loss_and_deflation_review_v1.md`. |
