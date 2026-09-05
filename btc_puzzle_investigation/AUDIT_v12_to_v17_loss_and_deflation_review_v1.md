# Audit: master lineage v12 → v17 — loss trace + deflation review

**Date:** 2026-08-27. **Trigger:** user concern that a prior session moved the handover/master
documents forward without asking, "smoothing, deflating, regressing to default training data."
**Method:** git provenance; line-count/mtime map; `compile-diff` gate (v12 → v17+ADDENDUM_1–4,
context-isolated); independent spot-checks of the pivotal claims (I did not take the subagent's
summary on trust). **Companion:** `ANALYSIS_external_claims_reconciliation_v1.md` (the paste audit
that started this).

## Verdict (three parts)

1. **"Moved forward without asking" — within autonomy, not a bypass.** Every master v2–v17, all 4
   addenda, the compendiums are **untracked working files — nothing committed or pushed** (git holds
   only the Jul-17 handovers). Versioning-forward is the required behavior (CLAUDE.md §1); file I/O is
   a Claude-alone decision (§9). The unsettling artifact — v12 (1671 ln) → **v13 (188 ln)** — was a
   transient *audit rewrite* that explicitly did **not** read v12 lines 1–1600 and **mandated** a
   restoration. **v14 IS that restoration** ("Full Corpus Revision," L1; scale banner restored L434;
   M1–M24/N1–N19 carried verbatim; compile rule re-encoded L483). The scary compression healed.

2. **Deflation at the DOCUMENT level — evidence runs against it.**
   - **No unartifacted grade-up.** Every UP-move (e₂ identity→PROVED; cap→PROVED-symbolic;
     M26→VERIFIED-CM; N16 discharged) names an artifact that exists on disk (15/15 verified present).
   - **All retractions carried; zero re-claims.** Spot-checked the 3 highest-hazard: #4 amicable
     (kept open, not re-claimed), #10 "KS bounds χ₂" (preserved as "via **Kummer** sheaf, not KS"),
     #16 "√p·ζ₆ = CM fingerprint FALSE / universal-120°-law over-generalized" (preserved as N32).
     *(#16 is the same over-generalization the external paste re-committed — see reconciliation §4.)*
   - **The failed citation is preserved loudly**, not smoothed: N31 "Weil-II purity … failed
     citation-verifier ×4 … STILL OWED" survives v14→v15→v16→v17 intact.
   - v14 **retires** the old H4 "door-map / honestly-open" closure frame (L435) and makes
     "honestly/genuine" a standing audit trigger (L480). Closure-frame/self-cert scan of v17 is clean.
   This is the **opposite** of the H3→H4→master liquidation (`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`).

   **BUT — one bias-relevant flag (this is the real answer to "were they deflating").** The two
   highest-stakes objects both moved toward **null**, the exact direction of the documented one-way
   suppression bias (`feedback_suppression_bias_asymmetric_2026_08_02`):
   - **M25** Semaev relation-yield — "the strongest positive finding" — A− → `[null — cofactor/
     sampling artifact, model scale]`.
   - **N15** joint readout — "the load-bearing open cryptographic question" — OPEN → `[VERIFIED-scope
     — scoped null]`.
   Each was done **correctly** (existing artifact + firing plant + prereg + explicit "Not a closure"
   + named untested channels), so **neither is a rule violation**. But same-model gates do not catch
   the suppression bias; the pattern — the two biggest positives converted to nulls, each defensibly
   — is what that bias looks like when it operates *within* the rules. **Owed a human/external eye.**

3. **The banner / analytical-findings question (correct instinct) — RESOLVED.**
   - The **e₂ identity / 120° law is genuinely PROVED elementarily** — Galois descent on `E[2]`,
     Riemann–Hurwitz + character decomposition of `H¹` (`RESULT_26_PROVED_weil_restriction_v1`, read
     in full; §9: "citation-verifier is **not owed** … no grade rests on" the removed Kani–Rosen
     route). It is scale-free, valid at every `p>3` with `n` odd — **so it holds at 2²⁵⁶**, and
     dropping the SCALE BANNER *for this finding* is **legitimate**. Your intuition was right.
   - The **cap `|V_y(a)|≤2√p` is PROVED-symbolic MODULO the Weil-II purity citation** (N31, owed).
     For *this* link scale-freeness is conditional — and v17 keeps that caveat. Correctly scoped.

## Pre-v12 (checked) — clean
Scale banner present in **every** master v1→v12 (hits 1→15 as the doc grew 253→1560 ln,
monotone-additive). Handover-era loss (H3→H4) already audited and **repaired into v12**. Losses
concentrate at the v12→v14 reorg, below.

## Confirmed losses (v12 → v14+; all low/mid stakes, verified absent downstream)

| # | v12 item (line) | status |
|---|---|---|
| L1 | **Frontier 9 — FLD-sign intrinsic-ness** (L928): "sign(FLD)=−χ₂(M) verified 54/54 but reduces to no tested intrinsic invariant" | **LOST** — "FLD" 0 hits in v13–v17; no M/N home; no resolving artifact |
| L2 | **"Also live" tail — 7 open items** (L1018–1023): σ₁σ₂ full-resolution boundedness; "is ε an arithmetic object?"; large-prime rank-10 μ₃ split; `p mod 8` law for ⟨σ,χ₃⟩/⟨eps,χ₂⟩; derive H1(ORB parity) from Cap-Law geometry; ff-zeta-as-RH-testbench; LRC↔μ₆/μ₂ shadow | **LOST** — 0 hits v14–v17; no home, no artifact |
| L3 | **Frontier 6 next-step clause** (L919): "‖D_odd‖_F at n~10⁶–10⁷, vary generator/prime" | **PARTIAL** — M7 bound carried; the open follow-up not restated |
| L4 | **Scale-banner carve-out** (which claims reach secp: P1,P2,P8,P9–P10,P15,Part-I congruences) | **DEMOTED** — banner substance + no-transfer conclusion carried; the explicit carve-out list compressed. *Worst-case guard "Do not quote P13 unconditionally" DOES survive (v14 L358).* |

## Recommended repair (pending user OK — edits the live master)
Write **v18** (delta successor) restoring L1, L2, L3 as live open frontiers (or resolve-by-artifact
if one exists), and restoring L4's carve-out list to the banner. Do **not** touch grades — grade
integrity is intact. Separately, surface the M25/N15 suppression-direction pattern for external eyes.
