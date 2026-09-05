# PREREG (PROVISIONAL) — CM decomposition-count / relation-yield test (R1 follow-up)

> **⛔ SUPERSEDED (2026-08-09) — DO NOT RUN.** Written on session-resume without awareness that
> intervening sessions had already completed this exact test. The CM relation-yield question is
> answered by **`RESULT_semaev_cm_relation_yield_v4.md`** (pre-reg `PREREG_semaev_cm_relation_yield_v4.md`,
> experiment-designer-cleared 2026-08-07): **VERDICT A1 — candidate lever confirmed.** `#E`-matched CM
> relation-yield fires at all `|V|∈{4..8}` for both j0/j1728, GROWS with `|V|`, and is NOT the
> automorphism/closure artifact (the discriminator drafted in §3). Scope: 24 primes `p∈[523,823]`, small
> `p`, no mechanism claim, nothing transfers to `2²⁵⁶`. The grounding in §1 (j1728 supersingular at
> `p=211`) remains a valid caveat on my own `p=211` reproduction probe only. Retained for the trail.

**Grade slot: `[PROVISIONAL — experiment-designer unavailable]`.** Date 2026-08-05.
The mandatory experiment-designer gate (CLAUDE.md §2) could not run: **weekly usage limit,
resets 2026-08-09 15:00 Australia/Brisbane.** Per §2a this is *gate-unavailable*, not
*gate-failed*. This document records (a) frame-free MECHANICAL grounding I self-discharged, and
(b) a DRAFT frame design that is **owed to the gate**. **No test is run and no grade moves** until
the gate validates the frame (§2a condition 4). Tests the effect surfaced in
`RESULT_semaev_dsolv_statistic_power_v1.md` Finding 3.

## 1. Grounding — MECHANICAL, self-discharged (artifact: `scratchpad/grounding_cm_curves_v1.py`)

At `p=211` (`p≡1 mod 3` ⇒ ζ₃∈F_p; `p≡3 mod 4` ⇒ i∉F_p), the three harness curves:

| curve | (A,B) | \|E\| | j | \|Aut(F_p)\| | note |
|---|---|---|---|---|---|
| secp_j0 | (0,7) | 199 | 0 | **6** (μ₆) | ordinary, genuine CM automorphisms |
| nonCM | (5,11) | 208 | 158 | 2 (μ₂) | ordinary generic |
| j1728 | (3,0) | **212=p+1** | 1728 | 2 (μ₂) | **SUPERSINGULAR at p≡3 mod4; μ₄ NOT rational** |

Achievable orders: j=0 twists → {183,196,199,225,228,241}; j=1728 twists → **{212} only**;
matched-`|E|`: **j0 ∩ generic = {196,199,225,228}** (so secp_j0 at 199 has a generic-j match),
but **j0 ∩ j1728 = ∅**.

## 2. What the grounding changes (mechanical facts; frame implications flagged for the gate)

- **The prior "j1728 control" is contaminated.** At `p=211`, `y²=x³+3x` is supersingular
  (`|E|=p+1`, μ₄ not rational), a known-weak object with atypical decomposition structure — **not**
  a μ₄-CM ordinary control. So Finding 3's "both CM curves show it, j1728 strongest 13/15" is
  substantially a **supersingularity artifact**; the "j1728 shows it too ⇒ secp not special"
  reasoning (that dissolved the secp-specific candidate) is itself confounded. *(Frame implication:
  drop/replace j1728, or run only at `p≡1 mod 4` where it is ordinary — GATE decides.)*
- **A clean |E|-controlled comparison exists** for the μ₆ arm: secp_j0 (|E|=199) vs a generic-j curve
  at |E|=199. A matched *triple* including an ordinary μ₄ curve needs `p≡1 mod 12`.

## 3. DRAFT design — FRAME LAYER, OWED TO THE GATE (do NOT run on this alone)

*(Recorded so the gate has a running start 2026-08-09; every item below needs gate validation.)*
- **Statistic:** `quo` (decomposition/relation count) in the consistent regime, **unforced excess
  above the `m!` permutation floor** only; secondary = automorphism-quotient count.
- **Controls (DRAFT):** (i) **|E|-matched** secp_j0 vs generic-j (both ordinary) at equal |E| — kills
  the group-order confound; (ii) run at **`p≡1 mod 12`** so μ₆ (j=0) and μ₄ (ordinary j=1728) are both
  rational; (iii) **exclude supersingular curves** (check trace≠0).
- **Decisive discriminator (DRAFT):** re-count decompositions modulo the rational automorphism action
  (μ₆/μ₄/μ₂). Excess that **vanishes** under the quotient ⇒ automorphism bookkeeping, **no net
  index-calculus lever** (standard practice already exploits it); excess that **persists as independent
  relations** ⇒ candidate real relation-yield lever.
- **Firing control (DRAFT):** plant a curve/target with genuinely independent extra decompositions;
  the discriminator must flag them as independent (else it is blind).
- **Power / scope (DRAFT):** several |E|-matched pairs across a band of `p≡1 mod 12` primes; consistent
  regime at `m=3` is cheap; integer/exact counts. Scale caveat: `p` small — a structural (scale-free)
  reading needs the effect to survive |E|-control and the automorphism quotient, not just appear.
- **Pre-commitment (DRAFT):** (a) excess vanishes under automorphism-quotient ⇒ known bookkeeping, NO
  net lever; (b) excess tracks |E| ⇒ artifact; (c) independent excess persists under both controls ⇒
  candidate real lever, OOS + larger-`p` owed.

## 4. Self-audit (§2a condition 2)

- **MECHANICAL, discharged (artifact = the grounding script):** §1 orders/Aut/supersingularity facts;
  §2's "j1728 supersingular at p=211" and "matched-|E| secp/generic exists at 199."
- **FRAME, NOT discharged — owed to the isolated gate (my suppression bias operates here):**
  matched-control adequacy (§3 controls), the automorphism-quotient discriminator's validity, the
  firing control, the pre-commitment, and the drop/replace-j1728 decision. A self-written frame on a
  CM/leakage test is precisely what §2b says isolation must supply.

## 5. Disposition

- **Gate owed:** re-run experiment-designer on this draft after 2026-08-09 15:00 Brisbane; then
  implement to the validated spec, run `check_no_float.sh`, execute exact over GF(p), report vs the
  pre-committed outcomes.
- **No test run; no grade moved.** R1 stays OPEN (master v5 §XI.4). The Finding-3 effect stays
  `[EMPIRICAL — suggestive, confounded]`, now further qualified by the j1728-supersingularity catch.
- Cross-links: `RESULT_semaev_dsolv_statistic_power_v1.md` (Finding 3), `POSITIVE_FINDINGS_MASTER_v5.md`
  §XI.4, `scratchpad/grounding_cm_curves_v1.py`.
