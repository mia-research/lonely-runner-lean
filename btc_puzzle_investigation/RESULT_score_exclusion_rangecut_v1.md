# RESULT — `s<3/16` deterministic range-cut: PRE-REFUTED before data (exact Fréchet floor + 6648 counterexamples); closes the amplifier route, NOT the avenue

**Date:** 2026-08-13. **Adjudicates:** `PREREG_score_exclusion_rangecut_v1.md` (frozen). The pre-registration
gate ruled the test pre-refuted; this file records the **independent verification** of the two load-bearing
artifacts (trust-but-verify). **Artifact:** `scratchpad/score_exclusion_frechet_verify_v1.py` (exact integer
signal path; float guard clean).

## The proposed test and why it never needed data

Probe #1 asked whether the public predicate `[s(x_P) < 3/16]` (which the s-gate proved pins the **coordinate**
Cap-Law flap `eps_coord=0`, 0 violations to 2^256) also deterministically pins a **scalar-side** carry bit
`ε_scalar(d)=0` — which would be a non-circular ≤3-bit search-space cut on `d` for the ~68% core fraction.

**HAZARD rulings (from the gate, each verified here):**

1. **Not circular.** An implication `A(public) ⇒ ε(scalar)=0` does not *read* the 256-bit carry from public
   data (which `ANALYSIS §4` forbids); it would *pin* a 1-bit scalar value from a public predicate — a genuine
   non-circular amplifier if it held. So the test is well-posed; it dies on Hazard 2, not circularity.

2. **Exact Fréchet floor — the pin is algebraically impossible for a balanced carry.** With our own measured
   marginals `Pr[s<3/16] ≈ 0.68` (s_gate_v2) and `Pr[ε_u=1] ≈ 0.49` (joint_fiber v1),
   `Pr[s<3/16 ∧ ε=1] ≥ 0.68 + 0.49 − 1 = 0.17 > 0` for ANY joint law ⇒ a 0-violation pin is impossible;
   forced violation rate `≥ Pr[ε=1] − (1−0.68) ≈ 0.17`. **Independent verification (20 000 constructed keys,
   exact cross-product `enorm·16 < 3p`):** `Pr[s<3/16]=0.6793`, `Pr[ε_u=1]=0.4926`, floor `= +0.1719`;
   **OBSERVED joint `Pr[s<3/16 ∧ ε_u=1] = 0.3324` (6648/20000)** — 33% violations, and the joint ≈ the product
   `0.3347` ⇒ `s<3/16` and the scalar carry are **independent** (consistent with the two-key MI null). The pin
   is not merely impossible, it is empirically shattered.

3. **Already empirically refuted for the tool-7 carry.** `RESULT_eps_to_d_constraint_v1.md` executed the exact
   gate `s<3/16 ⇒ ε_7=0` and found **21–93 violations per cell** (p∈{43,547,907,1303}) — verified present.

**The one escape fails on power:** the only scalar bit rare enough to dodge the Fréchet floor is `ε=[c=0]`,
but on constructed full-range `Pr[c=0] ≈ 4/n ≈ 2^−254`, so `ε=1` never occurs at feasible N ⇒ firing control
dead ⇒ a "0-violation pass" is vacuous. A rate-matched rare bit chosen after looking is inadmissible (ordering).

## Grade, scope

**`[VERIFIED — deterministic refutation, exact artifact]`.** The deterministic-pin amplifier route
(`s<3/16` supplies the scalar carry) is refuted three independent ways: exact Fréchet inequality on measured
marginals, 6648 direct counterexamples (independence observed), and the prior `eps_to_d_constraint` run
(21–93 violations). **Payoff was moot anyway:** a perfect pin is ≤1 bit on 68% of keys, class ceiling ≈3 bits
(ARSENAL tools 6/7), and **no Babai/GLV compounding** (lattice reduction decomposes a *known* scalar; it does
not amplify a partial carry bit) — a constant factor, not a break.

**Closes the amplifier route, NOT the avenue.** Per the closure-burden rule, this is a refutation of one
specific mechanism (public core-membership ⇒ scalar-carry pin). It closes **no** avenue: CM/GLV at large, the
lattice/rare-carry repairs below, and the µ₆ Semaev solving-degree lever all remain open. Moves no grade up on
a citation.

## Minimal non-circular repairs (registered separately, not run here)

1. A **geometric/lattice** cut: compose `s<3/16` core-membership with a Babai step — escapes the single-bit
   Fréchet floor, but a run must FIRST exhibit a non-trivial scalar constraint from `s` before the lattice
   step is meaningful (none exists yet).
2. A **rare, pre-defined, firing-control-live** scalar carry on the constructed set with a matched MI test —
   no such object exists in the current arsenal.

Next actioned probe (user order): **#2 — the µ₆ solving-degree lever for the j=0 Semaev system**
(`ANALYSIS_semaev_cm_yield_mechanism_v1.md` P2), which lives outside the KS-bounded correlation frame and the
Fréchet-bounded single-bit frame entirely.
