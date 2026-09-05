# RETROSPECTIVE FINDING 01 — the sub-Rayleigh deficit: a real anomaly demoted at consolidation

**Date:** 2026-08-04. Executes worklist item S2 of `RETROSPECTIVE_suppression_audit_v1.md` (top-down).
**Grade of the underlying object:** `[EMPIRICAL — 7 primes, pre-registered, control-surviving]`, unchanged.
**Grade of this finding:** `[AUDIT — consolidation-phase demotion, evidenced below]`.

This is not a new measurement. It is the trace of the project's **self-declared #1 open lead** (the joint
(x,y) shadow, master §VI / §XI.1) through the interpretation/consolidation layer, and what the master
says about it now versus what the RESULT files establish.

---

## 1. What the object actually is (established, not disputed)

The 0.93–0.96 joint-(x,y) alignment is `Corr(a₀) = (1/(n−1))·Σ_{(b,c)}|U(a₀,b,c)|` — an **l¹ norm** over
harmonics, verified point-space-vs-direct-sum to `rel ≤ 2.3e−16` (`harmonic_support_pattern_v1` C1).

Across two pre-registered runs (`harmonic_support_pattern_v1`, `subrayleigh_deficit_locus_v1`, both
2026-07-20) and three follow-ups (`harmonic_deficit_locus_v1`, `y_channel_chi2_vs_axis_v1`,
`row_budget_lowtail_v1..v3`):

- **The character's harmonics are systematically SMALLER than a random unit-phase target's** — a
  `0.06–0.10%` deficit in `mean|U|`, **one-directional at 7/7 primes**, growing with p (`−3.7σ` at p=163
  → **`−13.9σ` at p=2089**; pooled Stouffer **`Z = −13.99`**).
- It **survives the exact value-multiset control** (MC2 permutes character values, preserving the exact
  multiset and `Σg(d)=−1`; deficit unchanged to the third decimal).
- It is carried by an **~8% excess of near-zero harmonics** (`r<0.10`), plus a thinner high tail.
- It holds for **EVERY character**, not a₀=1 (24/24 orbit representatives at p=2089, median z=−12.58).
- It is **distinct** from the χ₂(y) 0.470 saturation (`y_channel_chi2_vs_axis_v1`, controls fire).
- **Two mechanisms were REFUTED without refuting the effect**: the 4th-moment/Δ=0 coincidence
  (`subrayleigh_deficit_locus §2`, pre-committed threshold, `Z(M4)=+0.95`), and the b=0-axis locus
  (`harmonic_deficit_locus`, a **wrong-null artifact** — the null omitted the forced Hermitian symmetry
  `g(n−d)=conj(g(d))`; symmetry-matched null collapses the on-axis −10% to −0.1..−3.8%). **The AGGREGATE
  ~−0.1% diffuse deficit survives the matched null.**

**This is the project's cleanest example of "refuting a mechanism ≠ refuting the claim."** The effect is
real, matched-null-validated, universal over characters, and mechanism-open.

---

## 2. The demotion (the finding)

The master v4 (`POSITIVE_FINDINGS_MASTER_v4.md`, the flagship "read this first" ledger per CLAUDE.md §1)
handles its own #1 lead in three ways, all pointing suppressive:

**(D1) The killing control is mis-attributed.** Master §VI/M14 caveats the 0.93 with *"the scalar-fidelity
statistic does not separate the character from random."* But `Σ_{b,c}|U|² = p²(n−1)` is a **forced
conservation, machine-zero-identical for the character and every random unit-phase target**
(`harmonic_support_pattern_v1` Arm B). **Any l²-normalized fidelity statistic is therefore forced equal
across targets — it cannot separate anything.** Its failure to separate is a property of the *statistic*,
not a bound on the *lead*. The master presents it as a limitation of the lead. *(Triage Q2: a control
forced to the same value for any target validates nothing.)*

**(D2) A completed run is still listed "NOT YET RUN."** Master §XI.1 says the frequency-support / which-
(b,c)-carry-the-alignment pattern is *"set up, pre-registration required, NOT YET RUN."* It **ran**
(`harmonic_support_pattern_v1`, 2026-07-20): the alignment is **Rayleigh across ~p² harmonics, no
active/starved split** (top 1% carry 2.7% = uniform; `N_eff/|S| → π/4` exactly). Plausibly true at v4's
writing (same day); **stale by two weeks as of this audit, in the direction of understating what is known.**

**(D3) The real anomaly the lead produced is absent from the master.** Master v4 cites **none** of the
five RESULT files of this thread and lists **no** frontier for the deficit (Part XI stops at 14; the only
"deficit" in the master is the *unrelated, fully-explained* equipartition one, M15). The deficit is
tracked as **Frontier #17** only in `POSITIVE_FINDINGS_ADDENDUM_2` and `PROJECT_SUMMARY` — it fell out in
the v3→v4 Part-XI renumber. **This is the documented H3→H4→master degradation pattern
([[feedback_verify_external_critiques]]: "master dropped the 5th frontier") recurring on a −13.99σ object.**

Net: the flagship document caveats its #1 lead with a control that can't separate, calls a done run
undone, and omits the one real anomaly the lead yielded. None of these is a false statement about the
data; together they read the lead down.

---

## 3. What is NOT the mechanism (ruled out here, with the argument)

The Weil ceiling (`|U_char| ≤ 4√p+1`; random targets exceed it, e.g. 5.5√p at p=2089) was excluded in
`harmonic_support §2` by declaration ("bounds the max, not the mean"). **The declaration is correct, and
here is why (so it is not just asserted):** at the pinned l², a thinner high tail with the *same* Σ|U|²
forces *more* mass into the mid/upper body, i.e. **fewer** near-zero harmonics — the **opposite sign** of
the observed near-zero *excess*. The ceiling explains the (secondary) thin high tail; it **cannot** be the
cause of the (dominant) low-tail excess. No ceiling-clipped surrogate is needed to see this.

The live mechanism candidate remains the **row-budget shadow** (Frontier #17: per-frequency conservation
`Σ_a|U(a,b,c)|² = n(n−1)`; is a near-zero at row a₀ the shadow of budget taken by other rows?), actively
worked in `row_budget_lowtail_v1..v3` (v3: F11 confirmed, C=−0.4950, subleading correction named). Open.

---

## 4. The re-test (decision-relevant; explicitly underpowered before) → goes to `experiment-designer`

`subrayleigh_deficit_locus §5` measured the p-scaling slope `s = −0.163` but **could not separate `const`
from `1/log p`** (Δ ≈ 1σ, pre-declared underpowered). This is the decision-relevant unknown:

- **`const` (or `1/log p`, ~flat):** the deficit is a **persistent structural property** of the
  curve+character system — it would still be present at secp's scale. A real handle, not a small-p artifact.
- **decaying (`1/√p`, `1/n` — already excluded):** vanishes at scale.

**Re-test:** power the scaling — enough enumerable model primes over a wide enough range (the row_budget
lineage already reached p=19231, so ≫2089 is feasible) to separate `const` / `1/log p` / residual decay
at ≥2σ. Pre-register statistic, prime schedule, null (symmetry-matched, per the wrong-null history on this
exact object), power, and the falsification threshold. **Promoting a false positive here is acceptable per
the session mandate; a persistent deficit that dodged the master is the thing being hunted.**

## 5. Ledger action
- **Restore the deficit to the master** as a live Not-Established / Frontier item (it is real, −13.99σ,
  mechanism-open, and currently absent). Cross-reference ADDENDUM_2 §A2.5 / Frontier #17.
- **Re-word the M14 caveat**: the scalar-fidelity control is *forced* non-separating (pinned l²); it is not
  a bound on the lead. The lead's real status is: Rayleigh in the (b,c) basis (no unitary concentration) +
  a real, universal, mechanism-open sub-Rayleigh deficit.
