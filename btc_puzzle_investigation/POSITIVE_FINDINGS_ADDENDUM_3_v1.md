> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS — ADDENDUM 3 (session 2026-08-10)

**Feeds the next master compile** (current head `POSITIVE_FINDINGS_MASTER_v8.md`, 2026-08-09). Additive:
records this session's results; changes nothing in v8. Two attach to the **sub-Rayleigh deficit frontier
(N7 / §XI.15)** as *characterizations* (narrowing where the deficit's organization is NOT); one is a new
analytical lock. Each item carries its grade and its source RESULT. Deficit itself: **unchanged** — real,
matched-null-surviving, universal, mechanism-open; row-budget shadow still its live candidate.

---

## A — 1-D "Intertwined Fourier Proxy" `W_N` extraction route: LOCKED (analytical)
`[VERIFIED — decidable artifact]` · `RESULT_intertwined_proxy_WN_tested_v1.md`

A proposed discrete-log extraction folding the μ₃/GLV geometry proxy `F=xy` and the scalar character
`e_n(a·d)` onto one index `d`, claiming to bypass Kohel–Shparlinski via a β↔phase "lock". Closed three
ways: (1) literal — `β∈F_p` (255-bit residue) cannot phase-cancel `e_n∈ℂ` (`|e_p(β)−ω|=0.89`); (2)
steelman (cubic character `χ₃`, so `χ₃(β)=ω` genuinely) still fails — the lock needs `e_n(a(λ−1)d)=ω⁻¹`
∀d, a nontrivial character of d (`|mean_d|≈5e−5` for every a); (3) the coherent form is a mixed character
sum over ⟨G⟩ — inside the KS/Weil family, not outside it. **Scope:** closes the 1-D collapse-onto-`d`
extraction; does NOT touch the 2-D `U(a,b,c)` deficit. *(The "KS-bounded" line is `[CITED-pending`
`citation-verifier]` before any grade moves on it.)* **Standing caution for any future "project onto the
ζ₃ eigenspace" arc:** the pullback couples `a` and `b`, so the full `(a,b)` diagonal orbit is a forced
zero and the fixed-`a₀≠0` `b↦βb` grouping is informative but **not pullback-licensed** (forced only on
`a₀≡0`) — keep the geometry's μ₃ index and the scalar phase on separate axes.

## B — Deficit characterization 1: μ₃/GLV frequency-support (MAGNITUDE) — scoped null
`[EMPIRICAL — scoped null, τ-robust, well-powered]` · `PREREG_mu3_glv_frequency_support_v1/v2.md` ·
`RESULT_mu3_glv_frequency_support_v1.md`

Is the deficit's carrier (the ~8% near-zero excess of `|U(a₀,b,c)|`) organized as μ₃-multiplicative
**near-zero co-occurrence** within the GLV triples `{b,βb,β²b}`? Statistic = near-zero pair-count in
μ₆/±-reps vs the marginal-preserving Null-B (exact combinatorial moments). 9 prime-order curves in 5
windows (all qualifying primes, no filtering), 24 a-reps. **Pooled Stouffer Z = −1.47 / +0.66 / +0.08 at
τ=0.05/0.10/0.15** — τ-robust, sign-incoherent; `S_GLV≈1/3` (no bulk μ₃-grading). Controls: implementation
Var≈0, plant +5965, scatter −0.75. **Reads:** near-zeros are NOT μ₃-clustered in `b` to sub-percent power.
NOT touched: c-axis, additive-b, the `c=±b` diagonal, higher μ₃-moments (→ item C).

## C — Deficit characterization 2: μ₃ PHASE-within-triple — scoped null (+ a caught null-miscalibration)
`[EMPIRICAL — scoped null, corrected null]` · `PREREG_mu3_phase_within_triple_v1.md` ·
`RESULT_mu3_phase_within_triple_v1.md`

The phase complement: μ₃-isotype alignment of the gauge-invariant real parts within a triple
(`ψ=|Σ_j ω^{-j}Re u_j|²/Σ|u_j|²`; forced ± gauge = per-rep conjugation, handled). Controls: gauge
self-test 0.00, plant +142, negative flat.
- **Null-miscalibration caught, not reported as a find.** The first (analytic per-block) null pooled the
  correlated `(a₀,c)` blocks as independent, underestimating variance ~2.85× and returning a spurious
  **pooled +10.36** — flagged by the *tell* that per-prime Z was ~constant (+3.4) across a 10× N range (a
  √N-flat Z = variance artifact). The negative control missed it (randomizing phase destroys the
  inter-block correlation that inflates the variance).
- **Corrected decision** (empirical global-repartition null, `mu3_phase_within_triple_globalnull_v2.py`):
  per-prime Z +0.57…+0.68, **pooled Stouffer Z = +1.88 < 3 → scoped null**.
- **Sub-threshold observation (flagged, not a finding):** the corrected per-prime Z is a *consistent* small
  positive (~+0.6). Plausibly the **forced λ-orbit-character correlation** — by the pullback the triple is
  `U` at `{a₀,λ⁻¹a₀,λ⁻²a₀}` — not a leak. Resolving forced-vs-real needs the **CM/non-CM discriminant**;
  not a fired cell, not run.
- **NOT closed (phase-specific, named):** higher-order phase invariants; the **imaginary-part isotype**
  (gauge-washes to `ΣIm²` at 2nd order — a distinct object this real-part statistic does not bound); and
  **c-column-specific phase structure** invisible after pooling. A null on ψ licenses none of these.

## Net effect on the deficit frontier (N7 / §XI.15)
The deficit's organization is **not** in the μ₃-graded `b`-frequency channel — neither near-zero magnitude
co-occurrence (B) nor real-part phase isotype (C). This narrows the mechanism search without touching the
effect. **Named next probes:** higher-order phase invariants; the c-axis / `c=±b` diagonal; and the
p-scaling const-vs-1/log-p re-test (`RETROSPECTIVE_FINDING_01` §4) — each its own pre-registration.

## Methodological ledger note (for the master's Anomaly-Drill layer)
A "must-fire" control can still MISS a variance-miscalibration when it does not share the signal's
**correlation structure**. The diagnostic that caught it here was **effect-size scaling with N**: a pooled
Z flat as N grows is a variance artifact, not a signal. Both directions of the asymmetric-rigor loop held
— the probe was run and its +10.36 taken seriously (no suppression), and audited to null before being
reported (no inflation).
