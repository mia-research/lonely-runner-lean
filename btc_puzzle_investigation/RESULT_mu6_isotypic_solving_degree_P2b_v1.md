# RESULT — P2b: the μ₃/ω-isotypic structure of the Semaev system is real and exact, but gives NO solving-degree lever at m=2,3 (earned, tested δ_r null) — and this supplies the tested *mechanism* behind P2's null

**Date:** 2026-08-15. **Executes** `PREREG_mu6_isotypic_solving_degree_P2b_v1.md` after an
`experiment-designer` audit that **refuted the prereg's primary statistic** and supplied the corrected
one (§2). Scripts (exact GF(p), `check_no_float` clean): `omega_isotypic_staircase_v1.py` (σ-invariance
probe), `_v2.py` (mechanism + target-orbit), `delta_r_corrected_v2.py` (the non-forced test),
`delta_r_sweep.py` (13-cell sweep). No leakage/ECDLP claim; model-scale.

**Grade:** the σ-symmetry structure `[VERIFIED — exact, scale-free]`; the isotypic-block degree-lever
`[VERIFIED — scoped NULL, m∈{2,3}, p∈[523,601], last-fall degree]`.

## 1. The structure is real (the positive, stated first)
- **S₄ (m=3) is exactly σ-invariant** under `σ: xᵢ↦βxᵢ` (`β³=1`), weight `κ=0` `[VERIFIED]`; S₃ (m=2) is
  σ-covariant, `κ=1`. This is an exact, scale-free algebraic symmetry of the j=0 Semaev system.
- **The fixed-target decomposition ideal breaks it** — σ *rotates the target*: `σ(Sx)=β^κ·S(x, β⁻¹·t)`
  `[VERIFIED]`. This is the **mechanism** behind `RESULT_mu6_solving_degree_v1.md`'s fixed-target `d_LF`
  null: P2 measured the symmetry-*broken* object, so it could not see the symmetry either way.
- **The target-orbit ideal restores σ-invariance** (add `xT³−t³`, keep {t,βt,β²t}): 0-dim, quotient 36,
  clean **12/12/12** ω-isotypic split `[VERIFIED]`.

## 2. The experiment-designer gate refuted the naive lever statistic (`[PROVED — mechanical]`)
The prereg's primary `Δ_iso = d_LF(whole) − max_r d_LF^(r)` is **forced to ≡ 0**: σ-invariance ⇒ the
Macaulay matrix block-diagonalizes exactly by isotype ⇒ falls add non-negatively ⇒
`d_LF(whole)=max_r d_LF^(r)` identically. And the 12/12/12 is **three permuted copies of the
fixed-target quotient** (verified `12+12+12=36`) — the **already-known ≤κ=3 constant-factor automorphism
speedup**, not a degree lever. Both facts mechanically verified by the gate and re-verified here
(`fiber_check`: the three fibers at {t,βt,β²t} each have quo=12).

## 3. The corrected, NON-FORCED test — and its result (the *earned* null)
Corrected statistic (gate F1): `δ_r = d_LF(fixed-target) − d_LF^(r)(target-orbit block r)` — two genuinely
different ideals, so `δ_r` can take either sign; `δ_r ≥ 1` = a real degree lever.

**Result (13 cells: m=2 × 6 primes × 2 seeds, plus m=3):** `δ_r ≤ 0` in **every cell**. Representative:

| p | m | d_LF(fixed) | block d_LF {0,1,2} | δ_r {0,1,2} |
|---|---|---|---|---|
| 523 | 2 | 13 | {15,13,14} | {−2, 0, −1} |
| 523 | 3 | 34 | {36,34,35} | {−2, 0, −1} |
| 541 (seed2) | 2 | 12 | {12,13,14} | {0, −1, −2} |

The isotypic blocks resolve **at or above** the plain fixed-target degree — one block matches (δ=0), two
are worse. Block degrees are **largely curve-blind**: isotypes 1,2 sit at {13,14} for every m=2 prime;
only isotype-0 moves, and it *tracks the fixed-target `d_LF`* (both drop to 12 at p=541 seed2). This is
the leading-form curve-independence of `semaev_elimination_v1.py` (B1) manifesting per-block.

> **⇒ No μ₃/ω isotypic-block solving-degree lever at m∈{2,3}.** The symmetry reorganizes the system into
> isotypic blocks but does not lower the last-fall degree below the plain solve; the block degrees are set
> by the (curve-blind) leading forms, not by the ω-covariant lower-order terms.

## 4. Scope, power, and what is NOT closed (anti-enlargement, per `feedback_negative_bias_enlarge_nulls`)
- **Object:** a μ₃/ω isotypic-block **solving-degree** lever for the prime-field Semaev decomposition system.
- **Class:** prime-field summation-poly index calculus, whose binding cost is the last-fall degree.
- **Power:** the naive statistic is `[PROVED]` forced-null; the corrected non-forced statistic is measured
  `≤ 0` across 13 cells (never `≥ 1`); the block degrees are curve-blind (leading-form-forced).
- **Scope:** m∈{2,3}, last-fall degree, p∈[523,601], the isotypic-block channel.
- **OPEN — not closed by this:** (i) **m=4/5** (S₅/S₆), where the record notes an effect could be
  *stronger* — compute is intractable, so it is a *mechanism* question (see
  `ANALYSIS_mu6_solving_degree_m4m5_mechanism_v1.md`); (ii) the finer **ω-graded syzygy-module** structure
  beyond scalar per-block `d_LF`; (iii) the R1 **yield** channel (a separate real positive) and today's
  **P1′ phase** lead; (iv) full IC-cost accounting; (v) the separate 120°/CAP-uniformity and
  CM-Hecke/monodromy sub-threads. The σ-symmetry itself remains a real structural object — a potential
  lever via (i)/(ii), not a wall.

## 5. Process / provenance
- `experiment-designer` gate: RUN; **refuted the primary statistic** (forced-null) and supplied the
  corrected F1 — the gate did its mechanical job. The premature "structural null" asserted before F1 ran
  was withdrawn; this null is the *measured* F1 outcome.
- `check_no_float`: PASS on all four scripts. Owed: `citation-verifier` on Caminata–Gorla (solving degree
  ≥ last-fall degree) before any grade rests on that bound (inherited from `RESULT_mu6_solving_degree_v1`).
- Promotion into a master requires `compile-diff` (target master **v9**); this is a leaf RESULT, not a
  promotion.
