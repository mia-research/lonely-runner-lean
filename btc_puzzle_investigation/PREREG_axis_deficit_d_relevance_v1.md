# PREREG — Does the b=0 axis deficit carry any d-information? (probe #2)

**File:** `PREREG_axis_deficit_d_relevance_v1.md`  **Date:** 2026-07-21  **Status:** PRE-RUN.

**Scope + expectation, up front.** Model curves `E:y²=x³+7`, prime order `n`, primes 163–2089. The b=0
axis deficit (`RESULT_harmonic_deficit_locus_v1`, `..._y_channel_chi2_vs_axis_v1`) is a **set-level**
statistic — a sum over all `d`. By the directory principle (only a joint property of the SET survives
the ECDLP scramble; a cheap per-point readout that recovered `d` would BE a break), the extraction arm
is **expected null** and is run to **bound**, not to hope. Nothing transfers to `2²⁵⁶`.

---

## 0. WELL-POSEDNESS (why "d-predictive" was rephrased)

The axis `A(a₀,c)=U(a₀,0,c)=Σ_d e_n(a₀ d) e_p(c y_d)` is aggregated over all `d`; it does not depend on
any single `d`, so "predict a specific `d`" is ill-posed. The strong automorphism relabel `d→s·d`
(`s∈(Z/n)*`) maps `A(a₀,c) → A(s⁻¹a₀, c)` — i.e. relabeling is exactly a **change of frequency a₀**. So
the set-level question is whether the deficit is **a₀-invariant** (a generic property of the y-marginal,
carrying no labeling/`d` information) or **a₀-specific** (carries labeling structure).

---

## 1. OBJECTS

- Axis deficit at frequency `a₀`: `D(a₀) = mean_{c≠0}|A(a₀,c)| − mean_{c≠0} E_r|A_r(a₀,c)|`, random
  target `g_r(d)` iid unit phase (same construction as the locus runs).
- Per-point readout (Arm B): a pre-committed `d`-free `f(x_P, y_P)` on single points `P=[d]G`.

---

## 2. FORCED FACTS — zero evidence

- **F1 GLV invariance `[VERIFY]`:** `U(a,0,c)=U(λa,0,c)` (from `U(a,b,c)=U(λa,βb,c)` at `b=βb=0`), so
  `D(a₀)=D(λa₀)` exactly. The a₀-sweep must therefore be read modulo the size-3 λ-orbit; only variation
  **beyond** the λ-orbit is evidence.
- **F2** the deficit exists at `a₀=1` (`−10..−13%`, input, not re-scored).

---

## 3. STATISTICS (frozen)

### ARM A — set-level d-relevance (is `D(a₀)` a₀-invariant?)
Sweep `a₀` over a **diverse shuffled sample** of `(Z/n)*` (≥ 200 values, seed-fixed, NOT lexicographic —
per the diverse-sampling rule). Statistic: the spread `sd_{a₀} D(a₀)` vs a matched null (permute the
`(a₀→D)` assignment) and vs the forced λ-orbit spread (which must be ~0 by F1).
- If `D(a₀)` is constant across the sweep (spread ≈ the λ-orbit/noise floor): the deficit is a **generic
  y-marginal property, a₀-invariant ⇒ carries no labeling/`d` information** — a bounded set-level
  characterization with no per-key content.
- If `D(a₀)` varies beyond the λ-orbit: the deficit magnitude is a₀-specific; characterize which a₀.

### ARM B — per-point extraction (expected null, run to bound)
Pre-committed `d`-free readouts, each `f(xP,yP)` only: `f1=legendre(yP)`, `f2=yP mod 3`,
`f3=high-bit(yP)`, `f4=legendre(xP)` (comparator). Target predicates `π(d)∈{LSB(d), d mod 3}`.
Statistic: rank correlation / AUC between `f` and `π`, against the **strong automorphism null**
(`P→[s]P`, geometry fixed, labeling scrambled; `π` relabeled by `π(s⁻¹·)`; `R≥500`). Report the bound.

---

## 4. TAUTOLOGY GUARD / CONTROLS / FLOAT

- **Guard (code-level):** every `f` has signature `f(xP,yP)`; `inspect.signature` asserts args ⊆
  `{xP,yP}`, never `d`, `a₀`, or a `d`-indexed array. Violation aborts.
- **Controls (must fire):** F1 λ-invariance to `<1e-6`; PLANT — a synthetic `f=LSB(d)⊕noise` must be
  flagged by Arm B (else no result); FLOOR — `f4` and a random-per-point value land in the null band.
- **Float:** curve/group + grids exact int; float only in the character sums / magnitudes; decisions are
  rank/permutation, no float threshold.

---

## 5. PRE-COMMITTED OUTCOME TABLE (no dismissal language)

| Case | Reported as |
|---|---|
| Arm A: `D(a₀)` a₀-invariant (spread at the λ-orbit/noise floor) | "The axis deficit is a generic, a₀-invariant y-marginal property on these primes — a bounded set-level statistic carrying no labeling/`d` information. The locus finding is structural, not per-key." (expected) |
| Arm A: `D(a₀)` varies beyond the λ-orbit | "The deficit magnitude is a₀-specific: [characterize]. New bounded object; needs its own follow-up. Still no per-point claim." |
| Arm B: all `f` in-band vs the strong null | "No pre-committed cheap `d`-free readout predicts `π(d)` above the automorphism-null floor (power stated). Scoped bound: method+sample+floor+readout-list; does not exclude other readouts." |
| Arm B: an `f` extreme vs the strong null | "Extraordinary vs the ECDLP prior — treated first as a control/tautology-guard failure; re-audited before any positive statement. A genuine such hit would be an ECDLP result and must clear every control twice." |
| PLANT fails or F1 fails | **No result.** Debug; re-run. |

---

## 6. OUTPUT TYPE

Bounded characterization (Arm A) + a scoped bound (Arm B). Never an ECDLP/extraction/security verdict;
the extraction arm's expected result is null and it is run to bound. Model primes only; no `2²⁵⁶` transfer.

## Files
- `axis_deficit_d_relevance_v1.py` / `.log`; `RESULT_axis_deficit_d_relevance_v1.md`; `_DEVIATIONS.md` if any.
