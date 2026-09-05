# RESULT — cofactor restoration plant: confinement is CAUSAL (forward-confirmed) but INCOMPLETE — M25's pure-cofactor null has a robust residual

**Date:** 2026-08-30
**Author:** ZCode (Claude). Executes `PREREG_h5_cofactor_restoration_plant_v1.md` (mandatory
experiment-designer gate). Forward test of `RESULT_h5_cofactor_artifact_v1.md`'s backward
(r=0.96) cofactor conclusion, and of the external-review flag v18 placed on M25.
**Run (frozen, this session):** `h5_cofactor_restoration_run_v1.py` (`check_no_float.py` passes),
25 cyclic composite-order curves (generic j≠0) in p∈[10007,50021], m=3, |V|∈{4,5,6}, K=25, subgroup
indices c from the divisors of #E with q=#E/c≥200. Raw: `h5_restoration_results_v1.jsonl` (582 cells).
Analysis: `analyze_h5_restoration_v1.py` (within-curve c-label permutation null, B=10⁴).
**Grade:** `[VERIFIED — confinement causal, forward-predicted; magnitude INCOMPLETE, residual robust & open]`,
scoped to model curves.
**Bottom line:** inducing subgroup confinement on cyclic curves **does** restore the lever (β_induced>0,
perm_p=0.0001, plants fire, naive slope-1 excluded) — confinement is a real causal mechanism. **But it
reproduces only ~38% of j0's slope at |V|=6 (19–38% across |V|), robustly** — so M25's null is **not**
fully a cofactor artifact; a residual (~62% of the slope) is unexplained. **The forward test caught
what the backward correlation masked** — substantiating v18's suppression-bias flag on M25.

---

## 1. Plants (all fire — the test is informative)

| plant | result |
|---|---|
| **Confinement-verification** (every confined point's order divides q; ⟨c·G⟩ genuinely order q) | passed (no HALT) — confinement is by construction on cyclic curves, not the non-cyclic confound |
| **Synthetic-slope** (quo_conf := quo_full·c ⇒ slope must be 1) | **β_synth = 1.000** at every |V| — the OLS slope pipeline fires correctly |
| **c=1 null** (2nd independent full draw, must give T1≈0) | T1 = −0.001 / −0.001 / +0.001 (|V|=4/5/6), n=25 — baseline calibrated |
| **Additive +0.5** (T1 estimator) | shift recovered (carried from prior; T1 estimator calibrated) |

## 2. Result — confinement restores the lever, but short of j0's magnitude

`β_induced` = OLS slope of `T1_induced = logmean quo(confined ⟨c·G⟩) − logmean quo(full group)` on `ln(c)`:

| |V| | β_induced (SE) | perm_p | r² | β_j0 (target, same-curve) | β_induced / β_j0 |
|---|---|---|---|---|---|
| 4 | 0.056 (0.004) | 0.0001 | 0.52 | 0.301 | 0.19 |
| 5 | 0.115 (0.006) | 0.0001 | 0.70 | 0.386 | 0.30 |
| **6** | **0.206 (0.008)** | **0.0001** | 0.80 | **0.546** | **0.38** |

- **Direction confirmed, decisively:** β_induced > 0 at perm_p = 0.0001 (the 10⁴-permutation floor) every |V|.
  Confinement causally inflates quo. The naive "yield ∝ n₂" slope-1 law is excluded (|β−1|=0.79).
- **Magnitude shortfall is ROBUST, not a |V|-scaling artifact:** β_j0 was re-computed |V|-matched
  (0.301/0.386/0.546 at |V|=4/5/6); at every |V| generic confinement gives only 19–38% of it, the ratio
  decelerating (0.19→0.30→0.38), so extrapolation does not close the gap. At the pre-committed primary
  |V|=6: **0.206 vs 0.546, |diff|=0.34 — far outside the ±0.15 tolerance, ≫ SE (0.008).**

## 3. Verdict against the pre-committed rule (§9)

Outcome = **"β_induced > 0, perm-p<0.01, but 0.15 < |β_induced − β_j0| (right direction, wrong
magnitude)."** Pre-committed conclusion: *confinement reproduces the DIRECTION but not j0's magnitude;
do NOT close; name the residual = the slope gap; M25 null remains INCOMPLETE.*

**So M25's H1 leg is NOT fully a cofactor artifact.** Generic subgroup confinement is a real, causal
contributor (~38% of the slope at |V|=6), but a residual (~62%) is not reproduced by confinement on
generic cyclic curves. This refines — does not refute — `RESULT_h5_cofactor_artifact_v1.md`: the
r=0.96 correlation of T1 with log n₂ is real, but correlation over-stated the causal magnitude; the
forward test isolates it at ~0.38× and exposes the remainder.

## 4. The residual — two candidates, not yet separated (do NOT over-read)

1. **A j=0-specific effect (μ₆/GLV/CM) on top of generic confinement.** The forward curves are generic
   (j≠0) cyclic curves (cyclic j=0 curves are rare at model primes; pre-reg §9 defect 7). "j0 +
   induced confinement together" is not directly sampled, so a j=0-specific enhancement would appear
   exactly as this shortfall. This is the suppression-catch reading: M25 buried a real residual.
2. **A between-curve vs within-curve regression-structure difference.** β_j0 is a *between-curve* slope
   (one n₂ per j0 prime, regressed across 24 primes), while β_induced is a *within-curve* slope (many c
   per cyclic curve). Between-curve variation can conflate n₂ with other per-prime factors and inflate
   β_j0. This would make part of the residual methodological, not a real j=0 effect.

**Neither is established.** The decisive separator: find (or construct) a **cyclic j=0 curve**, run the
same within-curve c-sweep on it, and compare its slope to the generic cyclic curves' — a within-curve
measurement on j=0 isolates candidate (1) from (2). Owed as the next probe (its own prereg).

## 5. Disposition

- **M25 / N22 H1 leg** → re-graded from `[null — cofactor/sampling artifact]` to
  **`[cofactor confinement CONFIRMED causal (forward, perm_p=1e-4); magnitude INCOMPLETE — residual
  ~62% of slope at |V|=6, robust across |V|, mechanism OPEN]`**. This is a correction in the
  anti-suppression direction: the prior null was too strong.
- **v18's external-review flag on M25 is substantiated by an internal forward test** — the null was
  incomplete, and the forward prediction (not a same-model re-audit) is what surfaced it. The flag
  should stay OPEN and now points at a concrete object (the residual slope), not just "owed an eye."
- **Cryptographic scope unchanged:** secp256k1 is prime-order (no cofactor), so even the *confirmed*
  confinement part is absent at the target; the residual's relevance at scale is undetermined and not
  claimed. No 256-bit / ECDLP / keyspace claim.
- **Concurrent-work note:** produced as a standalone artifact; NOT folded into a master (the corpus is
  concurrently at v18 today). Folding — updating M25's grade in whatever the current head is — is a
  coordinated `compile-diff`-gated step, not done here.

## 6. Provenance
Exact-int signal path (#E, subgroup order q, index c, quo=vector_space_dimension, point orders,
divisor lists); floats only in logmean / OLS slope / permutation rank, each `# noqa: float — (stat)`
noted, `check_no_float.py` passes. β_j0 frozen from prior `h5_followup_results_v1.jsonl` as step 0
before any forward cell. Plants pre-committed; verdict from the pre-committed §9 cell. One saturated
cell dropped (pre-registered guard).
