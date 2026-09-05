# RESULT — §2·CAL and §8 mechanical debts of `PREREG_incomplete_shortscalar_v2`

**Date:** 2026-07-30. **Target spec:** `PREREG_incomplete_shortscalar_v2.md`, freeze SHA
`d560abddebdeee87ad15721773a842b08e6d77903b3dff11eca8a52d7645ae5c`.

**This file does not amend v2.** The freeze SHA covers every byte through the end-of-body marker,
so editing v2's grade slot would break it. The two mechanical debts are discharged *here*, against
that SHA; the frame layers remain owed to the unavailable gate.

| debt | grade | verdict |
|---|---|---|
| **§2·CAL** — FWER calibration of the primary rule | `[VERIFIED — 20 000 reps]` | **DISCHARGED, clean** |
| **§8** — exactness over every named script | `[VERIFIED — AST scan + object-level triage]` | **DISCHARGED with 3 required repairs** |

---

## 1. §2·CAL — the primary rule is calibrated

**Artifact:** `holm_fwer_calibration_v1.py` → `CAL_holm_fwer_v1.log`.

**What was at risk.** v2 §2.1 uses the control ensemble twice — once to form the leave-one-out mean
`mbar`, again as the reference distribution for the rank. The v1 self-audit named this as the
obvious place for an anti-conservative null.

**Primary block** — B=1e4 sample sizes (sextant/norm `M`=18 000, flap `M`=6 000, C_T `M`=36 000,
joint `M`=18 000), `K=999`, **20 000 reps**:

| law | `P(p ≤ .05)` | `P(p ≤ .01)` |
|---|---|---|
| sextant | 0.0505 | 0.0102 |
| norm | 0.0505 | 0.0093 |
| flap | 0.0501 | 0.0109 |
| C_T | 0.0456 | 0.0089 |
| joint | 0.0471 | 0.0101 |

> **Holm FWER at nominal 0.05 = `0.0482`** (MC se 0.0015).

Every per-law p-value is valid at both thresholds; the family-wise rate sits just below nominal.
**The leave-one-out scheme does fix the double-use.**

**Robustness — 7 further blocks, all FWER within ~1σ of nominal:**

| block | FWER (nominal 0.05) |
|---|---|
| norm-band vector: record-head + even tail | 0.0508 |
| norm-band vector: record-head + decreasing tail | 0.0532 |
| norm-band vector: uniform 4-cell | 0.0482 |
| norm-band vector: adversarial skew (0.90/0.06/0.03/0.01) | 0.0512 |
| `K = 199` | 0.0462 |
| `K = 999` | 0.0460 |
| `K = 4999` | 0.0502 |
| small-`M` + adversarial skew (10 000 reps) | 0.0529 |

Two things this settles:
- **The norm-band cell vector does not matter.** It was not recoverable from the record files (only
  the head is exactly derivable: `P(cell 1) = (3/16)·2π/√3 = 0.6802` from the §0 density law). Since
  the decision is a *rank* against a matched ensemble, not a χ² approximation, the vector cancels —
  demonstrated across four vectors including an adversarial skew, rather than assumed.
- **`K` does not matter for validity**, only for p-grid resolution.

**Contrast with the demoted statistic.** The pooled `T_dev` null was the one that failed to
replicate (`FPR@.05` of 0.0493 vs 0.074 across two runs, ≈3σ apart). The per-law + Holm rule is
stable across all eight blocks above. The inversion fixed the calibration as well as the power.

*Scope: this is a calibration of the decision procedure under its own null model, using floats and
an RNG for the multinomial draws — a study of the instrument, not a signal-path computation (the
carve-out the v1 self-audit declared). The real run computes `G_ℓ` as `fractions.Fraction` on
integer counts.*

---

## 2. §8 — exactness: core is clean, three repairs required

**Artifacts:** `CAL_check_no_float_v1.log` (raw AST scan), `float_triage_v1.py` →
`CAL_float_triage_v1.log` (hit → enclosing function).

**The raw scan is not the answer.** `check_no_float.py` is a blunt AST guard: it flags every float
literal and every `/`, and **cannot distinguish `Fraction / int` (exact) from `float / int`
(lossy)**. It fires on 7 of 8 scripts, 98 hits, exit 1. A hit is a review flag, not a violation —
so each was mapped to its enclosing function.

### 2.1 The exact lift/point core is CLEAN

Zero hits inside any function v2 reuses for the lift, the points, or the cell readouts:

`eis` · `sextant` · `reduced_basis` · `rdiv` · `enorm` · `mul_jac` · `eps` · `om` · `om2` ·
`reduce_P` · `Lift.__init__` · `Lift._rdiv_vec` · `Lift.eis_scalar` · `Lift.eis_array` ·
`Lift.state_vec`

Two files (`eisenstein_lift_sextant_exact_v1.py`, `lift_sextant_law_proof_v1.py`) are clean outright.

**This was verified at the object level, not by list-match.** Every reused name was resolved against
the files' ASTs first — because a triage keyed on a stale name list reports zero by construction
(the tag-count failure mode, `DEGRADATION_AUDIT_H3_TO_MASTER_v1`). Three names did not resolve:
`N` and `enorm` are absent from `eisenstein_lift_sextant_exact_v1.py` (they live in the rhombus
file; v2's inventory attributes them to the wrong one of the two files it lists — a documentation
error, no effect, that file has zero hits), and `state` is a method of `Lift`, covered by the class.

### 2.2 ★ Three genuine issues — all outside the core, all required before a run

**(R1) `ct_event_complete_v1.py:72`, in `prime_order_curve` — float sqrt as an integer bound.**
```python
if not all(n % q for q in range(2, int(n ** .5) + 1)): return None, None
```
`n ** .5` is an IEEE double sqrt of a big integer, then truncated. For `n` beyond 2⁵³ the bound can
land below the true `⌊√n⌋`, so a divisor just under the root is never tested and a composite is
declared prime. This selects the curve. **Repair: `math.isqrt(n)`.** (It is also infeasible as
trial division at ladder scale, so this path cannot be the one used at `p_hi`/secp — but it must
not silently mis-select at the small rungs either.)

**(R2) `surrogate_counts` — float probability vectors generate the controls, and v2 §8 does not
declare this carve-out.** Lines 224 (`s / s.sum()`) and 233 (`np.clip(T2p, 1e-12, None)`) build the
surrogate distribution in float. No key-derived value is in that path, so it is defensible — but
v2 §8 declares only two carve-outs, (i) C_T eigen/G²/log as a monotone ranking value and (ii)
θ/δ*/CDF as report-only. **A float-driven control generator is neither.** Repair: either add an
explicit third carve-out to the spec, or draw the surrogate from integer/`Fraction` weights.

**(R3) `selftest` (9 hits) is named in v2's inventory as "`--selftest` firing calibration" and is
float throughout.** If a firing threshold is set from it, that is float precision deciding a
verdict — banned by `CLAUDE.md` outright, not carve-out-able. **Repair: use `selftest` for smoke
testing only; the §3(c) plant fires-criterion must be the integer Holm comparison of v2 §2.2.**

### 2.3 Everything else is out of the primary path

| location | hits | why it does not apply |
|---|---|---|
| `main` (4 files), `analyze`, `theta_deg`, `theta_of`, `p0_closed`, `shoelace`, `_tri_circle_area.*` | 61 | drivers, plots, analytic overlays — report/label carve-out (ii) |
| `row_normalise`, `spectrum_stats`, `g2_factorisation` | 11 | the **deferred** C_T spectral probe. v2 §2.4 puts the primary C_T path on the 9-cell Fraction histogram and defers the spectral version — correctly, and this is why |
| `tdev_ceiling_exact_v1.py` (`ih_cdf`, `ih_quantile`, module) | 5 | every flagged `/` is `Fraction / int`; the two `float()` calls are inside `print` |

**(R4, procedural)** The run's driver must **import the named functions**, never call `main()` or
`selftest()`. Every hit above sits in a driver or a deferred probe; invoking one re-admits float.

---

## 3. Standing after this file

**Discharged:** §2 statistic (calibration), §5 power (ceiling proof, `tdev_ceiling_exact_v1.py`),
§8 exactness (subject to R1–R4).

**Still owed to the unavailable gate — FRAME layers, which no self-audit can discharge**
(`CLAUDE.md` §2a): **§1** object/disjointness · **§3** matched-control adequacy · **§6** scope ·
**§7** falsification · **§9** pre-commitment.

**Still owed, mechanical:** **§4** plant constructibility and firing — cannot run until the
short-box enumerator (tooling item 1) exists.

**`[PROVISIONAL — experiment-designer unavailable]` stands, and no grade may be promoted on a run
against this spec** (§2a condition 4). Gate attempted 3×: 2026-07-29 org access; 2026-07-29 weekly
limit; 2026-07-30 watchdog stall at 600s, having reached §8.
