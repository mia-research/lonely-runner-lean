# No-float re-examination — HIGH-risk nulls/certificates + rule/guard tightening

**Date:** 2026-08-27. **Trigger:** user tightened the rule to "no float anywhere unless justified and
noted," and asked whether float could be destroying results (manufacturing nulls). This is the
started-with-all-HIGH-risk pass. **Not exhaustive** — the ~558-file annotation backlog remains owed.

## Rule + guard changes (done)
- **`CLAUDE.md` no-float section rewritten:** float banned *everywhere*, exact by default; exemptions
  only via inline `# noqa: float — <reason>` naming a case (stat / display / hi-prec-xchecked); a
  discrete/algebraic **decision** in float has **no** exemption. Adds the second failure mode we kept
  missing: float doesn't only *smear* low bits of big ints, it *fakes* exactness (reports "dist 0.0"
  for a non-square) at any magnitude.
- **`check_no_float.py` rewritten + deployed:** scans **all** `*.py` (was a hard-coded 9-file list),
  catches numpy/math/cmath/`.real`/`.imag`/fractional powers (was blind to all of these), requires a
  *justified* noqa. **Baseline: 570/787 files carry un-noted float.**

## What was re-examined, and the verdict

### Category A — verdict decided by a float tolerance (~12 scripts) → **ROBUST, rule-noncompliant**
Files: `d2_twist_rigidity_certificate` (1e-12), `lmono_gkr_rank4_eigenderiv` (1e-10/1e-6),
`lmono_routeB_geom_iso_certificate` (1e-9), `n1_flap_bridge_v2` (1e-6), `mu3_glv_frequency_support`,
`mu3_phase_within_triple`, `n1_phase_cap_v2_controls`, `subrayleigh_deficit_locus` (1e-11),
`q4_principal_survival`, `curve_native_beam_scan_v2`, `xdomain_derivation_checks`.
- All operate on **model-scale** eigenvalue/character/phase quantities (|·|~O(√p), p≤~200). The
  float64 error budget (~1e-13 absolute) sits **orders of magnitude below** the tolerances
  (1e-6…1e-9), so those verdicts are numerically robust; a flip would need the true value to sit in a
  measure-zero band at the threshold. They **violate the new rule** (un-noted float) and are **owed a
  noqa or exact reimplementation**, but did not manufacture false verdicts.
- **Two marginal exceptions flagged, not cleared:** `d2_twist_rigidity_certificate` (1e-12) and
  `subrayleigh_deficit_locus` (1e-11) are only ~10–100× above the float floor. Both are **positive
  certificates that PASSED** (so the risk is false-*positive* = inflation, the low-risk direction for
  this project's bias), but they are **owed an exact recheck** for full rigor.

### Category B — key-path smearing in leak/null tests (the catastrophic case) → **SOUND**
The danger the rule exists for: float on a 256-bit key deletes the low bits where the signal lives,
before the test runs. **Checked the main leak harnesses — the data paths are exact:**
- `nk_leak_harness_v1–v4`: decomposition is **exact `Fraction`** (`Fraction(d-A,A).limit_denominator(256)`);
  `s.n` is the **Farey denominator ≤256**, not the key; features are **exact modular `pow(x,(p-1)//k,p)`
  / `%`** (small residues). `astype(float)` and `log2` touch only values `< 2^53`. **No smearing.**
- `n15_readout_confinement_runner` (the load-bearing recent null, N15) is **exemplary**: keys stay
  exact via modular `pow`; only small int labels stored; float appears **only** in the MI statistic,
  already tagged `# noqa: float`. Its scoped null is **not** float-contaminated.
- The one genuine exactness-in-float **lapse this session (Sym³ check) was caught and redone exactly**
  (`ANALYSIS_perfect_square_theme_rigidity_v1`, `sym3_exact.py`) — it gave the right answer, but exact
  is the standard.

## Systematic sweep (done 2026-08-27) — classification, not mass-annotation
`classify_float.py` bucketed all **~8,100 flagged lines**: SAFE-DISPLAY 911, SAFE-STAT 633,
SAFE-SKLEARN 19, REVIEW-DECISION 192, REVIEW-SMEAR 49, REVIEW-OTHER 6,289. `genuine_decisions.py`
then filtered REVIEW-DECISION down to the lines that actually decide a verdict from float — excluding
Sage-exact number fields, div-by-zero guards, `nan` sentinels, statistical p-value/z verdicts, and
already-noted lines — leaving **68 genuine float-exactness-decision lines** (`FLOAT_EXACTIFY_BACKLOG_v1.md`).

**Finding: all 68 are safe today.** Every one is **model-scale** (|·|~O(√p), p≤~200) where the
float error (~1e-13) is orders below the tolerance, **OR** high-precision Sage (`ComplexField(212)`,
tol `1e-50` — the CM-probe / Newton-diag eigenvalue tests), **OR** statistical. **None operates on a
256-bit key.** So the sweep confirms no float-manufactured verdict in the decision set — this is a
**rigor/compliance backlog, not a correctness emergency.**

**Policy decision — do NOT mass-annotate.** Auto-attaching `# noqa: float — <reason>` to the ~8,000
DISPLAY/STAT/OTHER lines would manufacture justifications not individually verified (e.g. asserting
"on exact data" for 633 STAT lines unseen) — that is a rubber-stamp at the annotation layer, the same
smoothing this project guards against. Instead:
1. **Enforce forward:** the guard is live; new/edited code must carry a justified note or be exact.
2. **Legacy stays PROVISIONAL** under the CLAUDE.md provenance clause — not silently blessed.
3. **Tracked exactify backlog = the 68** (`FLOAT_EXACTIFY_BACKLOG_v1.md`), priority the two nearest the
   float floor (`d2_twist_rigidity` 1e-12, `subrayleigh_deficit_locus` 1e-11). Fix each to exact
   `CyclotomicField`/integer `==`, or a justified noqa where it is genuinely a ranked statistic.

## Scripts (this audit)
`check_no_float.py` (rewritten guard), `classify_float.py` (bucketer), `genuine_decisions.py`
(genuine-set filter), `sym3_exact.py` / `floatcheck.py` (the perfect-square exact redo + float demo).
