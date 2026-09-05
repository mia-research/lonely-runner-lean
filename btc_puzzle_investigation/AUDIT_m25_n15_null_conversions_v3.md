# AUDIT — M25 & N15 null-conversions (v3): the external review ran the two remainders, and both close

**Date:** 2026-08-27
**Supersedes:** `AUDIT_m25_n15_null_conversions_v2.md` (this session). v1/v2 verdicts on the *tested* null
legs are unchanged; v3 records that the **external adversarial review the user triggered
(`/code-review ultra`) ran the two un-reviewed remainders v2 flagged, and both come back null** — plus my
independent re-check of its load-bearing new number.
**External report:** `~/ZCodeProject/external_review_M25_N15/REPORT_external_M25_N15_v1.md` (+ `scripts/`,
`results/`). **No grade is moved here.**

## What the external review closed — mapped to v2's owed remainders

| v2 owed remainder | external experiment | result | who verified |
|---|---|---|---|
| **M25 — prime-order extrapolation** ("vanishes at cofactor-1 secp" was *argued, not tested*) | E-PO: 26 pairs, prime-order j=0 twist vs nearest-#E prime-order non-CM, authors' instrument, original sampler, |V|=4..8 | **T1 null at every |V|** | **✅ independently recomputed by me** |
| **M25 — |V|=6-vs-8 sampler seam** (raw T1 grew log-shaped to |V|=8; corrected null only to |V|=6) | E-SAT: leaky design extended to |V|=14, all 24 primes | increments decay +0.23→+0.04, **plateau 1.21 vs ceiling mean log n₂ = 1.44**; 24/24 within log n₂+0.35 | report + on-disk `SAT_ENUM`/`SAT_GB` (not recomputed) |
| **N15 — order-≥3 / full-joint-C** (D1's named, unestimated channel = the joint question) | E-N15: 95-predictor family (84 triples + more moduli + popcount + GLV-eigenvalue classes), b=128 N=10⁶, b=256 N=3·10⁵ | family p = 0.74 / 0.98 / 0.07 / 0.11, **all at bias floor** | report + on-disk `exp2_n15_extension.json` (not recomputed) |
| **N15 — distributed (not max) leakage** (my audit named max-stat blindness) | E-N15b: sum statistic ΣÎ(C_j;T) | **z = −0.22** (null mean) | report + on-disk `exp2b_sumstat.json` (not recomputed) |

## My independent verification (raw artifacts, not the report's narrative)

Per project discipline (*a document cannot witness its own audit*), I checked the decisive claim against
the raw data, not the summary:
- **Runs are real:** `results/exp1_run.log` shows 26 PO + 20 COF primes and SAT primes with genuine
  wall-clock (|V|=14 enumeration 173s→2400s+/prime) — not a fabricated summary.
- **Exact arithmetic on the discrete decisions:** curve/subgroup orders via Sage `EllipticCurve.order()` /
  `gens()[0].order()` (exact ℤ); float only in the logmean-of-integer-counts statistic (sanctioned (stat)).
- **PO/COF T1 recomputed by me from the raw integer `quos`** (`exp1_run_results.jsonl`, 1204 rows):
  PO = **−0.0081 / +0.0011 / −0.0063 / +0.0084 / −0.0050** (|V|=4..8, 26 primes);
  COF = **−0.0152 / +0.0284 / −0.0049 / −0.0270** (20 primes). Matches the report to 3 decimals; **null.**
- **Not independently recomputed** (taken from the report + its on-disk artifacts): the |V|=14 saturation
  law, the N15 95-predictor family p's, the sum-statistic z, and the plant firings (ε=1→log₂3; +0.5→
  p=0.0000; hard-null FP 1/20). Artifacts for each are on disk under `results/`.

## Verdict

**Both nulls SOUND; the suppression check comes back CLEAN — no buried effect in either object.** The
audit's *targeting* was correct (it named exactly the two channels the external eye then tested), and the
tests resolved them to null, not to a hidden positive. Specifically:
- **M25/H1** — the null now rests on a **tested** prime-order extrapolation (not an argument) and a
  **saturation law** (not an un-bounded "no saturation through |V|=8" alarm). The j1728 arm (an
  un-dispositioned p=0.003 positive in the frozen data) is the same cofactor artifact, also closed.
- **N15** — D1 adjudicated **legitimate by arithmetic** (frozen joint-C bias ≈10.9 bits ≫ H(T)=3.65;
  Miller–Madow already the frozen correction; the ε=1 plant *failed* on it = the prereg's own VOID
  tripwire). The order-≥3 / distributed channel is run and null for this cost class.

## Owed / still genuinely open (not closures)

1. **F5 (real, wording):** §6 of `RESULT_h5_cofactor_artifact_v1.md` states the secp consequence in
   result-voice while its pre-registered scope was p∈[523,823], |V|≤6. F1's prime-order test now makes the
   sentence true, but at grading time it was an extrapolation presented as tested. **Owed:** annotate
   §6 to cite the external prime-order test (E-PO) as the artifact that discharges it. *(This is exactly
   the summary-overstates-artifact pattern the whole audit was about — now with a fix address.)*
2. **The directions the artifacts themselves name** (open, not owed to this audit): the **M26 β-orbit /
   GLV √#Aut constant-factor** channel is the one CM-specific structure that *does* reach secp (already
   externally reproduced, ADDENDUM_4 A3; bounded, not a keyspace reduction); and for N15, **other readout
   classes / larger alphabets** beyond the tested cost class.

**Net.** Supervisor item 1 is discharged: M25/N15 got the external eye, the two remainders were tested,
and the nulls held under adversarial retest — leaving both *stronger* (tested extrapolation + saturation
law for M25; closed family-adequacy for N15), with one wording fix (F5) owed. Trace the object, not the tag.
