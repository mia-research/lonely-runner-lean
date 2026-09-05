# RESULT v2 — cofactor restoration, CORRECTED: at matched p AND index, confinement FULLY reproduces j0's lever. No residual. (v1's "residual" was a p-scale confound.)

**Date:** 2026-08-31
**Author:** ZCode (Claude). **Supersedes `RESULT_h5_cofactor_restoration_v1.md`**, whose
"confinement incomplete / j0-specific residual" conclusion was a **p-scale confound** and is
**retracted** here. Same pre-registration (`PREREG_h5_cofactor_restoration_plant_v1.md`; the
secondary comparability band p∈[523,823], §6, which v1 skipped — that omission is the whole error).
**Runs:** `h5_cofactor_restoration_run_v1.py` (large-p, v1) + `h5_restoration_smallband_v1.py`
(the matched-p band, this correction; `check_no_float`-clean). Data: `h5_restoration_results_v1.jsonl`,
`h5_restoration_smallband_v1.json`, `h5_followup_results_v1.jsonl` (j0).
**Grade:** `[VERIFIED — cofactor confinement is the FULL mechanism; forward-validated at matched p and
index]`, scoped to model curves.
**Bottom line:** the confinement differential `T1 = logmean quo(confined) − logmean quo(full)` is
**strongly p-dependent** (large at small p, small at large p). v1 compared j0 (small p) to induced
confinement measured at LARGE p and read the gap as a j0-specific residual. **At MATCHED p, induced
confinement on generic cyclic curves reproduces j0's lever fully — same levels and same slope — so
there is NO residual. M25's cofactor-artifact null is CONFIRMED and now forward-validated.**

---

## 1. The error in v1 (named precisely)

v1 compared two things at **different p-scales**:
- `β_j0 = 0.546` — j0's confinement slope, from j0 curves at **p∈[523,823]**.
- `β_induced = 0.206` — induced confinement slope, from generic cyclic curves at **p∈[10007,50021]**
  (chosen for the wide c-range).

It then read `0.206 < 0.546` as "confinement reproduces only ~38% of j0's slope → residual." **But T1 is
p-dependent** (§2), so the two slopes are not comparable. The pre-reg's own secondary band
(p∈[523,823], §6) — skipped in v1 — is the matched control that settles it.

## 2. T1 is strongly p-dependent (the fact v1 missed)

`T1(index k)` for generic cyclic curves, same statistic, two p-bands:

| index k | generic **large-p** (10⁴–5·10⁴) | generic **small-p** (523–823) |
|---|---|---|
| 2 | 0.008 | **0.236** |
| 4 | 0.036 | **0.565** |
| 6 | 0.087 | **0.803** |

Same mechanism, ~7–30× larger at small p. (Interpretation: at small p, `|V|^m` is comparable to the
subgroup size `q=#E/k`, so confinement bites harder; at large p, `|V|^m ≪ q`, so a subgroup restriction
barely changes the decomposition count. A saturation-regime dependence — real, and it invalidates any
cross-p comparison of T1.)

## 3. Matched p AND matched index — confinement fully accounts for j0

Comparing the SAME statistic at the SAME p-scale (523–823) and the SAME confinement index:

| index k | j0 (natural cofactor n₂=k) | generic cyclic (induced c=k) | j0 − generic |
|---|---|---|---|
| 2 | 0.197 | 0.236 | −0.039 |
| 4 | 0.647 | 0.565 | +0.082 |
| 6 | 0.718 | 0.803 | −0.085 |
| mean over common k | | | **−0.014 (≈0, mixed sign)** |

- **No systematic j0 excess** — the differences are ~0.01–0.08, mixed sign, mean ≈0.
- **Slope matches too:** the small-p generic slope over c∈{2,…,7} (T1 = 0.236/0.404/0.565/0.735/0.803/0.838)
  is **β_induced(small-p) ≈ 0.51**, statistically indistinguishable from **β_j0 = 0.546**.

So at j0's own scale, inducing subgroup confinement on a generic cyclic (j≠0) curve reproduces j0's
lever in **both level and slope**. The forward prediction is confirmed at matched p; **there is no
j=0-specific component.**

## 4. Verdict (corrected)

- The confinement mechanism is **causal and COMPLETE**: forward-induced on cyclic curves at matched p,
  it reproduces j0's lever fully (level + slope). Plants fired in both runs (confinement-verify;
  synthetic-slope β=1.000; c=1 null T1≈0).
- **v1's "residual / incomplete / suppression-catch" is RETRACTED** — an artifact of comparing across
  p-scales for a p-dependent statistic. There is no residual.
- **M25 / N22 H1 leg** stays `[null — cofactor/sampling artifact, model scale]`, now upgraded in
  support to **forward-validated at matched p and index** (not merely backward r=0.96). The original
  `RESULT_h5_cofactor_artifact_v1.md` conclusion stands.
- **v18's external-review flag on M25** is addressed constructively: the forward test at matched p is
  exactly the independent check the flag asked for, and it **confirms** the cofactor explanation is
  complete — the null is not a suppression artifact but a mechanism reproduced on demand.

## 5. Discipline note (both directions audited)

This episode ran the full loop in the correct direction: v1 surfaced a candidate positive (a residual)
rather than pre-deflating it; the matched control (matched-p band) was then run before banking it, and
it dissolved the candidate as a p-confound. The candidate was a false POSITIVE (an over-claimed
residual), killed by a control — the anti-inflation direction. Net: M25's null is stronger, not weaker,
and the correction is on the record.

**Scoped observation (this experiment only — NOT a corpus rule):** in this run the statistic `T1` was
strongly p-dependent between the two bands tested (≈7–30× larger at p∈[523,823] than at p∈[10007,50021]),
which is why v1's cross-p comparison was invalid and v2 matches p. Whether this p-dependence extends to
other statistics, other |V|, or other bands is untested here. If it's worth turning into a standing
methodological rule, that's the user's call — flagged as a candidate for review, not imposed.

## 6. Scope / provenance
Model curves only (p∈[523,823] matched band + [10007,50021] large band), m=3, |V|∈{4,5,6}, K=25.
secp256k1 is prime-order (no cofactor) — the mechanism is absent at the target regardless; no 256-bit /
ECDLP / keyspace claim. Exact-int signal path; floats only in logmean/OLS/permutation, `# noqa: float`
noted, `check_no_float.py` passes. Standalone artifact — NOT folded into a master (corpus concurrently
at v18); the M25 grade note (forward-validated) is a coordinated `compile-diff`-gated fold, not done here.
