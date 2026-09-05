# RESULT — β² excess characterization (v1)

**Grade:** `[MEASURED-EXACT — the β² excess is DIFFUSE; no band/bucket/key localizes it at this power;
scoped]`. Ran 2026-07-27 per frozen [PREREG_diffset_cubic_beta2_characterization_v1.md]. Matched MT
null, 3000 resamples. Integer-exact.

---

## Answer: the +75 β² excess is DIFFUSE, not localized
A roughly uniform ~+2.3% relative tilt toward class β² spread across all pairs — no band, pair-bucket,
or key carries it disproportionately.

### Per-bucket (β² fraction vs null 0.333)
| bucket | pairs | real frac | z | pctile |
|---|---|---|---|---|
| LL (1–40²) | 780 | 0.356 | +1.37 | 91.6 |
| MM (41–80²) | 496 | 0.377 | +2.07 | 98.1 |
| HH (81–130²) | 45 | 0.333 | −0.00 | 56.6 |
| LM | 1280 | 0.340 | +0.51 | 70.6 |
| LH | 400 | 0.367 | +1.47 | 93.9 |
| MH | 320 | 0.375 | +1.55 | 94.3 |

5 of 6 buckets mildly positive (consistent with a uniform tilt), MM highest. **MC-corrected: real
max|z| = 2.07 vs null-of-max|z| 95% = 2.60, p(max|z|) = 0.212 → no bucket localizes the excess.**

### Concentration (per-key)
- Per-key β² dispersion (variance of the 82 per-key counts) = **15.29**, at the **20th percentile** of
  the null (null mean 17.58) — i.e. *sub*-null, per-key counts are if anything slightly *more* uniform
  than random. Not over-dispersed ⇒ not concentrated.
- Hottest key = puzzle 115 (count 38, z=+2.6 vs Binomial(81,1/3)); but **null of the max-per-key = 41
  at 95%, p = 0.465** ⇒ the hottest key is unremarkable among 82. Top-5 (b115, b42, b61, b130, b18)
  match the E3 jackknife drivers but none is individually special.

## What the decomposition shows
The +75 β² excess does not localize in any tested partition: no band or bucket beyond the
MC-corrected max|z| null (p=0.21), no hot key (p=0.47), and per-key dispersion *below* the null (20th
pctile). It is distributed as a small ~uniform β² tilt across the 3321 pairs. This is consistent with
either a small uniform effect or an unresolved aggregate fluctuation — the decomposition does not
distinguish those. Finer partitioning would add multiple-comparison noise without adding resolution
at n=82.

## Power + scope
Rules out **localization** above max|z| ≈ 2.6 (per-bucket) or per-key dispersion ≈ 23.3, at n=82 with
these 3 bands / 6 buckets and 3000 nulls. A diffuse tilt below the localization threshold is not
resolvable here. Scope: real 82 (bits {1–70,75–130}), MT control, secp cubic character.

## Effect on the aggregate
None. The E3 aggregate stays a weak (p≈0.03–0.04), MC-non-significant, un-replicated anomaly whose
interpretation is open (see [RESULT_diffset_cubic_secondcontrol_v1.md]). Characterization sharpened it
(diffuse, unlocalized) — it did not upgrade or close it.

## Scope of this result, and what is untested
The "diffuse" finding is scoped to **E3's cubic-character marginal counts (a,b,c)** and **these 3
bands / 6 buckets / per-key** at n=82. It does **not** test other characters (quartic, sextic),
higher-order or joint (triangle) x-difference statistics, or other partitions — those are untested,
not shown structureless. So this locates no cell to chase *within this statistic*, and makes no claim
beyond it.
A separate direction that probes a *different* kind of structure is a **group-law** joint object
(`P_i ± P_j` via curve addition), which connects to the discrete log through curve arithmetic rather
than describing x-coordinates. Pre-register separately if pursued.
