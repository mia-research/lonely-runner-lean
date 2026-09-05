# PREREG — characterization of the β² excess in cubic `E3` (v1)

**Status:** design FROZEN before computing any decomposition. Follow-up to the fired cell
[RESULT_diffset_cubic_v1.md] (EXPLORATORY per that prereg). Date: 2026-07-27. Descriptive
decomposition — **no reject/accept verdict**; every sub-slice carries its own matched null.

---

## Object
Decompose the +75 excess in cubic class **β² (=class 2)** of E3(real): (a,b,c)=(1082,1057,1182) over
the 3321 unordered pairwise x-differences of the real 82. Questions: **concentrated or diffuse**; if
concentrated, **which keys / which bit-bands**.

## Fixed partitions (locked NOW, before data)
- 3 bit-bands: **L = bits [1,40]** (40 keys), **M = [41,80]** (32 keys), **H = [81,130]** (10 keys).
- 6 pair-buckets with locked sizes: LL=780, MM=496, HH=45, LM=1280, LH=400, MH=320 (Σ=3321 ✓).
- Per-key: each key's β²-count over its 81 pairs.

## Statistics (locked) + their nulls
Null = matched MT control (`constructed_keys_1to160_100k.csv`, bit-length-matched — so bands and
buckets transfer), 3000 resamples, empirical (integer counts). Classes are ~iid-uniform under the
null (control class means ≈1107, Var(a)≈727≈independent-multinomial, established in the E3 prereg).
1. **Per-bucket β²-count** vs null: report real fraction, null mean, z, empirical percentile.
   **Multiple-comparison control:** judge the largest deviation against the empirical null of
   **max|z| across the 6 buckets** — not per-bucket α (6 buckets ⇒ a nominal 0.05 hit is expected).
2. **Per-key dispersion** = variance of the 82 per-key β²-counts. Real vs null distribution of that
   variance. Over-dispersed (> null 97.5%) ⇒ concentration; within null ⇒ diffuse.
3. **Top-5 per-key β²** keys, each key's count vs Binomial(81,1/3) (mean 27, sd 4.24), and the
   empirical null of the **max per-key count** (MC control for "hottest key").

## Pre-committed interpretation
- **max-bucket |z| within its null AND per-key dispersion within its null** ⇒ the β² excess is
  **DIFFUSE**: a uniform ~+2.3% relative tilt (75/3321) across all pairs; no band or key carries it
  disproportionately. Characterization = "diffuse tilt, magnitude +75 (relative +2.3%), located in no
  sub-partition at this power."
- **A bucket exceeds the max-|z| null, OR dispersion exceeds its null, OR a key exceeds the
  max-per-key null** ⇒ **LOCALIZED**: name the band/keys, tagged EXPLORATORY (needs its own
  reproduction; a located cell here does not upgrade the aggregate grade).

## Guardrails (the "with rigor" part)
- Exact integer cubic class (`pow(z,(P−1)//3,P)`); integer counts; empirical (integer) nulls. No float
  threshold on data.
- Report ALL 6 buckets and the full per-key distribution — not only the extreme cells.
- This is characterization, not a verdict. The aggregate E3 reject stays weak (p≈0.03–0.04, 1 of ~7
  tests, un-replicated); no sub-result changes that. **No closure, no impossibility, no "the signal
  lives here" without its control firing.**

## Scope
Real 82 (bits {1–70,75–130}); MT control pool; secp P; cubic character; 3000 null resamples; these
3 bands / 6 buckets. No number generalizes past this scope.
