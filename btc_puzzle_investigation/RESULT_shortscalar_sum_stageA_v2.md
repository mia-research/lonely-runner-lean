# RESULT — R-CONTIG firm bound vs the correctly-matched null (v4 amendment executed)

**Date:** 2026-08-02. **Executes:** `PREREG_shortscalar_sum_object_v4_amendment.md`
(SHA `731d3a6f20928ffa9f8b904edff99e162741a959bf936f9a9feb182d132d2ae0`), which amends v3's R-CONTIG
null after `RESULT_shortscalar_sum_stageA_v1.md` showed the iid null invalid. **Script:**
`shortscalar_sum_stageA_v2.py`. **Supersedes** the v1 RESULT's provisional numbers with a firm bound.

**Grade: `[EMPIRICAL — bounded; correctly-matched null; 5-seed OOS; NO closure]`.**

> **⚠ CORRECTION (2026-08-02, bias audit):** the **"generic/near-artifactual"** phrasing (§4) for the
> location-INDEPENDENT interval effect was an unearned pre-judgment; **SUPERSEDED** by
> `RESULT_interval_vs_random_characterize_v1.md` (tested, power-controlled: intervals = real random ⇒
> Stage A low-tail = bootstrap artifact, earned not asserted).

---

## 1. What ran
R-CONTIG = incomplete character sum `Σ_{s∈I} χₖ(x([s]G))` over `L=5000` consecutive points, readouts
χ₂/χ₃/χ₆ + D₆, `k∈{40,64,96,128,160,200}`. **Primary gating null = 300 random-location intervals**
(like-to-like; shares the arm's forced equidistribution and true class distribution, differs only in
`s₀`'s location → isolates the bit-length/location leakage question). Two-sided 99th screen,
same-tail 5-seed OOS. Seed 20260802.

## 2. Controls (all behaved)
- **C-GLV** φ-closed → E₃=E₆=0 exact (instrument).
- **C-NEG** 30 fresh random-location intervals: HI-tail 11/120, LO-tail 10/120 (nominal 5% each) —
  calibrated; a first draw read LO 13/120 (noise, gone on the clean draw); mild lower-tail heaviness
  is integer-discreteness in the compressed lower tail, non-load-bearing (arms are mid, not tail).
- **C-PLANT** injecting a coherent cubic-class-0 excess fires between ~2.5% and ~10% excess,
  bracketing the analytical ε*.

## 3. The bound (Rule 5 — a bound, never a closure)
> **No band cell screened the same tail on 5/5 seeds.** Every band arm is statistically
> indistinguishable from a random-location interval across all k × 4 readouts.
>
> **R-CONTIG at L=5000 excludes a coherent single-cubic-class excess ≥ ε\* = 6.70%** (excess relative
> to the expected class size `L/3`; from V₉₉(E₃)=28063, `ε*=2√V₉₉/L`, C-PLANT-confirmed). **BLIND
> below ε\*.**

**Bit-length-band confinement `[2^{k−1},2^k)` induces no detectable location-specific character
structure in the interval character sum, at this L.** ε\* scales `~1/√L`, so a deeper (logged
background) run at L≈2×10⁵ would tighten it toward ~1%; the null there costs ~300·2L modexps (~1 h).

## 4. Scope — what is NOT bounded (open, not closed)
- **Location-INDEPENDENT** interval effects common to all `s₀` are invisible to a random-location
  null (both sides share them); the leading candidate — lower-than-iid discrepancy of a deterministic
  orbit — is a generic/near-artifactual property (named, not a secp leakage claim), but a genuine
  location-independent secp effect would need a different instrument.
- **R-BAND** pairwise-sum object; the **group-law difference** χ₂/χ₆ arm (item C2); triples;
  non-dyadic/non-uniform intervals; readouts beyond χ₂/χ₃/χ₆/D₆; larger L.

## 5. Compute (Rule 2) — all real, all logged
366 real intervals × 2L modexp = 3.66M modexp; `pow`=72.6µs; null 287s, arms 29s, total 352s wall.
The null (real intervals) is the cost driver, not a resample — stated before running. No hallucinated
numbers; the M=6.25×10⁶ pairwise case remains flagged NEEDS-chunk (never run).

## 6. Session methodology note (why this bound is trustworthy)
This channel took **three matched-null corrections** to measure honestly: a Weil pre-dismissal
(self-audit), a 133× sum-multiplicity artifact (experiment-designer gate), and an iid-vs-deterministic
null inflation (`L²δ²` pool imbalance + equidistribution; caught by the like-to-like control). The
firm bound rests on the **like-to-like interval null**, which is immune to all three because both arm
and null are real intervals. The lesson carried forward: for a deterministic-orbit arm, the matched
null must itself be a deterministic orbit.

## 7. Files
`shortscalar_sum_stageA_v2.py` (firm-bound run); `PREREG_...v4_amendment.md` (frozen spec);
predecessors `..._stageA_v1.py`, `..._nullmatch_diag_v1.py`; `RESULT_...stageA_v1.md` (the journey).
