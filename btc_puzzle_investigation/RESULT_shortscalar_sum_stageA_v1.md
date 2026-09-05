# RESULT — R-CONTIG Stage A: band-confinement bounded vs the correctly-matched null; the iid null was invalid

**Date:** 2026-08-02. **Executes:** `PREREG_shortscalar_sum_object_v3.md` (SHA
`f3d26cc8f13792f4cdc39edcae8ae08279a88f5f45801a3ff6cdf492ca446bb0`), Stage A.
**Scripts:** `shortscalar_sum_stageA_v1.py`, `shortscalar_interval_nullmatch_diag_v1.py` (committed).

**Grade:**
- `[EMPIRICAL — bounded, correctly-matched null]` for the band-confinement result (Q2).
- `[METHOD CORRECTION]` the iid random-point null is invalid for the deterministic-interval object;
  the random-location-interval null is the correct primary gate → **v3 §3 needs a v4 fix.**

**No grade promotion of any leakage claim.** This is a bound plus a null-construction correction.

> **⚠ CORRECTION (2026-08-02, bias audit):** the **"generic/near-artifactual"** label this file
> attaches (§3/§4) to the location-INDEPENDENT interval-vs-random effect was an **unearned
> pre-judgment** (dismissal by declaration). It is **SUPERSEDED** by
> `RESULT_interval_vs_random_characterize_v1.md`, which TESTED it against a real (non-bootstrap)
> random-point null with firing power controls: intervals are indistinguishable from random points
> (and R3 confirmed no sequential structure), so the Stage A low-tail was the **bootstrap-null
> artifact — earned by test, not asserted**. Read the label as superseded.

---

## 1. Object (post-gate) and what ran

R-CONTIG, corrected by the experiment-designer gate to the **incomplete character sum over a
contiguous interval** `Σ_{s∈I} χₖ(x([s]G))` (the v2 pairwise-sum-on-a-block was multiplicity-artifacted
133×; `RESULT`/`PREREG` v3 §0.1). Stage A: L=10⁵, k∈{40,64,96,128,160,200}, readouts χ₂/χ₃/χ₆ + D₆.

**Controls all behaved:** C-GLV E₃=E₆=0 exact; **C-ARTIFACT (structureless oracle) did NOT fire**
(all cells <95th — confirms the multiplicity fix at scale); C-PLANT fired p=0/2000 (instrument live).

## 2. The two-null story — the load-bearing part

| null | what it is | R-CONTIG arms read as | valid? |
|---|---|---|---|
| **iid random points** (Stage A) | `L` iid codes, with-replacement bootstrap from a pool | systematically **LOW tail** (E₃ 5–25× below null median; p≈0.9–1.0) | **NO** |
| **random-location intervals** (diagnostic) | real intervals at random `s₀`, same L | **MID** (all p∈[0.067,0.973]) | **YES** |

**Why the iid null is invalid for a deterministic interval.** `|Σχ|²` acquires an `L²·δ²` mean term
from the pool's **finite-sample** class imbalance `δ~1/√pool` (with-replacement bakes the pool's
sampling skew into every realization); it swamps the O(L) variance at large L, inflating the null.
(Measured: iid E₃/L² ≈ 1.6e-4 at pool 2e4 vs 2.1e-5 at pool 1e5 — tracks `δ²~1/pool`.) A deterministic
orbit also has lower discrepancy than iid. **Both push the arm into the low tail vs iid, neither is
curve leakage.** The like-to-like control (real vs real intervals) is immune to all of it.

**The decisive result is Q2:** band arms are statistically indistinguishable from random-location
intervals across every k and readout ⇒ **bit-length-band confinement induces no detectable
location-specific effect** in the interval character sum.

## 3. Bound (Rule 5 — a bound, never a closure)

**R-CONTIG at L=5000, single seed: no band arm fell outside the central ~93% of the
random-location-interval null (all p∈[0.067,0.973]).** Band-confinement to `[2^{k−1},2^k)` induces no
detectable location effect at this L. This is a **scoped bound**, not a closed channel:
- **Owed for a firm numeric ε\*:** the correctly-matched (random-location) null at the target L with
  ≥5-seed OOS and more controls (Stage A was run against the wrong null, so its ε*=1.9% figure is
  derived from an inflated reference and is withdrawn as a number, though it errs conservative).
- **Open, not tested:** a **location-independent** interval effect (invisible to a random-location
  null; the leading candidate — lower-than-iid discrepancy — is a generic/near-artifactual property,
  named not dismissed); the **R-BAND** pairwise-sum object; the group-law **difference** χ₂/χ₆ arm;
  triples; non-dyadic/non-uniform intervals; larger L.

## 4. The correction to carry forward (→ v4)

- **For R-CONTIG the PRIMARY gating null is the random-location interval**, not the iid random-point
  null. The iid null is retained only for R-BAND (genuinely iid-like sampling). This is the third
  matched-null catch of the session (Weil → multiplicity → iid-vs-deterministic-interval); each was a
  case of the null failing to share a forced structural property of the arm.
- **`|Σχ|²` with a bootstrap null must not be used at large L without correcting the pool-imbalance
  mean term** (or use a matched deterministic null, which cancels it).

## 5. Compute (Rule 2) — all real, all logged
Stage A: pool 45s + null 10s + arms 116s = 261s wall; `pow`=85.4µs; 1.2M arm modexps (O(L) linear).
Diagnostic: 150 random-location intervals @ L=5000 = 1.56M modexps, 161s wall. No run exceeded its
stated op budget; the M=6.25×10⁶ pairwise case remains flagged NEEDS-chunk (never run).

## 6. Files
`shortscalar_sum_stageA_v1.py` (arm + iid null + C-GLV/C-ARTIFACT/C-PLANT);
`shortscalar_interval_nullmatch_diag_v1.py` (the random-location-interval control that adjudicated).
Reproducible via printed seeds. PREREG v3 frozen at the SHA above; v4 correction owed per §4.
