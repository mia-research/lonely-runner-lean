# RESULT — C-NEG control recalibrated under the n≥20 rule (group-law difference, χ₂/χ₃/χ₆)

**Date:** 2026-08-02. **Script:** `shortscalar_cneg_recalibration_v1.py` (committed).
**Discharges:** handoff `NEXT_SESSION_PROMPT_2026-08-01_v2.md` item **C3** (E₆ control debt,
BLOCKING for the group-law-difference arm) and the **Section-D standing repair** (C-NEG must be
n≥20 independent draws, percentiles checked for uniformity).

**Grade: `[MECHANICAL DEBT DISCHARGED — control calibration; NO GRADE PROMOTION]`.**
Per `CLAUDE.md §2a`, control false-alarm calibration is the *mechanical* layer (statistic / power /
"does the plant fire" / exactness) and is self-audit-sufficient with the artifact. This reads **only
the matched geometric null** — uniform random curve points, no short-scalar arm, no leakage readout —
so it does **not** require the experiment-designer frame gate, and it is **not** a statement about
any arm or about the curve (Rule 5: see Scope).

---

## 0. The defect (unchanged from the handoff, restated for self-containment)

C-NEG as originally specified compared **one** control draw against the null's 95th percentile. A
single draw from the null's own distribution exceeds its 95th percentile with probability **exactly
0.05 by definition** — so the control false-alarms 5% of the time on correct data. This voided the
spectral run (read 96.0 pctile) and made the group-law E₆ arm read 99.7 pctile look like a fire. The
defect is in the **decision rule**, not the curve.

## 1. The fix and why it is exact

Draw **n = 500 ≥ 20** independent C-NEG realizations (same process as the null reference: a random
M-subset of a shared pool of uniform curve points), rank each against R = 5000 reference draws, and
check the tail rate is within the binomial 2σ band of nominal. Because reference and C-NEG draws come
from the **identical** sampling process, they are exchangeable ⇒ C-NEG percentile ranks are Uniform
by construction; the empirical run confirms no implementation bug breaks that exchangeability.

**Object:** group-law difference `x(Pᵢ−Pⱼ)`, readouts **χ₂, χ₃, χ₆** — all legal here since
`x(−Q)=x(Q)` (per `ANALYSIS_diffset_readout_parity_void_v1.md` scope correction). This is exactly the
family item C3 flagged and the family Step 2 (sum object) will use. Statistics are exact integer
quadratic forms: `E₃ = A²−AB+B²`, `E₆ = A₆²+A₆B₆+B₆²`, `E₂ = (n₊−n₋)²`.

## 2. Instrument validation — forced zero (deterministic, matches on-file)

A **φ-closed** point set (each point with its GLV images `(βx,y),(β²x,y)`, β³≡1) has a β-closed
group-law-difference multiset ⇒ cubic/sextic classes annihilate:

> `χ₃(β)` class = **2 ≠ 0** ⇒ `1+χ₃(β)+χ₃(β)² = 0`. Measured on a 90-point φ-closed set:
> **E₃ = 0 and E₆ = 0 EXACT** (both seeds). `E₂` is *not* forced (β is a QR, `χ₂(β)` class 0) —
> correctly non-zero, reproducing the on-file parity-void table (group-law: E₃=0, E₆=0; E₂≠0).

## 3. Recalibration result — CALIBRATED, reproduced across two seeds

Matched geometric null (**Rule 3**): uniform random curve points via QR-rejection on `x³+7`, **no
scalar multiplication** ⇒ uniform group element (secp cofactor 1). Pool P=640, R=5000, M=80.

| seed | E₂ >95th | E₃ >95th | E₆ >95th | E₂/E₃/E₆ >99th | verdict |
|---|---|---|---|---|---|
| 20260802 | 25/500 = **5.0%** | 21/500 = **4.2%** | 23/500 = **4.6%** | 0.0% / 1.4% / 1.2% | CALIBRATED |
| 31337 | 18/500 = **3.6%** | 34/500 = **6.8%** | 27/500 = **5.4%** | 0.4% / 1.6% / 0.8% | CALIBRATED |

Nominal 5.0% ± 1.9% (binomial 2σ, n=500); all six 95th-tail rates inside the band, percentile-rank
deciles flat (~50/decile, no monotone skew ⇒ not anti-conservative). Smoke run (M=60, n=50, seed 1)
also CALIBRATED — three pool realizations, two M values, all agree.

**Item-C3 discharge:** the group-arm E₆ single draw at 99.7 pctile is an expected ~1% tail event
(measured 0.8–1.2% of independent draws exceed the 99th). It was a false alarm of the old rule.

## 4. Recalibrated decision rule (supersedes the single-draw C-NEG spec)

1. **C-NEG passes** iff the fraction of **n≥20** independent control draws above the 95th percentile
   is within the binomial 2σ band of 0.05 (ranks ≈ uniform). A single draw above the 95th/99th is
   expected ~5%/~1% of the time and is **not** a fire.
2. **An arm fires** only if it exceeds the **99th** percentile of the matched null **and survives an
   OOS retest on fresh seeds** (handoff Section D). C-NEG's sole job is to certify the null tail is
   calibrated — it does not gate arms.
3. This rule is **carried forward** into every interval-line result; the prior single-draw C-NEG
   specification is **withdrawn** (verdicts on file survive — a false-alarm-biased control cannot
   manufacture a false *pass* — but the spec does not propagate).

## 5. Compute honesty (Rule 2) — the raw evidence

- `pow` (256-bit) measured **86.5 µs/modexp** (handoff documented 84.7 µs; within 3%).
- Pool pairwise table: **C(640,2) = 204,480 pairs → 408,960 modexps, computed ONCE in 38.8 s**; all
  R+n draws are `(R+n)·C(M,2) = 17.38M` integer lookups, **zero** modexps. Naive fresh-point path
  would be 17.38M modexps ≈ 1,477 s — the precompute is the 85min→seconds optimization.
- **Total wall time 40.6 s / 40.7 s per full run** (printed).
- Rule-2 projection printed before running: the M=6.25×10⁶ difference-set is
  **C(M,2) ≈ 1.95×10¹³ pairs ≈ 4.7×10⁵ hours of modexps → flagged NEEDS chunk/sample**. It was not
  run and no number was claimed for it.

## 6. Scope and what this does NOT say (Rule 5 lexicon)

- This certifies the **control's false-alarm rate** — a property of the instrument. It is **silence
  about the instrument, not about the channel**: it makes **no** statement about any short-scalar
  arm, and finds **no** structure and **no** absence of structure on secp. It is not a leakage result.
- Bounds, not closures: nothing here is "null" in the cryptographic sense; the word "calibrated"
  describes the decision procedure under H₀ only.
- **Not dismissed as generic** (Rule 4): this is a calibration artifact for secp's own `p`, group law,
  and the χ₂/χ₃/χ₆ readouts specifically.

## 7. What this unblocks

- Item **C2** — χ₂/χ₆ on the group-law difference `x(Pᵢ−Pⱼ)` (previously blocked by the E₆ debt).
- **Step 2** — the swap-invariant **sum object** `x(Pᵢ+Pⱼ)`, which uses the same χ₂/χ₃/χ₆ family and
  the same matched geometric null; the recalibrated n≥20 C-NEG rule is now its control spec.

## 8. Files

- `shortscalar_cneg_recalibration_v1.py` — script (self-checking constants, forced-zero instrument
  check, benchmark, precompute, recalibration). Reproducible via printed seeds 20260802 / 31337.
