> **⚠ SUPERSEDED (2026-07-21) — the "axis deficit" analyzed below is largely a WRONG-NULL ARTIFACT**
> (see the retraction banner on `RESULT_harmonic_deficit_locus_v1.md` and `_axis_null_check_v1.py`).
> The χ₂-distinctness determination therefore compares an artifact and is moot as a statement about a
> "b=0 axis object." What survives independently is the DIFFUSE ~−0.1% aggregate deficit, which is not
> χ₂-localized — consistent with "broad, not χ₂," but the b=0-"axis" framing here is retracted. Retained
> for the record.

# RESULT — the b=0 axis deficit is distinct from the χ₂(y) 0.470 suppression

**Date 2026-07-21.** Executes `PREREG_y_channel_chi2_vs_axis_v1.md`; the v1 run failed its controls and
was rebuilt as v2 (fixes below). Artifacts: `y_channel_chi2_vs_axis_v2.py` / `.log` (v1 kept for the
record). Scope: model curves `E:y²=x³+7`, `a₀=1`, 7 primes 163–2089. **No ECDLP/extraction/secp claim.**

---

## 0. Why v2 (v1 control failure, honestly recorded)

v1 was **inconclusive — controls failed**: (a) its calibration chased the recorded `0.470`, which is a
**max-over-a** χ₂(y) saturation, while the axis and the deficit spectrum are at **a₀=1** — different
statistics, so it could not calibrate (my numbers 0.53–0.69, growing in `p`); (b) the χ₂ mode was
**confounded by the forced Sy structure** (`V(χ₂)≈0` exactly at p≡3 mod 4); (c) the prereg's "l² pinned"
forced-fact was wrong for the multiplicative-character basis (it holds for the (b,c) Fourier basis) and
the check had a Jensen bug. Per the prereg's own gate, v1 produced no verdict.

**v2 fixes:** calibration is the FORCED fact `Re V(χ₂)=0` at p≡3 mod 4 (an exact channel check, not the
`0.470`); the analysis is split by residue class to isolate the Sy confound; the l² check is dropped.

---

## 1. Controls now fire

- **C1 channel check `[VERIFIED, exact]`:** `Re V(χ₂)=0` to `<1e-6` at every p≡3 mod 4 prime (163,211,991);
  `Im V(χ₂)=0` at every p≡1. The forced Sy structure is reproduced exactly ⇒ the χ₂(y) readout
  `V(χ₂)=Σ_d χ₂(y_d)e_n(d)` is computed correctly.
- Random-target deficit spectrum is flat (v1 C2, unchanged).

---

## 2. Determination `[EMPIRICAL, 7 primes]` — DISTINCT

| p | p%4 | axis deficit (a₀=1) | D_V(χ₂) | χ₂ rank | note |
|---|---|---|---|---|---|
| 163 | 3 | −12.3% | −10.48 | 8 | χ₂ small = forced Sy |
| 211 | 3 | −9.6% | −10.72 | 20 | forced Sy |
| 991 | 3 | −10.2% | −22.27 | 119 | forced Sy |
| 349 | **1** | −11.0% | −5.78 | **176** | clean |
| 433 | **1** | −10.7% | −5.29 | **255** | clean |
| 577 | **1** | −12.8% | **+1.43** | **514** | clean |
| 2089 | **1** | −11.8% | **+11.93** | **1294** | clean |

- **Axis deficit robust:** negative at all 7 primes, both residue classes, −9.6 … −12.8%.
- **χ₂ is not the carrier:** in the clean p≡1 class, the χ₂-mode deficit **flips sign** and χ₂
  **ranks 176–1294** (of ~`p−2` characters) — never dominant. The strong χ₂ suppression at p≡3
  (ranks 8–119) is the **forced Sy** effect (C1), not the axis deficit. No single multiplicative
  character carries the axis deficit; top contributors are scattered.

**Conclusion.** The b=0 axis deficit and the χ₂(y) `0.470` are **distinct statistics on the same
y-channel**: the axis effect is a **broad, sub-Rayleigh, l¹-distributional** suppression of the pure-y
additive harmonics, *not localized to χ₂*; the `0.470` is a **χ₂-specific max-over-frequency**
saturation. The located locus is therefore not the `0.470` relocated — it is its own object.
(This resolves `RESULT_harmonic_deficit_locus_v1.md` §3.) Whether the two share a common cause is
unaddressed.

---

## 3. Grade & scope

`[EMPIRICAL, 7 primes, replicated, controls fired]`. Model primes 163–2089, `a₀=1`, this readout set.
The locus is `d`-free and publicly computable ("b=0"); it is a location of magnitude suppression, **not**
a `d`-readout. Nothing transfers to `2²⁵⁶`. No security claim.

---

## 4. Next probe (its own prereg)

Probe #2 is now worth registering: is the length-`p` deficit pattern `D_A(c)` along the b=0 axis
`d`-predictive (any hardcore predicate of `d`) against the strong automorphism null, tautology-guarded?
Expected **null** by the ECDLP-scramble prior; run to **bound**, not to hope. This is the only probe
that would bear on extraction.
