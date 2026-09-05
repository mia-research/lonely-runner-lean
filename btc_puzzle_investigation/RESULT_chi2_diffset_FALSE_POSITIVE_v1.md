# RESULT — the χ₂ difference-set "finding" was a FALSE POSITIVE (dissolved on valid reproduction)

**Date:** 2026-08-02. **Grade: `[DISSOLVED-ON-TEST — false positive, killed by valid reproduction]`.**
Supersedes `RESULT_c2_chi2_leak_lead_REPRODUCED_v1.md` (WITHDRAWN). **Scripts:**
`c2_grouplaw_diffset_curve_v1.py` (the valid, independent-arm test), executes frozen
`PREREG_chi2_diffset_characterization_v1.md` (SHA `ec136ef8`). **Settled by**
`chi2_diffset_definitive_v1.py` → `chi2_definitive.log` (N=80 independent arms).

## 0. SETTLED (the definitive run, N=80 — not an argument)
80 genuinely-independent band-random arms vs 80 fresh-uniform sets, secp M=400:
**χ₂/E2 arm mean pctile = 0.519, P(arm>fresh) = 0.478 → NULL** (E3 0.503, E6 0.444, both NULL). E2 is
~0.6σ from 0.5; a real 0.60 effect would have registered at ~3σ. **The χ₂ lean was a false positive.**

## 1. What happened
A χ₂ (QR-class) elevation in band-confined group-law difference-sets read as reproduced (mean arm
pctile 0.600 → 0.601). The characterization drill (control-curve, secp vs P-256, via one script with
genuinely seed-dependent arms) instead **dissolved it**:

| curve | independent arm-realizations (χ₂ mean pctile) | mean |
|---|---|---|
| **secp256k1** | 0.600 (stageA) · **0.384** · **0.523** | **0.502 (null)** |
| P-256 | 0.451 · 0.480 | 0.466 |

All runs passed the instrument gate (fresh-vs-pool PASS, E₂ plant FIRES, arithmetic `[n]G=O` verified).
The 0.600 was a single ~1.9σ-high arm draw; it does not survive varying the arms.

## 2. Why the original "reproduction" was invalid (the mechanism)
`c2_grouplaw_diffset_stageA_v1.py` **line 185**: `arng = random.Random(sd ^ (k*0x9E3779B1))`. The arm
draws depend only on the fixed `OOS_SEEDS` list and `k` — **not on the base seed**. So both "reproduction"
runs (seeds 20260802, 31337) used the **identical arms**; only the null pool differed. The near-identical
sorted p-value lists across the two runs were the tell — the SAME arm E₂ values ranked against two
similar pools. It tested pool-robustness, never arm-reproducibility.

## 3. The lesson (methodological, distinct from the suppression bias)
**A reproduction must vary the OBJECT UNDER TEST — here the band-random arms — not just the null pool.**
An invalid reproduction is not a reproduction. This one inflated a chance-high draw into an apparent
"finding"; the same flaw could equally hide a real effect. The valid test (independent arms, and a
second curve) is what settled it.

## 4. Framing (per `feedback_suppression_bias_asymmetric_2026_08_02`)
This is the directive **working**, not failing: the positive was **surfaced** (not suppressed),
**chased** hard, and **killed by a test** (independent-arm reproduction + control curve) — the healthy
dynamic. Killing a false positive *in a test* is not the suppression reflex; deflating a positive *in
prose before testing* is. The distinction held.

## 5. What this does NOT mean (counter-prior)
One candidate died on a valid test. This is **not** evidence the band-difference-set avenue, or the
curve, is clean — a dead candidate is a failed search, not an absence. Other objects / characters /
scales remain open; the short-scalar sums & difference-sets bounds established earlier (C-NEG recal,
R-CONTIG, interval-vs-random, R3, C2 tail-screen) stand as before, at their stated powers.

## 6. Files
`c2_grouplaw_diffset_curve_v1.py` + logs `c2_curve_{secp,p256}_s{1,2}.log`; withdrawn
`RESULT_c2_chi2_leak_lead_REPRODUCED_v1.md`; frozen prereg `PREREG_chi2_diffset_characterization_v1.md`.
