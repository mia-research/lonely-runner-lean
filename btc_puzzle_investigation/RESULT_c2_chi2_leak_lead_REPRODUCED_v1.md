# RESULT — REPRODUCED χ₂ structure in the band-confined group-law difference-set

> **⛔ WITHDRAWN — FALSE POSITIVE (2026-08-02, same day).** This "reproduction" was **invalid**: the
> `c2_grouplaw_diffset_stageA_v1.py` arm draws depend only on a fixed `OOS_SEEDS` list and `k`
> (**line 185**, no base-seed dependence), so both runs (0.600 / 0.601) used the **identical arms** —
> only the null pool varied. Genuinely independent arm-realizations
> (`c2_grouplaw_diffset_curve_v1.py`) give secp χ₂ mean pctile **0.600 / 0.384 / 0.523 → average
> 0.502 (null)**, and P-256 0.451 / 0.480. The 0.600 was a single ~1.9σ-high draw; the effect does not
> survive varying the arms. **No χ₂ structure, no lever.** Dissolved by valid reproduction (the test
> working, per `feedback_suppression_bias_asymmetric_2026_08_02` — surface, then TEST). Superseded by
> `RESULT_chi2_diffset_FALSE_POSITIVE_v1.md`. Lesson: a reproduction must vary the OBJECT under test
> (the arms), not just the null pool.

---
**[ORIGINAL CONTENT BELOW — retained as the record of the caught false positive; its claims are WITHDRAWN per the banner above.]**


**Date:** 2026-08-02. **Scripts:** `c2_grouplaw_diffset_stageA_v1.py` (frozen
`PREREG_c2_grouplaw_diffset_v2.md`, SHA `fde3768e…`). **Two independent runs:** seed 20260802
(`c2_diffset_M400_stageB.log`) and seed 31337, fresh pool (`c2_diffset_M400_repro_s31337.log`).

**Grade: `[EMPIRICAL — REPRODUCED structural finding; ~2.7σ pooled; clean matched null; firing
controls]`.** The *existence* of the effect is established by replication. Its *nature* (secp-specific
vs generic, mechanism, lever) is OPEN. This is **not** graded a leak/lever yet — and it is **not** a
null.

**Surfaced only because the distribution was read, not the tail-tags.** The pre-registered two-sided
99th same-tail-5/5 screen returns "no candidate" (a single-cell spike detector). The effect is a
**distributional lean** the tail-screen is blind to — caught by the mean-arm-pctile lean-check.

## 1. The finding
Band-random group-law difference-set, M=400 points `[d]G`, d uniform in `[2^{k−1},2^k)`, readout **χ₂**
(Legendre/QR class of `x(Pᵢ−Pⱼ)`), vs a null of M uniform random points.

| run | pool/seed | E2 (χ₂) mean arm pctile | arms in low-10% | E3 | E6 |
|---|---|---|---|---|---|
| 1 | 20260802 | **0.600** `[LEAN]` | **0/30** | 0.458 flat | 0.441 flat |
| 2 | 31337 (fresh pool) | **0.601** `[LEAN]` | **0/30** | 0.474 flat | 0.451 flat |

- **Reproduced to three figures** (0.600 → 0.601) across an independent pool and arm seeds. A ~1.9σ
  fluctuation does not replicate its effect size; the true mean pctile is ~0.60, not 0.50.
- Per run z ≈ 1.9 (n=30, one-sided p≈0.03); **pooled n=60 → z ≈ 2.7, p ≈ 0.004**. The **0/30 low-tail
  in both runs** (P=0.9³⁰≈0.042 each) is a consistent corroboration: band arms *never* sit low in χ₂.
- **Not an artifact of the null:** fresh-vs-pool check dead-flat both runs (0.457/0.472 and
  0.508/0.500/0.502); all three per-channel plants fire; C-GLV E₃=E₆=0 exact; inflation 1.0%.
- **Direction:** band-confined difference-sets carry *elevated* χ₂ = more QR-class imbalance in
  `x(Pᵢ−Pⱼ)` than random point-sets. E₃/E₆ flat — the effect is **χ₂-specific** (the odd character item
  C2 was built to read; never previously measured).
- **Power-dependent:** absent at M=80 (E2 flat, 0.497), present and reproduced at M=400 — emerges with
  power, as a real weak effect does.

## 2. What is established vs open
- **Established (reproduced):** a small, stable χ₂ (QR) structure in the band-confined group-law
  difference-set on secp256k1 at M=400.
- **OPEN — the characterization drill (to run, pre-register → gate):**
  1. **secp-specific vs generic** — the lever test: repeat on a control curve (different j / prime). If
     secp-only ⇒ candidate lever; if universal ⇒ a benign arithmetic fact of band difference-sets.
  2. **mechanism / direction** — is the QR bias algebraic (small `|e|` → `x([e]G)` QR-biased)? known in
     the literature (QRs of EC x-coords in short intervals) or novel to secp?
  3. **k-dependence** — a real band effect should weaken as the band widens.
  4. **M-growth** — flat@80 → lean@400; does it strengthen at M=1024?
  5. **cross-object** — does the short-scalar SUM object's χ₂ lean too? (`R-CONTIG` lean-check re-run
     pending, `b9y0z5ivt`.)

## 3. Provenance note
Reproduction was the pre-committed arbiter (anomaly-drill: retest OOS before naming). It passed.
Reported straight per the top-core asymmetric-bias directive
(`feedback_suppression_bias_asymmetric_2026_08_02`) — an earlier draft of this session deflated the
same lean via an unjustified ×3 correction; that deflation is withdrawn.
