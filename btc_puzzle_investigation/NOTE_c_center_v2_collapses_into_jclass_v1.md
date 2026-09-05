# NOTE — C-center v2, drafted honestly, collapses into `PREREG_jclass_120deg_discriminator_v2.md`

**Date:** 2026-08-21. **Status:** decision note (no C-center v2 produced; see recommendation).
**Trigger:** while importing the reference-arm firing controls the C-center second-read said were
missing (C-COEFF/C-FORCED/C-FIRE4 from `PREREG_jclass_120deg_discriminator_v2.md`), it became clear the
C-center verdict IS jclass_v2's already-frozen object. Three object-level reasons, each decidable.

## 1. Verdict duplication (C-center audit item 1, now sharpened)
`PREREG_jclass_120deg_discriminator_v2.md` §4 pre-registers, verbatim, the CM-type g₃ contrast C-center's
`I₃=[g₃≥1]` measures:

| arm | jclass_v2 §4 prediction |
|---|---|
| J0 (μ₆) | g₃ = 2 at every surviving cell |
| J1728 (μ₄) | g₃ = 0 |
| JGEN (μ₂) | g₃ = 0 |

C-center's `Δ₃ = Q₃(J0) − Q₃(REF)` reads out exactly this table (`Q₃(J0)=1` iff g₃≥1 on J0;
`Q₃(REF)=0` iff g₃=0 on the references). Same arms, same statistic family, same frozen contrast.

## 2. The "geometric center / π₀" framing is unreachable by this statistic (audit item 1, object-vs-proxy)
C-center §1 names the object "the finite center and component group π₀ of the **geometric** monodromy."
jclass_v2 §0.1 **proves** no eigenvalue-level statistic distinguishes the decomposition `H¹≅W⊕W⊗ξ`
(the geometric center) from its semisimplification (traces see only the latter); the operator-`T` route
was retired as circular, its existence equivalent to `g₃≥1` — the census statistic itself. `I₃` is an
eigenvalue-level statistic ⇒ it measures the **arithmetic ζ₃-signature and its CM-type specificity**,
NOT the geometric center. The C-center object label was an over-reach; the reachable object is jclass_v2's.

## 3. The statistical apparatus is mis-framed — the contrast is DETERMINISTIC, not statistical
C-center built a two-proportion `Δ₃` with a permutation null, a measured accidental-rate `q₀`, and a
power model. But:
- `Q₃(J0) ≡ 1` is a **theorem** — `RESULT_120deg_resultant_certificate_v1.md` PART 1 gives `g≥2` as an
  a-independent universal identity in `ℤ[e₁,p,ω]` (verified: line 35/43). So J0 is a deterministic arm.
- `Q₃(REF) = 0` is **exactly certified** — jclass_v2 §3 certification direction (gate D3): a computed
  `g₃=0` certifies `g_true=0` exactly (the reference prediction is on the exactly-certified side).
So both arms are exact per-cell certified computations. There is nothing to permute and no `q₀` to
measure; a permutation null / power model is the wrong instrument. jclass_v2's framing — pre-committed
exact `g₃` predictions with a verbatim deviation list per cell (§4 "decidable form of every") — is the
correct one.

## What C-center appeared to add, and why each delta does not survive
- **A measured-`q₀` decoupled null** — unnecessary: references' `g₃=0` is exactly certified (stronger
  than any permutation `q₀`); jclass_v2's C-NEG (pinned negative plants) already covers the "708
  accidental g=2 under an unpinned rule" concern.
- **The GLV-equivariance arm** — C-center itself demoted it to EXPLORATORY / non-verdict (D-TAUT: `λa`
  shares `a`'s μ₆-coset). Adds no verdict content.
- **The geometric-center framing** — unreachable (reason 2).

## Recommendation
**Do NOT produce a C-center v2 — it would duplicate jclass_v2.** The thesis (is the μ₃/ζ₃ lock
CM-type-specific?) is LIVE and correctly instrumented by jclass_v2; this is not a closure of that
question. The actual open work is **completing jclass_v2**: build its "to build" controls — C-COEFF
(gate C1, coefficient-sign, load-bearing: a sign error reproduces the all-zero off-j=0 table), C-FORCED
(C2), C-FIRE4 (C3, curve-derived firing on the reference arms so `g=0` off-j=0 is distinguishable from a
broken pipeline), C-ZERO (C4) — and write the arm runner (recorded unwritten + experiment-designer-gate-
blocked in `RESULT_cross_j_independence_check_v1.md`). That gate failing 3× is the first thing to
understand before building.

Two small C-center-origin deltas worth folding into jclass_v2 if it is completed:
- carry the honest object label ("arithmetic ζ₃-signature CM-specificity," not "geometric center");
- keep C-center's j=1728 construction note and the STAGING_NOTES arm-availability (6/10 discovery primes)
  as the runnable-prime filter.
