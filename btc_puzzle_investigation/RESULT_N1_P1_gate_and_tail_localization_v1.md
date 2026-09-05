# RESULT — N1: parity refuted, bulk moment shown blind, anomaly localized to the tail (v1)

**Date:** 2026-07-20
**Object:** Anomaly **N1** — `χ₂(y)` saturates `0.470 → ½` of its `4√p` Weil ceiling while the
same-dimension `bx+cy` reaches `0.876`. Recorded status in `POSITIVE_FINDINGS_MASTER_v4.md`:
*"the one measured anomaly in the set with no account. Twice attempted, twice not closed."*
**Scripts:** `chi2y_parity_saturation_v1.sage`, `n1_P1_calibrator_gate_v1.sage`,
`n1_P1_positive_control_v1.sage`.
**This file yields NO verdict on N1.** N1 is as unexplained after this work as before it.

---

## 1. The parity mechanism: claim correct, consequence REFUTED `[MEASURED]`

**The claim, which is correct.** `−P = (x,−y)`, so `χ₂(y_{−P}) = χ₂(−1)·χ₂(y_P)`. At `p ≡ 3 mod 4`,
`χ₂(−1) = −1`, so `χ₂(y)` is **odd** in `d`; at `p ≡ 1 mod 4` it is **even**. Verified exactly,
10/10 primes. This correctly accounts for finding M4 (`V(a)` purely imaginary at `p≡3 mod 4`,
purely real at `p≡1 mod 4`).

**The consequence, which fails.** A mechanism "oddness forbids coupling with even eigenspaces,
starving two channels" predicts that `p ≡ 1 mod 4` — where `χ₂(y)` is even and the restriction is
absent — must NOT sit at ½. Measured saturation `max|V(a)|/(4√p)`:

| `p mod 4` | primes | `χ₂(y)` parity | saturation |
|---|---|---|---|
| 3 | 991, 1051, 1303, 1831, 2143 | **odd** (5/5) | 0.4966, 0.4944, 0.4879, 0.4975, 0.4959 |
| 1 | 1237, 1249, 1669, 2089, 2281 | **even** (5/5) | 0.4999, 0.4977, 0.4893, 0.4987, 0.4890 |

**Identical in both classes.** A mechanism present in one class and absent in the other cannot
explain a constant. **Parity as cause is refuted.** This independently reproduces the master's M4
line ("parity does not cause the ½ — both classes ≈0.47") by direct measurement.

*Note the values here (0.488–0.500, `n ≈ 1000–2200`) sit above the recorded 6-prime figure
(0.470) and are consistent with the recorded convergence sequence `0.432, 0.455, 0.477, 0.459,
0.500, 0.499` tending to exactly ½. The tightness of that convergence is a datum in its own right
and suggests something exact rather than statistical.*

## 2. The bulk 4th moment is structurally blind to this question `[MEASURED + REASONED]`

`PREREG_N1_eigenvalue_starvation_v1.md` chose `M4 = (1/n)Σ_a|V(a)|⁴ = Σ_t c(t)²` as primary,
to escape the max statistic's upward bias. Its run-blocking gate P1 (known-rank calibrators must
separate) was executed. **P1 FAILED:**

| readout | nominal dim | `M4/n²` at `p=1303` | at `p=2143` |
|---|---|---|---|
| `χ₂(y)` | 4 | 2.0234 | 1.9884 |
| `χ₂(x)` | 2 | 2.0260 | 2.0187 |
| `bx` | 3 | 2.0418 | 2.0225 |
| `bx+cy` | 4 | 1.9948 | 1.9664 |
| **random ±1** | — | **1.9211** | **2.0085** |

No separation; every readout equals the random control. **Per the prereg's pre-committed outcome
cell P1: PIPELINE DEFECT — no N1 verdict in either direction.**

**The statistic is sound; the specification was wrong.** Positive control at `n = 1249`:

| plant | `M4/n²` |
|---|---|
| true spectral rank 1 | **156.13** |
| true spectral rank 2 | **312.25** (exactly linear in rank) |
| random ±1 | 2.03 |

So the implementation detects genuine spectral rank with a factor ~150 margin. The failure is a
**specification error**:

> **"dim 4" is a Weil bound on `max|V(a)| ≤ 4√p`. It is NOT a statement about DFT support.**
> `χ₂(y_d)` has full-support, random-looking spectrum with `|V(a)| ~ √p` at typical `a`. The
> dimension manifests only in how few frequencies approach the ceiling — `O(1)` frequencies out of
> `n`, contributing `O(n)` against a bulk of `O(n²)`. **No bulk average over all frequencies can
> ever detect it.** Any future statistic of that form is disqualified a priori.

## 3. What this DOES establish: the anomaly is an extremal-tail phenomenon `[MEASURED]`

Combining the two measurements localizes N1 rather than merely failing to explain it:

- **Max separates the readouts:** `χ₂(y)` 0.470 vs `bx+cy` 0.876 — identical dim, ceiling,
  frequency count, estimator.
- **Bulk 4th moment does not separate them:** 2.02 vs 1.99, both equal to random.

The readouts are therefore **not** noise — they demonstrably differ — and **the entire difference
lives in the extremal tail** of the distribution of `|V(a)|/√p`. This is a bounded
characterization, and it is the sharpest statement N1 has had.

## 4. Consequence for the extraction programme `[SCOPED]`

Proposals of the form "target the specific μ₆-isotypes carrying the missing mass" or "pick the
active eigenvalues locally from a single point" presuppose **spectral concentration** — a sector
holding disproportionate energy. At the primes measured, under this statistic, the energy is flat
(2.0, versus 312 for a genuinely concentrated object). This is consistent with two prior results:
**M15** (character energy exactly `1/6` per μ₆-isotype in five isotypes, cross-isotype
orthogonality ≤1.6e-15) and **M20** (six isotype-pure readouts × 9 curves, `p=211→6397`, no
concentration above the power floor, 54 cells).

**Scope, stated tightly:** this bounds *spectral concentration in the bulk, at `n ≲ 2200`, under
one statistic*. It does not establish that no gate exists.

> **⚠ CORRECTION — this section was overstated. Handover 3's central result applies to it.**
>
> H3 point 3, `[PROVED]` + `[CITED: Weil / Kohel–Shparlinski]`: *"Every 'null' in this whole
> investigation used a MISALIGNED readout… a misaligned readout sees exactly `√p` noise. So 'we
> measured `√p`, therefore generic' was evidence about **the instrument, not the curve** —
> provably."*
>
> **Every readout in §2's table — `χ₂(y)`, `χ₂(x)`, `bx`, `bx+cy` — is a misaligned readout.**
> Finding them indistinguishable from random is therefore close to what H3 says is *provably*
> guaranteed regardless of what the curve does. This measurement is largely a fact about the
> instrument. It does **not** carry the weight I originally gave it against isotype-targeting
> proposals, and the sentence "the energy is flat, so there is no concentrated sector to target"
> is withdrawn as stated.
>
> **What still survives the correction**, because it is a *differential between two misaligned
> readouts* rather than an absolute magnitude: `χ₂(y)` (0.470) and `bx+cy` (0.876) have identical
> dimension, ceiling, frequency count and estimator, and differ by 1.86× in the max while being
> identical in the bulk. Both are misaligned, so the misalignment cancels in the comparison. That
> differential is the anomaly, and §3's localization of it to the extremal tail stands.
>
> The M15/M20 equipartition and no-concentration results are cited above as context; note they
> are themselves misaligned-readout measurements and inherit the same caveat. They should not be
> quoted as bounding aligned structure.

## 5. What this does NOT say

1. **N1 is not explained, dissolved, or closed.** The ½ is untouched.
2. **Starvation vs spreading is NOT settled.** I previously stated the 4th moment would settle it
   in one integer. **That was wrong** — the statistic is blind to the distinction (both readings
   produce the same max and the same flat bulk). The control caught this before it produced a
   false answer.
3. **No ECDLP or security claim** follows from anything here.
4. The `p mod 4` result refutes *one named mechanism*, not the anomaly.

## 6. Next

`PREREG_N1_tail_structure_v2.md` — commissioned via `experiment-designer`, targeting the upper
tail of `|V(a)|/√p`. Its run-blocking precondition is a **plant-separation test**: two synthetic
objects with matched marginals, one genuinely 2-of-4 starved and one 4-live-but-phase-locked. A
statistic that cannot separate those two cannot answer N1 and must abort before touching curve
data.
