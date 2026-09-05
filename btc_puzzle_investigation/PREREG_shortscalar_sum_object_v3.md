# PRE-REGISTRATION (v3) — short-scalar character structure: contiguous-interval sum + band pairwise-sum

**Status: `[FROZEN on SHA below — experiment-designer FRAME-GATE cleared for the corrected design]`.**
Supersedes v1 (Weil defect) and v2 (multiplicity defect). Both retained as the record of the two
caught errors. Control spec inherited from `RESULT_shortscalar_cneg_recalibration_v1.md` (n≥20 C-NEG).

---

## §0.1. Change log — two frame defects were caught and fixed

- **v1→v2 (self-audit):** retracted a Rule-1 violation (using a Weil bound to pre-expect k≥128 nulls).
- **v2→v3 (experiment-designer gate, 2026-08-02 — BLOCKING defect):** v2's PRIMARY arm (R-CONTIG as
  the pairwise **sum** of a contiguous block) is **fatally artifacted**. In a contiguous block
  `Pᵢ+Pⱼ = [2d₀+i+j]G` depends only on `i+j`, so the `C(L,2)` pairs collapse onto `2L−3` distinct
  points, each heavily multiplied, all copies sharing one χ value. The magnitude statistic inflates by
  `Σmult²/C(L,2) ≈ L/3` (**133× at L=400**) vs a geometric all-distinct null — a **pure counting
  artifact, independent of curve structure**, that would screen AND replicate 5/5 OOS (multiplicity is
  identical every seed). **Fix (the gate's, verified empirically — `shortscalar_sum_stageA_v1.py`
  C-ARTIFACT does not fire):** the distinct sum-points *are* `{[s]G : s ∈ contiguous interval}`, so
  R-CONTIG is correctly the **incomplete character sum over a contiguous interval**,
  `Σ_{s∈I} χₖ(x([s]G))` over `L` consecutive points, matched vs `L` random points — multiplicity 1 on
  both sides, defect closed, and now **O(L) not O(L²)**. R-BAND (genuine all-distinct pairwise sum) is
  unaffected — the gate confirmed it valid.

## §0. Counter-prior and scope boundary (binding)
Constructed scalars only; no puzzle keys, no 82-key object, no generator pool. Null provenance =
uniform random curve points. A quiet arm is a **bound** (§5), never a closed channel.

## §1. Objects, and why the readouts are legal (FRAME — gate-cleared)

### §1.1 Two short-scalar objects
- **R-CONTIG [PRIMARY]:** `Σ_{s∈I} χₖ(x([s]G))`, `I = {s₀, s₀+1, …, s₀+L−1}`, `s₀ ∈ [2^{k−1},2^k)`.
  The incomplete character sum over a contiguous interval of consecutive scalar-multiples. **O(L).**
- **R-BAND [SECONDARY, labeled low-power]:** the swap-invariant pairwise sum `x(Pᵢ+Pⱼ)` over `M` points
  `[d]G`, `d` uniform in `[2^{k−1},2^k)`; sums generically all-distinct (birthday collisions ≲2 at
  k≥40), so the geometric null is matched. **O(M²).** Tests band-membership via joint-2 sums.

**Why χ₂/χ₃/χ₆ are all legal (algebraic, Rule 1 — corrected reasoning).** On both objects each pair /
each point yields **one canonical field value** because `x(−Q)=x(Q)`, and the value multiset is **not
negation-closed** (the odd-character void of `ANALYSIS_diffset_readout_parity_void_v1.md` is specific
to the negation-closed **field-difference** multiset `{xᵢ−xⱼ}`). *(v2's justification "s>0, no −s
partner" was a non-sequitur — the gate flagged it; the operative reason is `x(−Q)=x(Q)` giving one
value per readout, verified by the C-GLV forced-zero E₃=E₆=0.)*

### §1.2 Why R-CONTIG is not a dismissable marginal (Rule 1, honest)
`Σ_{s∈I}χ(x([s]G))` is a **sum of per-point readouts over a structured set**. A single term is
Farey-generic; the sum over a **contiguous interval** is the classical **incomplete character sum** —
the one regime the completion/Weil bound is **vacuous** for (`|I|=L ≪ √p`), per
`ANALYSIS_correlation_hierarchy_weil_closure_v1.md`. Vacuous ⇒ theory neither predicts nor forbids ⇒
**we measure it against a matched null** (this is the correct use of the closure classification — to
*motivate* an empirical probe, never to *pre-expect* a null; contrast the retracted v1 error).

### §1.3 Disjointness
Feature = χ of a point's x-coordinate (nonlinear, ECDLP-hard in `s`); structure under test =
contiguity/band-membership of the scalars. No shared algebraic component; not fired by construction.

## §2. Statistics and decision rule
**Readouts:** χ₂, χ₃, χ₆; magnitude `E₂,E₃,E₆ = |Σχ|²` (exact integer forms, Appendix A; sensitive to
**coherent** bias) + `D₆` = integer 6-cell histogram χ²-numerator (`Σ(6H−T)²`; catches **non-coherent**
concentration). Cells = readouts × k.
1. Rank each arm statistic vs the matched-null reference → exact `Fraction` p-value. **All per-cell
   p-values reported UNCORRECTED.** No FWER suppression at the screen.
2. **SCREEN:** cell exceeds the **99th** percentile of the matched null.
3. **GATE = OOS:** a screened cell is named a candidate only if it exceeds the 99th on **≥5 independent
   fresh seeds** (arm + null re-drawn). Screen-once-fail-OOS → reported as a non-replicating screen.
4. **Bound** (Rule 5): below the 95th on all seeds → report measured floor ε*.
5. **C-NEG** per the recalibrated n≥20 rule (Step 1); a single high draw is not a fire.
6. **Holm** over the cell family = reported secondary summary only; does not gate/suppress.

## §2·CAL. Calibration (MECHANICAL)
- C-ARTIFACT (structureless oracle) must NOT screen — **verified** at smoke (all cells mid-dist).
- Screen+5-seed-OOS false-positive rate under H₀ (null vs null), ≥10⁴ reps, target ≪0.05 family-wise.
- C-NEG re-confirmed on the interval statistic (same machinery as Step 1).

## §3. Matched control / null geometry (FRAME — gate-cleared; Rule 3)
**Primary gating null:** uniform random curve points (QR-rejection on `x³+7`, **no scalar
multiplication** ⇒ uniform group element, cofactor 1); same statistic over `L` points. Multiplicity 1 —
matches the corrected R-CONTIG exactly (the v2 defect was precisely a multiplicity mismatch here).
**Secondary control (R-CONTIG):** a contiguous interval at a **random** `s₀` — same interval structure,
shuffled location; separates "contiguity/interval leaks" from "this band leaks." Reported.
**FORBIDDEN:** sums/points from random `F_p` integers (not curve x-coords ⇒ misaligned; artifact kill).
**C-GLV** φ-closed set ⇒ E₃=E₆=0 exact (instrument + legality; **verified**, complete-triples only).
**C-PLANT** cubic-class-biased set ⇒ fires ≥99th (**verified**, p=0/1000). **C-NEG** Step 1.

## §4. Plant-fires (MECHANICAL — verified at smoke; full ladder owed)
C-PLANT constructibility + power curve at δ∈{0,½δ*,δ*,2δ*}; the δ=0.18 plant fired at the 99th in smoke.

## §5. Power and the measured bound (Rule 5)
**R-CONTIG:** `|Σχ|²` over `L` points detects a **coherent** single-class fractional excess
`ε* = 2√V₉₉/L ~ 1/√L` from the measured null `V₉₉`. **Reported per L as the measured ε*.** Because
R-CONTIG is **O(L)**, the floor is pushed cheaply:

| L | expected coherent floor ε* |
|---|---|
| 10⁴ | ≈ 4.4% |
| 10⁵ | ≈ 1.4% |
| 10⁶ | ≈ 0.44% |

`D₆` covers non-coherent structure. **R-BAND:** `ε*=2√V₉₉/C(M,2) ~ 1/M` (O(M²)). The RESULT states the
**measured** floor, not these estimates.

## §6. Scope (FRAME — gate-cleared; Rule 4)
secp `p,G`; no "generic" labeling of a secp anomaly; **no global-bound down-weighting of any k** (v1
retraction stands). `k ∈ {40,64,96,128,160,200}`, no privileged value. Deferred (not dismissed):
non-dyadic intervals, triples, R-CLUSTER dense sub-windows, the group-law **difference** χ₂/χ₆ arm.

## §7. Falsification (FRAME — gate-cleared)
Candidate ⇒ screens 99th AND replicates ≥5/5 fresh seeds vs the matched geometric null; mechanism then
requires anomaly-drill characterization, never a verdict. Bounded ⇒ magnitude + ε*, channel open below.
Kill: fails OOS <5/5; C-PLANT dead; C-NEG miscalibrated; reproduced by the forbidden `F_p` null;
R-CONTIG fires but the random-`s₀` secondary fires equally (⇒ generic contiguity, re-scoped not named).

## §8. Exactness (MECHANICAL)
Pure `int` signal path; characters via `pow`; statistics integer quadratic forms + integer χ²-num;
ranks exact. Only float is the ε* display (`math.sqrt` on the null V₉₉, a monotone display of a bound,
never a signal-path threshold). Driver imports named functions; no `main`/plot path in the signal path.

## §9. Pre-commitment and freeze (FRAME — gate-cleared)
**Frozen:** objects (R-CONTIG primary, R-BAND secondary); readouts {χ₂,χ₃,χ₆} + D₆; k-ladder
{40,64,96,128,160,200}; **R-CONTIG L-ladder {10⁴, 10⁵, 10⁶}** (Stage A = 10⁵); R-BAND M-ladder
{400,1024,2000}; null pool multiplier (≥5) and R_null (≥2000); the screen-99th / OOS-≥5-seeds /
bound-95th rule; nulls (geometric primary; `F_p` forbidden; random-`s₀` secondary); C-GLV/C-PLANT/
C-ARTIFACT/C-NEG; seeds recorded per run. SHA-256 over the body pins this. Executing script:
`shortscalar_sum_stageA_v1.py`.

## §10. Compute plan (Rule 2)
**R-CONTIG is O(L)** (the v2 O(L²) was the artifact): `2L` modexps/arm × 6 arms; null pool `2·(mult·L)`
modexps ONCE, realizations are integer resamples. Measured `pow ≈ 85–90 µs` (Step 1 + smoke).

| stage | L | arm modexps (6·2L) | pool modexps (2·5L) | mode |
|---|---|---|---|---|
| A | 10⁵ | 1,200,000 | 1,000,000 | single-response (≤600 s) or logged |
| B | 10⁶ | 12,000,000 | 10,000,000 | background + logged (`-u`, log, never `tail`) |

R-BAND (O(M²)) sizing as in v2 §10. **M=6.25×10⁶ pairwise NOT in ladder** (Step 1 projection). Sampled
estimator for any `C(·,2) > 10⁶`.

---
## Appendix A — exact integer statistics
6-cell `H[code]`, `code=3b+c`: `E₂=((H0+H1+H2)−(H3+H4+H5))²`; `A₃=(H0+H3)−(H2+H5)`,`B₃=(H1+H4)−(H2+H5)`,
`E₃=A₃²−A₃B₃+B₃²`; `nm=[H0,H5,H1,H3,H2,H4]`,`A₆=nm0−nm2−nm3+nm5`,`B₆=nm1+nm2−nm4−nm5`,
`E₆=A₆²+A₆B₆+B₆²`; `D₆=Σ_code (6·H[code]−T)²`. All integers; ranks are integer counts.
