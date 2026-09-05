# RESULT — μ₃ PHASE alignment within GLV triples: a scoped null, and a caught null-miscalibration

**Date:** 2026-08-10. Executes `PREREG_mu3_phase_within_triple_v1.md`.
**Grade:** `[EMPIRICAL — scoped null, corrected null]`. No grade change to the −13.99σ deficit
(`RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`), which stays real, matched-null-surviving,
mechanism-open.
**Artifacts:** `mu3_phase_within_triple_v1.py` (statistic + gauge/plant/negative selftest, header now
carries the pooling WARNING); `mu3_phase_within_triple_globalnull_v2.py` (the CORRECTED decision runner);
logs `mu3_phase_within_triple_v1_run.log` (biased), `mu3_phase_corrected_null.log` (decision);
`phase_facts.py`, `phase_null_diagnostic.py` (scratchpad).

---

## 1. What was tested

The PHASE complement of the magnitude probe (`RESULT_mu3_glv_frequency_support_v1.md`, scoped null):
whether the three complex values of a μ₃/GLV triple `u_j=U(a₀,β^j b,c)` concentrate in a μ₃-isotype
(`u_j≈ω^j·C`) in their PHASE, at fixed magnitudes. Gauge-invariant statistic (forced ± gauge is per-rep
conjugation, so only `Re(u_j)` and `|u_j|` are admissible):
`ψ = |Σ_j ω^{-j} Re(u_j)|² / Σ_j|u_j|²`, and `|R_ω|² = ½Σ_{i<j}(r_i−r_j)²`, so summed over triples the
only quantity that moves under repartition is `P = Σ_{within-triple pairs} r_i r_j`.

Controls (all correct): forced-diagonal implementation self-test Var(|U|)=0; gauge self-test
`ψ−ψ_flip=0.00e0` over all 8 gauge flips; **plant fires** (μ₃-aligned phases, Z=+142 at p=2089);
**negative flat** (random phases, Z=−1.13). The statistic is gauge-invariant, non-forced (ψ varies
0.004–0.79), and specific.

## 2. The finding that mattered — a null-miscalibration, caught before it became a false positive

The first run used an **analytic per-block permutation null** (closed-form moments of `P` under
repartition, exact PER BLOCK) and pooled per-block variances across the `(a₀,c)` blocks. It returned:

| pooled Stouffer Z (analytic, 24 a-reps) | **+10.356** — every prime ≈ +3.4 (+3.39…+3.55) |

**The tell:** the per-prime Z was ~**constant across a 10× range of N** (p=2089→19249). A genuine
per-block signal grows like √N (≈+3.4→≈+10); a Z flat in N is the signature of a **variance
under-estimate**, not a signal.

**The mechanism:** the true μ₃-grouping `{b,βb,β²b}` is the SAME across all columns and a-reps, so the
honest null must draw ONE regrouping and apply it across all (correlated) blocks. Pooling per-block
variances treats the blocks as independent and **under-estimates Var(P_total) by ~2.85×**, inflating
every prime's Z by that constant factor. The negative control could not catch this: randomizing phases
destroys the inter-column correlation that inflates the variance, so it is not matched to this failure.

**The check (`phase_null_diagnostic.py`):** comparing the analytic Z to an empirical **global-repartition**
null (one regrouping shared across all blocks) on the same data —

| p | analytic Z (biased) | empirical global-null Z (correct) | std ratio |
|---|---|---|---|
| 2089 | +1.71 | +0.61 | 2.88 |
| 8191 | +1.78 | +0.64 | 2.84 |

## 3. Corrected decision (`mu3_phase_within_triple_globalnull_v2.py`, all 9 primes)

Empirical global-repartition null (one regrouping shared across every block — the correct null), 6 a-reps
(Z is a-rep-invariant: numerator and denominator both scale with the shared grouping), B=400:

| p | analytic Z (biased) | **global-null Z (decision)** |
|---|---|---|
| 2089 | +1.71 | +0.67 |
| 2143 | +1.79 | +0.68 |
| 4159 | +1.71 | +0.64 |
| 8191 | +1.78 | +0.66 |
| 8209 | +1.73 | +0.61 |
| 8293 | +1.75 | +0.62 |
| 16477 | +1.71 | +0.58 |
| 19231 | +1.72 | +0.57 |
| 19249 | +1.72 | +0.61 |
| **POOLED Stouffer** | **+5.20** (artifact) | **+1.88 (decision)** |

## 4. Reading (pre-committed outcome table, PREREG §9)

Corrected pooled **|Z\*| = 1.88 < 3**, PLANT fired, NEGATIVE flat ⇒ **SCOPED NULL**. Per the
pre-commitment, we abandon "the deficit's μ₃ phase is organized in the gauge-invariant real-part isotype"
at this power/scope. Companion to the magnitude null: within μ₃-triples, both the near-zero magnitude
co-occurrence AND the real-part phase isotype co-occur at chance.

**What this closes (named):** object = real-part μ₃-isotype energy `|R_ω|²` of `U(a₀,·,c)` on CM
`y²=x³+7`; class = quadratic gauge-invariant μ₃-phase content of the real parts; power = the corrected
global-null resolves the effect at pooled |Z*|≈1.9 over 9 primes to p≈19k; scope = 9 listed primes, τ-free
(phase), 6–24 a-reps.

**What this does NOT close (scoped, not structureless):** higher-order phase invariants; the imaginary-part
isotype (gauge-washes to `ΣIm²` at 2nd order — a different object); c-column-specific phase structure
invisible after pooling; and the −13.99σ deficit itself (unchanged, row-budget shadow still its live
candidate).

## 5. A bounded sub-threshold observation (not a finding — flagged, not buried)

The corrected per-prime Z is a **consistent small positive** (+0.57…+0.68, pooled +1.88), below the
falsification threshold. This is plausibly the **forced λ-orbit-character correlation**: by the pullback
`U(a₀,βb,c)=U(λ⁻¹a₀,b,c)`, a true μ₃-triple is `U` at three related characters `{a₀,λ⁻¹a₀,λ⁻²a₀}` of the
same point-sum, whereas a random repartition groups three unrelated frequencies — a structural asymmetry
that need not be a leak. Resolving forced-vs-real would take the **CM/non-CM discriminant** (β exists on a
non-CM curve with 3|p−1, but no λ, so the character-orbit identity is absent); it is not a fired cell, so
it was not run. Recorded as the natural next probe if this sub-threshold consistency is pursued.

## 6. Methodological lesson (for the ledger)

A control that "must fire" (here the negative) can still MISS a variance-miscalibration if the control
does not share the signal's correlation structure — randomizing phases destroyed the very inter-column
correlation that inflated the variance. The diagnostic that caught it was **effect-size scaling with N**:
a Z that is flat as N grows is a variance artifact, not a signal. Both directions of the asymmetric-rigor
loop held: the probe was run and its +10.36 taken seriously (no suppression), and the +10.36 was audited
to null before being reported as a find (no inflation).
