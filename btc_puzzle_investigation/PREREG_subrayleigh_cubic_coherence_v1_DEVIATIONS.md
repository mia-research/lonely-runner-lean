# DEVIATIONS — PREREG_subrayleigh_cubic_coherence_v1 (run 2026-08-17/18)

Frozen spec SHA-256 `fbd8616e0643c83fb6671461e693078f953f0e8e1268ef313b2047f7cb0bef87`.
Recorded per the project's deviation discipline; each names the clause, what happened, and the effect.

**D1 — §7 power table is ~5× optimistic; CAL-OVER's `z_over ≥ +4 at p≥1249` bar is unreachable → routes to O2.**
§7 tabulates "per-prime z at δ=0.10%: 3.53 (p=1249) … 10.97 (p=12043)", but its own stated formula
`z ~ δ·√(p−1)/0.135` gives `z ≈ 0.26` at δ=0.1% (p=1249) — an internal inconsistency (~10–13×). The run
confirms the formula, not the table: a **calibrated +1.0% planted deficit** (CAL-OVER, plant_def measured
+0.69…+1.11%) fires `z_over` monotonically and correctly, but reaches +4 only at **p ≳ 7600**
(+4.0 at 7639, +5.0 at 12043), not at p≥1249 (where it is +1.1). This is **not** over-matching (the O2
failure mode): CAL-UNDER passes (pooled +1.38 ∈ [−3,3]) and CAL-OVER responds monotonically in the right
direction — the instrument is calibrated; the spec's threshold rested on the bad table. **Per the frozen
decision rule this still routes to O2: the coherence-matched primary `Z_B` is INVALID as a verdict; report
the secondaries (`D_slice`, MC-HP).** The primary was NOT rescued post-hoc by relaxing CAL-OVER (that would
violate the discipline). `Z_B` is reported as computed, explicitly NOT as a verdict.

**D2 — P-COH threshold `|C_char| ≥ √n · median|C_MCHP|` over-excludes (7/30 pass).**
P18 (`|C_char| ≈ √p·n²`) is confirmed present at all 30 primes by P-DIR (`|C|/bound ∈ [0.86,1.04]`, all
pass). Yet P-COH excludes 23/30 — the `√n` factor is too aggressive: a shuffled `|C_MCHP|` is a
non-trivial fraction of `|C_char|`, so `√n·median` exceeds `|C_char|` at most primes. The coherence IS
present (P-DIR proves it); P-COH's specific threshold is miscalibrated. Effect: moot — the primary is
already O2-invalid (D1), so the P-COH-restricted primary pool is not used for any verdict.

**D3 — rejection sampler starved (as anticipated); importance-reweighting fallback used and recorded.**
The 2% complex-match acceptance is ~1/4000 « the spec's 1/500 switch threshold, so the §8-declared
importance-reweighting fallback (Gaussian kernel in `S − C_char`, bandwidth widened to ESS ≥ 300) was used
throughout. CAL-UNDER/CAL-OVER were run under the fallback (as §8 requires). The fallback inflates the
conditional L1 variance (reducing `z_over`, contributing to D1); the clean secondary `D_slice` (vs the
L2-only null B0, no reweighting) is unaffected.

**No deviation on:** the frozen 30-prime schedule (asserted equal, all n odd, all generators found incl.
composite n), the exactness anchors (E_rel ≤ 1.3e-15 all primes; global anchor validated), P-DIR (30/30),
the a₀=1 primary, the model-scale banner, and the H0/anti-suppression framing.
