# DEVIATIONS — `PREREG_mu3_orthogonal_projection_v1.md`

Run artifacts: `mu3_projection_v1.py`, `mu3_selfnull_v1.py`, `mu3_projection_discovery_run_v1.out`,
`mu3_selfnull_run_v1.out`, `RESULT_mu3_projection_v1.md`.

---

## D-strat — the §6.1 stratum table is void in this frame (supersingular labels wrong)

**Spec §6.1** labels strata S2/S3 (`p ≡ 7 mod 12`) as "supersingular" with the `A_new` char poly
`t⁴+mpt²+p²` and `m`-values. **`y²=x³+B` is supersingular iff `p ≡ 2 mod 3`.** The frame *requires*
`p ≡ 1 mod 3` (else `β ∉ F_p` and GLV is undefined), so **every frame unit is ordinary** and no unit is
supersingular. The `m`-law / `A_new`-supersingular labels do not apply.

**Handled:** units are relabelled by the only invariant that actually varies here — `p mod 4`, which
sets `χ₂(−1)` and hence whether χ₂(y) is μ2-odd (`p≡3`) or μ2-even (`p≡1`). Both classes show the ½
identically. Consequence: **S2 is empty** (its condition is part of the void table), reported as a
label defect, not a filter. This does not affect the §2 result of the RESULT file, which is an exact
magnitude cap independent of the stratum labels.

## D-float — `|V|²` via numpy FFT, not the §8 certified fixed-point

**Spec §8** specifies certified fixed-point arithmetic (`B ≥ 128` bits) for ordering `Q_f(a)`.
**Taken:** numpy float FFT of the exact-integer c-sequence. This is the CLAUDE.md carve-out (a monotone
statistic ranked against a matched permutation null): the **same** float pipeline is applied to every
NULL-A draw, the primary is a rank, and a top-16 boundary-gap guard is printed per unit (typically
tens to hundreds, ≫ float epsilon at these `p`). **The §2 N1 cap does not rely on this at all** — it is
`max|V|/√p` reproduced to 3 digits on 22 primes. Signal path (c, coordinates) is exact integer.

## D-plantP1 — P-1 planted sequences are real-valued, not `{±1}`

**Spec §4 P-1** says `{±1}` sequences. **Taken:** real-valued planted sequences (white background +
`r` equal-amplitude cosines), so per-frequency magnitude is held fixed — which is exactly the
rank-resolution property P-1 must certify. The `{±1}` detail is not load-bearing for that property. P-1
orders correctly (S strictly increasing in r).

## D-discovery-only — replication decade and out-of-sample arm NOT run

**Spec §6.2** requires a disjoint replication decade (`n ∈ [10⁴,10⁵]`) and out-of-sample confirmation
before a `D₄` result may be named. **Only the discovery decade (`n ∈ [10³,10⁴]`) was run** for the
statistical D₄/self-null arms. Consequence: **the statistical H_proj refutation is discovery-only** and
is reported as such. The **§2 N1 magnitude cap is not a statistical claim** — it is an exact saturation
reproduced across 22 primes (12 discovery + 10 original N1 primes), so the replication requirement is
met in substance for that result; it is not met for the D₄ p-values.

## D-arm2 — Arm 2 (twisted eigenvalue multiset) NOT run

**Spec §2.6 / §6.3** specify a Sage/exact eigenvalue arm at `p ≤ 61`. **Not run.** The §2 empirical cap
(`max|V| = 2√p` for single-factor sums) is the object-level answer Arm 2 targeted, at the *magnitude*
level; the **eigenvalue-multiset proof** that single-factor → `H¹` top-mass dimension 2 remains owed
and is the named next step (Sage is available).

## D-P3 — P-3 detects only δ = 0.5 per unit

As the §5 power estimate predicted (per-unit `δ ≈ 0.35–0.45`). The observed effect is ½-scale, so
per-unit detection at δ=0.5 suffices and the pooled statistic is `Z=11`. Not a defect; the disclosed
per-unit power limit.

## Not deviations

- Frozen readout parameters (`x₀`, `(x₁,x₂)` by the deterministic least-integer rule), generator rule,
  `A_rep = (n−1)/6` μ6-orbit reps, `k=16`, exact `l²` identity check — all as specified.
- The literal projection was **not** run (it is a forced zero, §1.3); the registered object was H_proj.
