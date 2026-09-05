# RESULT — E3 (A-1d) owed measurement DISCHARGED: set-specific reject survives the generator-free null, bounded family-wise

**Date 2026-08-18.** Executes FROZEN `PREREG_e3_owed_measurement_v2.md` (arms A1–A4), `experiment-designer`-
signed core engine. Discharges `POSITIVE_FINDINGS_MASTER_v12.md` **§E.3** / `ROADMAP_REDIRECT_v3.md`
**Brick A**. Script `e3_owed_measurement_v1.py`, log `e3_owed_measurement_v1.log`, summary
`e3_owed_measurement_v1_summary.json`, nulls `e3_struct_null_{E2,E3,E6}_v1.npy`. Integer-exact signal +
decision path (`check_no_float.py`: only display p-values/percentiles/powers are float; every verdict is
integer). No security / keyspace / extractability claim is made or reachable.

**Grade:** `[EMPIRICAL @ secp — set-specific cubic reject vs a generator-free structural null (p=0.035,
98.2nd pctile), BOUNDED: family-wise non-significant (p_FWER=0.083 over {E2,E3,E6}; Bonferroni 0.248 over
the 7-stat session), N=82 power ceiling. NOT dissolved, NOT family-wise significant.]`

---

## 0. What was owed, and what this settles
Master §E.3: *"E3 (A-1d) owes a MEASUREMENT — MC-correction across the pre-registered family; reproduction
(exact); a matched null sharing the signal's forced symmetries; OOS on the constructed known-generator set.
Until then it is neither signal nor noise."* All four delivered. The load-bearing question the
`CORRECTION_e3_cmvanishing_interaction_reading_v1` raised — *"E3's null is a known-MT pool, so the test is
a generator test whatever the instrument; check the null's provenance"* — is answered by **replacing** the
generator pool with a generator-free structural null (A1). **The reject survives.**

## 1. The two positives (surfaced first; each carries its test)

**A1 — the reject is NOT a generator-pool artifact.** Structural null = 20,000 sets of 82 uniform random
valid secp `E(F_P)` points (no `d`, no PRNG, no bit-length) — shares E3's forced symmetries (valid-x
population, j=0/μ₆ cubic bias, 3321 pairs, `a+b+c=3321`, `E3≡0 mod3`), differs only in the tested contrast.
At N=20000 its 97.5th-percentile region **[84, 11973]** converges onto the retired MT-null region [84,11997];
the generator provenance was **not** carrying the effect.

> `E3(real)=13125 > U_struct=11973` → **REJECT-HIGH**, 98.24th pctile, two-sided `p_struct=0.0354`.

**A3 — the excess is SET-SPECIFIC, not bit-band/pipeline.** 1,000 band-matched known-MT19937 sets (one
constructed key per real bit-length — the full-power known-generator control, `feedback_test_on_both_sets`)
have median E3 at the **48.6th** pctile of the structural null (pipeline is neutral), and

> `q_MT = #{MT-set E3 ≥ 13125}/1000 = 0.015` → real is above **98.5%** of band-matched known-MT sets.

The excess needs the specific real `d`-values; identical bit-bands with MT-drawn keys do not reproduce it.
(Consistent with the independent band-arms null E3=0.503, `RESULT_chi2_diffset_FALSE_POSITIVE_v1`.)

**Instrument fires (A4).** β²-count plant on structural-null sets (E3 = f(cube marginals), so the plant is
exactly matched): Δ=0 FPR **0.022** ≈ nominal 0.025; monotone; power **0.878** at Δ=100, **1.000** at Δ=150.
At the real effect's own magnitude (deviations −25/−50/**+75** in β²) power is ~0.57 — a genuine-but-weak
effect at N=82, exactly what a `p≈0.035` single-statistic reject predicts. A null here would have been
informative, not blind.

## 2. The bound (with power + scope — a brick, not a closure)

**A2 — family-wise non-significant.** Westfall–Young max-statistic (min-p) over the character family
{E2,E3,E6} on the same structural null, integer p-numerators, symmetric `+1`, inclusive-tie convention:

| statistic | two-sided p vs structural null |
|---|---|
| E2 (quadratic) | 0.932 |
| **E3 (cubic)** | **0.0354** ← the family standout |
| E6 (sextic) | 0.445 |

`p_FWER(E3) = 0.0833` (does not clear α=0.05). Bonferroni ×7 across the full 2026-07-26 session family
{μ₆-marg, χ₂-marg, 12-cell, KW, point-biserial, S_diff, E3} = 0.248.

**Scope of the bound (what it does and does NOT close).** This bounds the **pooled, orientation-symmetric,
marginal cubic energy** channel — E3 is `¼|1ᵀC1|²`, one rank-1 all-ones projection of the 3321 pairwise
field differences. It is **blind by construction** to orientation-odd, joint-triple, and band-localized
subspaces (`RESULT_spectral_decomp_v1`: secp's orthogonal modes are *quieter* than random, 6.5th pctile — a
rank-1 excess with compensating suppression, a constraint signature). **Power ceiling:** N=82 is the entire
sample (#135 unsolved; no solved-key statistic transfers except via a generation model, out of bounds); raw
`p=0.035` cannot strengthen under null redraws. So the bound is: *the marginal cubic-energy channel carries
a set-specific reject that does not survive family-wise correction and cannot exceed this magnitude on this
statistic.* It is **not** a closure of the cubic channel.

## 3. Curve-class scope (A5 folded from the established field-fixed fact; μ₄ arm deferred)
A1 rejected, so A5 is live. Its **field-fixed** content is already in hand and reused, not re-run: on the
**same prime P**, the E3 excess is present on secp (j=0/μ₆/CM) and **absent on non-CM E′** (`y²=x³+x+1`,
67.1st pctile, fail-to-reject — `RESULT_diffset_cubic_cmvanishing_v1`). No field confound (same χ₃). So the
reject is a **key-set × curve(CM/j=0) interaction**: expressed *through* secp's cubic endomorphism structure,
not a curve-independent `d`-fingerprint (which would show through any curve map). **Form-level, banner-
admissible with its own proof obligation.**

**μ₄ discriminator — deferred, not run.** Over secp's own field `P≡3 mod4` the clean j=1728/ℤ[i]/μ₄ object
does not exist (supersingular, no F_P-rational μ₄, no Cornacchia) — a structural scope fact
(`experiment-designer` audit, `RESULT_cm_ring_universality_v1`). A μ₄ check would need a prime `p′≡1 mod4`,
reintroducing a **named field confound**; it is optional, field-confounded, needs its own re-gated prereg,
and is a sharpener. Investigation>sharpening: not run here.

## 4. Net — the brick, and the named next probe
**Standalone** (frozen prereg + script + nulls + summary). **Reusable:** (i) a generator-free structural-null
percentile machinery + integer FWER, portable to any set statistic; (ii) the graded fact — *E3=13125 is a
set-specific, CM-mediated cubic-difference concentration on secp, surviving the correct null, bounded to a
family-wise-non-significant magnitude at the N=82 ceiling.* **Direction-true:** carries null (structural),
control (A4 fires; E′ dissolves), OOS (q_MT), grade, scope.

**This is not a door shut.** The bound is on **one marginal rank-1 statistic**; the effect is real at the
single-statistic level and set-specific. The named next probe is the one both the correction and cmvanishing
point to — a statistic extracting more from the **same 82 keys**, where E3 is blind:
1. **Group-law E3** — `χ₃(x(P_i − P_j))` via curve addition, the CM endomorphism's native operation
   (Frontier #29); prediction: fires harder than the field-difference version because the group law is where
   CM acts.
2. **Triples** `C(82,3)=88,560` / band-localized structure — more resolution from the fixed sample than any
   number of E3 reruns can give (the power ceiling is on E3, not on the key set).

## 5. What no grade elsewhere may claim from this
No promotion elsewhere. This removes the master's "neither signal nor noise" caveat on A-1d by **measuring**
it: a bounded, set-specific, CM-mediated positive with power+scope, and a live next probe. It is not a
keyspace reduction, not extractability, not a cubic-channel closure.

*Predecessors: `RESULT_diffset_cubic_v1` / `_secondcontrol_v1` / `_cmvanishing_v1`,
`CORRECTION_e3_cmvanishing_interaction_reading_v1`, `RESULT_spectral_decomp_v1`,
`RESULT_chi2_diffset_FALSE_POSITIVE_v1`, `RESULT_cm_ring_universality_v1`. Frozen spec:
`PREREG_e3_owed_measurement_v2.md` (§7 gate audit). Debt closed: MASTER_v12 §E.3.*
