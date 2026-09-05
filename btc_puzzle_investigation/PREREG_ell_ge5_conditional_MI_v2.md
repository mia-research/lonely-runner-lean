# PREREG v2 — ℓ≥5 CONDITIONAL MI (incorporates the experiment-designer audit)

**Date:** 2026-07-25 · **Supersedes `PREREG_ell_ge5_conditional_MI_v1.md`, which was NEVER run on the
arms** — pre-data revision after the mandated `experiment-designer` audit (the intended workflow, not
p-hacking). Carries all of v1 §0–§7 unchanged **except** the two fixes below (both audit-required,
neither touches frozen data). Verifications backing this rewrite are in
`ell_condmi_verify_designer_v1.py` (identities 300/300; power split measured).

The audit's thesis verdict: **sound test of the pre-committed conditional blind spot, conditional on
these two fixes.** Points 1 (mediator principled), 2 (Mc+ is the decidable witness — rejects the
synthetic coupling marginal MI misses), 3 (both nulls
correct for their H0), 6 (scope correctly bounded) were CONFIRMED-OK.

## FIX 1 (point 5) — `Tcond` is PRIMARY for the shift alternative at ℓ≥11; per-arm power gate

**Measured** (uniform-shift injection `j=k+w` on fraction `s`, N=12000, detect `p<0.00625`, R=20):

| ℓ | s | `Icond` hit% | `Tcond` hit% |
|---|---|---|---|
| 11 | 0.03 | 35% | **100%** |
| 11 | 0.04 | 80% | 100% |
| 13 | 0.03 | 40% | **95%** |
| 13 | 0.04 | 75% | 100% |

⇒ `Icond` (ℓ strata × ℓ² joint cells) is **under-powered at ℓ≥11** for the pre-committed uniform-shift
alternative; `Tcond` (targeted, ℓ² cells) carries it. **Re-designation:**

- **PRIMARY = `Tcond`** (the shift-bridge alternative — exactly the E3-generalized law under test).
- **CO-PRIMARY = `Icond`** = omnibus that *alone* catches **non-shift** conditional dependence.
- **Per-arm power gate (pre-committed):** every null arm is reported **with its own R2 detectable-`s`
  floor** for that statistic; a null is graded "no bridge with copy-fraction `≳ floor`," never "no
  bridge." If a statistic's floor exceeds the injected target at that ℓ/N it is reported **no-power**,
  not null. Measured floors (≥80%): `Tcond` **s≈0.03** (N=12000) / **s≈0.06** (N=8000);
  `Icond` **s≈0.04–0.06** (N=12000) / **s≈0.06** (N=8000). R2 already covers all four ℓ (5,7,11,13).
- Bonferroni unchanged: 4 arms × 2 stats = 8 ⇒ threshold **0.00625**.

## FIX 2 (point 4) — C-cong gets a planted positive (`Mc-cong+`) and adequate stratified N

The audit verified a real **common-`U` channel**: since `p ≡ (t−1) mod n` and `n ≡ −(t−1) mod p`
(300/300), `j = χ_ℓ((t−1) mod n)` and `k = χ_ℓ(−(t−1) mod p)` are both symbols of `±U = ±(t−1)`. `U`
varies inside a `w`-stratum, so this is actual conditional dependence given `w` that the within-stratum
null (correctly) does not remove — **C-cong is the control that attributes it** (shared-`U` congruence
vs the CM tie). For C-cong to attribute a *positive*, it must be shown able to fire at its actual N.

- **C-cong uses the targeted `Tcond`** (`ℓ²` cells `d×w`, not `ℓ³`) so it has power at ℓ=13, and its
  **per-`w`-stratum N is reported**.
- **★ `Mc-cong+` (new machinery control, required):** on the real C-cong construction (two independent
  primes `P ≡ Q mod U`, both `≡1 mod ℓ`, stratified by the instance's `w`), inject a `w`-mediated shift
  `k' := (j' + w) mod ℓ` on a fraction `s` of pairs and require conditional `Tcond` to **fire**
  (`p ≤ 1e−3` at a modest `s`). This proves the C-cong instrument, **at its actual sample size**, can
  detect a congruence-only conditional coupling — so a C-cong *null* means "no such coupling," not
  "no power." Report the natural (un-planted) C-cong p beside it.

## Everything else unchanged from v1

§0 objects (mediator `w=(t−1)/ℓ mod ℓ`, forced `t≡1 mod ℓ` verified 300/300 per arm), §1 statistic
definitions + choice-freeness (M0 ✓), §2 the two nulls (both CONFIRMED correct for their H0), §3
machinery (M0 ✓, Mc+ ✓, Mc− calibration FPR-tracks-α ✓, R2 ✓ + Mc-cong+ new), §4 data controls
(C+, C−, C−r, C-cong-with-plant), §5 arms + drill-protocol decision rule (flicker < 0.00625 ⇒ OOS
retest before naming; all-null ⇒ bound with power+scope), §6 scope bounds, §7 falsification/prior-art.

Deviations: `PREREG_ell_ge5_conditional_MI_v2_DEVIATIONS.md`.
