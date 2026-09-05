# ℓ≥5: the blind spot held no bridge — a mutual-information probe tightens the D3 null

**Date:** 2026-07-25 · Pre-registered: `PREREG_ell_ge5_mutual_information_v2.md` (frozen, audited by
`experiment-designer` before any data — R1/R2/R3/N1 incorporated). Scripts: `scratchpad/ell_mi_v*.py`,
`ell_mi_oos.py`, `ell_mi_final.py`. Exact integers for the number theory; MI/T are monotone statistics
against exact permutation nulls (project float rule satisfied).

Attacks the pre-committed blind spot of `RESULT_bridge_dichotomy_v1` §3: the 2×2 association test that
found `A⊥B` at ℓ=5,7,11,13 is blind to a bridge with a *uniform* correction. Mutual information is not.

---

## 0. The tool was verified before it was aimed (machinery, all pass)

| control | result | meaning |
|---|---|---|
| **M0** `Î`, `T` invariant under unit relabelings `ζ→ζ^a` | **bit-identical** (MI `0.8483602531` ×3; T ×3) | both statistics are **choice-free** (no dependence on the arbitrary root of unity) |
| **M0 bug caught pre-run (R1)** | at ℓ=3, exponent `3≡0` collapses the alphabet (`MI 0.4055→0`) | fixed to unit-only relabelings; would have spuriously voided the ℓ=3 controls |
| **M1 synthetic-positive** | 2×2 `(0,0)`-cell test `p=1.0` (blind); **MI `p=0.0001`** on the same coupling | **proves MI sees what the 2×2 cannot** — the blind spot is real and MI defeats it |
| **R2 power (injection)** | MI & T floor at **`s≈0.03`** (N=8000) | detects a shift-bridge where only **3% of instances copy** — strong power |

## 1. Calibration on real curves (the statistic has power against the KNOWN bridge)

| control | ℓ | result | expected |
|---|---|---|---|
| **C+** D=−3 (bridge known, B1) | 3 | **MI `p=0.0001`, T `p=0.0001`** | fires ✓ |
| **C−** D=−11 (no bridge, w=2) | 3 | MI `p=0.30`, T `p=0.34` | null ✓ |
| **C−r** random base, every arm | 5,7,11,13 | `p = 0.98 / 0.08 / 0.37 / 0.90` | clean ✓ |
| **C-cong** (R3, congruence-preserving/CM-breaking) | 5 | N=1178, MI `p=0.64` | null ✓ (functional) |

## 2. The arms, in-sample and out-of-sample

**In-sample** (30-bit `p`, N≈8000, seed 13):

| ℓ | MI p | T p |
|---|---|---|
| 5 | 0.649 | 0.800 |
| 7 | 0.501 | 0.204 |
| **11** | **0.0021** | 0.024 |
| **13** | **0.0130** | 0.115 |

Two arms came in below the gate. Neither was reported as a signal. Per the anomaly-drill protocol (retest out-of-sample
before naming any signal; the record already had 2 chance patterns die), and because MI fired *more*
than the shift-targeted T at ℓ=11 (`0.002 < 0.024` — the wrong ordering for a shift bridge), both were
sent to a fully independent retest:

**Out-of-sample** (32-bit `p`, N=12000, fresh seed 777333 / 424242):

| ℓ | in-sample MI p | **OOS MI p** | fate |
|---|---|---|---|
| 5 | 0.649 | 0.066 | null |
| 7 | 0.501 | 0.183 | null |
| **11** | **0.0021** | **0.663** | **DIED** |
| **13** | **0.0130** | **0.105** | **DIED** |

Neither replicated. With 8 primary tests, an in-sample min of `0.0021` (Bonferroni `≈0.017`) that fails
to replicate is consistent with multiple-comparison noise. These are the third and fourth in-sample
patterns in this record to fail an out-of-sample retest.

## 3. Result — graded as a bound, not an absence

> **No reciprocity bridge between `χ_ℓ(p mod n)` and `χ_ℓ(n mod p)` is detectable at ℓ=5,7,11,13 by a
> choice-free mutual-information (or shift-targeted) statistic, out-of-sample.**
> `[VERIFIED — bounded]`

**This is a real tightening of D3, not a re-run of it.** D3's 2×2 bounded only the `(0,0)` cell;
`I(j;k)` bounds the **full marginal joint** `(j,k)` over `(ℤ/ℓ)²`. Quantitatively (from R2): any
shift-bridge copying `≳ 3–6%` of instances, or any dependence explaining `≳0.1%` of the character's
entropy, would have fired — and none did, on a statistic that provably (M1) sees the uniform-correction
case the 2×2 missed, and that provably (C+) detects the genuine ℓ=3 bridge.

## 4. Scope — pre-committed, stated as bounds (not closures)

- **Marginal, not conditional.** An `I(j;k)`-null does **not** exclude `I(j;k | t,v,U) > 0`. The cubic
  correction `c₃` is itself a function of ideal data `(t,v)`; an ℓ≥5 bridge that is *purely
  conditional* on `(t,v,U)` would be invisible to marginal MI. **Untested.**
- **Rational, not ideal.** A null on the rational exponents `(j,k)` does **not** establish "no ℓ-th
  power reciprocity in `ℚ(ζ_ℓ)`." The general power-reciprocity law (Artin/Hilbert; Lemmermeyer Ch. 7)
  operates on symbols in `ℚ(ζ_ℓ)` with a **choice of prime ideals** over `p,n`; the rational projection
  can wash an ideal-level relation into rational independence. This probe bounds the rational shadow only.
- **Small ℓ only.** secp's own factors `149, 631, 107361793816595537, …` are **out of MI reach**
  (`ℓ²` cells); only the boolean 2×2 (D3) or a 1-dim contrast is testable there. **Separate, harder.**

## 5. What this bounds and what it opens

> ⚠ **CORRECTION 2026-07-25 (self-audit).** This section previously read **"Closes:"** and *"the `D=−3`
> bridge is **confirmed special to ℓ=2,3**"* — a **closure stated inside a file that grades itself
> `[VERIFIED — bounded]` (§3) under the headings "graded as a bound, not an absence" and "stated as
> bounds (not closures)" (§4).** The conclusion over-graded its own result: "special to ℓ=2,3" asserts
> a fact over **all** ℓ from an out-of-sample null at **ℓ=5,7,11,13** with this file's own **~3–6%
> copy-fraction power floor**. Corrected below. (Found by grep-comparing the file's grade tag against
> its conclusion sentence — see [[feedback_self_cert_words_audit_trigger]]; the self-cert word in this
> very section sat on a *true* clause four lines away, which is why the old clause-scoped litmus
> cleared it.)

**Bounds:** the specific blind spot D3 left open — "a uniform-correction bridge at ℓ≥5 could be hiding"
— is **bounded away at the tested ℓ and the achieved power** (M1 shows the statistic rejects that
synthetic case; the arms are null OOS). **No bridge past ℓ=3 was detected for `D=−3`** at ℓ=5,7,11,13,
by a statistic that would have caught a hidden analogue copying `≳3–6%` of instances. This does **not**
establish that the bridge is special to ℓ=2,3 as a fact over all ℓ: `ℓ≥17` is untested, and a weaker
bridge below the power floor is unexcluded.

**Opens (the next probes, per §4):** the **conditional** statistic `I(j;k | t,v,U)` — the one
alternative marginal MI cannot see; and the **ideal-level** symbol in `ℚ(ζ_ℓ)`, which is where the
general power-reciprocity law actually lives and which no rational-exponent test can reach.

## 6. Prior art / grade

Exploration, not a novelty claim (no gate tripped). The general power-reciprocity law is **classical**;
nothing here is claimed original. The contribution is a **measurement** with a **new, verified
instrument** (choice-free MI that defeats the 2×2's blind spot). Public data only; no leakage/ECDLP
content.
