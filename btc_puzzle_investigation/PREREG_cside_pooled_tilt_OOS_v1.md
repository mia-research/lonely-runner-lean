# PREREG — does the c-side inversion pooled negative tilt replicate out-of-sample?

**Date:** 2026-07-31. **FROZEN BEFORE DATA.** No OOS prime has been evaluated when this file is
written. The only numbers in hand are the discovery-sample numbers already published in
`RESULT_cside_nonalgebraic_correlation_v1.md` (18 primes, `p = 10831…15919`).

**Gate status:** _(to be stamped after the `experiment-designer` call — see §8)_

---

## 0. The lead being tested (stated, so the test cannot be re-aimed after the fact)

`RESULT_cside_nonalgebraic_correlation_v1.md` reports, on the inversion index map:

- **family-wise NULL** per prime (max |z| = 2.39, 0 cells clear Bonferroni), and
- a **pooled negative tilt**: 15 of 18 primes negative, raw Stouffer `z = −2.64`, which **survived a
  null-calibration control** (pure-random orbit values give pooled `z = +1.02`, so the null does not
  manufacture the sign). Calibration std `0.793` ⇒ the raw z's are mildly inflated; corrected pooled
  `z ≈ −2.1`.

That is a **discovery-sample** observation. This prereg asks one question and pre-commits its answer:

> **Does the negative tilt reproduce on primes that were never looked at?**

The direction (**negative**) is fixed by the discovery sample and is therefore **pre-committed
one-sided** here. The discovery primes take no part in the decision (§3).

## 1. Object and scope — no key set, no generator, no PRNG

**Object:** the map `c(d) = χ₂(y_{[d]G})` on `E : y² = x³ + 7` over `F_p` for `p ≡ 7 (mod 12)` with
`n = #E(F_p)` prime, and its correlation along the **non-algebraic** index map `f(d) = d⁻¹ mod n`.

This is the CDH/inversion channel — the one index family the Weil closure
(`ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2) does **not** cover, because `d ↦ d⁻¹` is not
induced by a curve endomorphism.

**Not in scope:** the 82 solved puzzle keys, any generator pool, any PRNG question. The object is
curve arithmetic at small `p`. Scope of any conclusion is bounded to `p ∼ 10⁴`, orbit counts
`5.7×10³ – 8.8×10³`, this one index map. It says nothing about `2^{256}`.

## 2. Statistic (FROZEN) — integer throughout, no float in the decision path

**Reduction (already verified, re-asserted as control C-FORCED below):** `c` is exactly constant on
each `μ₃` orbit (GLV invariance `c(λd) = c(d)`, forced), and `inv` maps orbits to orbits. Free units =
the `L = (n−1)/3` orbits; `val[r] ∈ {−1,+1}` is `c` on orbit `r`; `fidx[r]` is the orbit `inv` sends
`r` to.

**Per-prime statistic — an exact integer:**

> `T(p) = Σ_{r=0}^{L−1} val[r] · val[fidx[r]] ∈ ℤ`

(The v1 script used the *mean* `T/L`; the sum is the same statistic and is exactly representable.
Every comparison below is an integer comparison. This is a deliberate upgrade over v1: **the
z-inflation problem is not corrected, it is removed** — no mean, no standard deviation, no Stouffer
z appears anywhere in the decision path.)

**Per-prime rank (exact integer):** with `R = 4000` null draws `T⁽¹⁾…T⁽ᴿ⁾`,

> `r(p) = #{ i : T⁽ⁱ⁾ < T(p) } + U(p)`, where `U(p) = #{ i : T⁽ⁱ⁾ = T(p) }` ties broken by a
> **randomised** integer draw (seed = `p`, recorded), which makes `r(p)` exactly uniform on
> `{0,…,R}` under H₀. The **conservative** (`U` counted as 0) and **anti-conservative** (`U` counted
> in full) ranks are both reported alongside; if the three disagree on the verdict, the verdict is
> INDETERMINATE.

**Pooled statistic (exact integer):** `S = Σ_{p ∈ OOS} r(p)`. A negative tilt drives `T(p)` low,
hence `r(p)` low, hence `S` low.

**Pooled p-value (EXACT, no simulation, no normal approximation):** under H₀ the `r(p)` are i.i.d.
uniform on `{0,…,R}`, so the null law of `S` is the `m`-fold discrete convolution of that uniform.
It is computed by exact integer dynamic programming (Python `int`, no float), giving

> `p_OOS = Pr[S ≤ S_obs]` as an **exact rational** `A / (R+1)^m`.

## 3. Sample (FROZEN) — the OOS set is disjoint from the discovery set by construction

Primes are enumerated in increasing order: `p ≡ 7 (mod 12)`, `p` prime, `n = #E(F_p)` prime.

- **Discovery / in-sample (IS), 18 primes:** `10831 … 15919`. **Re-run for reproduction only. It has
  no vote in the decision.**
- **OOS decision set, 30 primes:** the next 30 in the enumeration, `16879 … 26083` (orbit counts
  5702 – 8802). **These have never been evaluated.** They are the sole basis of the §5 verdict.

**Independence caveat, pre-registered (found while enumerating, before any statistic was computed):**
the enumeration contains **amicable pairs** — `#E(F_p) = q` and `#E(F_q) = p`. Inside the OOS set:
`(19471,19483)`, `(21163,21247)`, `(21739,22003)`, `(22807,23059)`, `(25447,25603)` — 5 pairs.
(The IS set contains 2: `(12919,13147)`, `(13567,13759)`.) These are not i.i.d. draws under any
hypothesis that relates the two curves. Therefore:

> **The primary decision is computed twice** — (a) on all 30, and (b) on the 25 obtained by dropping
> the *larger* member of each amicable pair. **Both must agree** for a FIRE or a NULL verdict; if
> they disagree the verdict is INDETERMINATE and the disagreement is itself the reported finding.

## 4. Controls — all must behave before any arm is read

| id | control | requirement |
|---|---|---|
| **C-PLANT** (firing) | fresh orbit-value assignment, drawn **independently of `c`**, with 80% of orbits forced to agree with their `inv`-image | must land at rank `≤ 0.01R` or `≥ 0.99R` at **every** prime. A prime where it fails is **void** and is dropped (and the drop is reported). |
| **C-CAL** (calibration) | the **entire pipeline** — same primes, same `fidx`, same null, same pooled DP — run on orbit values drawn uniformly at random (`E[T] = 0` by construction) | `p_OOS` on the calibration data must be **non-extreme** (`0.05 < p < 0.95`). If it is extreme, the instrument manufactures the sign and **every arm is void**. This is the control that made the v1 lead credible; it is re-run at the new scale, not assumed. |
| **C-FORCED** | `c` constant on all `μ₃` orbits (0 deviations); `fidx` a permutation of `{0..L−1}`; `T` an integer of the same parity as `L` | asserted at every prime, printed |
| **C-EXACT** | no float anywhere in signal path or decision path: curve order, `c`, orbits, `fidx`, `T`, ranks, `S`, `p_OOS` all integer/rational | asserted; `check_no_float.sh` must pass on the script |

## 5. Decision rule (PRE-COMMITTED, one-sided, negative direction)

On the **OOS set only**, with C-PLANT firing everywhere and C-CAL non-extreme:

| `p_OOS` (both the 30-prime and 25-prime computations) | verdict |
|---|---|
| `≤ 0.01` | **REPLICATES.** The negative tilt in the CDH/inversion channel is a real small effect at this scale. Grade `[EMPIRICAL — replicated OOS]`; report the effect size and its scope. **Not** a leak claim; a characterisation. |
| `≥ 0.10` | **DOES NOT REPLICATE.** The discovery tilt is graded a draw of the statistic. Report as a **scoped null with power stated** (§6) — object, class, power, scope, per the closure-grade bar. This does **not** close the CDH/inversion avenue; it closes *this statistic at this scale*. |
| `0.01 < p_OOS < 0.10` | **INDETERMINATE.** Report the number, no verdict, no grade movement. |

**Secondary, reported but not deciding:** (i) the pooled p on all 48 primes (IS+OOS); (ii) the
per-prime Bonferroni scan for any single cell clearing `α = 0.05/30`; (iii) the same pooled test for
the power maps `pow5/7/11/13` where `gcd(k, n−1) = 1`, Bonferroni over 4. These are **exploratory**;
none may move a grade.

## 6. Power (computed pre-data, from the null law alone)

The pooled rank test with `m = 30`, `R = 4000`, `α = 0.01`, one-sided:
`S` has null mean `mR/2` and sd `R·√(m/12)`. A per-prime standardised shift `z` in the underlying
statistic moves `E[r(p)]` by `≈ R(Φ(z) − ½) ≈ 0.399·R·z`, so detection at `α = 0.01` needs

> `0.399·m·z ≥ 2.326·√(m/12)` ⟹ `z ≥ 0.307` (for `m = 30`), and `z ≥ 0.336` for `m = 25`.

The discovery sample's per-prime mean was `z ≈ −0.62` raw, `≈ −0.49` after the calibration
correction. **Both exceed the detection threshold by a factor ≈ 1.5–2**, so this design has high
power against the effect actually claimed. Concretely, at `m = 30` the power against a true per-prime
`z = −0.49` is `Φ(0.399·30·0.49/(√(30/12)) − 2.326) = Φ(3.71 − 2.33) ≈ 0.92`.

**This is the sentence that makes a null informative:** if the tilt is real at the discovery-sample
magnitude, this test finds it ~9 times out of 10. If `p_OOS ≥ 0.10`, the effect is bounded to
`|z| ≲ 0.3` per prime, i.e. `|T|/L ≲ 0.3/√L ≈ 0.004` — an order of magnitude below the discovery
claim and two below the per-prime detection floor. That is the scope any null here may claim, and no
more.

The claim is verified by direct simulation of the pooled DP null in the script (uses no data).

## 7. Falsification / readings (PRE-COMMITTED)

- **F-REPLICATE.** `p_OOS ≤ 0.01` on both computations ⇒ a real, sub-per-prime-detection negative
  correlation of `c` along inversion. Next step is *not* a claim: it is the scale question — does
  `|z|` grow with `L`? (`z ∝ ε√L` with fixed `ε` vs. `z` flat.) That is what decides whether it is a
  fixed-size artefact of the orbit construction or a genuine channel.
- **F-NULL.** `p_OOS ≥ 0.10` ⇒ the tilt was a draw. The scoped null of §6 is the result. The
  CDH/inversion avenue is **not** closed by it — the shortscalar arm at the `2^128` scale
  (`STRUCTURAL_IMPLICATIONS §5.4`) is a different regime this test cannot reach, and remains open.
- **F-BROKEN.** C-CAL extreme, or C-PLANT failing widely ⇒ the instrument is reported as broken and
  **no** verdict is issued on the data, in either direction.
- **F-SPLIT.** The 30-prime and 25-prime computations disagree ⇒ the amicable-pair coupling is
  carrying the pooled signal. That is a *finding about the pair structure*, reported as such, and it
  retro-flags the v1 discovery tilt (which contained 2 such pairs in 18).

## 8. Gate

`experiment-designer` sign-off is requested on this spec before the script is run. If the gate is
**UNAVAILABLE** (infrastructure), CLAUDE.md §2a applies: the run proceeds tagged
`[PROVISIONAL — experiment-designer unavailable]` in the grade slot, with a self-audit naming its
uncovered **frame** layers (object/disjointness, matched-control adequacy, scope, falsification,
pre-commitment — the layers a self-audit cannot discharge), the gate recorded as owed, and **no grade
promotion** until it clears. If the gate **FAILS** (runs and finds a defect), the defect blocks.

## 9. Files

- Script (to be written after sign-off): `cside_pooled_tilt_oos_v1.py`
- Predecessor: `cside_orbitlevel_v1.py`, `RESULT_cside_nonalgebraic_correlation_v1.md`
