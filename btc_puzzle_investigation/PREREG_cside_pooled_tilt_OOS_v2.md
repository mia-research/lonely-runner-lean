# PREREG v2 — does the c-side inversion pooled negative tilt replicate out-of-sample?

**Date:** 2026-07-31. **FROZEN BEFORE DATA.** No `c(d)` value at any OOS prime has been computed when
this file is written. Everything used to build this spec is **structure-only** — curve orders, the
`μ₃`-orbit combinatorics, the negation and inversion maps — none of which touches `χ₂(y)`.

**Supersedes `PREREG_cside_pooled_tilt_OOS_v1.md`**, which received **SIGN-OFF WITHHELD** from
`experiment-designer` on 8 layers (M1–M4, F2–F5). v1 is retained unmodified as the audit trail. Every
withheld layer is addressed below and the fix is named in §10.

**Gate status:** _(stamped in §10 after the v2 `experiment-designer` call)_

---

## 0. The lead, and the correction that must travel with it

`RESULT_cside_nonalgebraic_correlation_v1.md` reported, on the inversion index map, a per-prime
family-wise NULL plus a **pooled negative tilt** (15/18 primes negative, raw Stouffer `z = −2.64`).

**That lead is weaker than reported, and this spec says so before testing it.** The v1 null (a free
permutation of orbit-value labels) **destroys a forced symmetry of the data** (§2.1), which makes it
under-dispersed by a factor `√2`. Every per-prime `|z|` in the discovery result — and the pooled
Stouffer `z` built from them — is inflated by that factor. The honest restatement of the discovery
sample is:

> pooled `z ≈ −2.64/1.41 ≈ −1.87` (one-sided `p ≈ 0.03`), per-prime effect `δ ≈ −0.44`, not `−0.62`.

The "calibration-corrected `z ≈ −2.1`" in that document has no basis and is withdrawn here: the
`0.793` calibration std was estimated from 18 draws (se ≈ 0.17, consistent with 1.0) on data that
also lacked the forced symmetry, and was applied in the shrinking direction with an inverted
rationale. `RESULT_...v1.md` will carry a correction note referencing this file. **The lead survives
as a lead** — it is simply a `p ≈ 0.03` discovery-sample observation, not a `p ≈ 0.004` one.

The question this spec pre-commits an answer to is unchanged:

> **Does the negative tilt reproduce on primes that were never looked at?**

Direction (**negative**) is fixed by the discovery sample and is therefore pre-committed **one-sided**.
The discovery primes take no part in the decision (§4).

## 1. Object and scope — no key set, no generator, no PRNG

**Object:** `c(d) = χ₂(y_{[d]G})` on `E : y² = x³ + 7` over `F_p`, `p ≡ 7 (mod 12)`, `n = #E(F_p)`
prime, correlated along the **non-algebraic** index map `f(d) = d⁻¹ mod n`.

This is the CDH/inversion channel — the index family the Weil closure
(`ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2) does **not** cover, `d ↦ d⁻¹` not being
induced by a curve endomorphism.

**Not in scope:** the 82 solved keys, any generator pool, any PRNG question. Any conclusion is bounded
to `p ∈ [1.7×10⁴, 4.3×10⁴]`, free-unit counts `M ∈ [1.4×10³, 3.6×10³]`, this one index map. It says
nothing about `2^{256}`, and nothing about the shortscalar regime (§8).

## 2. The forced structure, and the null it dictates

### 2.1 Two forced symmetries — one of which v1's null broke

- **GLV (used by v1):** `c(λd) = c(d)`, `λ³ = 1`. Free units are the `L = (n−1)/3` `μ₃`-orbits, with
  `val[r] ∈ {±1}`.
- **Oddness (broken by v1):** `p ≡ 7 (mod 12) ⇒ p ≡ 3 (mod 4) ⇒ χ₂(−1) = −1`, and
  `y_{[−d]G} = −y_{[d]G}`, so `c(−d) = −c(d)` — **exact, forced, universal.** Negation descends to a
  map `ν` on orbits, and `ν` is a **fixed-point-free involution** (an orbit is `ν`-fixed only if
  `−1 ∈ μ₃`, impossible since `2 ∤ 3`). Hence `val[ν(r)] = −val[r]` identically: the data lives on a
  constraint surface of dimension `L/2`, not `L`.

v1's null (`rng.shuffle`) leaves that surface. Verified at `p = 16879, 17959, 18211`: null sd on the
surface `152.8 / 154.6 / 156.6` vs free-permutation sd `104.5 / 110.1 / 112.1`, ratio `1.46/1.40/1.40`
→ `√2`. **Direction matters and is stated honestly: the mismatch inflates dispersion, not location —
it does not manufacture a negative sign.** It inflates `|z|` symmetrically and makes a nominal
`α = 0.01` truly ≈ `0.024`.

### 2.2 The null is not simulated — it is exact in closed form

`ν` and `fidx` (inversion on orbits) are commuting involutions (verified: `fidx[fidx] = id`,
`ν[fidx] = fidx[ν]`, at all three primes). Write `t(r) = val[r]·val[fidx[r]]`; then `t(ν r) = t(r)`
and `t(fidx r) = t(r)`, so `t` is constant on `⟨ν, fidx⟩`-orbits. Three kinds occur:

| kind | condition | count | contribution to `T` |
|---|---|---|---|
| `fidx`-fixed | `d² ∈ μ₃` | `F₊ = 2` | `+1` each, **deterministic** |
| `fidx`-anti-fixed | `d² ∈ −μ₃` | `F₋ = 2` if `n ≡ 1 (4)`, else `0` | `−1` each, **deterministic** |
| generic | — | `4M`, `M = (L − F₊ − F₋)/4` | `4·s_j`, `s_j = ε_j₁·ε_j₂` |

`fidx` induces a **perfect matching** on the `L/2` `ν`-pairs, so the `M` products `s_j` are products
over **disjoint** pairs of the free signs — hence **i.i.d. uniform `±1` under H₀**. Therefore, exactly:

> `T = (F₊ − F₋) + 4(2B − M)`, `B ~ Binomial(M, ½)` — **an exact null law, no Monte Carlo.**

Verified: `4M + F₊ + F₋ = L` exactly, `(T − (F₊−F₋)) ≡ 0 (mod 4)` on every draw, and empirical null
sd matches `4√M = 2√L` to 1%. This replaces v1's ranks, tie-breaks and convolution outright — the
defects M1 and M2 are dissolved rather than patched.

### 2.3 Statistic (FROZEN) — integers only, end to end

Per prime: the sufficient statistic is the integer count

> `B(p) = #{ j : s_j = +1 } = (T(p) − F₊ + F₋ + 4M)/8`

Pooled across the decision set: `B_tot = Σ_p B(p)`, `N = Σ_p M(p)`. Under H₀, **exactly**
`B_tot ~ Binomial(N, ½)`. The negative-tilt alternative is `Pr[s_j = +1] = ½ − ε/2`, i.e. `B_tot`
small. One-sided exact p-value:

> `p_OOS = 2^{−N} Σ_{k ≤ B_tot} C(N, k)` — an **exact rational**, computed in Python `int`.

Decisions are integer cross-products (`2·A ≤ 2^{N}·α_num/α_den` style), never a float division of the
rational. No float appears in the signal path or the decision path.

## 3. Alternative and power (computed pre-data, exactly)

The alternative is one free parameter, `ε` = per-free-unit bias. It is the natural parametrisation
because `B_tot` is sufficient for it and the binomial test is **UMP** against it.

**Mapping the discovery effect into `ε`.** The v1 per-prime `z` was measured against the
under-dispersed null; corrected, `δ ≈ −0.44` in units of the true null sd `4√M`. Since a bias `ε`
gives `E[T] − T₀ = 4εM` and sd `4√M`, `δ = ε√M`. At the discovery primes (`M ≈ 1400`),
**`ε ≈ 0.44/37.4 ≈ 0.0117`**. That is the effect size this design must detect.

**Sample (see §4): `m = 70` OOS primes, `N = 172{,}326`; drop-one arm `m = 59`, `N = 146{,}513`.**

| arm | `N` | power at `ε = 0.0117`, `α = 0.01` | min `ε` detectable at 90% power |
|---|---|---|---|
| primary (70) | 172,326 | **0.994** | 0.00869 |
| drop-one (59) | 146,513 | **0.984** | 0.00943 |

The binding arm is the drop-one arm at **98.4%** power. (v1's design — 30 primes, and a power formula
that omitted the data-side sampling variance — had true power ≈ 0.43–0.53, which the gate correctly
computed. That is why the sample is 70 and not 30.) Power is quoted from
`Φ(ε√N − 2.3263)`; §6's C-PLANT-CAL validates it empirically at the claimed effect size rather than
asserting it.

## 4. Sample (FROZEN) — disjoint by construction, and its dependence structure enumerated

Enumeration: `p ≡ 7 (mod 12)`, `p` prime, `n = #E(F_p)` prime, in increasing order from `p = 10831`.

- **IS (discovery), 18 primes, `10831 … 15919`** — re-run under the corrected null for **reproduction
  only. No vote.**
- **OOS (decision), 70 primes, `16879 … 43003`, `N = 172{,}326`** — never evaluated. Sole basis of §5.

**Dependence structure, enumerated exhaustively over the directed order-graph `p → n(p)` restricted to
IS ∪ OOS** (the gate's F5; run before any statistic):

- **Amicable 2-cycles** (`#E(F_p) = q`, `#E(F_q) = p`): **exactly 10 inside OOS** — `(19471,19483)`,
  `(21163,21247)`, `(21739,22003)`, `(22807,23059)`, `(25447,25603)`, `(30391,30703)`,
  `(32503,32839)`, `(34267,34603)`, `(38431,38791)`, `(39043,39439)`. (2 inside IS:
  `(12919,13147)`, `(13567,13759)`; the next, `(44563,44647)`, falls outside.) These are not
  independent draws under any hypothesis relating the two curves. The list is fixed by the
  enumeration rule and re-derived by the script, not chosen.
- **Anomalous curve**, `n(p) = p` (trace 1, `E(F_p) ≅ Z/p`): **`p = 24571`**, inside OOS. It is a
  self-link in the order graph, invisible to a mutual-2-cycle filter, and it is not exchangeable with
  the rest — the group carries a canonical additive `p`-adic structure the others lack. (`p = 50311`
  is the next such prime and falls outside the sample.)
- **One-way links, longer cycles, IS↔OOS crossings: none** (verified over the full enumeration).

**Pre-committed handling — three arms, all fixed now:**

| arm | membership | role |
|---|---|---|
| **A-PRIMARY** | all 70 | decision |
| **A-DROP** | 59: drop the **larger** member of each OOS amicable pair, and drop `24571` | decision — **must agree with A-PRIMARY** |
| **A-ANOM** | `{24571}` alone | reported as a single labelled cell, never pooled |

A FIRE or a NULL verdict requires **A-PRIMARY and A-DROP to agree**. Disagreement ⇒ INDETERMINATE, and
the disagreement is itself the reported finding (F-SPLIT).

## 5. Decision rule (PRE-COMMITTED, one-sided negative, on OOS only)

Conditional on §6's controls behaving:

| `p_OOS` (both A-PRIMARY and A-DROP) | verdict |
|---|---|
| `≤ 0.01` | **REPLICATES.** A real small negative correlation of `c` along inversion at this scale. Grade `[EMPIRICAL — replicated OOS]`, with the effect size `ε̂` and its CI. **Not** a leak claim — a characterisation. |
| `≥ 0.10` | **DOES NOT REPLICATE.** The discovery tilt is graded a draw. Reported as a **scoped null carrying an explicit upper confidence bound on `ε`** (§7), naming object, class, power, scope. |
| `0.01 < p < 0.10` | **INDETERMINATE.** Report the number. No verdict, no grade movement. |
| `Pr[B_tot ≥ b_obs] ≤ 0.01` (opposite tail) | **SIGN REVERSAL.** Reported `[EXPLORATORY]`, no grade movement — the outcome space is not `{signal, nothing}`. |

**Secondary, reported, non-deciding:** (i) the equal-weight exact **sign test** across the 70 primes
(`Binomial(m, ½)` on `sign(T − E[T])`, exact, guarding the alternative "constant `z` per prime" rather
than "constant `ε`"); (ii) the IS reproduction under the corrected null; (iii) the combined 88-prime
pooled count; (iv) per-prime Bonferroni scan at `α = 0.05/70`; (v) the same pooled test for the power
maps `pow5/7/11/13` where `gcd(k, n−1) = 1`, Bonferroni over 4. **None may move a grade.**

## 6. Controls — all must behave before any arm is read

| id | control | requirement |
|---|---|---|
| **C-ODD** | assert `val[ν(r)] = −val[r]` on the **real data**, every orbit, every prime | **0 deviations.** This is the forced symmetry v1's null broke; here it is also a signal-path check. Any deviation ⇒ the signal path is wrong ⇒ F-BROKEN. |
| **C-FORCED** | `ν` a fixed-point-free involution; `fidx` an involution; `ν∘fidx = fidx∘ν`; `4M + F₊ + F₋ = L`; `F₊ = 2`; `F₋ = 2·[n ≡ 1 mod 4]`; `T ≡ F₊−F₋ (mod 4)` | asserted and printed at every prime |
| **C-PLANT-STRONG** (wiring) | `s` drawn with `ε = 0.5`, **planted directly on the free units** — not by overwriting `val`, which is what made v1's plant realise 98.1% instead of its nominal 80% (`fidx` is an involution, so writes clobber) | must give `p < 10⁻⁶` at every prime |
| **C-PLANT-CAL** (power) | 200 independent draws with `ε = 0.0117` — the discovery effect size — through the **whole pooled pipeline** | the pooled test must fire at `α = 0.01` on **≥ 95%** of draws (§3 claims 99.4%; a shortfall means the power claim, not the data, is wrong). This is the control that validates the power number; the strong plant validates only the wiring. |
| **C-CAL** (calibration) | 200 draws of `s` uniform on the free units (`ε = 0`) through the whole pooled pipeline | the pooled `p` must be uniform: the fire rate at `α = 0.01` must lie in `[0.001, 0.035]` (exact binomial 99% band for 200 draws). Fires ⇒ instrument manufactures the sign ⇒ **F-BROKEN, every arm void.** Note the v1 C-CAL could not have caught v1's defect: its calibration data also lacked oddness, so it was exchangeable under the wrong null by construction. Here it is drawn **on the constraint surface**. |
| **C-EXACT** | integer/rational only in signal and decision path; `check_no_float.sh` passes on the script | asserted |

**Voids (pre-committed, closing the gate's F4(i)):** a prime is void iff C-ODD or C-FORCED fails there.
Voids change `N`, and `N` enters both the null law and the power; the DP runs at the **realised** `N`,
which is printed. **More than 3 voids ⇒ F-BROKEN, no verdict in either direction** — so the number of
primes entering the decision is not a free parameter fixed after the run.

## 7. What a null may and may not claim (the gate's F3)

If `p_OOS ≥ 0.10`, the reported result is **not** "the tilt was a draw, avenue closed." It is:

> a one-sided upper confidence bound on `ε` computed **from the observed count** (Clopper–Pearson at
> 99%, exact), together with the object, the class of observable, the power (§3), and the scope (§1).

A non-rejection is not a bound; the bound must come from the data, not from recycling the `α = 0.01`
detection threshold. And the CDH/inversion **avenue** is not closed by any outcome here: the
shortscalar arm at the `2^{128}` scale (`STRUCTURAL_IMPLICATIONS §5.4`) is a different regime this
test cannot reach and remains open.

## 8. Falsification / readings (PRE-COMMITTED)

- **F-REPLICATE.** `p_OOS ≤ 0.01` on both arms ⇒ a real sub-per-prime-detection negative correlation.
  The next question is **not** a claim but the scaling one: is `ε` constant in `M` (a genuine channel)
  or is `δ = ε√M` constant (a fixed-size artefact of the orbit construction)? The 70 primes span
  `M ∈ [1.4k, 3.6k]`, enough to separate these by regression of `δ̂` on `√M` — pre-committed as the
  immediate follow-up, reported `[EXPLORATORY]`.
- **F-NULL.** `p_OOS ≥ 0.10` ⇒ §7's scoped bound. Avenue not closed.
- **F-BROKEN.** C-CAL extreme, C-PLANT-CAL under 95%, C-ODD failing, or > 3 voids ⇒ instrument
  reported broken, **no verdict on the data in either direction.**
- **F-SPLIT.** A-PRIMARY and A-DROP disagree ⇒ the amicable coupling carries the pooled signal. A
  finding about the pair structure, reported as such — and it retro-flags the discovery tilt, which
  contained 2 such pairs in 18.
- **F-ANOM.** A-ANOM (`p = 24571`) is reported as a labelled single cell regardless of outcome, never
  pooled, never used to move the verdict.

## 9. Files

- Script (written after sign-off): `cside_pooled_tilt_oos_v2.py`
- Predecessors: `cside_orbitlevel_v1.py`, `RESULT_cside_nonalgebraic_correlation_v1.md` (to carry the
  §0 correction), `PREREG_cside_pooled_tilt_OOS_v1.md` (withheld; audit trail)

## 10. Disposition of the v1 withheld layers

| layer | v1 defect | v2 fix |
|---|---|---|
| **M1** | rank formula was the anti-conservative rank, contradicting its own uniformity claim | **dissolved** — no ranks. Sufficient statistic `B(p)`, exact binomial null (§2.2–2.3) |
| **M2** | convolution needed unstated joint independence | **dissolved** — one exact `Binomial(N, ½)`. Independence across primes is still required and is now *enumerated* (§4) rather than assumed. Integer cross-product comparison pre-committed |
| **M3** | power omitted data-side variance (`0.399` vs `0.282·R·δ`); true power 0.43–0.53, not 0.92 | recomputed on the exact binomial in the `ε` parametrisation; sample raised 30 → 70 to reach **0.984** in the binding arm (§3), and validated by C-PLANT-CAL rather than asserted |
| **M4** | plant realised 98.1% not 80% (`fidx` is an involution; writes clobber) | plant built **directly on the free units** `s_j`, so the realised rate equals the nominal by construction; on the constraint surface; plus a second plant **at the discovery effect size** to validate power (§6) |
| **F2** | free-permutation null destroys forced oddness; under-dispersed by `√2`; C-CAL structurally blind to it | null replaced by the exact law on the constraint surface (§2.2); **C-ODD** added on the real data; C-CAL redrawn on the surface; the discovery result's inflated `z` corrected and withdrawn in §0 |
| **F3** | null branch quoted wrong bounds and over-read a non-rejection | §7: exact Clopper–Pearson bound **from the data**, avenue explicitly not closed |
| **F4** | realised `m` not pre-committed; no cell for the opposite tail | §6 void rule with a hard `>3 ⇒ F-BROKEN`; §5 sign-reversal cell |
| **F5** | filter saw only mutual 2-cycles; missed `n(p) = p` at `p = 24571` | full directed-order-graph enumeration (§4); `24571` pre-committed to its own arm **A-ANOM**; `50311` noted as outside the sample |
