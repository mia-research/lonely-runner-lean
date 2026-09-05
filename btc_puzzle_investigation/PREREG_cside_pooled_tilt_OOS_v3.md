# PREREG v3 — does the c-side inversion pooled negative tilt replicate out-of-sample?

**Date:** 2026-08-01. **FROZEN BEFORE DATA.** No `c(d)` value at any OOS prime has been computed when
this file is written. Everything used to build this spec is **structure-only** — curve orders, the
`μ₃`-orbit combinatorics, the negation and inversion maps — none of which touches `χ₂(y)`.

**Supersedes v2** (`SIGN-OFF WITHHELD`, defects D1–D4), which superseded v1 (`SIGN-OFF WITHHELD`,
defects M1–M4, F2–F5). Both are retained unmodified as the audit trail. Disposition tables: §10 (v1),
§11 (v2).

**Gate status:** _(stamped in §12 after the v3 `experiment-designer` call)_

---

## 0. The lead, and the correction that must travel with it

`RESULT_cside_nonalgebraic_correlation_v1.md` reported, on the inversion index map, a per-prime
family-wise NULL plus a **pooled negative tilt** (15/18 primes negative, raw Stouffer `z = −2.64`).

**That lead is weaker than reported, and this spec says so before testing it.** The v1 null (a free
permutation of orbit-value labels) **destroys a forced symmetry of the data** (§2.1), making it
under-dispersed by `√2`. Every per-prime `|z|` in the discovery result, and the pooled Stouffer `z`
built from them, is inflated by that factor. Verified two ways: theoretically,
`sd_surface/sd_free = 2√(L−F₊−F₋)/√(2(L−2)) = √2` to within 0.02% at these `L`; empirically,
`1.411 / 1.415 / 1.412` at three primes. Location differs by `≤ 2` against `sd ≈ 106–151` (`≈ 0.007`
in `z`), so a **flat `√2` rescaling is the correct correction**:

> pooled `z ≈ −2.64/√2 ≈ −1.87` (one-sided `p ≈ 0.03`); per-prime effect `δ ≈ −0.44`, not `−0.62`.

The "calibration-corrected `z ≈ −2.1`" in that document has no basis and is **withdrawn**: the `0.793`
calibration std was estimated from 18 draws (se ≈ 0.17, consistent with 1.0) on data that also lacked
the forced symmetry, and was applied in the shrinking direction with an inverted rationale.
`RESULT_...v1.md` will carry a correction note referencing this file. **The lead survives as a lead** —
it is a `p ≈ 0.03` discovery-sample observation, not a `p ≈ 0.004` one.

The pre-committed question is unchanged:

> **Does the negative tilt reproduce on primes that were never looked at?**

Direction (**negative**) is fixed by the discovery sample, hence pre-committed **one-sided**. The
discovery primes take no part in the decision (§4).

## 1. Object and scope — no key set, no generator, no PRNG

**Object:** `c(d) = χ₂(y_{[d]G})` on `E : y² = x³ + 7` over `F_p`, `p ≡ 7 (mod 12)`, `n = #E(F_p)`
prime, correlated along the **non-algebraic** index map `f(d) = d⁻¹ mod n` — the index family the Weil
closure (`ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2) does not cover, `d ↦ d⁻¹` not being
induced by a curve endomorphism.

**Not in scope:** the 82 solved keys, any generator pool, any PRNG question. Any conclusion is bounded
to `p ∈ [1.7×10⁴, 5.3×10⁴]`, free-unit counts `M ∈ [1425, 4352]`, this one index map. It says nothing
about `2^{256}`, and nothing about the shortscalar regime (§8).

**What the statistic actually aggregates (stated up front, not discovered later).** Because each `μ₃`
orbit has 3 elements contributing equally, `3T = Σ_d c(d)c(d⁻¹)`, and by multiplicative Fourier
inversion on `(Z/n)^×`,

> `3T = (n−1)·Σ_χ ĉ(χ)²`  — note `ĉ(χ)²`, **not** `|ĉ(χ)|².`

So `T` is not a pure "inversion channel" statistic: it aggregates every character-space concentration
of `c`. Oddness forces `ĉ(χ) = 0` for even `χ`, and the real character `χ₂^{(n)}` is odd exactly when
`n ≡ 3 (mod 4)`, in which case it contributes `(n−1)ĉ(χ₂)² ≥ 0` with a **forced non-negative sign**
(confirmed: `ĉ(χ₂) = 0` at `n = 37, 61`; `≠ 0` at `n = 31, 43, 67`). This cuts in the tested
direction's favour — a Legendre-symbol-of-index effect can only push `T` **positive**, so it cannot
manufacture a negative tilt, only mask one — but the two channels are separable at zero cost, so §5
pre-commits to reporting `B_tot` **stratified by `n mod 4`** (the OOS set splits 45/45).

## 2. The forced structure, and the null it dictates

### 2.1 Two forced symmetries — one of which v1's null broke

- **GLV (used by v1):** `c(λd) = c(d)`, `λ³ = 1`. Free units are the `L = (n−1)/3` `μ₃`-orbits,
  `val[r] ∈ {±1}`.
- **Oddness (broken by v1):** `p ≡ 7 (mod 12) ⇒ p ≡ 3 (mod 4) ⇒ χ₂(−1) = −1`, and
  `y_{[−d]G} = −y_{[d]G}`, so `c(−d) = −c(d)` — exact, forced, universal. Negation descends to `ν` on
  orbits, a **fixed-point-free involution** (an orbit is `ν`-fixed only if `−1 ∈ μ₃`, impossible since
  `2 ∤ 3`). Hence `val[ν(r)] = −val[r]` identically: the data lives on a constraint surface of
  dimension `L/2`, not `L`.

**These two are the complete automorphism-induced structure:** for `j = 0` and `p ≡ 1 (mod 3)`,
`Aut(E) = μ₆ = ⟨μ₃, −1⟩` exactly. `Σ_d c(d) = 0` is implied by oddness, and `n` an odd prime forces no
2-torsion, so `c` never vanishes on `(Z/n)^×`. No third forced constraint exists at this level —
which is an argument, not a guarantee, and is why §6 adds **C-MATCH**, a control that can fire on the
real data if an *unknown* one does exist.

### 2.2 The null is not simulated — it is exact in closed form

`ν` and `fidx` (inversion on orbits) are commuting involutions (verified at `n = 10861, 11257, 17107,
18097`). With `t(r) = val[r]·val[fidx[r]]`: `t(ν r) = t(r)` and `t(fidx r) = t(r)`, so `t` is constant
on `⟨ν, fidx⟩`-orbits. Three kinds occur:

| kind | condition | count | contribution to `T` |
|---|---|---|---|
| `fidx`-fixed | `d² ∈ μ₃` | `F₊ = 2` always | `+1` each, **deterministic** |
| `fidx`-anti-fixed | `d² ∈ −μ₃` | `F₋ = 2` iff `n ≡ 1 (mod 4)`, else `0` | `−1` each, **deterministic** |
| generic | — | `4M`, `M = (L − F₊ − F₋)/4` | `4·s_j`, `s_j = ε_{j₁}·ε_{j₂}` |

`fidx` descends to an involution on the `L/2` `ν`-pairs whose fixed points are exactly the
`(F₊+F₋)/2` special pairs; **after removing them it is fixed-point-free, giving a genuine perfect
matching into `M` disjoint pairs-of-pairs** (verified: `generic ν-pairs = 2M`, matching involutive,
0 fixed points, exactly `M` distinct 2-cycles, no pair reused). The `M` products `s_j` are therefore
products over **disjoint** pairs of free signs — i.i.d. uniform `±1` under H₀. Exactly:

> `T = (F₊ − F₋) + 4(2B − M)`, `B ~ Binomial(M, ½)` — **an exact null law, no Monte Carlo.**

Verified: `4M + F₊ + F₋ = L` exactly; `T − (F₊−F₋) + 4M ≡ 0 (mod 8)` on every draw; empirical null sd
matches `4√M = 2√L` to 1%; and the **tails** match — `χ²(19 df) = 25.4 / 10.4 / 15.2` over 20
equiprobable bins at three OOS primes (20,000 draws each), with left-tail agreement at
`α = 0.05/0.01/0.005/0.001` (e.g. exact `0.01134` vs empirical `0.01070`). This replaces v1's ranks,
tie-breaks and convolution outright.

### 2.3 Statistic (FROZEN) — integers only, end to end

Per prime, the sufficient statistic is the integer count

> `B(p) = #{ j : s_j = +1 } = (T(p) − F₊ + F₋ + 4M)/8`

Pooled over the decision set: `B_tot = Σ_p B(p)`, `N = Σ_p M(p)`. Under H₀ and the independence
assumption of §4.1, **exactly** `B_tot ~ Binomial(N, ½)`. The negative-tilt alternative is
`q := Pr[s_j = +1] = ½ − ε/2`, i.e. `B_tot` small. One-sided exact p-value:

> `p_OOS = 2^{−N} Σ_{k ≤ B_tot} C(N, k)` — an **exact rational**, computed in Python `int`.

The binomial family has monotone likelihood ratio in `B_tot`, so this one-sided test is **UMP** against
that single-parameter alternative. Decisions are integer cross-products, never a float division of the
rational. No float appears in the signal path or the decision path.

## 3. Alternative and power (computed pre-data, exactly, under BOTH live scalings)

**Mapping the discovery effect.** Corrected, `δ ≈ −0.44` in units of the true null sd `4√M`; since a
bias `ε` gives `E[T] − T₀ = 4εM` and sd `4√M`, `δ = ε√M`. The **18 IS primes have
`M ∈ [904, 1317]`, mean `1117.2`** (v2 wrongly used `M ≈ 1400`, an OOS value — corrected here), so

> **`ε ≈ 0.44/√1117.2 ≈ 0.01316`.**

**Two scalings are live and §8 names both**, so power is quoted for both rather than only the
favourable one:

- **constant-`ε`** (a genuine per-free-unit channel): non-centrality `ε√N`.
- **constant-`δ`** (a fixed-size artefact of the orbit construction): non-centrality `δ·Σ_p√M_p/√N`.

**Sample (§4): `m = 90` OOS primes, `N = 252{,}117`; drop-one arm `m = 75`, `N = 210{,}683`.**

| arm | `N` | power at `ε = 0.01316` | power at `δ = 0.44` | min `ε` at 90% power |
|---|---|---|---|---|
| A-PRIMARY (90) | 252,117 | **1.000** | **0.964** | 0.00719 |
| A-DROP (75) | 210,683 | **0.9999** | **0.925** | 0.00786 |

The binding case is A-DROP under constant-`δ`: **92.5%**. (v2's `m = 70` gave `0.847` there — below
90% — which is why the sample is 90.) Power is validated empirically by **C-PLANT-CAL** (§6) rather
than asserted.

## 4. Sample (FROZEN) — disjoint by construction, dependence structure enumerated

Enumeration: `p ≡ 7 (mod 12)`, `p` prime, `n = #E(F_p)` prime, in increasing order from `p = 10831`.

- **IS (discovery), 18 primes, `10831 … 15919`** — re-run under the corrected null for **reproduction
  only. No vote.**
- **OOS (decision), 90 primes, `16879 … 52291`, `N = 252{,}117`, `M ∈ [1425, 4352]`** — never
  evaluated. Sole basis of §5.

### 4.1 Independence — an explicit ASSUMPTION, not something the enumeration discharges

All the power of this design comes from pooling `m = 90` primes into one `Binomial(N, ½)`. That step
**assumes** the `B(p)` are jointly independent. Enumerating order-graph links removes *known*
dependence mechanisms; it does not establish independence, and this spec does not claim it does. The
mechanisms actually checked, exhaustively, over the directed graph `p → n(p)` restricted to IS ∪ OOS:

- **Amicable 2-cycles** (`#E(F_p) = q`, `#E(F_q) = p`): **13 inside OOS** — `(19471,19483)`,
  `(21163,21247)`, `(21739,22003)`, `(22807,23059)`, `(25447,25603)`, `(30391,30703)`,
  `(32503,32839)`, `(34267,34603)`, `(38431,38791)`, `(39043,39439)`, `(44563,44647)`,
  `(46279,46351)`, `(46327,46747)`. (2 inside IS: `(12919,13147)`, `(13567,13759)`.)
- **Anomalous curves**, `n(p) = p` (trace 1, `E(F_p) ≅ Z/p`): **`p = 24571` and `p = 50311`**, both
  inside OOS. Self-links, invisible to a mutual-2-cycle filter, and not exchangeable with the rest —
  the group carries a canonical additive `p`-adic structure the others lack.
- **One-way links, longer cycles, IS↔OOS crossings: none.**

Any residual dependence not of these forms is an **unquantified assumption**, stated here as a limit
on every conclusion in §5 and §7.

### 4.2 Three arms, all fixed now

| arm | membership | role |
|---|---|---|
| **A-PRIMARY** | all 90 | decision |
| **A-DROP** | 75: drop the **larger** member of each of the 13 OOS amicable pairs, and drop `24571`, `50311` | decision — **must agree with A-PRIMARY** |
| **A-ANOM** | `{24571, 50311}` | reported as labelled single cells, never pooled |

Dropping the larger member is fixed by the enumeration, applied uniformly to all 13 pairs, and chosen
before any statistic — no selection effect on the `c`-side. A FIRE or NULL verdict requires
**A-PRIMARY and A-DROP to agree**; disagreement ⇒ INDETERMINATE (F-SPLIT).

## 5. Decision rule (PRE-COMMITTED, one-sided negative, OOS only)

Conditional on §6's controls behaving:

| condition (both A-PRIMARY and A-DROP) | verdict |
|---|---|
| `p_OOS ≤ 0.01` | **REPLICATES.** A real small negative correlation of `c` along inversion at this scale. Grade `[EMPIRICAL — replicated OOS]`, with `ε̂` and its CI. **Not** a leak claim — a characterisation. |
| `Pr[B_tot ≥ b_obs] ≤ 0.01` | **SIGN REVERSAL.** Headlined over DOES-NOT-REPLICATE whenever both hold (they are not exclusive: an opposite-tail `p ≤ 0.01` forces `p_OOS ≥ 0.99 ≥ 0.10`). Reported `[EXPLORATORY]`, **no grade movement.** |
| `p_OOS ≥ 0.10` and no sign reversal | **DOES NOT REPLICATE.** The discovery tilt is graded a draw. Reported as a **scoped null carrying an explicit upper confidence bound on `ε`** (§7), naming object, class, power, scope. |
| `0.01 < p_OOS < 0.10` | **INDETERMINATE.** Report the number. No verdict, no grade movement. |

**Secondary, reported, non-deciding, none may move a grade:** (i) `B_tot` **stratified by `n mod 4`**
(45/45 split), per §1's character-sum decomposition; (ii) the equal-weight exact **sign test** across
the 90 primes, guarding the constant-`δ` alternative; (iii) the IS reproduction under the corrected
null; (iv) the combined 108-prime pooled count; (v) per-prime Bonferroni scan at `α = 0.05/90`;
(vi) the power maps `pow5/7/11/13` where `gcd(k, n−1) = 1`, Bonferroni over 4 — **the script must
derive the `⟨ν, f⟩`-orbit census separately for each map and must not assume the exact binomial law
carries over**, since a non-involutive `f` changes the census and hence the null.

## 6. Controls — all must behave before any arm is read

| id | control | requirement |
|---|---|---|
| **C-ODD** | assert `val[ν(r)] = −val[r]` on the **real data**, every orbit, every prime | **0 deviations.** This is a mathematically forced identity (`χ₂(−1) = −1`, `y(−P) = −y(P)`), so any failure is a **code fault**, not a property of a prime ⇒ **global F-BROKEN**, no verdict. It is *not* a void condition. |
| **C-FORCED** | `ν` fixed-point-free involution; `fidx` involution; `ν∘fidx = fidx∘ν`; `4M + F₊ + F₋ = L`; `F₊ = 2`; `F₋ = 2·[n ≡ 1 mod 4]`; `T − (F₊−F₋) + 4M ≡ 0 (mod 8)` | asserted and printed at every prime. **This is the only void condition** (§6.1). |
| **C-MATCH** (real-data null adequacy) | recompute the whole pooled pipeline on the **real** `val`, with `fidx` replaced by each of **200 independent random `ν`-commuting fixed-point-free involutions** on the `ν`-pairs | the 200 pooled exact p-values must be uniform: fire rate at `α = 0.01` within `[0.001, 0.035]`, and a KS test against `U(0,1)` not rejecting at `α = 0.01`. **This is the only control that can fire on real data**, and it would have caught v1's defect (the `√2` over-dispersion shows up directly in the p-value spread). Failure ⇒ **F-BROKEN**: the null is inadequate for reasons beyond the two forced symmetries. |
| **C-PLANT-STRONG** (wiring) | `s` drawn with `ε = 0.5`, planted **directly on the free units** — not by overwriting `val`, which is what made v1's plant realise 98.1% against a nominal 80% (`fidx` is an involution, so writes clobber) | `p < 10⁻⁶` at every prime |
| **C-PLANT-CAL** (power) | 200 independent draws at **`ε = 0.01316`** — the corrected discovery effect size — through the whole pooled pipeline | pooled test must fire at `α = 0.01` on **≥ 95%** of draws (§3 claims ≈100% under constant-`ε`). A shortfall means the **power claim** is wrong, not the data. |
| **C-CAL** (arithmetic calibration) | 200 draws of `s` uniform on the free units (`ε = 0`) | pooled `p` uniform; fire rate at `α = 0.01` within `[0.001, 0.035]`. **Scope stated honestly:** C-CAL draws from the *assumed* null, so it validates the arithmetic of the exact p-value, **not** the null's adequacy. C-MATCH is what covers adequacy. |
| **C-EXACT** | integer/rational only in signal and decision path; `check_no_float.sh` passes | asserted |

### 6.1 Voids (pre-committed)

A prime is void **iff C-FORCED fails there** — and only then. Voids change `N`, and `N` enters both
the null law and the power; the exact binomial runs at the **realised** `N`, which is printed.
**More than 3 voids ⇒ F-BROKEN, no verdict in either direction**, so the number of primes entering the
decision is not a free parameter fixed after the run.

## 7. What a null may and may not claim

If `p_OOS ≥ 0.10` with no sign reversal, the reported result is **not** "the tilt was a draw, avenue
closed." It is a bound computed **from the observed count**:

- the **99% one-sided Clopper–Pearson lower limit `q_L`** on `q = Pr[s_j = +1]`, reported as
  **`ε_U = 1 − 2q_L`**, computed on **A-PRIMARY**, with the A-DROP value reported alongside;
- if `B_tot > N/2` then `ε_U ≤ 0` and that is what is printed — a bound consistent with no negative
  effect, stated as such rather than truncated to 0 silently;
- **`ε_U` bounds `ε` under the constant-`ε` parametrisation and does NOT bound `δ`.** The
  corresponding constant-`δ` bound is reported separately. Equating the two alternatives' shifts in
  `E[B_tot]` — `εN = δ·Σ_p√M_p` — gives **`δ_U = ε_U·N / Σ_p√M_p`**, computed from the same count.

A non-rejection is not a bound; the bound must come from the data, not from recycling the `α = 0.01`
detection threshold. Every bound is further conditioned on §4.1's independence assumption. And the
CDH/inversion **avenue** is not closed by any outcome here: the shortscalar arm at the `2^{128}` scale
(`STRUCTURAL_IMPLICATIONS §5.4`) is a different regime this test cannot reach and remains open.

## 8. Falsification / readings (PRE-COMMITTED)

- **F-REPLICATE.** `p_OOS ≤ 0.01` on both arms ⇒ a real sub-per-prime-detection negative correlation.
  The next question is not a claim but the scaling one: is `ε` constant in `M` (a genuine channel) or
  is `δ = ε√M` constant (a fixed-size artefact of the orbit construction)? The 90 primes span
  `M ∈ [1425, 4352]`, a 3.05× range, enough to separate these by regression of `δ̂_p` on `√M_p` —
  pre-committed as the immediate follow-up, reported `[EXPLORATORY]`.
- **F-NULL.** `p_OOS ≥ 0.10` ⇒ §7's scoped bounds. Avenue not closed.
- **F-BROKEN.** C-ODD failing, C-MATCH non-uniform, C-CAL extreme, C-PLANT-CAL under 95%, or > 3
  C-FORCED voids ⇒ instrument reported broken, **no verdict on the data in either direction.**
- **F-SPLIT.** A-PRIMARY and A-DROP disagree ⇒ the amicable coupling carries the pooled signal. A
  finding about the pair structure, reported as such — and it retro-flags the discovery tilt, which
  contained 2 such pairs in 18.
- **F-ANOM.** `24571` and `50311` are reported as labelled single cells regardless of outcome, never
  pooled, never used to move the verdict.

## 9. Files

- Script (written after sign-off): `cside_pooled_tilt_oos_v3.py`
- Predecessors: `cside_orbitlevel_v1.py`; `RESULT_cside_nonalgebraic_correlation_v1.md` (to carry the
  §0 correction); `PREREG_cside_pooled_tilt_OOS_v1.md`, `..._v2.md` (withheld; audit trail)

## 10. Disposition of the v1 withheld layers (M1–M4, F2–F5)

| layer | v1 defect | fix |
|---|---|---|
| **M1** | rank formula was the anti-conservative rank, contradicting its own uniformity claim | **dissolved** — no ranks. Sufficient statistic `B(p)`, exact binomial null (§2.2–2.3) |
| **M2** | convolution needed unstated joint independence | **dissolved** — one exact `Binomial(N, ½)`; independence now stated as an explicit assumption (§4.1) |
| **M3** | power omitted data-side variance; true power 0.43–0.53, not 0.92 | recomputed exactly, both scalings, sample raised to 90 (§3) |
| **M4** | plant realised 98.1% not 80% (`fidx` is an involution; writes clobber) | plant built directly on the free units, realised rate = nominal by construction (§6) |
| **F2** | free-permutation null destroys forced oddness; C-CAL structurally blind | exact law on the constraint surface (§2.2); C-ODD; C-MATCH; discovery `z` corrected in §0 |
| **F3** | null branch quoted wrong bounds, over-read a non-rejection | §7 exact CP bound from the data; avenue explicitly left open |
| **F4** | realised `m` not pre-committed; no opposite-tail cell | §6.1 void rule; §5 sign-reversal cell with headline precedence |
| **F5** | filter saw only mutual 2-cycles; missed `n(p) = p` | full order-graph enumeration (§4.1); both anomalous primes to **A-ANOM** |

## 11. Disposition of the v2 withheld layers (D1–D4)

| layer | v2 defect | fix |
|---|---|---|
| **D1** | `ε` derived from `M ≈ 1400` (an OOS value); IS primes have `M ∈ [904,1317]`, mean 1117.2. Power quoted only under constant-`ε`; under constant-`δ` the binding arm was 0.847 | `ε = 0.01316` (§3); power table carries **both** scalings; sample 70 → **90** so the binding arm is **0.925**; C-PLANT-CAL re-set to `ε = 0.01316`; §7 names the CP limit, the arm, the `B_tot > N/2` case, and that `ε_U` does not bound `δ` |
| **D2** | no control could fire on a mis-specified null from the **real-data** side — v1's instance removed, not its class | **C-MATCH** added (§6): 200 random `ν`-commuting fixed-point-free involutions on the real `val`, pre-committed uniformity band. Plus §1's character-sum identity `3T = (n−1)Σ_χ ĉ(χ)²` and pre-committed **`n mod 4` stratification**. §2.1 records that `Aut(E) = μ₆` exactly, so GLV + oddness is the complete automorphism-induced structure |
| **D3** | §10/M2 overstated what the enumeration delivers | §4.1 restates independence as an explicit **assumption**, naming the mechanisms actually checked and flagging the residual as unquantified |
| **D4** | C-ODD had two incompatible dispositions; sign-reversal and does-not-replicate could both fire; "DP" was a v1 leftover | C-ODD ⇒ **global F-BROKEN** only; voids reserved for C-FORCED (§6.1); §5 gives sign reversal headline precedence; "DP" removed |
| **caveat** | §5(v) assumed the pow-k maps reuse the same null law | §5(vi) requires the census be **derived per map**; non-involutive `f` changes it |

## 12. Gate

`experiment-designer` sign-off on this spec before the script is run. If the gate is **UNAVAILABLE**
(infrastructure), CLAUDE.md §2a applies: the run proceeds tagged
`[PROVISIONAL — experiment-designer unavailable]` in the grade slot, with a self-audit naming its
uncovered **frame** layers, the gate recorded as owed, and **no grade promotion** until it clears. If
the gate **FAILS** (runs and finds a defect), the defect blocks — as it did at v1 and v2.
