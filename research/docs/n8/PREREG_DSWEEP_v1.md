# PREREG — D-sweep for unnamed runners (n = 8, threshold 1/8)

2026-09-13. Written **before any data**. Nothing had been run against it when it was written.
Pre-registration is mandatory before a sweep (`CLAUDE.md` §2); this is that gate for the
question *"when do the AP and grid readings fail, and does enlarging the reference step clear
the runners they miss."*

---

## 0. Reduction, and the ceiling that fell out of writing this

All three readings are one predicate at different `D`. With `u = p·(v_i − v_j) mod 8D`:

    clear(i, D)  ⟺  ∃ p ∈ {1,3,5,7} :  ∀ j ≠ i,   D ≤ ( p·(v_i − v_j) mod 8D ) ≤ 7D

because `‖x/(8D)‖ ≥ 1/8 ⟺ min(u, 8D−u) ≥ D ⟺ D ≤ u ≤ 7D`. Pure integer arithmetic — no
`Fraction`, no float. Reading A is `clear(i, g)`; Reading B is `clear(i, d_min(i))`.

> **Ceiling  `[PROVED]`.** If `D > 7·d_min(i)` then for every `p ∈ {1,3,5,7}` the nearest
> difference gives `u = p·d_min(i) < D`, so that `p` fails. Hence
>
>     the admissible steps are  A(i) = { D ∈ ℤ : 1 ≤ D ≤ 7·d_min(i) },   K(i) = 7·d_min(i)
>
> and the sweep over `D` is **exhaustive, not truncated**.

`[VERIFIED — 32,000 runner-instances]` no clearing `D` above `7·d_min`; the ratio
`(largest clearing D)/d_min` attains 7 exactly.

### Assertions that must pass before any statistic is computed

| ID | Assertion |
|---|---|
| A1 | The four `p` give **identical** Reading-A verdicts (`p` invertible mod 8, so `‖p·m/8‖ ≥ 1/8 ⟺ 8 ∤ m`). Any `p`-dependence in A is an implementation error. |
| A2 | Sweeping `D` to `20·d_min(i)` on 100 configurations yields no clearing `D > 7·d_min(i)`. |
| A3 | For `c ∈ {2,3,5}`, `S(c·v) ∩ cℤ = c·S(v)` exactly. |
| A4 | Every admitted case has `clear(i,g) = False` and `clear(i,d_min(i)) = False` — forced by the selection rule. |
| A5 | The planted control fires at the pre-set rate. |

## 1. Object

    S(i) = { D ∈ A(i) : clear(i, D) }        D*(i) = min S(i)   (∅ if S(i) = ∅)

for a runner named by **neither** reading. Hypothesis: `D*(i)` is a function of low-dimensional
scalar functionals of the configuration.

**Two hazards, both load-bearing.**
1. **The gap vector is the object.** The sorted gap vector determines the configuration up to
   translation, so predicting `D*` from "the gaps" predicts the object from itself. Only
   *scalar* functionals are admissible predictors.
2. **Selection forces two predictors to zero.** The population is defined by A and B failing, so
   `D = g` and `D = d_min(i)` have structurally zero hit rate. Both are logged FORCED, excluded
   from the predictor family and from every correction.

The control must therefore be drawn **under the same selection**.

## 2. Statistic

**Primary, fixed now.** `Q23(c) = { ⌊span/7⌋, ⌈span/7⌉ }`, a set predictor of declared
cardinality ≤ 2 (the floor/ceil pair is committed as a set so the choice cannot be made after
seeing data).

    H = # { cases c : D*(c) ∈ Q23(c) },   restricted to c with Q23(c) ∩ A(c) ≠ ∅

One-sided Fisher exact against the §3 surrogate, α = 0.01. Cases failing the admissibility
restriction are forced misses, reported separately, never pooled. One case per configuration —
the unnamed runner of smallest index; `#unnamed` recorded as a covariate.

**Recorded, never substituted:** `D*` and the full `S`; `1[S ≠ ∅]`; `K = 7·d_min(i)`; `|S|`; the
clearing `p`.

**Secondary family, K = 8, Holm at family α = 0.05, fixed now in this order:**
`Q1 span`, `Q2 ⌊span/7⌋`, `Q3 ⌈span/7⌉`, `Q4 max_j |v_i − v_j|`, `Q5 second-smallest difference`,
`Q6 gcd_j |v_i − v_j|`, `Q7 min gap`, `Q8 max gap`. Forced ledger: `F1 D = g`, `F2 D = d_min(i)`.
No predictor may be added after the run.

**Characterisation block** (recorded always, explicitly non-inferential, no p-values): multiset of
`D*`, `D*/g`, `D*/d_min(i)`, `7D*/span`; `D* mod m` for `m ∈ {2,3,4,5,7,8}`; `gcd(D*, g)`,
`gcd(D*, d_min)`, `gcd(D*, span)`; whether `D* | span`; whether `S` is an interval or scattered;
`|S|/K`; the clearing-`p` distribution. Anything interesting here licenses **one** thing: a new
pre-registration.

**Two arms, both fixed now.** PRIMARY (raw): `D` over all of `A(i)`. SECONDARY: `D ∈ A(i) ∩ gℤ`.
The raw arm is not scale-covariant; that is the small-denominator hazard and it is measured, not
assumed. The secondary arm may never be swapped in for the primary after seeing results.

## 3. Matched control

**C1 — budget-and-predictor-matched surrogate (the primary null).** For each real case, `R = 20`
surrogates redrawing the other six speeds subject to: 8 integer speeds; same `span` (so `Q23` is
identical); same `d_min(i)` (so `K`, the search budget, is identical); same `g`; and `i'` unnamed
by both readings. Rejection cap `10^4`; unfillable cases excluded and counted.
Preserves the number of `D` tried, so *"more `D` tried = more chances to clear"* is held exactly
fixed. Destroys only the interior arrangement.

**C2 — budget-inflation curve.** Clearing-existence rate under truncation to `D ≤ m`,
`m ∈ {5,10,25,50,100} ∩ [1,K]`, real and surrogate.

**C3 — resolution control.** (a) Scale replication `c ∈ {2,3,5}`: fraction with
`D*(c·v) ≠ c·D*(v)` in the raw arm; exact equality asserted in the g-multiple arm.
(b) `K`-stratification `K < 10`, `10 ≤ K < 100`, `K ≥ 100` — a result present only in `K < 10` is
a coarse-resolution effect and may not be stated unstratified.
(c) Draw-range stratification `N ∈ {10³, 10⁵, 10⁷}` in equal thirds; if the three hit rates are
not inside a ±0.03 band the result is `N`-dependent and the pooled number is not stated.

## 4. Planted control

The naive plant fails: differences all divisible by `D0` makes `g = D0` and the plant is Reading A
relabelled. So: fix `D0 ≥ 2`, choose `q_j ≥ 0` and `D0 ≤ r_j ≤ 7D0`, set
`v_j = v_i − (8·D0·q_j + r_j)`. Then `clear(i, D0)` holds at `p = 1` by construction. Force at
least one difference divisible by 8 so Reading A fails; keep the overall `gcd` at 1. Verify
population membership with the same predicate used on real data; report discards.

**P-EXISTENCE:** `D0` uniform in `[2, 7·d_min(i)]`; criterion `D0 ∈ S(i)` in ≥ 99%. Failure ⇒ the
detector is broken; abort.
**P-RULE:** `D0 = ⌊span/7⌋` exactly, diluted into real cases at `φ ∈ {1, 0.5, 0.25, 0.10}`. At
`φ = 1` the primary must reject at α = 0.01 with A5 firing ≥ 95%. The smallest `φ` that still
rejects is the measured minimum detectable rule prevalence and is reported with the result.
**If P-RULE does not fire at `φ = 1`, the primary has no power and the null is uninformative.**

## 5. Power

One-sided Fisher, real arm `n`, surrogate `20n`, α = 0.01, power 0.80. Detectable real rate `π₁`:

| `π₀` | n=200 | n=500 | n=1000 | n=2000 |
|---|---|---|---|---|
| 0.02 | 0.100 | 0.060 | 0.046 | 0.038 |
| 0.05 | 0.150 | 0.105 | 0.085 | 0.075 |
| 0.10 | 0.220 | 0.170 | 0.147 | 0.133 |
| 0.20 | 0.350 | 0.290 | 0.263 | 0.244 |

**Target `n = 1000`.** At `π₀ = 0.05` this detects `π₁ ≥ 0.085` — a 1.7× lift — and does **not**
detect a 1.3× lift; any null must say so. Family Holm threshold `0.00625` raises it to ≈ 0.088.
Existence: 1000 clean cases bound the failure rate at ≤ 0.37% (rule of three); that cannot
distinguish "always" from "99.7%". **No interim analysis, no optional stopping.**

## 6. Scope

Integer speeds, exactly 8 runners, threshold exactly `1/8`, closed inequality (a gap of exactly
`1/8` counts as lonely). Candidate instants only `t = p/(8D)`, `p ∈ {1,3,5,7}`,
`1 ≤ D ≤ 7·d_min(i)` — a configuration whose only lonely instants lie off this grid reads as "no
clearing `D`", which is a statement about the grid. Draw: 8 distinct integers uniform without
replacement from `{0,…,N−1}`, `N ∈ {10³,10⁵,10⁷}`, thirds; sorted, translated to `v_1 = 0`; `g`
recorded, not normalised away. Population: ≥ 1 runner named by neither reading, one case per
configuration, draw to 1000 cases, cap `10⁶` configurations, incidence reported with a CI.
Results split by arm, `K`-stratum and `N`-stratum; unstratified figures only if C3b and C3c both
hold their bands. Fixed recorded seed.

## 7. Falsification

**"There is a rule for which `D` to pick"** is falsified within scope if P-RULE fires at `φ = 1`,
**and** the primary does not beat the C1 surrogate at α = 0.01 with `n = 1000`, **and** no family
member survives Holm at 0.05. The permitted conclusion is then exactly: *no rule of the form
"`D*` equals one of the eight pre-registered scalar functionals" exists at prevalence above the §5
level, in this scope.* Not "no rule". Not "`D*` is random".

**"A `D` always exists"** is falsified by a single case with `S(i) = ∅`, which must be printed in
full and is the headline.

## 8. Exactness

Signal path pure Python `int` — the predicate needs no division. `⌊span/7⌋ = span // 7`,
`⌈span/7⌉ = -((-span) // 7)`. No float touches `clear`, `S`, `D*`, the predictors or the
population predicate. Float carve-out, analytic size only: Fisher p-value, Clopper-Pearson
interval, power table.

## 9. Pre-commitment

| # | Outcome | Licenses | Does **not** license |
|---|---|---|---|
| O1 | P-RULE fails at `φ = 1` | Nothing about real data. Repair and re-register. | Any statement about real configurations. |
| O2 | A case with `S(i) = ∅` | "The `p/(8D)` grid does not name every runner — here is the counterexample." | "That runner has no lonely instant" — it does, off the grid. |
| O3 | Existence = 1, real ≈ surrogate | "A clearing `D` was found in every case, failure ≤ 0.37%" **and** the surrogate achieves the same, so existence is a property of the budget `K = 7·d_min`, not of the configuration. | Calling existence a structural fact about the configuration. |
| O4 | `Q23` beats surrogate, C3 clean | "`D*` is predicted by `⌊span/7⌋` or `⌈span/7⌉` at rate `π₁` vs `π₀`, scope §6." Next step: out-of-sample replication, fresh seed and fresh `N`. | A theorem. "`span/7` is *the* rule." Extension to other `n` or non-integer speeds. |
| O5 | `Q23` fails, a family member survives Holm | "`Qk` survives a pre-registered family of 8 with Holm at 0.05, prevalence `π₁`." **Mandatory** out-of-sample replication before any use. | Reporting `Qk` as if it had been primary. The correction travels with the number permanently. |
| O6 | Primary and family null, plant fired | The scoped conditional negative of §7. | "`D*` is unrelated to the configuration." "The enlargement idea is dead." "No structure." A null on 8 projections is a null on 8 projections. |
| O7 | **`D` always exists, value matches no named property** | Exactly that sentence with power attached; the §2 characterisation block becomes the deliverable. Live possibilities stay on the record: (i) `D*` is a function of the gap **vector**, not any scalar summary; (ii) the invariant is a residue class or divisibility relation, against which an exact-match statistic has zero power by construction; (iii) the invariant is carried by `S` as a set, not by its minimum. Each needs a new pre-registration. | Concluding `D*` is arbitrary or noise. |
| O8 | C3a high, or effect only in `K < 10`, or C3c bands break | "The raw-arm effect is resolution-dependent; here is its size per stratum." | Quoting any pooled raw-arm number, or swapping in the g-multiple arm as the pre-registered result. |

**Deviation rule.** Any departure — a predictor added, a case excluded, an arm swapped, `n`
changed, a stratum dropped — is permitted only if listed in the run output under
`DEVIATIONS FROM PREREG v1` with the reason and the point at which it was decided. An undisclosed
deviation voids the run.

---

`[PROVED]` §0's ceiling. `[VERIFIED — 32,000]` the ceiling empirically, attained at 7.
**No data has been collected against §§1–9.**
