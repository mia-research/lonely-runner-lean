# PREREG — Amicable-partner correspondence: bits beyond the `log₂6` Aut ceiling (v2)

**Date 2026-07-23. Supersedes `PREREG_amicable_correspondence_bits_v1.md` (frozen, unmodified).**
Every change from v1 is logged in `PREREG_amicable_correspondence_bits_v1_DEVIATIONS.md` (D1–D6),
decided **before** any data from the registered features existed. Computations run at spec time were
confined to (a) the CM-counter **validation**, (b) the **sample frame** enumeration, (c) the **power**
arithmetic — §6 and §5. **No statistic of §2 has been evaluated on any curve.**
Scratchpad scripts: `cm2.py`, `frame3.py`, `design2.py`, `design3.py`.

Inherited facts, verified against disk: `RESULT_secp_amicable_pair_v1.md` (F1),
`RESULT_orbit_bit_ladder_v1.md` (F2), `RESULT_d1_information_extraction_v1.md` +
`RESULT_D1_lift_affine_test_v1.md` (F3), `PREREG_localized_bit_extraction_v1_DEVIATIONS.md` D1 (the
generator-swap trap).

**Two arms, reported separately, never merged into one verdict.**
**ARM-A** — attack-shaped: does a `P`-only partner-side feature exceed the `log₂6` ceiling?
**ARM-B** — channel-shaped: structural invariants **of the correspondence itself**. It measures the
banned map; it does not use it.

---

## 1. OBJECT

Setting. `E_b : y² = x³ + b` with `b = 7`, over `F_p`, `p ≡ 1 mod 3`, `p > 7`, `n := #E(F_p)` prime. Then
`Aut(E) = μ₆`, and (verified over the whole §6 frame) `n ≡ 1 mod 6`, so `μ₆ ≤ (Z/n)^*` exists on the
scalar side. `Ẽ` is `E_7` over `F_n`. The pair is **amicable** iff `#Ẽ(F_n) = p` (F1: true at secp, exact,
full 256-bit scale).

### 1A. ARM-A object — the symmetry group of the induced scalar partition

Let `Φ` map `E(F_p)∖{O}` to a finite label set, computed **only** from the integer coordinate
representatives `x, y ∈ [0,p)` and the public constants `(p, n, b=7)`. Enumerate `P_j = [j]G`,
`Φ_j := Φ(P_j)`. The object is

> `Γ*(Φ) := { t ∈ (Z/n)^* : ∃ σ ∈ Σ_Φ with Φ_{t·j} = σ(Φ_j) for all j }` ≤ `(Z/n)^*`,

with `Σ_Φ` a pre-declared label-symmetry group (§2, frozen). `Γ*(Φ)` is exactly the group whose orbits are
the (σ-twisted) fibres of `Φ` on scalar space. F2's ceiling is `|Γ*| ≤ 6` for every `Aut`-quotient.
**Hypothesis: `|Γ*(Φ)| > 6` for some partner-side `Φ`, replicating, specific to amicability.**

**Why not mutual information.** `d ↦ P_d` is a bijection, so `I(feature; d)` is saturated for *any*
injective feature — the raw `x`-coordinate already gives `log₂n − 1` "bits". An MI/bit statistic here is a
**proxy that is tautologically maximal**, the same shape as the recorded `r = v − w` failure. `Γ*` is
immune: an injective `Φ` returns `{1}`, not a large value.

**T1 — the CM coordinate map is banned from every feature (unweakened from v1).**
`cm_amicable_correspondence_v1.py` records `E(F_p) ≅ Z[ω]/(π_p−1) ≅ F_n`: the partner field **is** the
coordinate ring, and the induced coordinate `φ(P)` **is the discrete logarithm**. Any feature built from
`φ` smuggles `d` into the feature path. Consequently the only `d`-free partner-side constructions are
those built from the **integer representatives** of `P`'s coordinates reduced mod `n`, plus public
constants — non-canonical by construction, which is exactly why no homomorphism exists (F4/F5).

**T2 — injective recodings are forced.** Any `Φ` injective in `x(P)` has fibres `{±d}` by construction, so
`Γ* = μ₂` is forced and carries zero information. `Γ*_forced` is pre-declared per feature in §2; only
`|Γ*| / |Γ*_forced|` is counted (project rule: count only unforced hits).

**Disjoint construction — structural, not conventional.** `Γ*` quantifies over all points and never
references `G` or `d`. The index `j` enumerates the group; `Φ` receives a **point**, never `j`. `Γ*` is
**provably generator-invariant**: with `G' = [s]G`, `P'_j = P_{sj}`, so `Φ'_{tj} = σΦ'_j ⟺ Φ_{t(sj)} =
σΦ_{sj}`, and `sj` ranges over all residues; `(Z/n)^*` is abelian so no conjugation survives. The recorded
trap `P_d^{[7]G} = P_{7d}^{G}` therefore **cannot contaminate the primary statistic**, and a generator
swap is barred from use as a replicate (§3).

**Disclosure forced by ARM-B (new in v2).** Computing `Γ*` uses the index `j = φ(P_j)`. That is a use of
`φ` on the **measurement side**, never in the feature path. The distinction is load-bearing: a group `Γ`,
once named, is usable **without** `φ` — which is why a positive finding would not inherit `φ`'s cost, and
why the measurement's use of `φ` is not a T1 violation. The same logic licenses plants that use `d`.

### 1B. ARM-B object — structural invariants of the correspondence

T1 bans `φ` from features; it does not make `φ` unmeasurable, and in-frame `φ` is computable. ARM-B
measures **properties of the channel**, never a recovered scalar.

- **Illegal (banned, still):** build a feature from `φ`, ask whether it predicts `d`. Circular — `φ` *is* `d`.
- **Legal (ARM-B):** invariants of the *relation* between `φ` and the T1-legal surrogates.

**`φ` alone has no unforced invariants.** With the enumeration `P_j = [j]G`, `φ(P_j) = j` identically; any
statistic of `φ` in isolation is a statistic of the identity map on `Z/n`. Its content is entirely
relational. Two of the three candidate invariants proposed for this arm are therefore **algebraically
forced and were dropped rather than registered weakly** (logged in DEVIATIONS D5):

| dropped candidate | why it cannot fire | salvaged as |
|---|---|---|
| `δ(P,Q) = φ(P+Q) − φ(P) − φ(Q) mod n` | `φ` is a group **isomorphism** ⇒ `δ ≡ 0` is an identity | **A2-3** (same defect, legal surrogate vs partner group law) |
| fibre geometry of `φ` vs μ₆ orbits | `φ` injective ⇒ fibres are singletons; `φ(λP) = ℓφ(P)` **is the definition** of the GLV eigenvalue | **A2-2** (does μ₆ descend through the legal reduction?) |

The legal surrogate is `ρ(P) := (x mod n, y mod n)`. **Every** legal feature factors as `Φ = f ∘ ρ`, hence

> `Γ*(ρ) ⊆ Γ*(Φ)` for every legal `Φ`,

so `Γ*(ρ)` is a **family-level floor** — the symmetry every legal feature has for free — a statement about
the whole legal family, not about the four members enumerated in §2. **An information-theoretic capacity
statement about that family would be vacuous**, since the family already contains injective maps; the
non-vacuous axis is structural.

---

## 2. STATISTIC

### 2A. ARM-A primary (exactly one): `|Γ*(Φ)|`, an integer, with the group **named**
(order, canonical generator, the `σ`'s). Null distribution: for label-collision probability
`q = Σ_v (m_v/(n−1))²`, a fixed `t` of order `k` lies in `Γ*` by chance with probability
`≈ |Σ_Φ| · q^{(n−1)(1−1/k)} < 2^{−(n−1)/4}` for every `n` in scope. **FPR numerically zero; power against
an exact symmetry is 1** (full enumeration, no sampling). Blind spot: *approximate* symmetry — registered
now as §2b, not discovered later.

**Validity gate (pre-declared, reported, never silently applied).** `Φ` is `Γ*`-faithful iff
`|image(Φ)| = (n−1)/|Γ*(Φ)|` exactly. Every row reports `(|Γ*|, |image Φ|, faithful Y/N)` **and the exact
fibre-size multiset**. Non-faithful rows are reported, not dropped.

**Frozen feature list — 4 hypothesis features + 1 degenerate control. No additions after this document.**
Write `x̄ = x mod n`, `ȳ = y mod n`, `δ = (ȳ² − x̄³ − 7) mod n`, `χ_n` the quadratic character mod `n`.

| id | `Φ(P)` | `Σ_Φ` | `Γ*_forced` (analytic) |
|---|---|---|---|
| `ΦA` | `χ_n(x̄³ + 7) ∈ {−1,0,+1}` — does the reduced `x` land on `Ẽ(F_n)` or its twist | `{id}` | `μ₂` (`x`-only) |
| `ΦB` | `χ_n(δ)` | `{id}` | `{1}` |
| `ΦC` | `δ` | `{id}` | `{1}` |
| `ΦD` | `±`-class of `e(P) := dlog_{G̃}(Q(P))` in `Ẽ(F_n)`; `Q(P)` = point with `X = x̄` and canonical `Y`; `⊥` on the twist branch | `{±1} × (Z/#Ẽ(F_n))^*` | `μ₂`; by T2 the **invariance** part is forced, so `ΦD`'s unforced content is entirely in the `σ ≠ id` equivariance part |
| `N0` | `ord(Q(P))` in `Ẽ(F_n)` | `{id}` | **degenerate control** — on the amicable arm `#Ẽ(F_n) = p` is prime, so `ord ≡ p`, `|image| = 1`, `Γ* = (Z/n)^*`. Must be caught by the faithfulness gate. **If `N0` is reported as a finding, the run is void.** |

**Forced-structure note, recorded now so it is not later mistaken for a finding.** The curve equation holds
mod `p`, so as an integer `y² − x³ − 7 = p·m`; hence `δ = p·m mod n` and `ΦB = χ_n(p)·χ_n(m)` with
`χ_n(p)` a per-curve constant. `gcd(p,n) = 1`, so this degenerates nothing, but the `p`-factor is forced
and is not a discovery.

`⊥` is a label value, never a discard; its rate is reported per curve. On non-amicable curves `#Ẽ(F_n)`
need not be prime, so `e` is the dlog in `⟨G̃⟩` when `Q ∈ ⟨G̃⟩` and `⊥` otherwise.

### 2b. ARM-A secondary, registered now (graded / subspace-escape)
Required by the rule that a bound may not become a verdict: an effect could be *approximate*, invisible to
`|Γ*|`. `(Z/n)^*` is cyclic, so each divisor `k | (n−1)`, `k > 6`, has a unique subgroup `Γ_k` with
canonical generator `t_k` (smallest generating residue). With `q` from `Φ`'s own image histogram:

> `a(k) := #{j : Φ_{t_k·j} = Φ_j}`, `z(k) := (a(k) − (n−1)q)/sqrt((n−1)q(1−q))`,
> **secondary statistic `z_max := max_{k>6, k|(n−1)} z(k)`**, Holm-corrected across the divisor cells
> (§6: up to 57 at Tier B), exact integer rank p-value against the §3 matched null.

Exact `Γ_k`-invariance ⟺ invariance under `t_k`, so §2b degrades continuously to §2A. `z_max` is a max
over a **small, pre-declared, subgroup-indexed** cell set, not over all `n−1` elements: pooling over all
`t` was rejected at design time (design calc: pooled `e_min ≈ 0.40` at `n = 2000` vs `0.10` subgroup-wise).

### 2B. ARM-B statistics (three, each with its own control and power)

| id | statistic | what it bounds | `Γ*_forced` / forced part |
|---|---|---|---|
| **A2-1** | `|Γ*(ρ)|` for `ρ(P) = (x̄, ȳ)`, exact integer, group named | the **family-level floor**: symmetry every legal feature has for free (§1B) | `{1}` — `ρ(P_{−j}) = (x̄, (p−y) mod n) ≠ ρ(P_j)`, so nothing is forced |
| **A2-2** | agreement count `#{x : r(βx mod p) ≡ u·r(x) + v (mod n)}` where `r(x) = x mod n`, `β³ ≡ 1 mod p` the GLV multiplier, and `(u,v)` fixed from the two smallest non-collision `x` — i.e. **does the μ₆/GLV action descend through the legal double reduction as an affine map?** | width of the channel with respect to the `Aut` action that sets the `log₂6` ceiling | the `p − n = t_p − 1` collision-set obstructions (orientation `p>n` only) are forced and are excluded from the count and reported separately |
| **A2-3** | support fraction of `δ_ρ(P,Q) := ρ(P+Q) ⊖ (ρ(P) ⊕ ρ(Q))`, `⊕` the `Ẽ(F_n)` group law, `⊥`-tagged when either operand is off-curve — **how far the legal reduction is from intertwining the two group laws** | the gap F4 leaves open: coprimality proves no homomorphism exists (support ≠ 0 somewhere) but says **nothing** about support size or distribution | nothing beyond "support ≠ 0 somewhere" (F4) |

ARM-B outputs are properties of the channel. **No ARM-B statistic returns, approximates, or bounds a
scalar**, and none may be quoted as a bit count about `d`.

**α.** ARM-A primary: `α = 0.01` on the §3 contrast. ARM-A secondary: `α = 0.01` Holm within unit, then
the §5 replication rule. ARM-B: `α = 0.01` per statistic on its own contrast. The three families are
reported separately and are never combined into a single p-value or a single verdict.

---

## 3. MATCHED CONTROL

**M1 — modulus swap (matched null for "the modulus is the curve order"); applies to every statistic in
both arms.** Recompute with `n` replaced by `n'`, a prime `≡ 1 mod 3` from the 199 primes nearest `n` in
that class, excluding `n` and excluding any `n'` with `#E_7(F_{n'}) = p`. Everything else byte-identical.
- **Preserves:** the curve and all its points; the scalar-side group order `n`; μ₆ and every automorphism
  structure; modulus size and residue class; each feature's `Γ*_forced`; the label alphabet and (to
  sampling error) the image histogram.
- **Destroys:** the identity `modulus = #E(F_p)` — the CM link between the field reduced *into* and the
  curve reduced *from*.
- **Not a shuffle.** No relabelling of points or scalars occurs, so M1 cannot destroy a symmetry the
  readout has by definition. This is the direct fix for the recorded "6–7σ soft shadow" null-mismatch: the
  μ₆ structure the readout has by construction survives M1 intact and is therefore not what M1 tests.

**M2 — scalar relabel: registered as a NULL, barred as a replicate.** `Φ(P_{t·d})` against `d` is exactly
the generator swap `G → [t]G` (D1 identity, verified on disk). The primary statistic is provably invariant
under it (§1A), so M2 has no discriminating power here and is **not run as a replicate**. Replication is
**across primes only**. Treating a generator swap as an independent replicate is a deviation and must be
logged.

**C — the amicability contrast (this is what attributes the effect).** M1 isolates "modulus = curve
order", which holds on amicable *and* non-amicable curves; it **cannot** attribute anything to
amicability. Attribution comes from §6's matched design: amicable vs size-matched non-amicable, same
`b = 7`, same `p ≡ 1 mod 3`, same `n` prime, same orientation stratum, differing **only** in whether
`#Ẽ(F_n) = p`. Both arms run the identical pipeline including M1.

---

## 4. PLANTED CONTROL

**P1 — ARM-A exact plant (must fire, deterministically).** For `k | (n−1)`, `k > 6`, set
`Φ^plant_k(P) :=` lexicographically smallest `(X,Y)` over `{[t]P : t ∈ Γ_k}` — computable from `P` alone.
Then `Γ*(Φ^plant_k) ⊇ Γ_k` by construction; the test must return `|Γ*| ≥ k` **and name `Γ_k`**. Ladder:
every `k | (n−1)`, `k > 6`, on every curve. **Any missed `k` ⇒ pipeline broken ⇒ the entire null is
uninformative, reported as instrument failure, no conclusion drawn.**

**P2 — ARM-A graded plant with a measured `e_min` ladder (must fire).** For
`ε ∈ {0.02, 0.05, 0.10, 0.20, 0.40, 0.80}`, `Φ^ε_k(P) := Φ^plant_k(P)` on the `⌈ε(n−1)⌉` points of
smallest `X`, `:= ΦC(P)` elsewhere. Report the smallest `ε` clearing Holm-corrected `α = 0.01` vs M1.
That measured value **is** `e_min(n)`; every §9 null cell must quote it.

**B1 / B2 — ARM-B two-sided plants for A2-2 (one must fire, one must not).**
`B1`: replace `β` by `1`. The affine descent then holds with `(u,v) = (1,0)` on **every** non-collision
`x` — the statistic must return the full count. `B2`: replace `β` by a uniformly drawn multiplier of
order `> 3`. The statistic must return chance-level agreement. **If B1 under-fires or B2 over-fires, A2-2
is void.**

**B3 / B4 — ARM-B two-sided plants for A2-3.** `B3`: replace `ρ` by the identity map on `E(F_p)` with the
`E(F_p)` group law on both sides — support must be exactly `0`. `B4`: replace `ρ` by a uniformly drawn
bijection onto the same label set — support must be full to within the §5 sampling resolution. **If either
misses, A2-3 is void.**

**A2-1** inherits P1: the plant `Φ^plant_k` is legal (uses `P` only), so `Γ*(ρ) ⊆ Γ*(Φ^plant_k) ⊇ Γ_k`
exercises the same code path; P1 firing validates A2-1's estimator.

**N0 — negative control (must NOT fire as a finding).** §2A degenerate row. If reported as a
beyond-ceiling finding, the faithfulness gate failed and the run is void.

---

## 5. POWER

**ARM-A exact arm.** Full enumeration over all `d ∈ [1,n)` and all `t ∈ (Z/n)^*`; no sampling. Power
against an exact symmetry `Γ_k ⊋ μ₆` is **1**; FPR `< 2^{−(n−1)/4}`. **Zero power against approximate
symmetry** — stated now; that is why §2b exists.

**ARM-A contrast, Tier A — exact Fisher one-sided, 108 vs 108 matched units** (`design2.py`, exact
rationals via `comb`):

| amicable arm fires | significant at `α=0.01` iff non-amicable fires at most | implied rate difference |
|---|---|---|
| 108/108 | 101/108 | **0.065** |
| 102/108 | 90/108 | 0.111 |
| 97/108 | 83/108 | 0.130 |
| 86/108 | 69/108 | 0.157 |
| 75/108 | 57/108 | 0.167 |

`108/108` vs `0/108` gives `p = 1.75 × 10⁻⁶⁴`. **Minimum detectable rate difference 0.065** (v1's Tier-B
value was 0.333). **The 0.23 effect v1 §5 called unreachable is inside this frame.** Paired exact
(McNemar) alternative: `b` discordant pairs all favouring amicable gives `p = 2^{−b}`, so `b ≥ 7`
discordant pairs are required for `p < 0.01`.

**ARM-A contrast, Tier B — 21 vs 21** (unchanged from v1): 21/21 significant iff non-amicable ≤ 14/21;
15/21 iff ≤ 6/21; **minimum detectable rate difference 0.333**.

**ARM-A graded arm — design estimate `e_min ≈ z*/sqrt((n−1)(1−q)/q)`, `z* = 4.5`, `q = 1/2`** (superseded
by the measured P2 ladder wherever they disagree; **the measured value governs**):

| `n` | 79 | 967 | 6091 | 19483 | *(Tier A `n` only:)* 50000 | 100000 | 198901 |
|---|---|---|---|---|---|---|---|
| design `e_min` | 0.510 | 0.145 | 0.058 | 0.032 | 0.020 | 0.014 | 0.010 |

The graded arm runs at **Tier B only** (cost, §6), so its live range is `e_min` 0.510 (`n = 79`) to 0.032
(`n = 19483`). `n = 79` is power-starved: it contributes to replication counting only and may not carry a
bound on its own. The Tier-A columns are shown solely to document what a future Tier-A graded run would
buy; **they may not be quoted as this run's floor.**

**ARM-B power.**
- **A2-1, A2-2:** exact, full enumeration over all points; power 1 against an exact structure, FPR as in
  §2A. Contrast at Tier A ⇒ minimum detectable rate difference **0.065**.
- **A2-3:** full enumeration of all `(n−1)²` pairs for `n ≤ 1000`; `M = 10⁵` uniformly sampled pairs
  otherwise. `5σ` resolution on the support fraction is `5·sqrt(s(1−s)/M)` = **0.0079** at `s = 1/2`,
  `M = 10⁵` (and 0.0025 at `M = 10⁶`, not run). **A support deficit below 0.0079 is undetectable here**
  and routes to §9 cell 8.

---

## 6. SCOPE

Every number inherits its tier's line and may not be quoted without it. **No number from one tier may be
quoted with the other's scope.**

- **Curve:** `E_7 : y² = x³ + 7` (F1's curve, fixed). No twist sweep, no other `b`.
- **Frame rule (complete enumeration, no selection):** `p` prime, `p ≡ 1 mod 3`, `11 ≤ p < LIMIT`,
  `n = #E_7(F_p)` prime, `n ≠ p`. Enumerated independently at spec time (`frame3.py`):

  | LIMIT | amicable | non-amic | fraction | 2-cycles |
  |---|---|---|---|---|
  | 20000 | 42 | 93 | 0.311 | 21 |
  | 200000 | 216 | 566 | 0.276 | 108 |

  The `p < 20000` sub-frame reproduces v1 §6 element-for-element. Observed amicable fraction 0.276 is
  consistent with the recorded `~26%` density (F1 §2). The `10⁶` frame was **not** verified at spec time
  and is not used.
- **Independence unit = the 2-cycle**, since `(67,79)` and `(79,67)` are the same object.
- **Orientation is a stratum, not a filter (D3).** Both orientations of every 2-cycle are run. For `p < n`
  reduction mod `n` is the identity on `[0,p)` and `ρ` is injective; for `p > n` it is a genuine reduction
  with collision set of size `p − n = t_p − 1`. v1's `p < n` unit rule silently selected the
  collision-free orientation. Matched pools: 279 non-amicable at `p<n`, 287 at `p>n` — ample for 108
  matched pairs each. Contrast tests are computed **within stratum**; the two orientations are never
  pooled into one rate without saying so.
- **Matched controls:** for each amicable unit, the qualifying non-amicable curve of the same orientation
  with `p` nearest (ties → smaller `p`), assigned without replacement in increasing amicable `p`.
- **Generator:** canonical (smallest `x`, then smallest `y`) on both curves. The primary statistic is
  generator-invariant by the §1A proof; `G̃` affects `ΦD` only up to `Σ_ΦD`, which absorbs it.
- **Point counting:** CM/Cornacchia + annihilation selection, `O(p)` character-sum fallback on ambiguity
  (D2). Validated **1123/1123** with 2 fallbacks below 20000. A curve whose order cannot be resolved is
  dropped **and listed**, never silently.

### Tier lines (quote verbatim beside every number)

> **Tier A** — `E_7`, `p ≡ 1 mod 3`, `11 ≤ p < 200000`, `n` prime: **108 amicable 2-cycles × 2
> orientations = 216 curves**, 216 matched non-amicable controls, `Σn = 3.47 × 10⁷`, `max n = 198901`,
> `mean n = 80275`, divisor cells per unit **4 to 102**. Carries: ARM-A exact arm, A2-1, A2-2.
> Contrast floor **0.065**. Max `p` is **17.60 bits**.

> **Tier B** — same rule with `p < 20000`: **21 amicable 2-cycles × 2 orientations = 42 curves**, 42
> matched controls, `Σn = 6.50 × 10⁵`, `max n = 19687`, divisor cells per unit **4 to 57**. Carries: ARM-A
> graded arm (§2b), A2-3. Contrast floor **0.333**. Max `p` is **14.25 bits**.

**Why the split (cost, not convenience).** The exact arm needs no resampling (analytic null) and costs
`Σn`. The graded arm needs 199 M1 replicates and costs `199 × Σn`: `1.29 × 10⁸` at Tier B (affordable) but
`6.91 × 10⁹` at Tier A (not). The `10⁶` frame would put the exact arm at `Σn ≈ 3.94 × 10⁸` (~23× Tier A)
and the graded arm at `7.8 × 10¹⁰`. Extending Tier A to `10⁶` is a pre-declared option contingent on a
faster exact-arm implementation and requires a new DEVIATIONS entry — never a run-time judgment call. The
marginal contrast gain (0.065 → 0.017) changes no §9 cell threshold.

### Scale honesty

`p < 200000` is **under 17.6 bits**; secp is **256 bits**. This run spans none of that gap.
- **F1 is exact at full scale.** Nothing here strengthens or weakens it.
- **A positive result** (a named `Γ_k` on a curve) is an **exact algebraic fact about that curve**:
  `[VERIFIED-INSTANCE]`, tier line attached. It becomes a claim about `E_7/F_p` generally, or about secp,
  **only by proof** — never by extrapolating the frame.
- **A null** is `[EMPIRICAL, scoped]`: bounded to these features, this tier, and the measured `e_min`
  floor. Not a statement about secp, not about untested features, and **not a closure of the amicable
  channel**.
- **ARM-B carries an additional clause:** its numbers are computed **where `φ` is computable, i.e. in-frame
  only. They do not transport to secp by computability** — there `φ` costs a discrete log. A structural
  law about the map could transport, **but only by proof.**
- `ΦD` needs an `O(√p)` partner-side discrete log; it is feasible only in-frame and **cannot** be
  evaluated at secp scale by anyone, including under a positive result.

---

## 7. FALSIFICATION

**ARM-A** is abandoned iff all four hold:
1. `|Γ*(Φ)| = |Γ*_forced(Φ)|` for all 4 features on all 108 Tier-A units in both orientations (and no
   `σ ≠ id` equivariance beyond `Γ*_forced` for `ΦD`); **and**
2. `z_max` fails Holm-corrected `α = 0.01` vs M1 on ≥ 18 of 21 Tier-B units; **and**
3. P1 fires on every planted `k`, and P2 fires at or below the §5 design `e_min`; **and**
4. `N0` is caught by the faithfulness gate.

**ARM-B** is abandoned iff A2-1 returns `Γ*(ρ) = {1}`, A2-2's agreement is at chance off the forced
collision set, and A2-3's support is full to within the §5 resolution — **with B1–B4 all firing
correctly**. If any plant misbehaves, the corresponding statistic is void and nothing is abandoned.

If ARM-A's (3) fails, nothing is abandoned — the run is void. If (1)–(2) hold but the amicable and
non-amicable arms are indistinguishable, the *amicability* attribution is abandoned while the structure
question is not (§9 cells 2/7).

**What this design cannot falsify, stated now:** (i) features outside the frozen §2 list; (ii) effects
below the measured `e_min` (ARM-A) or below 0.0079 support resolution (A2-3); (iii) effects appearing only
at `p ≫ 200000`; (iv) non-group-structured fibre patterns that are neither exact `Γ_k`-orbits nor
`t_k`-approximate — partially covered by the reported fibre-size multiset, by neither statistic. These
four are the declared blind spots and must be restated verbatim beside any null.

---

## 8. EXACTNESS

`int` throughout the signal path, per `btc_puzzle_investigation/CLAUDE.md`:
- point arithmetic, Cornacchia, trace candidates, coordinate representatives, `x mod n`, `δ`, characters
  via `pow(a,(n−1)//2,n)`, orbit enumeration, `Γ*` membership, subgroup generators, divisors, `a(k)`,
  `(u,v)` fitting in A2-2, `⊕`/`⊖` in A2-3, image histograms, fibre multisets, integer BSGS discrete logs:
  all `int`.
- Permutation/rank p-values vs M1 are **exact integer ranks** over 199 replicates; Fisher exact and
  McNemar via `math.comb` / `fractions.Fraction` (§5's numbers were produced this way).
- **Float carve-outs, analytic-size only, none in the signal path, none deciding a threshold on raw
  data:** (a) `z(k)`, `z_max` are monotone re-expressions of the integer counts `a(k)` and are ranked
  against integer M1 ranks — **the rank decides, the `z` is display**; (b) `log₂` of exact integers when a
  `|Γ*|` is quoted in bits; (c) Holm arithmetic on already-exact rank p-values; (d) the `5·sqrt(s(1−s)/M)`
  resolution figure for A2-3, a design quantity only.
- **Pipeline-validity controls that must pass before any statistic is read:** `check_no_float.sh` on all
  run scripts; and the CM-counter validation of D2 (**1123/1123** agreement with the `O(p)` counter below
  20000, 2 ambiguous resolved by fallback), re-run as a gate since above 20000 the CM counter is the sole
  source of `n`.

---

## 9. PRE-COMMITMENT

Filled in before the run; no cell renegotiable afterwards. "Fires" = `|Γ*|/|Γ*_forced| > 1` with the
faithfulness gate passed (exact), or Holm-corrected `α = 0.01` vs M1 (graded). **ARM-A and ARM-B
conclusions are written in separate sections of the result document and never merged into one verdict.**

### ARM-A

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| 1 | Exact arm fires, faithful, on **≥ 77 of 108** Tier-A units (in both orientation strata), **and** the within-stratum contrast is Fisher-significant at `α=0.01` (§5 table) | **A symmetry beyond the F2 ceiling exists on the amicable arm.** Report it by *name*: `Γ*`, its order, canonical generator, the `σ`'s, the fibre multiset — never as a bit count alone. `[VERIFIED-INSTANCE]`, Tier A line verbatim. Next step is a **proof** that `Γ_k` is forced by the amicable relation, since only a proof reaches secp. **No ECDLP claim is made or implied.** |
| 2 | Exact arm fires ≥77/108 **but the contrast fails** | **A CM / `j=0` family law, not an amicable one.** The amicability attribution is withdrawn in the same sentence that reports the structure. F1 is not invoked. |
| 3 | Exact arm fires on **< 77 of 108**, or fires in one orientation stratum only | **Chance pattern (or an orientation artifact), not named.** Report the unit list and the stratum split; name no group; escalate nothing. |
| 4 | Exact arm at forced value everywhere; **graded arm fires** (≥18/21 Tier-B units, Holm `α=0.01`, contrast significant) | **Approximate, not exact, symmetry.** Output is a *characterization*: which divisors `k`, which `t_k`, the agreement excess, the fibre multiset — routed to an anomaly drill. Not called a leak; not called bits. |
| 5 | Exact arm at forced value everywhere; graded arm within M1 null on ≥18/21; **P1 and P2 both fire** | **Scoped null with power.** Mandatory statement form: "Among the 4 frozen partner-side features, on `E_7/F_p` for the 108 amicable 2-cycles with `p < 200000` (both orientations), no symmetry beyond `μ₆`-forced was detected exactly; and on the 21 Tier-B units, none approximately above `ε = e_min(n)` (measured, per-curve table)." Followed **verbatim** by the four §7 blind spots. **Not a closure of the amicable channel; may not be written as one.** |
| 6 | **P1 or P2 fails to fire** anywhere | **Run void — instrument failure.** No conclusion in either direction. Fix, re-run under this spec. |
| 7 | Contrast null (arms indistinguishable) while something fires | Attribute to the shared structure (CM by `Z[ω]`, `j = 0`, `n` prime), **not** to amicability. |
| 8 | Fewer usable matched pairs than the tier states, or an observed rate difference below the tier floor (**Tier A 0.065 / Tier B 0.333**), or `e_min` above what the plant ladder resolves | **Abstain on that arm.** Abstention is reported as abstention: not a null, not a closure, and it does not license a post-hoc statistic on the same data. |
| 9 | `N0` reported as a finding | Faithfulness gate failed. **Run void.** |
| 10 | A `d`-dependent quantity found anywhere in a hypothesis feature's evaluation path | **Stop; report the construction defect as the finding.** No statistic from that feature is reported, at any significance. |

### ARM-B

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| 11 | **A2-1**: `Γ*(ρ) ⊋ {1}`, replicating ≥77/108, contrast significant | **The whole T1-legal family has a free symmetry**, named by group and generator — a statement about the family, not about §2's four members. Report with the §1B factorisation argument (`Γ*(ρ) ⊆ Γ*(Φ)` for all legal `Φ`) as its justification. Channel property only; **no scalar is claimed, bounded, or approximated.** |
| 12 | **A2-1**: `Γ*(ρ) = {1}` throughout | The legal family has **no free symmetry** at this tier: any beyond-ceiling symmetry a legal feature has must come from `f`, not from `ρ`. A width statement about the channel, `[EMPIRICAL, Tier A]`. Not a closure. |
| 13 | **A2-2**: the affine descent holds off the forced collision set (B1 fires, B2 does not) | **The GLV/μ₆ action descends through the legal double reduction.** Report `(u,v)`, the agreement count, the forced-collision count separately. This is a property of the correspondence; it bears on what legal features can see for free, and is **not** a bit count about `d`. |
| 14 | **A2-2**: agreement at chance off the collision set | The μ₆ action **does not** descend affinely through the reduction at this tier — a width bound on the channel, with the forced collision count reported beside it. Not a closure. |
| 15 | **A2-3**: `δ_ρ` support **bounded away from full** by more than the §5 resolution (0.0079), replicating, contrast significant | **A measured width for the gap F4 leaves open**: coprimality forbids a homomorphism, and this quantifies how far from one the legal reduction actually is. Report the support fraction, its distribution, and the `⊥` rate — as a channel property. Escalate to a proof attempt on the support's algebraic description. |
| 16 | **A2-3**: support full to within resolution | The legal reduction is **maximally non-homomorphic** at this resolution — also a width statement, and the natural complement of F4. `[EMPIRICAL, Tier B, resolution 0.0079]`. Not a closure. |
| 17 | **B1–B4**: any plant misbehaves | The corresponding ARM-B statistic is **void**; report instrument failure for that statistic only. Cells 11–16 for that statistic are not filled. |
| 18 | Any ARM-B number is quoted without its in-frame `φ`-computability clause, or is used to support an ARM-A conclusion | **Reporting defect.** The two arms are separate; correct the document before promotion. |

**Standing constraints on every cell.** No number is quoted without its tier line. No cell licenses a
statement about secp or about ECDLP. No cell licenses adding a feature to §2 and re-running; a new feature
requires a new prereg. Deviations go to `PREREG_amicable_correspondence_bits_v1_DEVIATIONS.md` before the
affected data are read.
