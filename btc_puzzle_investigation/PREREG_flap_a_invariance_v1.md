# PRE-REGISTRATION — Flap classifier `a`-invariance of the doubling 2×2 (Coupling-Principle test)

**Status: SPEC ONLY. FROZEN before any per-`a` table, log-odds, or dispersion statistic is computed.**
**Date 2026-07-23. Designed context-isolated by `experiment-designer`.**
Implementation target: `flap_a_invariance_v1.py`. Inputs already seen and treated as given (not
re-tested): `PREREG_flap_grouplaw_transition_v1.md`, `flap_grouplaw_run_v1.out`,
`flap_grouplaw_transition_v1.py`.

---

## 0. OBJECT

### 0.1 Curve and classifier (as implemented)
secp256k1 `E : y² = x³ + 7` over `p = 2²⁵⁶ − 2³² − 977`; `β³ ≡ 1`, `ρ = β + 1` primitive 6th root
(`ρ² − ρ + 1 ≡ 0`); `cent(u) = u₀ − p·[u₀ > (p−1)//2]`.

```
ε_a(X) = 1  ⟺  2·|cent(aX mod p) − cent(ρ·(aX) mod p)| > p
```

**DEFINITIONAL DISCLOSURE, made before the run.** `PREREG_flap_grouplaw_transition_v1.md` §0 states
the *signed* form `cent(s) − cent(ρs) > p/2`; `flap_grouplaw_transition_v1.py` line 47 implements the
*absolute-value* form above. The completed run's gate density `16273/65536 ≈ 0.2483` matches the
absolute-value form (the signed form would give ≈ 1/8). **This experiment uses the AS-IMPLEMENTED
absolute-value form**, so that it is testing the same object the completed run tested. The spec/code
divergence is recorded here as a pre-existing disclosed deviation of
`PREREG_flap_grouplaw_transition_v1`. ARM-0 will print the gate density under **both** forms so the
record is unambiguous. **Every conclusion below is scoped to the absolute-value form.**

### 0.2 The object under test
```
x2(X) = (X⁴ − 56X) · (4(X³+7))⁻¹  mod p          # x-coordinate of 2P
```
`ε_a(X) = ε_1(aX)` (immediate from the definition). Substituting `Y = aX`:
```
( ε_a(X), ε_a(x2(X)) )  =  ( ε_1(Y), ε_1(D_a(Y)) ),      D_a(Y) := a · x2(a⁻¹ Y)
```
**The object is the correlation of the flap indicator `1_{S_1}` with its pullback under the
`a`-conjugated doubling map `D_a = m_a ∘ x2 ∘ m_a⁻¹`, as `a` varies.** `S_1 = {Y : ε_1(Y) = 1}`.
`D_a` is a degree-4 rational map for every `a` — never degree 1 — so `ε_1 ∘ D_a` is never a
relabelling of `ε_1` and the joint is never forced.

### 0.3 Confirmation / refutation of the motivating reasoning (asked for explicitly)
- **CONFIRMED:** `ε_a(X) = ε_1(aX)` exactly, so varying `a` relabels which abscissas are flap.
- **CONFIRMED:** `x(2P)` is not determined by `a·x(P)` — scaling and doubling do not commute — so
  the joint statistic depends on `a` through the genuinely `a`-dependent map `D_a`. **The joint is
  NOT a relabelling and the question is well posed.**
- **REFINEMENT (derived here, before the run):** the population marginals of both coordinates are
  `|S_1|/(#valid abscissas)` for **every** `a` (both `m_a` and `x2` are bijections on valid
  abscissas; `2` is invertible mod the odd `N_ord`). Hence the population 2×2 has its two margins
  pinned and **exactly one free degree of freedom: the log-odds `θ_a`.** The `a`-invariance question
  is one-dimensional. (On a finite sample the margins fluctuate at `O(√n)`; the conditional
  permutation null of §3 conditions on the observed margins and handles this exactly.)

### 0.4 Tautological / forced components — named and DISCARDED by name
- **T-i (FORCED, discarded).** The **marginal** flap density is `a`-invariant by construction
  (population level, §0.3). Any statistic that is a function of the margins alone has zero
  information about `a`-dependence. **Discarded: per-`a` flap density, per-`a` marginal drift, and
  any 1-df test of "is the flap rate the same across `a`".**
- **T-ii (FORCED, discarded — and reused as a gate).** For `ζ ∈ μ₆ = {±1, ±β, ±β²}`, `ε(ζY) = ε(Y)`
  (established, ARM-0 verified), so the **entire 2×2 table for `ζa` is cell-by-cell identical to that
  for `a`.** Additionally `x2(βX) = β·x2(X)` exactly (since `β⁴ = β`, `β³ = 1`), so `D_{βa} = D_a` as
  maps. **The effective `a`-space is `(ℤ/p)*/μ₆`, of size `(p−1)/6`.** Consequence: two draws in the
  same `μ₆`-orbit are **one** configuration, not two. Enforced at sampling (§4 G6) and reused as a
  forced-invariance detector gate (§4 PC-id). **Discarded: any tally that counts `a` and `βa` as two
  instances.**
- **T-iii (discarded).** Comparing the pooled-over-`a` 2×2 to the analytic `[[¾,¼],[¾,¼]]` — same
  Markov-trivial / wrong-null defect as D1 in the parent prereg.
- **NOT tautological:** feature `ε_1(Y)` and target `ε_1(D_a(Y))` share the classifier but are linked
  only by the degree-4 map `D_a`; neither is a sub-construction of the other. **No `r = v − w`
  hazard.**

---

## 1. STATISTIC (exactly one primary, named now)

Let `K` values of `a` be sampled (§6). For each `a`, on a **shared** pool of `n` index positions,
form the 2×2 `[CC_a, CF_a, FC_a, FF_a]` from `(ε_a(X_i), ε_a(x2(X_i)))`, `i = 1..n`; write
`rowF_a = FC_a + FF_a`, `colF_a = CF_a + FF_a`.

### 1.1 PRIMARY — `D_int`, exact integer dispersion across `a`
```
D_int  =  Σ_{a}  ( n · FF_a  −  rowF_a · colF_a )²
```
Each summand is the squared integer deviation of `FF_a` from its conditional-independence mean,
scaled by `n` to stay in integers. `n` is **identical for every `a`** by construction (§6.2), so the
summands are equally weighted and `D_int` is a monotone transform of Cochran's `Q` on the log-odds.
**No float in the primary path.** Null distribution: the joint conditional permutation ensemble of
§3 (integer ranks), `B = 9999` draws, `p = (1 + #{b : D_int^{(b)} ≥ D_int^{obs}}) / (B+1)`.
Analytic reference (reported, not decisive): `Q ~ χ²_{K−1}` under `a`-invariance.

### 1.2 Effect-size / characterization companion (named float carve-out)
```
θ_a  = log( CC_a · FF_a / (CF_a · FC_a) )       # per-a log-odds; 1 free df per §0.3
V    = 1/CC_a + 1/CF_a + 1/FC_a + 1/FF_a  ≈  256/(9n)
τ̂    = weighted SD of {θ_a}                     # the reported dispersion magnitude
```
`log` is a monotone statistic reported alongside the integer-ranked primary; it decides nothing.

### 1.3 SECONDARY — `M_max`, sparse-alternative statistic
```
M_max = max_a | n·FF_a − rowF_a·colF_a |
```
Ranked against the **same** `B` permutation draws (the null draw computes the same max, so it is
exactly calibrated). Aimed at the alternative "a few `a` decouple strongly while most do not" — the
pooled `D_int` has low power against a single outlier among `K`. **This is the pre-registered
"what if the effect lives in a subspace we are not projecting onto" arm** (here: sparsity in `a`).

### 1.4 SECONDARY — `θ̄`, pooled mean log-odds across `a`
Inverse-variance-weighted mean of `θ_a`; integer companion `Σ_a (n·FF_a − rowF_a·colF_a)` ranked vs
the same `B` draws. Because different `a` give largely independent flap partitions of the **same**
points, this aggregates toward an effective sample far beyond the prior single-`a` run and yields a
**tighter universal-`θ` bound** (§5). Disclosed: this is **not** an independent replication of the
prior null — same pool, relabelled flap sets.

### 1.5 EXPLORATORY — arithmetic structure of `θ_a` (characterization, no `α` spent)
Stratify `θ_a` by pre-listed **`μ₆`-invariant** invariants of `a`:
`enorm(eis_p(a))` bucketed into deciles; `min bit_length` over the `μ₆`-orbit of `a`.
**`legendre(a,p)` and `χ₃(a)` are EXCLUDED by name**: `p ≡ 3 mod 4` gives `legendre(−1,p) = −1`, so
`legendre` is not `μ₆`-invariant and is ill-defined on the effective `a`-space; likewise
`χ₃(βa) ≠ χ₃(a)` in general. ARM-0 verifies the `μ₆`-invariance of each stratifier by exact integer
check before it is used; a stratifier failing that check is dropped and the drop is disclosed.

### 1.6 DISCARDED statistics (named, §0.4): per-`a` marginal density (T-i); any tally counting
`μ₆`-conjugate `a` separately (T-ii); comparison to the analytic stationary matrix (T-iii);
max-over-`a`-and-over-`n` composite scores; any statistic computed on `a` values selected after
seeing `θ_a`.

---

## 2. MATCHED CONTROL

**The null must reproduce every structure the real data has except the arithmetic pairing.**

**Null-P (PRIMARY, joint conditional permutation).** Precompute two `K × n` label matrices
`DOM[a,i] = ε_a(X_i)` and `IMG[a,i] = ε_a(x2(X_i))`. For each null draw `b`, take **one** uniform
permutation `σ_b` of `{1..n}` and apply it **simultaneously to every row** of `IMG`:
`IMG_b[a,i] = IMG[a, σ_b(i)]`. Recompute all `K` tables.
- **PRESERVES exactly:** every per-`a` margin `rowF_a` and `colF_a` (integers, unchanged); the real
  `ε_a` classifier including its `μ₆`-invariance in **both** arms (no null-symmetry mismatch); the
  shared-pool cross-`a` coupling (the same `σ_b` for all `a`, exactly mirroring the fact that all `a`
  read the same points); `K`; `n`; the flap partition geometry.
- **DESTROYS only:** the pairing `X_i ↔ x2(X_i)` — precisely the arithmetic link under test.
- This is the per-`a` hypergeometric null of `flap_grouplaw_transition_v1.py` lifted to the joint
  across-`a` statistic; it is exact and needs no independence assumption between `a` values.
- `B = 9999`. Min attainable `p = 10⁻⁴ < α* = 1/60` ✓.

**Null-I (cross-check, compute-permitting).** `K_I = 4` **disjoint** pools of `n_I` points each, so
that the `θ_a` are genuinely independent and the `χ²_{K−1}` reference applies without the shared-pool
caveat. Confirms Null-P is not inheriting a shared-pool artifact.

**Why the naive alternative was rejected (stated so the choice is not made later):** replacing the
image by an independent uniform point (parent prereg's Control B) would require `B` fresh pools of
`n` valid abscissas — `B·2n` modular exponentiations, infeasible at `B = 9999`. Null-P attains the
same conditional null at permutation cost. Control-B-style independent-image draws are retained as a
single sanity realization only, not as the null.

**BANNED nulls:** (i) shuffling `a` (destroys nothing — `a` is not paired to anything); (ii) any null
that re-draws points, which would break the margins the readout has by definition; (iii) permuting
`DOM` and `IMG` with **different** permutations per `a` (destroys the shared-pool coupling that
exists under the true null ⇒ inflated dispersion ⇒ exactly the "null-mismatch artifact" failure).

---

## 3. PLANTED CONTROLS (each must fire, or the named arm is VOID)

- **PC-max (inherited, per `a`).** Image map `X ↦ βX`; `ε_a(βX) = ε_a(X)` ⇒ forced diagonal
  `CF_a = FC_a = 0`. **Must hold for all `K` values of `a`.** Fail ⇒ VOID.
- **PC-id (forced `μ₆` collapse — the `a`-axis detector gate, zero extra cost).** For every sampled
  `a`, the full 2×2 for `a` and for `(β·a) mod p` must be **cell-by-cell identical** (forced by T-ii,
  and by `D_{βa} = D_a`). Any exception ⇒ the `a`-machinery is broken ⇒ **VOID**.
- **PC-dep-arith (the required `a`-DEPENDENT plant; curve-native, no injected labels).** Choose
  `A_plant ⊂ {sampled a}` with `|A_plant| = K/4`. For `a ∈ A_plant` use image map `X ↦ βX`
  (forced diagonal); for `a ∉ A_plant` use the real `x2`. This makes `θ_a` genuinely, maximally, and
  arithmetically `a`-dependent. **`D_int` and `M_max` must both fire at `α*`.** Fail ⇒ the dispersion
  test cannot see `a`-dependence ⇒ **VOID the whole experiment.**
- **PC-dep-α (tunable, gives the §5 threshold).** Independence background; for `a ∈ A_plant` force
  the image label equal to the domain label on the first `m = ⌊αn⌋ ` indices. Analytic effect:
  `δ = P(F|F) − ¼ = 3α/4`, `θ_plant ≈ 4α`, and with `h = |A_plant|`,
  `τ² = (h/K)(1 − h/K)(4α)²`. Sweep `α ∈ {2^{-k} : k = 3..12}`, `h ∈ {1, K/4, K}`, 100 reps.
  **Report the smallest firing `α` (empirical power ≥ 0.8) and check it matches the analytic `τ_min`
  of §5. That number must be printed with every null this experiment produces.**
- **PC-dep-NEG (proves the statistic measures heterogeneity, not a mean shift).** The `h = K` cell of
  the sweep plants the **same** `θ` in every `a` ⇒ zero dispersion. **`D_int` must NOT fire at
  `h = K` while `θ̄` (§1.4) MUST fire.** If `D_int` fires at `h = K`, it is reading a common shift,
  i.e. a proxy, and is VOID as a dispersion statistic.
- **PC-FP (false-positive gate).** 100 pure Null-P realizations through the full pipeline; empirical
  firing rate for `D_int` must be `≤ 2α* = 1/30`.
- **DISCLOSED POWER LIMIT (design boundary, stated now).** There is no cheap curve-native *weak*
  `a`-dependent coupling to plant. PC-dep-arith exercises the **maximal** `a`-dependence; PC-dep-α
  calibrates the **threshold** via label forcing. Neither exercises a weak *arithmetic* `a`-coupling
  between distinct abscissas. Any null must carry this sentence.

---

## 4. ARM 0 — GATE (deterministic; any failure ⇒ VOID, no verdict)
- **G1** `check_no_float.sh` passes on `flap_a_invariance_v1.py`.
- **G2** `μ₆`-invariance, ZERO exceptions: `ε_a(X) = ε_a(βX) = ε_a(β²X) = ε_a((p−X))` over
  `n_g = 2¹⁶` gate abscissas (`random.Random(20260721)` + QR filter), **for every sampled `a` and
  for `a₀`**.
- **G3** quarter density per `a`: `|4·nf_a − n_g| ≤ 6·isqrt(3·n_g)` for every sampled `a`.
  Additionally print the density under the *signed* classifier form for the §0.1 record.
- **G4** PC-id holds with 0 exceptions on the full pool.
- **G5** `x2` correctness: for 1000 pool points, `x2(X)` equals the x-coordinate of `2P` from an
  independent affine point-doubling routine. (The entire experiment rides on the quartic formula.)
- **G6** `μ₆`-orbit distinctness of the sampled `a`: no two sampled `a` lie in a common orbit
  `{±a, ±βa, ±β²a}` (exact integer check). **Distinct configuration count = `K`, and only that
  number may appear in a `k/k` tally.**
- **G7** stratifier `μ₆`-invariance check (§1.5); non-invariant stratifiers dropped and disclosed.

---

## 5. POWER (computed now)

Per-`a` variance of the log-odds under margins `(¾, ¼)`:
`V = (1/n)(16/9 + 16/3 + 16/3 + 16) = 256/(9n)`, `√V = 16/(3√n)`.

**Allocation reasoning (the requested trade-off, resolved before the run).** With the Null-P design
the expensive work — `2n` QR modular exponentiations (148 µs each, measured) and `n` quartic
exponentiations for `x2` — is paid **once**, shared by all `a`; only the `ε` evaluations
(`2Kn` modular multiplications, ≈ 3 µs per `ε`) scale with `K`. At fixed `ε`-budget `Kn`,
`τ_min ∝ K^{1/4}/√(Kn)`, so **small `K` minimizes `τ_min`**: at `Kn = 3.2·10⁷`, `K = 8` gives
`τ_min = 3.5·10⁻³` vs `K = 32` giving `4.8·10⁻³` — a factor 1.4. That factor is traded for a 4×
better sample of the effective `a`-space `(ℤ/p)*/μ₆`, because the alternative of interest (`M_max`,
§1.3) is **sparse in `a`** and a `K = 8` sample would miss a sparse decoupling entirely.

**PRE-COMMITTED ALLOCATION: `K = 32`, `n = 10⁶` (shared pool), `B = 9999`.**

| statistic | detectable effect at `α* = 1/60`, power 0.8 | in `P(F|F)` units |
|---|---|---|
| `D_int` (dispersion, 1-sided) | `τ_min = 0.868·√V = 4.6·10⁻³` (SD of `θ_a` across `a`) | `8.7·10⁻⁴` |
| `θ̄` (pooled mean, 2-sided) | `3.05·10⁻³` (`SE = √(V/K) = 9.4·10⁻⁴`) | `5.7·10⁻⁴` |
| `M_max` (single decoupled `a`) | `\|θ_a\| ≥ 2.3·10⁻²` | `4.3·10⁻³` |

**Calibration against the completed run.** The prior single-`a` T1 at `n = 10⁶` had
`δ_min ≈ 3.4·10⁻³`, i.e. `θ`-resolution `≈ 1.8·10⁻²`. This design resolves **`a`-to-`a` dispersion at
`4.6·10⁻³`, ~4× finer than the prior run could resolve a mean shift at a single `a`** — so if the
true `θ_a` varied across `a` by as much as the prior run's own detection floor, this test sees it at
≈ 15 standard deviations. That is the justification for the allocation.

**Compute (from measured primitives).** pool `2·10⁶` QR modexps ≈ 300 s; `10⁶` quartic modexps + one
batch inverse ≈ 5 s; `2Kn = 6.4·10⁷` `ε` evaluations ≈ 190 s; PC arms ≈ 200 s; `B = 9999` Null-P
draws on `numpy uint8` `32 × 10⁶` matrices (gather + AND + row-sum ≈ 0.1 s/draw) ≈ 17 min.
**Total ≈ 30 min.** If wall-clock exceeds 60 min, the pre-committed fallback is `B = 1999`
(min `p = 5·10⁻⁴ < α*`), taken as a **disclosed deviation**, never silently.

**SECONDARY arm (few-`a` / large-`n`), pre-committed, compute-conditional:** `K_I = 4` (the **first
four** sampled `a`, fixed in advance — no post-hoc selection), `n = 10⁷`, disjoint pools (Null-I).
`τ_min = 1.56·√(256/(9·10⁷)) = 2.6·10⁻³`. Cost ≈ 1 h (dominated by `2·10⁷` QR modexps). **If this arm
is not run, that is a disclosed deviation naming the arm — not a silent filter.**

**Multiplicity.** Family counted now = **3** cells: `{D_int, M_max, θ̄}`. `α* = 0.05/3 = 1/60`.
`§1.5` stratifications and the Null-I cross-check spend no `α` and are labelled EXPLORATORY.

---

## 6. SCOPE

### 6.1 Sampling distribution for `a` (fixed now; answers "is `a = 1` a valid draw?")
`SEED_A = 20260723`, `random.Random(SEED_A)`. Draw `a` uniform on `[1, p−1]`; **reject** if:
(i) `a = 0`; (ii) `bit_length(a) < 200`; (iii) the `μ₆`-orbit `{±a, ±βa, ±β²a}` intersects an
already-accepted value. Continue to `K = 32` accepted values.
- **`a = 1`, `a = 2`, `a = 3` are EXCLUDED from the confirmatory sample** by filter (ii). Rationale
  fixed now: they are not draws from the intended uniform law, they are arithmetically special
  (`a` small ⇒ `aX` un-reduced for small `X`), and admitting them would let a structured point drive
  a dispersion statistic. Filter (ii) is a **pre-registered** filter, applied before any statistic.
- **`a₀ = extract_a()` (the CM-basis value used by the completed run) is EXCLUDED from the
  confirmatory sample because it has been SEEN.** It appears only in the reference panel.
- **REFERENCE PANEL (EXPLORATORY, reported separately, NOT in `D_int`/`M_max`/`θ̄`):**
  `a ∈ {1, 2, 3, ρ, β, ρ+1, a₀}`. If a panel value is an outlier relative to the confirmatory
  distribution of `θ_a`, that is reported as a **characterization requiring its own confirmatory
  test**, never as a confirmatory result of this run.

### 6.2 Fixed
Curve secp256k1 full scale; `(ρ, β)` as in `flap_grouplaw_transition_v1.py`; classifier =
absolute-value form (§0.1); pool = `n = 10⁶` valid abscissas from `random.Random(424242)` + QR
filter, guards skipping 2-torsion (`x2` denominator 0) and 3-torsion (`x2(X) = X`), resampled until
**exactly** `n` valid pairs so that `n` is identical for every `a`; `B = 9999`; `α* = 1/60`;
`n_g = 2¹⁶`; `K = 32`; family size 3.

### 6.3 Untested — a null here excludes none of these (stated now, restated on every null)
(i) the full Eisenstein/Dedekind rhombus position, of which `ε` is a **1-bit projection**;
(ii) `ν_π` / lattice class; (iii) higher iterates `x(2^k P)`, `k ≥ 2`, and `x(mP)`, `m > 2`;
(iv) `≥ 3`-point joints; (v) `ε` coupled to `y`; (vi) `a` with `bit_length < 200` (excluded by the
pre-registered filter); (vii) any `a` outside the sampled 32 orbits — the effective `a`-space has
`(p−1)/6 ≈ 2²⁵³` elements and 32 draws bound the **typical** `a`, not every `a`.

---

## 7. FALSIFICATION (the three requested verdicts, written before the run)

Let all gates (§4) pass, PC-max and PC-id hold with 0 exceptions, PC-dep-arith fire, PC-dep-NEG
behave (`D_int` silent at `h = K`, `θ̄` firing), and PC-FP pass. Then:

- **"THE NULL WAS `a`-SPECIFIC"** ⟺ `D_int` fires (`p ≤ 1/60`), **or** `M_max` fires.
  Meaning: `θ_a` is heterogeneous; the completed single-`a` T1 null was a property of `a₀`, not of
  the `ρ`-lattice. Required output: the per-`a` `θ_a` table, which `a` are outliers, the §1.5
  stratification, and the pre-committed follow-up (§8).
- **"CONSISTENT WITH `a`-INVARIANCE AT THIS RESOLUTION"** ⟺ `D_int` and `M_max` both null.
  Reported as: *dispersion of `θ_a` across 32 uniform `μ₆`-distinct `a` (bit_length ≥ 200) is bounded
  by `τ < 4.6·10⁻³` (log-odds SD; `8.7·10⁻⁴` in `P(F|F)`), and no single sampled `a` deviates by
  `|θ_a| ≥ 2.3·10⁻²`, at `n = 10⁶` per `a`, power 0.8, `α* = 1/60`, secp256k1, 1-bit `ε`,
  absolute-value classifier form, PC-dep-α floor = [printed], §6.3 untested list.*
  **This is a scoped magnitude bound over a sample of `a`. It is NOT a proof of rigidity.**
  The words **"the null is forced"** and **"the `ρ`-lattice is rigid"** are **reserved for an
  analytic derivation** — e.g. a proof that `⟨1_{S_1}, 1_{S_1} ∘ D_a⟩` is independent of `a` — and
  **this experiment cannot produce them.** The permissible upgrade over the completed run is exactly:
  *"the T1 null is not an artifact of the single `a₀`; it holds uniformly over a 32-point sample of
  the effective `a`-space at 4× finer resolution."* Nothing wider.
- **VOID** ⟺ any of: G1–G7 fails; PC-max fails for any `a`; PC-id has ≥ 1 exception;
  PC-dep-arith fails to fire; `D_int` fires under PC-dep-NEG at `h = K` (statistic is reading a mean
  shift, i.e. a proxy); PC-FP firing rate `> 1/30`. **A VOID arm produces no verdict of any kind.**

---

## 8. PRE-COMMITTED OUTCOME TABLE

| Cell | Outcome | Pre-committed conclusion |
|---|---|---|
| **`D_int` (PRIMARY)** | FIRES, all PCs good | **The doubling 2×2 is `a`-DEPENDENT.** The completed single-`a` T1 null was `a₀`-specific. Report `τ̂`, the full `θ_a` table with signs, the outlier `a`, and the §1.5 stratification. **NEXT PROBE (fixed now): re-run T1 at the two extreme `a` with `n = 10⁷` (`δ_min ≈ 1.1·10⁻³`) as an independent confirmatory test; and test whether `θ_a` is a function of a `μ₆`-invariant of `a`.** Do not report a "break". |
| **`D_int`** | NULL, `M_max` NULL, all PCs good | **Scoped magnitude bound** exactly as worded in §7 bullet 2, with power, `τ` bound, PC-dep-α floor, and the §6.3 untested list in the same paragraph. Explicitly: *not* "rigid", *not* "forced", *not* "closed", *not* "avenue dead". |
| **`D_int`** | NULL, **`M_max` FIRES** | **Sparse `a`-dependence.** Most `a` are homogeneous; ≥ 1 decouples. Report which `a`, its `θ_a`, its `μ₆`-orbit representative, its `enorm(eis_p(a))` decile. **NEXT PROBE: `n = 10⁷` at that `a` plus 31 fresh `a` drawn from the same stratum** — a new pre-registration, not an extension of this one. |
| **`D_int`** | FIRES, **`M_max` NULL** | Diffuse `a`-dependence (many small deviations rather than one outlier). Report `τ̂` and the `θ_a` distribution shape; test whether `θ_a` correlates with a §1.5 invariant. |
| **`θ̄` (SECONDARY)** | FIRES | A **universal** doubling→flap coupling exists that the prior single-`a` run at `δ_min = 3.4·10⁻³` could not resolve. Report `θ̄`, its **SIGN** (`+` = flap→flap resonance, `−` = anti; both are structure), magnitude, and the shared-pool caveat (§1.4). Confirm at the Null-I arm before any further claim. |
| **`θ̄`** | NULL | Universal-`θ` bound tightened from the prior `δ < 3.4·10⁻³` to `δ < 5.7·10⁻⁴` (`P(F|F)`), power 0.8, `α* = 1/60`, `K = 32`, `n = 10⁶`, shared pool. A **bound**, with §6.3 attached. |
| **Null-I cross-check** | agrees / disagrees with Null-P | Agreement ⇒ the shared-pool coupling is not driving Null-P. Disagreement ⇒ **report both**, treat Null-P as suspect, and do not issue a verdict until reconciled. |
| **Reference panel** | `a₀`/small `a` outlying | EXPLORATORY characterization only. **May not be merged into any confirmatory tally** and may not be used to reinterpret the confirmatory cell. Requires its own pre-registration. |
| **PC-id** | any exception | **VOID.** The `a`-machinery does not respect the forced `μ₆` collapse ⇒ implementation bug. |
| **PC-dep-arith** | does not fire | **VOID.** The dispersion test cannot detect `a`-dependence it was handed; the null is uninformative — full stop. |
| **PC-dep-NEG** | `D_int` fires at `h = K` | **VOID.** `D_int` is reading a common mean shift, i.e. a **proxy** for the intended object. Replace the statistic and re-register. |
| **G1–G7** | any fail | **VOID.** No verdict of any kind. |

**Tally discipline.** Any `k/k` figure must use **distinct `μ₆`-orbit configurations** (`K = 32`),
never raw `a` draws, and must exclude forced cells (PC-id agreements are forced by T-ii and carry
zero information about `a`-dependence — they are a gate, not evidence).

---

## 9. EXACTNESS (repo rule: `btc_puzzle_investigation/CLAUDE.md`)

- **`check_no_float.sh` must pass before any statistic is computed** (gate G1).
- **Signal path — 100% `int`:** `cent`; the `ε` threshold as `2·|·| > p` (integer comparison, never
  `p/2`); QR test `pow(·,(p−1)//2,p)`; `x2 = ((pow(X,4,p) − 56·X) · pow(4·((X³+7)%p)%p, p−2, p)) % p`;
  batch inverse (`pow(·, p−2, p)`); `βX % p`; all 2×2 counts; `D_int`; `M_max`; the pooled integer
  companion of `θ̄`; every permutation rank `p = (1 + #{·})/(B+1)` compared to `α* = 1/60` by integer
  cross-multiplication; the `μ₆`-orbit distinctness check; `isqrt` in G3.
  **The PRIMARY decision path contains no float.**
- **Named float carve-out:** `θ_a`, `τ̂`, `V`, the `χ²` reference, and the §1.5 decile bucketing.
  Justified as monotone/analytic reporting quantities computed **from integer counts already fixed**,
  ranked against the integer permutation ensemble; **no key, coordinate, or classifier input passes
  through a float**, and no threshold is applied to a float. Matches the repo's existing MI/`G²`
  carve-out.
- **Banned:** `/`, `float(...)`, `round(...)`, `**0.5`, `math.*`/`np.*` applied to any
  key/coordinate/classifier value. `numpy` is used only on `uint8` label matrices (permutation gather,
  bitwise AND, row sums) — integer operations on already-computed 0/1 labels.
- **Ordering enforcement:** the `K = 32` values of `a` are drawn from `SEED_A` and written to
  `a_sample_v1.txt` with its SHA-256 recorded **before** the pool is generated; `A_plant` for
  PC-dep-arith is fixed as the first `K/4` entries of that file. No `a` may be added, removed, or
  reordered afterwards.
