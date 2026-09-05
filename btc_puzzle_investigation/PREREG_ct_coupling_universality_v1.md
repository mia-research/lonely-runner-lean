# PRE-REGISTRATION — C_T inter-coordinate coupling: universal constant, or noise floor? — v1

**Written 2026-07-19, BEFORE any sweep data is seen.** This is a test specification, not a result.
It fixes the statistic, control, power, scope, exactness, and both falsification branches in advance,
so no exponent / threshold / subset can be chosen after looking. Post-run, audit the run against this
file; every deviation must be disclosed, whether or not it is wrong.

Prior art READ before writing this spec (not taken on summary):
`ANOMALY_DRILL_01_CT_SPLIT_v1.md`, `_anomaly_drill_ct_split_v2.py`, `ct_coupling_universality_v1.py`,
`lift_sextant_rhombus_law_proof_v2.py`, `check_no_float.py`.

---

## 0. VERDICT ON THE EXISTING SCRIPT (`ct_coupling_universality_v1.py`) — why its stat and logic are replaced

Both the statistic and the verdict logic of the existing not-yet-run script are **inadequate given
DRILL 01's finding**, for two independent reasons. This section is the load-bearing correction; the
rest of the spec implements it.

- **Its statistic `max|T_j − T_f|` is a noise-floor magnitude, not a coupling magnitude.** DRILL 01
  measured exactly this quantity against a zero-coupling matched surrogate and got `0.02751` real vs
  `0.02256 ± 0.00311` surrogate, **z = +1.59** — i.e. the surrogate (coupling-free BY CONSTRUCTION)
  reproduces ~82% of it and all of it within ~1.6σ. A max over 81 noisy cells is upward-biased and
  low-power; it tracks estimation noise on a 9×9 operator, which is the floor. It does **not** track
  the coupling. **REPLACED** (see §2) by a surrogate-normalized, pooled statistic aimed at the
  factorization, plus its swap-channel decomposition aimed at where the ⅓-degeneracy actually splits.

- **Its verdict rule "~constant dev across generators & primes ⇒ universal geometric coupling" is
  invalid — it is the DRILL-01-v1 trap re-armed.** A *universal NOISE FLOOR* is ALSO ~constant across
  generators and primes at fixed sample count `n`, because the floor is a universal function of `n`
  alone (`dev_surrogate ~ n^(−0.58)` in the drill, generator/prime-independent). So "constant dev"
  is equally consistent with a real universal coupling AND with universal estimation noise — it
  **discriminates neither**. Reading it as coupling is precisely how the v1 pass read `p^(−0.36)` (two
  junk rows) as "intermediate, therefore interesting." **REPLACED** (see §7) by the **n-SCALING of the
  surrogate-normalized statistic** (a floor is flat / ratio→1; a real coupling grows), and by the
  **cross-cell constancy of the IMPLIED COUPLING ε̂** (not of the raw dev).

`max|T_j − T_f|` is retained in the run **only** as a descriptive reproduction of the drill's floor
(to confirm we see the same ~2.7% and the same surrogate cloud). It is never a universality
discriminator here.

---

## 1. OBJECT

The mathematical object is the **inter-coordinate coupling of the 9×9 addition-rounding Markov
operator `C_T`** on the state `(c₁,c₂) ∈ {−1,0,1}²`, for the fixed-step orbit `d ↦ [d]G` on
`E: y² = x³ + 7` over `F_p` (`p ≡ 1 mod 3`, prime order, so CM by `Z[ω]`, `j=0`). The coupling is the
departure of `C_T` from the tensor square `C_1 ⊗ C_1` of its coordinate marginals — equivalently the
lifting of the doubly-degenerate eigenvalue `⅓` (eigenvectors `v⊗u`, `u⊗v`) into `λ₂ ≠ λ₃`.

We measure the coupling itself — the factorization defect `D = C_T − T̂₁ ⊗ T̂₂` and its swap-parity
channels — **not** a proxy for it. Two tautology guards, stated now:
- **Feature/target are NOT co-constructed.** The marginals `T̂₁, T̂₂` are estimated from the SAME
  sequence as the joint `Ĉ_T`. A raw `Ĉ_T − T̂₁⊗T̂₂` therefore carries a finite-`n` estimation defect
  even under perfect factorization (the coordinates share one sample path). This shared-construction
  bias is exactly why a **matched surrogate that reuses `T̂₁, T̂₂` at the same `n`** — not an analytic
  `χ²₁₆` p-value alone — is the null (§3). Reporting `χ²` significance without the surrogate would be
  the invalid move.
- The degeneracy split `|λ₂−λ₃|` is a downstream readout of the SAME `D`; DRILL 01 showed it is the
  lowest-power view of it (`z=+0.13`). It is reported for continuity, never as the decision statistic.

---

## 2. STATISTIC (exactly one primary, named now; two corroborating; distribution under the null)

Per cell = per `(generator, prime, n)`:

**PRIMARY — surrogate-normalized pooled factorization statistic `z_G²`.**
1. From exact **integer** transition counts, form the 9 source-conditional 3×3 count tables
   `N_s[c₁',c₂']` (`s` = source state, rows over the 9 states, entries = counts of the next state).
2. `G²_real = 2 · Σ_s Σ_{c₁',c₂'} N_s · ln( N_s / Ê_s )`, the pooled likelihood-ratio statistic for the
   hypothesis that, within each source state, the two next-coordinates are independent
   (`Ê_s[c₁',c₂'] = rowmarg₁ · rowmarg₂ / total_s`). Pooled df = `9 × (3−1)(3−1) = 16`.
   **Distribution under the tensor null:** `G² ~ χ²₁₆` asymptotically (mean 16, sd `√32 ≈ 5.66`),
   plus a finite-`n`/shared-path bias which the surrogate carries.
3. Draw `M = 40` matched surrogates (§3), recompute `G²` on each → `{G²_surr}`.
   `z_G²(cell) = ( G²_real − mean(G²_surr) ) / std(G²_surr)`.

Why `z_G²` tracks the coupling and not the floor: under the tensor null both `G²_real` and every
`G²_surr` are draws from the same (χ²₁₆ + identical finite-`n` bias) law, so the floor cancels in the
numerator and `z_G² ~ N(0,1)` at every `n`. Under a true coupling of magnitude `ε` (def. below) the
factorization is non-central: `E[G²_real] = 16 + n·ε²`, while every `G²_surr` stays null at `16`; so
`E[z_G²] ≈ n·ε² / 5.66` — it **grows with `n`** (slope `+1` in `log z` vs `log n`). Floor → flat;
coupling → rising. This is the discriminator the existing script lacked.

**HEADLINE DERIVED MAGNITUDE — bias-corrected implied coupling `ε̂` (in coupling units, comparable
across cells).** `ε̂(cell) = sqrt( max(0, G²_real − mean(G²_surr)) / n )`. Under the null,
`G²_real − mean(G²_surr)` fluctuates around 0, so `ε̂ ~ n^(−1/2)` (**decreasing**). Under coupling,
`ε̂ → ε` (**flat**, `n^0`). Its scaling exponent is the physical-units restatement of `z`'s: **−0.5 =
floor, 0 = universal constant** — directly parallel to the drill's `dev_real ~ n^(−0.596)` vs
`dev_surrogate ~ n^(−0.584)` (both ≈ −0.5 = floor). `ε` is defined as this pooled RMS
factorization-breaking amplitude per transition (`ε² = λ_nc/n`), a **pooled** (not max-over-cells)
magnitude, so equal `ε̂` across cells is the meaningful "same geometric constant" signature.

**CORROBORATING — swap-parity-targeted Frobenius statistic (guards the "effect in an unprojected
subspace" failure).** The ⅓-degeneracy splits along the coordinate-swap `S:(c₁,c₂)→(c₂,c₁)` (matrix
`SW`). Decompose `D = Ĉ_T − T̂₁⊗T̂₂` into `D_even = ½(D + S D S)`, `D_odd = ½(D − S D S)`. Report
`‖D_odd‖_F` and `‖D_even‖_F`, each normalized by its surrogate: `z_odd, z_even` (same 40-draw
recipe). `‖D_odd‖_F` is a low-dimensional statistic aimed at the exact direction the degeneracy
splits — `n^(−1/2)` power instead of a max over 81 cells. **Rule (subspace guard):** if the omnibus
`z_G²` is flat but `z_odd` (or `z_even`) rises with `n` and reaches ≥5 at `n_max`, that IS a coupling
living in that swap channel — it must be reported as such, NOT buried under the omnibus null.

Float carve-out for §2: eigenvalues (`np.linalg.eig`), the `ln` inside `G²`, Frobenius norms, and the
mean/std z-normalization are analytic magnitudes / a monotone statistic ranked against the matched
null. None defines a state and none is a threshold applied to raw data. See §8.

---

## 3. MATCHED CONTROL / NULL

**Surrogate = independent-coordinate walk with EXACTLY the measured marginals at the same length `n`**
(`surrogate()` in `_anomaly_drill_ct_split_v2.py`): estimate `T̂₁, T̂₂` from the real sequence, then
generate two INDEPENDENT Markov walks of length `n` with transition matrices `T̂₁` and `T̂₂`, and pair
them coordinate-wise. `M = 40` independent draws per cell (pre-committed; the z-denominator is the
sample std of the 40 `G²_surr`; 40 estimates the surrogate mean to ≈ 0.16σ). RNG seed fixed
**20260719**, stated here so nothing is drawn after seeing data.

- **PRESERVES:** each coordinate's marginal transition operator `T̂₁, T̂₂` (hence each marginal
  spectrum `{1,⅓,1/9}`, row sums, stationary occupancy) AND the finite-`n` estimation noise on each
  coordinate AND the shared-length `n`.
- **DESTROYS:** only the inter-coordinate dependence — the joint next-state is forced to be the
  product of its marginals. This is the *precise* null for the tensor-square hypothesis: the one
  structure under test (coupling) is removed and nothing else is.

This is a valid null (unlike a plain shuffle): it does not destroy any symmetry the readout has by
construction. It reproduces every finite-`n` artifact of `Ĉ_T − T̂₁⊗T̂₂` except the coupling, which is
why the drill's `max|·|` and `|λ₂−λ₃|` both came back `z≈0` against it.

---

## 4. PLANTED CONTROL (positive control; the null is uninformative unless this fires as predicted)

Inject a **known coupling of known size** into the surrogate and require the statistic to fire exactly
where §5's power table says it must. Construct a coupled joint operator
`T_couple(δ) = (1−δ)·(T̂₁⊗T̂₂) + δ·K`, `K` a stochastic coupling kernel (given source `(c₁,c₂)`, draw
`c₁'~T̂₁[c₁,·]` and set `c₂' = c₁'` — a copy-coupling), generate a length-`n` sequence from
`T_couple(δ)`, run the full §2 pipeline. `δ` maps to `ε` by `ε ≈ δ·‖K − T̂₁⊗T̂₂‖` (measured and
reported so the plant's `ε` is known, not assumed). Also run a **swap-odd-only** plant (antisymmetrize
`K` about `S`) and a **swap-even-only** plant, to confirm channel localization.

**Pass conditions (pre-committed; all must hold):**
- Plant `ε ≈ 2%`, `n = 131072`: `z_G² ∈ [7, 12]` (predicted ≈ 9.3) — **FIRES**.
- Plant `ε ≈ 2%`, `n = 5000`: `z_G² < 2` — **CORRECTLY SILENT** (below the power floor).
- Plant `ε ≈ 1%`, `n = 131072`: `z_G² ∈ [1.5, 3.5]` (predicted ≈ 2.3) — **borderline, as predicted**.
- Plant `ε ≈ 0.5%`, `n = 131072`: `z_G² < 1.5` — **CORRECTLY SILENT** (needs `n ~ 10⁶`).
- Swap-odd plant loads `z_odd` (not `z_even`); swap-even plant loads `z_even` (not `z_odd`).

**If the planted control does not fire/localize as above, the null is uninformative — FULL STOP.** No
floor claim may be made from a pipeline whose positive control did not fire at the predicted `n`.

---

## 5. POWER (computed now, not after)

Pooled factorization test, df = 16, α = 0.05, critical `χ²₁₆ = 26.30` (0.01: 32.00; 0.001: 39.25).
Non-centrality `λ_nc = n·ε²`. Detection threshold `λ* = 24` gives **80% power** at α=0.05 (headline);
`λ* = 30` gives ≈94% (the drill's implicit `√(30/n)`). Minimum detectable coupling
`ε_detect(n) = sqrt(λ*/n)`:

| n | ε_detect @80% (λ=24) | ε_detect @94% (λ=30) | in scope (p ≤ 2¹⁷)? |
|---:|---:|---:|:--|
| 5,000 | 6.9% | 7.7% | yes |
| 20,000 | 3.46% | 3.87% | yes |
| 50,000 | 2.19% | 2.45% | yes |
| 100,000 | 1.55% | 1.73% | yes |
| **131,072 (=2¹⁷, largest full orbit)** | **1.35%** | **1.51%** | **yes — this is the in-scope floor** |
| 240,000 | 1.00% | 1.12% | NO (needs p≈2¹⁸) |
| 1,000,000 | 0.49% | 0.55% | NO (needs p≈2²⁰) |
| 24,000,000 | 0.10% | 0.11% | NO (needs p≈2²⁵) |

**n at which each named target becomes detectable (80% power):** 2.0% → `n ≥ 60,000` (**in scope**,
top half of the prime range); 1.0% → `n ≥ 240,000` (**out of scope**, p≈2¹⁸); 0.5% → `n ≥ 960,000`
(**out of scope**, p≈2²⁰); 0.1% → `n ≥ 2.4×10⁷` (**out of scope**, p≈2²⁵).

**Hard power consequence, pre-stated:** within `p ≤ 2¹⁷` this sweep resolves couplings **≥ ~1.35%**
(at the largest full orbit) down to ~2% (mid-range). It has **no power below ~1.35%**, and **zero
power at 2²⁵⁶**. A coupling that switches on below this floor, or only near cryptographic size, is
**not tested here** and must not be reported as excluded (§7 floor branch, §9).

---

## 6. SCOPE (inherited by every number the run produces; never stated without it)

- **Curve family:** `b = 7` ONLY (`y²=x³+7`, `j=0`, CM by `Z[ω]`). Nothing here speaks to `b ≠ 7`.
- **Primes (Axis 2):** `p ≡ 1 mod 3`, `p` prime, **`#E(F_p)` prime** (prime-order ⇒ full orbit
  `n = #E ≈ p`, the drill-v2 requirement — NOT the existing script's weaker "walk G till it closes",
  which admits sub-group orbits). Range `p ∈ [~2×10³, 2¹⁷]`. Select ≥ 8 prime-order curves whose
  orbit lengths are ≈ **log-spaced** over `[5000, 131072]` (targets ~5k,10k,20k,40k,80k,131k), with
  **≥ 2** curves within a factor √2 of the top to anchor the large-`n` end.
- **Anti-defect guards (the v1 pass failed exactly here):** (a) **log EVERY candidate `p`** with its
  `#E`, whether `#E` is prime, and the include/exclude reason — no silent filter (v1 silently cut 8→3
  on `p%3==1`). (b) **Inclusion floor `n ≥ 5000`** (χ²₁₆ asymptotics + ≥ a few expected counts on the
  occupied cells); cells below it are excluded WITH REASON, never fitted (v1 let `n=146`, `n=3353`
  junk rows dominate a scaling fit). (c) The scaling fit is over cells as equal points in
  `(log n, statistic)` — no count-weighting, so one huge orbit cannot dominate.
- **Generators (Axis 1):** at fixed `p = 100003`, step generators `[h]G` for **8 distinct `h`** drawn
  by the fixed RNG (seed 20260719), each with `gcd(h, #E) = 1` (so `[h]G` generates), **fixed window
  `n = 50000`** across all 8 (isolates the generator effect at fixed `n`). Log every `h`.
- **Fixed-`n` cross-prime check (Axis 2b):** on each Axis-2 prime take an `n = 20000` window; compares
  primes at equal `n` to separate "prime-specific" from "`n`-driven".
- **Estimator:** pooled `G²` (16 df) + swap-parity Frobenius, surrogate-normalized (§2). NOT
  `max|·|` (retained descriptively only). Surrogate: 40 draws/cell (§3).
- **This is a `2¹⁷`-scale measurement.** State it on every reported number.

---

## 7. FALSIFICATION — both directions, pre-committed, non-reinterpretable

Decision gate at the **largest in-scope orbit** `n_max ≈ 131072`, with `Z* = 5` (well beyond
family-wise multiplicity over ~26 cells, and matching the plant's 2%-fires prediction).

**BRANCH A — UNIVERSAL NONZERO COUPLING** (hypothesis confirmed as a geometric constant). Requires ALL:
- (A1) `z_G²` **grows with `n`**: slope of `log z_G²` vs `log n` (Axis-2 full orbits) `≥ +0.5`
  (null slope 0; coupling slope ≈ +1), AND `ε̂` vs `n` slope `≥ −0.2` (i.e. NOT the `−0.5` floor).
- (A2) At `n_max`: `z_G² ≥ 5` AND raw `G²_real >` the `χ²₁₆` 0.001 critical value `39.25`.
- (A3) **Universality:** implied `ε̂` is **constant within ±30%** across the 8 generators (Axis 1)
  AND across primes at fixed `n=20000` (Axis 2b).
⇒ Conclude: **evidence for a universal inter-coordinate coupling of magnitude `ε̂ = <value>`**, stated
WITH scope `(b=7, p ≤ 2¹⁷, pooled-G²/swap estimators)`. Even here, extrapolation to `2²⁵⁶` is NOT
claimed — only that within-scope the coupling is a generator/prime-independent constant. Report which
swap channel (odd/even) carries it.

**BRANCH B — UNIVERSAL NOISE FLOOR** (coupling at/below the estimator floor). Requires ALL:
- (B1) `|z_G²| < 5` at **every** cell including `n_max`, AND `log z_G²`-vs-`log n` slope `< +0.5`.
- (B2) `ε̂` vs `n` slope consistent with `−0.5` (within ±0.2), AND `dev_real/dev_surrogate ∈ [0.5, 2]`
  across the whole range (the drill's ratio≈1 signature), AND raw `G²_real` consistent with `χ²₁₆`
  (no cell `p < 0.01` after multiplicity correction).
- (B3) `z_odd` and `z_even` also flat (no rising subspace channel), and `z` at fixed `n` is
  surrogate-consistent (≈0) across generators and primes.
⇒ Conclude: **any inter-coordinate coupling is BOUNDED above by `ε_floor(n_max) ≈ 1.35%`** at
`n ≈ 1.3×10⁵`, `b=7`, `p ≤ 2¹⁷`, pooled-G²/swap estimators, control fired. This is a **magnitude with
its power and scope** — explicitly NOT "no coupling," NOT "§X.6 closed." A coupling below ~1.35%, or
one switching on above `2¹⁷`/near `2²⁵⁶`, is not excluded; the frontier stays live and the tensor law
gets a stated in-scope precision, not a closure. (Enforces the negative-bias rule: a `n^(−1/2)` decay
is a size, not an absence.)

**BRANCH C — ORBIT / GENERATOR / PRIME-SPECIFIC** (real but not universal). Triggered when `z_G²`
reaches ≥5 in SOME cells but the implied `ε̂` **varies beyond the surrogate spread** across generators
(Axis 1) or across primes at fixed `n` (Axis 2b) — i.e. A1/A2 hold for some cells but A3 fails.
⇒ Conclude: **a coupling that is present but generator/prime-specific**, reported cell-by-cell WITH
each cell's scope and `ε̂`. Neither "universal constant" nor "floor."

**BRANCH D — UNDERPOWERED / AMBIGUOUS** (guards against calling "floor" when merely underpowered).
Triggered when `z_G² < 5` at `n_max` BUT the `log z`-vs-`log n` slope is clearly positive (`≥ +0.5`)
or `z_odd/z_even` is rising — a trend that has not yet crossed `Z*` within `2¹⁷`.
⇒ Conclude: **not resolvable at `p ≤ 2¹⁷`**; pre-commit to the prime-range **extension** (p up to
2¹⁸/2²⁰/2²⁵ to reach `ε`=1%/0.5%/0.1% per §5) — do NOT record a floor. Extension runs under a new
prereg inheriting §2–§4.

No outcome may be reinterpreted after the data is in; every branch's conclusion is fixed above.

---

## 8. EXACTNESS (no-float-in-signal-path rule)

**State-defining path is integer-exact — confirmed by reading `lift_sextant_rhombus_law_proof_v2.py`:**
`rdiv` (rounded division, l.65-67) is pure `divmod` + integer comparison; `cornacchia_4p_D3` uses
`math.isqrt` + integer ops; `gauss_reduce`/`enorm`/`reduced_basis` are integer; `add_c` is mod-`p`
integer EC addition; `eis()` and `state()` call `rdiv` on integer inputs. So each `(c₁,c₂)` is
produced by integer arithmetic only — no float touches the key, the point, the lift, or the state.

**Float carve-out, justified (analytic magnitudes / monotone-vs-null only, no state, no data
threshold):** (i) transition **counts accumulated as Python `int`** (or asserted `< 2^53`; at
`n ≤ 2¹⁷` trivially exact even in float64) — pre-committed to `int` accumulators so exactness survives
any p-extension; (ii) eigenvalues `np.linalg.eig` (analytic size); (iii) the `ln` inside `G²` and
Frobenius norms (analytic likelihood/size); (iv) the surrogate-`z` mean/std (a monotone statistic
ranked against the matched null, permitted by the rule). The only float threshold in the whole design
(`Z* = 5`, slope cuts) is applied to a **surrogate-normalized** statistic, never to raw key-derived
data. The `theta_of`/`p0_closed` floats in the lift file are NOT on this path. Run `check_no_float.py`
on the sweep script's signal-path functions before the run.

---

## 9. PRE-COMMITMENT (filled in BEFORE the run — one row per possible outcome)

| Observed at `n_max`≈1.3×10⁵ and across cells | Branch | Pre-committed conclusion |
|---|---|---|
| `z_G²≥5` & rising (slope≥+0.5) & `ε̂` const ±30% across gen/prime | **A** | Universal coupling `ε̂`, scope (b=7, p≤2¹⁷); no 2²⁵⁶ claim; name swap channel |
| `z_G²<5` everywhere, slope<+0.5, `ε̂`~n^(−0.5), ratio∈[0.5,2], odd/even flat | **B** | Coupling **bounded < ~1.35%** at n≈1.3×10⁵ (b=7, p≤2¹⁷); NOT closed; frontier live |
| `z_G²≥5` in some cells but `ε̂` varies beyond surrogate across gen/prime | **C** | Coupling present but generator/prime-specific; report per-cell `ε̂`+scope |
| `z_G²<5` at n_max BUT slope≥+0.5 or `z_odd/z_even` rising | **D** | Underpowered at 2¹⁷; extend p→2¹⁸/2²⁰/2²⁵ (new prereg); do NOT call floor |
| Omnibus `z_G²` flat but `z_odd` (or `z_even`) ≥5 & rising | **A/subspace** | Coupling in that swap subspace — report it, do NOT bury under omnibus null |
| Planted control fails to fire/localize at predicted `n` (§4) | — | Null uninformative — FULL STOP; fix pipeline, re-run before any verdict |

**Abandon the "universal nonzero constant" hypothesis** iff Branch B holds (flat `z`, `ε̂~n^(−0.5)`,
ratio≈1, control fired) — reported as the bounded magnitude above, never as "no structure."
**Abandon the "pure finite-size floor" hypothesis** iff Branch A or C holds.
