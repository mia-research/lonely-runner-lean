# PREREG — locus and mechanism of the sub-Rayleigh `mean|U|` deficit

**File:** `PREREG_subrayleigh_deficit_locus_v1.md` **Date:** 2026-07-23
**Status: PRE-RUN.** No statistic in §3–§7 below has been computed. The only code executed
while writing this spec was `prime_order_curve` on `[5,150)` to fix the validation scope
(§6); it returns `(p,n)` pairs only and no arm statistic.

**Scope banner (inherited by every number this run produces).** Enumerable model curves
`E : y² = x³ + 7` over `F_p`, `p` in the frozen list of §6, prime group order `n`,
`d = 1..n−1` fully enumerated. `p = 2²⁵⁶−2³²−977` is **not** enumerable and **nothing here
transfers there** — every object below is a full group sum over all `d`. No ECDLP,
extraction, or security claim is made or may be derived from any outcome.

---

## 1. OBJECT

Fixed by `t_y_maxbound_v1.prime_order_curve` / `group_coords` (exact int curve arithmetic):
`x_d, y_d` = affine coords of `d·G`, `d = 1..n−1`.

```
U_g(b,c) = Σ_{d=1}^{n−1} g(d) · e_p(b x_d + c y_d)          (b,c) ∈ [0,p)²
S        = {(b,c) ≠ (0,0)},  |S| = p² − 1
char     : g(d) = e_n(a d),  a ∈ (Z/n)^*,  a₀ = 1
σ̂²       = p²(n−1)/(p²−1)          (exact rational; = mean over S of |U|², identical for
                                     char and for every unit-modulus g, verified in the
                                     prior run to ≤1.3e−16)
r(b,c)   = |U_g(b,c)| / σ̂           (normalized magnitude; E[r²] = 1 exactly, both arms)
```

**The object measured is the distribution of the multiset `{r(b,c) : (b,c) ∈ S}` for
`g = character` versus for matched non-character targets, and the integer quadruple
statistics of the point set that control its fourth moment.**

**Tautology check.** The character `e_n(a d)` and the coordinate set `{(x_d,y_d)}` are both
indexed by the same `d`. This is not a residue-vs-component tautology: the controls (§4)
swap **only** `g(d)` and hold the point set, `S`, `p`, `n`, and the readout fixed. The
hypothesis is precisely that the coincidence of the two indexings is what produces the
deficit, so the shared indexing is the object, not an artifact of the comparison. The
statistic is a joint property of the point SET, not a per-point readout.

## 2. THE MECHANISM BEING TESTED — provenance declared

**Derived pre-run from algebra; untested; no statistic below has been computed; not fit to
any data.** Chain, stated so each link is separately falsifiable:

- (M-a) `l²` is pinned exactly (`Σ_S |U|² = p²(n−1)`, basis-invariant). A deficit in
  `l¹ = Σ|U|` at fixed `l²` means the magnitudes are **more unequal** than the null.
- (M-b) The character's max is **lower** than the null's (measured: `3.55√p` vs `4.03√p` at
  `p=2089`). More unequal at fixed `l²` with a lower max ⇒ the excess mass is in the
  **low** tail, not the top.
- (M-c) "More unequal at fixed `l²`" is an **excess in the fourth moment**.
- (M-d) The fourth moment is exactly countable. Over **all** `p²` frequencies,
  ```
  Σ_{b,c} |U_g(b,c)|⁴ = p² · Σ_{(d1,d2,d3,d4)} g(d1)g(d2) conj(g(d3)) conj(g(d4))
  ```
  the sum over ordered quadruples in `[1,n−1]⁴` with
  ```
  x_{d1} + x_{d2} ≡ x_{d3} + x_{d4}  (mod p)   AND   y_{d1} + y_{d2} ≡ y_{d3} + y_{d4}  (mod p).
  ```
  For a random-phase `g` only the diagonal `{d1,d2} = {d3,d4}` survives in expectation. For
  `g(d) = e_n(a₀ d)` the weight is exactly `e_n(a₀ Δ)`, `Δ = d1+d2−d3−d4 mod n`, so **every**
  quadruple with `Δ ≡ 0` contributes coherently with weight exactly `1`.
- (M-e) `d1+d2 ≡ d3+d4 (mod n)` is `P1+P2 = P3+P4` under the **group law**;
  `x1+x2 ≡ x3+x4 (mod p)` is **naive coordinate addition**. These are different conditions.
  **The pre-registered mechanism: the deficit is carried by quadruples where the two
  coincide, in excess of the chance rate `1/n`.**

**Pre-committed quantitative link (derived pre-run).** Embed the profile in the one-parameter
family `|U|²/σ̂² ~ Gamma(k, 1/k)` (`k=1` is Rayleigh/exponential, `k<1` = fatter low tail at
fixed `l²`). Then `d log M1/dk = ψ(k+½)−ψ(k)−1/(2k) = +0.1137` and
`d log(M4/M2²)/dk = −1/(k+1) + ... = −0.5` at `k=1`, so

> **`δ log M4 ≈ −4.4 · δ log M1`.**

An `l¹` deficit of `0.08%` therefore predicts an `M4` **excess of ≈ 0.35%**, and (by the same
family, small-`u` expansion `log F(u) = k log(uk) − logΓ(k+1)`) a **`+2.8%` relative excess in
the count of harmonics below `r = 0.10`**. These two numbers are frozen predictions.

## 3. STATISTIC — one primary per arm, named now

| arm | primary statistic (the only one that can produce a verdict) | null distribution |
|---|---|---|
| **1 LOCUS** | Zone decomposition of the mean deficit. `mean r = ∫₀^∞ (1−F(t))dt`, so `mean_char − mean_null = −∫ (F_char − F_null) dt` **exactly**. Report the three additive pieces `I_LOW = ∫₀^0.5`, `I_MID = ∫_0.5^1.5`, `I_HIGH = ∫_1.5^∞` of `(F_char − F_null)dt`, and the fraction of the total each carries. **Zones sum to the total deficit by construction — this arm cannot return "nothing"; it always localizes.** | rank of each zone fraction among `R` null replicates |
| **2 M4** | `M4 = (1/|S|) Σ_S r⁴` (normalized; comparable across `p` since `M2 = 1` exactly). Report `z = (M4_char − mean M4_null)/sd M4_null` per prime, then **pooled** Stouffer `Z = Σz_i/√7` and a 7-prime sign test. Pooled, not max-over-primes. | `R` null replicates per prime |
| **3 QUADRUPLES** | The **integer histogram** `H[Δ] = #{ordered quadruples satisfying both coordinate-sum relations, with d1+d2−d3−d4 ≡ Δ (mod n)}`, `Δ ∈ Z/n`, split into `H_diag` (`{d1,d2}={d3,d4}`) and `H_off`. Primary scalar: the **enrichment ratio** `E = H_off[0] / (N_off/n)`, `N_off = Σ_Δ H_off[Δ]`. Pure integers. | exact combinatorial expectation `N_off/n` (chance rate), plus the permuted-point control of §4 |
| **4 a-DEPENDENCE** | Fraction of sampled orbit representatives `a` with `z_a < −3`, where `z_a` = the `mean r` deficit z-score for character `a` against the same null. Reported **per distinct configuration**, never per row. | same `R` null replicates |
| **5 SCALING** | Weighted least-squares slope `s` of `log δ(p)` vs `log p`, `δ(p) = 1 − mean r_char/mean r_null`, weights `1/σ_i²`. **Only the four pre-committed candidates `s ∈ {0 (const), −1/log p (≈−0.15), −0.5 (1/√p), −1 (1/n)}` may be evaluated. A free exponent may NOT be fit.** Output = which candidates are excluded at 2σ, with leave-one-out stability. | Gaussian on `s` with `σ_s` from the weights |

Secondary, reported but never verdict-bearing: full quantile table of `r` on the grid
`t ∈ {0.05,0.10,0.20,0.35,0.50,0.75,1.0,1.25,1.5,2.0,2.5,3.0,3.5}`; counts below `t*=0.10`
and `t=0.05`; the moment ladder `M1, M2, M3, M4, M6`; `max r`.

## 4. MATCHED CONTROLS — what is preserved, what is destroyed

Two nulls, **both required**. The prior run used MC1 only; MC2 is new and is the primary.

- **MC1 — iid continuous unit phase.** `g(d) = e^{iθ_d}`, `θ_d` iid uniform. *Preserves:* the
  point set `{(x_d,y_d)}`, `S`, the readout map, `p`, `n`, `|g|=1`. *Destroys:* that `g` is a
  character; also destroys that `g` takes each `n`-th root of unity exactly once and that
  `Σ_d g(d) = −1` exactly. `R = 200`.
- **MC2 — permuted character (PRIMARY).** `g(d) = e_n(a₀ π(d))` for a uniformly random
  permutation `π` of `{1,…,n−1}`. *Preserves:* everything MC1 preserves, **plus** the exact
  value multiset of the character (each non-trivial `n`-th root once) and hence `Σ_d g(d) = −1`
  exactly and `U_g(0,0) = −1` exactly. *Destroys:* only the alignment between the character's
  additive structure in `d` and the group law — exactly the (M-e) condition. `R = 200`.
- **MC3 — discrete-alphabet iid** (diagnostic only, `R = 50`): `g(d) = e_n(u_d)`, `u_d` iid
  uniform on `Z/n`. Separates "phase alphabet is discrete" from "value multiset is exact".

**Why MC2 is load-bearing.** MC1 does not reproduce the zero-sum / exact-multiset structure
the character has by definition. A deficit measured only against MC1 could be a
sampling-without-replacement artifact and not the (M-e) coincidence at all. **A deficit
against MC1 that vanishes against MC2 refutes the mechanism and names the cause as the exact
value multiset.** This is the single most likely benign explanation and it is controlled
before Arm 3 is interpreted.

- **Arm 3 control (MC2-analogue, integer).** Recompute `H[Δ]` with the `d`-labels of the
  point set randomly permuted (`d ↦ π(d)` in the `Δ` bookkeeping only, coordinates untouched),
  `R = 50`. This preserves the coordinate-sum incidence structure exactly (`N_off` is
  unchanged, integer-identical — **assert this**) and destroys only the `d`-alignment.

## 5. PLANTED POSITIVE CONTROLS — all must fire before any verdict

| id | plant | must fire in | pass criterion (printed) |
|---|---|---|---|
| **P1** | synthetic magnitude array with a deliberately fattened low tail: `r'` drawn from `Gamma(k=0.9, 1/k)`, renormalized to `M2 = 1` exactly | Arm 1 | `I_LOW` fraction > 0.5 and outside the MC1/MC2 null range at every prime |
| **P2** | target with deliberately inflated `M4`: `g` iid unit phase multiplied into a rank-1 spike, or `r'` from `Gamma(k=0.9)`; nominal `M4` excess `+5%` | Arm 2 | `z > +5` at every prime |
| **P3** | brute-force validation of the `O(n²)` hashing route against direct `O(n⁴)` enumeration at `(p,n) = (13,7)` and `(43,31)` | Arm 3 | `H[Δ]` arrays **integer-identical**, all `Δ`; `H_diag` matches the closed form `2(n−1)(n−2) + (n−1)` |
| **P4** | planted coherence: replace the point set's `d`-labels by a construction with a known injected excess of `Δ=0` off-diagonal quadruples (e.g. duplicate a known-coincident pair class), nominal `E = 5` | Arm 3 | measured `E ≥ 4` |
| **P5** | a character `a` known to be in `a₀`'s equivariance orbit | Arm 4 | its `mean r` **identical** to `a₀`'s to `≤1e−9` relative (forced, zero evidence) |
| **P6** | synthetic `δ(p) = C·p^{−0.5}` with the measured error bars | Arm 5 | the fit excludes `const` and `1/n`, retains `1/√p` |

**If any of P1–P6 does not fire, the corresponding arm reports "control did not fire; null
uninformative" and no verdict is issued for that arm.**

**Forced readout checks (zero evidence, must be printed).**
- **C-EQ (constraint 1).** `λ³ ≡ 1 mod n`, and `β` **derived from the data** as
  `β = x_{λd}/x_d`; assert `max_d ((x_{λd} − β x_d) mod p) == 0` **as an exact integer
  assertion**, then assert `|U(a₀,βb,c)| = |U(λ⁻¹a₀,b,c)|` to ≤1e−11. The prior run's bug —
  choosing the order-3 elements of `Z/n` and `F_p` independently, which broke the identity at
  `p=433` and `p=577` — is guarded by the paired derivation. No equivariance-based statistic
  may run before this assertion passes.
- **C-M2.** Re-verify `M2 = 1` (i.e. `Σ_S|U|² = p²(n−1)`) for char and for every null draw.
  Forced; validates the readout only.
- **C-X (cross-check, load-bearing).** `M4` from the float FFT (Arm 2) must agree with the
  exact integer route `p²·Σ_Δ H_full[Δ] e_n(a₀Δ)` (Arm 3) to ≤1e−9 relative, at every prime
  where both run. **This makes Arm 2 and Arm 3 the same quantity computed two ways; a
  disagreement halts both arms.**

## 6. SCOPE

- **Arms 1, 2, 4, 5 primes:** `p ∈ {163, 211, 349, 433, 577, 991, 2089}` with
  `n = {139, 199, 313, 397, 613, 1009, 2143}`. Frozen. `a₀ = 1`.
- **Arm 3 primes:** the same 7, **plus** the validation pair `(p,n) = (13,7)` and `(43,31)`.
- **Optional extension, declared now:** the first qualifying prime-order `y²=x³+7` curve with
  `p ∈ [5500,6500]`, attempted for Arms 2 and 3 only. The run must report whether it was
  attempted and, if not, why. It may not be added silently, and it may not be added only if
  it helps.
- **Cost model.**
  - Arms 1/2/4: one `p×p` complex FFT per target; at `p=2089` that is `4.36e6` complex128
    ≈ 70 MB per array, `R=200+200+50` sequential draws. Feasible. At `p≈6000` it is ≈576 MB
    per array — this is the binding constraint on the extension prime.
  - Arm 3: build all `(n−1)²` ordered pairs keyed by `(x1+x2 mod p, y1+y2 mod p)` carried
    alongside `s = d1+d2 mod n`; sort by key; per key with multiplicity `m_K` do `m_K²` work
    accumulating `H[Δ]`. Time/space `O(n²)`, `Σ_K m_K² ≈ (n−1)² + (n−1)⁴/p²`. At `n=2143`:
    `4.59e6` int64 records ≈ **75 MB**, `≈9.4e6` accumulate operations, **seconds**. Combined
    key `((X·p+Y)·n + s) < 9.3e9 < 2⁶³` — no overflow.
  - **Arm 3 therefore runs at ALL primes Arms 1–2 run at, and its ceiling (`n ≲ 10⁴`,
    ≈1.6 GB) is higher than Arms 1–2's.** No arm is restricted to a subset of the others'
    primes. If this changes at run time it is a deviation and must be recorded.

## 7. POWER — computed now

Null spread is set by `|S| = p²−1`, **not by `R`**. `R` only stabilizes the null mean/sd;
increasing `R` beyond ~200 does not increase power for any arm here. Stated per arm.

**Variance model (derived, not fit).** With `|U|²/σ̂² ~ Exp(1)` conditioned on `Σ` fixed
(the exact `l²` conservation), per-sample conditional variances are
`Var(√E | ΣE) = 0.0183` (vs `0.2146` unconditional — a `11.7×` reduction, consistent with
the prior run's observed `≈12.8×`) and `Var(E² | ΣE) = 4` (vs `20`).

| statistic | null rel. sd | at `p=2089` | at `p=991` | at `p=577` | at `p=163` |
|---|---|---|---|---|---|
| `mean r` (`M1`) | `0.135/√|S|` | `7.0e−5` | `1.5e−4` | `2.7e−4` | `9.7e−4` |
| `M4` | `1/√|S|` | `4.8e−4` | `1.0e−3` | `1.7e−3` | `6.1e−3` |
| `#{r<0.10}` | `1/√(0.00995|S|)` | `4.8e−3` | `1.0e−2` | `1.7e−2` | `6.2e−2` |

**Arm 1.** Predicted signal `+2.8%` in `#{r<0.10}` ⇒ `z ≈ 5.9` at `p=2089`, `≈3.1` at
`p=991`, `≈1.2` at `p=577`, `<1` at `p ≤ 433`. **Resolvable at `p ≥ 991` only.**
**Arm 2.** Predicted signal `+0.35%` in `M4` ⇒ per-prime `z ≈ 7.3 (2089), 3.9 (991),
1.5 (577), 1.2 (433), 1.1 (349), 0.4 (211), 0.7 (163)`; pooled Stouffer `Z ≈ 6.1`, sign test
`2⁻⁷ = 0.0078`. **The pooled statistic is the powered one; the 5 smallest primes are
individually underpowered and must not be read individually.**
**Arm 3.** Exact integers, no sampling error. Expected scale at `n=2143`:
`N_tot ≈ 9.4e6`, `H_diag = 2(n−1)(n−2) + (n−1) ≈ 9.18e6`, `N_off ≈ 2e5`, chance
`N_off/n ≈ 93`. To supply a `+0.35%` `M4` excess the mechanism needs
`H_off[0] ≈ 3.2e4`, i.e. **enrichment `E ≈ 340`**. This is a sharp, decidable, integer
prediction with no sampling noise; Arm 3 is the highest-powered arm.
**Arm 4.** Individual `z_a` is the same size as `a₀`'s (`−13.9` at `p=2089`), so
`|{a}| ≥ 12` distinct configurations separates "all characters" from "`a₀` only" at
overwhelming margin. Sample: **all** orbit representatives at `p ≤ 433`; a
seed-`20260723` random sample of **60** representatives at `p ∈ {577, 991, 2089}`.
**Arm 5 — explicitly underpowered, stated now.** `σ_s ≈ 0.153` from the frozen error bars.
This separates `const (0)` from `1/√p (−0.5)` at `3.3σ` and from `1/n (−1)` at `6.5σ`, but
**cannot separate `const` from `1/log p` (Δs ≈ 0.15 = 1.0σ_s)**. Further, `p=991` and
`p=2089` carry `94%` of the total weight — effectively 2 points. **Leave-one-out on `p=2089`
must be reported.** Arm 5 may report exclusions only; it may not name an exponent.

**Equivariance / distinct configurations (constraint 1, mandatory in every significance
statement).** `|U(a,b,c)|` is invariant under `a ↦ λa` (paired `b ↦ βb`) **and** under
`a ↦ −a` (paired `(b,c) ↦ (b,−c)`, i.e. the `[−1]` map `y ↦ −y`), so the full multiset
`{|U(a,·,·)|}` — and hence every statistic here — is constant on orbits of the order-6 group
`⟨λ, −1⟩` acting on `(Z/n)^*`. The distinct-configuration count is therefore `≈(n−1)/6`, **not**
`n−1` and **not** `(n−1)/3`. **The run must COUNT the orbits explicitly (some `a` may have a
nontrivial stabilizer) and print `#orbits`; every Arm-4 significance statement must be in
units of distinct configurations.**

## 8. EXACTNESS

- **Exact `int`:** curve arithmetic (`ec_add`, `group_coords`), the `(b,c)` grid, `σ̂²` as a
  `Fraction`, **all of Arm 3** (pair keys, sort, `H[Δ]`, `H_diag`, `N_off`, `E` as an integer
  ratio), the `C-EQ` assertion `max_d ((x_{λd} − βx_d) mod p) == 0`, orbit counting, all
  permutation/rank counts and `p`-values (integer counts over integer denominators).
- **Float carve-out (analytic size only, no key in the path):** the `p×p` FFT producing `|U|`,
  the trig factor `e_n(a₀Δ)` in the `C-X` cross-check, and the reported `z` values.
  Justification: these are magnitudes of an analytic sum, not key-derived low bits.
- **No pass/fail is decided by float precision.** Every verdict-bearing comparison is a rank
  of the character's value among `R` null draws (Arms 1,2,4), an integer ratio (Arm 3), or a
  fit exclusion at a stated `σ` (Arm 5). Thresholds like `r < 0.10` are applied to float
  magnitudes but never decide a verdict directly — only the **rank of the resulting count**
  against the null does.
- `check_no_float.sh` must pass on the Arm-3 module before Arm 3 is run.

## 9. PRE-COMMITTED OUTCOME TABLE

Filled in before the run. Every row is a positive result naming what the deficit is or is not.
**No row licenses a closure, a verdict about ECDLP/extraction/security, or the words
"generic / benign / tautological / at the floor / no structure".**

| # | Outcome | Conclusion reported |
|---|---|---|
| **O1** | **MC2 deficit ≈ 0** (character matches permuted-character null) while MC1 deficit persists | **The mechanism (M-e) is REFUTED at this scope.** The deficit is named as an artifact of the character's exact **value multiset / zero-sum constraint** (`Σ_d g(d) = −1`), i.e. sampling-without-replacement, not group-law/coordinate coincidence. Report as a positive identification of the cause. Arms 2–3 are then reported as consistency checks, not tests. |
| **O2** | MC2 deficit persists; **Arm 2 shows `M4` excess** with pooled `Z > 3` and per-prime signs consistent; **Arm 3 shows `E ≫ 1`** at the scale §7 predicts | Mechanism **SUPPORTED** at this scope. Report the measured `E` per prime with its integer counts, the measured `δlog M4 / δlog M1` ratio against the frozen `−4.4`, and Arm 1's zone fractions. Next probe named in the result file, not chosen post hoc. |
| **O3** | **Arm 2 shows no `M4` excess** (pooled `|Z| < 2`) or a `M4` **deficit** | **Mechanism (M-c/M-d) REFUTED.** This is a positive result: it names that the `l¹` deficit is **not** carried by fourth-moment inequality. Report the full moment ladder `M1,M2,M3,M4,M6` so the run still localizes which moment does carry it. Explicitly record that a refuted mechanism is not a closed frontier and that the deficit remains live and unexplained. |
| **O4** | **Arm 3: `E ≈ 1`** — no excess of coherent off-diagonal quadruples over the chance rate `N_off/n` | The group-law / naive-coordinate-addition coincidence is **absent at this scope**. Report the integer `H_off[0]`, `N_off`, `n`, and `E` with CI-free exactness. If Arm 2 nonetheless shows an `M4` excess, the excess is carried by the **oscillatory** part `Σ_{Δ≠0} H[Δ]e_n(a₀Δ)` — report that sum and the shape of `H[Δ]` as the new object. |
| **O5** | Arm 2 and Arm 3 disagree (C-X fails or the two `M4` routes differ) | **No verdict on either arm.** Report the discrepancy, both numbers, and halt. |
| **O6** | Arm 1: `I_LOW` carries `>50%` of the deficit | Locus confirmed as the **low tail**; report the zone fractions and the `#{r<t}` table. |
| **O7** | Arm 1: `I_MID` or `I_HIGH` carries the majority | Locus is **not** the low tail ⇒ (M-b) is wrong. Report which zone, and that the mechanism's predicted locus failed even if Arm 2 fires. |
| **O8** | Arm 4: `≥90%` of sampled distinct configurations show `z_a < −3` at `p ∈ {991,2089}` | "**Characters are sub-Rayleigh relative to random targets**" — a property of the curve+character system, scoped to these primes. Report the fraction and `#orbits`. |
| **O9** | Arm 4: `a₀` deficits at `z < −3` while `≥90%` of other configurations sit at `|z_a| < 2` | An **`a₀`-specific** effect. Much stronger claim; report it as **requiring its own follow-up prereg** and do not interpret Arms 1–3 (which are all computed at `a₀`) as general until that follow-up runs. |
| **O10** | Arm 4: mixed (between the O8 and O9 bands) | Report the empirical distribution of `z_a` over distinct configurations, no verdict; name the mixed case as the object for the next probe. |
| **O11** | Arm 5: `const` and `1/log p` both retained, `1/√p` and `1/n` excluded | Report exactly that, with `σ_s`, the leave-one-out result, and the statement that `const` vs `1/log p` is **not resolvable at 7 primes over one decade**. No exponent is named. |
| **O12** | Arm 5: any candidate retained/excluded pattern other than O11 | Report all four residuals and the leave-one-out table. No free exponent fit. If the exclusion pattern flips under leave-one-out on `p=2089`, report the arm as **unresolved**. |
| **O13** | Any of P1–P6 fails to fire | The corresponding arm reports "**planted control did not fire; null uninformative**" and issues **no verdict**, regardless of how clean its numbers look. |
| **O14** | C-EQ assertion fails at any prime | Halt. Fix the `(λ,β)` pairing (derive `β` from the data). This is a bug, not a finding — as it was at `p=433` and `p=577` in the prior run. |

**Effect-in-an-unprojected-subspace clause (mandatory).** If Arms 1–3 all come back flat, the
run must NOT report "no structure". It must report: (i) the bounded magnitude with its power
number and scope; (ii) the full moment ladder, so the moment carrying the deficit is named or
bounded; (iii) the `H[Δ]` histogram shape, which is the deficit's exact generating function
and may carry structure at `Δ ≠ 0` that the scalar `E` does not see; (iv) an explicit list of
what was not projected onto — non-`(b,c)` bases, non-unitary transforms, higher-degree
readouts, `a ≠ a₀` beyond the Arm-4 sample, `p > 2089`.

**Output type, pre-committed.** A characterization plus bounds, each carrying its power number
and the §6 scope. Never a verdict about ECDLP, extraction, or security.
