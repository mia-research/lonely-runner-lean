# PREREG v2 — the N1 phase cap `S_y ≤ 2`: out-of-sample test, matched null, calibrated plant

**File:** `PREREG_n1_phase_cap_v2.md`  **Date:** 2026-07-24  **Status: PRE-RUN (frozen).**

Repairs the six audited gaps in `n1_phase_cap_sweep_v1_DEVIATIONS.md` (no pre-registration, no
deviations file, no planted control, self-contradicted frozen text, no numerical R2/R3 criterion, no
out-of-sample split). Re-graded v1 result: `RESULT_n1_phase_cap_v2.md`. Instrument as run:
`n1_phase_cap_sweep_v1.py`. Structure established: `RESULT_xdomain_ports_v2.md` §1.

**Scope banner — inherited by every number this run produces, never omitted from any of them.**
Model curves `E : y² = x³ + 7` over `F_p`, `p ≡ 1 mod 3`, `n = #E(F_p)` prime, `G` a generator,
`(x_d, y_d) = [d]G` for `d = 1..n−1`, `p` in the frozen holdout of §6. `p = 2²⁵⁶−2³²−977` is not in
scope and **nothing here transfers to it**. No leakage, key-recovery, extraction or ECDLP claim is made
or may be derived from any outcome. Abstention is legitimate and is **not** a closure.

---

## 0. SEEN-DATA DECLARATION — read before anything else

Pre-registration is an ordering claim. v1 ran and printed numbers. **Those numbers are seen.**

| quantity | status | consequence |
|---|---|---|
| `S_y ≤ 2` at 193/193, 402,718 μ₆ configurations, 0 violations, `p < 30000`, `p ≡ 1 mod 3` | **SEEN** | may be cited as `[SEEN-DATA]` only; **may never be reported as a pre-registered discovery** |
| max `S_y = 1.99979` at `p = 1237` | **SEEN** | `[SEEN-DATA]` |
| range means `1.97911` / `1.98563` / `1.99189`; slope `−0.448` | **SEEN** | `[SEEN-DATA]`. Used **only** to design §5's power and to fix G2's alternative; never re-reported as a result |
| `S_x > 2` at 51/193, max excess `0.0203` | **SEEN**; its inference withdrawn (v1 D4) | **excluded from this design entirely** (§3.6). The run may not compute `S_x`. |
| random unit-modulus target `S ≈ 3.2` | **SEEN** | `[SEEN-DATA]`; superseded by the derived null law F-NULL (§2) |
| Everything at `p > 30000` | **UNSEEN — no statistic has ever been computed there** | the holdout of §6 is a genuine out-of-sample set |
| The null law F-NULL, `Σ_O s_O² = n/4`, C-CEIL/C-FLOOR values, `ε*_pred`, all §5 power numbers | derived from `(n, λ)` and synthetic `Z/n` sequences; **no curve read** | pre-registered predictions, §2 |

**`p < 30000` with `p ≡ 1 mod 3` is burned as a discovery set.** No holdout prime may be drawn from it.

---

## 1. OBJECT

`h(d) = χ₂(y_d) ∈ {±1}` for `d = 1..n−1` (`n` odd prime ⇒ no 2-torsion ⇒ `y_d ≠ 0`, so `h` never
vanishes); `h(0) := 0`.

```
V(a) = Σ_{d=1}^{n−1} h(d) · e_n(a·d)          a ∈ Z/n
S_y(p) := max_{a ≠ 0} |V(a)| / √p
```

**Under test:** `S_y(p) ≤ 2` on prime-order `y² = x³+7` curves — equivalently, given the weight-1
premise below, `|sin θ₁ + sin θ₂| ≤ 1` for the two free eigenangles.

### 1.1 Tautology check

The feature (`h`, from `y`) and the target (`S_y ≤ 2`) share no construction: the target is a bound on
the Fourier transform of the feature, not a rederivation of it. There is no residue-vs-component
tautology here (`feedback_residue_vs_component_tautology_2026_07_14`). **Design is valid to run.**

### 1.2 ⚠ OBJECT vs PROXY — the one place this spec is a proxy, stated up front

`S_y ≤ 2` is **object-level and exact** for the statement *"`max_a |V(a)| ≤ 2√p`"*.

It is a **proxy** for the phase statement *"`|sin θ₁ + sin θ₂| ≤ 1`"*. The translation
`|V(a)| = 2√p·|sin θ₁ + sin θ₂|` needs two inputs:

| input | grade |
|---|---|
| multiset closed under `α ↦ −ᾱ` (⇒ two pairs `{α,−ᾱ}`, two real parameters) | `[DERIVED — FORCED]` from `χ₂^{(k)}(−1) = (−1)^{(p^k−1)/2}` |
| **all four twisted eigenvalues have modulus exactly `√p`** | **`[VERIFIED — p = 13, 43 ONLY; six unforced cells]`** |

The weight-1 premise costs `O(p⁴)` (it needs `E(F_{p^k})`, `k ≤ 4`) and **cannot be checked anywhere in
the holdout.** Therefore:

> **Every phase-language sentence this run produces carries the tag `[weight-1 premise: VERIFIED at
> p = 13, 43 only]`. Every `S_y ≤ 2` sentence is object-level and carries no such tag.**

**ARM-3 (optional, §3.7)** extends the premise from 2 primes to every `p ≡ 1 mod 3` with `n` prime and
`p ≤ 100`. If ARM-3 is not run, the premise stands at 2 primes and the tag is mandatory.

### 1.3 Symmetry type of the readout — the class the null must live in

Both relations are forced by `Aut(E) = μ₆` acting on `y` as `y ↦ ±y`:

| relation | source | forced? |
|---|---|---|
| `h(λd) = h(d)`, `λ` of order 3 in `(Z/n)^*` | GLV endomorphism `(x,y) ↦ (βx, y)` **fixes `y`** | **FORCED, a priori** |
| `h(−d) = χ₂(−1)·h(d)` | `[−d]G = (x_d, −y_d)` | **FORCED, a priori** |
| nothing else is forced | `RESULT_xdomain_ports_v2.md` §2: the forced multiples are exactly `Aut(E)`; ≈3400 non-automorphism multiples tested at 19 primes, none forcing | `[VERIFIED — 19 primes, exhaustive in k]` |

⇒ `h` is a `±1` function on `(Z/n)^*` that is **constant on `⟨λ⟩`-orbits** and **transforms by `χ₂(−1)`
under `[−1]`**. Call this the **admissible class `A(n)`**; `|A(n)| = 2^{(n−1)/6}`.

**Two strata, never pooled:**

| stratum | `p mod 12` | `χ₂(−1)` | `h` | `V` | `V(0)` |
|---|---|---|---|---|---|
| **ODD** | `7` | `−1` | odd | purely imaginary, `V(−a) = −V(a)` | `= 0` exactly |
| **EVEN** | `1` | `+1` | even | real, `V(−a) = V(a)` | generally `≠ 0` |

`|V(a)| = 2√p·|sin θ₁+sin θ₂|` (ODD) / `2√p·|cos θ₁+cos θ₂|` (EVEN).

### 1.4 The object, re-typed exactly — an integer autocorrelation and a spectral radius

`|V(a)|² = Σ_{Δ} C(Δ)·e_n(aΔ)` with `C(Δ) = Σ_{d} h(d)h(d+Δ) ∈ Z`, `C(0) = n−1`. So the circulant
`Circ(C)` has eigenvalues exactly `|V(a)|²`, and

> **H-CAP ⟺ the integer circulant `Circ(C)` has spectral radius `≤ 4p`.**

This is the symmetry-type/subspace form of the question. It is registered now so that no outcome of
this run can be reported as a bare magnitude: whatever `S_y` does, `C(Δ)` — an exact integer sequence,
itself μ₆-invariant — is the object the successor characterizes.

---

## 2. WHAT IS FORCED — zero information, computed and stated BEFORE the run

**F1 — generator invariance `[PROVED]`.** `G' = [c]G` ⇒ `h'(d) = h(cd)` ⇒ `V'(a) = V(ac^{-1})` ⇒
`S_y` **unchanged**. `G' = −G` flips `V` by `χ₂(−1)`; `|V|` unchanged. **"A different generator" may
never be reported as a control.** Checked as `C-GEN`, zero evidence.

**F2 — μ₆ collapse `[PROVED]`.** `V(aλ) = V(a)` and `V(−a) = χ₂(−1)V(a)`, so the `n−1` frequencies
collapse to exactly `M := (n−1)/6` **distinct configurations**. `6 | n−1` is forced (`λ` of order 3
acts on a cyclic group of prime order `n` ⇒ `3 | n−1`; `n` odd ⇒ `2 | n−1`). **Every denominator in
this run is `M = (n−1)/6`, never `n−1`.** Asserted as an integer identity (`C-CELLS`).

**F3 — Parseval `[PROVED]`.** `Σ_{a=0}^{n−1}|V(a)|² = n(n−1)`. ODD: `V(0)=0` ⇒
`mean_{a≠0}|V(a)|² = n` **exactly**. EVEN: `mean_{a≠0}|V(a)|² = (n(n−1) − V(0)²)/(n−1)`.
**Consequences, both forced:**
- `S_y ≥ √(n/p)` always, and `√(n/p) = 1 + O(p^{−1/2})` by Hasse. **`S_y ≳ 1` is forced; it is not a finding.**
- `rms_a |sin θ₁+sin θ₂| = 1/2` exactly (ODD, under the weight-1 premise). So **H-CAP is the statement
  that the max is at most `2×` the rms**, over `M ≈ p/6` cells. Independent uniform eigenangles would
  give `rms = 1`, four times too large — the angles are already strongly constrained, and that
  constraint is forced by Parseval, not measured.

**F4 — Weil ceiling `[CITED + premise]`.** Four weight-1 eigenvalues ⇒ `S_y ≤ 4`. **This is forced and
carries zero information.** The live question is the factor 2 between `4` (forced) and `2` (claimed).
⚠ **Disclosure:** the randomization nulls of §4 do **not** reproduce the Weil ceiling — they exceed it.
Part of any real-vs-null gap is therefore a restatement of Deligne, and the run must say so; see
outcome cell O-P1's wording, which is bound to this.

**F5 — purity `[PROVED]`.** `V` purely imaginary (ODD) / real (EVEN). Instrument check only
(`C-PURITY`, `≤ 1e−12`), zero evidence.

**F6 — the exact variance of the matched null `[PROVED, and MC-verified to machine precision]`.**
For `a ≠ 0`, writing `s_O(a) = Σ_{j=0}^{2} sin(2πaλ^j d_O/n)` and `c_O(a)` likewise with `cos`, over
the `M` orbits `O`:

```
ODD :   Σ_O s_O(a)²  =  n/4         exactly, every a ≠ 0
EVEN:   Σ_O c_O(a)²  =  n/4 − 3/2   exactly, every a ≠ 0
```

*Proof.* `Σ_O Σ_j sin²θ_j = (1/6)·3·Σ_{d=1}^{n−1} sin²(2πad/n) = n/4`; each cross pair `(j≠k)` gives
`(1/6)·(1/2)[Σ_d cos(2πa(λ^j−λ^k)d/n) − Σ_d cos(2πa(λ^j+λ^k)d/n)] = (1/6)(1/2)[(−1)−(−1)] = 0`
(`λ^j ≠ λ^k` and `λ^j ≠ −λ^k`, the latter since `λ` has odd order). For `cos`, the first term is
`(n/2−1)/2` and each of the 6 ordered cross pairs contributes `(1/6)(1/2)[(−1)+(−1)] = −1/6`. ∎

*Verified numerically, synthetic `Z/n`, no curve:* `n = 30013` → `7503.2500` vs `n/4 = 7503.2500` (ODD),
`7501.7500` vs `n/4 − 1.5 = 7501.7500` (EVEN); same to the last digit at `n = 100003, 400009`.

Hence under any independent sign assignment on the `M` orbits, `E|V(a)|² = n` (ODD) / `n − 6` (EVEN) —
**the matched null reproduces Parseval exactly.**

**F7 — ⚠⚠ THE CRUX, SETTLED IN ADVANCE: parity does NOT force the cap `[DERIVED + MC-verified, curve-free]`.**

This is repair (3). The `α↦−ᾱ` closure — and hence the collapse to two real parameters — follows from
oddness alone, not from the curve. **If oddness also forced `S ≤ 2`, N1's "explanation" would be a
restatement of oddness.** It does not:

Under the matched null (uniform on `A(n)`), each cell is `|V(a)|/√n ≈ |N(0,1)|` by F6, and there are
`M` of them. Standard extreme-value theory with `a_M = √(2 ln 2M)`:

```
E[S_null] ≈ a_M − (ln ln 2M + ln 4π)/(2 a_M) + γ/a_M ,      sd[S_null] ≈ (π/√6)/a_M
```

| `M = (n−1)/6` | 5 002 (`n≈3.0e4`) | 16 667 (`n≈1.0e5`) | 66 668 (`n≈4.0e5`) |
|---|---|---|---|
| EVT `E[S_null]` | 3.873 | 4.156 | 4.462 |
| **MC mean** (200/200/60 draws, synthetic `Z/n`) | **3.861** | **4.112** | **4.441** |
| MC sd / EVT sd | 0.290 / 0.299 | 0.279 / 0.281 | 0.307 / 0.264 |
| MC min over all draws | 3.249 | 3.576 | 3.941 |
| **fraction of draws with `S_null > 2`** | **1.000** | **1.000** | **1.000** |
| analytic `P(S_null ≤ 2) ≲ (1−0.0455)^M` | `10^−101` | `10^−337` | `10^−1348` |

Same conclusion for the independently derived **odd-only** variant (μ₆ **not** imposed),
`M' = (n−1)/2`, `a_{M'} = √(2 ln(n−1))` (quoted there in the uncorrected form `√(2 ln(n/2))`; the
corrected form above is what the MC matches): 40 synthetic trials per `n`, oddness asserted (`V` purely
imaginary to `<1e−12`), fraction with `S > 2` = **0.95 at `n = 139`** and **1.00 at every
`n ∈ {397, 1009, 2143, 4243, 10861, 27361}`**, with `S` rising `2.535 → 4.107` across that range.

> **F7, pre-registered as a DERIVED PREDICTION:** under the parity-and-μ₆-matched null,
> `S_null(n) ≈ √(2 ln((n−1)/3))` (corrected form above), and `P(S_null ≤ 2) < 10^{−100}` at every
> holdout prime. **Parity + μ₆-invariance + the `±1` multiset + Parseval do NOT produce the cap.**

**⚠ HALT CONDITION (mandatory, written before the run).** If the matched null returns
`S_null ≤ 2` at any holdout prime, or its median deviates from the derived value by more than
`4 × sd_EVT`, that is an **INSTRUMENT FAILURE, not a discovery.** Named likely causes, each with its
own printed diagnostic: (i) parity not actually imposed → `C-PURITY` on the null draws; (ii) the max
taken over the wrong index set → `C-CELLS` (`#distinct |V|` must equal `(n−1)/6` exactly);
(iii) mis-normalized transform → `C-PARSEVAL` (`Σ_a|V_null|² = n(n−1)`). The run halts and reports the
failing diagnostic. **It may not report "the cap is parity-forced".**

**F8 — exact realizable range of `S_y` over `A(n)` `[PROVED; endpoints attained by named targets]`.**

| target | `S` | admissible in | status |
|---|---|---|---|
| `h(d) = χ_n(d)` (Legendre symbol mod `n`) | **`√(n/p)` exactly** (`|V(a)| = √n`, Gauss sum), `= 1 + O(p^{−1/2})` | the stratum with `χ_n(−1) = χ₂(−1)`, i.e. `p ≡ n mod 4`. μ₆-invariant since `χ_n(λ)³=1, χ_n(λ)=±1 ⇒ χ_n(λ)=1` | **exact floor** = the Parseval bound, attained |
| `ε_O = sign(s_O(1))` (resp. `sign(c_O(1))`) | `2Σ_O|s_O(1)|/√p`, computable from `n` alone before the run; MC: `55.14` at `n=30013`, `100.66` at `n=100003`, `201.32` at `n=400009` ⇒ **`≈ 0.318·√n`** | both strata | **ceiling witness** |
| uniform draw from `A(n)` | `≈ √(2 ln((n−1)/3))` ≈ `3.9 … 4.5` (F7) | both | the matched null |
| `χ₂(y)` — the object | **under test**; `≤ 2` is the hypothesis | — | — |

> **The scale, stated the way `PREREG_row_budget_lowtail_v2.md` F14 states `[0, n−1]`:**
> `S_y` ranges over `[√(n/p), ≈0.318√p]` — at `p = 10⁵` that is `[1.00, ≈100]` — with **both endpoints
> attained by explicit admissible targets**, and a uniform random admissible target concentrated at
> `≈4.1 ± 0.28`. **The claim is that `χ₂(y)` sits at `≤ 2`.** No simulation is needed to bound what any
> admissible target could do.

**F9 — the plant's response is derived, not fitted `[PROVED]`.** Flipping the sign of a fraction `ε` of
the μ₆ orbits (retention `ρ = 1−2ε`) gives, by F6, `E|V_ρ(a)|² = ρ²|V_0(a)|² + (1−ρ²)·n` (ODD; `n−6`
EVEN), and **`mean_a |V_ρ(a)|² = n` exactly at every `ε`** — the plant redistributes spectral mass
without changing the total, so its entire effect on `S` is concentration. Setting the planted max equal
to 2, using only `S_0(a) ≤ 2` (the hypothesis) and `S_null = T`:

```
ε*_pred(p) = (1 − ρ*)/2 ,      ρ*² = 1 − 3/(T² − 1)
```

| `n` | `3.0e4` | `1.0e5` | `4.0e5` |
|---|---|---|---|
| `T` (F7) | 3.861 | 4.112 | 4.441 |
| **`ε*_pred`** | **0.058** | **0.051** | **0.043** |

---

## 3. STATISTICS — one verdict-bearing statistic per question, all named now

### 3.1 PRIMARY (the cap): `S_y(p)`, and the integer count of violations

```
Nviol = # { holdout primes p : S_y(p) > 2 }      integer, 0 ≤ Nviol ≤ 120
```

Deterministic; **a falsifying instance is available at every one of the `≈5.6×10⁶` cells.** No null is
needed for this statistic; its null is the hypothesis itself. Reported per stratum, never pooled across
strata. Every `S_y > 2` candidate is re-decided exactly (`C-PREC`, §4.5).

Also reported: the **achieved margin** `m(p) = 2 − S_y(p)` per prime and its per-band mean — this is the
run's own, model-free power statement (§5.2).

### 3.2 R2 vs R3 — the criterion v1 never had (repair 1)

`L(p) = log₁₀(2 − S_y(p))`, defined only if `Nviol = 0`. Regress `L` on `log₁₀ p`, **separately in each
stratum**, `K = 60` primes each, OLS, `SE(β̂)` from the residuals, `df = 58`.

- **G2 (PRIMARY, self-normalizing):**
  `t₀ = β̂/SE(β̂)` (vs `β = 0`); `t₁ = (β̂ + 0.448)/SE(β̂)` (vs the seen exponent `β = −0.448`).
  - **R2 fires** iff `t₀ ≤ −3.0`.
  - **R3 fires** iff `t₁ ≥ +3.0` **and** `t₀ > −3.0`.
  - otherwise **R-INDET**.
- **G1 (SECONDARY, model-light corroborator):** two-sample `t` on band-mean `L`, top band
  (`log₁₀ p ∈ [5.85,6.00)`) minus bottom band (`[4.50,4.65)`), pooled within-band sd (`df = 50`).
  **Corroborates R2** iff the difference `≤ log₁₀ 0.5 = −0.301`; **corroborates R3** iff `> −0.301`.
- **Both must agree**; disagreement ⇒ **R-INDET** with both printed.

**False-failure rates, computed now** (§5.1), under the EVT-derived residual scatter `σ_L = 0.557/γ`
with `1/γ = 0.448` ⇒ `σ_L = 0.250`, and `SE(β̂) = σ_L/(√K·sd(log₁₀p)) = 0.250/(√60·0.431) = 0.0749`:

| gate | fails by chance when its own hypothesis is TRUE | value |
|---|---|---|
| G2 R2 (`t₀ ≤ −3`), true `β = −0.448` | `P(Z > 2.98)` | **0.14 %** |
| G2 R3 (`t₁ ≥ 3` and `t₀ > −3`), true `β = 0` | `P(Z<−2.98) + P(Z≤−3)` | **0.27 %** |
| G1 corroborate-R2, true `β = −0.448` | `P(Z > 2.11)`, `SE_diff = 0.250·√(2/6) = 0.144` | **1.75 %** |
| G1 corroborate-R3, true `β = 0` | `P(Z < −2.09)` | **1.85 %** |
| **joint: correct call when R2 true** | `(1−0.0014)(1−0.0175)` | **98.1 %** |
| **joint: correct call when R3 true** | `(1−0.0027)(1−0.0185)` | **97.9 %** |

**Robustness clause, pre-committed.** These hold if the measured residual sd `σ̂_L ≤ 0.25`. The run
prints `σ̂_L`. **If `σ̂_L > 0.35`** (at which point the G2-R2 false-failure rate reaches `≈10 %`) **the
design is underpowered at the frozen `K` and the run reports R-INDET with the achieved CI. It does NOT
enlarge `K`, add primes, or re-band.**

### 3.3 The matched null and its firing criterion (repair 3)

**N-PERM (PRIMARY NULL).** Uniformly permute the `M` orbit signs of the real `h`.

| preserves — exactly | destroys |
|---|---|
| length `n−1`; parity `h(−d) = χ₂(−1)h(d)`; μ₆-invariance `h(λd)=h(d)`; the `±1` value multiset; the cell count `(n−1)/6`; Parseval `Σ_a\|V\|² = n(n−1)`; `V(0)`; the estimator, the index set and the code path | **only** the curve's assignment of signs to μ₆ orbits |

`R = 64` draws per prime. `F(p) = #{r : S^{(r)} > 2}/R`; per-prime rank
`π(p) = (1 + #{r : S^{(r)} ≤ S_y})/(R+1)`, floor `1/65`.

**Firing criterion, pre-committed (not merely "exceeds 2"):**
`F(p) = 1` **and** `|median_r S^{(r)} − E[S_null]_EVT| ≤ 4·sd_EVT` (F7), at ≥ 118 of 120 primes.
**Anything else is the F7 HALT, not a discovery.**

**N-ODD (SECONDARY, DECOMPOSITIONAL, NEVER VERDICT-BEARING).** Uniform odd `±1` with μ₆ **not**
imposed. **Registered as a deliberately mismatched null**: it destroys `V(a) = V(aλ)`, which the readout
has by definition, tripling the cell count `M → 3M` and inflating the max by the computable
`a_{3M} − a_M ≈ ln 3/a_M ≈ 0.26`. Its only job is to split the parity contribution from the
parity+μ₆ contribution. **It may not be compared with the real data as a primary null** — that is the
`6–7σ soft shadow` failure mode.

### 3.4 The planted control and its calibration read (repair 2)

`S_y` is a deterministic max, so "detection" is just `S > 2`. Two distinct jobs, kept separate:

**(a) P-CEIL — the must-fire positive control.** The admissible target `ε_O = sign(s_O(1))` (resp.
`cos`), run through the **identical** orbit→Legendre→FFT→max path.
**PASS:** `|V(1)|/√p` equals the pre-computed `2Σ_O|s_O(1)|/√p` to `1e−10` relative, **and** `S > 2`.
This establishes the code path reports values above 2 on an admissible `±1` odd μ₆-invariant target,
which is what v1 had no way to show (D3). **If P-CEIL does not fire, the null is uninformative and the
run issues no verdict, however clean its numbers look.**

**(b) P-FLOOR — the must-fire negative control.** `h = χ_n` where admissible (`p ≡ n mod 4`).
**PASS:** `S = √(n/p)` to `1e−12` relative — the statistic must also be able to reach the exact
Parseval floor. Admissible count printed; forced, zero evidence.

**(c) P-DOSE — the calibration, which is a measurement and never a gate.** Balanced orbit-sign swaps:
choose `j` `+`-orbits and `j` `−`-orbits uniformly and swap, so the value multiset is preserved
**exactly** in both strata; retention `ρ = 1 − 4j/M`, `ε = 2j/M`. `ε = 0` is the real readout; `ε = 0.5`
is exactly N-PERM. **Both endpoints are known in advance** (`≤2` under H-CAP; `≈4.1` by F7).
Ladder, frozen: `ε ∈ {0, 0.005, 0.01, 0.02, 0.03, 0.05, 0.08, 0.12, 0.20, 0.35, 0.50}` (11 levels),
**nested** (`D(ε₁) ⊂ D(ε₂)`, one chain per draw), `R_plant = 32` draws, on the **20 frozen plant primes**
of §6.

```
ε*(p) = min { ε in the ladder : median_r S_ε > 2 }        the fragility number
```

**Pre-committed calibration read, with the number, per the brief:**

| `ε*` | conclusion, fixed now |
|---|---|
| **`ε* ≤ 0.10`** | The cap is **fragile**: corrupting `≤10 %` of the μ₆ orbits breaks it. `χ₂(y)` surviving at 120/120 is therefore **informative**. |
| **`ε* ≥ 0.25`** | The cap **survives corruption of a quarter of the orbits** ⇒ it is close to **vacuous**, and **the question as posed is uninteresting.** Pre-commitment: say exactly that, and promote ARM-2 (§3.5) to the primary object. |
| `0.10 < ε* < 0.25` | Report `ε*` per band with its bootstrap CI and its `p`-scaling; no fragility verdict. |

**Agreement check (derived, not fitted):** `|ε*_meas − ε*_pred| ≤ max(0.5·ε*_pred, 0.01)`, with
`ε*_pred` from F9 computed from the run's own measured `T = median S_null`. Agreement ⇒ the fragility is
**fully accounted for by the additive-noise budget**, so `ε*` alone is not evidence of specialness; what
is evidence is the distance from `ε* ` to `0.5`. Disagreement ⇒ the shape of the real profile (not just
its max) governs the response; that is named as the next prereg's object and may not be reported as a
finding of this run.

### 3.5 ARM-2 — the pooled, targeted shape statistic (so no outcome is only "signal or nothing")

The Parseval rms is forced (`mean_a|V|² = n`), so the threshold is not chosen:

```
N_rms(p) = # { cells a : |V(a)|² > n }        integer count over the M = (n−1)/6 cells
```

Real vs N-PERM, paired per prime, pooled by Stouffer over the 120 holdout primes (never a max over
primes or cells). Null expectation `0.3173·M`. **Pooled 4σ MDE = 0.80 % relative** (§5.3). This is the
statistic that survives if the cap turns out fragile-but-uninformative or parity-explained, and it is
the registered replacement the brief asks for.

**Registered EXPLORATORY companion (non-verdict):** the pooled edge exponent `γ̂` from
`log(1 − u_{(q)})` on `log(q/M)`, `u = |V(a)|/(2√p)`, `q = 1..50`, pooled across all 120 primes
(`≈6000` order statistics — **not** a 3-point fit; `ANOMALY_DRILL_01` failure mode explicitly avoided).
Consistency check with §3.2: `|1/γ̂ + β̂| ≤ 0.10`.

### 3.6 `χ₂(x)` — EXCLUDED from the design, with the reason (repair, D4)

v1 froze `χ₂(x)` as *"context, not controls — no inference is drawn from them"* and then drew the
load-bearing inference from it. **The disclaimer stands and this spec resolves the contradiction by
exclusion, not by promotion.** `S_x` **may not be computed by this run.**

Reason it is not needed: the alternative it was improperly used against — "the estimator, the
max-over-configurations, or the `+1` term caps the statistic at 2" — is excluded twice over, by
controls that take their max over the **same index set** with the **same estimator** and the **same code
path**: **P-CEIL** (an admissible `±1` target that provably reads `≈0.32√p`) and **N-PERM** (which reads
`≈4.1`). Note `χ₂(x)` has *even* parity at **both** `p mod 4` classes and a different sheaf rank, so it
was never a matched comparison anyway. The v1 numbers (`S_x > 2` at 51/193) remain `[SEEN-DATA]` with
their inference withdrawn.

### 3.7 ARM-3 — OPTIONAL, and it repairs the weakest link in the chain

Extend the four-eigenvalue weight-1 computation from `{13, 43}` to **every `p ≡ 1 mod 3` with
`#E(F_p)` prime and `p ≤ 100`**, all `a` in `(n−1)/6` cells, via `V_k` on `E(F_{p^k})`, `k ≤ 4`, plus
Newton identities. Reported as an unforced-cell count (currently **six**). Budget: `O(Σp⁴) ≈ 10⁸`
field operations; if the budget is exceeded the arm is **not run** and §1.2's tag stands unchanged. The
planted eigenvalue 4-tuple control (C2, already fired at `4.4×10⁻¹⁶`) is re-run and must fire.

---

## 4. CONTROLS AND FORCED READOUT CHECKS

### 4.1 Positive controls (must fire; failure ⇒ no verdict)
`P-CEIL` (§3.4a) — predicted value computed from `n` before the run. `N-PERM` firing criterion (§3.3).

### 4.2 Negative controls (must NOT fire)
`P-FLOOR` (§3.4b) — must land on the exact Parseval floor `√(n/p)`, not above it.
`P-SIZE`: `ε = 0` in the P-DOSE ladder must reproduce `S_y(p)` **bit-identically** (integer assertion on
the orbit-sign vector, then `|S_{ε=0} − S_y| = 0`). A ladder whose `ε=0` cell moves is broken.

### 4.3 ⚠ Hasse guard — MANDATORY (v1's fifth instrument bug)
`curve_orbit` returns `ord(G)`, **not** `#E`; when `G` lands in a small prime-order subgroup, `ord(G)`
is prime and a naive primality filter accepts it (v1 admitted `p=1951→n=5`, `p=11833→n=61`, which
dragged every mean down and **would have flipped the R2/R3 reading**). Required, as an **exact integer**
assertion, no float, no `sqrt`:

```
(n − p − 1)² ≤ 4·p        and  isprime(n)  and  n ≡ 1 (mod 6)  and  [n]G = O
```

Any prime failing any clause is dropped **at list-freezing time** (§6), before any `V` is computed, and
the drop is logged with its reason.

### 4.4 Forced readout checks — zero evidence, all must print
`C-PARSEVAL` `Σ_a|V(a)|² = n(n−1)`, rel `≤ 1e−12`, on the real arm, **every** null draw and **every**
plant level. `C-PURITY` (F5), rel `≤ 1e−12`, real and null. `C-CELLS`: `#distinct |V(a)|` over `a≠0`
equals `(n−1)/6` (integer assertion, real and null). `C-HASSE` (§4.3). `C-GEN`: at the two smallest
holdout primes rebuild with `G' = [2]G`; `S_y` identical to `1e−13` (**forced by F1, zero evidence**).
`C-FFT`: at the 5 smallest `p ≡ 1 mod 3` with `n` prime and `n < 200` (instrument primes, **outside the
holdout**, flagged as such), the FFT max is cross-checked against a direct `O(n²)` 60-digit evaluation,
agreement `≤ 1e−40`.

### 4.5 `C-PREC` — how a float never decides the verdict
The FFT is a **screen**. Any cell with `| |V(a)|²/p − 4 | < 10⁻⁶` is escalated:
`numpy.longdouble` → if still within `10⁻¹²`, `mpmath` at 60 digits evaluating `V(a) = Σ_d h(d)e_n(ad)`
from the **exact integer** `h` and the **exact integer** index `ad mod n`. The borderline count is
printed. **If any cell is within `10⁻³⁰` of exactly 2, the run HALTS and reports the exact cell** — an
exact tie is a mathematical event of independent interest, not a data point.

### 4.6 RNG discipline
Every random object is drawn from a stream seeded by
`SHA-256("n1phasecap-v2" | p | stratum | arm | level | replicate)`. N-PERM verdict streams, N-ODD
streams and P-DOSE streams are **disjoint**. No result depends on execution order or on the order of
primes.

---

## 5. POWER — computed now, at the planned sample size

### 5.1 R2/R3 discrimination
`K = 60` primes per stratum, 10 log-spaced bands, `sd(log₁₀ p) = 0.431`, `σ_L = 0.250` (EVT-derived,
§3.2). `SE(β̂) = 0.0749`. **Detectable slope difference at 4σ: `Δβ = 0.30`.** Correct-call rates
**98.1 % (R2 true) / 97.9 % (R3 true)**; per-gate false-failure rates in the §3.2 table, all `≤ 1.85 %`.

### 5.2 The cap
Deterministic: any single cell above 2, confirmed at 60 digits, falsifies. Two power statements:

- **Model-free, reported by the run:** achieved margin `m(p) = 2 − S_y(p)`. The arm then establishes
  *"any cap at `2(1+δ)` with `δ ≥ m/(2−m)`, approached as tightly as the observed maximum at that prime,
  would have fired."* Reported per band with the §6 scope.
- **Design-time, under the `[SEEN-DATA]` extrapolation** `2−S ≈ 0.0081·(p/1.7×10⁴)^{−0.448}` (v1's range
  means and slope; **this extrapolation is itself `[SEEN-DATA]` and may fail**): at the top band
  (`p ≈ 8.4×10⁵`) the predicted margin is `1.4×10⁻³`, i.e. **`δ > 7.1×10⁻⁴` would fire**.

Cells tested: `Σ_p (n−1)/6 ≈ 5.6×10⁶` distinct μ₆ configurations, `≈14×` v1's 402,718.

### 5.3 ARM-2 (`N_rms`)
Per prime `sd = √(0.2166·M)`; pooled `Σ M ≈ 5.6×10⁶` ⇒ relative `SE = 0.200 %`, **4σ MDE = 0.80 %**.

### 5.4 Real vs matched null
Separation `≈ 4.1 − 2.0 = 2.1` against null `sd ≈ 0.28` ⇒ per-prime `z ≈ −7.5`; the rank statistic
bottoms at its floor `1/65` at every prime. Pooled exact sign test over 120 primes bottoms at `2⁻¹²⁰`.
**This is a foregone conclusion given F7 and is registered as an instrument check, not a discovery.**

### 5.5 Cost
Per prime: `n` point additions (one modular inverse each, measured `0.5 s` per `10⁶` at 20-bit `p`),
`n` Legendre symbols (`0.6 s` per `10⁶`), one length-`n` FFT (`0.09 s` at `n = 10⁶`, Bluestein).
Totals: `Σ n ≈ 3.4×10⁷` ⇒ orbit `≈ 90 s`, Legendre `≈ 25 s`; `120×65 = 7800` verdict FFTs `≈ 240 s`;
`20×11×32 = 7040` plant FFTs `≈ 210 s`. **Whole run ≈ 15–30 min**, peak memory `< 250 MB`.

---

## 6. SCOPE — the frozen holdout, defined by a rule that admits no discretion

**All holdout primes satisfy `p > 30000`, so the entire holdout is UNSEEN (§0).**

**Bands (10):** `B_i = [10^{4.50 + 0.15(i−1)}, 10^{4.50 + 0.15 i})`, `i = 1..10`; i.e.
`[10^4.50, 10^4.65), …, [10^5.85, 10^6.00)`. `10^{4.50} = 31623 > 30000`.

**Selection rule, per band, per stratum.** Scan `p` upward from `⌈10^{4.50+0.15(i−1)}⌉`; accept `p` iff:
(a) `p` prime; (b) `p ≡ 7 mod 12` (**ODD stratum**) or `p ≡ 1 mod 12` (**EVEN stratum**);
(c) `n = #E(F_p)` prime; (d) the §4.3 integer Hasse guard holds.
**Take the first 6 accepted primes in each band × stratum.**

> **`K = 60` per stratum, `120` primes total, `Σ (n−1)/6 ≈ 5.6×10⁶` distinct μ₆ configurations.**

**Plant primes (P-DOSE, §3.4c), frozen now:** the **first** accepted prime of each band in each stratum
= **20 primes**. No discretion.

**Generator:** `G` = the point of smallest `x ∈ [1,p)` with `x³+7` a QR, `y` = the square root with the
smaller integer representative. **Forced-irrelevant by F1**; checked by `C-GEN`; may never be reported
as a control.

**Freezing procedure — `C-FREEZE`, mandatory.** The run materializes the list to
`PREREG_n1_phase_cap_v2_HOLDOUT.txt` (columns `band, stratum, p, n, trace`), computes its SHA-256, and
writes the hash to the run log **before any `V(a)` is computed**. Only the selection variables
(`p, n, primality, Hasse`) may be read during freezing. **If the run computes any `S` before the hash is
written, the holdout is void and every outcome cell is capped at `[SEEN-DATA]`.** The list is materialized
by the run, not by this spec, because this spec was written without touching curve data; the rule above
is the freeze.

**The run may not add, drop, re-band or re-order a prime.** A prime rejected by §4.3 is logged with its
reason at freeze time. `p ≢ 1 mod 3` is out of scope (no `λ`, hence no μ₆ collapse). Composite `n` is out
of scope. Other curves `y² = x³ + b` are out of scope.

**Unforced-cell denominators — the only legitimate denominators.** Per prime: `M = (n−1)/6`, never
`n−1`. Cross-prime: `K = 60` per stratum, `120` total, `20` for P-DOSE; every "`k/K` fires" statement
prints the per-prime margin beside it. Null ranks: integer numerator over `R+1 = 65`. ARM-3: the
unforced-cell count, currently **six**.

---

## 7. FALSIFICATION — written before the run

- **H-CAP** — *`S_y(p) ≤ 2` on prime-order `y²=x³+7` curves with `p ≡ 1 mod 3`.*
  **Falsified by a single holdout cell with `|V(a)|² > 4p`**, confirmed at 60 digits by `C-PREC`. One
  cell out of `≈5.6×10⁶`. The arm cannot be talked out of it.
- **H-CURVE** — *the cap is a property of the curve's sign assignment, not of the readout's parity and
  automorphism invariance.* **Falsified if the matched null also obeys the cap** — i.e. if `F(p) = 0` at
  any prime **while all three F7 diagnostics pass**. Given F7 this would refute a derived,
  MC-verified prediction; the run then prints the offending `n` and issues **no verdict on H-CAP**.
- **H-CONV (R2)** — falsified if G2 fires R3 (`t₁ ≥ 3`, `t₀ > −3`) with G1 corroborating.
- **H-PLATEAU (R3)** — falsified if G2 fires R2 (`t₀ ≤ −3`) with G1 corroborating.

**The spec is VOID and no verdict may be issued if:** `P-CEIL` does not fire or misses its pre-computed
value; `P-FLOOR` misses `√(n/p)`; `P-SIZE` shows the `ε=0` cell moving; `C-PARSEVAL`, `C-PURITY`,
`C-CELLS`, `C-HASSE`, `C-GEN` or `C-FFT` fails; `C-FREEZE` was not honoured; or the F7 halt condition
triggers. **A control that cannot fire invalidates the null regardless of how clean the numbers look.**

---

## 8. EXACTNESS

- **Exact `int`, no float (signal path):** curve arithmetic and point counting; the Hasse guard
  `(n−p−1)² ≤ 4p`; `[n]G = O`; the Legendre symbols `pow(y,(p−1)//2,p)` and `pow(d,(n−1)//2,n)`; the
  `⟨λ,−1⟩` orbit construction and canonicalization; `λ` from `λ²+λ+1 ≡ 0 mod n`; the orbit-sign vectors
  and the nested balanced-swap sets `D(ε)`; the autocorrelation `C(Δ)`; every count (`Nviol`, `N_rms`,
  `#distinct |V|`, `M`); every rank and sign test (integer numerator over `R+1`); every RNG seed
  (SHA-256 of an integer string); the SHA-256 of the frozen holdout file.
- **Float carve-out (analytic size only, no key in the path):** the length-`n` FFT producing `|V|`; the
  reported `z`, Stouffer `Z`, OLS `β̂`/`SE`, bootstrap CIs; the `erf`/EVT evaluations of F7 and §5.
  Justification: magnitudes of an analytic exponential sum whose inputs are exact integers — `h(d) ∈
  {0,±1}` and `ad mod n` are exact `int` before the single phase evaluation; no key, index or coordinate
  low bit passes through a float.
- **No verdict is decided by float precision.** The one float threshold (`S ≤ 2`) is a **screen**; every
  borderline cell is re-decided in 60-digit arithmetic from exact integers (`C-PREC`, §4.5), with a halt
  at `10⁻³⁰`. Every null comparison is an integer rank through a bit-identical code path.
- `check_no_float.sh` must pass on the curve / orbit / Legendre / permutation / plant / counting modules
  before the run.

---

## 9. PRE-COMMITTED OUTCOMES — filled in BEFORE the run

**No row licenses a closure, a verdict about ECDLP / extraction / security, or the words
*safe / generic / nothing here / closed / no structure / benign / at the floor / tautological /
obstructed*.** Abstention is legitimate and is **not** a closure. Every number carries the §6 scope.

### The cap

| # | Outcome | Conclusion reported, fixed now | Grade it may earn |
|---|---|---|---|
| **O-C1** | `Nviol = 0`; P-CEIL, P-FLOOR, P-SIZE and all §4.4 checks pass; F7 firing criterion met | **H-CAP holds out-of-sample.** Report per stratum with the achieved margin per band, the `≈5.6×10⁶`-cell denominator, and the §5.2 power statement. **The chain's last link stays `[VERIFIED]`, never `[PROVED]`; N1 is not closed.** Named next objects: (i) the integer circulant `Circ(C)` and its spectral-radius certificate (§1.4); (ii) the weight-1 premise beyond 2 primes (ARM-3). | `[VERIFIED — 120 out-of-sample primes, p ∈ [10^4.5,10^6), y²=x³+7, n prime, Hasse-guarded, ≈5.6×10⁶ distinct μ₆ cells, 0 violations]` |
| **O-C2** | `Nviol ≥ 1`, confirmed at 60 digits | **H-CAP FALSIFIED.** N1's "half of the `4√p` ceiling" framing is wrong and the phase-pairing bound with it. Report the prime, the cell `a`, the exact margin, and re-type the question to *what is the cap* — report `max_p S_y(p)` and its band profile. **G1/G2 are VOID** (`log` of a non-positive number); no R2/R3 call is made. | `[VERIFIED — counterexample, exact at 60 digits]` |
| **O-C3** | A cell within `10⁻³⁰` of exactly 2 | **HALT.** Report the exact algebraic cell. Not a data point. | — |

### The trend (evaluated only under O-C1)

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-T1** | G2 fires R2 **and** G1 corroborates | `S_y → 2`: the cap is approached, so the `½` **is** the phase-pairing constraint at the asymptotic level. Report `β̂ ± CI` per stratum, `σ̂_L`, and the §3.2 false-failure rate beside the call. **Does not close N1** — the inequality remains unproved. `[EMPIRICAL — out-of-sample, K=60/stratum]` |
| **O-T2** | G2 fires R3 **and** G1 corroborates | `S_y` **plateaus** at `2 − ĉ`: a **further constraint on the phases exists**, and that constraint is the object. Report `ĉ` with its CI per stratum and register it as the next prereg's target. `[EMPIRICAL — out-of-sample, K=60/stratum]` |
| **O-T3** | G2 and G1 disagree, or neither gate fires, or `σ̂_L > 0.35` | **R-INDET.** Print `β̂`, its 95 % CI, `σ̂_L`, and both gates. **No R2/R3 call.** Do not enlarge `K`, add primes, or re-band. |
| **O-T4** | The two strata give different calls | Report both. **The `p mod 4` dependence of the approach law is the finding** and is the next object. Never pool the strata. |
| **O-T5** | `\|1/γ̂ + β̂\| > 0.10` (§3.5) | The trend is **not** explained by the edge law of `\|sin θ₁+sin θ₂\|`. That mismatch is named as the object; report both numbers, fit no exponent to few points. |

### The matched null (repair 3 — the crux)

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-P1** | Firing criterion met (`F(p)=1` at ≥118/120, medians within `4 sd_EVT` of F7) | **The cap is NOT forced by parity.** Report: parity + μ₆-invariance + the `±1` multiset + Parseval — every structure the readout has by definition — put a random admissible target at `S ≈ 4.1`, while `χ₂(y)` sits at `≤ 2`, on the same index set, the same estimator and the same code path. **⚠ Mandatory qualifier, bound to F4:** the null does **not** reproduce the Weil ceiling `S ≤ 4`, so the portion of the gap from `4.1` down to `4` is a restatement of Deligne and carries **zero information**; the live content is the factor 2 from `4` to `2`. |
| **O-P2** | `F(p) < 1` at ≥3 primes, or a median off F7 by `>4 sd_EVT` | **HALT — instrument failure, not a discovery.** Print `C-PURITY`, `C-CELLS`, `C-PARSEVAL` for the null draws and name the failing one. |
| **O-P3** | `F(p) = 0` at ≥1 prime **with all three diagnostics passing** | This **refutes F7**, a derived and MC-verified prediction. Print the offending `n`, the null's own `Σ_O s_O²` against `n/4`, and the empirical `S_null` law. **Issue no verdict on H-CAP.** The failure of the derived prediction is the finding. |
| **O-P4** | N-ODD (secondary) and N-PERM differ by more than the computable `≈0.26` cell-count inflation | Report the excess as the **μ₆ layer** of the parity effect, with the inflation subtracted and named. Non-verdict. |

### Calibration (repair 2)

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-K1** | `ε* ≤ 0.10` **and** `ε*` agrees with `ε*_pred` | The cap is **fragile**, and its fragility is **fully accounted for by the additive-noise budget** (F9) — so `ε*` alone is not evidence of specialness. What is evidence: `χ₂(y)` survives where a `≤10 %` orbit corruption does not, and `ε*` sits far below `0.5`. **The 120/120 is informative.** Report `ε*` per band and its `p`-scaling against `ε*_pred ∝ 3/(4(T²−1))`. |
| **O-K2** | `ε* ≥ 0.25` | **The cap survives gross corruption ⇒ it is close to vacuous, and the question as posed is uninteresting.** Say exactly that. Promote **ARM-2** (`N_rms`, §3.5) to the primary object and register the successor prereg on it. This is a legitimate outcome, not a failure. |
| **O-K3** | `0.10 < ε* < 0.25`, or `ε*` disagrees with `ε*_pred` beyond tolerance | Report `ε*` and the full dose curve against the derived `Δ_pred`. A disagreement means the **shape** of the real profile, not its max, governs the response — named as the next object; may not be reported as a finding of this run. |
| **O-K4** | P-CEIL does not fire, or misses its pre-computed value | **"Planted control did not fire; the null is uninformative."** No verdict on H-CAP, however clean the numbers look. **This is not a loop:** P-CEIL's value is derived from `n` alone, so a miss locates the defect in the transform or the normalization, not in the carrier. Print `C-PARSEVAL` and `C-FFT` as the diagnostic. |

### ARM-2 and cross-arm

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-E1** | `N_rms` char vs N-PERM at pooled `\|Z\| > 4` | Positive characterization of the profile shape at the forced Parseval rms, with direction, size, the 0.80 % MDE and the §6 scope. Requires its own prereg before any mechanism is asserted. |
| **O-E2** | pooled `\|Z\| < 4` | **A bounded magnitude, not an absence.** Report the bound with its MDE (0.80 % relative), the §6 scope, and the mandatory unprojected list below. |
| **O-A3** | ARM-3 run | Report the unforced-cell count for the weight-1 premise (currently 6) and update §1.2's tag. If the premise **fails** at any new prime, **every phase-language statement in this run is withdrawn** and only the object-level `S_y ≤ 2` survives. |
| **O-X** | Anything the tables above do not cover | Report the raw numbers, the MDEs, the scope, and **no verdict**. Name the uncovered case explicitly as a gap in this spec. |

### Effect-in-an-unprojected-subspace clause (mandatory)

`S_y` is a **max of a magnitude**, at one prime, in one basis. If every arm lands inside its MDE the run
must **not** report "no structure". It must report (i) the bounded magnitude with its power number and
the §6 scope; (ii) the exact realizable interval `[√(n/p), ≈0.318√p]` of F8, so the bound is a **position
on a known interval with both endpoints attained**; and (iii) this explicit list of what was **not**
projected onto:

**which** cell attains the max and its relation to `λ`, to the CM ideal and to `a`; the **sign** of `V`
(only `|V|` enters; `PREREG_Sy_sign_skew_v1.md` is the separate ledger); the joint law of `(θ₁,θ₂)`
beyond their sine-sum; the higher `V_k` and hence the weight-1 premise (ARM-3); the **integer
autocorrelation `C(Δ)`** and its μ₆ structure (§1.4 — the successor's object); cross-frequency and
cross-prime structure; the `p ≡ 1 mod 4` / `3 mod 4` contrast beyond its slope; `p ≢ 1 mod 3`; composite
`n`; other curves `y² = x³ + b`; `p > 10⁶`; and `p = 2²⁵⁶−2³²−977`.

### Grade cap

`[PROVED]` is available **only** to F1–F9 (the algebra: generator invariance, μ₆ collapse, Parseval,
purity, `Σ_O s_O² = n/4`, the F8 endpoints, the F9 response model) and is graded independently of the
run. **No measured quantity may carry `[PROVED]`.** The cap tops out at `[VERIFIED — 120 out-of-sample
primes, …]`; the trend at `[EMPIRICAL — out-of-sample, K=60/stratum, β̂ ± CI]`; anything computed on
`p < 30000` is `[SEEN-DATA]` and **may not be reported as a pre-registered discovery**. No outcome may be
stated without the §6 scope banner. **Nothing transfers to `p = 2²⁵⁶−2³²−977`.**

---

## 10. WHAT CHANGED FROM v1 — each change named with its justification

| # | element | v1 | v2 | why |
|---|---|---|---|---|
| 1 | pre-registration | none (rule overridden) | this document, before any holdout read | v1 D1 |
| 2 | R2/R3 criterion | none — the call was post-hoc | **G2 (`t₀`,`t₁`, df 58) primary + G1 band-ratio corroborator, each with its false-failure rate computed (§3.2)** | v1 D5; the recurring pass-criterion defect |
| 3 | planted control | **none** | **P-CEIL** (must fire, value derived from `n`) + **P-FLOOR** (exact Gauss-sum floor) + **P-SIZE** | v1 D3 |
| 4 | calibration | none | **P-DOSE**, both endpoints known in advance, `ε*` with a pre-committed fragility threshold **and a number** | brief repair 2 |
| 5 | null | none (a random unit-modulus *complex* readout, non-matched, declared non-inferential) | **N-PERM**, matched on parity, μ₆, multiset, cell count, Parseval, code path; **N-ODD** as a disclosed mismatched decomposition layer | brief repair 3 |
| 6 | the parity question | unexcluded | **settled in advance by F7**, derived + MC-verified on synthetic `Z/n`, with an explicit HALT if the control contradicts it | brief repair 3 |
| 7 | `χ₂(x)` | frozen as non-inferential, then used as the load-bearing inference | **excluded from the design; may not be computed** | v1 D4 — the contradiction is resolved by exclusion, not promotion |
| 8 | out-of-sample | none | **120-prime frozen holdout, `p ∈ [10^4.5,10^6)`, rule-defined, SHA-256'd before any `S`** | v1 D6 |
| 9 | strata | pooled | **`p ≡ 1 mod 12` and `p ≡ 7 mod 12` never pooled** (different parity ⇒ different forced law) | F6 gives different exact constants |
| 10 | exactness of the verdict | float FFT comparison to 2 | **`C-PREC` 60-digit escalation + `10⁻³⁰` halt** | the no-float rule: a float may not decide a verdict |
| 11 | Weil ceiling | unstated | **F4 named as forced**, and O-P1 is bound to disclose that the null exceeds it | forced quantities carry zero information and must be named |
| 12 | object typing | a magnitude | **§1.4: the integer circulant `Circ(C)` and its spectral radius** | a magnitude is a size, not a structure |
| 13 | weight-1 premise | implicit | **§1.2 tag on every phase sentence; ARM-3 to extend it past 2 primes** | object-vs-proxy |

### Carried over untouched
The object `V(a)` and its normalization; the μ₆ collapse and the `(n−1)/6` denominator; the Hasse guard;
the forced purity check; `R = 64`; the `p ≡ 1 mod 3` restriction; the exactness rules and the float
carve-out; the rule that "a different generator" is never a control; the rule that abstention is
legitimate and is not a closure.

---

## 11. DEVIATION DISCIPLINE

Any change to the statistic, the band definition, the selection rule, `K`, `R`, `R_plant`, the `ε`
ladder, the gate thresholds (`t₀ ≤ −3`, `t₁ ≥ +3`, `−0.301`, `σ̂_L > 0.35`, `ε* ∈ {0.10, 0.25}`), the
null constructions, the control set, the `C-PREC` escalation levels, or the outcome tables must be
written to **`PREREG_n1_phase_cap_v2_DEVIATIONS.md` BEFORE the holdout is read**, with the
pre-committed value, the actual value, and the handling. **A deviation is not necessarily wrong — it is
necessarily disclosed.**

If the run is stopped early, the deviations file must state how many bands were completed; **partial
results are reported per band with their own `K` and their own recomputed power, never pooled to the
frozen `K`.**
