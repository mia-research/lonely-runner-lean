# PREREG — the row budget and the low tail: is the near-zero excess a shadow of `Σ_a |U|² = n(n−1)`?

**File:** `PREREG_row_budget_lowtail_v1.md`  **Date:** 2026-07-24  **Status: PRE-RUN.**
Executes the probe named verbatim in `RESULT_subrayleigh_deficit_locus_v1.md` §7.

**No arm statistic in this document has been computed.** The only code executed while writing this
spec was (i) point-counting `#E(F_p)` for `y²=x³+7` to fix the curve population (§6), and (ii) pure
integer enumeration of `μ₆×conj` orbits on the frequency plane to emit the frozen frequency lists.
Neither touches `U`, an FFT, a phase, or any statistic below.

**Frozen input artifacts (committed with this spec):**

| file | SHA-256 | lines |
|---|---|---|
| `PREREG_row_budget_lowtail_v1_FREQS.txt` (generic stratum) | `9695989bcd52777dc3e3012477dd460f5f29ffcd0da099d09bf7294d983005f3` | 87345 |
| `PREREG_row_budget_lowtail_v1_FREQS_SPECIAL.txt` (`c=0` and `b=0` strata) | `dfa9f7a40d27a03f906e9fb03d6466775b980b28c62a04e6675792124811ee9e` | 6145 |

The run **must** read `(p,b,c)` from these files. Generating frequencies at run time is a deviation.

**Scope banner (inherited by every number this run produces, and never omitted from any of them).**
Enumerable model curves `E : y² = x³ + 7` over `F_p`, `p` in the frozen 10-prime list of §6, group
order `n = #E(F_p)` prime, `d = 1..n−1` fully enumerated, generic `μ₆×conj` frequency stratum
except where a special stratum is named. `p = 2²⁵⁶−2³²−977` is **not** enumerable and **nothing
here transfers to it** — every object below is a full group sum over all `d`. No ECDLP, extraction,
or security claim is made or may be derived from any outcome.

---

## 1. OBJECT

Curve data fixed by `t_y_maxbound_v1.prime_order_curve` / `group_coords` (exact `int` arithmetic):
`(x_d, y_d)` = affine coordinates of `[d]G`, `d = 1..n−1`; `d = 0` (point at infinity) excluded.

```
s_{b,c}(d) = e_p(b·x_d + c·y_d)                      unit modulus, d = 1..n−1
U(a,b,c)   = Σ_{d=1}^{n−1} s_{b,c}(d) · e_n(a·d)     a ∈ Z/n
ρ(a; b,c)  = |U(a,b,c)|² / (n−1)
r(a; b,c)  = |U(a,b,c)| / √(n−1)                     so ρ = r²
```

**The object measured is the SHAPE of the row profile `ρ(· ; b,c)` — the length-`n` vector indexed
by `a` at a FIXED frequency `(b,c)` — for the real curve labelling versus for matched relabellings.**
It is not a marginal over `(b,c)` at fixed `a`; that is the axis the prior run measured.

For fixed `(b,c)`, `U(·,b,c)` is exactly one length-`n` DFT of `s_{b,c}` (zero-padded at `d=0`), so

> **`Σ_{a mod n} ρ(a; b,c) = n`  exactly, for every `(b,c)`** — Parseval, `[PROVED]`, holds for any
> unit-modulus function of `d`.

`π_{b,c}(a) := ρ(a;b,c)/n` is therefore an exact probability vector on `Z/n`. The object is the
shape of that vector.

**Normalization is compatible with the prior run.** The prior used `r̃ = |U|/σ̂`,
`σ̂² = p²(n−1)/(p²−1)`. Here `r/r̃ = p/√(p²−1) = 1 + 1/(2p²) + O(p⁻⁴)`, so the prior's low-tail
threshold `r̃ < 0.10` is `r < 0.10·(1 + 1/(2p²))`. **We freeze the threshold in the new
normalization at exactly `ρ < 0.01`** and note the `1.9e−5` relative offset from the prior's
threshold at `p = 163` (smaller at every larger prime). No threshold is being chosen here: `0.10`
is inherited from `RESULT_subrayleigh_deficit_locus_v1.md` §3.

**Tautology check.** The feature (the curve's `d ↦ (x_d,y_d)` labelling) and the target (the
character family `e_n(ad)`) share the index `d`. This is the object, not an artifact: every control
in §3 holds the point SET, the frequency list, `p`, `n`, and the readout fixed and changes **only**
the `d`-labelling. The statistic is a joint property of the point set at one frequency, never a
per-point readout. This is **not** the `r = v − w` residue-vs-component tautology
(`feedback_residue_vs_component_tautology_2026_07_14`): no quantity is regressed on a quantity it
was constructed from.

**Symmetry structure of the object, derived pre-run `[PROVED]`.** Write `β ∈ F_p^*` of order 3 and
`λ ∈ (Z/n)^*` of order 3 with `x_{λd} = β x_d`, `y_{λd} = y_d` (the `j=0` / CM endomorphism;
`p ≡ 1 mod 6` and `n ≡ 1 mod 3` are verified for all 10 primes in §6). Then

| identity | source | consequence for `ρ(·;b,c)` |
|---|---|---|
| `s_{b,c}(λd) = s_{βb,c}(d)` | GLV endomorphism | `ρ(a; βb, c) = ρ(λ⁻¹a; b, c)` |
| `s_{b,c}(−d) = s_{b,−c}(d)` | `[−1] : (x,y)↦(x,−y)` | `ρ(a; b, −c) = ρ(−a; b, c)` |
| `conj U(a,b,c) = U(−a,−b,−c)` | formal, any sequence | `ρ(a; b, c) = ρ(−a; −b, −c)` |
| composition of the last two | — | **`ρ(a; b, c) = ρ(a; −b, c)` elementwise** |

Hence **every symmetric functional of `{ρ(a;b,c)}_a` is constant on the orbits of the order-12
group `(b,c) ↦ (u·b, ±c)`, `u ∈ μ₆ ⊂ F_p^*`.** Generic orbits (`b≠0, c≠0`) have size exactly 12
(verified by brute-force enumeration at `p=163`: all 2187 orbits of size 12, `2187 = 162²/12`).
`c=0` orbits have size 6; `b=0` orbits have size 2; `(0,0)` is a fixed point.

**Generator choice is not a free parameter and not an independent null.** `G' = [s]G` gives
`x'_d = x_{sd}`, hence `U'(a,b,c) = U(a s⁻¹, b, c)` — a permutation of rows. **Every statistic in
this spec is invariant under the choice of `G`** `[PROVED]`. Constraint: "a different generator"
may never be reported as a control.

## 2. WHAT IS FORCED — and therefore carries zero information

Stated before the run so that no forced quantity can later be reported as a result.

- **F1 (the reason the naive test is void).** `Σ_a ρ(a;b,c) = n` holds identically for the real
  system **and for every unit-modulus target**. "Is the low tail at one row compensated at other
  rows?" therefore has the answer **yes, always, as an arithmetic identity**. The question carries
  zero information and **is not asked in this spec.**
- **F2.** A deficit of order 1 in `ρ(a₀)` spread over the other `n−1` rows is `O(1/n)` per row —
  forced and unmeasurable. No per-row compensation magnitude may be reported as a finding.
- **F3.** `ρ(a;0,0) = n−1` at `a=0` and `1/(n−1)` at every `a≠0`, exactly. `(0,0)` is excluded from
  every frequency list; its profile is printed once as a forced check.
- **F4.** `U(0,b,c) = Σ_d s_{b,c}(d)` depends only on the value **multiset** of `s_{b,c}`, which
  every null in §3 preserves exactly. **The `a=0` row is identical in every arm** and is excluded
  from every statistic. Printed as an exact forced check (`|U_char(0,f) − U_null(0,f)| = 0` to
  machine zero at every `f`).
- **F5 (this one shapes the design).** For any function `φ`, the doubly-pooled additive functional
  `Σ_{(b,c)} Σ_a φ(r(a,b,c))` over the FULL frequency grid equals `Σ_a [Σ_{(b,c)} φ(r(a,b,c))]`,
  i.e. the sum over `a` of the **prior run's `(b,c)`-marginal at each `a`**. Given Arm 4 of
  `RESULT_subrayleigh_deficit_locus_v1.md` (every character behaves like `a₀`), this is `≈ n ×` a
  number already measured, up to the `1 + O(p⁻²)` normalization offset. **Consequence, pre-declared:
  the CHARACTER-side value of the primary statistic is not new information.** All new content of
  this run is in the **null side** — i.e. in which relabelling group the character is compared
  against. §3 is therefore the load-bearing section of this spec, not §2 or §4.
- **F6.** Sampling `(b,c)` without orbit reduction inflates the denominator by up to 12× in forced
  duplicate bits. **Every tally in this run is denominated in `μ₆×conj` orbits** (§6), never in
  `(b,c)` pairs and never in rows.
- **F7.** `c=0` ⇒ `ρ(a;b,0) = ρ(−a;b,0)` (within-profile symmetry). `b=0` ⇒ `U(a,0,c) ∈ R` for
  every `a`, and `ρ(a;0,c) = ρ(−a;0,c)`. Both special strata have structurally different profile
  laws **by construction**, and a null that does not commute with `d ↦ −d` destroys a symmetry the
  real system has by definition. **On the special strata, a free label shuffle is an invalid null**
  (this is the `6–7σ soft shadow` failure mode). The strata are analysed separately, with
  negation-commuting nulls only, and are never pooled with the generic stratum.
- **F8 (realizable extremes, exact).** The primary `N_LOW` (§3) has an exactly attained range on
  realizable unit-modulus targets:
  - chirp `s(d) = e_n(κd²)`, `κ ≢ 0`: `U(a)` = (complete quadratic Gauss sum) `− 1`, so `|U(a)| ∈ [√n−1, √n+1]`
    and `ρ(a) ≥ (√n−1)²/(n−1) > 0.01` for every `n ≥ 5` ⇒ **`N_LOW = 0` exactly, at every `a`, every
    prime.** `[PROVED]`
  - pure tone `s(d) = e_n(−a*d)`, `a* ≠ 0`: `ρ(a*) = n−1`, `ρ(a) = 1/(n−1)` otherwise ⇒
    **`N_LOW = n−2` exactly** (all `n ≥ 102`, hence all 10 primes). `[PROVED]`

  So `N_LOW ∈ [0, n−2]` and the unconstrained-Rayleigh reference sits at `(n−1)(1−e^{−0.01})`,
  i.e. `≈ 1/100` of the way up the realizable range at every prime (ratio `99.8 → 100.5`, §6 table).
  **No simulation is needed to bound what any realizable target could do.**

## 3. STATISTIC — exactly one primary, plus a NESTED NULL LADDER that decomposes it

### 3.1 Primary (the only verdict-bearing quantity)

```
N_LOW(f)  = #{ a ∈ Z/n, a ≠ 0 :  |U(a,f)|² < 0.01·(n−1) }          integer count
N̄(p)      = (1/m_p) Σ_{f ∈ F_gen(p)} N_LOW(f)                       f from the frozen list
```

Per prime, the verdict scalar is the position of the character's `N̄` in the primary null's
replicate distribution:

```
z_p        = ( N̄_char − mean_r N̄^{(r)}_{MN-μ6} ) / sd_r( N̄^{(r)}_{MN-μ6} )
p_p (exact) = ( 1 + #{ r : N̄^{(r)}_{MN-μ6} ≥ N̄_char } ) / (R + 1)       integer rank, R = 64
```

Pooled across the frozen 10-prime list: **Stouffer `Z = Σ_p z_p / √10`** and a 10-prime **sign
test**. Pooled, never a max over primes or over frequencies.

**Why a low-tail count and not a moment.** `RESULT_subrayleigh_deficit_locus_v1.md` §3 localized the
prior effect at `r < 0.10`, where `r⁴ ≈ 10⁻⁴` — the fourth moment has essentially no sensitivity
there, which is exactly why the prior Arm 2 returned null while Arm 1 localized. `N_LOW` puts unit
weight on precisely the cells `M4` cannot see and zero weight elsewhere. It is not a fourth moment,
and it is not the quadruple-coincidence histogram in disguise: `Σ_a |U|⁴ = n Σ_Δ |A(Δ)|²` with
`A` the autocorrelation of `s_{b,c}`, an identity that `N_LOW` does not satisfy in any form.
**Constraint 1 satisfied.**

**Why it is not a re-basing.** The `a`-DFT is unitary and `Σ_a ρ = n` is basis-invariant, so no
change of basis can create concentration. `N_LOW` is not a total, not a norm and not linear: it is
a count of cells in a fixed, pre-inherited window of a fixed basis. **Constraint 2 satisfied**, with
the corollary stated: the row profile carries no more information than `s_{b,c}` itself; this run
tests the shape in this one basis and says nothing about others (see §9, unprojected clause).

### 3.2 The nested null ladder — four named layers, additive by construction

All four comparisons use **the identical frozen frequency list and the identical code path**;
they differ only in which group the `d`-relabelling permutation `π` is drawn from. Write
`s'_f(d) = s_f(π_f(d))`. Every `π` is a bijection of `{1,…,n−1}`, so **every null preserves unit
modulus, the exact value multiset of `s_f`, the row conservation `Σ_a ρ' = n`, and `U(0,f)` — all
exactly** (constraint 4 satisfied: the null satisfies the conservation).

| null | `π` drawn from | preserves, beyond the above | destroys | valid on |
|---|---|---|---|---|
| **MN-μ6 (PRIMARY)** | permutations commuting with `d ↦ ±λ^i d` | the full `⟨λ,−1⟩ = μ₆` orbit structure of the `d`-labelling | the group-law / arithmetic alignment of `d` with the coordinate map, beyond `μ₆` | all strata |
| **MN-neg** | permutations commuting with `d ↦ −d` | the `[−1]` (negation) pairing only | additionally the order-3 CM/GLV layer | all strata |
| **MN-free** | all `(n−1)!` permutations (**= the prior run's MC2, transposed**) | nothing beyond multiset/modulus/budget | additionally the negation pairing | **generic stratum only** (F7) |
| **REF-RAY** | not a null — the analytic reference `E[N_LOW] = (n−1)(1−e^{−0.01})` | — | — | reported as a scale, never as a verdict null |

**Construction of `π` (exact integers).** `μ₆ = {±1, ±λ, ±λ²} ⊂ (Z/n)^*` acts freely on
`{1,…,n−1}` (`n` prime ⇒ `ud = d` forces `u = 1`), giving `(n−1)/6` orbits. Pick a uniform
permutation `σ` of the orbits and a uniform `u_O ∈ μ₆` per orbit; set `π(u·d_O) = u·u_O·d_{σ(O)}`.
This commutes with `μ₆` by construction. MN-neg is the same construction with `μ₆` replaced by
`{±1}`. `λ` is **derived from the curve data**, never chosen independently of `β`: assert
`max_d ((x_{λd} − β x_d) mod p) == 0` as an exact integer assertion before any null is drawn (this
is the guard for the `p=433/577` pairing bug recorded in the prior run's deviations).

**One `π_f` per frequency, drawn independently across `f`.** Justification, pre-declared: the row
conservation and the multiset preservation are per-frequency properties, so independence across `f`
costs the null nothing that the primary statistic uses, and it makes the null's variance honestly
`Var(N)/m` rather than dominated by a permutation-common component. A shared-`π` variant
**MN-μ6-shared** (one `π` per replicate, all frequencies) is run at the same `R`; if its null `sd`
exceeds MN-μ6's by more than 3×, the primary `z_p` is **also** reported against the shared null and
**the more conservative of the two is the verdict**. Pre-committed; not a post-hoc choice.

**The decomposition.** Because the four levels are nested, the differences

```
(char − MN-μ6)   =  group-law / arithmetic alignment beyond μ₆
(MN-μ6 − MN-neg) =  the order-3 CM/GLV (λ) layer of the d-labelling
(MN-neg − MN-free) = the negation ([−1]) layer of the d-labelling
(MN-free − REF-RAY) = the unit-modulus / exact-multiset / row-budget layer
```

sum **exactly** to `char − REF-RAY`. Like the prior Arm 1, this arm therefore **always localizes**;
it cannot return "nothing". Each layer is a named group-theoretic object, not a residual.

### 3.3 Pre-committed secondaries — reported, **never verdict-bearing on their own**

| id | quantity | why it is named now |
|---|---|---|
| **S1 coupling** | `Θ_p` = Spearman rank correlation across `f ∈ F_gen` between `N_LOW(f)` and `B_HIGH(f) := (1/n)Σ_{a≠0, r>1.5} ρ(a;f)` (the prior's own HIGH-zone edge). Integer mid-ranks. Compared to `{Θ_p^{(r)}}` by rank. | The ONLY statistic here that is not an additive marginal (F5) and can distinguish "the low tail is slaved to the top at the same frequency" from "the low tail is row-local". A large forced positive coupling is present in **both** arms (fixed budget); only the char−null **difference** is read. |
| **S2 dispersion** | `D_p = Var_f(N_LOW)/mean_f(N_LOW)` | over/under-dispersion of the low tail across frequencies; `≈1` under row-independence. |
| **S3 order statistic** | the `⌈0.01(n−1)⌉`-th smallest `ρ` in each profile, pooled median | threshold-free robustness twin of the primary; **must agree in sign with the primary**. Disagreement ⇒ arm reported UNRESOLVED (§9 O9). |
| **S4 top** | `mean_f max_{a≠0} ρ`, `mean_f B_HIGH` | the Weil-ceiling side of the budget. Declared a **max over cells** and therefore upward-biased and low-power — reported with that label, never as a verdict. |
| **S5 low-set symmetry** | `μ₆`-orbit occupancy of `{a : ρ(a;f) < 0.01}` within each profile, `χ²` against uniform-over-orbits, pooled | This is the "effect in an unprojected subspace" probe. `N_LOW` is symmetric in `a` and **blind to which rows are low**. Unforced at generic `f` (§1: the `μ₆` identities relate different frequencies, not rows within one). **If S5 fires at `|z| > 4`, it is the object of the NEXT prereg and may not be reported as a finding of this run.** |
| **S6 strata** | primary recomputed on `c=0` and `b=0` separately, MN-μ6 and MN-neg only | F7. Never pooled with the generic stratum. |

## 4. PLANTED CONTROLS — two different objects, built separately (constraint 6)

### 4.1 P-DET — does the detector fire? (tests the statistic)

Interpolation between the real system and the exact realizable maximum (F8). For each `f`, draw
`a*_f ∈ (Z/n)^*` and `D_f ⊂ {1,…,n−1}` with `|D_f| = round(ε(n−1))`, both from a frozen seed; set

```
s^{(ε)}_f(d) = e_n(−a*_f · d)   for d ∈ D_f ;    = s_f(d)   otherwise
```

Unit modulus is preserved exactly ⇒ the row conservation is preserved exactly (printed check).
`ε = 0` is the character system; `ε = 1` is the pure tone.

**Injection level swept:** `ε ∈ {0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 1.00}`.

**Derived pre-run prediction (not fit).** The tone spike carries `ρ(a*) ≈ ε²(n−1)`, i.e. budget
share `≈ ε²`; the remaining `n−1` rows share mean `≈ 1 − ε²`, so for exponential-like off-tone rows
`N_LOW` scales by `1/(1−ε²)`:

| `ε` | 0.05 | 0.10 | 0.15 | 0.20 | 0.30 | 0.50 | 1.00 |
|---|---|---|---|---|---|---|---|
| predicted relative excess `ε²/(1−ε²)` | +0.25% | +1.01% | +2.3% | +4.2% | +9.9% | +33% | **`N_LOW = n−2` exactly** |

**Pass criteria — all four must print PASS before any verdict is issued:**
1. `ε = 1.00` returns `N_LOW = n−2` **exactly**, at every `f`, every prime (integer assertion).
2. The chirp `s(d) = e_n(κd²)`, `κ = 1`, returns `N_LOW = 0` **exactly**, at every `f`, every prime
   (integer assertion). This is the negative-direction control: it proves the statistic can also
   go to the floor, not only up.
3. `N̄(ε)` is **strictly increasing** across the seven swept levels at every prime.
4. `z(ε = 0.20)` vs MN-μ6 exceeds `+6` at every prime with `p ≥ 577`.

Also reported (calibration, not a pass criterion): the smallest swept `ε` with `z > 4` — the
detector's **measured** MDE, to be compared with the computed MDE of §5.

**If any of 1–4 fails, the primary reports "planted control did not fire; the null is
uninformative" and issues NO verdict, however clean its numbers look.** If criterion 3 holds but the
measured excess at `ε=0.20` falls outside `[2.1%, 8.4%]` (factor 2 of the derived 4.2%), the
detector is declared **calibrated but mis-modelled**: the measured `ε`-response replaces the derived
one, and this is recorded as a deviation.

### 4.2 P-SEP — separation from a REALIZABLE null (a different object)

`{s_{b,c}}` is unit-modulus by construction, so the realizable row profiles are exactly the
periodograms of unit-modulus sequences; F8 pins the attainable range of the primary to `[0, n−2]`
**exactly, with both endpoints attained by explicit realizable sequences**, and places the
unconstrained-Rayleigh reference at `≈ 1%` of that range. P-SEP therefore requires **no simulation**:
the run prints, per prime, `N̄` for char / MN-μ6 / MN-neg / MN-free / REF-RAY / chirp / tone on this
single exact scale. Any effect this run can report is a movement on a scale whose ends are known
exactly in advance. (Note the analogous frequency-side constraint from the prior work: `{U_g}` spans
only an `(n−1)`-dimensional subspace of the `p²` frequencies, so no realizable target can concentrate
on a small fraction of frequency space — that bound is on the other axis and is not re-derived here.)

### 4.3 Forced readout checks — zero evidence, must all be printed

| id | check | tolerance |
|---|---|---|
| **C-BUDGET** | `Σ_a \|U(a,f)\|² = n(n−1)` for char, every null draw, every plant level | rel `≤ 1e−12` |
| **C-A0** | `U_char(0,f) = U_null(0,f)` exactly (F4) | rel `≤ 1e−13` |
| **C-EQ-int** | `max_d ((x_{λd} − β x_d) mod p) == 0` with `β` **derived from the data** | exact integer `== 0` |
| **C-EQ-flt** | `ρ_char(a; βb, c) = ρ_char(λ⁻¹a; b, c)` and `ρ_char(a;b,c) = ρ_char(a;−b,c)` elementwise | rel `≤ 1e−11` |
| **C-NULLSYM** | the same two identities hold for MN-μ6, hold for MN-neg only in the `−b` form, and **fail** for MN-free | printed as PASS/PASS/FAIL — a FAIL here for MN-free is *required*; if MN-free passes, the null construction is wrong and the run halts |
| **C-GEN** | recompute the primary at `p = 349` with `G' = [s]G`, `s = 2`; `N̄` identical | rel `≤ 1e−14`; forced (§1), zero evidence |
| **C-PREC** | every row with `\| \|U\|²/(n−1) − 0.01 \| < 1e−6 · 0.01` recomputed at 50 decimal digits (`mpmath`); the count of such borderline rows is printed; any flip is reported | expected `< 1` row per prime |

## 5. POWER — computed now, at the planned sample size

Cell budget frozen by the rule `m_p = min( N_orb_gen(p), ⌊1.6e7 / (n−1)⌋ )`, `R = 64` replicates
per null. `N_LOW` cells per prime `= m_p·(n−1)`; expected count `T_p = m_p(n−1)(1−e^{−0.01})`;
relative `sd(N̄) = 1/√T_p` (row-level dependence induced by the fixed budget is `O(1/n)` per pair
and shifts this by `≈ 1%` of itself — negligible, and the run reports the **measured** null `sd`
alongside).

| `p` | `n` | `m_p` (orbits) | exhaustive | cells | `E[T_p]` | rel `sd` | **MDE @4σ** | Spearman `sd` (S1) | MDE(Θ) @4σ |
|---|---|---|---|---|---|---|---|---|---|
| 163 | 139 | 2187 | **yes** | 301 806 | 3 003 | 1.825% | **7.30%** | 0.0214 | 0.086 |
| 211 | 199 | 3675 | **yes** | 727 650 | 7 240 | 1.175% | **4.70%** | 0.0165 | 0.066 |
| 349 | 313 | 10 092 | **yes** | 3 148 704 | 31 330 | 0.565% | **2.26%** | 0.0100 | 0.040 |
| 433 | 397 | 15 552 | **yes** | 6 158 592 | 61 279 | 0.404% | **1.62%** | 0.0080 | 0.032 |
| 577 | 613 | 26 143 | no | 15 999 516 | 159 198 | 0.251% | **1.00%** | 0.0062 | 0.025 |
| 991 | 1009 | 15 873 | no | 15 999 984 | 159 203 | 0.251% | **1.00%** | 0.0079 | 0.032 |
| 2089 | 2143 | 7 469 | no | 15 998 598 | 159 189 | 0.251% | **1.00%** | 0.0116 | 0.046 |
| 4159 | 4243 | 3 771 | no | 15 996 582 | 159 169 | 0.251% | **1.00%** | 0.0163 | 0.065 |
| 9319 | 9127 | 1 753 | no | 15 997 878 | 159 182 | 0.251% | **1.00%** | 0.0239 | 0.096 |
| 19 231 | 19 501 | 820 | no | 15 990 000 | 159 103 | 0.251% | **1.00%** | 0.0349 | 0.140 |

**Pooled over the 10 primes: `Σ T_p = 1 057 895`, relative `sd = 0.097%`, MDE @4σ = `0.39%`
relative in `N_LOW`.** Pooled S1: `sd(Θ) = 0.0034`, MDE @4σ = `0.014`.

**What this buys, stated as a size and not as a verdict.** The prior run's low-tail excess on the
`(b,c)` axis was `+7.8% … +14.3%`. An effect of that size on the row axis would give pooled
`Z ≈ 80`; an effect 20× smaller (`0.4%`) is still at the pooled 4σ MDE. At the four smallest primes
the frequency stratum is **exhaustive** (no frequency sampling error at all), but their per-prime
MDE is `1.6% … 7.3%` — **`p = 163` and `p = 211` are individually underpowered against anything
below `≈5%` and must not be read individually**; they enter only the pooled `Z` and the sign test.
`R = 64` fixes the null mean to `sd/8` and the null `sd` to `±8.9%` relative; increasing `R` does
not increase power for the primary, only the resolution of the exact rank `p`-value (floor
`1/65 = 0.0154`).

**Cost model.** `(R+1)·m_p` length-`n` FFTs per prime per null level, `= 5.68e6` FFTs total for the
generic stratum across the ladder's primary null; `×3` for the three null levels plus `×7` for the
P-DET sweep at reduced `R`. Batched `numpy.fft` over chunks of ≤1024 rows keeps peak memory under
300 MB at every prime (`m_p·n·16 B` never exceeds 256 MB even unchunked). Prime `n` triggers
Bluestein; the largest transform is `n = 19501 → 65536`. **Arm cost is `O(m·n log n)`, not
`O(p²n)`** — this is why the ladder reaches `p = 19231`, 9.2× the prior run's ceiling.

## 6. SCOPE

**Frozen curve population** (computed at spec-writing time by full point-counting of `y²=x³+7`;
`p ≡ 1 mod 6` and `n ≡ 1 mod 3` verified for all ten, so `β` and `λ` both exist):

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `n` | 139 | 199 | 313 | 397 | 613 | 1009 | 2143 | 4243 | 9127 | 19501 |
| trace `p+1−n` | 25 | 13 | 37 | 37 | −35 | −17 | −53 | 83 | −193 | 269 |
| `β` (order 3 in `F_p^*`) | 58 | 14 | 122 | 198 | 213 | 113 | 826 | 1604 | 3138 | 9365 |

The first seven are exactly the prior run's list, kept **whole** — including `p = 211`, whose prior
`z` was `−0.63`. Dropping it would be a silent post-hoc filter. The three new primes are the first
qualifying prime-order `y²=x³+7` curves found in the windows `[4000,4600]`, `[9000,9600]`,
`[19000,19600]`, chosen before any statistic was computed. `p ≈ 40000` was searched
(`[40000,40600]`, none qualifying) and is **not** in scope; the run may not add a prime.

**Frozen frequency population.** Generic stratum `b≠0, c≠0`: `N_orb_gen = (p−1)²/12` orbits of the
order-12 group `(b,c) ↦ (ub, ±c)`, `u ∈ μ₆`. Canonical representative = `(min_{u∈μ₆}(ub mod p),
min(c, p−c))`, exact integer. Sampling: exhaustive when `N_orb_gen ≤ ⌊1.6e7/(n−1)⌋`, else uniform
without replacement over orbit representatives with seed `20260724·10⁶ + p`. Special strata `c=0`
(`(p−1)/6` orbits) and `b=0` (`(p−1)/2` orbits), capped at `⌊4e6/(n−1)⌋`, seeds `+1` / `+2`.
**All lists are emitted, hashed, and committed with this spec** (header of §0). `(0,0)` is excluded
(F3).

**Generator.** `G` = the point of smallest `x ∈ [1,p)` with `x³+7` a QR, `y` = the `tonelli` root,
as returned by `t_y_maxbound_v1.prime_order_curve`. Forced-irrelevant (§1, C-GEN).

**Unforced-cell denominators — the only legitimate denominators in this run.**
- Frequency tallies: `m_p` **orbits** (never `12 m_p` pairs).
- Row tallies within a profile: `n−1` (the `a=0` row is forced, F4).
- Cross-prime tallies: `K = 10`, the whole frozen list. A "`k/K` fires" statement must use `K = 10`
  and must print, beside it, each prime's MDE from §5. Underpowered primes are flagged, never
  dropped.
- Rank `p`-values: integer numerator over `R+1 = 65`.

## 7. FALSIFICATION — written before the run

The hypothesis under test, from `RESULT_subrayleigh_deficit_locus_v1.md` §7:

> **H-BUDGET.** The near-zero excess is a shadow of the exact per-frequency row budget — i.e. it is
> produced by any target sharing unit modulus, the exact value multiset, the budget
> `Σ_a ρ = n`, and the `μ₆` label structure, and is therefore reproduced by MN-μ6.

**H-BUDGET is falsified if** the pooled Stouffer `Z` for `N̄_char` vs MN-μ6 exceeds `+4` **and** the
sign test is `≥ 8/10` in the same direction **and** S3 (the order statistic) agrees in sign **and**
all four P-DET criteria and all seven forced checks of §4.3 passed. In that case the low tail
survives a null carrying the entire budget structure, so the budget is not what makes it, and the
surviving layer is `char − MN-μ6` = the group-law/arithmetic alignment beyond `μ₆`.

**The spec itself is void, and no verdict may be issued, if:** any P-DET criterion fails; the chirp
control does not return `N_LOW = 0` exactly; the tone control does not return `N_LOW = n−2` exactly;
C-EQ-int fails; C-NULLSYM shows MN-free *passing* the `−b` identity; or C-BUDGET drifts beyond
`1e−12`. A control that cannot fire invalidates the null regardless of how clean the numbers look.

## 8. EXACTNESS

- **Exact `int` (no float anywhere in the path):** curve arithmetic (`ec_add`, `group_coords`);
  point counting; the `μ₆` and `⟨λ,−1⟩` orbit constructions and canonicalization; the frozen
  frequency lists; the permutation constructions for MN-μ6 / MN-neg / MN-free; `(b x_d + c y_d) mod p`;
  `D_f`, `a*_f` and the chirp exponent `κd² mod n`; the C-EQ-int assertion; all counts `N_LOW`;
  all ranks, sign tests and exact permutation `p`-values (integer numerator / integer denominator);
  every "orbits" denominator.
- **Float carve-out (analytic size only, no key in the path):** the length-`n` FFT producing
  `|U(a,f)|`, the reported `z` values and Stouffer `Z`, and the Spearman/variance arithmetic of S1–S2.
  Justification: these are magnitudes of an analytic exponential sum computed **from exact integer
  inputs** (`(b x_d + c y_d) mod p` is an exact `int` before the single division by `p` inside the
  phase); no key, index or coordinate low-bit passes through a float.
- **No verdict is decided by float precision.** Every verdict-bearing comparison is an integer rank
  of the character's value among `R` null draws through a **bit-identical code path**. The one float
  threshold (`ρ < 0.01`) is applied identically to both arms and decides nothing by itself; C-PREC
  re-evaluates every borderline row at 50 digits and prints the count.
- `check_no_float.sh` must pass on the curve/orbit/permutation/counting modules before the run.

## 9. PRE-COMMITTED OUTCOMES — filled in BEFORE the run

Every row is a positive characterization. **No row licenses a closure, a verdict about
ECDLP/extraction/security, or the words safe / generic / nothing here / closed / no structure /
benign / at the floor.** Abstention is legitimate and is **not** a closure.

| # | Outcome | Conclusion reported |
|---|---|---|
| **O1** | Pooled `Z(char vs MN-μ6) > +4`, sign `≥8/10`, S3 agrees | **H-BUDGET falsified.** The row-axis low tail survives a null carrying unit modulus + exact multiset + the budget + `μ₆`. Report the surviving layer `char − MN-μ6` with its size, its MDE and the §6 scope, and the full four-layer decomposition. Named next object: the `d`-alignment structure that MN-μ6 does not reach. |
| **O2** | Pooled `\|Z\| < 2` **and** `MN-free − REF-RAY` carries essentially all of `char − REF-RAY` | **"It was the confound all along," in its exact form.** The row-axis near-zero excess over Rayleigh is the shadow of the per-frequency budget / unit-modulus constraint, shared by every unit-modulus target; the curve's `d`-labelling adds nothing detectable at MDE `0.39%` pooled. Reported as a **bounded magnitude with its power number**, not as an absence of structure. Explicitly: this bounds the ROW axis only and does **not** touch the prior run's `(b,c)`-axis result. |
| **O3** | Pooled `\|Z(char vs MN-μ6)\| < 2` but `Z(char vs MN-free) > +4` — i.e. the `(MN-μ6 − MN-neg)` and/or `(MN-neg − MN-free)` layers carry the effect | **Positive localization: the effect is carried by the `μ₆ = ⟨λ,−1⟩` orbit structure of the `d`-labelling — the CM/GLV layer — not by the group law.** Report which of the two sub-layers dominates, both with sizes and MDEs. Since MN-free is the prior run's MC2 transposed, this **names the mechanism of the prior 8%** and is the strongest available positive result of this run. Requires its own follow-up prereg before any mechanism is asserted. |
| **O4** | Pooled `Z < −4` (character has **fewer** near-zero rows than MN-μ6) | The row profile is **flatter** than the matched null — the opposite sign to the `(b,c)` axis. Report both signs side by side with S4 (the top), and name the sign flip between axes as the object of the next prereg. Do not reconcile the two axes post hoc in this document. |
| **O5** | Primary within MDE, but **S1** `\|Θ_char − Θ_null\|` exceeds its pooled MDE `0.014` with a consistent sign | The **magnitude** of the low tail is matched but its **coupling to the top at the same frequency** is not: over-coupling ⇒ the low tail is slaved to the budget split; under-coupling ⇒ it is row-local. Report the sign, the size, the MDE, and that S1 is a secondary: this is a named next-probe object, **not** a verdict of this run. |
| **O6** | Any P-DET criterion fails, or chirp `≠ 0`, or tone `≠ n−2` | "**Planted control did not fire; null uninformative.**" No verdict, regardless of how clean the primary looks. Report the failing criterion and its numbers. |
| **O7** | C-EQ-int fails, or C-NULLSYM shows MN-free passing | **Halt.** This is a bug in the `(λ,β)` pairing or in the permutation construction, not a finding — precisely the failure recorded at `p=433/577` in the prior run's deviations. |
| **O8** | Special strata (S6) differ from the generic stratum | Reported **separately, with F7 restated**: `c=0` and `b=0` have within-profile symmetry by construction, `b=0` additionally has real `U`, so their profile laws differ *a priori*. A difference there is a forced structural fact and may **not** be pooled with, or read as corroboration of, the generic result. |
| **O9** | Primary and S3 (order statistic) disagree in sign at pooled `\|Z\| > 2` each | Arm reported **UNRESOLVED**. Print both, print the C-PREC borderline count, and issue no verdict. |
| **O10** | S5 (low-set `μ₆`-orbit occupancy) fires at pooled `\|z\| > 4` | Recorded as the **object of the next prereg** under an explicit `EXPLORATORY` heading. It may not be reported as a finding of this run: it was not the primary and its null was not built for it. |
| **O11** | MN-μ6-shared null `sd` exceeds MN-μ6's by `>3×` | The primary `z_p` is reported against **both** nulls and the more conservative is the verdict (pre-committed in §3.2). Print the variance decomposition. |
| **O12** | Anything the table above does not cover | Report the raw four-layer decomposition, the MDEs, the scope, and **no verdict**. Name the uncovered case explicitly as a gap in this spec. |

**Effect-in-an-unprojected-subspace clause (mandatory).** `N_LOW` is a symmetric functional of the
row profile at one frequency in one fixed basis. If every layer comes back inside its MDE, the run
must **not** report "no structure". It must report: (i) the bounded magnitude with its power number
and the §6 scope; (ii) the full four-layer decomposition, which is additive by construction and
therefore always localizes; (iii) the exact realizable scale `[0, n−2]` of F8, so the bound is
stated as a position on a known interval; and (iv) an explicit list of what was **not** projected
onto — **which** rows are low (S5: the symmetry type of the low set), the **phases** of `U` (only
`|U|` is used), the autocorrelation `A_{b,c}(Δ) = Σ_d s(d)\overline{s(d−Δ)}` whose Fourier transform
the profile is, cross-frequency structure (each `f` is treated independently), non-`μ₆` strata,
thresholds other than `ρ < 0.01`, and `p > 19231`.

**Grade the result may earn.** At most **`[EMPIRICAL — 10 model primes 163…19231, generic μ₆×conj
frequency stratum, statistic `N_LOW` at `ρ<0.01`, nulls MN-μ6 / MN-neg / MN-free]`**. The identities
of §1, F1–F8 (row conservation, orbit size 12, generator invariance, chirp `N_LOW=0`, tone
`N_LOW=n−2`, the F5 Fubini redundancy) are `[PROVED]` algebra and are graded independently of the
run. **No measured layer may carry a `[PROVED]` tag, and no outcome may be stated without the §6
scope banner attached.** Nothing in any outcome transfers to `p = 2²⁵⁶−2³²−977`.

---

**Deviation discipline.** Any change to the statistic, the frozen lists (hashes in §0), the prime
list, `m_p`, `R`, the thresholds `ρ<0.01` / `r>1.5`, the null constructions, or the outcome table
must be written to `PREREG_row_budget_lowtail_v1_DEVIATIONS.md` **before the arms are read**, with
the pre-committed value, the actual value, and the handling. A deviation is not necessarily wrong —
it is necessarily disclosed.
