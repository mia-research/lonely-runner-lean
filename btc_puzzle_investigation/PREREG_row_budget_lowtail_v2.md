# PREREG v2 — the row budget and the low tail: amended plant, corrected forced-structure section, strata arm

**File:** `PREREG_row_budget_lowtail_v2.md`  **Date:** 2026-07-24  **Status: PRE-RUN (frozen).**
Amends `PREREG_row_budget_lowtail_v1.md` after its planted control failed
(`RESULT_row_budget_lowtail_v1.md`, outcome **O6**; `PREREG_row_budget_lowtail_v1_DEVIATIONS.md`,
five deviations + one found while writing this spec, §11).

**Frozen input artifacts — unchanged from v1, re-hashed, no curve and no frequency added or dropped:**

| file | SHA-256 | lines |
|---|---|---|
| `PREREG_row_budget_lowtail_v1_FREQS.txt` (generic stratum) | `9695989bcd52777dc3e3012477dd460f5f29ffcd0da099d09bf7294d983005f3` | 87345 (= 87335 freqs + 10 headers) |
| `PREREG_row_budget_lowtail_v1_FREQS_SPECIAL.txt` (`c=0`, `b=0` strata) | `dfa9f7a40d27a03f906e9fb03d6466775b980b28c62a04e6675792124811ee9e` | 6145 |

The run **must** read `(p,b,c)` from these two files. Generating frequencies at run time is a deviation.
v2 consumes the SPECIAL file, which v1 never opened (v1 D4).

**Scope banner (inherited by every number this run produces, never omitted from any of them).**
Enumerable model curves `E : y² = x³ + 7` over `F_p`, `p` in the frozen 10-prime list of §6, group
order `n = #E(F_p)` prime, `d = 1..n−1` fully enumerated, `μ₆×conj` frequency strata as frozen.
`p = 2²⁵⁶−2³²−977` is **not** enumerable and **nothing here transfers to it**. No ECDLP, extraction
or security claim is made or may be derived from any outcome. Abstention is legitimate and is **not**
a closure; frontier §XI.17 is open and no outcome below closes it.

---

## 0. SEEN-DATA DECLARATION — read before anything else

Pre-registration is an ordering claim. v1 ran, printed numbers, and abstained on a control failure.
**Those numbers are seen.** Re-running them behind a repaired gate does not make them unseen. This
section states exactly which quantities are seen, by whom, and what grade each arm may therefore earn.
Every downstream section is bound by it.

| quantity | status entering v2 | consequence |
|---|---|---|
| Generic-stratum `N̄_char`, `N̄_MN-μ6/neg/free`, `REF-RAY`, per-prime `z`, excess, pooled `Z=+76.73`, sign 10/10 | **SEEN** (all 10 primes, `RESULT_ …_v1.md` §4) | Arm A is **CONFIRMATORY-REPAIR ON SEEN DATA**. It may not be reported as a pre-registered discovery. Max grade §9. |
| Ladder layer means (`+7.3090`, `−0.0356`, `−0.0331`, `−0.1573` % of REF-RAY) | **SEEN** as means over primes | The *per-prime* values and their `1/n` scaling are **UNSEEN** — see F11, Arm A3. |
| `S3` sign agreement (10/10), `S5` (`\|z\| ≤ 2.37`) | **SEEN** | descriptive only |
| `S1` Spearman coupling, all 10 primes | **SEEN** (run after v1 abstained; `Θ_char ≈ Θ_null ≈ +0.085`, pooled `Z = −0.275`) | **Not promoted.** Registered as a measured bound with power, §3.5. |
| `S6` strata, `p ∈ {577, 2089, 4159, 9319, 19231}` | **SEEN** | descriptive; drives the *prediction*, never the test |
| `S6` strata, `p ∈ {163, 211, 349, 433, 991}` | **UNSEEN BY THIS SPEC** | Arm B out-of-sample test — **admissible only under the attestation of §3.4** |
| `S2` dispersion | computed by v1, **not reported**; unknown to this spec | promoted to a gate (`C-DISP`); if the operator has read it, declare SEEN in the run log |
| Fragility `L(ε=0.05)` (the `−50.5% … −77.8%` losses) | **SEEN**, all 10 primes | S7 registers `ε ∈ {0.10, 0.15, 0.20, 0.30}` only |
| Everything produced by the v2 controls (P-DET-A/-C0/-B0, P-SIZE, C-SELFZ, C-DISP), the constant/QR extremes, the paired frequency-population SE, the per-prime layer scaling | **UNSEEN** | genuinely pre-registered |

**No curve may be added.** The frozen 10-prime list is binding (§6), so Arm A has **no out-of-sample
set available** and cannot acquire one. This is stated as a limitation, not worked around.

**Attestation requirement.** Arm B (§3.4) is confirmatory **only if** the run log carries a written
statement that the `c=0` / `b=0` numbers for `p ∈ {163, 211, 349, 433, 991}` were not read before this
spec was frozen. Absent that statement, Arm B is descriptive and its outcome cells O-B1/O-B2 are void
(O-B4 governs).

---

## 1. OBJECT

Carried from v1 §1 **verbatim and unchanged**: the curve data `(x_d, y_d) = [d]G`, `d = 1..n−1`;

```
s_{b,c}(d) = e_p(b·x_d + c·y_d)                      unit modulus, d = 1..n−1
U(a,b,c)   = Σ_{d=1}^{n−1} s_{b,c}(d) · e_n(a·d)     a ∈ Z/n
ρ(a; b,c)  = |U(a,b,c)|² / (n−1)
```

The object is the **SHAPE of the row profile `ρ(· ; b,c)` at a FIXED frequency `(b,c)`** for the real
`d`-labelling versus for matched relabellings. Threshold frozen at `ρ < 0.01`, inherited from
`RESULT_subrayleigh_deficit_locus_v1.md` §3 (`r̃ < 0.10`); not chosen here. Tautology check, symmetry
table (`ρ(a;βb,c) = ρ(λ⁻¹a;b,c)`, `ρ(a;b,−c) = ρ(−a;b,c)`, `ρ(a;b,c) = ρ(a;−b,c)`), order-12
`μ₆×conj` orbit structure, and generator-invariance — all carried from v1 §1 unchanged. **"A different
generator" may never be reported as a control.**

### 1.4 What the row conservation is, and therefore what frontier #17 can possibly show `[PROVED]`

Established in `row_budget_core_v1.py` and carried in as a **correction to the frontier's premise**:

> For fixed `(b,c)`, `U(·,b,c)` is one length-`n` DFT of `s_{b,c}` (zero-padded at `d=0`). Hence
> `Σ_a |U(a,b,c)|² = n·Σ_d |s(d)|² = n(n−1)` is **Parseval for a unit-modulus sequence in `d`**. It
> holds for **any** target of modulus 1 — verified against a random unit-modulus target at exactly `0`.
> **It is not a curve property.**

`POSITIVE_FINDINGS_ADDENDUM_1_v1.md` §A1.7-3 records it as "the one conservation the nulls do not
carry". That is accurate **only** about the specific prior nulls MC1/MC2, which permute character
values at fixed `a₀` and therefore have no `a`-family at all — the constraint is *vacuous* for them,
not violated. Four consequences, all forced, all pre-declared:

- **(i)** Every arm of this spec's ladder is a `d`-relabelling of a unit-modulus sequence, so every arm
  carries the conservation exactly, for free. **The conservation contributes exactly `0` to
  `char − MN-μ6`, `char − MN-neg`, `char − MN-free`.** No char-vs-matched-null difference can ever be
  attributed to it.
- **(ii)** The only place it can act is `char − REF-RAY`, because REF-RAY (`Exp(1)`) is not a realizable
  law. Its contribution is the finite-`n` gap between the true periodogram law of a unit-modulus
  sequence and `Exp(1)` — a forced quantity (F11), **not a structural layer**. v1's fourth ladder entry
  is relabelled accordingly.
- **(iii)** v1's hypothesis **H-BUDGET** ("the excess is a shadow of the row budget") is therefore
  **settled by algebra, not by measurement: NO.** A constraint carried identically by both arms cannot
  produce a contrast between them. This is `[PROVED]` and is not a run outcome.
- **(iv)** What remains — the entire live content of frontier #17 — is one question:
  **does the character's own `d`-labelling give a different low-tail count from a `μ₆`-commuting
  relabelling of the same value multiset?** and, if so, which sub-layer (`λ` / `[−1]` / beyond) carries
  it. #17 cannot decide anything about the value multiset (identical in every arm by construction), the
  conservation (universal), the phases of `U` (only `|U|` enters), or the frequency axis (that is the
  prior run's axis). Everything #17 can ever show lives in `char − MN-μ6` and its decomposition.

## 2. WHAT IS FORCED — carries zero information, stated before the run

**F1–F6 and F8 are carried from v1 §2 verbatim and unchanged** (row conservation is universal and the
compensation question is void; `O(1/n)` per-row compensation is unmeasurable; `ρ(a;0,0)` exact;
`U(0,f)` identical in every arm and excluded; **F5** — the doubly-pooled additive functional equals
`n ×` the prior run's `(b,c)`-marginal, so **the character side of `N_LOW` is not new information and
all new content is the null column**; F6 — every tally denominated in `μ₆×conj` orbits).

### F7 — CORRECTED. v1's F7 contains an error; v2 must not inherit it

v1 F7 states: "`c=0` ⇒ `ρ(a;b,0) = ρ(−a;b,0)`. `b=0` ⇒ `U(a,0,c) ∈ R` for every `a`, **and
`ρ(a;0,c) = ρ(−a;0,c)`**." The bolded clause is **FALSE**. The two strata have *different* symmetries,
not overlapping ones:

| stratum | source identity | consequence | verified |
|---|---|---|---|
| `c=0` (x-only) | `x_{−d} = x_d` ⇒ `s` **even** in `d` | `U(−a) = U(a)` ⇒ **profile symmetric**; `U` is **not** real | `p=577`: symmetric TRUE, `max\|Im U\|/max\|U\| = 0.86` |
| `b=0` (y-only) | `y_{−d} = −y_d` ⇒ `s(−d) = conj s(d)` | **`U(a) ∈ R` for every `a`**; profile **not** symmetric | `p=577`: symmetric FALSE, `max\|Im U\|/max\|U\| = 6.6e−16` |

Realness belongs to `b=0` only; profile symmetry to `c=0` only. No v1 number relied on the false
clause. **F7's conclusion stands and is carried:** a null that does not commute with `d ↦ −d` destroys
a symmetry the real system has by definition, so **on the special strata a free label shuffle is an
invalid null** (this is the `6–7σ soft shadow` failure mode); MN-free is inadmissible there; MN-μ6 and
MN-neg both preserve the correct symmetry in each stratum (verified, `≤ 6e−16`) and are the admissible
class. **The strata are never pooled with each other or with the generic stratum.**

### F9 — parity of `N_LOW` on `c=0` `[PROVED]`

`ρ(a) = ρ(−a)` pairs the `n−1` rows into `(n−1)/2` equal pairs ⇒ **`N_LOW` is even, exactly, at every
`f` in the `c=0` stratum, in every arm.** Printed as an integer check. Consequence for power:
`Var(N_LOW) = 2(n−1)q(1−q)`, i.e. **variance doubled** relative to independent rows; every `c=0` MDE
carries a `√2`.

### F10 — the `b=0` stratum has a DIFFERENT forced low-tail law, `8.0×` the generic rate `[PROVED]`

`U(a,0,c) ∈ R` ⇒ under the Gaussian limit `ρ` is `χ²₁` scaled to mean 1, not `Exp(1)`. Hence

```
q_generic = 1 − e^{−0.01}          = 0.00995017        REF = (n−1)·q_generic
q_{b=0}   = erf(√(0.01/2))         = 0.07965567        REF = (n−1)·q_{b=0}       ratio 8.0055
```

| `p` | 577 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|
| `c=0` forced REF `(n−1)q_gen` | 6.090 | 21.313 | 42.209 | 90.805 | **194.028** |
| `b=0` forced REF `(n−1)q_{b=0}` | 48.749 | 170.622 | 337.899 | 726.938 | **1553.286** |

**A successor that used the generic `REF-RAY` on the `b=0` stratum would report a spurious `+700%`
"excess".** The `b=0` REF is `(n−1)·erf(√(θ/2))`, full stop. Corollary: on `b=0` the frozen threshold
`ρ<0.01` sits at the **7.97% quantile** of the forced law, not the 0.995% quantile — **`N_LOW` on
`b=0` is not measuring "the low tail" in the same sense as on the generic stratum**, and the two
numbers may never be compared as if they were the same statistic.

### F11 — `MN-free − REF-RAY` is a finite-`n` reference-model error, not a layer `[PROVED to leading order]`

For a unit-modulus sequence of `N = n−1` terms, the Pearson random-walk correction gives density
`e^{−ρ}[1 − (ρ²−4ρ+2)/(4N)] + O(N^{−2})` (normalization and mean both exactly preserved), hence

```
P(ρ<θ) = (1 − e^{−θ}) − e^{−θ}·θ(2−θ)/(4N),   relative deviation = −c/(n−1),  c = 0.4950 at θ=0.01
```

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| predicted `MN-free − REF-RAY` (%) | −0.359 | −0.250 | −0.159 | −0.125 | −0.081 | −0.049 | −0.023 | −0.012 | −0.005 | −0.003 |

Mean over the ten primes `= −0.1065%`. **The mean is SEEN** (v1 measured `−0.1573%`) and therefore is
**not** a test. The **per-prime `1/(n−1)` scaling is UNSEEN and is registered** (Arm A3): fit
`log|layer|` on `log(n−1)` across the 10 primes; the pre-committed slope is `−1`.

### F12 — the plant has NO predicted response below `ε ≈ 1/√(n−1)` `[PROVED]`

For a tone plant at `a* ≠ 0` the spike carries budget share `ε²`, but the spike **row itself is removed
from the low count**. The two effects cancel at leading order for `ε² (n−1) ≪ 1`:
`Δ_pred(ε) = A(ε)·B(ε) − 1` with `A = (1−e^{−θ/(1−ε²)})/(1−e^{−θ}) ≈ 1+ε²` and
`B = ((n−2)+e^{−ε²(n−1)/(1−ε²)})/(n−1) ≈ 1−ε²`, giving `Δ_pred ≈ −ε⁴ ≈ 0`.

| `p` | `1/√(n−1)` | `Δ_pred` @0.05 | @0.10 | @0.15 | @0.20 | @0.30 | @0.50 | @0.80 |
|---|---|---|---|---|---|---|---|---|
| 163 | 0.0851 | **+0.037%** | +0.455 | +1.580 | +3.393 | +9.040 | +32.15 | +173.3 |
| 991 | 0.0315 | +0.158% | +0.905 | +2.189 | +4.042 | +9.727 | +32.98 | +175.1 |
| 19231 | 0.0072 | +0.244% | +1.000 | +2.285 | +4.140 | +9.830 | +33.11 | +175.3 |
| (v1's model `ε²/(1−ε²)`) | — | +0.251% | +1.010 | +2.302 | +4.167 | +9.890 | +33.33 | +177.8 |

**So v1's derived table was wrong at small `n` by up to `7×` at `ε=0.05`**, in the direction of a
predicted *decrease*, independently of any carrier excess. Part of v1's criterion-3 dip was forced.
v2 removes the term entirely by planting `a* = 0` (§4.1).

### F13 — any value-replacement plant convolves the profile with a kernel `200·ε(1−ε)` window-widths wide `[PROVED]`

Replacing a fraction `ε` of the values by anything gives
`U^{(ε)}(a) = (1−ε)U(a) + η(a)`, with `η` a mean-zero fluctuation of total variance `2ε(1−ε)(n−1)`
(fixed exactly by the budget: `(1−ε)² + 2ε(1−ε) = 1−ε²`). In `ρ` units the smearing kernel has width
`2ε(1−ε)`, i.e. `2ε(1−ε)/θ = 200·ε(1−ε)` **threshold-window widths** — `9.5` at `ε = 0.05`.

**Consequence, pre-declared: any structure confined to `ρ < θ` is destroyed by the plant at a rate
`O(1/(1+200ε))` — strongly super-linear in `ε` and forced by the construction.** v1's measured
`≈60%` loss at `ε=0.05` is of exactly this order. It is therefore **not, by itself, a substantive
property**; what is substantive is whether the *measured* loss curve matches the smearing model
computed from the character's own `ρ`-histogram. That is registered as **S7** (§3.6), not left as an
incidental observation.

**Corollary that decides the v2 plant design: a plant may only be applied to a carrier with no
sub-threshold structure of its own.** Planting into the character violates this by construction, which
is why v1's criterion 3 was not a well-posed gate.

### F14 — exact realizable extremes per stratum, all three verified `[PROVED]`

| target | `N_LOW` | admissible in | verified at all 10 `n` |
|---|---|---|---|
| constant `t(d) ≡ 1` | **`n−1` exactly** (`U(a) = −1`, `ρ = 1/(n−1) < 0.01` for `n ≥ 102`; the spike lands on the **excluded** `a=0` row) | generic, `c=0` (even), `b=0` (real, even) | yes |
| chirp `t(d) = e_n(d²)` | **`0` exactly** (`\|U\| ∈ [√n−1, √n+1]`) | generic, `c=0` (**even** in `d`) | yes, even=TRUE |
| QR `t(d) = χ(d)` (`n≡1 mod 4`), `= i·χ(d)` (`n≡3 mod 4`) | **`0` exactly** (`\|U(a)\| = √n` for all `a≠0`, Gauss sum) | `b=0` (`U` **real**, `t(−d)=conj t(d)`) | yes, `max\|Im U\|/max\|U\| ≤ 1.5e−15`, `herm_err = 0` |
| tone `t(d) = e_n(−a*d)`, `a*≠0` | **`n−2` exactly** | generic, `b=0` (`t(−d)=conj t(d)`) | v1, re-checked |

The chirp is **not** `b=0`-admissible (`e_n(d²)` is even, not Hermitian); the QR sequence is **not**
`c=0`-admissible when `n≡3 mod 4` (`χ` is odd there). Each stratum therefore gets its own floor target,
named above. `N_LOW ∈ [0, n−1]` with **both endpoints attained by explicit realizable sequences in
every stratum**, and the unconstrained-Rayleigh reference sits at `≈1%` of that range on the generic
and `c=0` strata and at `≈8%` on `b=0`. **No simulation is needed to bound what any realizable target
could do.**

## 3. STATISTICS — two arms, each with one verdict-bearing statistic

### 3.1 Arm A primary (CONFIRMATORY-REPAIR ON SEEN DATA, §0)

Unchanged from v1 in definition:

```
N_LOW(f) = #{ a ∈ Z/n, a ≠ 0 : |U(a,f)|² < 0.01·(n−1) }          integer count
N̄(p)     = (1/m_p) Σ_{f ∈ F_gen(p)} N_LOW(f)                     f from the frozen list
```

**CHANGED — the error model.** v1 read only `z_p` against the `R=64` MN-μ6 replicate distribution.
v2 registers the **paired per-frequency difference** as the primary error model:

```
δ(f)  = N_LOW_char(f) − (1/R) Σ_r N_LOW_null^{(r)}(f)            same f, same code path
Δ̄(p)  = mean_f δ(f)                     SE(p) = sd_f(δ) / √m_p
```

`Δ̄/N̄_null` is the excess; `SE/N̄_null` is its **frequency-population** standard error — the correct
error bar for the scope statement "over the generic `μ₆×conj` stratum of this curve", which the
replicate-only `z` does not provide at the six primes where the frozen list is a sample. Under row
independence `SE/N̄ = √((1−q)/T_p)·√(1+1/R)`, reproducing v1 §5 to 3 digits; the **measured** value
governs (see `C-DISP`). The replicate rank statistic is retained unchanged as the randomization
`p`-value: `p_p = (1 + #{r : N̄^{(r)} ≥ N̄_char})/(R+1)`, `R = 64`, floor `1/65`.

Pooled: **Stouffer `Z = Σ_p z_p/√10`** and a 10-prime **sign test**, pooled, never a max over primes or
frequencies. Null ladder MN-μ6 (primary) / MN-neg / MN-free / REF-RAY, constructions carried from
v1 §3.2 **verbatim** (`μ₆`-commuting orbit permutation, `λ` derived from the curve data with the
`C-EQ-int` guard, one `π_f` per frequency, MN-μ6-shared variant at the same `R`).

### 3.2 Arm A2 — dispersion, promoted from secondary `S2` to a GATE (`C-DISP`)

```
D_p = Var_f(N_LOW) / mean_f(N_LOW)          computed for char and for the null replicates
```

Registered because the whole primary rests on the null's spread being right. **Gate:** if
`D_char/D_null > 1.5` at any prime, that prime's `SE` is inflated by `√(D_char/D_null)` and **both the
inflated and uninflated numbers are printed**, the inflated one governing. Pre-committed, not a
post-hoc choice. Also reports `D` against the row-independence value `≈ 1`.

### 3.3 Arm A3 — the layer-scaling check (UNSEEN)

Per-prime `MN-free − REF-RAY` regressed as `log|layer|` on `log(n−1)`. Pre-committed slope `−1`
(F11). **Pass:** slope in `[−1.35, −0.65]`. A slope outside that band means the fourth ladder entry is
not the finite-`n` reference error and must be renamed. The **pooled mean is seen and is excluded from
this check.**

### 3.4 Arm B — the special strata, out-of-sample (the only genuinely pre-registered verdict here)

**Hypothesis H-STRATA, fixed now from the five SEEN primes and tested on the five UNSEEN primes:**

> On the `c=0` (x-only) stratum the character's `N_LOW` is **below** its MN-μ6 null; on the `b=0`
> (y-only) stratum it is **above**. The two strata carry opposite signs.

Seen basis (`p ∈ {577, 2089, 4159, 9319, 19231}`, descriptive, never re-used as a test): `c=0` `z =`
`−1.08, −10.42, −20.37, −26.80, −24.34`; `b=0` `z = +5.44, +20.95, +28.03, +27.66, +24.96`; at
`p=19231`, `c=0` char `160.6` vs null `194.0` (**−17%**), `b=0` char `1676.5` vs null `1553.2`
(**+7.9%**), against a generic-stratum `+7.4%`.

**Test set: `p ∈ {163, 211, 349, 433, 991}`, admissible only under the §0 attestation.**
Statistic, one per stratum, fixed now: the **one-sided pooled Stouffer `Z₅ = Σ z_p/√5`**, sign
pre-registered (`c=0` negative, `b=0` positive), plus the 5-prime sign test. Nulls: **MN-μ6 primary,
MN-neg secondary, MN-free inadmissible (F7).** Forced references per F10. Strata never pooled with each
other or with the generic stratum; `N_LOW` parity checked per F9.

**Pass:** `c=0` `Z₅ ≤ −4` **and** `b=0` `Z₅ ≥ +4`, with the pre-registered signs, with all stratum
controls of §4.3–4.4 firing. **Fail:** either `Z₅` of the wrong sign, or `|Z₅| < 2` in either stratum.

### 3.5 `S1` coupling — NOT promoted; registered as a measured bound with power

v1 singled `S1` out as the only statistic F5 does not render uninformative on the character side. It
has since been run under v1's frozen definition at all 10 primes and is **null**: `Θ_char ≈ Θ_null ≈
+0.085` (the forced budget coupling, present in both arms exactly as v1 predicted), `z =` `−0.33,
−1.36, +1.34, −0.03, +1.54, +0.49, −1.30, −0.61, −0.84, +0.23`, 5 negative / 5 positive, all
`|z| < 1.6`, pooled `Z = −0.275`.

**Decision: do not promote.** Promoting a statistic whose value is already known is not a test; it is
the ordering failure this spec exists to prevent. Registering it as "primary" in v2 would let a seen
null be re-reported as a pre-registered null. It is instead carried as a **bounded magnitude with its
power number and scope**, computed now:

```
sd(Θ) = 1/√(m_p − 1) per prime (distribution-free);  pooled sd = 1/√(Σ m_p) = 1/√87335 = 0.00338
pooled MDE @4σ = 0.0135  =  15.9% of the forced coupling Θ ≈ +0.085
```

**Statement v2 is permitted to make about `S1`, and no stronger one:** over the frozen generic stratum
of these 10 curves, the char−null difference in the `N_LOW`/`B_HIGH` rank coupling is bounded by
`0.0135` at 4σ, i.e. below 16% of the coupling the budget forces into *both* arms.
**Unprojected clause (mandatory):** this bounds one pair of functionals in one basis. It does **not**
bound (a) the coupling of `N_LOW` to the single top row rather than to `B_HIGH`'s aggregate, (b) any
*conditional* coupling at fixed `B_HIGH` decile, (c) coupling across frequencies in a `μ₆` orbit, or
(d) coupling on either special stratum, where `S1` has never been computed. Any of these is a separate
prereg; none may be run against these data and reported as a finding of this run.

### 3.6 `S7` FRAGILITY — the `60%`-loss observation, promoted to a registered quantity with a forced baseline

Apply the **constant plant** (§4.1) at `ε` to the **character** and to a **matched MN-μ6 carrier**, and
read the fraction of the char−null excess destroyed:

```
L(ε) = 1 − [ N̄_char^{(ε)} − N̄_null^{(ε)} ] / [ N̄_char^{(0)} − N̄_null^{(0)} ]
```

**Forced prediction (F13), computed from the character's own measured `ρ`-histogram, not fitted:**
smear both histograms with the exact Rice/Marcum kernel
`P(ρ^{(ε)} < θ | ρ) = 1 − Q₁( √(2(1−ε)²ρ/σ²), √(2θ/σ²) )`, `σ² = 2ε(1−ε)`, and take the difference of
sub-threshold masses ⇒ `L_pred(ε)`.

**`ε = 0.05` is SEEN and is excluded from the test.** Registered grid: `ε ∈ {0.10, 0.15, 0.20, 0.30}`.
**Criterion:** `|L_meas(ε) − L_pred(ε)| ≤ max(3·SE, 0.15)` at every registered `ε`.
**Reading, pre-committed:** agreement ⇒ the fragility is **forced by smearing** and the excess is
generic sub-threshold mass with no extra phase coherence — a positive characterization, not a null.
Disagreement ⇒ the excess is **not** determined by the marginal `ρ` law alone (row correlations, or
structure outside the marginal); that is named as the object of the next prereg and may **not** be
reported as a finding of this run.

### 3.7 Carried secondaries — reported, never verdict-bearing on their own

`S3` order statistic (`⌈0.01(n−1)⌉`-th smallest `ρ`, pooled median; **must agree in sign with the
primary**, disagreement ⇒ UNRESOLVED); `S4` top (`mean_f max_a ρ`, `mean_f B_HIGH`; declared a max over
cells, upward-biased, low-power, labelled as such); `S5` low-set `μ₆`-orbit occupancy (`χ²` vs
uniform-over-orbits — the "effect in an unprojected subspace" probe; **if it fires at `|z|>4` it is the
object of the NEXT prereg and may not be reported as a finding of this run**). Definitions carried from
v1 §3.3 unchanged.

**Pre-declared diagnostic, non-verdict:** the **threshold ladder** `θ ∈ {0.0025, 0.005, 0.01, 0.02,
0.04}` — the paired sub-threshold mass difference at each `θ`, with its derived plant response
`(1−e^{−θ/(1−ε²)})/(1−e^{−θ}) − 1` at each `θ`. Registered now so that, if a gate fails again, the
diagnostic exists without a post-hoc choice of statistic. **`θ = 0.01` alone is verdict-bearing.**

## 4. CONTROLS

### 4.1 P-DET-A — the AMENDED plant (generic stratum)

**Four changes from v1, each named with its justification:**

**(C-a) Carrier: MN-μ6, not the character.** For each `f`, draw a fresh `π_f` from the MN-μ6 group on a
**stream disjoint from the `R` verdict replicates**, and plant into `s_f ∘ π_f`.

*What this certifies, stated plainly.* A positive control's job is to establish the **power of the
decision rule** — a joint property of (i) the null's spread and (ii) the statistic's response to a
deviation of a given size. Both are properties of the null and the statistic, not of the real system;
injecting a known effect into a null draw and requiring detection is the canonical construction, and it
is what the template ("inject a known effect of known size; the test must fire") asks for.
*What it does not certify.* It says nothing about the real system's own behaviour under deformation —
that is a measurement, not a control, and conflating the two is exactly what broke v1's criterion 3.
That measurement is preserved and registered separately as **S7** (§3.6).
*The residual objection, and why the carrier change does not answer it.* A tone plant certifies
sensitivity to a **tone-shaped** deviation; this is true on either carrier, so it is not fixed by
changing carriers. It is answered instead by the structure of the statistic: `N_LOW` is a **count of
rows below a fixed threshold**, so its response is a function of the sub-threshold elevation **alone**
— two deviations producing the same elevation are indistinguishable to `N_LOW` by construction.
A plant calibrating the elevation is therefore adequate **for `N_LOW`, and only for `N_LOW`**. It is
**not** adequate for `S1` (which reads the joint low/high structure) — hence `S1` is not verdict-bearing
here (§3.5) — and the one way this argument could fail is if a perturbation changed `Var_f(N_LOW)`
without changing its mean; that is precisely what `C-DISP` (§3.2) measures.

**(C-b) Plant target: the constant `t(d) ≡ 1` (`a* = 0`), not a tone at `a* ≠ 0`.** The plant's spike
then lands on the `a=0` row, which `N_LOW` **excludes by definition (F4)**, so the F12 cancellation
disappears and the response model becomes exact, `n`-free and provably monotone:

```
Δ_pred(ε) = (1 − e^{−θ/(1−ε²)}) / (1 − e^{−θ}) − 1          Exp(1) carrier  (generic, c=0)
Δ_pred(ε) = erf(√(θ/(2(1−ε²)))) / erf(√(θ/2)) − 1           χ²₁ carrier     (b=0, F10)
```

Both are strictly increasing on `[0,1)` by inspection; `ε = 1` gives `N_LOW = n−1` **exactly** (F14).
**Validity condition, stated as required:** the model holds **iff the carrier's own `ρ`-law is the
forced law of its stratum with no sub-threshold excess** — true for MN-μ6 by construction, false for
the character (F13 corollary). The `≤ 0.2%` residual of the MN-μ6 carrier from the forced law is a
constant offset that **cancels in the paired difference** (C-d).

| `ε` | 0.05 | 0.10 | 0.15 | 0.20 | 0.30 | 0.50 | 0.80 | 1.00 |
|---|---|---|---|---|---|---|---|---|
| `Δ_pred`, `Exp(1)` carrier | +0.249% | +1.005% | +2.290% | +4.145% | +9.836% | +33.11% | +175.3% | `N_LOW = n−1` |
| `Δ_pred`, `χ²₁` carrier (`b=0`) | +0.125% | +0.502% | +1.140% | +2.055% | +4.811% | +15.41% | +66.18% | `N_LOW = n−1` |

**(C-c) Nested subsets.** `D_f(ε₁) ⊂ D_f(ε₂)` for `ε₁ < ε₂`, one nested chain per `f`. v1's script drew
`D` independently at each `ε`, adding noise to the very comparison the monotonicity gate reads.

**(C-d) Paired baseline.** The `ε = 0` cell is **the same carrier `s_f ∘ π_f`, unplanted**; every
`Δ_meas(ε)` is a paired ratio against it. Removes carrier idiosyncrasy and draw-to-draw variance.

**Swept levels:** `ε ∈ {0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.80, 1.00}` — **8 levels**, restoring
`0.15` (frozen in v1's spec, silently dropped by v1's script) and retaining `0.80` (silently added by
v1's script). See §11 D6.

**PASS CRITERIA — all five must print PASS before any Arm A verdict is issued:**

1. `ε = 1.00` returns `N_LOW = n−1` **exactly**, every `f`, every prime (integer assertion; **changed
   from v1's `n−2`** because the plant target changed from `a*≠0` to `a*=0`, F14).
2. The chirp `t(d) = e_n(d²)` returns `N_LOW = 0` **exactly**, every `f`, every prime (integer
   assertion) — the negative-direction control: the statistic must be able to reach the floor.
3. **`Δ_meas(ε)` agrees with `Δ_pred(ε)`:** `|Δ_meas(ε) − Δ_pred(ε)| ≤ max(3·SE_meas(ε),
   0.5·|Δ_pred(ε)|)` at every `ε` in the prime's **admissible sub-grid**, AND `Δ_meas` is strictly
   increasing across that sub-grid. `SE_meas` is the paired bootstrap SE over frequencies.
   **Admissible sub-grid = the swept levels with `Δ_pred(ε) > 3 × relsd(p)`, fixed now:**

   | `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
   |---|---|---|---|---|---|---|---|---|---|---|
   | generic `relsd` | 1.830% | 1.178% | 0.567% | 0.405% | 0.251% | 0.251% | 0.251% | 0.251% | 0.251% | 0.251% |
   | first admissible `ε` | 0.30 | 0.20 | 0.15 | 0.15 | 0.10 | 0.10 | 0.10 | 0.10 | 0.10 | 0.10 |

   Levels below the prime's first admissible `ε` are **printed but not gated** — they are below the
   instrument's own resolution and gating on them is testing noise (this is what v1's bare
   monotonicity criterion did at `p=163`, where the forced prediction is `+0.037%` against a `1.83%`
   resolution).
4. `z(ε = 0.20)` vs MN-μ6 exceeds `+6` at every prime with `p ≥ 577` (carried from v1 unchanged;
   v1 PASSED this).
5. **P-SIZE (negative control, NEW):** the unplanted carrier (`ε = 0`) must **not** fire — `|z| ≤ 3` at
   every prime, and over 64 independent carriers the fraction with `|z| > 2` must be `≤ 0.10`. A test
   that fires on an unplanted null is broken regardless of how well the positive control fires.

Also reported (calibration, not a criterion): the smallest swept `ε` with `z > 4`, the detector's
**measured** MDE, against the computed MDE of §5.

**If any of 1–5 fails, Arm A reports "planted control did not fire; the null is uninformative" and
issues NO verdict, however clean its numbers look** — and §9 O-A6 governs, which is not a loop.

### 4.2 `C-SELFZ` — null self-calibration (NEW)

The entire verdict is a `z` against the MN-μ6 replicate spread. That spread is therefore checked
directly: split the `R = 64` replicates into two halves, compute `z` of one half's mean against the
other half's distribution, and repeat leave-one-out. **Pass:** `|z_split| ≤ 3` at every prime, and the
sd of the 64 leave-one-out `z`'s lies in `[0.7, 1.4]`. A fail means the replicate spread is
mis-estimated and every `z` in the run is mis-scaled; the arm halts.

### 4.3 P-DET-C0 / P-DET-B0 — per-stratum planted controls (NEW; v1 had none for the strata)

Same amended design, with the plant restricted to each stratum's **admissible class** (F7, F14):

| | `c=0` | `b=0` |
|---|---|---|
| required symmetry of the plant | even in `d` | `t(−d) = conj t(d)` |
| replacement set | `D_f = −D_f` (±-symmetric) | `D_f = −D_f` |
| ceiling target | constant `t≡1` ⇒ `N_LOW = n−1` exactly | constant `t≡1` ⇒ `N_LOW = n−1` exactly |
| floor target | chirp `e_n(d²)` ⇒ `N_LOW = 0` exactly | QR `χ(d)` (`n≡1(4)`) / `i·χ(d)` (`n≡3(4)`) ⇒ `N_LOW = 0` exactly |
| response model | `Exp(1)`: `Δ_pred` row 1 of §4.1 | `χ²₁`: `Δ_pred` row 2 of §4.1 |
| forced reference | `(n−1)(1−e^{−θ})` | `(n−1)·erf(√(θ/2))` |
| carried checks | `N_LOW` even (F9); profile symmetry preserved by MN-μ6/MN-neg | `max\|Im U\|/max\|U\| ≤ 1e−12`; profile **not** symmetric |

**Admissible sub-grids, fixed now** (first swept `ε` with `Δ_pred > 3·relsd`):

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `c=0` `relsd` | 23.29% | 17.08% | 10.57% | 8.42% | 5.87% | 3.49% | 1.65% | 0.83% | 0.71% | 0.71% |
| `c=0` first `ε` | 0.80 | 0.80 | 0.50 | 0.50 | 0.50 | 0.50 | 0.30 | 0.20 | 0.15 | 0.15 |
| `b=0` `relsd` | 3.24% | 2.38% | 1.47% | 1.17% | 0.82% | 0.49% | 0.23% | 0.17% | 0.17% | 0.17% |
| `b=0` first `ε` | 0.50 | 0.50 | 0.30 | 0.30 | 0.30 | 0.20 | 0.15 | 0.15 | 0.15 | 0.15 |

**Pass criteria per stratum: 1, 2, 3, 5 of §4.1** with the stratum's own ceiling/floor targets,
response model and sub-grid. Criterion 4 is replaced by: `z(ε = first admissible level ×2)` exceeds
`+4` at every prime where that level is swept. **If a stratum's control fails, that stratum reports
O-B4 and issues no verdict** — including the out-of-sample test of §3.4.

### 4.4 Forced readout checks — zero evidence, must all be printed

Carried from v1 §4.3 unchanged: **C-BUDGET** (`Σ_a|U|² = n(n−1)`, rel `≤1e−12`, char / every null
draw / every plant level); **C-A0** (`U_char(0,f) = U_null(0,f)` exactly, rel `≤1e−13`; **applies to the
null arms only** — the plant deliberately changes `U(0)`); **C-EQ-int** (`max_d((x_{λd} − βx_d) mod p)
== 0`, `β` derived from the data, exact integer, run before any null is drawn); **C-EQ-flt**;
**C-NULLSYM** (MN-free must **FAIL** the `−b` identity; if it passes, the construction is wrong and the
run halts); **C-GEN** (`p=349`, `G' = [2]G`, `N̄` identical, rel `≤1e−14`; forced, zero evidence);
**C-PREC** (borderline rows recomputed at 50 digits, count printed).

New: **C-SYM-C0** (`c=0` profile symmetric, rel `≤1e−12`, char and both admissible nulls);
**C-REAL-B0** (`b=0` `max|Im U|/max|U| ≤ 1e−12`, char and both admissible nulls);
**C-PARITY** (`N_LOW` even at every `c=0` frequency, integer assertion, every arm);
**C-STRATREF** (`b=0` null `N̄` within `1%` of `(n−1)erf(√(θ/2))`; `c=0` null `N̄` within `1%` of
`(n−1)(1−e^{−θ})` — F10 as a forced check, not a result).

**RNG discipline (NEW).** Every random object is drawn from a stream seeded by
`SHA-256("rowbudget-v2" | p | b | c | arm | replicate)`, so no result depends on execution order or on
the order of primes. The plant carriers use `arm = "pdet"`; the verdict replicates use `arm = "null"`;
the streams are disjoint. v1 consumed one shared generator in data-dependent order.

## 5. POWER — computed now, at the planned sample size

Cell budget unchanged: `m_p = min(N_orb(p), cap)` from the frozen lists, `R = 64`. `T_p = m_p(n−1)q`.
Relative `SE` of the paired excess `= √((1−q)/T_p)·√(1+1/R)`, `×√2` on `c=0` (F9).

**Generic stratum (Arm A):**

| `p` | `n` | `m_p` | `T_p` | rel `SE` | **MDE @4σ** |
|---|---|---|---|---|---|
| 163 | 139 | 2 187 | 3 003 | 1.830% | **7.32%** |
| 211 | 199 | 3 675 | 7 240 | 1.178% | **4.71%** |
| 349 | 313 | 10 092 | 31 330 | 0.567% | **2.27%** |
| 433 | 397 | 15 552 | 61 279 | 0.405% | **1.62%** |
| 577 | 613 | 26 143 | 159 198 | 0.251% | **1.01%** |
| 991 | 1009 | 15 873 | 159 203 | 0.251% | **1.01%** |
| 2089 | 2143 | 7 469 | 159 189 | 0.251% | **1.01%** |
| 4159 | 4243 | 3 771 | 159 169 | 0.251% | **1.01%** |
| 9319 | 9127 | 1 753 | 159 182 | 0.251% | **1.01%** |
| 19 231 | 19 501 | 820 | 159 103 | 0.251% | **1.01%** |

**Pooled: `ΣT_p = 1 057 895`, rel `SE = 0.0975%`, MDE @4σ = `0.390%`.** `p = 163` and `p = 211` are
individually underpowered against anything below `≈5%` and **must not be read individually**; they
enter only the pooled `Z` and the sign test. `R = 64` fixes the rank-`p` floor at `1/65 = 0.0154`;
increasing `R` does not increase primary power.

**Special strata (Arm B), forced laws per F10:**

| `p` | `c=0` `m` | `c=0` `T` | `c=0` rel `SE` | MDE@4σ | `E\|z\|` if `−17%` | `b=0` `m` | `b=0` `T` | `b=0` rel `SE` | MDE@4σ | `E\|z\|` if `+7.9%` |
|---|---|---|---|---|---|---|---|---|---|---|
| 163 | 27 | 37 | 23.29% | 93.2% | 0.73 | 81 | 890 | 3.240% | 12.96% | 2.44 |
| 211 | 35 | 69 | 17.08% | 68.3% | 1.00 | 105 | 1 656 | 2.376% | 9.50% | 3.33 |
| 349 | 58 | 180 | 10.57% | 42.3% | 1.61 | 174 | 4 324 | 1.470% | 5.88% | 5.37 |
| 433 | 72 | 284 | 8.42% | 33.7% | 2.02 | 216 | 6 813 | 1.171% | 4.69% | 6.74 |
| 577 | 96 | 585 | 5.87% | 23.5% | 2.90 | 288 | 14 040 | 0.816% | 3.26% | 9.68 |
| 991 | 165 | 1 655 | 3.49% | 13.9% | 4.88 | 495 | 39 745 | 0.485% | 1.94% | 16.29 |
| 2089 | 348 | 7 417 | 1.65% | 6.6% | 10.32 | 1 044 | 178 130 | 0.229% | 0.92% | 34.49 |
| 4159 | 693 | 29 251 | 0.83% | 3.3% | 20.50 | 942 | 318 301 | 0.171% | 0.69% | 46.10 |
| 9319 | 438 | 39 773 | 0.71% | 2.8% | 23.91 | 438 | 318 399 | 0.171% | 0.69% | 46.11 |
| 19 231 | 205 | 39 776 | 0.71% | 2.8% | 23.91 | 205 | 318 424 | 0.171% | 0.69% | 46.11 |

**Power of the Arm B out-of-sample test at the five unseen primes**, computed under the seen-basis
effect sizes (`c=0` `−17%`, `b=0` `+7.9%`):

```
c=0 : expected one-sided Stouffer Z₅ = −4.57 ; P(5/5 correct sign | H₁) = 0.597 ; P(≥4/5) = 0.938
b=0 : expected one-sided Stouffer Z₅ = +15.28 ; P(5/5 correct sign | H₁) = 0.992 ; P(≥4/5) = 1.000
                                                 P(5/5 | H₀) = 1/32 = 0.031 per stratum
```

**`c=0` at `p ∈ {163, 211}` has `E|z| ≤ 1.0`: those two primes cannot individually contribute and are
flagged, never dropped.** The `Z₅ ≤ −4` bar for `c=0` is met in expectation with margin `0.57`; the
arm is therefore reported with its power number attached in every statement.

**`S1` (bound, §3.5):** pooled `sd(Θ) = 0.00338`, MDE @4σ `= 0.0135` `= 15.9%` of the forced coupling.

**Cost model.** `(R+1)·m_p` length-`n` FFTs per prime per null level for the generic stratum, `×3` null
levels, `×8` P-DET levels at the same `R`; strata add `Σ(m_{c=0}+m_{b=0}) = 2137 + 4188` frequencies,
negligible. Batched `numpy.fft` over chunks of `≤1024` rows; peak memory `< 300 MB` at every prime.
Bluestein at prime `n`; largest transform `n = 19501 → 65536`. Arm cost `O(m·n log n)`.

## 6. SCOPE — carried from v1 §6 verbatim; nothing added, nothing dropped

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `n` | 139 | 199 | 313 | 397 | 613 | 1009 | 2143 | 4243 | 9127 | 19501 |
| trace `p+1−n` | 25 | 13 | 37 | 37 | −35 | −17 | −53 | 83 | −193 | 269 |
| `β` (order 3 in `F_p^*`) | 58 | 14 | 122 | 198 | 213 | 113 | 826 | 1604 | 3138 | 9365 |
| `m` generic | 2187 | 3675 | 10092 | 15552 | 26143 | 15873 | 7469 | 3771 | 1753 | 820 |
| `m` `c=0` | 27 | 35 | 58 | 72 | 96 | 165 | 348 | 693 | 438 | 205 |
| `m` `b=0` | 81 | 105 | 174 | 216 | 288 | 495 | 1044 | 942 | 438 | 205 |

`p = 211` is kept whole despite its prior `z = −0.63`; dropping it would be a silent post-hoc filter.
`p ≈ 40000` was searched and none qualified; **the run may not add a prime.** Generator `G` = the point
of smallest `x ∈ [1,p)` with `x³+7` a QR — forced-irrelevant (§1, `C-GEN`). `(0,0)` excluded (F3).

**Unforced-cell denominators — the only legitimate denominators in this run.** Frequency tallies:
`m_p` **orbits**, never `12 m_p` pairs. Row tallies within a profile: `n−1`, never `n`. Cross-prime
tallies: `K = 10` for Arm A, `K = 5` for the Arm B test set; a "`k/K` fires" statement must print each
prime's MDE from §5 beside it, and underpowered primes are flagged, never dropped. Rank `p`-values:
integer numerator over `R+1 = 65`.

## 7. FALSIFICATION — written before the run

**Arm A (H-ALIGN, replacing v1's H-BUDGET, which §1.4(iii) settles by algebra):**

> The generic-stratum low-tail excess over a `μ₆`-commuting relabelling is produced by the character's
> own `d`-labelling alignment with the coordinate map, beyond `μ₆`.

**H-ALIGN is falsified if** pooled `|Z(char vs MN-μ6)| < 2` **and** the paired excess `Δ̄/N̄_null` lies
within the pooled MDE `0.390%` **and** all five P-DET-A criteria, `C-SELFZ`, `C-DISP` and the seven
forced checks passed. In that case the excess would have to live in `MN-μ6 − MN-free` or in the
reference error, both of which are named layers with their own sizes.

**Arm B (H-STRATA):** falsified if either stratum's `Z₅` at the five unseen primes carries the **wrong
pre-registered sign**, or if `|Z₅| < 2` in either stratum, with its stratum control firing.

**The spec is void and no verdict may be issued if:** any P-DET criterion fails; the constant target
does not return `N_LOW = n−1` exactly; the chirp does not return `0` exactly; the QR target does not
return `0` exactly on `b=0`; `C-EQ-int` fails; `C-NULLSYM` shows MN-free *passing* the `−b` identity;
`C-SELFZ` fails; `C-PARITY` fails; `C-STRATREF` misses by `>1%`; or `C-BUDGET` drifts beyond `1e−12`.
**A control that cannot fire invalidates the null regardless of how clean the numbers look.**

## 8. EXACTNESS

- **Exact `int` (no float in the signal path):** curve arithmetic and point counting; the `μ₆` and
  `⟨λ,−1⟩` orbit constructions and canonicalization; the frozen frequency lists; the MN-μ6 / MN-neg /
  MN-free permutations; `(b x_d + c y_d) mod p`; the nested `D_f(ε)` chains and their `±`-symmetrization
  on the strata; the chirp exponent `d² mod n`; the Legendre symbols `χ(d)` (`pow(d,(n−1)//2,n)`,
  exact); the `C-EQ-int` assertion; all counts `N_LOW`; the `N_LOW`-even parity assertion; all ranks,
  sign tests and exact permutation `p`-values (integer numerator / integer denominator); every "orbits"
  denominator; every RNG seed (SHA-256 of an integer string).
- **Float carve-out (analytic size only, no key in the path):** the length-`n` FFT producing `|U|`; the
  reported `z`, Stouffer `Z`, bootstrap SEs; the Spearman/variance arithmetic; the Marcum-`Q` and
  `erf` evaluations of F10/S7. Justification: magnitudes of an analytic exponential sum computed from
  exact integer inputs — `(b x_d + c y_d) mod p` is an exact `int` before the single division by `p`
  inside the phase; no key, index or coordinate low bit passes through a float.
- **No verdict is decided by float precision.** Every verdict-bearing comparison is an integer rank of
  the character's value among `R` null draws through a bit-identical code path. The one float threshold
  (`ρ < 0.01`) is applied identically to every arm and decides nothing by itself; `C-PREC` re-evaluates
  every borderline row at 50 digits and prints the count.
- `check_no_float.sh` must pass on the curve / orbit / permutation / plant / counting modules before the
  run.

## 9. PRE-COMMITTED OUTCOMES — filled in BEFORE the run

Every row is a positive characterization. **No row licenses a closure, a verdict about
ECDLP/extraction/security, or the words safe / generic / nothing here / closed / no structure / benign /
at the floor.** Abstention is legitimate and is **not** a closure.

### Arm A (generic stratum) — bounded above by the §0 SEEN label in every cell

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-A1** | All controls fire; pooled `Z(char vs MN-μ6) > +4`, sign `≥8/10`, `S3` agrees, `C-DISP` and `C-SELFZ` pass | **H-ALIGN supported on seen data.** Report the surviving layer `char − MN-μ6` with its paired excess, its frequency-population SE, its MDE and the §6 scope, plus the full four-layer decomposition with the fourth entry **relabelled** per F11. Grade: `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED]` (§0). Named next object: the `d`-alignment structure MN-μ6 does not reach. **This does not close #17 and does not upgrade v1's abstention to a discovery.** |
| **O-A2** | All controls fire; pooled `\|Z\| < 2` and the paired excess is within the pooled MDE `0.390%` | **"It was the confound all along," in its exact form** — but note §1.4(iii): the budget was never a candidate, so the confound named here would be the `μ₆` relabelling class itself. Report as a **bounded magnitude with its power number** and the §6 scope, never as an absence of structure. Bounds the ROW axis only; does not touch the prior `(b,c)`-axis result. |
| **O-A3** | `\|Z(char vs MN-μ6)\| < 2` but `Z(char vs MN-free) > +4` | **Positive localization: the effect is carried by the `μ₆ = ⟨λ,−1⟩` orbit structure of the `d`-labelling — the CM/GLV layer — not by the group law.** Report which sub-layer dominates, with sizes and MDEs. Requires its own follow-up prereg before any mechanism is asserted. |
| **O-A4** | Pooled `Z < −4` | The row profile is **flatter** than the matched null — opposite in sign to the `(b,c)` axis. Report both signs side by side with `S4`; name the inter-axis sign flip as the next prereg's object. Do not reconcile the axes post hoc in this document. |
| **O-A5** | Primary and `S3` disagree in sign at pooled `\|Z\|>2` each | Arm **UNRESOLVED**. Print both, print the `C-PREC` borderline count, issue no verdict. |
| **O-A6** | **Any P-DET-A criterion fails again** (incl. criterion 3 a second time) | "**Planted control did not fire; null uninformative.**" No Arm A verdict. **AND — this is not a loop:** a second failure with a *different carrier*, a *different plant target*, a *derived* (not fitted) response model and an *admissible sub-grid* locates the defect in the **statistic's response model**, not in the carrier. Report the measured `Δ(ε)` curve against `Δ_pred(ε)` as **the finding**: the periodogram of these relabelled sequences does not obey the Gaussian-limit law its power calculation assumes. Print the §3.7 threshold ladder as the diagnostic. Name the successor instrument: the paired sub-threshold **empirical CDF** compared by a pooled Anderson–Darling against the matched null — a statistic whose response does not require a Gaussian limit. |
| **O-A7** | `C-EQ-int`, `C-NULLSYM`, `C-SELFZ`, `C-PARITY` or `C-STRATREF` fails | **Halt.** A bug in the `(λ,β)` pairing, the permutation construction, the replicate spread, or the stratum reference — not a finding. |
| **O-A8** | `C-DISP` shows `D_char/D_null > 1.5` at any prime | Print both the inflated and uninflated `z`; **the inflated one governs**. If inflation moves the pooled `Z` across the `±2` or `±4` boundary, report the arm as UNRESOLVED and name over-dispersion of the char arm across frequencies as the next object. |
| **O-A9** | `P-SIZE` fires (unplanted carrier gives `\|z\|>3`, or `>10%` of carriers exceed `\|z\|=2`) | **Halt.** The null is mis-calibrated and every `z` in the run is void, including v1's. This supersedes every other cell. |
| **O-A10** | `S5` fires at pooled `\|z\|>4` | Object of the **next** prereg under an explicit `EXPLORATORY` heading. May not be reported as a finding of this run: it was not the primary and its null was not built for it. |
| **O-A11** | Arm A3 layer-scaling slope outside `[−1.35, −0.65]` | The fourth ladder entry is **not** the finite-`n` reference error. Print the measured slope and rename the entry; F11's prediction is recorded as failed. |
| **O-A12** | MN-μ6-shared null `sd` exceeds MN-μ6's by `>3×` | `z_p` reported against **both** nulls, the more conservative governing (carried from v1 O11). Print the variance decomposition. |

### Arm B (special strata)

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-B1** | Attestation present; both stratum controls fire; `c=0` `Z₅ ≤ −4` **and** `b=0` `Z₅ ≥ +4`, signs as pre-registered | **H-STRATA confirmed out-of-sample.** Report: over the frozen strata of these 10 curves, the x-only readout is **sub-Rayleigh** and the y-only readout **super-Rayleigh** in the low tail, opposite in sign, each against its own forced law (F10) and its own admissible null (F7). Report both `Z₅` with the §5 power numbers and the flag on `p ∈ {163,211}` for `c=0`. Named next object: **why the sign depends on which coordinate the readout uses** — an `x`-vs-`y` asymmetry of the row profile, which the generic stratum averages away. Requires its own prereg; no mechanism may be asserted here. |
| **O-B2** | Attestation present; controls fire; either `Z₅` carries the **wrong** sign, or `\|Z₅\| < 2` in either stratum | **H-STRATA falsified for that stratum.** The seen five-prime pattern did not reproduce out-of-sample. Report the failure with the power number (`c=0` had `P(5/5\|H₁)=0.60`, so a `c=0` miss at `p∈{163,211}` is expected under `H₁` and does not by itself falsify — the `Z₅` bar governs, and both are printed). Do not widen this into a statement about the generic stratum. |
| **O-B3** | Signs reproduce but magnitudes do not scale with `p` as the seen basis suggests | Report the measured `p`-dependence as a **registered magnitude with scope**, and name the `p`-scaling as an open question. Do **not** fit an exponent to `≤10` points and do **not** report an intermediate exponent as interesting (`ANOMALY_DRILL_01` failure mode). |
| **O-B4** | No attestation, **or** a stratum control fails, **or** `C-SYM-C0`/`C-REAL-B0`/`C-PARITY` fails | Arm B is **descriptive only**: print the numbers with the §0 SEEN label and the missing-control label, and issue **no verdict**. The strata then belong to a separate prereg, and this run's job for them was to build and certify the instrument. |
| **O-B5** | The `c=0` and `b=0` results agree in sign (contradicting the seen basis) | Print it. The seen five-prime opposite-sign pattern would then be prime-range-specific, which is itself the finding, reported with scope and power. |

### Cross-arm

| # | Outcome | Conclusion reported |
|---|---|---|
| **O-X1** | `S7` fragility matches `L_pred` at every registered `ε` | The `≈60%` loss at `ε=0.05` is **forced smearing** (F13); the excess is generic sub-threshold mass. Positive characterization; **not** a null and **not** a dismissal of the excess. |
| **O-X2** | `S7` deviates from `L_pred` beyond the criterion | The excess is **not** determined by the marginal `ρ` law alone — row correlations or structure outside the marginal. Named as the object of the next prereg; may not be reported as a finding of this run. |
| **O-X3** | Anything the tables above do not cover | Report the raw decomposition, the MDEs, the scope, and **no verdict**. Name the uncovered case explicitly as a gap in this spec. |

**Effect-in-an-unprojected-subspace clause (mandatory, carried and extended).** `N_LOW` is a symmetric
functional of the row profile at one frequency, at one threshold, in one fixed basis. If every layer
comes back inside its MDE, the run must **not** report "no structure". It must report: (i) the bounded
magnitude with its power number and the §6 scope; (ii) the four-layer decomposition, additive by
construction and therefore always localizing, with the fourth entry relabelled per F11; (iii) the exact
realizable scale `[0, n−1]` of F14, so the bound is a position on a known interval; and (iv) an
explicit list of what was **not** projected onto — **which** rows are low (`S5`), the **phases** of `U`
(only `|U|` enters), the autocorrelation `A_{b,c}(Δ)` whose transform the profile is, cross-frequency
structure (each `f` independent), the `S1` alternatives (a)–(d) of §3.5, thresholds other than
`ρ<0.01` (the §3.7 ladder is printed but not verdict-bearing), and `p > 19231`.

**Grade any result may earn.** Arm A: at most `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED; 10 model
primes 163…19231, generic μ₆×conj stratum, N_LOW at ρ<0.01, nulls MN-μ6/MN-neg/MN-free]`. Arm B: at
most `[EMPIRICAL — 5 out-of-sample model primes 163…991, c=0 and b=0 strata, N_LOW at ρ<0.01 against
each stratum's own forced law, null MN-μ6]`, and only under the §0 attestation. The identities of §1.4
and F1–F14 are `[PROVED]` algebra graded independently of the run. **No measured layer may carry a
`[PROVED]` tag; no outcome may be stated without the §6 scope banner. Nothing transfers to
`p = 2²⁵⁶−2³²−977`.**

## 10. WHAT CHANGED FROM v1, AND WHAT CARRIED OVER UNTOUCHED

### Changed (each named as a change, with its justification)

| # | element | v1 | v2 | why |
|---|---|---|---|---|
| 1 | **plant carrier** | the character | **MN-μ6 null draw**, paired | v1's carrier had a sub-threshold excess of its own, so the plant added and destroyed simultaneously (F13). A control must inject into a carrier with no structure to destroy. |
| 2 | **plant target** | tone `e_n(−a*d)`, `a*≠0` | **constant `t≡1`** (`a*=0`); tone retained as a second plant | the spike lands on the excluded `a=0` row, removing the F12 cancellation. Response model becomes exact, `n`-free and provably monotone. |
| 3 | **derived response** | `ε²/(1−ε²)`, no validity condition, wrong by up to `7×` at small `n` | `(1−e^{−θ/(1−ε²)})/(1−e^{−θ}) − 1` (Exp) and `erf(√(θ/(2(1−ε²))))/erf(√(θ/2)) − 1` (`χ²₁`), **with the validity condition stated**: carrier at its stratum's forced law, no sub-threshold excess | v1's model described the spike term alone |
| 4 | **criterion 3** | bare "strictly increasing over 7 levels" | **agreement with `Δ_pred` to `max(3·SE, 0.5·Δ_pred)`, plus monotonicity, on a per-prime admissible sub-grid `Δ_pred > 3·relsd`** | gating on levels below the instrument's resolution is testing noise |
| 5 | **criterion 1** | `ε=1 ⇒ N_LOW = n−2` | `ε=1 ⇒ N_LOW = n−1` | follows from change 2 (F14) |
| 6 | **`ε` grid** | spec `{.05,.10,.15,.20,.30,.50,1.00}`; script `{.05,.10,.20,.30,.50,.80,1.00}` | `{.05,.10,.15,.20,.30,.50,.80,1.00}` | restores the silently dropped `0.15`, retains the silently added `0.80` (§11 D6) |
| 7 | **`D_f` across `ε`** | independently redrawn per level | **nested chain** `D(ε₁) ⊂ D(ε₂)` | independent draws add noise to the monotonicity comparison itself |
| 8 | **negative control** | none | **P-SIZE** (unplanted carrier must not fire) | a test that fires on an unplanted null is broken however well the positive control fires |
| 9 | **null calibration** | none | **C-SELFZ** (split-half / leave-one-out replicate `z`) | every verdict is a `z` against the replicate spread; the spread itself was unchecked |
| 10 | **`S2` dispersion** | secondary, unreported | **gate `C-DISP`** with a pre-committed SE inflation | over-dispersion of the char arm would inflate every `z` |
| 11 | **error model** | replicate `z` only | **paired per-frequency `δ(f)` with a frequency-population SE**, replicate rank retained | the frozen list is a *sample* at 6 primes; the replicate `z` does not carry that error |
| 12 | **F7** | `b=0` wrongly credited with profile symmetry | **corrected**: `c=0` symmetric & complex; `b=0` real & asymmetric | the admissible null class is chosen per stratum from its own symmetry |
| 13 | **strata references** | implicit generic `REF-RAY` | **F10**: `b=0` reference is `(n−1)erf(√(θ/2))`, `8.0055×` the generic rate; `c=0` variance doubled (F9) | using the generic reference on `b=0` would manufacture a `+700%` artifact |
| 14 | **strata controls** | none existed | **P-DET-C0 / P-DET-B0** with per-stratum admissible plants and exact per-stratum floors (chirp / QR-Gauss-sum, F14) | v1's strata numbers are uncalibrated characterizations |
| 15 | **`S1`** | pre-committed secondary, never run | **not promoted**; registered as a measured bound `0.0135` at 4σ with the unprojected list | it has since been measured and is null; registering a known value as a test is the ordering failure |
| 16 | **`S6` strata** | never run, no design | **Arm B**, 5 primes seen / 5 unseen, one-sided `Z₅` with pre-registered signs, under attestation | the only genuinely out-of-sample verdict available inside the frozen scope |
| 17 | **fragility** | incidental observation in `RESULT §3` | **`S7`**, registered, with the Marcum-`Q` forced baseline and `ε=0.05` excluded as seen | a super-linear loss is forced by F13; what is testable is the deviation from the forced curve |
| 18 | **ladder layer 4** | "unit-modulus / multiset / row-budget layer" | **finite-`n` reference-model error** `−0.4950/(n−1)`, with the per-prime scaling as the registered check (Arm A3) | §1.4(ii): the conservation is universal, so layer 4 is not a structural layer |
| 19 | **hypothesis** | H-BUDGET | **H-ALIGN** (Arm A) + **H-STRATA** (Arm B); H-BUDGET recorded as settled by algebra, §1.4(iii) | a constraint carried by both arms cannot produce a contrast |
| 20 | **RNG** | one shared generator, order-dependent | per-`(p,f,arm,replicate)` SHA-256-seeded streams; plant and verdict streams disjoint | reproducibility independent of execution order |
| 21 | **seen-data discipline** | not applicable (v1 was first) | **§0 declaration**; Arm A capped at `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED]` | v1's primary numbers are seen and re-running them behind a fixed gate does not make them unseen |

### Carried over untouched

The object and its normalization; the `ρ < 0.01` threshold (inherited, not chosen); the `μ₆×conj`
symmetry table and order-12 orbit structure; generator invariance and the ban on reporting "a different
generator" as a control; **F1–F6 and F8 verbatim**, including **F5** (the character side of the primary
is not new information — the entire new content is the null column); the four-level null ladder and
every permutation construction (`μ₆`-commuting orbit permutation with per-orbit unit, MN-neg, MN-free,
one `π_f` per frequency, the MN-μ6-shared variant); `R = 64`; the frozen 10-curve list **whole**,
including `p = 211`; both frozen frequency files with their SHA-256s; `m_p` for every prime and every
stratum; the unforced-cell denominators (orbits, `n−1` rows, `K`, integer ranks over `R+1`); the forced
readout checks `C-BUDGET` / `C-A0` / `C-EQ-int` / `C-EQ-flt` / `C-NULLSYM` / `C-GEN` / `C-PREC`; the
exactness rules and the float carve-out; `S3`, `S4`, `S5` and their non-verdict status; the
effect-in-an-unprojected-subspace clause; the scope banner; and the rule that abstention is legitimate
and is not a closure.

## 11. DEVIATION DISCIPLINE

Any change to a statistic, the frozen lists (hashes in the header), the prime list, `m_p`, `R`, the
thresholds `ρ<0.01` / `r>1.5`, the `ε` grid, the plant carrier or target, the admissible sub-grids, the
null constructions, or the outcome tables must be written to
`PREREG_row_budget_lowtail_v2_DEVIATIONS.md` **before the arms are read**, with the pre-committed
value, the actual value, and the handling. A deviation is not necessarily wrong — it is necessarily
disclosed.

**D6 — a sixth v1 deviation, found while writing this spec and not in
`PREREG_row_budget_lowtail_v1_DEVIATIONS.md`.** v1 §4.1 froze `ε ∈ {0.05, 0.10, 0.15, 0.20, 0.30,
0.50, 1.00}` and printed a derived-prediction table with a `0.15` column. `row_budget_pdet_v1.py` line
25 runs `EPS = [0.05, 0.10, 0.20, 0.30, 0.50, 0.80, 1.00]` — **`0.15` dropped, `0.80` added** — and the
result table reports the script's grid. The swept levels are an input to criterion 3, which is the
criterion that failed, so this belongs in v1's deviation ledger. It does not change v1's outcome (the
dip is at `ε ≤ 0.10`, present in both grids) and it is disclosed here rather than repaired there.
v2 sweeps the union, `{0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.80, 1.00}`.
