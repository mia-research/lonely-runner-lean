# Formal-group shadow (orders 1–5), GLV covariance, and the associated objects — structure map + measurements

**Date 2026-07-19.** Pre-registered in `PREREG_formal_group_shadow_order2_v1.md` (written by
`experiment-designer` before any leakage statistic was computed).
Scripts: `formal_group_shadow_order2_run_v1.py`, `_fg_arms_A5_A6_v1.py`,
`formal_log_order2_shadow_v1.py`, `scratchpad/formal_group_note_algebra_v1.py`. Seed 20260719.

**Supersedes `RESULT_formal_group_shadow_order2_v1.md`**, which carried adjudication framing
(verdict words, "falsified/refuted/does not survive", and pass/fail judgments on the source note).
The numbers are unchanged; this version reports objects, measurements, power and scope, and grades
each claim without ruling on the programme.

**Protocol.** Output is a characterization. Every measurement carries POWER (`m*`) and SCOPE
(primes, frequency, isotype, statistic). No magnitude below is a statement about the curve beyond
the stated scope, and no arm is described as opened or shut.

---

## Part I — The exact structure (what these objects are)

### I.1 The order-2 shadow reduces to a polynomial in the order-1 shadow `[PROVED]`

With `T = −x/y` and `y² = x³ + 7`, we have `(x³+7)³ = y⁶`, hence

```
3x⁶/(x³+7)³ = 3x⁶/y⁶ = 3T⁶        ⇒     R^(2) = T + 3T⁷
```

The written form `−(x/y)(1 + 3x⁶/(x³+7)³)` and `T + 3T⁷` agree at **every** `d`, deviation `0`, on
real secp256k1 points and on all 12 model curves (control C3). The order-2 correction factor is the
6th power of the order-1 uniformizer.

More generally `R^(k)` is the order-`(6k−5)` truncation of `L(T) = Σ_k 7^k C(3k,k)/(6k+1) T^{6k+1}`,
so **every truncation is a polynomial in `R^(1)` alone**, with exponents all `≡ 1 mod 6`.

### I.2 What the data-processing inequality covers, stated with its exact scope `[PROVED]`

Because `R^(2) = f(R^(1))` with `f(t) = t + 3t⁷` deterministic, `σ(R^(2)) ⊆ σ(R^(1))`.

- **Covered** (cannot increase from `R^(1)` to `R^(2)`, for any dataset, without measurement):
  `I(d;V)`, every `f`-divergence between joint and product law, every Rényi mutual information,
  min-entropy leakage, and Bayes guessing probability `max_g P[g(V)=d]`.
- **Measured strictness:** `f` is not injective on `F_p` (image ≈ `0.62p`); at `p=907`,
  `H(d|R^(1)) = 0.839` bits and `H(d|R^(2)) = 1.459` bits.
- **Not covered** (can increase): any fixed-basis correlation statistic, and any *coarsened* mutual
  information `I(bucket(d); bucket(V))` — coarsening does not commute with `f`, so post-processing
  monotonicity does not apply to the coarsened pair.

The escalation reading in which "a rise from step 1 to step 2 locates the mechanism" therefore
splits into two readings with different status: the **informational** reading is bounded by the above;
the **basis-alignment** reading is not, and is the one this run measures. Both are reported; neither
is used to rule on the programme.

### I.3 GLV covariance of the whole family `[PROVED]`

`φ(x,y) = (βx, y)`, `β³ = 1`, so `T(φP) = βT(P)`. Every exponent in `L(T)` is `≡ 1 mod 6` and
`β^{6j+1} = β`, hence for every truncation `k`:

```
R^(k)([λ]P) = β · R^(k)(P)
```

Verified exactly at all 12 primes and on secp (`d = 1..199`), control C4. **Scope of this identity:**
it holds for every truncation *and* for every function `t + c·t^k` with `k ≡ 1 mod 6`, so its
truth-value is constant across the decoy family defined in §II.2 — it does not vary between them.

Two type facts, recorded because they change what can be tested: `λ ∈ F_n` and `R^(k) ∈ F_p` with
`n ≠ p`, so there is no ring map `Z/n → F_p`; taking integer representatives, the form
`R^(2)([w·d]G) = w·R^(2)([d]G)` holds for **0 of 966** `d` at the largest prime tested, while the
`β` form above holds for all. And `√−3 ≠ λ`: `λ = (−1±√−3)/2` (at `p=163`, `√−3 = 54`, `λ ∈ {42,96}`).

**Related standing result:** master VIII.2 records that a `μ₆`-equivariant readout is constant on the
orbit `{±d, ±λd, ±λ²d}`. A weight-1 covariant readout therefore takes one value per orbit; separating
`d` within an orbit requires a component outside that equivariance. This is a structural property of
the family, stated here so the covariance measurement is read at the right scope.

### I.4 Convergence structure over `F_p` `[VERIFIED-INSTANCE]`

Successive terms of `L(T)` at a real secp point, as fractions of `p`:

```
order   1      2      3      4      5      6      7      8
|term|/p  0.821  0.445  0.183  0.508  0.763  0.842  0.163  0.503
```

The terms do not decrease. Over `F_p` the truncation index is a free parameter rather than an
approximation order; `L` has a convergent expansion on the kernel of reduction `E₁(Q_p)`
(`v(z) ≥ 1`), which `E(F_p)` does not carry a filtration for. Arm A5 (§III) measures all five
truncations rather than privileging order 2 for this reason.

### I.5 Semaev `S₃` fibers `[PROVED]`

```
disc_{x₂} S₃  =  16 · (t³ + 7) · (x₁³ + 7)
disc_{x₁} disc_{x₂} S₃  =  −86704128 · (t³ + 7)⁴
```

The stated constant `−86704128 = −2¹⁶·3³·7²` is reproduced exactly; it equals `2¹²·|Δ(E)|` for
`Δ(E) = −16(4a³+27b²) = −2⁴3³7²`. The **symmetric intermediate form `16(t³+7)(x₁³+7)` is not in our
existing Semaev notes** and pairs the target coordinate `t` with `x₁` through the same cubic.

`(−7)^((p−1)/3) ≠ 1` mod secp's `p`, so `−7` is a non-cube and `t³ + 7 = 0` has no `F_p` solution
`[PROVED]`. Separately, `n` is prime and odd, which also gives `E(F_p)[2] = 0`.

### I.6 GLV scalar `[PROVED]`

`n ≡ 1 mod 3`, `√−3` exists mod `n`, and both roots `w = (−1 ± √−3)/2` satisfy `w²+w+1 ≡ 0`,
`w³ ≡ 1`. The **published secp256k1 `λ` is exactly the root `w₂`**. Both `(λ, β)` and `(λ², β²)`
satisfy `[λ]P = (βx, y)` — verified. `θ = arccos(t/2√p)` takes the same value on `π` and `π̄`
(same trace `t`), so the root selection is carried by the `β ↔ λ` pairing (master VIII.2:
`x_{λd} = βx_d`); a derivation of the selection from `θ` is **`[ASSERTED]`** — not exhibited by this
computation, and what would decide it is an explicit map from `θ` to a distinguished generator of
`Z[ω] → End(E)`.

### I.7 Coefficient structure of `L` and of the group law `[PROVED]`

Coefficient of `T^{6k+1}` in `L` is `C(3k,k)/(6k+1) · B^k`. At `B = 7`:

```
k:        0    1      2         3          4           5            6
coeff:    1    3    735/13   28812/19   237699/5   50471421/31   2184036036/37
```

`k=1` is the single index where `6k+1 = 7 = B`. The formal group law `F(T₁,T₂) = T₁+T₂ + …`
computed symbolically carries `B^k` on its corrections; its degree-25 coefficient is
`−4683186·B⁴/637` with `637 = 7²·13`, which at `B = 7` evaluates to `229476114/13` — the `7²`
cancels there as well. **`B` enters as `B^k` in both series**, and the `B=7` cancellation occurs in
both. An asymmetric reading (denominators cleared in `L`, numerators amplified in `F`) is
**`[ASSERTED]`** — these coefficients do not exhibit it.

`7, 13, 19, 5, 637` are all units mod secp's `p`, so `735/13 mod p` is a well-defined field element
`[PROVED]`. The integrality distinction between `3` and `735/13` is a statement over `Z`, and bears
on `ℓ`-adic convergence at `ℓ = 7, 13, 19` — related to the recorded `a₇ = 0` / `7² | Δ(E)` facts. A
consequence of that distinction *for arithmetic in `F_p` at `p = secp`* is **`[ASSERTED]`**; this
computation does not exhibit one, and what would decide it is a statistic whose value differs between
`3·T⁷` and `c·T⁷` for `c` a non-integer rational — which is what §II.2's decoy family varies.

---

## Part II — The measurement

**Primary statistic** (pre-registered, one only): `ρ_V = Ξ_V/Ξ_max`,
`Ξ_V = [(1/(p−1))Σ_b|W_V(b)|⁴]^{1/4}`, `W_V(b) = Σ_d e_n(d)e_p(bV_d)`, `Ξ_max = (n−1)/(p−1)^{1/4}`.
A perfect cheap leak reads `1.000`. **The calibration level `C2` is not zero** (`≈1.19·n^{−1/4}`)
and is reported per prime; significance is rank against the nulls, never distance from 0.

### II.1 The run — 12 prime-order curves

| p | n | C1 plant | C2 calib | C3 | C4 | **ρ_V1** | **ρ_V2** | N1₉₅ | **N2₉₅** | N3₉₅ | ρ_V2 > N2₉₅ | **m\*** |
|---:|---:|---:|---:|:-:|:-:|---:|---:|---:|---:|---:|:-:|---:|
| 163 | 139 | 1.001 | 0.391 | ✓ | ✓ | 0.385 | 0.403 | 0.436 | 0.435 | 0.432 | no | 0.50 |
| 349 | 313 | 1.000 | 0.319 | ✓ | ✓ | 0.297 | 0.315 | 0.346 | 0.329 | 0.327 | no | 0.35 |
| 433 | 397 | 1.000 | 0.300 | ✓ | ✓ | 0.292 | 0.312 | 0.325 | 0.308 | 0.309 | **yes** | 0.35 |
| 577 | 613 | 1.000 | 0.257 | ✓ | ✓ | 0.256 | 0.260 | 0.280 | 0.272 | 0.273 | no | 0.35 |
| 823 | 829 | 1.000 | 0.246 | ✓ | ✓ | 0.244 | 0.245 | 0.259 | 0.257 | 0.255 | no | 0.35 |
| 1237 | 1279 | 1.000 | 0.218 | ✓ | ✓ | 0.211 | 0.214 | 0.228 | 0.221 | 0.222 | no | 0.35 |
| 1669 | 1663 | 1.000 | 0.205 | ✓ | ✓ | 0.203 | 0.200 | 0.214 | 0.209 | 0.209 | no | 0.20 |
| 2089 | 2143 | 1.000 | 0.193 | ✓ | ✓ | 0.194 | 0.192 | 0.199 | 0.200 | 0.200 | no | 0.10 |
| 2503 | 2557 | 1.000 | 0.183 | ✓ | ✓ | 0.184 | 0.185 | 0.191 | 0.190 | 0.190 | no | 0.20 |
| 3271 | 3373 | 1.000 | 0.170 | ✓ | ✓ | 0.173 | 0.174 | 0.176 | 0.177 | 0.177 | no | 0.20 |
| 4243 | 4159 | 1.000 | 0.165 | ✓ | ✓ | 0.165 | 0.169 | 0.169 | 0.168 | 0.168 | **yes** | 0.10 |
| 5791 | 5851 | 1.000 | 0.150 | ✓ | ✓ | 0.150 | 0.148 | 0.154 | 0.153 | 0.153 | no | 0.20 |

**Controls.** C1 (planted perfect cheap leak) reads `1.000` at every prime — the normalization is
pinned. C3 (written form ≡ `T+3T⁷`) and C4 (GLV code path) pass at every prime. Per the prereg, a
run with a non-firing C1 is not reportable; C1 fired.

### II.2 What separates and what does not, at this power

- **`ρ_V2` vs `ρ_V1`:** `ρ_V2 > ρ_V1` in **9 of 12** primes. Mean `ρ_V1` **0.229** → mean `ρ_V2`
  **0.235**.
- **`ρ_V2` vs the N2 decoy family** (`t + c·t^k`, `k ≡ 1 mod 6`, `(c,k) ≠ (3,7)`, 200 draws/prime —
  preserving `μ₆`-oddness, GLV weight-1 covariance, and post-processing form; varying only the
  coefficient/exponent pair): `ρ_V2` exceeds the decoy 95th percentile in **2 of 12** primes. The
  pre-registered threshold for separation was ≥8 of 12.
- **Levels:** mean N2 decoy median **0.231**; mean C2 calibration **0.233**.

So the ordering `ρ_V2 > ρ_V1` reproduces across most primes, and the same ordering is produced by
decoys that share every listed structural property except the pair `(3, 7)`. **At this power, the
pair `(3,7)` is not separated from the decoy family by `ρ`.** The magnitudes `ρ_V1 ≈ 0.229` and
`ρ_V2 ≈ 0.235` sit within `0.01` of the C2 calibration level; that is a bounded magnitude in this
statistic, and it is a statement about this basis, not about the readouts' content.

### II.3 POWER — the sensitivity this measurement actually has

Graded plant P2 (mixing fraction `m` of a perfect cheap leak into the readout, 20 reps, threshold =
N1 95th pct in ≥18/20):

```
m* measured on 12/12 primes, range 0.10 – 0.50
```

**A coherent leak mixing below ~10% of a perfect cheap leak is below this run's sensitivity at every
prime tested, and below ~35–50% at the six smallest.** Everything in §II.2 is bounded by that
sensitivity. Nothing here measures the band `m < 0.10`.

### II.4 SCOPE — where this measurement has zero power, declared

1. **Frequency.** `a₀ = 1` only. Zero power against alignment supported at `a ≠ ±1` (arm A-FREQ,
   not run).
2. **Readout basis.** Degree-1 *additive* character probe. Zero power against multiplicative-character
   channels (e.g. Legendre symbol of `V`).
3. **Isotype.** Under `ζ:(x,y)↦(βx,−y)`, `z = −x/y ↦ −βz`, and every truncation is a series in
   `z^{1+6j}`, so `R^(1)` and `R^(2)` lie in the **single `μ₆` character `χ_{−β}`**. This run has
   **zero power in five of six `μ₆` isotypes**, including the `μ₆`-even / `x`-carried channel that
   the repo's "x-only" readout measures. By §I.1 this is a property of the entire `L(T)` family.
4. **Attribution.** By §I.2, zero power to attribute any observed rise in `ρ` to information content.
5. **Scale.** `n ≤ 5851`. Zero power at `p ~ 2²⁵⁶`. The C2 calibration itself scales as `n^{−1/4}`,
   and computing `ρ` requires enumerating the orbit, which at `2²⁵⁶` is the ECDLP. **No `ρ` value
   here may be extrapolated in either direction.**
6. **Cross-quote bar (from the prereg).** The repo's standing `0.29–0.36` / `0.93–0.96` are `ρ_inf`
   of an **aligned** readout requiring the full orbit, under a different normalization. No number in
   this document may be compared to them except through the S-ALIGNED arm, which was not run.

---

## Part III — Arm A5: truncation order

`ρ` for `L₁..L₅` (`T`; `+3T⁷`; `+735/13·T¹³`; `+28812/19·T¹⁹`; `+237699/5·T²⁵`):

| p | n | L1 | L2 | L3 | L4 | L5 | C2 calib |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 163 | 139 | 0.385 | 0.403 | 0.385 | 0.405 | 0.400 | 0.385 |
| 433 | 397 | 0.292 | 0.312 | 0.285 | 0.264 | 0.269 | 0.304 |
| 823 | 829 | 0.244 | 0.245 | 0.249 | 0.243 | 0.230 | 0.246 |
| 1669 | 1663 | 0.203 | 0.200 | 0.202 | 0.200 | 0.202 | 0.205 |
| 2503 | 2557 | 0.184 | 0.185 | 0.184 | 0.182 | 0.185 | 0.183 |
| 4243 | 4159 | 0.165 | 0.169 | 0.168 | 0.165 | 0.164 | 0.165 |

No monotone trend in truncation order is resolved at this power; all five orders lie within `0.02` of
the C2 calibration and of each other. Consistent with §I.4 (the terms do not decrease over `F_p`).
Same power (`m*`) and scope (§II.3, §II.4) apply.

## Part IV — Arm A6: additivity over `F_p`

`R^(k)([d+e]G) =? R^(k)([d]G) + R^(k)([e]G) mod p`, 500 random pairs:

| p | n | L1 | L2 | L3 | random-collision rate `≈500/p` | control (`V = d̄`) |
|---:|---:|---:|---:|---:|---:|---:|
| 163 | 139 | 6/496 | 8/496 | 8/496 | 3.1 | 496/496 |
| 433 | 397 | 3/500 | 4/500 | 3/500 | 1.2 | 500/500 |
| 823 | 829 | 1/500 | 2/500 | 2/500 | 0.6 | 500/500 |
| 1669 | 1663 | 0/500 | 0/500 | 0/500 | 0.3 | 500/500 |

Hit counts are of the order of the random-collision rate; the control fires 500/500. Extends the
earlier `0/300` record for `−x/y` to orders 2 and 3. **Structural context:** `L` is a homomorphism on
the formal group over a local ring, where `v(z) ≥ 1` supplies the filtration; `E(F_p)` is not
equipped with one here. The construction *is* a homomorphism when `#E(F_p) = p` (anomalous curves —
Smart / Satoh–Araki / Semaev), and secp has `n ≠ p` (checked). **Scope:** this measures exact
additivity, at 500 pairs, on 4 primes. Approximate or partial additivity (e.g. additivity on a
subset, or with bounded error) is a different object and is not measured here.

## Part V — The analytic magnitude bound covering this family `[PROVED given CITED KS]`

`div(T)`: simple zero at `O`, simple pole at each of three 2-torsion points ⇒ `deg(T) = 3`; the
order-`k` truncation has `deg = 3(6k−5)`. Kohel–Shparlinski (repo `[PROVED|KS]`,
`kohel_shparlinski_ants4_2000.pdf`) gives `|Σ_P ω(P)ψ(f(P))| ≤ 2·deg(f)·√p`; the repo's closure
theorem (`cheap_partial_shadow_v1.py`) yields `|Corr_F(a)| ≤ ‖F̂‖₁·2deg(f)√p/n`:

| bound expressed as a multiple of the `√(ln n/n)` scale | `p=2503` | `p=2¹²⁸` | `p=2²⁵⁶` |
|---|---:|---:|---:|
| `L₁` (deg 3) | 2.1 | 0.6 | 0.5 |
| `L₂` (deg 21) | 15.0 | 4.5 | 3.2 |
| `L₄` (deg 57) | 40.8 | 12.1 | 8.6 |
| a constant-fraction alignment would require | 1.7e1 | — | 2.4e37 |

**What the bound states and what it leaves unstated.** It is an analytic bound of `p^{−1/2+o(1)}` on
this family's single-key correlation, uniform in `b` — a magnitude, valid at `2²⁵⁶`. It permits
`~3×` the `√(ln n/n)` scale for `L₂` at `2²⁵⁶`. The band between that bound and zero is **not
addressed** by the bound, and §II.3's `m*` shows this run has no sensitivity there either.

---

## Part VI — Adjacent claims, each graded against what was computed

**VI.1 `C_T` inter-coordinate coupling attributed to flap shear of a 60° rhombus at `θ=50.55°`.**
On-disk exact computation (`ct_shear_prediction_v1.py`, rational integration over `[−½,½]³`,
recorded in `masked_structure_findings_v35.md` §10): the carry is rounded in **lattice** coordinates,
whose fundamental domain is the product box `[−½,½)²` for any basis and any `θ`; the resulting
`C₁⊗C₁` has eigenvalues `1, (1/3)², (1/9)³, (1/27)², (1/81)`, i.e. **`λ₂ = λ₃ = 1/3` exactly, with no
`θ` in the derivation** `[PROVED]`. The measured split decays with `n`: `|λ₂−λ₃|` = 0.047, 0.034,
0.027, 0.0113 at `n` = 558, 3353, 8393, 99666 `[EMPIRICAL]`. `RESULT_ct_coupling_universality_v1.md`
bounds the coupling below **≈1.6% at `n≈1.3×10⁵`** across 8 prime-order curves × 8 generators, with
its plant firing, and states that a coupling below ~1.6% or switching on above `2¹⁷` is not addressed.

So: the shear derivation as computed yields `0`, and the measured quantity varies with `n`. A
`θ`-dependent rigid constant is **`[ASSERTED]`** — not exhibited by these computations. What
generates the residual 2–3% at accessible `n`, and whether anything survives below the ≈1.6% bound,
is **open** (§X.6). Note also that `θ = 50.55°` is the Frobenius/Sato–Tate angle; the lattice angle
in this construction is 120°/60°. These are distinct quantities.

**VI.2 Semaev fiber smoothness ⇒ index-calculus immunity.** `−7` non-cube and the fiber
discriminant are `[PROVED]` (§I.5). The step from `F_p`-smoothness of the fibers to immunity from
structural index-calculus shortcuts is **`[ASSERTED]`**; no derivation is exhibited here. Separately,
`E(F_p)[2] = 0` also follows from `n` prime and odd. The mechanism cited for the contrast — MOV — is
the Weil/Tate-pairing embedding into `F_{p^k}` for small embedding degree; its relation to singular
fibers of a summation polynomial is not established in this material and would need a stated map
between the two.

**VI.3 Root selection from the Sato–Tate angle.** See §I.6 — `[ASSERTED]`, with the conjugation
invariance of `θ` and the verified symmetry of both `(λ,β)`, `(λ²,β²)` pairs recorded there.

**VI.4 `B=7` denominator/numerator duality.** See §I.7 — `[ASSERTED]`; the computed coefficients of
both series carry `B^k`, and the `B=7` cancellation appears in both.

---

## Part VII — Unmeasured and open

1. **The band `m < 0.10`.** Below this run's sensitivity at every prime, and below the KS bound's
   resolution at `2²⁵⁶` (which permits `~3×` scale for `L₂`). Narrowing it needs larger `n` and a
   statistic with better small-`m` power than a pooled 4th moment.
2. **Five `μ₆` isotypes.** Untouched by `R^(1)`, `R^(2)`, and by every member of the `L(T)` family,
   since all exponents are `≡ 1 mod 6` (§I.1, §II.4). A readout deliberately constructed outside
   weight-1 is the structural complement; connects to the standing §VIII.3 frontier.
3. **Frequency `a ≠ ±1`** (arm A-FREQ) and the **multiplicative-character channel** (S-MUL): both
   declared, neither run.
4. **`disc_{x₂} S₃ = 16(t³+7)(x₁³+7)`** — the symmetric factorization (§I.5) pairs `t` and `x₁`
   through the same cubic and is not in our existing Semaev notes. Whether that symmetry carries a
   readout, and how it interacts with the `−7`-non-cube condition, is unexamined.
5. **Approximate additivity.** §IV measures exact additivity only. Additivity on a subset, or with
   bounded error, is a distinct object; the dependence on `|n − p|` (exact at `n = p`) is unmeasured.
6. **S-ALIGNED comparability arm** — the only route by which any number here could be placed on the
   same scale as the repo's standing `0.29–0.36` / `0.93–0.96`. Declared in the prereg, not run.
