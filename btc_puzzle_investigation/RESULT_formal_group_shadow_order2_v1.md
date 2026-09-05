# RESULT — Formal-group shadow orders 1–2, GLV covariance, and the note's four side-claims

**Date 2026-07-19.** Pre-registered in `PREREG_formal_group_shadow_order2_v1.md` (written by the
`experiment-designer` agent before any leakage statistic was computed).
Scripts: `formal_group_shadow_order2_run_v1.py` (the run), `_fg_arms_A5_A6_v1.py` (arms A5, A6),
`formal_log_order2_shadow_v1.py` (secondary statistic, repo-comparable), and the exact-algebra
decider `scratchpad/formal_group_note_algebra_v1.py`. Seed 20260719.

**Anomaly-Drill protocol.** Output is a **characterization** with POWER and SCOPE attached, not a
closure. Every null below is bound to its statistic, its isotype, its frequency, and its `m*`.

---

## 0. What the note got RIGHT (verified exactly — lead with this)

| Claim | Check | Grade |
|---|---|---|
| `3x⁶/(x³+7)³` is the correct order-2 correction; `L^(2) = −(x/y)(1+3x⁶/(x³+7)³)` | algebra reproduces | **PROVED** |
| `L(T) = Σ_k B^k C(3k,k)/(6k+1) T^{6k+1}`; at `B=7` the `k=1` term is the integer `3` | series matches k≤4 | **VERIFIED-INSTANCE** |
| `λ² + λ + 1 ≡ 0 (mod n)` solvable; `λ = (−1±√−3)/2 mod n` | both roots computed; **published secp `λ` IS the `w₂` root** | **PROVED** |
| `−7` is a **non-cube** mod `p` ⇒ `t³+7=0` has no `F_p` solution | `(−7)^((p−1)/3) ≠ 1` | **PROVED** |
| Semaev `S₃` fiber discriminant `Δ(t) = −86704128·(t³+7)⁴` | `disc_{x₁} disc_{x₂} S₃` = exactly that. Intermediate: `disc_{x₂}S₃ = 16(t³+7)(x₁³+7)` — a clean symmetric form the note did not state | **PROVED** |
| GLV covariance of the truncations | `R^(k)([λ]P) = β·R^(k)(P)`, since every exponent is `1 mod 6` and `β³=1` | **PROVED** |

The `86704128 = 2¹⁶·3³·7²` factorization carries the curve discriminant `Δ(E) = −16(4a³+27b²) = −2⁴3³7²`
— the note's constant is `2¹²·|Δ(E)|`. That is real structure and it is stated correctly.

---

## 1. The load-bearing algebra: `R^(2)` is a function of `R^(1)`

Because `y² = x³+7`, we have `(x³+7)³ = y⁶`, so with `T = −x/y`:

```
3x⁶/(x³+7)³ = 3x⁶/y⁶ = 3T⁶        ⇒     R^(2) = T + 3T⁷ = f(R^(1))
```

Verified deviation `0` at every `d` on real secp points and on all 12 model curves (control C3).

**`[PROVED]` Consequence.** `σ(R^(2)) ⊆ σ(R^(1))`. By the data-processing inequality, **no**
information-theoretic quantity — `I(d;V)`, any `f`-divergence, any Rényi MI, min-entropy leakage, or
the Bayes guessing probability `max_g P[g(V)=d]` — can rise from step 1 to step 2, on any dataset,
without an experiment. `f(t)=t+3t⁷` is not injective (image ≈ 0.62p), so the inequality is **strict**:
the prereg measured `H(d|R^(1)) = 0.839` bits → `H(d|R^(2)) = 1.459` bits at `p=907`. **`R^(2)` carries
0.62 bits LESS about `d` than `R^(1)`.**

**Therefore the note's stated inference — "if step 1 gives 0.40 and step 2 gives 0.60 you have
mathematically proven the formal group logarithm is the exact mechanism" — is invalid a priori,
independent of any numbers.** What *can* rise is a fixed-basis **correlation**; a nonlinear odd
relabeling can raise one. That is basis alignment, not located mechanism, and it is what was run.

---

## 2. THE RUN — primary statistic `ρ_V`, 12 prime-order curves

`ρ_V = Ξ_V/Ξ_max`, `Ξ_V = [(1/(p−1))Σ_b|W_V(b)|⁴]^{1/4}`, `W_V(b) = Σ_d e_n(d)e_p(bV_d)`,
`Ξ_max = (n−1)/(p−1)^{1/4}`. A perfect cheap leak reads 1.000. **The floor is not zero**
(`≈1.19·n^{−1/4}`) and is reported per prime.

| p | n | C1 plant | C2 floor | C3 | C4 | **ρ_V1** | **ρ_V2** | N1₉₅ | **N2₉₅** | N3₉₅ | V2>N2? | **m\*** |
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

**All controls fired.** C1 plant reads 1.000 at every prime (normalization pinned). C3 (the note's
written form ≡ `T+3T⁷`) and C4 (GLV code path) pass at every prime.

### The decision, per the pre-committed rule

- **`ρ_V2` exceeds the N2 decoy 95th pct in 2/12 primes.** The rule required ≥8/12.
  **H_FG is falsified in the basis-alignment reading.**
- **The note's own criterion fires — and is the trap the prereg named.** `ρ_V2 > ρ_V1` in **9/12**
  primes. Read naively that is "the second-order shadow pushes the leak up," which is exactly what
  the note said would constitute proof. But the **decoys rise identically**: mean `ρ_V1` 0.229 →
  mean `ρ_V2` 0.235, against a mean N2 decoy median of **0.231** and a mean C2 floor of **0.233**.
  This is pre-registered outcome **(3)**: *the rise is generic to odd nonlinear relabeling, not
  specific to the formal group.* Any `t + c·t^k` with `k ≡ 1 mod 6` does the same thing.

### Characterization (not a verdict)

> At `p ∈ [163, 5791]`, `a₀ = 1`, degree-1 additive readout, in the single `μ₆`-character `χ_{−β}`,
> with measured detection threshold **`m* = 0.10–0.50`**, the formal-group coefficients `(3,7)` are
> **not distinguishable** from matched odd weight-1 relabelings `t + c·t^k`. Both `R^(1)` and `R^(2)`
> sit at the C2 floor to within 0.01.

**The power here is weak and that is the honest headline of the null.** `m*` says the test would
only have caught a plant mixing **10–50%** of a perfect leak. A coherent leak below ~10% mixing is
invisible to this run. This bounds a magnitude in one isotype at one frequency; it is **not** "no
structure", **not** "the formal group is irrelevant", and **not** a closure of the coordinate-shadow
avenue.

### Where power is exactly zero (declared)
`a ≠ ±1`; multiplicative-character channels; **five of the six `μ₆` isotypes** — both readouts lie in
the single character `χ_{−β}` by construction, so they are structurally blind to the `x`-carried/even
channel; attribution of any rise to *information* (§1); and `p ~ 2²⁵⁶`.

---

## 3. Arm A5 — does the alignment escalate with truncation order? No trend.

`ρ` for truncations `L₁..L₅` (`T`, `+3T⁷`, `+735/13·T¹³`, `+28812/19·T¹⁹`, `+237699/5·T²⁵`):

| p | n | L1 | L2 | L3 | L4 | L5 | C2 floor |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 163 | 139 | 0.385 | 0.403 | 0.385 | 0.405 | 0.400 | 0.385 |
| 433 | 397 | 0.292 | 0.312 | 0.285 | 0.264 | 0.269 | 0.304 |
| 823 | 829 | 0.244 | 0.245 | 0.249 | 0.243 | 0.230 | 0.246 |
| 1669 | 1663 | 0.203 | 0.200 | 0.202 | 0.200 | 0.202 | 0.205 |
| 2503 | 2557 | 0.184 | 0.185 | 0.184 | 0.182 | 0.185 | 0.183 |
| 4243 | 4159 | 0.165 | 0.169 | 0.168 | 0.165 | 0.164 | 0.165 |

No monotone trend; every order sits at the floor. **Relatedly, "order 2" has no privileged status
over `F_p`:** the successive terms of `L(T)` evaluated at a real secp point have sizes
`0.82, 0.44, 0.18, 0.51, 0.76, 0.84, 0.16, 0.50` (as fractions of `p`) — **they do not shrink.** Over
`F_p` the series does not converge, so the truncation order is a free parameter, not an approximation
order. The note's "second-order approximation" language presupposes a `p`-adic filtration that the
`F_p` point set does not have.

## 4. Arm A6 — the homomorphism the note's program needs does not appear

The "escalating polynomial path toward the discrete log" requires some truncation to be additive.
`R^(k)([d+e]G) =? R^(k)([d]G) + R^(k)([e]G) mod p`, 500 random pairs:

| p | n | L1 | L2 | L3 | chance ≈ 500/p | control (`V=d̄`) |
|---:|---:|---:|---:|---:|---:|---:|
| 163 | 139 | 6/496 | 8/496 | 8/496 | 3.1 | 496/496 |
| 433 | 397 | 3/500 | 4/500 | 3/500 | 1.2 | 500/500 |
| 823 | 829 | 1/500 | 2/500 | 2/500 | 0.6 | 500/500 |
| 1669 | 1663 | 0/500 | 0/500 | 0/500 | 0.3 | 500/500 |

Hit counts track the random-collision rate; the control fires at 500/500. This extends the earlier
0/300 record for `−x/y` to the order-2, order-3 truncations. **The formal logarithm is a homomorphism
on the formal group over a local ring (`v(z) ≥ 1`); `E(F_p)` carries no such filtration.** The
construction is a genuine attack exactly when `#E(F_p) = p` (anomalous curves — Smart / Satoh–Araki /
Semaev), and secp has `n ≠ p` (checked).

## 5. The analytic bound that covers this family (independent of the run)

`div(T)`: simple zero at `O`, simple pole at each of the three 2-torsion points ⇒ `deg(T) = 3`, so the
order-`k` truncation has `deg = 3·(6k−5)`. Kohel–Shparlinski (repo `[PROVED|KS]`) gives
`|Σ_P ω(P)ψ(f(P))| ≤ 2·deg(f)·√p`, and the repo's closure theorem
(`cheap_partial_shadow_v1.py`) turns that into `|Corr_F(a)| ≤ ‖F̂‖₁·2deg(f)√p/n`:

| | `p=2503` | `p=2¹²⁸` | `p=2²⁵⁶` |
|---|---:|---:|---:|
| bound / floor, `L₁` (deg 3) | 2.1 | 0.6 | 0.5 |
| bound / floor, `L₂` (deg 21) | 15.0 | 4.5 | 3.2 |
| bound / floor, `L₄` (deg 57) | 40.8 | 12.1 | 8.6 |
| a **constant-fraction** leak would need | 1.7e1 | — | 2.4e37 |

**What this does and does not say.** It **rules out** any constant-fraction leak from this family at
`2²⁵⁶` — `p^{−1/2+o(1)}`, an analytic statement, not an empirical null. It does **not** rule out a
small-but-real bias: at `2²⁵⁶` the bound still permits `~3×` the floor for `L₂`. The gap between
"below 3× floor" and "zero" is **open** and this method has no power in it.

---

## 6. The note's other three claims, audited at object level

**(a) "The `T¹³` term needs division by 13, which shatters the resonance and scrambles the signal in
`F_p`" — `[FALSE as a mechanism]`.** `7, 13, 19, 5, 637` are all units mod `p`. `735/13 mod p` is an
ordinary field element, no more "scrambling" than the integer `3`. The `B=7` cancellation is an
**integrality fact over `Z`**, with no `F_p` consequence at secp's prime. Where it *does* live is the
`ℓ`-adic radius of convergence at `ℓ = 7` — which is the already-recorded `a₇ = 0` / `7 | Δ(E)` fact,
not a statement about the base field.

**(b) The "`B=7` duality" (log cleans denominators / group law amplifies numerators) — `[FALSE]`.**
Computed symbolically: `B` enters **as `B^k` in both series identically**. The group law's degree-25
coefficient is `−4683186·B⁴/637` with `637 = 7²·13`; at `B=7` the `7²` **cancels**, leaving
`229476114/13`. So `B=7` cleans the group law too. There is no clean/dirty duality and hence no
"self-balancing structural lock". Separately, the log is *not* cleaned beyond `k=1`: at `B=7` the
coefficients are `1, 3, 735/13, 28812/19, 237699/5, …` — only `k=1` is an integer, because that is
the single index where `6k+1 = 7 = B`.

**(c) "The 2.75% `C_T` coupling is the exact geometric shear of a 60° rhombus, a rigid constant for
θ=50.55°" — `[already refuted on disk, before this session]`.** `masked_structure_findings_v35.md`
§10 computes the shear prediction exactly (`ct_shear_prediction_v1.py`, rational integration): the
carry is rounded in **lattice** coordinates, whose fundamental domain is the product box `[−½,½)²`
for *any* basis and *any* θ, so `C_T = C₁⊗C₁` with eigenvalues `1, (1/3)², (1/9)³, (1/27)², (1/81)`
— **`λ₂ = λ₃ = 1/3` exactly, and θ-independent.** The shear predicts a split of **0**, not 2.75%.
And the measured split **decays with n** (`|λ₂−λ₃|` = 0.047 → 0.0113 at n = 558 → 99666), which a
rigid geometric constant cannot do. `RESULT_ct_coupling_universality_v1.md` independently bounds the
coupling below ≈1.6% across 8 curves × 8 generators. Also: θ = 50.55° is the **Frobenius/Sato–Tate**
angle, not the lattice angle (120°/60°); the note conflates them.

**(d) "The sign in `w = (−1±√−3)/2` is fixed by the Sato–Tate angle θ = 50.55°" — `[FALSE]`.** θ =
arccos(t/2√p) is a conjugation-**invariant** scalar (`π` and `π̄` share `t`), so it cannot separate the
two conjugate roots. Verified: **both** `(λ,β)` and `(λ²,β²)` satisfy `[λ]P = (βx, y)`; both roots are
"the" GLV scalar for their own `β`. The pairing is fixed by the choice of `Z[ω] → End(E)`, and is
already recorded VERIFIED in master VIII.2 as `x_{λd} = βx_d`.

**(e) The GLV covariance test as literally posed is type-incoherent.** `R^(2)([w·d]G) = w·R^(2)([d]G)`
multiplies an `F_p` element by `w ∈ F_n`; there is no ring map `Z/n → F_p` (`n ≠ p`). Taking the
integer representative, it fails for **100% of d** (966/966 at the largest prime tested). The
**corrected** identity `R^(k)([λ]P) = β·R^(k)(P)` is PROVED and holds — but it holds for **every**
truncation and every decoy `t + c·t^k` with `k ≡ 1 mod 6`, so **covariance discriminates nothing**.
Worse for the program: master VIII.2 already shows a `μ₆`-equivariant readout is *constant on the
orbit* `{±d, ±λd, ±λ²d}` — covariance is a reason such a readout **cannot** separate `d` inside an
orbit, not a step toward the DLP.

**(f) "Because `−7` is a non-cube, the curve is analytically proven immune to structural
index-calculus shortcuts" — `[NOT PROVED]`.** The premise is true and the fiber-smoothness conclusion
follows. But "no rational 2-torsion" is *already forced* by `n` prime (odd), so the non-cube property
adds nothing there. And smoothness of Semaev fibers does not establish immunity to index calculus.
The stated mechanism is also wrong: **MOV** is the Weil-pairing embedding into `F_{p^k}` for small
embedding degree — it has nothing to do with singular fibers of a summation polynomial.

---

## 7. What stays open (door left open, per protocol)

1. **The sub-floor band.** `m* = 0.10–0.50` is weak power. A coherent leak below ~10% mixing is
   invisible here, and the KS bound still permits `~3×` floor at `2²⁵⁶`. Pushing `n` (and the `a≠1`
   frequency arm A-FREQ) is the probe that would narrow this.
2. **The five blind `μ₆` isotypes.** Both readouts live in `χ_{−β}` by construction. The `x`-carried /
   even channel is untouched by this run — and by §1's argument it is untouchable by *any* member of
   the `L(T)` family, since every exponent is `1 mod 6`. A readout deliberately built **outside**
   weight-1 is the structural complement, and connects to the standing §VIII.3 frontier.
3. **`disc_{x₂} S₃ = 16(t³+7)(x₁³+7)`** — the symmetric factored form is cleaner than anything in the
   current Semaev notes, and pairs `t` with `x₁` in the 2-torsion locus. Whether that symmetry has a
   readout is unexamined.
4. **Anomalous-curve boundary.** A6 fails over `F_p` because there is no filtration; it succeeds
   exactly at `#E = p`. How far the construction degrades as a function of `|n − p|`, if at all, is
   not something this run measured.
