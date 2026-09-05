# PREREG — Formal-Group Shadow, Orders 1 and 2 (`R^(1)`, `R^(2)`), + GLV-covariance arm

**Status:** PRE-REGISTRATION. Written before any leakage statistic was computed.
**Date:** 2026-07-19
**Applies to:** the enumerable curve family `E: y^2 = x^3 + 7 / F_p`, `p = 1 mod 6`, `n = #E(F_p)` prime.
**Harness of record:** `btc_puzzle_investigation/joint_shadow_decompose_v1.py` (conventions, controls),
`t_y_maxbound_v1.prime_order_curve` / `.group_coords` (exact curve arithmetic).
**Binding protocol:** Anomaly-Drill protocol (`feedback_anomaly_drill_protocol_2026_07_17`) + no-float rule
(`btc_puzzle_investigation/CLAUDE.md`).

---

## 0. DISCLOSURE — what was computed BEFORE this spec was written

Item (4) of the commission required verifying a structural identity with a script. That script was run.
It computed **algebraic/fiber properties of the map only**. It did **not** compute any leakage statistic
(`rho`, `Xi`, character sum, MI, or plant/decoy comparison). Everything it produced is listed in §S1–§S4
below and is **excluded from being an output of the run**. The primary statistic `rho` (§2) has never
been evaluated on any data.

Scripts (in repo, exact int arithmetic, reproducible):
`btc_puzzle_investigation/_prereg_fg_algebra_check_v1.py` (checks [0]-[8]),
`btc_puzzle_investigation/_prereg_fg_entropy_logseries_v1.py` (fiber collapse + `log_F` series).

---

## S. STRUCTURAL FACTS ESTABLISHED BEFORE THE RUN (these decide two arms outright)

### S1. `R^(2)` is a polynomial in `R^(1)` alone. Exact.

On `E: y^2 = x^3 + 7`, put `T = -x/y` and `R^(1) = x/y = -T`. Since `y^2 = x^3 + 7`,

```
y^6 = (x^3 + 7)^3   =>   3*x^6 / (x^3+7)^3  =  3*x^6/y^6  =  3*T^6  =  3*(R^(1))^6
```

Therefore the note's second-order shadow collapses:

```
R^(2) = (x/y) * (1 + 3*x^6/((x^3+7)^3))  =  R^(1) * (1 + 3*(R^(1))^6)  =  R^(1) + 3*(R^(1))^7      (in F_p)
```

**Verified exactly, all `d` in `1..n-1`, at `p = 163, 349, 433, 907`** — the literal expression and
`R1 + 3*R1^7` agree at every point (`_prereg_fg_algebra_check_v1.py`, checks [1],[2]). Also verified: `n` odd prime
⇒ no 2-torsion ⇒ `y_d != 0` for every `d != 0`, so `R^(1)` is defined on the whole affine orbit.

### S2. `R^(2)` is the order-7 truncation of the formal logarithm. Exact.

Solving `w = z^3 + a6*w^3` with `z = -x/y`, `w = -1/y`, and integrating `omega = dx/(2y)`:

```
omega/dz = 1 + 3*a6*z^6 + 15*a6^2*z^12 + 84*a6^3*z^18 + ...
log_F(z) = z + (3*a6/7) z^7 + (15*a6^2/13) z^13 + (84*a6^3/19) z^19 + ...
a6 = 7   =>   log_F(z) = z + 3*z^7 + (735/13) z^13 + (28812/19) z^19 - (79233/5) z^25 + ...
```

So `R^(2) = -(z + 3 z^7) = -[log_F(z)]_{<=7}` and `R^(1) = -z = -[log_F(z)]_{<=1}`. The note's
identification of the correction term with the formal group logarithm is **correct at this order**, and
the coefficient `3` is exactly `3*a6/7` at `a6 = 7` (the `7` in the denominator cancels the curve's `b=7`;
no division by 7 survives, so the formula is valid for every `p != 2, 3`).

### S3. The map `t -> t + 3t^7` is NOT injective on `F_p`. Exact, measured.

| p | \|image of f\| / p | distinct `R^(1)` over orbit | distinct `R^(2)` | `H(d\|R^(1))` bits | `H(d\|R^(2))` bits |
|---|---|---|---|---|---|
| 163 | 115/163 | 114/138 | 90/138 | 0.4135 | 0.7941 |
| 349 | 211/349 | 240/312 | 180/312 | 0.5486 | 1.0581 |
| 433 | 265/433 | 252/396 | 192/396 | 0.8645 | 1.3757 |
| 577 | — | 396/612 | 283/612 | 0.8391 | 1.4453 |
| 907 | 565/907 | 624/966 | 438/966 | 0.8394 | 1.4585 |
| 1669 | — | 1110/1662 | 792/1662 | 0.7896 | 1.3772 |

`R^(1)` has max fiber 3 over the orbit at every `p` tested (expected: `t = x/y` with `y^2=x^3+7` gives the
cubic `t^3 y^3 - y^2 + 7 = 0`). `R^(2)` fibers reach 6–7.

### S4. GLV covariance of `R^(1)` and `R^(2)` is a THEOREM, not a measurement.

`beta in F_p^*`, `beta^3 = 1`, `beta != 1`; `phi(x,y) = (beta*x, y)` equals `[lambda]` for
`lambda in Z/n` with `lambda^2 + lambda + 1 = 0 (mod n)`. Then

```
z = -x/y  |->  -beta*x/y = beta*z        =>   R^(1) |-> beta * R^(1)
R^(2) = R1 + 3*R1^7  |->  beta*R1 + 3*beta^7*R1^7  =  beta*(R1 + 3*R1^7)  =  beta * R^(2)
```

because `beta^7 = beta^(3*2+1) = beta`. **Verified exactly for all `d` at `p = 163, 349, 433, 907`**
(`_prereg_fg_algebra_check_v1.py`, check [6]; `lambda = 42, 98, 362, 824` respectively, each satisfying
`lambda^2+lambda+1 = 0 mod n`).

**Generalization:** every term of `log_F(z)` has exponent `1 + 6j`, and `beta^(1+6j) = beta`. So *every*
truncation of the formal logarithm, at *every* order, is `beta`-covariant of weight 1. The covariance is
therefore **non-discriminating**: it holds identically for `R^(1)`, for `R^(2)`, for all higher
truncations, and for every decoy `t + c*t^k` with `k = 1 mod 6`. Observing it distinguishes nothing.

**Additionally verified:** `mu6`-oddness `R^(k)(-d) = -R^(k)(d) (mod p)` holds for all `d`, `k = 1, 2`,
at all four primes (check [5]).

---

## THE NINE-ITEM SPEC

### 1. OBJECT

The object is the **pair of cheap pointwise readouts on the full orbit of a prime-order curve**:

```
V^(1): d |-> R^(1)([d]G) = x_d * y_d^(-1) mod p           d = 1 .. n-1
V^(2): d |-> R^(2)([d]G) = R^(1) + 3*(R^(1))^7 mod p
```

on `E: y^2 = x^3 + 7 / F_p`, `n = #E(F_p)` prime, `G` a generator. "Cheap" = computable from a single
public point with `O(1)` field operations; no orbit knowledge. This is the object, not a proxy: `V^(k)`
IS the quantity the note proposes, evaluated exactly.

**Tautology / construction-sharing audit.** Feature `V^(k)` and target `d` are constructed by disjoint
routes (`d` is the scalar index; `V` is a field element from the point's coordinates), so the
`r = v - w` failure mode does not apply. **However** there IS a construction-sharing hazard *between the
two arms*: by §S1, `V^(2) = f(V^(1))` with `f(t) = t + 3t^7`. Arm A1 and Arm A2 are therefore NOT
independent measurements, and §9 pre-commits what may and may not be inferred from their difference.

**Blindness by construction (subspace clause).** `Aut(E)` for `j = 0` is `mu6`, generated by
`zeta: (x,y) |-> (beta*x, -y)`. Under `zeta`, `z = -x/y |-> -beta*z`, a primitive 6th root of unity, and
every truncation of `log_F` is a series in `z^(1+6j)`, hence lies in the **single `mu6`-character
`chi_{-beta}`**. Consequently `V^(1)` and `V^(2)` are structurally blind to the other five `mu6`
isotypes — including the `mu6`-even / `x`-carried channel that the repo's "x-only" readout measures. A
null from this prereg bounds **one isotype at one frequency in one readout basis**, and must never be
written as "`R` does not leak" or as any statement about the curve.

### 2. STATISTIC — exactly one primary

For a readout `V: {1..n-1} -> F_p`, define the degree-1 additive-character alignment at the leaking
frequency `a0 = 1`:

```
W_V(b) = sum_{d=1}^{n-1} e_n(d) * e_p(b * V_d)                    b = 1 .. p-1
Xi_V   = [ (1/(p-1)) * sum_{b=1}^{p-1} |W_V(b)|^4 ]^(1/4)         (pooled 4th moment)
```

**PRIMARY STATISTIC:**

```
rho_V = Xi_V / Xi_max ,      Xi_max = (n-1) / (p-1)^(1/4)
```

Pooled, not a max-over-cells (per protocol: a max of noisy quantities is upward-biased and low-power).
The 4th moment is the concentration detector: it rises when one or a few `b` carry coherent mass,
without being a max.

*Distribution under the null.* If the `W_V(b)` behave as independent complex Gaussians with
`E|W|^2 = n-1` (the matched-null expectation), then `E[Xi^4] = 2(n-1)^2` and
`rho_floor ~= 2^(1/4) * (p-1)^(1/4) / (n-1)^(1/2) ~= 1.19 * n^(-1/4)` for `p ~ n`. **The floor is not
zero and it drifts with `n`** — at `n = 1663` it is `~0.19`. Every reported `rho` must be accompanied by
its own prime's measured C2 floor. Significance is the **rank of `rho` in the matched-null / decoy-null
sample** (§3), never a distance from 0.
*A perfect cheap leak reads `rho = 1.000` by construction of `Xi_max` (see C1, §4).*

This statistic makes the note's "a leak of 0.40" decidable: **`rho = 0.40` means "40% of the alignment a
perfect degree-1 cheap leak would produce, at `a0 = 1`, against a floor of `1.19 n^(-1/4)`."**

**Declared secondaries** (each with its own null and its own C1; a secondary may NEVER be promoted to
primary after the run, and may never be quoted as "the" leak number):

- **S-MI (coarsened predictability reading).** `I_k = I( floor(d*2^k/n) ; floor(V_d*2^k/p) )`, `k = 3`,
  plug-in estimator with the matched-null distribution supplying the bias correction. This is the
  "predictability" reading of "a leak of 0.40". *Raw (uncoarsened) MI is banned as a statistic here:*
  by §S3 `V^(1)` is at most 3-to-1, so `I(d; V^(1))` is within `log2(3)` of maximal for reasons of
  injectivity alone — it measures the map's injectivity, not leakage. It is a tautology on this object.
- **S-MUL (multiplicative-character channel).** `|sum_d e_n(d) * chi(V_d)|/sqrt(n-1)` for `chi` the
  quadratic character. Covers the channel `rho` has zero power against (§5).
- **S-ALIGNED (comparability arm).** `rho_inf` from `joint_shadow_decompose_v1.py` with `V^(k)`
  substituted as the target `g` in `recon_fidelity`, so that a comparison to the repo's standing
  aligned numbers is made on the *same* statistic.

**BANNED CROSS-QUOTE.** The repo's standing `0.29–0.36` (x-only) and `0.93–0.96` (joint) are `rho_inf`
of an **aligned** readout that requires the full orbit. `rho` here is a **cheap** readout under a
different normalization. **No number from this prereg may be compared to `0.29/0.36/0.93/0.96`** except
via the S-ALIGNED arm, which recomputes both on one scale.

### 3. MATCHED CONTROL

Three nulls, each preserving a different amount of structure. All are required.

**N1 — sign-preserving pair permutation (the leak-alignment null).**
Let `H = {1, ..., (n-1)/2}`. Draw a uniform permutation `pi` of `H` and iid signs `s_d in {+1,-1}`. Set
`V'_d = s_d * V_{pi(d)}` for `d in H`, and `V'_{n-d} = -V'_d`.
*Preserves:* the exact value multiset up to sign, the fiber-size profile, and **the `mu6`-oddness
`V(-d) = -V(d)` that both readouts have by definition**. *Destroys:* the `d <-> V_d` pairing.
**A plain flat shuffle of `V` over `d` is a FORBIDDEN null here** — it destroys the oddness the readout
possesses by construction, which is precisely the null-mismatch that manufactured the earlier
"6-7 sigma soft shadow" (`feedback` record). N1 exists to not repeat it.

**N2 — DECOY RELABELING (the formal-group-mechanism null). This is the null that decides the headline.**
```
g_{c,k}(t) = t + c * t^k ,   c in F_p^*,  k = 1 (mod 6),  7 <= k <= p-2,  (c,k) != (3,7)
V'_d = g_{c,k}( R^(1)_d )
```
*Preserves:* being a deterministic post-processing of `R^(1)`; `mu6`-oddness (`k` odd); GLV weight-1
`beta`-covariance (`k = 1 mod 6` ⇒ `beta^k = beta`, §S4); the "add one higher odd power" form.
*Destroys:* the specific formal-group coefficient/exponent pair `(3, 7)`.
**Only N2 can separate "the formal group logarithm is the mechanism" from "any odd weight-1
relabeling does this."** 200 draws of `(c,k)` per prime.

**N3 — oddness-only decoy (channel separation).** Same as N2 but `k` odd and `k != 1 (mod 6)`.
*Preserves* oddness; *destroys* GLV weight-1. Separates "oddness carries it" from "weight-1 carries it".

### 4. PLANTED CONTROL

**C1 — perfect cheap leak. Must read `rho = 1.000` (accept `>= 0.99`).**
```
dbar = signed representative of d in (-n/2, n/2)
L_d  = ( (dbar * p) // n ) mod p          # exact integer arithmetic, no float
```
`L` is odd in `d` (matched to the readout's symmetry) and is the closest a mod-`p` readout can come to
resonating with `e_n(d)`. If C1 does not read `1.000`, the normalization `Xi_max` is wrong and **no
result from this prereg may be reported** — full stop.

**C2 — floor.** `V_d` = iid uniform `F_p` values symmetrized to be odd in `d`. Must read
`rho ~= 1.19 * n^(-1/4)`. Reported per prime alongside every `rho`.

**C3 — exactness control.** `V^(2)` computed two ways (literal `x/y * (1 + 3x^6/(x^3+7)^3)` vs
`R1 + 3*R1^7`) must agree at every `d`, in ints. Already verified at 4 primes (§S1); re-run per prime.

**C4 — GLV code-path control.** `R^(k)([lambda]P) == beta * R^(k)(P)` exactly for all `d`, `k = 1,2`.
By §S4 this is a theorem; a failure means the `beta`/`lambda`/indexing code is wrong, and the run halts.

**If C1 does not fire, the null is uninformative and nothing is reported.**

### 5. POWER

**Graded plant P2.** Fix a mixing fraction `m`. Choose a uniformly random subset `S` of the `(n-1)/2`
`±`-pairs with `|S| = m*(n-1)/2`; set `V_d = L_d` for `d in S` (and `-L_d` at `-d`), `V_d = R^(k)_d`
otherwise. Sweep `m in {0, 0.01, 0.02, 0.05, 0.10, 0.20, 0.35, 0.50, 0.75, 1.0}`, 20 reps each.

**Report `m*` = the smallest `m` at which `rho` exceeds the N1 95th percentile in `>= 18/20` reps.**
Analytic expectation: a coherent contribution of size `m*(n-1)` must beat the `sqrt(n)` noise, so
`m* ~ C/sqrt(n)` — at `n ~ 10^3` that is `m* ~ few %`, at `n ~ 10^4`, `~1%`. **The measured `m*` must be
stated for every prime. A bound with no `m*` is not a result and may not be written down.**

**Where power is exactly zero — declare all of these with any null:**
1. **Frequency.** `rho` is evaluated at `a0 = 1` only. Zero power against a leak supported at `a != ±1`.
   Companion arm A-FREQ (below) exists for this; it is a separate arm, not a post-hoc fallback.
2. **Readout basis.** `rho` is a degree-1 *additive* character probe on `V`. Zero power against a leak
   carried by multiplicative characters of `V` (e.g. the Legendre symbol) — hence secondary S-MUL.
3. **Isotype.** Zero power in five of the six `mu6` isotypes (§1 subspace clause).
4. **Attribution.** Zero power to attribute any observed rise to *information*: by §7 (DPI) `V^(2)`
   carries no information `V^(1)` lacks. No experiment on this pair can establish "the formal group log
   is the mechanism of a leak" in the informational sense. Attribution power exists only for the
   weakened claim tested by N2 (basis alignment).
5. **Scale.** Zero power at `p ~ 2^256` (§6).

### 6. SCOPE

**Primes.** 12 curves, one from each disjoint window via `prime_order_curve(lo, hi)`:
`[150,250], [250,400], [400,550], [550,750], [750,1100], [1100,1500], [1500,1900], [1900,2500],
[2500,3200], [3200,4200], [4200,5500], [5500,7000]`. `n` from ~139 to ~7000.
**Generator:** the `G` returned by `prime_order_curve` (first `x0` with a square RHS). **Frequency:**
`a0 = 1`. **Curve family:** `a = 0, b = 7` only. **Readouts:** `V^(1)`, `V^(2)`, and (arm A5) the
order-13 and order-19 truncations.

**Every number produced under this prereg carries the tag `(p = ..., n = ..., a0 = 1, mu6-character
chi_{-beta}, degree-1 additive readout)` and may not be stated without it.**

**What enumerable-`p` results DO say about `p ~ 2^256`:**
- §S1 (`R^(2) = R^(1) + 3*(R^(1))^7`), §S2 (formal-log identification), §S4 (`beta`-covariance and the
  weight-1 assignment of every truncation), and the `mu6`-character assignment are **polynomial
  identities on `y^2 = x^3 + 7`, independent of `p`** (valid for every `p != 2, 3`, and `p != 13, 19`
  for the higher truncations). These **do transfer to secp256k1**.
- §7's data-processing inequality is a theorem about deterministic post-processing. It **transfers**.

**What they do NOT say about `p ~ 2^256`:**
- Every *statistic* — `rho`, `Xi`, floors, `m*`, decoy quantiles, `H(d|V)` — is measured on orbits of
  size `n <= ~7000`. The floor itself is `~n^(-1/4)`, i.e. the measurement scale changes with `n`.
  **No `rho` value may be extrapolated.**
- The statistic requires enumerating `{[d]G}`. At `n ~ 2^256` that enumeration *is* the ECDLP. No arm
  here is a distinguisher at secp scale, and no result may be phrased as one, in either direction.
- Non-injectivity fractions of `f` (§S3, `|image|/p ~ 0.62`) are `p`-specific counts, not a limit claim.

### 7. EXACTNESS

Signal path is int-only: `prime_order_curve` / `group_coords` (exact `int` EC arithmetic), `R^(1)` via
`x * pow(y, p-2, p) % p`, `R^(2)` via `(r1 + 3*pow(r1,7,p)) % p`, decoys via `pow(t,k,p)`, plant via
`(dbar * p) // n`. No `/`, no `float()`, no `**0.5` on any key-derived value.

**Float carve-out (identical to `joint_shadow_decompose_v1.py`, lines 62–70):** the character sum
`W_V(b)` is computed by building the integer histogram `H[v] = sum_{d: V_d = v} e_n(d)` and taking a
length-`p` FFT. The float sees only (i) the phases `e_n(d)`, a function of the *index* `d`, and (ii) an
FFT over a histogram of `F_p`-values. Analytic size only; no key in the float path. `Xi`, `rho`, and the
null quantiles are analytic-size floats. Significance is a **rank** among null draws (an integer count),
so no float threshold decides a verdict.

**Also int-only:** C3 (two-route agreement of `R^(2)`), C4 (GLV identity), the fiber counts of §S3, and
Arm A6's additivity check — all exact equality tests on integers.

### 8. FALSIFICATION — written before the run

The hypothesis under test, stated so it can die:

> **H_FG:** *The order-7 formal-group correction `+3t^7` is the mechanism of a cheap coordinate leak —
> i.e. it aligns `d` with the degree-1 additive readout measurably better than a structurally identical
> relabeling with the formal-group coefficients replaced.*

**H_FG is falsified if:** `rho_{V^(2)}` fails to exceed the N2 decoy 95th percentile in fewer than
8 of the 12 primes. (Under N2 each prime is an independent 5% event; `P(X >= 8 | Bin(12, 0.05)) ~ 6e-8`.)

**H_FG is ALSO falsified — and this is prior to any measurement — if the run confirms §S1**, in the
strong informational reading the note asserts ("mathematically proven that the formal group logarithm is
the exact mechanism"): see §9, outcome (0). That reading is dead by algebra.

**The note's own escalation criterion is explicitly rejected as a falsifier or a confirmer:**
`rho_{V^(2)} > rho_{V^(1)}` on its own decides nothing. Any nonlinear odd relabeling can raise a
fixed-basis correlation. Only the N2 comparison counts.

### 9. PRE-COMMITMENT — what we conclude for each outcome

**(0) The algebra arm (already decided; recorded here so it cannot be re-litigated after the run).**
`V^(2) = f(V^(1))` with `f(t) = t + 3t^7` (§S1, verified). By the **data-processing inequality**, for any
functional `Phi` of the joint law of `(d, V)` satisfying `Phi(d, h(V)) <= Phi(d, V)` for deterministic
`h` — this includes `I(d;V)`, `H(d) - H(d|V)`, every `f`-divergence between joint and product law
(KL, chi^2, TV, Hellinger), every Renyi mutual information, min-entropy leakage, and the Bayes guessing
probability `max_g P[g(V) = d]` — we have, **for every dataset, with no experiment**:

```
Phi(d, V^(2))  <=  Phi(d, V^(1))
```

and since `f` is not injective on `F_p` (§S3, `|image|/p ~ 0.62`) the inequality is strict on this
orbit: measured `H(d|V^(1)) = 0.839` bits vs `H(d|V^(2)) = 1.459` bits at `p = 907` — `V^(2)` carries
**0.62 bits LESS** about `d` than `V^(1)`.

- **CANNOT rise from `R^(1)` to `R^(2)`:** any information-theoretic or Bayes-optimal-guessing measure.
  The note's "0.40 → 0.60" is *impossible* under any such reading.
- **CAN rise:** the primary `rho`, any `|sum_d psi(d) chi(V_d)|` for a **fixed** test function `chi`, and
  any **coarsened** MI `I(bucket(d); bucket(V))` — because a coarsening does not commute with `f`, so
  post-processing monotonicity does not apply to the coarsened pair. **A rise in these measures
  quantifies alignment of a pre-existing signal with the chosen readout basis. It is not new
  information and cannot be evidence that a mechanism was located.**
- **Therefore, pre-committed:** the note's inference — "if `R^(1)` gives 0.40 and `R^(2)` gives 0.60 you
  have mathematically proven the formal group logarithm is the exact mechanism" — is **invalid a priori,
  independent of the numbers.** The only survivable form of the claim is the basis-alignment form, and
  that is exactly what N2 adjudicates. This paragraph is binding on the write-up.

**(1) `rho_{V^(2)}` beats the N2 decoy 95th pct in `>= 8/12` primes, C1 fires, `m*` stated.**
Conclude: *the specific coefficient/exponent pair `(3,7)` aligns the `mu6`-odd channel with the degree-1
additive readout at `a0=1` better than matched odd weight-1 relabelings, at `p in [150, 7000]`.* This is
a statement about **basis alignment in one isotype at one frequency**, with `m*` attached. It is NOT a
statement that information increased (impossible, §9(0)), NOT a statement about secp, and NOT a "path to
the discrete log" unless Arm A6 also fires. Next probe: A5 (higher truncations) and A6 (additivity).

**(2) `rho_{V^(2)}` does not beat the N2 decoys (`< 8/12`), C1 fires, `m*` stated.**
Conclude: **H_FG falsified in the basis-alignment reading.** Write-up form, mandatory:
*"At `p in [150,7000]`, `a0 = 1`, degree-1 additive readout, `mu6`-character `chi_{-beta}`, with detection
threshold `m* = ...`, the formal-group coefficients `(3,7)` are not distinguishable from matched odd
weight-1 relabelings `t + c t^k`."* This bounds a magnitude in one isotype. It is **not** "no structure",
**not** "the formal group is irrelevant", and **not** a closure of the coordinate-shadow avenue. Both
`rho_{V^(1)}` and `rho_{V^(2)}` and their common decoy level must still be reported as the
**characterization** (what magnitude does this channel carry, and is it above C2?), per the drill
protocol: the output is a characterization, never a verdict.

**(3) `rho_{V^(2)} > rho_{V^(1)}` but the N2 decoys rise equally.**
Conclude: *the rise is generic to odd nonlinear relabeling, not specific to the formal group.* This is
the outcome the note's own criterion would have misread as proof. Record it as such, explicitly.

**(4) `rho_{V^(2)} < rho_{V^(1)}`.** Conclude: the order-7 term degrades alignment with the degree-1
additive basis. Consistent with, but not implied by, the information loss of §9(0) — record separately;
do not merge the two.

**(5) C1 does not read 1.000, or C4 fails.** Nothing is reported. Fix the normalization / code path and
re-run. No `rho` from a run with a broken control may appear in any document.

**(6) N1 and N2 give indistinguishable null distributions.** Then N2 has not preserved what it claims to;
the decoy family is mis-specified and the mechanism arm is uninformative. Report as such, do not
substitute N1.

---

## THE ARMS

### Arm A1 — `rho_{V^(1)}` (first-order shadow)
Statistic `rho`, nulls N1 + N2 + N3, controls C1–C3, plant P2 for `m*`. 12 primes.

### Arm A2 — `rho_{V^(2)}` (second-order shadow) and the difference
Same. **Difference test, pre-committed form:** `Delta = rho_{V^(2)} - rho_{V^(1)}`, compared to the
decoy difference distribution `Delta_g = rho_{g(V^(1))} - rho_{V^(1)}` over the 200 N2 draws.
Decision rule: `Delta` above the N2 `Delta`-distribution's 95th percentile in `>= 8/12` primes.
**The run must report the per-prime sd of `Delta_g`. Without it no `Delta` claim may be made.**
No comparison of `Delta` to the note's "0.40 vs 0.60" is permitted; those were undefined numbers.

### Arm A3 — GLV covariance (re-registered as a VERIFICATION, per §S4)
The literal proposed identity is **not well-typed**:

```
proposed:  R^(2)([w*d]G)  =?  w * R^(2)([d]G)
```
LHS lives in `F_p`; `w = lambda` lives in `Z/n`. `n != p`, both prime, and there is no ring homomorphism
`Z/n -> F_p`. Taking `lambda`'s integer representative and multiplying in `F_p`, the identity **fails for
100% of `d`** — measured `138/138`, `312/312`, `396/396`, `966/966` at `p = 163, 349, 433, 907`.

Also: **`sqrt(-3) mod n` is not `lambda`.** `lambda = (-1 ± sqrt(-3)) * 2^(-1) mod n`; `sqrt(-3) = 2*lambda+1`.
Measured: `p=163`: `sqrt(-3) = 54`, `lambda in {42, 96}`, `54 != 42, 96`. Same at all four primes. The
note's "One root is the GLV scalar lambda" is false as written; the roots of `t^2 = -3` are `2*lambda+1`
and `2*lambda'+1`.

**Corrected, well-typed form — pre-registered as a pass/fail exact-integer verification, not a
measurement:**
```
R^(k)([lambda]P)  ==  beta * R^(k)(P)   in F_p,   for all d,  k = 1, 2, and all truncations of log_F
```
**Pre-committed conclusion (both directions):**
- *Holds* (expected by the proof in §S4, and already verified at 4 primes): **this is zero evidence for
  a leak.** It holds for `R^(1)`, for every truncation, and for every N2 decoy, because every exponent is
  `1 mod 6`. It confirms the code path (`beta`, `lambda`, orbit indexing) and nothing else. The sentence
  "the leak is a GLV-covariant formal group shadow" may **not** be written on the strength of it.
- *Fails:* a bug in `beta`, `lambda`, or the orbit indexing. Halt and fix; no other arm may be reported
  from that run.
- **Informative replacement, if a GLV-flavoured measurement is wanted:** decompose a readout by
  `mu6`-isotype and measure `rho` **per isotype**. `V^(1)`, `V^(2)` occupy `chi_{-beta}` only, so this
  arm's real content is: *which isotype carries the alignment, and are the other five above C2?* That
  is where "the effect might live in a subspace we are not projecting onto" gets tested.

### Arm A4 — S-ALIGNED comparability
`recon_fidelity(..., g = V^(k), mask)` in `joint_shadow_decompose_v1.py`, with its own char-vs-random
target control (the existing GENERIC/CHAR-SPECIFIC test). This is the **only** channel through which any
comparison to the standing `0.29–0.36 / 0.93–0.96` numbers may be made.

### Arm A5 — the "escalating polynomial path"
`R^(3) = R1 + 3 R1^7 + 735*13^(-1) R1^13`, `R^(4) = R^(3) + 28812*19^(-1) R1^19` (mod `p`; requires
`p != 13, 19`). Same statistic, same nulls, same C1. **All are functions of `R^(1)`; §9(0) applies to
every one of them** — the informational content is non-increasing along the whole "escalating path",
and strictly decreasing wherever the truncation is non-injective. Pre-committed: a monotone rise in
`rho` along `k = 1, 7, 13, 19` that also beats N2 at each order is a **basis-alignment gradient**, and is
reported with that name.

### Arm A6 — additivity of the truncation (the mechanism the note's program actually needs)
The formal logarithm is a homomorphism `E_1(Q_p) -> G_a` **on the formal group over a local ring**, i.e.
for points with `v(z) >= 1`. Over `F_p` there is no such filtration: every affine point has `z in F_p`
with no valuation, and `log_F` neither converges nor terminates. Whether a truncation is nonetheless
additive mod `p` is decidable:

```
for random pairs (d, e):   R^(k)([d+e]G)  ==?  R^(k)([d]G) + R^(k)([e]G)  (mod p)
```
Exact integer equality; `M = 10^4` random pairs per prime per order `k in {1, 7, 13, 19}`.
Matched null: the same count for N2 decoys `t + c t^k`.
**Statistic:** the exact integer count of additive pairs. **Control:** the same check on the additive
group `V_d = dbar mod p` must give `M/M` (fires).
**Pre-commitment:**
- Count `= M` at some order: `d |-> R^(k)` is additive on the orbit; report immediately — that would be
  the mechanism the note names, and it is checkable by exact arithmetic alone.
- Count consistent with the ~`M/p` chance level and with the N2 decoys: the truncation is not additive
  over `F_p` at that order; the phrase "escalating polynomial path toward the discrete log" has **no
  named mechanism** and may not be used. Report the count and the decoy count, scoped.
- Count above chance but below `M`: report the exact excess and the decoy comparison; characterize (which
  pairs?), do not verdict.

### Arm A-FREQ — frequency scope (separate arm, not a fallback)
`rho` recomputed with `a0` pooled: `Xi^(pool) = [ (1/((n-1)(p-1))) sum_{a != 0} sum_{b != 0}
|W_V(a,b)|^4 ]^(1/4)`, same normalization discipline, its own C1 and C2. Registered now so that a null
at `a0 = 1` cannot be silently widened to "all frequencies", and so that this arm cannot be introduced
post hoc if `a0 = 1` disappoints.

---

## RUN CHECKLIST (all must be present in the RESULT file, or it is not reportable)

- [ ] C1 reads `1.000` (`>= 0.99`) on every prime.
- [ ] C2 floor reported next to every `rho`.
- [ ] C3 two-route `R^(2)` agreement exact on every prime.
- [ ] C4 GLV identity exact on every prime.
- [ ] `m*` from the graded plant reported per prime.
- [ ] N1, N2, N3 null distributions reported (not just their 95th percentiles).
- [ ] sd of `Delta_g` reported per prime.
- [ ] Every `rho` tagged `(p, n, a0=1, mu6-char chi_{-beta}, degree-1 additive)`.
- [ ] The five zero-power statements (§5) restated verbatim in the conclusion.
- [ ] §9(0) (the DPI paragraph) restated verbatim; no informational claim about `R^(2) > R^(1)`.
- [ ] No cross-quote against `0.29/0.36/0.93/0.96` outside Arm A4.
- [ ] Any deviation from this spec listed in `PREREG_formal_group_shadow_order2_v1_DEVIATIONS.md`.
