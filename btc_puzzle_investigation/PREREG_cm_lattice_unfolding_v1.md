# PREREG — CM Lattice-Unfolding Leak Test (`cm_lattice_unfolding_v1`)

**Status: FROZEN pre-registration. No data seen. Written before any run.**
Grade of any result this spec can produce: **EMPIRICAL**, scoped to the small-p
ladder in §6. Nothing here can license a claim at the 2²⁵⁶ scale (§6 scale banner).

This spec pre-registers ONE experiment with a designated PRIMARY statistic (§2)
and pre-registered SECONDARY arms under a single family-wise multiplicity control
(§2d). It obeys the six BINDING design constraints supplied in the task; each is
discharged at the section named in brackets.

---

## 1. OBJECT

**What we measure.** Whether the PUBLIC single-point Eisenstein lift of the point
`P = [d]G` carries information about the PRIVATE 2-D lattice unfolding of the
scalar `d`, BEYOND the trivial `d ↔ [d]G` bijection.

- **Curve / arithmetic (given, on disk).** `E: y² = x³ + 7` over `F_p`,
  `p ≡ 1 mod 3`, CM by `Z[ω]`. `n = #E(F_p)` prime. `π_p ∈ Z[ω]`, `N(π_p)=p`,
  `N(π_p−1)=n`. GLV `φ = [λ]`, `λ ≡ ω mod (π_p−1)`. Silverman–Stange amicable
  partner `π_n ∈ Z[ω]`, `N(π_n)=p`.

- **FEATURE (public, function of the POINT only — no `d`).**
  `Φ(P)` built from `eis(X)` where `X = x(P)`:
  `eis(X)` (`int1_frame_operator_v1.build_secp` / `make_lift`, exact integer
  Babai reduction of `X` against the gauss-reduced Z-basis of the ideal `(π_p)`,
  norm `p`) returns `(u,v) ∈ Z²`. Derived public integers: `eps(X) ∈ {0,1,2}`
  (flap indicator, Cap-Law ¾:⅛:⅛), `sextant(u,v) ∈ {0..5}`, cubic exponent
  `e ∈ {0,1,2}` (`x^((p−1)/3) ≡ β^e`), sign `s = [ y > p/2 ]`, norm
  `Fraction(enorm(u,v), p) ∈ [0, 3/4]`.

- **TARGET (private, function of the SCALAR only — needs `d` / the DLP).**
  `LATT(d) = (a,b) ∈ Z²` := exact integer Babai reduction of the Eisenstein
  integer `(d mod n) + 0·ω` (Z-coords `(d mod n, 0)`) against the gauss-reduced
  Z-basis of the ideal `(π_p−1)` (norm `n`). Under `d → λd`, `λ ≡ ω mod (π_p−1)`
  ⇒ `(a,b) → ω·(a,b)` reduced (μ₃-covariant), matching `φ` on the feature side.
  Reduced target: `T_ℓ = (a mod ℓ, b mod ℓ) ∈ (Z/ℓ)²`.

- **PARTNER FEATURE (public, function of the POINT only — ARM N).**
  `Ψ(P)` := exact integer Babai reduction of `X` against the gauss-reduced Z-basis
  of the ideal `(π_n−1)` (norm `p`), giving `(u',v') ∈ Z²`; reduced
  `Ψ_ℓ = (u' mod ℓ, v' mod ℓ)`.

**DISJOINTNESS (discharges trap #2, residue-vs-component tautology).**
`Φ` and `Ψ` are functions of `X` (public point coordinate) reduced against the
norm-`p` lattices `(π_p)` resp. `(π_n−1)`. `T` is a function of `d` (scalar)
reduced against the norm-`n` lattice `(π_p−1)`. **Different input** (`X` vs `d`),
**different lattice** (norm `p` vs norm `n`). Neither is a sub-construction of the
other; there is no `r = v − w` residual anywhere. The ONLY coupling is the DLP
(`X = x([d]G)`). Predicting `T` from `Φ` beyond the matched null (§3) is therefore
a non-tautological partial-DLP leak test. **Construction audit** (§8) verifies at
runtime that `d` never enters the `Φ`/`Ψ` code path and that `X` never enters the
`T` code path.

**Tautology risk statement (discharges trap #1).** `[d]G` is a bijection
`Z/n → E(F_p)`, so any injective feature of `P` has full MI with `d` by
construction. This spec therefore never measures `I(feature; d)`; it measures
`I(Φ; T)` on a μ₆-transversal against a shuffle-of-pairing null (§3). A raw
`I(feature; d)` would be tautologically maximal and is NOT a registered statistic.

---

## 2. STATISTIC

### 2a. PRIMARY statistic (exactly one, named now)

`S := Î(Φ₂ ; T₂)` — the plug-in empirical **mutual information in bits** between
the frozen public feature alphabet `Φ₂ = (u mod 2, v mod 2, eps) ∈ (Z/2)²×{0,1,2}`
and the frozen target `T₂ = (a mod 2, b mod 2) ∈ (Z/2)²`, computed on the
**μ₆-transversal sample** (§3) of a single ladder prime `p` (§6).

**Distribution under the null.** Under the matched null (§3, shuffle the `Φ ↔ T`
pairing on the transversal), `Φ₂` and `T₂` are independent with the observed
marginals; `Î` is the standard plug-in MI of two independent categoricals. Its
plug-in bias is a positive constant depending only on the marginals and `N`, and
is **absorbed by ranking against the permutation null** (the null shares the exact
marginals). The reported p-value is exact:
`p_perm = (1 + #{ Ŝ_b ≥ S_obs }) / (1 + B)`, `B = 9999`, over `B` independent
`Φ ↔ T` shuffles. Integer counts only; the `log` inside `Î` is a monotone
transform ranked against the matched permutation null (float carve-out, §8).

Chosen as a POOLED, low-df targeted statistic (not a max-over-cells): one MI on a
fixed small alphabet, aimed at the joint 2-D `(a,b)`-residue object that constraint
#3 names as the LIVE hypothesis.

### 2b. SECONDARY arms (pre-registered, under §2d multiplicity control)

- **ARM P sweep:** `S_ℓ = Î((u mod ℓ, v mod ℓ, eps) ; (a mod ℓ, b mod ℓ))` for
  `ℓ ∈ {3,5,7}`, same transversal, same shuffle null.
- **ARM N (amicable second equation):** conditional MI
  `S_Nℓ = Î((Φ_ℓ, Ψ_ℓ) ; T_ℓ) − Î(Φ_ℓ ; T_ℓ)` for `ℓ ∈ {2,3,5,7}` (est. of
  `I(Ψ_ℓ ; T_ℓ | Φ_ℓ)`). Null: permute `Ψ_ℓ` **within `Φ_ℓ` strata** (preserves
  `Φ_ℓ`–`T_ℓ` dependence exactly, destroys `Ψ_ℓ`–`T_ℓ` dependence within cells) —
  the matched null for a conditional-MI statistic. `B = 9999`.

### 2c. On the `ℓ | n` vs `ℓ ∤ n` distinction (discharges trap #4 and the n-prime degeneracy)

`n` is prime at every ladder rung (§6 constraint), so **no small `ℓ | n` exists**
(only `ℓ = n`). The registered target is therefore the **integer lattice-coordinate
residue** `(a mod ℓ, b mod ℓ)` — well-defined for any `ℓ` via the fixed canonical
integers `(a,b)`, independent of `ℓ | n`. The `ℓ ∤ n` generic-modulus arm and the
`ℓ | n` group-character arm coincide as this integer-residue test; the group-
character (order-`n`) content is reachable only at the full modulus and is NOT part
of this frozen spec. This is a conditional-ENTROPY / MI test (does `Φ` reduce
`H(T_ℓ)`?), never a vanishing / exact-identity test (DC5: prime-modulus full-orbit
sums cannot vanish exactly).

### 2d. Multiplicity control

One permutation loop recomputes ALL registered statistics per shuffle (4 ℓ × ARM P
+ 4 ℓ × ARM N = 8 statistics). Family-wise p-value = permutation rank of the
**maximum** standardized statistic across the 8 (min-p / max-T method), exact,
integer counts. **Family-wise α = 0.001.** The PRIMARY statistic (§2a) additionally
carries its own single-test `p_perm` reported un-corrected for transparency, but the
LEAK verdict requires the family-wise-corrected threshold.

---

## 3. MATCHED CONTROL

**The μ₆ trap (discharges the null-mismatch failure).** `μ₆ = ⟨φ, [−1]⟩` acts
DIAGONALLY: on the point (`e → e+1 mod 3`, `s → 1−s`, i.e. `sextant → sextant+2`)
and on the scalar (`d → ±λ^j d`). Both `Φ` and `T` are μ₆-covariant, so within a
full 6-point orbit the feature-sextant and target-sextant increment **in lockstep**
— a FORCED correlation that is not leak. A plain `d ↔ (a,b)` shuffle on the full
orbit set destroys this lockstep and would manufacture apparent MI (the recorded
"6–7σ soft shadow → null-mismatch artifact" failure mode). Such a shuffle is an
**INVALID null here** and is NOT used.

**The matched null (used).** Work on the **μ₆-transversal**: keep exactly the one
point per orbit with `e = 0 ∧ s = 0` (`y < p/2`); `N` = number of distinct μ₆
orbits `≈ (n−1)/6`. On the transversal the μ₆ lockstep is already quotiented out
(sextant/`e`/`s` are constant), so the matched null is the **shuffle of the `Φ ↔ T`
pairing among the `N` transversal samples**.
- **Preserves:** the transversal marginal of `Φ` (Cap-Law, `eps` distribution,
  `(u mod ℓ,v mod ℓ)` marginal), the marginal of `T`, and the μ₆ quotient
  structure (μ₆ is preserved *because it is quotiented*, not shuffled).
- **Destroys:** only the specific `Φ ↔ T` correspondence — the object under test.

Every "k/k" tally reports **distinct-orbit** counts (μ₆-quotient), never raw
point counts (discharges the distinct-configuration rule).

**μ₆-MISMATCH WITNESS (registered null-validity check, NOT a power arm).** Run
`S` on the FULL orbit set with the plain `d ↔ (a,b)` shuffle. **Pre-committed
prediction:** the full-set/plain-shuffle statistic shows inflated MI that VANISHES
on the transversal. If the plain shuffle does NOT show inflation, or the transversal
does NOT remove it, the null model is mis-specified and the run is **inadmissible**
(redo before any verdict).

---

## 4. PLANTED CONTROL (must fire or the arm is VOID)

**Positive plant (power calibration).** Augment the feature with a synthetic symbol
`c(P)` that equals `(a mod ℓ)` with probability `ε` (drawn from a fixed seed keyed
to the point index) and is uniform on `Z/ℓ` otherwise; feature becomes `(Φ_ℓ, c)`.
Sweep `ε ∈ {0, 1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 1}`. The pipeline MUST recover the
injected dependence; report `ε_min` = smallest `ε` with family-wise
`p_perm < 0.001` at the run's `N`. **If `ε = 1` (full plant) does NOT fire, the
statistic/pipeline is broken and every arm is VOID — full stop, no null is
reported.** `c` is drawn from `(a mod ℓ)` (a target quantity) ONLY inside the plant
harness, never in the real feature path.

**Hard null (must NOT fire — calibration).** Feature = a fixed public function of a
point that has been **pre-paired to a random scalar** (`Φ` of point `i` matched to
`T` of a random `j`). Over 100 independent such re-pairings, the empirical
family-wise false-positive rate at α = 0.001 must be `≤ 2α`. If it exceeds `2α`,
the permutation null is miscalibrated and the run is **VOID**.

---

## 5. POWER

Detection is a permutation MI test with `df = (A−1)(ℓ²−1)`, `A = |alphabet(Φ_ℓ)|`
(`≤ 12` for ℓ=2; `eps` may be constant on the transversal, then `A = 4`).
Analytical detectable MI at family-wise α = 0.001, power 0.8:
`I_min(bits) = λ_nc(df, α=0.001, power=0.8) / (2·N·ln2)`, `λ_nc` the χ² non-central
parameter. For the PRIMARY (`ℓ=2`, `A=4`, `df=9`, `λ_nc ≈ 27`):
- ladder prime `p ≈ 10⁵` ⇒ `N ≈ 1.6·10⁴` ⇒ `I_min ≈ 27/(2·1.6·10⁴·0.693) ≈ 1.2·10⁻³ bits`.
- power prime `p ≈ 10⁶` ⇒ `N ≈ 1.6·10⁵` ⇒ `I_min ≈ 1.2·10⁻⁴ bits`.

**The arm is powered iff `I_min ≤ 0.01 bits` at the run's `N`** (satisfied by the
ladder above). BOTH numbers are reported: the analytical `I_min` AND the empirical
`ε_min` from §4. A null with `I_min > 0.01 bits` is UNDER-POWERED and may not be
read as a bound (recorded as "insufficient power", not as a result).

---

## 6. SCOPE

**Small-p ladder (deterministic selection rule — frozen, no cherry-picking).**
For each residue class `c ∈ {1, 7} mod 12` (secp is `7 mod 12`; `1 mod 12` is the
companion class; both give `p ≡ 1 mod 3`):
- **Ladder rungs:** the smallest 3 primes `p > 10⁴` with `p ≡ c (mod 12)` such that
  `E: y²=x³+7` over `F_p` has `n = #E(F_p)` prime.
- **Power rung:** the smallest 1 prime `p > 10⁶` with `p ≡ c (mod 12)` and `n` prime.
Total 8 primes (4 per class). Every reported number carries its `p`, `n`, `N`,
`class mod 12`, `ℓ`, and arm. No number is stated without this scope.

**Real-key witness (validation/witness step, NOT a power arm).** Puzzles **#135**
and **#140** (public `(x,y)` on disk, `d` unknown for both). A positive at small `p`
yields a FROZEN predictor; on #135/#140 we compute `Φ`, `Ψ` (public) and RECORD the
predicted `(a mod ℓ, b mod ℓ)` distribution. Because `d` is unknown for both, this
is a **recorded falsifiable prediction** (checkable if/when a key is solved), NOT a
present validation.

**Scale banner (discharges trap #6).** A positive at small `p` is **scale-blocked**:
it licenses (i) running the frozen predictor on the covered small-`p` orbits, (ii) a
recorded prediction on #135/#140, and (iii) making the amicable over-determination
(ARM N) testable at small `p`. It does **NOT** license any claim about the leak's
presence, size, or exploitability at `p = 2²⁵⁶`. A null at small `p` bounds the
channel only at small `p`.

**In-bounds (discharges trap #7).** Scalars `d` are drawn uniformly on `[1,n)` (no
generator bias). Any public→`(a,b)` structure is a property of the curve's CM/GLV
arithmetic — number-theoretic key structure, in-bounds per the 2026-08-18 boundary
decision. The PRNG/generation mechanism is not studied.

---

## 7. FALSIFICATION

**Per arm, written before the run:**

- **Kills the leak hypothesis (ARM P):** family-wise `p_perm ≥ 0.001` on the
  transversal, WITH (a) the `ε=1` plant firing, (b) `I_min ≤ 0.01 bits`, (c) the
  hard-null FP rate `≤ 2α`, and (d) the μ₆-witness behaving as pre-committed. This
  result **bounds** the public single-point lift channel to `< I_min bits` about
  `(a mod ℓ, b mod ℓ)` on the transversal, **at the stated small-`p` scope** — a
  scoped bounded channel with power+scope, **NOT a closure** and NOT a statement
  about `2²⁵⁶`.
- **Kills the amicable lever (ARM N):** conditional `p_perm ≥ 0.001` with the
  ARM-N plant firing ⇒ the partner-lattice public feature adds `< I_min,N bits`
  beyond the `(π_p)` side at scope — bounded, scoped, not a closure.
- **Un-decidable (inadmissible, redo):** any of — `ε=1` plant does not fire
  (arm VOID); hard-null FP `> 2α` (null miscalibrated, VOID); μ₆-witness does not
  match its pre-commitment (null mis-specified). None of these is a null result.

A null on the `(π_p)`-only single-character content says **nothing** about ARM N
(constraint #3): the ARM-N verdict is read only from its own conditional statistic.

---

## 8. EXACTNESS

**Signal path is int/Fraction only.** `eis`, `Φ`, `Ψ`, `LATT`, `T`, all point
arithmetic, all Babai reductions (`rdiv`, `make_lift`, `gauss_reduce`), `enorm`,
`sextant`, `cubic_exp`, and all permutation counts are exact Python `int`; the
lift-norm feature is `Fraction(enorm, p)`. No `/`, `float()`, `**0.5`, `round`,
`math.*`/`np.*` on any curve-, feature-, or target-derived value.

**Construction audit (runtime assertions, frozen):**
1. `d` symbol is never referenced inside the `Φ`/`Ψ` code path (assert at import
   via source scan of the feature functions).
2. `X`/point data is never referenced inside the `LATT`/`T` code path.
3. `LATT` and `Φ`/`Ψ` use provably different lattice bases (`(π_p−1)` norm `n` vs
   `(π_p)`/`(π_n−1)` norm `p`) — assert `enorm`-determinants differ as expected.

**Float carve-out (named, justified).** The ONLY float is `math.log` inside the MI
estimator `Î`, tagged `# noqa: float`. It is a monotone transform whose value is
used ONLY via its rank against the matched permutation null (§2a); the null shares
the exact marginals so all plug-in bias cancels in the rank. No key, feature, or
target value ever passes through a float; no float threshold is applied to data.

**Gate:** `bash check_no_float.sh <new signal-path file>` must exit 0 before any
statistic is computed.

---

## 9. PRE-COMMITMENT — outcome table (filled BEFORE the run)

Preconditions for ANY verdict (else inadmissible → redo): `ε=1` plant fires;
hard-null FP `≤ 2α`; μ₆-witness matches its pre-commitment; `I_min ≤ 0.01 bits`.

| Arm | Outcome | Pre-committed conclusion (grade EMPIRICAL, scope = stated `p,n,N,ℓ,class`) |
|---|---|---|
| **P (primary, ℓ=2)** | family-wise `p_perm < 0.001` | **LEAK detected** on the lattice-residue channel at scope. Public single-point lift carries `(a mod ℓ,b mod ℓ)` beyond the bijection. Un-gates the conditional d-shadow arsenal on covered small-`p` orbits; record the frozen predictor; emit the #135/#140 recorded prediction. Scale-blocked (§6). |
| **P** | family-wise `p_perm ≥ 0.001`, preconditions met | **Bounded null:** channel `< I_min bits` about `(a mod ℓ,b mod ℓ)` on the transversal at scope. A scoped bounded channel with power+scope — NOT a closure, NOT a `2²⁵⁶` statement. Collapses the circular single-point arsenal cleanly at this scope. |
| **P sweep (ℓ∈{3,5,7})** | any `p_perm < 0.001` (FWER-corrected) | LEAK on that `ℓ`'s residue channel at scope; report which `ℓ`. |
| **P sweep** | all `p_perm ≥ 0.001` | bounded null across `ℓ ∈ {3,5,7}` at scope, each with its `I_min`. |
| **N (amicable)** | conditional `p_perm < 0.001` | The amicable **second equation adds information** beyond the `(π_p)` side at scope — the "two equations" lever fires; the over-determination of `(a,b)` is testable at small `p`. |
| **N** | conditional `p_perm ≥ 0.001`, ARM-N plant fired | Partner-lattice public feature adds `< I_min,N bits` beyond `Φ` at scope. Bounded, scoped; says nothing about ARM P's own verdict. |
| **any arm** | `ε=1` plant did NOT fire | **VOID** — null uninformative; fix pipeline; no verdict. |
| **any arm** | hard-null FP `> 2α` | **VOID** — permutation null miscalibrated; no verdict. |
| **run** | μ₆-witness contradicts §3 pre-commitment | **INADMISSIBLE** — null mis-specified; redo before any verdict. |

**Brick-either-way.** A LEAK (P or N) un-gates the conditional d-shadow arsenal on
covered points and makes the amicable over-determination testable; a bounded null
(P and N, preconditions met) collapses the circular single-point arsenal and bounds
the lattice channel — with power and scope, not a closure. Either resolves the
single load-bearing "public function of `P` is redundant with `P`" dependency at the
small-`p` scope, decidably.

---

### Frozen feature/target/null registry (for the audit)

- `Φ_ℓ = (u mod ℓ, v mod ℓ, eps)`, `(u,v)=eis(X)`, lattice `(π_p)` norm `p`. Public.
- `Ψ_ℓ = (u' mod ℓ, v' mod ℓ)`, `(u',v')` = Babai(X, `(π_n−1)`) norm `p`. Public.
- `T_ℓ = (a mod ℓ, b mod ℓ)`, `(a,b)=LATT(d)` = Babai((d mod n,0), `(π_p−1)`) norm `n`. Private.
- Transversal: one point/orbit, `e=0 ∧ s=0`. `N ≈ (n−1)/6`.
- Primary statistic: `S = Î(Φ₂;T₂)` bits, permutation p-value, `B=9999`.
- Matched null: shuffle `Φ↔T` on transversal (ARM P); permute `Ψ` within `Φ`-strata (ARM N).
- Multiplicity: max-T over 8 statistics, family-wise α = 0.001.
- Plants: positive `ε`-sweep (must fire at `ε=1`); hard null (FP `≤ 2α`); μ₆-witness.
- Exactness: int/Fraction; float carve-out = `math.log` in `Î` (`# noqa: float`); `check_no_float.sh` exit 0.
- Ladder: 3+1 primes per class `c∈{1,7} mod 12`, `p>10⁴` (power `p>10⁶`), `n` prime, `y²=x³+7`.
