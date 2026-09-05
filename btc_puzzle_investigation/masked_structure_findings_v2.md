# Masked-Structure Investigation — Findings v2  (CORRECTIONS to v1)

**Date:** 2026-07-16 · supersedes `masked_structure_findings_v1.md`
**Why v2:** v1 was audited on challenge and **three of its claims were wrong or inflated.**
This version retracts them. Scripts: `masked_structure_harness_v1.py`,
`cubic_moment_power_v1.py` (new).

> v1's errors were all the same error in different costumes: **stating a fact at a
> higher epistemic grade than earned** — a textbook identity as a discovery, a shape
> constant as arithmetic, a zero-power test as a null. Recorded in full because the
> failure mode is the point.

---

## R1. RETRACTED — the "χ₂ doubling transport law" is the textbook duplication formula

v1 §4 called `χ₂(x(2P)) = χ₂(x·(x³−56))` a *"PROVED + VERIFIED y-free transport law…
a positive curve fact worth keeping."* **It is none of those things.**

For any short Weierstrass curve, `x(2P)` is a rational function of `x` **alone** — the
standard division-polynomial fact, and precisely why x-only (Montgomery) ladders exist.
So *"no dependence on y"* is not a property discovered: **everything** about `x(2P)` is
y-free. The remainder is one line — the denominator `4(x³+7) = 4y²` is a square, so its
character is 1.

The "0/3000 verification" verified that our code implements secp256k1's duplication
formula correctly. That is a **self-test of the arithmetic**, not evidence of structure.
It yields no reduction (evaluating `χ₂(x(x³−56))` requires all of `x`).

**Correct tag: CITED (textbook).** Not a finding. Deleted from the positive ledger.

---

## R2. CORRECTED — the Cap Law is TRUE and PROVED, but it is pure lattice geometry
##      with ZERO arithmetic content

v1 §1 presented the Cap Law as a new exhaustively-verified law and made *"prove it"* the
**top open item**. The proof is **two lines**, and it *deflates* the result.

### The proof

`build()` defines the label directly as *"is a lattice reduction needed?"*:

```python
def eps(X):
    U0 = eis(X); U1 = eis((beta*X) % p)
    c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
    if c == (0,0): return 0            # eps=0  <=>  om^2 * z  is ALREADY in the domain
```

So `ε(x) = 0 ⟺ ω²·z ∈ P`. In the reduced basis, ω acts by a **fixed integer matrix of
order 3, identical at every prime** (measured: `ω²R₁ = −R₂`, `ω²R₂ = R₁−R₂`; the p=100003
row shows only the ω↔ω² relabel that follows the sign of β). Hence for `z = uR₁ + vR₂`
with `u,v ∈ [−½,½)`:

```
    ω²z = u(−R₂) + v(R₁−R₂) = v·R₁ − (u+v)·R₂          coefficients (v, −(u+v))
    ω²z ∈ P  ⟺  |u+v| ≤ ½                              (|v| ≤ ½ is automatic)
    ⇒  ε(x) ≠ 0  ⟺  |u+v| > ½  ⟺  |⟨z, D̂⟩| > a/2       ∎
```

(last step: `⟨z, R₁+R₂⟩ = (3p/2)(u+v)` and `a = |R₁+R₂|/2 = √(3p)/2`, so
`|⟨z,D̂⟩| = a·|u+v|`.) **Verified 0/111,018** exhaustively, and now also
`ε≠0 ⟺ |u+v|>½` at **0/1008, 0/10008, 0/100002**.

### Why this deflates rather than elevates

`(π_p) = π_p·ℤ[ω]` is **always** a scaled (`√p`) and rotated (`arg π_p`) copy of the
hexagonal lattice. So the domain is always a 60° rhombus of side `√p`, giving
`b² = p/4`, `a² = 3p/4` **by lattice geometry, not by the norm-band empirics** (v1
derived `b²=p/4` from the 3:16 ÷ 1/4 ratio — backwards; it was never in doubt).

**Consequence: every constant in v1's headline table is a shape constant of a rhombus.**
`½, ¾, 33, 33/34, 5/48, 17/48, 3/16, 1/4, 1/6, 3/4:1/8:1/8` hold for **any** p ≡ 1 mod 3,
**any** Eisenstein lattice, **any** CM curve. They carry **no information about
secp256k1**. v1's "universal ≈33 across all primes!" was not a discovery of universality
— it is universal because it was never about primes.

In coefficient coordinates the whole `3/4 : 1/8 : 1/8` ε-law is: *in the unit square
`[−½,½)²`, the band `|u+v| ≤ ½` has area 3/4 and the two corner triangles have area 1/8
each.* That is the entire content.

### v1's other error here

v1 wrote *"Int.1 VERIFIED → DERIVED"* for `½` and `¾`. **Wrong** — Int.1 already
attributed `¾` to the 60°-rhombus `√3:1` ratio and `½` to 120°-symmetry. They were
already derived. v1 re-derived them and claimed the promotion.

### What survives (honestly)

- The two-line **proof** (new, and it is a proof, not an empirical test).
- `33 = 11a²/b²`, `33/34`, `5/48`, `17/48`, axis = long diagonal — **new but inert**:
  exact shape constants with no arithmetic content.
- The **useful** consequence, stated as a *closure*: **any readout built from ε, the
  norm band, or the frame operator is a function of the lift coefficients `(u,v)` only,
  hence shape-determined and incapable of carrying arithmetic.** Those panels are closed
  **by proof** — not by declaration, not by a limited empirical test.
- **Where the arithmetic actually lives:** entirely in the *map* `x ↦ (u,v)` — the
  distribution of lift coefficients over curve points. Not in any shape observable
  computed from them. That is the correct redirect. (See §A2.)

---

## R3. RETRACTED — "A came back null and well-controlled" (it had ZERO power)

v1 §3 reported the 82 keys' cubic moment at rank-pct 0.333 vs control 0.427 ⇒ *"null,
well-controlled."* **A null with no power statement is near-vacuous, and this one was
worse than vacuous.**

`cubic_moment_power_v1.py` re-runs it on **both sets** (standing rule, violated in v1:
the 36k full-range known-d set `constructed_keys_fullrange_v1.npz` was sitting in the
directory and went unused while v1 hand-rolled a 9000-point pool), with the ranking done
in **exact Fraction** comparison (the statistic is ~1e227 — one order of magnitude from
overflowing a double; v1's float version had already emitted an overflow warning).

**Power — minimum injected coherent fraction `f` detectable at 80% power / 95% of null:**

| N | min detectable f | meaning |
|---|---|---|
| **82** | **1.0** | **every point must be perfectly aligned before the test notices** |
| 500 | 0.35 | |
| 2000 | 0.35 | |
| 10000 | 0.10 | |
| 36000 | 0.05 | ~1800 aligned points |

**At N=82 the test cannot detect anything short of total, perfect coherence.** v1
reported the absence of an effect the test was structurally incapable of seeing. The
set-mean cubic moment compresses N points into a single 2-vector and discards nearly
everything; it is a weak detector even at N=36000.

### R3a. Two "ANOMALY" flags in the re-run are my own tautologies

| row | S | rank | truth |
|---|---|---|---|
| 36k constructed (whole set) | **0.000e+00** | 0.000 "ANOMALY" | μ is *defined* as the mean of this set ⇒ `E−μ = 0` **identically** |
| 36k subset bitlen≥240 | 1.7e223 | 0.020 "ANOMALY" | 22000 of the same 36000 that define μ ⇒ not independent |

This is exactly the **residue-vs-component tautology** the memory warns against, and the
verdict function walked into it. Any set used to define the baseline cannot be tested
against it.

### R3b. Test A on the 82 was a generation-side test in disguise

`d` is known and `d ↦ x([d]G)` is deterministic, so *"are these 82 points atypical?"* can
only be interesting if the **d's** were special — which is the generation side we have
dropped (hard, repeated). The 82-key set test should not have been in a curve-side panel
at all. **The 36k cannot substitute as a rival hypothesis** either — they are our own
random keys; for this statistic they are a *null/control*, not a competing group. That is
the honest answer to *"why only the 82 and not the 36k?"*: the 36k belonged there as the
**null pool and power calibration** (which is what destroyed the test's credibility), not
as a second sample.

---

## A2. The well-posed curve-side replacement for A  [EXACT, full enumeration]

F's exact anchor (`Σ_{x∈F_p} z³ = 0`, since `z³` is odd and the field is `x→−x`-closed) is
the useful part of v1 and it survives. It hands over the properly-posed question — no keys
involved:

```
   E_curve[z³] ∝ Σ_x χ₂(x³+7)·z(x)³  =:  T(p)
```

(because `Σ_x z³ = 0` kills the trivial half of `(1+χ₂(x³+7))/2`). This is the
QR-restriction of the curve tested against the μ₃-invariant cubic — a genuine character
sum. Exact, full enumeration, no float in the signal path:

| p | \|T\| | \|T\|/p² | \|T\|/p^2.5 | verdict |
|---|---|---|---|---|
| 103 | 1.476e3 | 0.139 | 0.0137 | ~√-cancellation |
| 337 | 2.236e4 | 0.197 | 0.0107 | ~√-cancellation |
| 859 | 1.004e5 | 0.136 | 0.0046 | ~√-cancellation |
| 2221 | 1.113e5 | 0.023 | 0.0005 | ~√-cancellation |
| 6427 | 6.866e6 | 0.166 | 0.0021 | ~√-cancellation |
| 39979 | 1.018e8 | 0.064 | 0.0003 | ~√-cancellation |

`|T| ~ 0.1·p²` against a no-cancellation scale of `p^2.5`: **square-root cancellation,
generic Weil behaviour, across three orders of magnitude in p.** Not zero, not enhanced.

**Scope:** this is a real test with real power (exact, full enumeration) — unlike the
N=82 set test it replaces. It bounds *this* character sum at the generic scale; it does
not speak to bilinear/joint objects (closure's named complement).

---

## S. STATUS AFTER CORRECTIONS

| v1 claim | v2 status |
|---|---|
| χ₂ doubling transport law [PROVED] | **RETRACTED** → CITED (textbook duplication formula) |
| Cap Law [VERIFIED, top open = prove it] | **PROVED in 2 lines**, but **inert**: pure lattice geometry, zero arithmetic |
| 33, 33/34, 5/48, 17/48, long-diag axis [NEW] | true, new, **inert shape constants** |
| Int.1 ½, ¾ "VERIFIED → DERIVED" | **wrong** — Int.1 had already derived them |
| `b²=p/4` derived from the norm band | **backwards** — it is lattice geometry a priori |
| A: "null and well-controlled" | **RETRACTED** — zero power at N=82 (needs f=1.0) |
| A's ANOMALY rows | **tautologies** (baseline defined from the tested set) |
| G: null by scaling trend | **stands** (N=40000, controls fire, slope ≈ −1.2…−1.8) |
| F: exact anchor `Σz³ = 0` | **stands** — and it is what makes A2 well-posed |

**Net:** v1's genuinely useful residue is (i) F's exact anchor, (ii) the **proof** that
the ε/norm-band/frame-operator panel is shape-determined and therefore closed to
arithmetic, (iii) G's scoped null with proper scaling, (iv) A2's generic character-sum
scale. The rest was inflation.

---

## OPEN — re-ranked after corrections

1. **The map `x ↦ (u,v)`.** R2 proves all shape observables are inert, so the *only*
   place arithmetic can live on this object is the distribution of lift coefficients over
   curve points. A2 tests one 1-dimensional projection of it (`z³`) and finds the generic
   scale. The joint/2-D distribution is untouched.
2. **B — bilinear / joint-SET on the difference set** `{x([dᵢ−dⱼ]G)}`. Closure bounds
   single sums only; this is its own named complement. **Design note from R3:** use a
   per-point distribution statistic, not a set mean — a set mean has ~no power at N=82,
   and the difference set gives `82·81/2 = 3321` pairs, not 82.
3. **E — cross-domain bilinear moment over the amicable bridge** (`z_p` vs `z_n`).
   Disjoint construction ⇒ tautology-clean.
4. **G′ — widen the closure-blind corner** (`‖F‖_A ≳ √p` in general; other high-Wiener
   readouts, other additive targets `e_n(ad)`).

## Method rules earned this session (the expensive way)

- **A null needs a power number.** "Null, well-controlled" with no minimum-detectable-
  effect is not a result. Report `f_min` or don't report the null.
- **Never let the tested set define the baseline.** Tautology, guaranteed.
- **A universal constant across all primes is a red flag, not a trophy** — it usually
  means the object isn't about primes.
- **Verifying an identity your code already implements verifies your code**, not nature.
  Before calling an identity a finding, ask whether it is the textbook formula.
- **Run every test on BOTH sets** — the 36k is the power calibration that makes a small-N
  result interpretable, and it was ignored.
