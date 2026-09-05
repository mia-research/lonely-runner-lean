# RESULT — D1: the non-homomorphic lift into the supersingular Prym carries no affine structure

**Date 2026-07-19.** Tests the lever candidate mapped in `RESULT_supersingular_cover_lever_v1.md` §4 (D1).
Scripts: `d1_fast_affine_v1.py` (+ p=67, p=79 variants), logs alongside. Exact divisor arithmetic over
`F_p`; principality of a degree-0 divisor via Riemann–Roch (`dim L(D) ≥ 1`). No floats anywhere.

## The question and why this test decides it
`A_new` = Prym of `C:w⁴=x³+7 → E:y²=x³+7` is **supersingular at secp** with small embedding degree, so its
internal DLP is subexponential. The lever needs a map carrying `d` into it. `Hom(E,A_new)=0` `[PROVED]`
kills the homomorphic route, leaving the **non-homomorphic lift** `Q(P)=[P⁺−P⁻]`, `P^± =(x_P,±√y_P)`.
A usable transfer requires `ℓ(d)=dlog_{A_new}(Q([d]G))` to be **affine in d** — equivalently, for every
arithmetic triple `d₁+d₃=2d₂`: `Q(d₁)+Q(d₃)−2Q(d₂) ~ 0`. That is one principality test per triple, and it
decides the lever condition **without computing any discrete log**.

## Result — controls fired, affine structure absent

| p | n=#E | liftable d (y_P a QR) | `2Q~0` | `3Q~0` | additivity `Q(a)+Q(b)=Q(a+b)` | **AFFINE** |
|---:|---:|---|---:|---:|---:|---:|
| 43 | 31 | 15/30 | 0/15 | 0/15 | **0/48** | **0/22** |
| 67 | 79 | 39/78 | 0/39 | 0/39 | **0/363** | **0/189** |
| 79 | 67 | 33/66 | 0/33 | 0/33 | **0/255** | **0/128** |

**Controls (fired at all three p):** `div(f)` principal = **True** (the test detects principal divisors);
`Q(d₀)` principal = **False** (the lift is non-trivial — a genuinely nonzero class in `A_new`).

**Positive structure recorded, not glossed:** the lift is **non-degenerate** — exactly half of `E(F_p)∖O`
lifts (forced by `χ₂(−1)=−1` at `p≡3 mod 4`, so exactly one of `±P` is rational on `C`), and `Q(d)` lands
on **high-order** elements (`2Q,3Q ≠ 0` at every tested `d`), not collapsed torsion.

**But:** `0/666` additivity and `0/339` affine triples. `ℓ(d)` is **not affine**, and the lift is
**not** a homomorphism — an independent empirical confirmation of `Hom(E,A_new)=0`, which is a theorem
valid **at secp**, not a small-`p` artifact.

## What this closes, and its exact scope
- **Closed (with evidence + fired controls):** the **D1 route** — the supersingular factor `A_new` is not
  reachable through the lift `Q=[P⁺−P⁻]` by an affine/homomorphic transfer. Computing the (easy) discrete
  log in `A_new` therefore returns `ℓ(d)` with no affine handle on `d`; inverting it is not cheaper than
  the original DLP. **`[EMPIRICAL, p∈{43,67,79}]` + `[PROVED]` Hom=0 (secp-valid).**
- **NOT closed:** **D2**, the Lang-torsor twist bridge (does the exact `√p·ζ` rigidity survive
  `L_{χ₂(y)}⊗L_{χ_a}`, giving `V(a)` exact algebraic values structured in `a`) — untouched by this test.
  Nor does it exclude a *non-affine but still efficiently invertible* `ℓ`, though affine is the form a
  transfer needs. Nor other correspondences (e.g. §X.3 amicable).
- **Unchanged and still real:** `A_new` supersingular at secp with small embedding degree, exact `√p·ζ`
  eigenvalues. That structural fact stands; what fails is *this* route from it to `d`.

## Bearing on puzzle 135
**No help.** The transfer this route would have supplied does not exist. Puzzle 135's `2^134` keyspace is
unaffected; the leading zeros of a 135-bit scalar are already fully exploited by interval methods
(Pollard kangaroo, `~2^67.5` group ops).

### ⚠ TWO CORRECTIONS to claims made earlier in this session (both were mine, both tested and wrong)

**C1 — "the DLP inside `A_new` is cheap" is NOT established, and is likely no gain.** Even granting a
transfer, the payoff is an `F_{p³}` DLP at `p≈2²⁵⁶` (field size `2⁷⁶⁸`):
`general NFS L[1/3,(64/9)^{1/3}] = 2^76.5` — **worse** than kangaroo's `2^67.5`; optimistic tower/SNFS
`L[1/3,1.526] = 2^60.7` — better by only ~`2^7`. **And the interval is destroyed:** kangaroo's `2^67.5`
comes from `d` lying in a 135-bit window; a transfer sends `d ↦ ℓ(d)` with no short-window image, so the
transferred problem is a *full-range* DLP. Separately, a computable non-degenerate pairing on a **Prym**
(not a Jacobian with an explicit model) was assumed, never implemented or verified. `[ASSERTED → withdrawn]`

**C2 — the "`√6` endomorphism speedup applies to kangaroo on 135" is FALSE.** Measured: of 100000 random
`d ∈ [2¹³⁴,2¹³⁵)`, the GLV image `λ·d mod n` lands back in the interval **0 times** (expected `≈1.9e−37`).
The `μ₆`/GLV orbit reduction **does not preserve a short interval**, so it cannot be used for interval
DLP. `√6` is the speedup for Pollard **rho on the full group**, not for kangaroo. The correct available
gain for an interval is `≈√2`, via **recentering** the interval symmetrically about 0 so the *negation*
map preserves it (Galbraith–Ruprai, PKC 2010, ~1.36× measured). `[ASSERTED → corrected]`

## Process note
This route was pursued *because* the user rejected an earlier dismissal of "just supersingularity."
That rejection was correct: the dismissal was unearned, the object is real and secp-relevant, and only
running the test produced evidence. The test came back negative for D1 — which is a result, not a
retro-justification of the dismissal. The order of operations matters: **build and test, then conclude.**
