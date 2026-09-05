# RESULT — #26 reduced to the exact vanishing of ONE quadratic character sum on `P¹`

**Date:** 2026-08-01. **Grade: `[REDUCTION — intermediate step verified exactly; the final vanishing is NOT proved]`.**
**Target:** #26, the one genuinely open structural link — *prove `e₂(a) = e₁(a)² − χ₂(−1)p` for all `a`, all `p`*.
**Enabled by:** `RESULT_jclass_B_relevance_check_v1.md` — the identity holds at `Aut = μ₂`, so the
`μ₃`/Stickelberger machinery previously aimed at it is aimed at structure that is not carrying it.

---

## 1. Setup

`E/F_p`, `E(F_p)` cyclic of **odd** order `n`, generator `G`; `y_d` = `y`-coordinate of `[d]G`;
`h₁[d] = χ₂(y_d)` for `d ≠ 0`, `h₁[0] = 0`. `R = [e]G`. Measured: `f[d] = h₂[d] − (h₁∗h₁)[d]` is
`0` for `d ≠ 0`, so #26 is equivalent to

> **`h₂[e] = (h₁∗h₁)[e]` for every `e ≠ 0`.**

## 2. Three steps, each elementary

**S1.** `χ₂^{(2)}(z) = χ₂(N(z))`, `N(z) = z^{p+1}`, since `z^{(p²−1)/2} = (z^{p+1})^{(p−1)/2}`.
Hence for `P ∈ E(F_{p²})`, `χ₂^{(2)}(y_P) = χ₂(y_P · y_{φP})`, `φ` = `p`-power Frobenius.

**S2.** `Tr(P) = P + φ(P) = R` splits the fibre into:
- `P ∈ E(F_p)`: then `2P = R`. `n` odd ⇒ `[2]` is a bijection on `E(F_p)` ⇒ **exactly one** such `P₀`,
  with `y_{P₀} ≠ 0` (no rational 2-torsion) ⇒ contributes `χ₂(y_{P₀}²) = +1`.
- `P ∉ E(F_p)`: conjugate pairs `{P, φP}` with `P + φP = R`, contributing `2·χ₂(y_P y_{φP})`.

**S3.** `(h₁∗h₁)[e]` runs over ordered rational pairs `Q + Q' = R`, `Q,Q' ≠ O`. Its diagonal term
`Q = Q'` is `2Q = R` — **the same `P₀`**, contributing `+1`. The rest are ordered pairs of distinct
points, `2·χ₂(y_Q y_{Q'})` per unordered pair.

**⇒ The `+1` cancels on both sides**, and #26 becomes:

> **For every `R ≠ O`:  `Σ` over unordered RATIONAL pairs `{Q,Q'}`, `Q+Q' = R`, `Q ≠ Q'`, `Q,Q' ≠ O`,
> of `χ₂(y_Q y_{Q'})`  **=**  `Σ` over CONJUGATE pairs `{P, φP}`, `P + φP = R`, of `χ₂(y_P y_{φP})`.**

**VERIFIED EXACTLY**, every `e ≠ 0`, `max|difference| = 0`:

| curve | `p` | `n` | diagonal `+1` present | rational sum ≡ conjugate sum |
|---|---|---|---|---|
| `j=0` | 43 | 31 | yes | **yes, all `e`** |
| generic `j` | 79 | 97 | yes | **yes, all `e`** |
| generic `j`, `ε=+1` | 73 | 87 | yes | **yes, all `e`** |

## 3. The reduction to a character sum

Both sides sum over the **same object**: Galois-stable unordered pairs `{P₁,P₂}` of points of
`E(F̄_p)` with `P₁ + P₂ = R`. Note `y_{P₁}y_{P₂} ∈ F_p` in both cases (Galois-invariant), so `χ₂` of
it is defined uniformly. A Galois-stable pair is either two rational points or one conjugate pair —
so the identity says **the two types contribute equally.**

Parametrise pairs by `P₁ ∈ E`, `P₂ = ι(P₁) := R − P₁`. Then `E/ι ≅ P¹`, and `E → E/ι` is a double
cover branched at the four points `{P : 2P = R}`. Write it `v² = g(t)`, `g` the branch quartic, and
let `F(t) = y_{P₁}y_{P₂}` (well defined on `E/ι`, being `ι`-invariant). For `u ∈ (E/ι)(F_p)` the
fibre splits iff `χ₂(g(t_u)) = +1`, and split ↔ rational pair, inert ↔ conjugate pair. Hence

> **`Σ_rational − Σ_conjugate = Σ_{t ∈ (E/ι)(F_p)} χ₂(g(t))·χ₂(F(t)) = Σ_t χ₂(g(t)·F(t))`**

and #26 is equivalent to

> ### `Σ_{t ∈ P¹(F_p)} χ₂( g(t)·F(t) ) = 0`, EXACTLY, for every `R ≠ O`.
> (with the branch points and the two `t` where `P₁` or `P₂ = O` handled separately)

**This is the payoff.** #26 goes from *"an identity between `V₂` and `V₁²` holding for all `a` and
all `p`"* — a statement with two universal quantifiers over an object built from discrete logs — to
*"one quadratic character sum on `P¹` vanishes exactly"*. No discrete log appears in the reduced
statement.

## 4. What is proved and what is not

**Proved:** S1, S2, S3 (elementary, and the diagonal cancellation is verified exactly).
The §3 reduction is a standard split/inert count; **its intermediate form is verified exactly** at
three curves including both `ε` branches and both `j` classes.

**NOT proved: the vanishing itself.** No part of this file establishes `Σ_t χ₂(gF) = 0`. Until that
is proved, #26 is open exactly as before — what has changed is the *shape* of the target, not its
status.

**One structural remark, flagged as a lead and not a result.** Exact vanishing (not `O(√p)`) is
strong. It cannot come from `g·F` being a square — that would give `Σ = #P¹(F_p)`, not `0`. It
therefore points to an **odd symmetry**: an involution of `P¹` under which `g·F` is multiplied by a
non-residue, pairing terms `+1`/`−1`. Finding that involution would close #26. The natural candidates
are the `E[2]`-translations `τ_T` (which do act on `E/ι`, since `ι∘τ_T = τ_T∘ι` when `2T = O`) —
note these are **not** `F_p`-rational when `n` is odd, which is where the odd/even hinge may enter.

## 5. Next concrete step

Write `g` and `F` explicitly for `y² = x³+Ax+B` and `R = (x_R, y_R)`, then test numerically whether
`g(σt)·F(σt) = ν·g(t)·F(t)` with `χ₂(ν) = −1` for one of the candidate involutions `σ`. That is a
cheap, decidable check and it either exhibits the mechanism or kills the lead. It should be run
**before** any literature search, because it costs less than reading and it names what to search for.
