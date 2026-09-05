# The Weil closure of the fixed-shift correlation hierarchy — and the scale frontier it leaves open

**Date:** 2026-07-31. **Grade: `[PROVED — Weil + bounded degree]` for §2; `[VERIFIED — exact]` for §4;
`[DERIVED]` for §1.** Recorded as a **recovery pass**: these items were generated in a structural
synthesis on 2026-07-31 and were not banked at the time — see §6.

**This is a closure claim, so it is stated at the closure-grade bar** (`btc_puzzle_investigation/
CLAUDE.md`; `feedback_closure_grade_2026_07_28`): object, class of observable, power, scope, in §2.
It does **not** claim an absence of structure; it claims a **magnitude bound on a named class**, and
§3 states what the bound does not reach.

---

## 1. The object, and why it is the only one `[DERIVED]`

The twisted-sum programme has a single underlying object:

> `c(d) = χ₂(y_{[d]G})`, a `±1` sequence on `ℤ/n`, with `V(a) = ĉ(a)`.

`c` is **odd** (`χ₂(−1) = −1` at `p ≡ 3 mod 4`) and **`μ₃`-invariant** (`[λ]P = (βx, y)` leaves `y`
fixed), so it is a signed function on `(ℤ/n)^×/μ₆` — `L = (n−1)/6` free values.

**Under the 120° law the char poly has ONE free coefficient, so every `V_k` is a polynomial in `V₁`.**
With `e₂ = e₁² + p`, `e₃ = χ₂(−1)p·e₁`, `e₄ = p²`, Newton gives (verified to `1e−47`, both branches):

| `χ₂(−1)` | `V₂` | `V₃` | `V₄` |
|---|---|---|---|
| `−1` | `V₁² + 2p` | `−2V₁³ − 6pV₁` | `V₁⁴ + 4pV₁² + 2p²` |
| `+1` | `V₁² − 2p` | `−2V₁³ + 6pV₁` | `V₁⁴ − 4pV₁² + 2p²` |

`V₂` is on file. **`V₃` and `V₄` are not, and they are testable** — `n1_twisted_eigenvalues_v1.sage`
measures `V₁..V₄` independently by point-counting over `E(F_{p^k})`. The ladder is graded: the `V₂`
identity tests `e₂` (the lock), `V₃` tests `e₃` (the closure **sign** — the D4 defect that once
produced a false null), `V₄` tests `e₄ = p²`. **Running it discharges the `C-FORCED` control the
`experiment-designer` gate has now flagged twice**, since the census route (`run_n1_120deg_v1.py`,
`verify_charpoly_collapse_v1.sage:78-79`) *derives* `e₃, e₄` rather than measuring them.

> **★ [CORRECTION to the record]** `btc_puzzle_INDEX.md` (2026-07-30, 3rd) states that resolving
> `θ_a` *"needs `p₃` = `E(F_{p³})` = `O(p³)`"*. **No extension field ever adds information**, at any
> level: every `p_k` is a polynomial in `e₁`, and the folding `θ ↦ 60°−θ` yields the *identical* root
> multiset (angles `{θ, θ+120, 180−θ, 60−θ}` are setwise invariant). `θ_a` was never an invariant;
> the invariant is `u(a) = V₁/(2i√p)`, and it is one real number.

### 1a. AUDITED SCOPE of that corollary — an earlier draft over-reached

An earlier revision added *"consequently every eigenvalue-level / **higher-moment** /
extension-field probe in the record was measuring `V₁` in disguise."* Audited against the record's
probe families, **the "higher-moment" half is false** and the claim splits:

| covered — **per-cell**, a function of `u(a)` alone | **NOT covered** — functions of the whole vector `{u(a)}`, `L = (n−1)/6` dof |
|---|---|
| purity `\|α\|=√p`; eigenvalue moduli and phases; `V₂`, `V₃`, `V₄`; the char poly; `g = deg gcd`; any `E(F_{p^k})` extension | monodromy `E[u²]`, `E[u⁴]`; spacing-KS, `Σ²`, small-ball, top-5, order statistics, `max\|u\|` saturation; additive/multiplicative autocorrelation, bispectrum, magnitude and signed spectra, multiplicativity; arrangement correlations |

The chirp / phase-family probes are outside both columns — `H(k,a) = Σ_d c(d)e_n(kd²+ad)` is a
`d`-side object whose `k=0` line is `V`; the collapse says nothing about `k ≠ 0`.

**The conclusion of the synthesis is unaffected and is in fact what this sharpens:** the per-cell
channel is exhausted by one real number, so **the only live channel is the arrangement across `a`** —
which is exactly where the record's untested objects (joint additive-multiplicative, short-scalar,
individual 4-point correlations at fixed shifts) sit.

## 2. ★ The closure `[PROVED — Weil + bounded degree]`

**Object.** Fixed-shift, fixed-order correlations of `c`:
`C_k(t₁,…,t_k) = Σ_{d∈ℤ/n} c(d)·c(d+t₁)···c(d+t_k)`.

**Mechanism.** `[d+t]G = [d]G + T`, and translation `τ_T` is an **automorphism of `E`**, so
`y ∘ τ_T` has the same degree as `y` (namely 3) **independently of `T`**. Hence
`y_P·y_{P+T₁}···y_{P+T_k}` is a rational function on `E` of degree `≤ 3(k+1)`, uniformly in the
shifts, and `C_k` is a complete character sum of a bounded-degree function on a curve.

> **`C_k(t₁,…,t_k) = O(k·√p)`, uniformly in the shifts, for all `p`, for every `k ≪ √p`.**

**Class closed.** Every fixed-shift correlation of every fixed order; equivalently the whole
**Gowers `U^s` hierarchy up to `s ≲ log√p`** (the `U^s` norm involves `2^s`-point correlations). Also
every index map induced by a curve endomorphism — `d ↦ md`, `d ↦ λd`, `d ↦ −d` — since those are
algebraic. Worked instance: `y_P·y_{2P} = (3x²/2)(x_P − x_{2P}) − (x³+B)`, a rational function of
`x_P` alone, so `Σ_d c(d)c(2d)` is a complete curve sum.

**POWER — and this is the load-bearing caveat.** The random level for these sums is `√p`; the bound
is `O(k√p)` with constant `~3k`. **The closure therefore excludes order-of-magnitude excess, NOT
fine structure.** A 12× excess in a 4-point correlation is excluded; a 3× excess is not. It is a
gross-scale bound that holds at *every* shift, and it is complementary to — not a substitute for —
the record's permutation tests, which probe the fine scale at limited power over few shifts.

**SCOPE.** Complete sums over all of `ℤ/n` only. Fixed `k` and fixed shifts. Says nothing about
incomplete sums, non-algebraic index maps, or `k` growing with `p`.

**Consistency check (not a discriminating one):** at `p = 127, 163, 211`, `max` over **all** shifts
of the 2-point correlation = 21, 23, 27 against the ceiling `6√p` = 66, 72, 84; sampled 4-point max
= 27, 29, 37 against `15√p`. Not violated. ⚠ The observed values also sit at the random level
(`≈ √(2n ln n)`), so this run does not distinguish the Weil mechanism from randomness — it only
fails to refute the bound.

## 3. What the closure does NOT reach — an enumeration, not a hand-wave

1. **Index maps arithmetic in the exponent** — `d ↦ d^{-1}`, `d ↦ d^k mod n`. These mix `ℤ/n`'s
   multiplicative structure with the curve's additive one; no cohomological machinery applies,
   because relating `[d²]G` or `[d^{-1}]G` to `[d]G` is the CDH / inversion problem, not ECDLP.
   **Design constraint, from `c` odd plus the need for a bijection:** `k` odd with
   `gcd(k, n−1) = 1`, and `6 | n−1` is forced, so `k ≡ ±1 mod 6`. **The admissible probe family is
   essentially one-parameter: `k ∈ {−1, 5, 7, 11, 13, …}`.** `k = −1` is canonical — and is
   independently the best-powered lens the record found (floor 0.25 vs the chirp's 0.5–1.0). *The
   classification predicts the empirical winner, which is the only corroboration it currently has.*
2. **Incomplete / short-interval sums.** Completing an interval sum costs `log p`, and the bound
   `O(√p log p)` **exceeds `|I|` outright** once `|I| ≲ √p` — at which point it says nothing at all.
3. **Order or degree growing with `p`.**

## 4. ⊘ RETRACTED — the "solved-key scale frontier" item

**An earlier revision of this file carried a §4 instantiating §3.2 on the bit-lengths of the 82
solved puzzle keys (81 of 82 below `√n = 2^128`). It is RETRACTED, on two independent grounds.**

1. **Scope violation.** It made the **solved key corpus** the object. That is the generation side,
   excluded by a standing project boundary (`btc_puzzle_investigation/CLAUDE.md` Scope;
   `feedback_no_prng_generation_side_2026_07_14`). The object of this project is curve arithmetic
   structure.
2. **It was wrong on its own terms, and wrong in the direction that matters.** The live target has
   bit-length 135, i.e. **above** `2^128`, and its interval `2^134` exceeds `√n·log n ≈ 2^131` — so
   by the very argument §4 advanced, the target sits where completion **does** work. The item was a
   closure with a positive's framing, aimed at the one case it purported to open. Retained here as
   a worked instance rather than deleted, because the failure is instructive: an
   out-of-scope object produced a conclusion pointing opposite to its own headline, and neither
   defect was visible from the headline.

**What survives is §3.2 alone, and it is a statement about the CURVE, with no key set in it:**

> Weil bounds **complete** character sums. For a sum restricted to an interval `I ⊂ ℤ/n`, completion
> costs `log p` and the bound `O(√p log p)` exceeds `|I|` outright once `|I| ≲ √p`, at which point it
> is vacuous. **Incomplete sums are outside the closure of §2**, as an arithmetic fact about the
> bound.

That fact is also why `E₃` (`|Σ_{i≠j} χ₃(X_i − X_j)|²/4`, a sum over 3321 differences rather than a
complete sum over `E(F_p)`) is not reached by §2 — a property of the **statistic's construction**,
not of any key set. See `CORRECTION_e3_cmvanishing_interaction_reading_v1.md`.

## 5. What this licenses, and what it does not

**Licenses:** concentrating probe design on §3's three survivors, and specifically the one-parameter
`d^k` family at the largest feasible `p` (the record's own power arithmetic already says the gain
comes from `n`, not from more primes: null grows `≈ 4 ln n`, full plant `0.16n`).

**Does NOT license:** any statement that the closed class is "dead" or "generic". A magnitude bound
at constant `3k` above random is a **bound**, and §2's POWER paragraph states exactly how coarse it
is. Nor does it license a security reading: the closure is about a specific readout `χ₂(y)` on a
specific sequence, not about ECDLP.

## 6. Provenance — why this file exists

These items were generated in a structural synthesis on 2026-07-31 and **were not banked**. Of six
substantial items produced in that pass, one (the cross-`j` discriminator) was followed and five were
left in conversation; four remained unrecorded through several subsequent turns of work. That is the
failure mode `SYNTHESIS_brainstorm_seven_cycles_ADDENDUM_1_v1.md` records verbatim — *"the losses
were NOT random: what survived had a crisp verdict attached; what died was open-ended and
cross-referential"* — reproduced in the same session in which that document was reviewed.

**Still unbanked as of this file** (recorded so the next pass can find them): the `F_{p³}`
perfect-square prediction and the duality `W^∨(1) ≅ W⊗ξ`, both asserted from the `W ⊕ W⊗ξ`
hypothesis and **never checked**; and the small-cofactor **range-extension** claim (order-`h`
characters are polylog-evaluable, giving the 120° law at `p ≈ 10⁴–10⁵` against 547 today), which is
untested and which `PREREG_jclass_120deg_discriminator_v2.md` does **not** use — v2 uses small
cofactor for arm construction only. The two were asserted to be "one repair"; they are not.
