# RESULT v2 — the μ₆ cover: the dichotomy is **FORCED**, and the discriminator is **χ₃(28)**

*2026-07-23. Supersedes `RESULT_mu6_cover_and_conductor_v1.md`, which is **superseded in §1 and carries
one refuted claim** (§0.2 below). §2 (conductor `f`) and §3 (harvested untested list) of v1 stand
unchanged and are not restated. Scripts: `scratchpad/mu6_derivation.py`, `secp_branch.py`.
Exact `ℤ[ζ₆]` / integer arithmetic; no float. No leakage, key-recovery or ECDLP claim.*

---

# 0. What changed, and what I got wrong

## 0.1 The headline

v1 §1.2 reported `N(S₁)/p ∈ {1,4}` at `93/93` and left the mechanism open, warning it "may be
classical … possibly FORCED ⇒ zero information." **That warning was correct.** The dichotomy is now
**derived from two textbook facts**, and the derivation also produces the discriminator that v1 left
unknown:

> **`N(S₁) = 4p` ⟺ `28` is a cubic residue mod `p`.**  Verified **206/206**, `p ≡ 1 mod 6`,
> `11 ≤ p ≤ 3000` — of which **113 primes are out-of-sample** relative to v1's `p ≤ 1200` scan.

## 0.2 ★ RETRACTED from v1 — and it pointed away from the answer

v1 §1.3 stated:

> *"Shape constraint on any future candidate, without fitting: the `4p` rate is `26/93 ≈ 0.28` — not
> `1/2`, `1/3`, or `1/6`. **A single quadratic or cubic residue condition cannot produce it.**"*

**FALSE.** It is exactly a single cubic residue condition. `26/93` against an expected `31 = 93/3` is
**1.1 standard deviations** (`σ = √(93·⅓·⅔) = 4.5`) — ordinary binomial noise, which I read as a shape
constraint. **Had a future session trusted that line it would have excluded the correct answer by
construction.** The failure mode is treating a small-sample rate as a structural invariant without
computing its sampling error. v1's other caveats (forced-ness, don't fit twice) were right and are
discharged here.

## 0.3 The literature question, answered honestly

You asked for a literature check first. **I did not run one — I derived the result instead**, which
settles the forced-ness question (the stated purpose) more completely than a search would, and yields
the discriminator as a by-product. **What is therefore still unchecked is priority, not correctness.**
Both inputs are textbook, so the composite statement is **unlikely to be novel** and should not be
presented as a discovery. Inputs used:

- **(i)** `|J(λ,μ)| = √p` whenever `λ`, `μ`, `λμ` are all nontrivial — classical.
- **(ii)** the **Hasse–Davenport product relation** `g(χ)·g(χρ) = χ̄(4)·g(χ²)·g(ρ)`, `ρ` the quadratic
  character — Berndt–Evans–Williams Thm 11.3.5 / Ireland–Rosen ch. 11. `[CITED — not verified against
  source; but step (D2) below is verified numerically 206/206, so the derivation does not rest on my
  recollection of the statement.]`

---

# 1. The derivation

`p ≡ 1 mod 6`, `p ≠ 7`. `χ₆` of exact order 6, `χ₃ = χ₆²`, `ρ = χ₂ = χ₆³`; `χ(0) := 0`.
`S₁ := Σ_{x∈F_p} χ₆(x³+7)`.

**(D1) Reduce the cubic to Jacobi sums.** As `x` runs over `F_p`, `#{x : x³ = u} = 1 + χ₃(u) + χ̄₃(u)`
for `u ≠ 0`. Summing, the two "trivial-character" contributions cancel exactly
(`χ₆(7) + Σ_{u≠0}χ₆(u+7) = χ₆(7) − χ₆(7) = 0`), leaving after `u = 7t` and `t ↦ −s`:
```
S₁ = χ₆(7) · [ χ₃(7)·J(χ₃,χ₆)  +  χ̄₃(7)·J(χ̄₃,χ₆) ]                 [VERIFIED 206/206, exact]
```

**(D2) The two Jacobi sums differ by a cube root of unity.** With `α₀ = J(χ₃,χ₆) = g(χ₃)g(χ₆)/g(ρ)`
and `β₀ = J(χ̄₃,χ₆) = g(χ̄₃)g(χ₆)/g(χ̄₆)` (note `χ₃χ₆ = ρ`, `χ̄₃χ₆ = χ̄₆`), Hasse–Davenport at `χ = χ₃`
gives `g(χ₃)g(χ̄₆) = χ₃(2)·g(χ̄₃)g(ρ)`, hence
```
β₀ / α₀ = χ̄₃(2)                                                      [VERIFIED 206/206, exact]
```

**(D3) The dichotomy.** The ratio of the two terms of (D1) is
```
r = [χ̄₃(7)β₀] / [χ₃(7)α₀] = χ₃(7)·χ̄₃(2) = χ₃(7)·χ₃(2)² = χ₃(28)        (28 = 4·7)
```
so `r ∈ μ₃`, and since `|α₀| = |β₀| = √p`,
```
N(S₁) = p · |1 + r|²  =  4p  if r = 1  (|1+1|² = 4)
                       =   p  if r = ζ₃^{±1}  (|1+ζ₃| = 1)
```
**∎ The dichotomy is forced; no third value is possible.**

## 1.1 Consequence for the evidential status of v1

`N(S₁)/p ∈ {1,4}` at `93/93` (v1) and `206/206` (here) is **FORCED** ⇒ **zero information as evidence**,
exactly as the drill protocol requires it be counted. Likewise the `206/206` on the discriminator is a
**check of my algebra**, not evidence about the curve. **The unforced content of this whole thread is
nil** — its value is that a well-posed open question is now closed by a proof rather than left for a
discriminator hunt that would have cost a pre-registration and a scan.

---

# 2. At secp — and the tie-in to a constant the record already uses

All exact, at the real 256-bit parameters. `p ≡ 1 mod 6` and `n ≡ 1 mod 6`, so `χ₆` exists over **both**
fields of the amicable pair.

| | `F_p` | `F_n` (amicable partner) |
|---|---|---|
| `28` a cubic residue | **YES** | **YES** |
| `7` a cubic residue | no | no |
| `2` a cubic residue | no | no |
| `[28/π]₆` | **`ζ₆³ = −1`** | **`ζ₆³ = −1`** |
| `[7/π]₆` | `ζ₆⁵` | `ζ₆` |
| **μ₆-cover branch** | **`N(S₁) = 4p`** | **`N(S₁) = 4n`** |

**The derivation is scale-free** — Hasse–Davenport and the Jacobi-sum modulus hold at every `p ≡ 1 mod 6`
— so **this row genuinely reaches `2²⁵⁶`**, unlike the `p ≤ 10⁵` measurements the scale banner governs.
That is rare in this record and is the reason to keep it.

**Cross-validation:** my independently computed `[7/π_p]₆ = ζ₆⁵` and `[7/π_n]₆ = ζ₆` **reproduce Part IV's
recorded values exactly**, at full scale — which validates the character normalisation used throughout §1.

**★ The shared constant.** Part IV records the flap classifier as **`ε = ζ₆^{3−[28/π]₆}`**, and
`secp256k1_arithmetic_v4` thread A records **`χ(π) = −(28/π)₆⁻¹`**. The μ₆-cover branch is governed by
**the cubic part of the sextic symbol of the same constant `28`**. So `28` now indexes **two** structures:
the flap classifier uses the **full sextic** symbol, the μ₆ cover uses its **cubic** part.
⚠ **This is a shared constant, not a proven relation between the two objects** — no derivation links
`ε` to `S₁` here, and none is claimed. Whether one exists is a well-posed new question.

**What `N(S₁) = 4p` means at secp `[DERIVED — UNVERIFIED]`:** `r = 1` makes the two Jacobi-sum
eigenvalues of the exact-order-6 eigenspace coincide up to unit, i.e. **the μ₆ cover's new dim-2 part has
a repeated Frobenius eigenvalue at secp**, so it is not simple. Contrast the μ₄ cover, which at secp
(`m = 1`, `[CONDITIONAL]`) **is** simple with `ℚ(π) = ℚ(√p, ω)` — see
`RESULT_anew_isogeny_type_correction_v1.md` §4. **The two covers land in opposite isogeny regimes at
secp.** Verify the repeated-eigenvalue reading before use.

---

# 3. What this leaves open

1. **Is there a relation between `ε` (flap) and `S₁` (μ₆ cover) beyond sharing `28`?** New, well-posed.
2. **`k = 3`** — `w³ = x³+7` is **genus 1**; its Jacobian is another elliptic curve attached to secp,
   still never computed. Cheapest remaining item in the cover family.
3. **`k = 8` (genus 7, new dim 4) and `k = 12`** — `k = 12` is where the μ₄ and μ₆ mechanisms meet, and
   is the only place they can interact. Untouched.
4. **Priority check** on §1 (and on v1 §2's conductor data) — not run.
5. v1 §2 (conductor `f = 3 · 79 · 349 · C112`, the volcano deformation family) and v1 §3 (the harvested
   untested list) — **unchanged and open**.

---

*Grades: §1 `[PROVED — UNREVIEWED]` (my derivation; every step independently verified numerically
206/206, but no adversarial pass) modulo the `[CITED]` Hasse–Davenport statement, which step D2's
206/206 numerical check independently corroborates. §2's table `[VERIFIED — exact, full 256-bit scale]`;
the isogeny reading `[DERIVED — UNVERIFIED]`. §0.2 is a retraction of v1 and must not be re-claimed.*
