# RESULT — the m-law reduces to a single Jacobi sum (v1)

**Date:** 2026-07-20
**Object:** `m = b₂/p`, the integer naming all four Frobenius eigenvalues of `A_new`
(`char(t) = t⁴ + m·p·t² + p²` at `p ≡ 3 mod 4`).
**Predecessor:** `secp_mu4_eigenvalue_individual_2026_07_20` — the `[EMPIRICAL]` law over
26 primes in `200<p<500`, whose recorded upgrade path was: *"evaluate
`S = Σ_{x∈F_{p²}} χ₄(x³+B)` in closed form (Jacobi sum, j=0)."* This file executes that step.
**Artifacts:** `jacobi_closed_form_m_law_v1.sage` / `.log`, `m_branch_secp_v1.py`.

---

## 1. The reduction `[PROVED]` (algebra, corroborated exactly by §3)

Let `q = p²`, `p ≡ 7 mod 12` (so `p ≡ 3 mod 4` and `p ≡ 1 mod 3`), `B ∈ F_p^*`.

Cubing is 3-to-1 on `F_q^*` (`3 | q−1`), so `#{x : x³ = u} = 1 + χ₃(u) + χ̄₃(u)`. Hence

```
S = Σ_{x∈F_q} χ₄(x³+B)
  = Σ_u χ₄(u+B)  +  Σ_u χ₃(u)χ₄(u+B)  +  Σ_u χ̄₃(u)χ₄(u+B)
```

The first term is a nontrivial character summed over all of `F_q`, hence `0`.

**Two facts specific to `p ≡ 3 mod 4`, `p ≡ 1 mod 3`:**

- **(F1) `χ₄` is trivial on `F_p^*`.** `(q−1)/4 = (p−1)·(p+1)/4` and `4 | (p+1)`, so for
  `B ∈ F_p^*`, `χ₄(B) = B^{(p−1)·(p+1)/4} = 1`. *The quartic character of `B` drops out entirely.*
- **(F2) `χ₃|_{F_p^*}` is the square of the `F_p` cubic character.** `χ₃` is the norm-lift
  `χ₃'∘N` (`N(x)=x^{p+1}`, and `N(x)=x²` on `F_p`), so `χ₃(B) = χ₃'(B)²`. In particular
  **`χ₃(B) = 1` iff `B` is a cubic residue mod `p`**, else `χ₃(B)` is a primitive cube root.

Substituting `u = −Bt` (a bijection; `χ₃(−1)=1` since `3∤2`) and applying (F1):

```
Σ_u χ₃(u)χ₄(u+B) = χ₃(B) · Σ_t χ₃(t)χ₄(1−t) = χ₃(B) · J(χ₃,χ₄)
```

giving the closed form

```
        S = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)                     (★)
```

**Consequence.** If `J(χ₃,χ₄) = −p` (real), then `S = −p·(χ₃(B) + χ̄₃(B))` and:

| `B` mod `p` | `χ₃(B)` | `χ₃(B)+χ̄₃(B)` | `S` | `m = Re(S)/p` |
|---|---|---|---|---|
| cubic residue | `1` | `2` | `−2p` | **`−2`** |
| cubic non-residue | `ω` (primitive) | `ω+ω̄ = −1` | `+p` | **`+1`** |

**This is exactly the measured law, both branches.** The `B`-dependence enters through
`χ₃(B)` and nothing else — which *explains* the predecessor's key observation that the law is
carried by **within-prime** discrimination (the three `B` disagreeing at the same `p`): the
cubic-residue symbol is the only `B`-input the closed form admits. That is a named mechanism,
not a fit.

## 2. What the law now rests on — one claim

```
        J(χ₃,χ₄) = −p        for  p ≡ 7 mod 12,  over F_{p²}
```

Structurally this is a Jacobi sum of a **norm-lifted cubic character** (F2) against a character
**trivial on the subfield** (F1) — the regime where Hasse–Davenport plus the standard evaluation
of subfield-trivial Gauss sums applies. `|J| = √q = p` is automatic; the content is that `J` is
real and negative.

**Grade: `[EMPIRICAL 6/6]` of a classical-type identity, NOT yet proved here.** Closing it is a
short Gauss-sum derivation, and it is the only remaining gap between the `[EMPIRICAL]` m-law
and a scale-free statement.

## 3. Verification (exact, `jacobi_closed_form_m_law_v1.log`)

Characters built from discrete logs in `F_{p²}^*`; values as exact `CyclotomicField(12)`
elements; sums exact. No floats in the signal path (the only float is the final `Re(S)/p`
display, cross-checked against the exact integer `S`).

- `J(χ₃,χ₄) = −p` **exactly** at `p = 7, 19, 31, 43, 67, 79` (6/6).
- `S` is an **exact rational integer** in every case — `Im(S) = 0`, never an off-branch value.
- `S ∈ {−2p, +p}` matching the cubic-residue branch of (★): **17/17** `(p,B)` configurations,
  `B ∈ {7,2,11}`.
- Within-prime discrimination reproduced: `p=19,31,43` have the three `B` disagreeing and the
  cubic symbol picks the split; `p=67,79` have all three `B` non-residues (no discrimination
  available there), consistent.

## 4. Why this would reach `2²⁵⁶` — and what it is not

**The bridge.** Every input to (★) is `p mod 12` and one cubic-residue symbol. **Neither grows
with `p`.** If §2 is proved, the m-law is scale-free and applies at
`p = 2²⁵⁶−2³²−977` directly — no extrapolation, no prime ladder, and §11-style power arguments
become irrelevant because nothing is being estimated.

**The secp branch (`m_branch_secp_v1.py`, exact):** `p mod 12 = 7`, `p mod 4 = 3`, `p mod 3 = 1`;
and `7^((p−1)/3) mod p ≠ 1`, so **`B = 7` is a cubic NON-residue mod `p`**. Under (★) with §2,
this gives **`m = 1`** at secp — i.e. `π⁶ = p³`, eigenvalues `√p·{±ζ₁₂, ±ζ₁₂⁵}`, `k(m) = 6`.

> **Status of that number.** It is `[CONDITIONAL on §2]`. Proving §2 promotes it to `[PROVED]`.
> Until then it is *not* an established fact about secp — it is the value the closed form
> predicts. The predecessor memory's hard-scope line ("says nothing about `m` at `2²⁵⁶`")
> remains correct as of this file; §2 is precisely what would retire it.

**What this is NOT.** This pins the Frobenius eigenvalues of `A_new` at secp. It is a structural
fact about a supersingular abelian surface. **It carries no ECDLP or security claim of any
kind, and no bit of any scalar `d` is extracted or approached by it.** In particular it does not
interact with the D1 lift's measured non-additivity (`0/48` raw, `0/22` affine,
`d1_fast_affine_v1.log`): naming the eigenvalues of the target of a lift says nothing about
whether the lift transports a discrete logarithm, and the transfer question is settled
separately and negatively at the level tested.

## 5. Next

1. **Prove §2** (Gauss sums + Hasse–Davenport + subfield-trivial evaluation). Single named gap.
2. Out-of-sample the closed form at `p ≡ 11 mod 12` — (★) predicts `S` there via the same route
   and the predecessor measured `m = 2` (42/42); the derivation should reproduce it or fail
   visibly. **A falsification arm, run before any promotion.**
3. Only after 1–2: `compile-diff` before this touches any master document.
