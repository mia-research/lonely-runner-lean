# `V(a)` as the `A_new` channel — route status after the exact run (v3)

*2026-07-27. Analysis update. Supersedes `..._v2.md` on the points below; §§1–5 of v2 stand unchanged
except where flagged. No leakage or ECDLP claim. New grades: `[PROVED-exact]` = exact identity at
stated cells (from `RESULT_n1_120deg_exact_v1.md`); `[CONFIRMED]` = verified this session by an exact
computation.*

> **What changed from v2.** (1) The premise is now **proved exactly** at 22 primes (`g=2`), which
> **re-scopes the whole route**: the ideal equality `(α₁)=(α₂)` no longer needs establishing per-cell —
> it *follows* from the proved `u=ζ₃`. Stickelberger's job narrows to **uniformity**. (2) The `[REV
> §4b]` ω-descent lead is **confirmed exactly** but shown **insufficient** for order-pinning — it is a
> compatible symmetry, not the lever. (3) The forced relation A6 is corrected: `e₃ = χ₂(−1)·p·e₁`
> (sign is `p mod 4`-dependent; v2/prereg had `−p·e₁`, true only for `p≡3 mod4`).

---

## §1 — The premise is now an exact theorem at the tested cells

From `RESULT_n1_120deg_exact_v1.md`: `g(p,a) = deg gcd(L*(T), L*(ζ₃T)) = 2` at **every** census-surviving
cell of **22 primes** (7 in-sample + 10 out-of-sample stratum-S `p≡7 mod12` + 5 stratum-C `p≡1 mod12`),
by exact no-float multi-modular computation, controls all firing.

> **`[PROVED-exact]` at those cells: `α₂/α₁ = ζ₃` exactly.** Equivalently the eigenvalue multiset is
> `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` (`p≡3 mod4`) or its `α↦ᾱ` analogue (`p≡1 mod4`).

**Consequence that re-scopes the route (v2 §4–§7):** since `ζ₃` is a **unit**, `α₂ = ζ₃α₁` gives
`(α₂) = (α₁)` **immediately**. So at every tested cell the ideal equality `(α₁)=(α₂)` — the hypothesis
S5 that carried the whole Kronecker chain in v2 — **holds, as a consequence of the run**, not as an
open assumption. The v2 chain `S5→S6→S7` (ideal equality ⇒ unit ⇒ Kronecker ⇒ root of unity) is
**confirmed downstream** at these cells; the order is even pinned (`=3`) there, directly.

**Therefore the ONLY remaining gap is uniformity:** prove `α₂/α₁ = ζ₃` for **all** `a` and **all** `p`
(eventually secp), not just the 22 tested primes. Everything else in the per-cell chain is now either
proved or a consequence.

---

## §2 — `[CONFIRMED]` The ω-descent (`[REV §4b]`), and why it is NOT the uniformity lever

**Confirmed exactly** (`characterize_n1_v1.py`, exact mod-ℓ coefficient equality, `p =
13,43,67,127,823,1051`):

> **`L*(a) = L*(λa)` for `λ` = the order-3 element of `(ℤ/n)*`** (the action of `ω:(x,y)↦(ζ₃x,y)`,
> which is an `F_p`-automorphism of `E` since `p≡1 mod3`, `j=0`).

Derivation (now rigorous, not a lead): `σ_λ : ζ_n ↦ ζ_n^λ` satisfies `σ_λ(V_m(a)) = V_m(λa)`, and the
ω-descent gives `V_m(λa) = V_m(a)`, so `σ_λ(V_m(a)) = V_m(a)`. Hence every power sum, hence every
`e_k(a)`, lies in `Fix(σ_λ) = ℚ(ζ_n)^{⟨σ_λ⟩}`:

> **`L*(a)` is defined over the index-3 subfield `ℚ(ζ_n)^{⟨σ_λ⟩} ⊂ ℚ(ζ_n)`.**

⚠ **But this does NOT force order-3, and I am retracting the v2 framing that called §4b "the most
likely source of the second input."** `σ_λ` **preserves** the ratio `α₂/α₁` (it is a field
automorphism fixing the coefficients, so it permutes the eigenvalues; a permutation cannot manufacture
the value `ζ₃`). The descent tells us *where* a `ζ₃` is compatible with living — it explains the natural
3-structure of the field — but it is a **symmetry the answer has, not a constraint that produces it**.
§4b is **necessary context, not the lever.** *(This is the same category error as the retracted §3
mechanisms — a group action relating cells, mistaken for a within-cell forcing. Logged so it is not
reached for a third time.)*

---

## §3 — `ζ₃ ∈` splitting field: `[CONFIRMED]` as a consequence

`g=2` gives two roots `β, β'` of `L*` with `β' = ζ₃β`, both in the splitting field, so
`ζ₃ = β'/β ∈` splitting field. And `ζ₃ ∉ ℚ(ζ_n)` (n prime, `n≡1 mod3` forced ⇒ `3∤n` ⇒ `ζ₃∉ℚ(ζ_n)`).

> **⇒ the splitting field of `L*` strictly contains `ℚ(ζ_n)`, and contains `ℚ(ζ_n, ζ₃) = ℚ(ζ_{3n})`.**

This was offered in v2 §6 as a forced instrument check; it is now **implied by the proved `g=2`**, so it
is automatically satisfied at the 22 tested primes (it is not an independent test). It remains a valid
necessary condition for any *untested* prime.

---

## §4 — The uniformity gap, stated precisely, and the two candidate levers

**Open, uniform statement to prove:** `α₂/α₁ = ζ₃` for all `a ∈ (ℤ/n)*`, all `p≡7 mod12` (⊇ secp).

Two candidate levers, in priority order:

**(L-Stick) Stickelberger on the Jacobi/Gauss-sum structure.** The route's premise (v2 §5): the
Frobenius eigenvalues on this Kummer-type sheaf **are** Gauss/Jacobi sums, whose exact prime
factorization Stickelberger supplies — giving `(α₁)=(α₂)` and the μ₁₂-order **uniformly**. Status of the
premise: **anchored at `a=0`** — there `A_new` is supersingular and the eigenvalues are `√p × μ₁₂` roots
of unity, the Jacobi/Gauss-sum values Stickelberger factorizes `[CITED; record L3, ℚ(ζ₁₂)]`. For `a≠0`
the twist by the Lang torsor `L_{χ_a}` deforms these; whether the deformed eigenvalues remain
Jacobi-sum-shaped (so Stickelberger still applies) is the **premise that must be verified before the
citation is used** — and is the precise question now sent to `citation-verifier`. **Do not move any
grade on L-Stick until both (i) the citation is verified for `m=12` (not a prime power), `f=2`, and
(ii) the `a≠0` eigenvalues are shown to be the sums Stickelberger governs.**

**(L-mono) Geometric monodromy.** Independent of Stickelberger: show the sheaf
`L_{χ₂(y)} ⊗ L_{χ_a}` has a `μ₃` in its arithmetic/geometric monodromy that acts on `H¹_c` with the
`ζ₃`-ratio as an eigenvalue relation. This is the honest home of a *within-cell* `ζ₃` (the thing §4b is
not). Not yet attempted; flagged as the alternative if L-Stick's premise fails for `a≠0`.

---

## §5 — What is proved, what is not (updated ledger)

**Proved / confirmed this session:**
- `[PROVED-exact]` `α₂/α₁ = ζ₃` at 22 primes × all cells (`RESULT_..._v1.md`); hence `(α₁)=(α₂)` and
  order-3 **at those cells**.
- `[CONFIRMED]` ω-descent `L*(a)=L*(λa)`; `L*` over the index-3 subfield `ℚ(ζ_n)^{⟨σ_λ⟩}`.
- `[CONFIRMED]` `ζ₃ ∈` splitting field (consequence of `g=2`).
- `[CONFIRMED-independent]` the forced signs: `e₄=p²`, `e₃=χ₂(−1)·p·e₁` (Sage `V₁..V₄`, `verify_e3_sign.sage`).

**Not proved (unchanged in kind from v2 §8, re-scoped):**
- **The cap `|V|≤2√p`** — still needs purity-at-every-embedding (A3, `[CITED]`, untested) plus the
  uniform `u=ζ₃`.
- **Uniform `u=ζ₃`** (all `a,p`) — the sole remaining structural gap (§4). Per-cell is proved; uniform
  is not, and no finite sweep gives it.
- **Stickelberger** — citation unverified; **and** its premise for `a≠0` unverified (§4 L-Stick).
- **secp scale** — banner #5; every cell is `p≈10³`.

**Retracted from v2:** the framing of `[REV §4b]` as "the most likely source of the second input"
(§2 above — it is confirmed but insufficient).
