# RESULT — the Jacobi sign law: `p≡2 mod 3` PROVED; `p≡1 mod 3` proved REAL, sign reduced to one square root (v1, 2026-07-23)

**Target:** the `[EMPIRICAL 12/12]` gap of `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` §A2.2 — the single
identity on which `m = 1` at secp256k1 is `[CONDITIONAL]`.
**Verification:** `jacobi_sign_law_proof_v1.py` — exact `Z[ζ₁₂]` arithmetic (integer vectors mod
`z⁴−z²+1`), no floating point. **27 primes: the 12 in-sample + 15 fresh, 0 disagreements.**

Setting throughout: `q = p²`, `p ≡ 3 mod 4`, `χ₃`/`χ₄` of orders 3/4 on `F_q^*`,
`J = J(χ₃,χ₄) = g(χ₃)g(χ₄)/g(χ₃χ₄)` (valid: `χ₃χ₄` has order 12, nontrivial). `|J| = √q = p` is
automatic; the content is that `J` is **real**, with sign set by `p mod 3`.

---

## 1. `p ≡ 2 mod 3` — **PROVED**, no gap remains `[PROVED — UNREVIEWED]`

`p ≡ 3 mod 4` and `p ≡ 2 mod 3` ⟺ `p ≡ 11 mod 12` ⟺ **`12 | p+1`**. Hence **all three** characters
`χ₃` (`N=3`), `χ₄` (`N=4`), `χ₃χ₄` (`N=12`) have order `N | p+1`, i.e. `p ≡ −1 mod N` — the
**semi-primitive** (uniform-cyclotomy) case, where the Gauss sum is explicitly evaluable:

```
g(χ) = (−1)^((p+1)/N) · p            [Berndt–Evans–Williams Thm 11.6.3, s = 1]
```

Write `p + 1 = 12k`. Then

```
J = g(χ₃)g(χ₄)/g(χ₃χ₄) = (−1)^E · p ,   E = (p+1)/3 + (p+1)/4 − (p+1)/12 = 4k + 3k − k = 6k
```

`E = 6k` is **even for every `k`**, so **`J = +p`**. ∎

No sign ambiguity, no case analysis, no fitted constant. Verified `E` even and `J = +p` at
`p = 11,23,47,59,71,83` (seen) and `107,131,167,179,191,227,239` (fresh).

---

## 2. `p ≡ 1 mod 3` — `J` is a **rational integer `±p`** `[PROVED — UNREVIEWED]`

This closes the step the ledger records as *"rationality would additionally need `σ₅`-invariance —
observed numerically, **not derived**."* It is derived here. `p ≡ 7 mod 12`, so `4 | p+1` but `3 ∤ p+1`.

**(a) `χ₄` and `ρ := χ₄²` are semi-primitive.** `g(χ₄) = (−1)^{(p+1)/4} p`; `g(ρ) = (−1)^{(p+1)/2} p
= +p` (as `4 | p+1` makes `(p+1)/2` even).

**(b) `χ₃` is a norm-lift — and this is now proved, not asserted.** Since `3 | p−1`, `χ₃^p = χ₃`, i.e.
`χ₃` is Frobenius-invariant; the Frobenius-invariant characters of `F_q^*` are exactly the lifts
`χ'∘N`. So `χ₃ = χ'∘N` with `χ'` cubic on `F_p^*`. *(This retires the §A2.2 source-flagged defect A3,
"the norm-lift step was asserted, not checked".)* For `u ∈ F_p^*`, `N(u) = u^{1+p} = u²`, hence
`χ₃(u) = χ'(u²) = χ̄'(u)`.

**(c) Key lemma: `g(λ^p) = g(λ)` for every `λ`.** Substituting `t ↦ t^p` and using
`Tr(t^p) = Tr(t)` ⇒ `ψ(t^p) = ψ(t)`. In particular **`g(χ₃χ̄₄) = g((χ₃χ₄)^p) = g(χ₃χ₄)`**.

**(d) Duplication over `F_q`** with `λ = χ₃χ₄` (so `λρ = χ₃χ̄₄`, `λ² = χ̄₃ρ`), using (c) on the left:

```
g(χ₃χ₄)² = λ̄(4)·g(χ̄₃ρ)·g(ρ) = χ'(4) · g(χ̄₃ρ) · p
```
(`χ₄(4)=1` as `χ₄` is trivial on `F_p^*`; `χ̄₃(4) = χ'(4)` by (b)).

**(e) `χ̄₃ρ` is also a lift.** It is Frobenius-invariant, restricts on `F_p^*` to `χ'` (as `ρ` is
trivial there), and has order 6 ⇒ `χ̄₃ρ = (χ̄'η)∘N` with `η` the quadratic character mod `p`.
**Hasse–Davenport lifting** gives `g_q(μ∘N) = −g_p(μ)²`, so `g(χ̄₃ρ) = −g_p(χ̄'η)²`, and likewise
**`g(χ₃) = −g_p(χ')²`**.

**(f) Duplication over `F_p`** with `χ = χ̄'`: `g_p(χ̄')g_p(χ̄'η) = χ'(4)·g_p(χ')·g_p(η)`. With
`g_p(χ')g_p(χ̄') = χ'(−1)p = p` (`χ'(−1)=1`, `χ'` cubic) and `g_p(η)² = η(−1)p = −p` (`p ≡ 3 mod 4`):

```
g_p(χ̄'η)² = χ'(4)²·g_p(χ')²·(−p)·g_p(χ')²/p² = −χ'(4)²·g_p(χ')⁴ / p
```

**(g) Assemble.** Substituting into (d):

```
g(χ₃χ₄)² = χ'(4)·p·( +χ'(4)²·g_p(χ')⁴/p ) = χ'(4)³·g_p(χ')⁴ = g_p(χ')⁴        (χ'(4)³ = 1)
```
and therefore
```
J² = g(χ₃)²·g(χ₄)² / g(χ₃χ₄)² = g_p(χ')⁴ · p² / g_p(χ')⁴ = p²        ⇒   J = ±p ∈ Z.  ∎
```

---

## 3. What remains — **exactly one square-root sign**

From (g), `g(χ₃χ₄) = s·g_p(χ')²` for some `s ∈ {±1}`, and then

```
J = (−g_p(χ')²)·((−1)^{(p+1)/4} p) / (s·g_p(χ')²) = −s·(−1)^{(p+1)/4}·p
```

**The entire remaining gap is the sign `s` in `g(χ₃χ₄) = s·g_p(χ')²`.** The observed law `J = −p`
forces the prediction **`s = (−1)^{(p+1)/4}`** — a sharp, decidable statement that did not exist
before, and that is now the single object to attack (Gauss-sum square-root signs are the classically
hard step, cf. the sign of the quadratic Gauss sum).

**At secp256k1:** `p ≡ 7 mod 12`; `(p+1)/4 = 2²⁵⁴ − 2³⁰ − 244` is **even**, so `(−1)^{(p+1)/4} = +1`
and `J = −s·p`. The empirical law needs `s = +1`.

---

## 4. Standing of `m = 1` at secp — **still `[CONDITIONAL]`, but on a strictly smaller gap**

secp is `p ≡ 7 mod 12`, i.e. **`p ≡ 1 mod 3` — the case §2 leaves open on sign.** So:

| before | after |
|---|---|
| sign law `[EMPIRICAL 12/12]`, both halves | `p≡2 mod 3` **`[PROVED]`**; `p≡1 mod 3` **`[PROVED real, `J=±p`]`** |
| `J` real at `p≡1 mod 3` underived (needed `σ₅`-invariance) | **derived** (§2) |
| norm-lift `χ₃ = χ'∘N` asserted, not checked (defect A3) | **proved** (§2b) |
| gap = "`J` real AND its sign" | gap = **one square-root sign `s`** |
| `m = 1` at secp `[CONDITIONAL]` | **still `[CONDITIONAL]`** — unchanged in status |

**The predecessor's hard-scope line still stands: this says nothing about `m` at `2²⁵⁶` until `s` is
settled.** What changed is the size and shape of what must be proved, not the verdict.

---

## 5. Verification `[VERIFIED, exact]`

`jacobi_sign_law_proof_v1.py`: exact `Z[ζ₁₂]` (no float). All 27 primes `p ≡ 3 mod 4` up to 239 give
`J` a **rational integer**, `J = −p` for every `p ≡ 7 mod 12` and `J = +p` for every `p ≡ 11 mod 12`;
**0 disagreements**. Of these, **15 are fresh out-of-sample** (`103,107,127,131,139,151,163,167,179,
191,199,211,223,227,239`) — the ledger's tally was 12.

**Honesty on grade.** §1 and §2 are the author's own derivations plus the author's own numerics; per
CLAUDE.md §3/§7 the independent adversarial pass has **not** been run, so both carry
`[PROVED — UNREVIEWED]`, the same grade §A2.2 uses for its reduction. The intermediate identity
`g(χ₃χ₄)² = g_p(χ')⁴` was not separately checked numerically; its consequence `J² = p²` was, on all
27 primes.

**No ECDLP content.** This pins Frobenius eigenvalues of a supersingular abelian surface; it extracts
and approaches no bit of any scalar `d`.
