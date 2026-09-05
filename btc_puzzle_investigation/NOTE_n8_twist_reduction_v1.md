> # ⚠ WITHDRAWN 2026-09-04 — DUPLICATIVE, AND ITS CENTRAL EXPLANATION IS WRONG
>
> **This note re-derives work already completed on 2026-09-01 in
> `NOTE_n8_pencil_reduction_v1.md` (21:57, before this note existed), and recorded in the `CLAIMS.md`
> **N8** row.** The identity itself is already **`[PROVED — uniform]` as P19** (Galois descent on
> `E[2]`), with **M21** regraded `[VERIFIED] → [PROVED] via P19`. N8 was not open in the sense I
> treated it.
>
> **Duplicated, all of it:** the `n` odd hypothesis (there: `n` odd ⟺ `x³+Ax+B` irreducible); the
> translation by the rational half `Q₀ = R/2`; the reduction to an explicit **degree-7** character sum
> on the x-line; the genus-3 curve `C : y² = f(c)` with `Σ = −a_p(C)`; the `R = O` evaluation
> (their §3 (b),(c), machine-checked); and `s₁ = 0`, `s₂ = 0` — which are literally the first two
> columns of their **falsifier table**, run on 4 curves.
>
> **And §4 of this note is REFUTED.** I attributed `L(t) = t⁶ + a₃t³ + p³` to "a **μ₃ action / CM by
> `Z[ω]`** on the Jacobian — the same μ₃ the L-mono campaign runs on." That is **wrong**. The pencil
> note's §4 is titled *"why this is **not** a CM phenomenon"* and settles it with data I did not
> gather: it holds on **non-`j=0`** curves (`p=17, A=1, B=5`; `p=29, A=2, B=1`) which have **no μ₃
> automorphism at all**. The real mechanism: `n` odd ⟺ `x³+Ax+B` irreducible ⟺ **Frobenius 3-cycles
> `E[2]∖{O}`**; `E[2]` descends to a Klein four-group of Möbius involutions of `P¹ = E/±`;
> `Jac(C) ~ E₁×E₂×E₃` with Frobenius permuting the three blocks cyclically; **a block permutation with
> no fixed block has trace 0.** The ζ₃ is Galois, not CM.
>
> **The test that would have killed my story in one run, and which they had already done:** the sum is
> **nonzero over `F_{p³}`** (Frob³ is trivial, so the blocks are fixed), and every `F_{p³}` value is
> **divisible by 3**. I only computed `k = 1, 2` — the two values a CM story and the block story agree
> on — and stopped at the point where the two hypotheses are indistinguishable.
>
> **Process failure (mine).** `CLAIMS.md` states at the top that it is the only current document and
> that `check_ledger.py` must be run **at session start and before reporting any result**. I ran
> neither, and never opened `CLAIMS.md` — while writing a roadmap that diagnosed the corpus's
> documentation problems. Nothing below should be built on. Kept, unedited, as the trail.
>
> *(Dating note: this note is headed 2026-09-02 from the session clock; the filesystem records it as
> 2026-09-04. The pencil note predates it either way.)*

# NOTE — N8 reduced to a single one-variable Weil sum, and the `R = O` case PROVED. The branch condition is exactly `#E(F_p)` ODD.

*2026-09-02. Advances **N8** (open since `POSITIVE_FINDINGS_MASTER_v12`; the mechanism behind **M21**).
Builds on `NOTE_n8_branch_confinement_v1.md` (same day) and supersedes the strategy sketch in
`NOTE_n8_pointwise_convolution_v1.md` §4. Script `n8_twist_reduction_v1.py` (+ `.log`), pure stdlib,
exact integer. **No leakage / ECDLP / keyspace claim.***

Throughout: `p ≡ 7 mod 12`, `E : y² = x³ + B` (`B = 7`), `n = #E(F_p)`, `leg = χ₂(−1) = −1`,
`h₁[P] = χ₂(y_P)`, `h₂[P] = Σ_{Tr Q = P} χ₂^{(2)}(y_Q)`. **N8** is `h₂ = h₁⋆h₁ − 2·leg·p·δ_O`.

---

## 1. The branch condition, sharpened: `#E(F_p)` is ODD `[PROVED]`

`NOTE_n8_branch_confinement_v1.md` gave the condition as "cyclic". That is *implied* but not sharp.
Since `p ≡ 1 mod 3`, `x³ = −B` has **three** roots or **none**, so `E(F_p)[2]` is either all of `E[2]`
or trivial:

> **`m = +1` ⟺ `x³+B` has no root in `F_p` ⟺ `E(F_p)[2] = {O}` ⟺ `#E(F_p)` is ODD.**
> Verified `p < 700`, **zero exceptions**.

This is the operative form, because odd `n` makes **multiplication by 2 an automorphism of `E(F_p)`**:
every `R` has a **unique** rational half `A₀ = ((n+1)/2)·R`. That is exactly what the argument needs,
and exactly what fails on the `m = −2` branch — where `2A = R` has four rational solutions or none.
*(It also explains why no rational point has `y = 0`, so `h₁` never vanishes for a nuisance reason.)*

## 2. Translation: both sides become sums of ONE function `[PROVED, verified all R]`

Put `C := A − A₀`. Then `R − A = A₀ − C`, so the involution `A ↦ R−A` becomes `C ↦ −C`. Define

> **`G_R(C) := y_{A₀+C} · y_{A₀−C}`.**

- For `C ∈ E(F_p)`: `χ₂(G_R(C))` is exactly the `(h₁⋆h₁)[R]` summand.
- For `C'` with `Frob C' = −C'` — i.e. `C' ∈ E'(F_p)`, **`E'` the quadratic twist** — we have
  `A₀ − C' = Frob(A₀+C')`, so `G_R(C') = N(y_{A₀+C'})` and
  `χ₂^{(2)}(y_{A₀+C'}) = χ₂(N(y_{A₀+C'})) = χ₂(G_R(C'))` — the `h₂[R]` summand.

> ### **`(h₁⋆h₁)[R] = Σ_{C ∈ E(F_p)} χ₂(G_R(C))`  and  `h₂[R] = Σ_{C' ∈ E'(F_p)} χ₂(G_R(C'))`**
> ### ⇒ **N8 ⟺ the same function's `χ₂`-sum over `E` and over its quadratic twist differ by `2p·δ_O`.**

**Verified exactly at every `R`**, `p = 31, 43, 67, 79, 103, 127`. *(`E'(F_p)` must include its
identity — omitting it costs exactly `+1` per `R ≠ O`, which is how the bookkeeping was caught.)*

## 3. `R = O` is PROVED, elementarily

`A₀ = O`, so `G_O(C) = y_C·y_{−C} = −y_C²`.
- **On `E(F_p)`:** `n` odd ⟹ no affine point has `y = 0`, so each of the `n−1` affine points gives
  `χ₂(−y²) = χ₂(−1) = −1` (using `p ≡ 3 mod 4`). Sum `= −(n−1)`.
- **On `E'(F_p)`:** `Frob C' = −C'` gives `y_{C'}^p = −y_{C'}`, so `y_{C'}^{p−1} = −1` and
  `χ₂^{(2)}(y_{C'}) = (y^{p−1})^{(p+1)/2} = (−1)^{(p+1)/2} = +1`, since `4 | p+1`. Each of the
  `n′−1` affine points contributes `+1`. Sum `= n′−1 = 2p+1−n` (as `n′ = 2p+2−n`).
- **Difference** `= (2p+1−n) − (−(n−1)) = **2p** = −2·leg·p`. ∎

*Note where `p ≡ 3 mod 4` enters twice, with opposite effect on the two curves — that asymmetry **is**
the `2p` defect. It is not an error term; it is the whole content at `R = O`.*

## 4. `R ≠ O` reduces to one Weil sum on the x-line `[VERIFIED]`

`G_R(−C) = y_{A₀−C}y_{A₀+C} = G_R(C)`, so **`G_R` is even**, hence a function `g_R(x_C)` of the
x-coordinate alone — a rational function on `P¹` defined over `F_p`. Above each `x`, `E` has
`1 + χ₂(x³+B)` points and `E'` has `1 − χ₂(x³+B)`. Therefore

```
 Σ_E χ₂(G_R) − Σ_{E'} χ₂(G_R) = 2 · Σ_{x∈F_p} χ₂( g_R(x) · (x³+B) )
```

> ### **N8 for `R ≠ O` ⟺ `W(R) := Σ_{x ∈ F_p} χ₂( g_R(x)·(x³+B) ) = 0`.**

**Verified: `W(R) = 0` EXACTLY, at every `R ≠ O`, `p = 31, 43, 67, 79, 103`.** (`g_R` is computed in
`F_{p²}` and lands in `F_p` at every `x`, as it must; the single `x = x_{A₀}` where `A₀ ± C = O` is
excluded consistently on both sides.)

## 5. Where this leaves N8

| piece | status |
|---|---|
| branch condition `= #E` odd | **`[PROVED]`** |
| translation ⇒ `E` vs quadratic twist, one function | **`[PROVED]`**, verified all `R` |
| **`R = O`** | **`[PROVED]`** — §3, complete and elementary |
| **`R ≠ O` ⟺ `W(R) = 0`** | **`[PROVED — reduction]`**; the vanishing itself **`[VERIFIED — exact, 5 primes, all `R`]`** |
| `W(R) = 0` | **OPEN — this is now all of N8** |

> ## ⚠ CORRECTED 2026-09-02 by `NOTE_n8_mu3_structure_v1.md`
> The paragraph below names a **fixed-point-free involution** as "the signature" of the exact
> vanishing. **That is refuted** — an exhaustive search over all Möbius involutions finds none. The
> real structure is **μ₃, not order 2**: `s₁ = 0` AND `s₂ = 0` (108 cases), which forces
> `L(t) = t⁶ + a₃t³ + p³`, a polynomial in `t³` — the signature of a μ₃/CM-by-`Z[ω]` Jacobian.
> `W(R) = 0` is a corollary of that. Read §5 of the new note instead.

**Why the last step should be findable.** `W(R)` is a sum of `±1` over `p` terms that vanishes
**exactly**, not to `O(√p)`. Exact vanishing of a quadratic-character sum is the signature of a
**fixed-point-free involution** on the x-line pairing terms of opposite sign (equivalently: the
hyperelliptic curve `u² = g_R(x)(x³+B)` has Frobenius trace exactly `0`). Finding that involution —
or the corresponding automorphism/supersingularity — closes N8 outright. **That is a one-variable
problem now, not a comparison of two loci on an elliptic curve.**

**Distance travelled today:** N8 went from "prove `V₂ = V₁² − 2·leg·p`, a Fourier identity over
`Q(ζ_n)` measured on 1171 μ₆-orbit cells" to "prove one explicit `±1` sum on `P¹(F_p)` vanishes,
with the `R = O` case already done and the hypothesis (`#E` odd) identified and required."

## 6. Owed
`W(R) = 0`. `compile-diff` if folded into a master. The `m = −2` branch is **out of scope by
counterexample** (`NOTE_n8_branch_confinement_v1.md` §3) — not an omission.
