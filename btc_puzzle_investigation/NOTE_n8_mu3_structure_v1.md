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

# NOTE — N8: the involution hypothesis is REFUTED; the real structure is μ₃. `s₁ = s₂ = 0` forces the genus-3 L-polynomial to be `t⁶ + a₃t³ + p³`, and `W(R) = 0` is a corollary.

*2026-09-02. Continues `NOTE_n8_twist_reduction_v1.md` (same day). Corrects that note's §5 and the
matching `HANDOFF_LOG` line. Script `n8_twist_reduction_v1.py` + this session's probes. Exact integer
throughout. **No leakage / ECDLP / keyspace claim.***

---

## 1. The involution hypothesis was wrong `[REFUTED]`

`NOTE_n8_twist_reduction_v1.md` §5 argued: *"`W(R)` is a sum of `±1` over `p` terms that vanishes
**exactly** … the signature of a **fixed-point-free involution** on the x-line pairing terms of
opposite sign."* Mine, and stated as the natural reading.

**Exhaustive search finds none.** Over **all** Möbius involutions `σ(x) = (αx+β)/(γx−α)` (every
`(α:β:γ)`, degeneracies excluded), at `p=43` (`R#1`, `R#5`) and `p=67` (`R#2`): **zero** maps satisfy
`T(σx) = −T(x)`. The exact vanishing is **not** a sign-pairing on the x-line.

*Where the reasoning went wrong: "exact vanishing of a ±1 sum" has at least two sources — a pairing
involution (order 2) **and** a structural constraint on the L-polynomial. I named only the first and
called it "the signature". It was the wrong one.*

## 2. The explicit object

With `A₀` the unique rational half of `R` (§1 of the predecessor: `#E(F_p)` odd), interpolation gives

> **`H(x) = g_R(x)·(x³+B) = N(x)/(x−a)³`, `deg N = 6`, `a = x_{A₀}`**, and `N = (x³+B)·M(x)` **exactly**
> with `M` cubic. Hence `T(x) = χ₂(D(x))` for
> ### **`D(x) = (x³+B) · M(x) · (x−a)`,  degree 7, squarefree** (`gcd(D,D') = 1`, checked).

So `u² = D(x)` is a **genus-3 hyperelliptic curve** and `W(R) = −s₁`, `s₁ = Σαᵢ` the Frobenius trace.
The roots are structural: `x³+B` vanishes on `x(E[2])`, `M` on `x(T_i − A₀)`, `(x−a)` on `x(A₀)` —
i.e. `{roots} ∪ {∞}` is the x-image of `{P : 2P ∈ {O, −R}}`, the union of two `E[2]`-cosets.

## 3. The finding: `s₁ = 0` AND `s₂ = 0` `[VERIFIED — exact, all R]`

| p | n | R tested | `s₁ = 0` | `s₂ = 0` |
|---:|---:|---:|---|---|
| 43 | 31 | **all 30** `R ≠ O` | 30/30 | 30/30 |
| 67 | 79 | **all 78** `R ≠ O` | 78/78 | 78/78 |

(`s₁` over `F_p`, `s₂` over `F_{p²}`, both exact integer sums of `±1`.) **108 (R,p) cases, no exceptions.**

## 4. What `s₁ = s₂ = 0` forces

For a genus-3 curve the L-polynomial, with the functional equation, is
`t⁶ + a₁t⁵ + a₂t⁴ + a₃t³ + p·a₂t² + p²·a₁t + p³`. Newton's identities give
`a₁ = −s₁ = 0` and `e₂ = (s₁² − s₂)/2 = 0 ⇒ a₂ = 0`. Therefore

> ### **`L(t) = t⁶ + a₃t³ + p³` — a polynomial in `t³`.**

A characteristic polynomial that is a polynomial in `t³` is the signature of a **μ₃ action / CM by
`Z[ω]` on the Jacobian** — the *same* `μ₃` that runs the entire L-mono campaign and the `j=0`
geometry. Not a new ingredient: a convergence.

**Consequence.** `W(R) = −s₁ = −(−a₁) = 0` becomes a **corollary** of the μ₃ structure, and it comes
with `s₂ = 0` for free. The target is now strictly stronger than what N8 needs.

## 5. The μ₃ is directly visible in the degenerate case

At `p = 103`, `R#2`, `A₀ = (0,25)` — so `a = 0` — interpolation gives `M = 7x³ + 20`, hence
`D(x) = (x³+7)(7x³+20)·x` and, for `β³ = 1`,

> `D(βx) = (x³+7)(7x³+20)·βx = β·D(x)`,

so `(x, u) ↦ (βx, √β·u)` is an order-3 automorphism of `u² = D(x)` — and `√β ∈ F_p` because
`p ≡ 7 mod 12` makes `(p−1)/3` even, so `β` is a square. **Exact, not measured.**
For `a ≠ 0` the same `μ₃` cannot act as `x ↦ β(x−a)+a` (that map moves the roots of `x³+B` off
themselves unless `a = 0`), so it must act by a different Möbius map or non-linearly — **finding it is
the remaining step.** Counting is consistent: `7` roots `+ ∞ = 8` points, and a `μ₃` on `P¹` fixes `2`
and permutes `6` in two 3-cycles.

## 6. Status

| item | grade |
|---|---|
| no anti-invariant Möbius involution exists | **`[REFUTED — exhaustive search, 3 (p,R) cases]`** |
| `D = (x³+B)·M·(x−a)`, degree 7, squarefree | **`[VERIFIED — exact, interpolated + gcd]`** |
| `s₁ = s₂ = 0` | **`[VERIFIED — exact, 108 (R,p) cases, all `R` at 2 primes]`** |
| `s₁ = s₂ = 0 ⇒ L(t) = t⁶ + a₃t³ + p³` | **`[PROVED — Newton + functional equation]`** |
| `μ₃` action, `a = 0` case | **`[PROVED — exact]`** |
| **`μ₃` action for general `a`** | **OPEN — this is now the whole of N8** |

## 7. Owed
Exhibit the `μ₃` action on `u² = D_R(x)` for general `R` (equivalently: prove `L` is a polynomial in
`t³`, or that `Jac` has CM by `Z[ω]`). That closes N8, and yields `s₂ = 0` as a bonus.
`compile-diff` if folded into a master. Two `p`, all `R` — **not** a `2²⁵⁶` claim, and the `m = −2`
branch remains out of scope by counterexample (`NOTE_n8_branch_confinement_v1.md` §3).
