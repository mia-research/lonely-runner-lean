> # ⚠ STATUS 2026-09-04 — this note is **M38** in `CLAIMS.md` `[VERIFIED — exact]`. It is NOT withdrawn.
> An earlier blanket "withdrawn/duplicative" header I added today was **wrong** and is removed:
> M38 (the pointwise form `h₂ = h₁⋆h₁ − 2·leg·p·δ₀`) is a recognised ledger row.
>
> Two corrections still apply, both mine, both standing:
> 1. `NOTE_n8_branch_confinement_v1.md` corrects §2's "far more is true" (the pointwise form adds
>    exactly ONE Fourier coefficient, and it is **vacuous** — it restates `m=1`, forced by the
>    branch) and §3's "not a cell artefact" (the composite-`n` primes are composite but still cyclic,
>    so still one branch). **M38's ledger wording "escapes M21's cell framework" inherits that
>    over-reach and should be narrowed when the ledger is next edited.**
> 2. **N8 itself was already reduced much further on 2026-09-01 (21:57) in
>    `NOTE_n8_pencil_reduction_v1.md`**, and the underlying identity is `[PROVED — uniform]` as **P19**.
>    This note's §4 "strategy" section was superseded before it was written.

# NOTE — N8 / M21 sharpened: the identity is POINTWISE, not just Fourier. `h₂ = h₁⋆h₁ − 2·leg·p·δ₀`, exact at 11 primes including composite `n`.

*2026-09-01. Advances **N8** (open since `POSITIVE_FINDINGS_MASTER_v12`; = the mechanism question
behind **M21**), restated with a converse in `RESULT_rho_branch_convention_v1.md` §7. Script
`n8_pointwise_convolution_v1.py` (+ `.log`), pure stdlib, exact integer throughout — no Sage, no
cyclotomic field, no factorisation. **No leakage / ECDLP / keyspace claim.***

> **Citation discipline, up front.** The `V₂ = V₁² − 2·leg·p` identity **is M21** and must be cited
> as M21 (v12: exact at 1171 μ₆-orbit cells, 11 primes `43 ≤ p ≤ 1303`, certified by exact integer
> convolution `f = h₂ − h₁⋆h₁`). It is **not** new, and the 2026-09-01 (b) `RESEARCH.md` entry's
> phrase "New high-priority open item" is wrong on the word *new* — `RESULT_rho_branch_convention_v1.md`
> §7 corrects itself on exactly this point. What is new here is the **pointwise form** and its
> **scope beyond the cell framework**, below.

---

## 1. The objects (from `audit_n1_vsign_v2_core.py`)

`E : y² = x³ + 7` over `F_p`, `n = #E(F_p)`, `G` a generator, `χ₂` the quadratic character of `F_p^*`,
`χ₂^{(2)}` that of `F_{p²}^*`, `leg := χ₂(−1)`.

- **`h₁[d] = χ₂(y_P)` for `P = [d]G`** (zero at `d=0` and at any `y=0` point).
- **`h₂[d] = Σ_{Q ∈ E(F_{p²}), Tr(Q) = [d]G} χ₂^{(2)}(y_Q)`**, where `Tr(Q) = Q + Frob(Q)`.
- `V₁(a) = Σ_d h₁[d]ζ_n^{ad}`, `V₂(a) = Σ_d h₂[d]ζ_n^{ad}` — so `V₁, V₂` are the **DFTs** of `h₁, h₂`,
  and `V₁² ` is the DFT of `h₁⋆h₁`.

## 2. The sharpening

M21 states `V₂(a) = V₁(a)² − 2·leg·p` **for `a ≠ 0`**. Transforming back, that only forces
`f := h₂ − h₁⋆h₁` to be **constant off `d=0`** with a prescribed jump. Measured directly, far more
is true:

> ### **`f[d] = 0` for EVERY `d ≠ 0`, and `f[0] = −2·leg·p`.**
> ### i.e.  **`h₂ = h₁⋆h₁ − 2·leg·p·δ₀`**

The entire discrepancy is concentrated at the identity element. Explicitly, for every `R = [d]G ≠ O`:

> `Σ_{Q ∈ E(F_{p²}), Q + Frob Q = R} χ₂^{(2)}(y_Q)  =  Σ_{P + P' = R, both in E(F_p)} χ₂(y_P)χ₂(y_{P'})`
> — **on the nose, no error term.**

## 3. Verification (exact integer, `n8_pointwise_convolution_v1.py`)

| p | n | leg | `f[d≠0]` distinct values | `f[0]` | `−2·leg·p` |
|---:|---:|---:|---|---:|---:|
| 43 | 31 | −1 | `{0}` | 86 | 86 |
| 61 | 61 | +1 | `{0}` | −122 | −122 |
| 67 | 79 | −1 | `{0}` | 134 | 134 |
| 79 | 67 | −1 | `{0}` | 158 | 158 |
| 97 | 79 | +1 | `{0}` | −194 | −194 |
| 103 | **111** | −1 | `{0}` | 206 | 206 |
| 127 | 127 | −1 | `{0}` | 254 | 254 |
| 139 | **147** | −1 | `{0}` | 278 | 278 |
| 151 | **133** | −1 | `{0}` | 302 | 302 |
| 163 | 139 | −1 | `{0}` | 326 | 326 |
| 193 | **219** | +1 | `{0}` | −386 | −386 |

**11 primes, both `leg` arms, every `d`, exact.** (`p=181` skipped — the script's generator search
assumes a cyclic group; not a failure of the identity, a limitation of the probe.)

> **Scope gain that matters.** Four of these have **composite `n`** (111, 147, 133, 219). M21's 1171
> cells are μ₆-**orbit cells**; the pointwise identity is stated and verified per group element, and
> holds where the cell/orbit framework does not obviously apply. This is evidence that the identity is
> **structural, not a cell artefact** — the exact worry that killed `ρ_p`.

## 4. Why this is the right form to attack, and the strategy

Both sides are **the same weight summed over two different Frobenius-stable loci.** Fix `R ≠ O` and
set `w(Q) := χ₂(y_Q · y_{R−Q})`. Then:
- for **rational** `Q`, `w(Q) = χ₂(y_Q)χ₂(y_{R−Q})` — the RHS summand;
- for `Q` with `Frob Q = R − Q`, `y_{R−Q} = y_Q^p`, so `y_Q y_{R−Q} = N(y_Q)` and
  `χ₂^{(2)}(y_Q) = N(y_Q)^{(p−1)/2} = χ₂(N(y_Q)) = w(Q)` — the LHS summand. **Same function.**

Let `φ(Q) := R − Q` (an involution of `E`, negation composed with translation by `R`). Then
> RHS sums `w` over `Fix(Frob)`; LHS sums `w` over `Fix(φ∘Frob)`.

`φ∘Frob` is a **twisted Frobenius**, so the two loci are the point sets of `E` and of its twist by the
cocycle `φ`, and the claim is that `w` has **equal total** over both. That is a torsor/twist
comparison with a character weight — an elementary, finite statement, with no `ℓ`-adic input. The
`d=0` defect `−2·leg·p` is exactly the correction at the degenerate fibre where `φ` is negation
(`R = O`), and `leg = χ₂(−1)` is precisely the sign by which negation acts on `y`.

**If this comparison is proved, `T2`'s entire finite shadow becomes a theorem** — no GKR rigidity, no
sheaf isomorphism `W′ ≅ W⊗ψ` (`ROADMAP_REDIRECT_v4.md` §3.1). Route B remains the only home for the
*labeling* (`RESULT_rho_branch_convention_v1.md` §6, a theorem), and is untouched by this.

## 5. Grade, and what is NOT claimed

| item | grade |
|---|---|
| `h₂ = h₁⋆h₁ − 2·leg·p·δ₀` (pointwise) | **`[EMPIRICAL — exact, 11 primes, both `leg` arms, every `d`, incl. 4 composite `n`]`** |
| equivalence to M21's `V₂ = V₁² − 2·leg·p` at `a≠0` | `[PROVED — elementary]` (DFT of a convolution) |
| the `w`-on-two-loci reformulation (§4) | `[PROVED — elementary]` — the two summands are the same function `w` |
| the twist comparison itself | **NOT PROVED. This is the open item (N8).** |

**Not claimed:** that §4 is a proof — it is a strategy, and the step that would close it (equal totals
of `w` over `Fix(Frob)` and `Fix(φ∘Frob)`) is not attempted here. **Not claimed:** any extension of
M21's grade — M21's 1171 cells remain the stronger *cell-level* evidence; this note's 11 primes are
independent re-confirmation in a different (pointwise, per-element) form, **not** an enlargement of
M21's base. **Not claimed:** anything about `p = 2²⁵⁶`.

## 6. Owed
`compile-diff` if folded into a master. `citation-verifier` not applicable (no external citation is
load-bearing here). The identity must be **cited as M21** wherever it is used; this note is a
sharpening of its *form* and an advance on **N8**, not a new result.
