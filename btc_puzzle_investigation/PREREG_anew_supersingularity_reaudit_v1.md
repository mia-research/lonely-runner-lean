# PREREG — re-audit of the `A_new` supersingularity proof, and a candidate replacement route

**Written 2026-08-02, BEFORE any script in this session was written or run.** No data from this
session has been seen. Governing rules: session rules 1–5 (zero fabrication; unconditional prereg
adherence; exact arithmetic + squarefree reduction; no narrative smoothing; explicit object
definitions), plus `btc_puzzle_investigation/CLAUDE.md` (counter-prior; closure carries the PROVED
bar) and root `CLAUDE.md` §2/§3.

---

## 0. Why this run exists

`RESULT_mu6_cohomology_supersingular_v2.md` grades **`A_new` supersingular at every `p ≡ 3 mod 4`**
as `[PROVED — scale-free, curve-independent]`, and its §5 records an **unpaid debt**:

> *"the two load-bearing external facts are (i) the Frobenius-twist relation `π φ = φ^σ π` and
> (ii) the surface `p`-rank/`End⁰` dichotomy. Both are standard; an independent re-derivation is
> the remaining diligence."*

That re-derivation has not been run in any session since 2026-07-20. This run pays it. Per the
Statement of intent, a `[PROVED]` claim that gates an avenue's status (P13 / `Hom(E,A_new)=0` /
Route 2) carries the same bar as any positive, so it is audited, not assumed.

**This is an audit of a PROOF, not a leakage test.** No key, no `(n,k,D)` decomposition, no target,
no d-side feature is touched. No ECDLP or leakage claim will be made from any outcome.

---

## 1. Objects — full definitions (rule 5)

Every symbol below is defined here in exact terms; nothing is inherited by shorthand.

| symbol | definition |
|---|---|
| `p` | a rational prime, `p > 3`. Two disjoint arms: **MAIN** `p ≡ 3 (mod 4)`, **CONTROL** `p ≡ 1 (mod 4)`. |
| `f` | a **separable** cubic in `F_p[x]`, `deg f = 3` exactly, `disc(f) ≠ 0` in `F_p`. Not assumed monic, not assumed of the form `x³+B`. |
| `C` | the smooth projective model over `F_p` of the affine curve `w⁴ = f(x)`. Since `gcd(4, 3) = 1`, `∞` is totally ramified; `C` has **genus 3**. |
| `ζ₄` | the automorphism `(x,w) ↦ (x, i·w)` of `C`, `i ∈ F̄_p` a primitive 4th root of 1. Defined over `F_p(i)`, i.e. over `F_{p²}` when `p ≡ 3 mod 4`. |
| `E` | the quotient `C/⟨ζ₄²⟩`, i.e. `y² = f(x)` with `y = w²`; an elliptic curve over `F_p` (rational point at `∞`). |
| `A_new` | the abelian surface `⊂ Jac(C)` complementary to `E`: `Jac(C) ~ E × A_new` over `F_p`, `dim A_new = 2`. Equivalently (per `RESULT_anew_identification_v1.md` §1, `[PROVED — UNREVIEWED]`) the **`χ₄`-isotypic** part, = the sum of the `μ₄`-eigenspaces on which `ζ₄²=−1` acts by `−1`. **The model is fixed as this specific subvariety of `Jac(C)`** — this matters, see §5. |
| `π` | the `p`-power Frobenius endomorphism of `A_new` over `F_p`. |
| `P_new(t)` | `= t⁴ + b₁t³ + b₂t² + p·b₁·t + p²`, the characteristic polynomial of `π` on `H¹(A_new)`. |
| **ordinary** | `p`-rank 2 (for a surface). |
| **supersingular** | for `g = 2`: isogenous over `F̄_p` to a product of supersingular elliptic curves ⟺ Newton polygon all slopes `1/2` ⟺ `p`-rank 0. **Isogeny-invariant.** |
| **superspecial** | `A ⊗ F̄_p ≅ E₁ × E₂` with both `Eᵢ` supersingular ⟺ `a`-number `= 2`, where `a(A) := dim_k Hom(α_p, A) = dim ker(Cartier | H⁰(A, Ω¹))`. **NOT an isogeny invariant** — it is a statement about the fixed model above. Strictly stronger than supersingular. |
| `𝒞` | the **Cartier operator**, the `p⁻¹`-semilinear map on `H⁰(C, Ω¹)` with `𝒞(h^p ω) = h·𝒞(ω)` and, on `F_p(x)`, `𝒞(Σ cᵢ xⁱ dx) = Σ c_{ip+p−1}^{1/p} xⁱ dx`. |
| `V_b` | the `μ₄`-eigenspace of `H⁰(C, Ω¹)` spanned by `x^a dx / w^b`, `b ∈ {1,2,3}`. `V₂` is the `E`-part; `V₁ ⊕ V₃` is the `A_new`-part. |
| `E^d` | the quadratic twist of an elliptic curve `E/F_p` by a non-square `d ∈ F_p*`. |

**Two objects that must not be conflated** (this project has a logged collision failure on the label
`(D2)`): "`End⁰` over `F_p`" vs "`End⁰` over `F̄_p`". Step 3 of the audited proof reasons about
`End⁰(A_new ⊗ F̄_p)`; `π` lies in it (the base-change of the relative Frobenius is `F̄_p`-linear),
and conjugation by `π` induces the Galois action `φ ↦ φ^{(p)}`. All claims below are about the
`F̄_p` algebra unless stated.

---

## 2. The three hypotheses, pre-committed

### H-A (audit of the existing proof, Step 3, ordinary stratum)

> The audited Step 3 excludes the ordinary stratum via: *"`End⁰(A_new)` is a commutative field
> (a quartic CM field). Then `π i π⁻¹ = i ≠ −i`."*
>
> **H-A: that exclusion is incomplete.** An ordinary abelian surface over `F_p` that is
> `F̄_p`-isogenous to `E²` has `End⁰ = M₂(K)`, `K` imaginary quadratic — non-commutative — and is
> not covered by either listed case. **Candidate explicit witness:** `A = E × E^d` with `E/F_p`
> **ordinary** and `p ≡ 3 mod 4`, with
> `i := (P,Q) ↦ (ψ(Q), −ψ⁻¹(P))`, where `ψ : E^d → E` is the twisting isomorphism over `F_{p²}`.

**Pre-committed decision rule.** H-A is upheld **only if all four** of the following are verified by
executed computation, each on `≥ 3` primes `p ≡ 3 mod 4` and `≥ 3` ordinary curves `E` each:

- **A1** `ψ` is an isomorphism `E^d → E` over `F_{p²}` and **not** over `F_p`, with `ψ^σ = −ψ`
  (`σ` = the non-trivial element of `Gal(F_{p²}/F_p)`), verified **pointwise on ≥ 20 points**.
- **A2** `i² = [−1]` on `A = E × E^d`, verified pointwise on `≥ 20` point-pairs.
- **A3** `A` is **ordinary**: `a_p(E) ≢ 0 (mod p)`, and `b₂(A) = 2p − a_p(E)² ≢ 0 (mod p)`.
- **A4** `b₁(A) = a_p(E) + a_p(E^d) = 0`, i.e. the witness reproduces the audited proof's own
  "Fact 1" signature while being ordinary.

If any of A1–A4 fails, **H-A is not upheld** and I report the existing Step 3 as un-refuted.

### H-B (candidate replacement proof: the graded Cartier route)

> **H-B:** for every `p ≡ 3 mod 4` and every separable cubic `f`, the Cartier operator **vanishes
> identically** on the new part `V₁ ⊕ V₃ ⊂ H⁰(C, Ω¹)`. Consequently `a(A_new) = 2`, i.e. `A_new` is
> **superspecial**, hence in particular supersingular.
>
> Two ingredients, both to be checked, not assumed:
> **(B-i)** `dim V₁ = 0`, `dim V₂ = 1`, `dim V₃ = 2` (from `dim V_b = ⌊3b/4⌋`).
> **(B-ii)** `𝒞(V₃) = 0` at `p ≡ 3 mod 4` — by the pre-derived degree count: `𝒞(x^a dx/w³)
> = w³·f⁻¹·𝒞(x^a f^{p−t} dx)` with `t = 3(p+1)/4`, and `deg(x^a f^{p−t}) ≤ (3p−5)/4 < p−1`, so no
> coefficient of index `ip+p−1` exists.

### H-C (the mirror, which is the control — see §3)

> **H-C:** at `p ≡ 1 mod 4` the same operator maps `V₃ → V₃` and is **generically non-zero**
> (rank ≥ 1, generically 2) ⇒ `A_new` ordinary.

---

## 3. Controls, and what makes this run VOID

Rule 2 governs: a fired control kills the adjudication, and no post-hoc argument rescues it.

| id | control | pre-committed pass condition | if it fails |
|---|---|---|---|
| **C1** | **Instrument validation.** `Tr(M) ≡ a_p(C) (mod p)` where `M` is the computed `3×3` Cartier matrix and `a_p(C) = p+1−#C(F_p)` from an **independent exact point count** (Manin's congruence). | Must hold at **every** `(p,f)` tested, both arms. | **Script is wrong.** Fix the script and re-run everything; no verdict may be read from a run in which C1 failed anywhere. |
| **C2** | **Discriminating control (the load-bearing one).** The *same code path* run at `p ≡ 1 mod 4` must report a **non-zero** new-part block for at least 1/3 of `(p,f)` pairs. | non-zero rate `≥ 1/3` on the `p ≡ 1 mod 4` arm | **The instrument cannot distinguish** ⇒ H-B's `p ≡ 3` zeros are vacuous ⇒ **the whole H-B arm is VOID**, not "confirmed". |
| **C3** | **Dimension check by divisor.** `dim V_b` verified by computing the **divisor** of `x^a dx/w^b` on the smooth model in Sage's function-field machinery (independent of the `⌊3b/4⌋` formula): `dx/w` must be **non**-holomorphic; `dx/w²`, `dx/w³`, `x·dx/w³` must be holomorphic; `x²·dx/w³` must be non-holomorphic. | all five verdicts as stated, at every `p` tested | (B-i) is wrong ⇒ H-B is refuted; report as such. |
| **C4** | **Perturbation control.** Feed the Cartier routine a deliberately corrupted `t` (`t+1`). | must break C1 (reject) | if a corrupted exponent still passes C1, C1 is not a real check ⇒ **VOID**. |
| **C5** | **Independent `b₂` route.** `p \| b₂` computed from exact point counts over `F_p, F_{p²}` (the 2026-07-20 route), on the same `(p,f)` pairs. | must agree with the Cartier verdict on supersingular-vs-ordinary at every pair | disagreement ⇒ one of the two instruments is wrong ⇒ **VOID until resolved**; no verdict from either. |

**Additional void condition (rule 1):** any number that appears in the result document must be
traceable to a line of executed script output in this session's `.log` files. Anything I cannot
point at gets deleted, not rounded.

---

## 4. Sampling, power, and scope — fixed now

- **MAIN arm:** all primes `p ≡ 3 mod 4` with `7 ≤ p ≤ 200`, plus `{211, 251, 503, 1019}`.
- **CONTROL arm:** all primes `p ≡ 1 mod 4` with `5 ≤ p ≤ 200`, plus `{257, 509, 1013}`.
- **Cubics per prime:** the record's 6 (`x³+7, x³+2, x³+11, x³+2x+5, x³+x+1, x³−x+3`) **plus 6
  uniformly random separable cubics** drawn with a **fixed seed = 20260802**, `a₃ ∈ F_p*`,
  `a₂,a₁,a₀ ∈ F_p`, rejecting `disc = 0`. Random draws are included because the 6-cubic list is
  curated and a curated list cannot establish curve-independence (project memory:
  *diverse sampling mandatory; lexicographic/curated iteration biases*).
- **Power statement, pre-committed:** this design can only detect a failure of H-B that occurs at
  some `(p, f)` **inside** the sampled ranges. It has **no power** against a failure first occurring
  at `p > 1019`, and **none at all** at `p = 2²⁵⁶−2³²−977`. The scale gap is not closed by any count
  of small primes — only the **proof** (H-B's degree count) is scale-free, and only if it survives.
- **Forced/unforced accounting, pre-committed:** if H-B's degree count is correct, then **every**
  main-arm zero is *forced by the same one-line inequality* and the arm therefore carries
  **`1` unforced bit, not `N` bits** — it is an **instrument check on my code**, not `N`-fold
  evidence. I commit now to reporting it that way regardless of how large `N` turns out to be.
  The genuinely unforced content is: **C2 (does the control fire), C3 (are the dimensions right),
  C5 (do two independent instruments agree)**.

---

## 5. What each outcome is allowed to conclude (pre-committed, before data)

| outcome | permitted conclusion | forbidden |
|---|---|---|
| H-A upheld (A1–A4 all pass) | *"Step 3's exclusion of the ordinary stratum is incomplete as written; an explicit ordinary witness satisfies its hypotheses."* The **`[PROVED]` grade of §A1.1 is not supported by the argument given**, pending a repair. | Concluding `A_new` is **not** supersingular. Refuting a mechanism ≠ refuting a claim. |
| H-A not upheld | *"Step 3 survives this attack."* | Upgrading anything; a survived attack is not an independent re-derivation. |
| H-B holds + C1–C5 all pass | *"`𝒞 ≡ 0` on the new part at `p ≡ 3 mod 4`; `A_new` is superspecial, hence supersingular, for every separable cubic — by an argument using only `4 \| p+1` and the standard Cartier formula."* Grade: **`[PROVED — UNREVIEWED]`** (my derivation), decidable shadow `[VERIFIED, N pairs]`. | Grading it `[PROVED]` flat. It is my own derivation, unreviewed, exactly as `RESULT_anew_identification_v1.md` §1 was graded. |
| H-B fails at any pair | Report the failing `(p,f)` and **retract H-B**. | Rescuing it by adjusting `t`, the basis, or the prime range after seeing which pair failed. |
| C2 does not fire | **VOID** the H-B arm; report VOID. | Reporting the `p≡3` zeros as confirmation. |

**Superspecial is model-dependent** (§1): it is a statement about `A_new ⊂ Jac(C)` as a fixed
subvariety, **not** about its isogeny class. The supersingular corollary *is* isogeny-invariant. Any
result text must keep these two apart.

**Nothing here bears on ECDLP, leakage, or key recovery, in any outcome.** The only ledger objects
touched are §A1.1's grade and the `RESULT_mu6_cohomology_supersingular_v2.md` §5 debt.

---

## 6. Falsification conditions, restated in one place

- H-A is false if any of A1–A4 fails.
- H-B is false if any `(p,f)` on the main arm has a non-zero new-part Cartier block, or if C3's
  divisor verdicts differ from `(0,1,2)`.
- The **run** is void if C1, C2, C4 or C5 fails, independent of what H-A/H-B look like.

*No arm of this prereg may be edited after the first script is executed. Deviations go in
`PREREG_anew_supersingularity_reaudit_v1_DEVIATIONS.md`, timestamped, with the reason.*
