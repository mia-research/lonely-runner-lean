# RESULT — FORK (1): the `a≠0` twisted eigenvalues are NON-ABELIAN → not Jacobi sums → L-Stick premise fails; the `ζ₃` is geometric (L-mono)

*2026-07-27. Exact number-field computation (Sage), plant-validated. Answers the open premise of
`ANALYSIS_..._kronecker_route_v3.md §4` and `RESULT_stickelberger_citation_verified_v1.md §3. No leakage
or ECDLP claim. Grade: `[VERIFIED — p=43,67; plant-validated]` (not `[PROVED — all p]`).*

---

## 1. The question and the answer

**Question (fork 1):** are the `a≠0` Frobenius eigenvalues of `H¹_c(E, L_{χ₂(y)} ⊗ L_{χ_a})` Jacobi
sums / Hecke-character values (⟹ abelian/cyclotomic ⟹ Stickelberger governs them, L-Stick lives)?

> **Answer: NO (generically). The `a≠0` eigenvalues are NON-ABELIAN over `ℚ`** — their splitting field
> is not even Galois over `ℚ`. So they are **not** cyclotomic, **not** Jacobi/Gauss sums, and classical
> Stickelberger does **not** factorize them. **L-Stick's premise is false for `a≠0`.**

---

## 2. Method and validation

1. `L*(a)` is irreducible degree-4 over `ℚ(ζ_n)`, and factors `[2,2]` over `K = ℚ(ζ_{12n})`
   (`anew_eigenvalue_identify_v1.sage`). So the splitting field is `K(√D₁, √D₂)`, `Dᵢ = disc` of the
   two quadratics.
2. **Kronecker–Weber criterion:** `K(√D)/ℚ` is abelian ⟺ `D ∈ ℚ*·(K*)²` (the only quadratic subfields
   of cyclotomic fields are `ℚ(√r)`, `r` rational). **Necessary condition (Galois over `ℚ`):**
   `σ(D)/D ∈ (K*)²` for every `σ ∈ Gal(K/ℚ)` (check generators of `(ℤ/12n)*`). Failure ⇒ not Galois
   ⇒ **not abelian**, definitively.
3. **Plant validation, in each field `K` used** (`anew_eigenvalue_verify_v4.sage`): `D=5` → passes
   (abelian ✓); `D=ζ_{12n}+2` → fails (non-abelian ✓). The discriminator is correct in the exact
   fields tested.

| prime | `n` | `K` | quad-discriminants `σ(D)/D∈K²`? | verdict |
|---|---|---|---|---|
| 13 | 7 | `ℚ(ζ_84)` | **pass** (both) | passes necessary cond. — small-`n` exception |
| **43** | 31 | `ℚ(ζ_372)` | **FAIL at σ₃₁₃** (both) | **NON-ABELIAN** |
| **67** | 79 | `ℚ(ζ_948)` | **FAIL at σ₇₉₃** (both) | **NON-ABELIAN** |

Two independent generic primes fail; the plants are correctly classified in those same fields. `p=13`
(`n=7`) is the small-case exception, not the generic behavior.

---

## 3. What this means — a coherent, corrected picture

- **The individual `a≠0` eigenvalues are GL(2)/big-monodromy type, not GL(1)/Hecke.** Non-abelian
  Frobenius is the signature of genuine 2-dimensional (modular-form-like) Galois structure — consistent
  with the sheaf being a true 4-dimensional deformation (`ANALYSIS_..._v1 §1`), whose `a=0` fiber is the
  CM/abelian degenerate case (`√p·μ₁₂`) and whose `a≠0` fibers turn on big monodromy.
- **The Hecke-character reading is falsified for generic `p`.** (The reasoning that spread is
  *compatible* with Hecke is correct — Jacobi sums spread and are cyclotomic — but the individual
  eigenvalues here are simply not abelian, so they are not Hecke values of a cyclotomic type. The
  "individual constants, not one absolute constant" refinement was the right correction to make; it just
  turns out the individuals aren't Hecke values either.)
- **The `ζ₃` ratio is cyclotomic even though the eigenvalues are not.** `α₂/α₁ = ζ₃` exactly (proved,
  `RESULT_n1_120deg_exact_v1.md`), a root of unity, while `α₁, α₂` individually generate a non-abelian
  field. **So the `120°` law's cyclotomic ratio is NOT an arithmetic fact about the eigenvalues — it is
  a relation *within* the GL(2) structure, i.e. a MONODROMY / geometric fact.** This is exactly the
  L-mono home, and it explains why every eigenvalue-arithmetic (Stickelberger) attempt was aimed at the
  wrong object.

---

## 4. Consequences for the route (updates `ANALYSIS_..._v3 §4`)

- **L-Stick (Stickelberger on the eigenvalues) is retired for the `a≠0` uniformity problem** — its
  premise is false. **Not wasted:** the `citation-verifier` result stands and remains valid for what it
  actually governs — the **`a=0` anchor** (supersingular `√p·μ₁₂` eigenvalues, which *are* Jacobi sums)
  and the separate Jacobi-sign-law result. The premise-check (this document) is exactly what stopped a
  mis-application of a correctly-verified citation to objects it does not govern.
- **L-mono (geometric monodromy) is now the primary route** to uniform `u=ζ₃`. The target: identify the
  `μ₃` in the geometric/arithmetic monodromy group of `L_{χ₂(y)} ⊗ L_{χ_a}` on `H¹_c` that forces the
  between-pair ratio to be a primitive cube root, uniformly in `a`.
- **§4b (the ω-descent) is an ingredient of L-mono, not a dead end.** `ω:(x,y)↦(ζ₃x,y)` puts a genuine
  `μ₃` into the arithmetic of the family (`L*(a)=L*(λa)`; `L*` over the index-3 subfield). It does not
  act *internally* on `H¹(F_a)` (still retracted), but it constrains the monodromy group to contain/
  commute with this `μ₃` — a real handle for the L-mono argument to build on. (So the v3 downgrade of
  §4b was correct that it is not *by itself* the order-pinning lever, but it is a live ingredient of the
  route that now matters.)

---

## 5. Scope

- `[VERIFIED — p=43, 67; plant-validated test]`. Not `[PROVED — all p]`; `p=13` (`n=7`) is an exception
  that passes the necessary condition (its full abelian-ness relied on a rougher rational-squarefree
  check). A wider sweep and a proof (why big monodromy for `a≠0`, generic `p`) are owed.
- This does **not** touch the proved per-cell `[PROVED-exact] u=ζ₃` (22 primes) — that stands; it only
  identifies the *mechanism* behind it as geometric, not eigenvalue-arithmetic.
- secp scale banner still governs.
