# RESULT — #26 IS PROVED. The mechanism is Galois descent on `E[2]`, not a pointwise symmetry.

**Date:** 2026-08-01.
**Grade: `[PROVED]`** for the theorem below — a symbolic/structural proof, valid at every `p > 3`,
with one link (closure of the canonical lifts into a Klein four-group) carrying an explicit
geometric construction plus exhaustive verification; that link is named in §5 and is not hidden.
**Scripts:** `jac26_zeta_and_branch_v2.sage`, `jac26_decomposition_v3.sage`, `jac26_quotient_v4.sage`,
`jac26_symbolic_and_endtoend_v5.sage`, `jac26_endtoend_v6.sage`,
`jac26_intonly_crosscheck_v1.py` (independent, division-free, passes `check_no_float.py`).

---

## 0. Statement

> **Theorem.** Let `p > 3` and let `E/F_p : y² = x³ + Ax + B` be nonsingular with `n = #E(F_p)`
> **odd**. Then for every `R ∈ E(F_p)`, `R ≠ O`,
>
> **`Σ_{λ ∈ F_p} χ₂(G_R(λ)) = 0` exactly**, where `G_R = D_R · F_R`,
> `D(λ) = λ⁴ − 6x_Rλ² − 8y_Rλ − 3x_R² − 4A`, `F(λ) = y_Rλ³ + (A+3x_R²)λ² + 3x_Ry_Rλ + y_R²`.
>
> Equivalently `h₂[e] = (h₁∗h₁)[e]` for every `e ≠ 0`, hence
> **`V₂(a) = V₁(a)² − 2χ₂(−1)p` and `e₂(a) = e₁(a)² − χ₂(−1)p` for every `a`** — i.e. **#26 holds,
> uniformly in `a` and in `p`.** The 120° law is a theorem.

**The hypothesis is `n` odd. It is NOT `j = 0`.** secp256k1 has odd prime `n`, so it is covered;
so is every odd-order curve, `j = 0` or not.

## 1. Why the previous session's exhaustive negative did not apply

`RESULT_26_G_explicit_and_symmetry_group_trivial_v1.md` §2 searched all `7·6·5 = 210` Möbius maps
**permuting `G`'s seven roots** and found only the identity, concluding *"no Möbius symmetry of `G`
exists at all, over the algebraic closure"* and *"the odd-symmetry programme is dead, completely."*

`deg G = 7` is **odd**, so the branch locus of `C : w² = G(λ)` is **eight** points — the seven roots
**and `∞`**. The relevant group is the stabiliser of that 8-point set, and its elements need not fix
`∞`. `tors2_fp3_symmetry_v2.py:71` rejects exactly those (`u is None` ⇒ `bad = True`), so the search
covered only the point stabiliser of `∞` — precisely the subgroup that **excludes the mechanism**.

Redone correctly over all `8·7·6 = 336` triples, the stabiliser has **order 4**, not 1
(p = 43, 67, 79; `j = 0` and generic `j`). The three nontrivial elements are the `E[2]`-translations,
each acting on the 8-point locus as **four transpositions** — in particular each swaps `∞` with a
root of `F`, which is why the 7-root search could not see them.

This also reverses that file's retirement of the `E[2]`-translation candidate: `τ_T` does not
permute `G`'s seven roots, but it does permute the branch locus, which is the condition that matters.

## 2. The two objects, symbolically

With `A, B, x_R, y_R` free indeterminates modulo `y_R² = x_R³ + Ax_R + B`
(`jac26_symbolic_and_endtoend_v5.sage`, exact algebra over `ℚ`):

- `x₁+x₂ = λ² − x_R`, `x₁x₂ = x_Rλ² + 2y_Rλ + A + x_R²`, hence `D = (x₁−x₂)²` and `F = y₁y₂` are the
  polynomials above — **polynomial identities, hence valid at every `p > 3`.**
- **`Res(D,F) = (4A³ + 27B²)²`** and **`disc(D) = −4096·(4A³ + 27B²)`.**

So `D` and `F` are coprime and separable **for every nonsingular `E` and every `R`** — no exceptional
locus. `n` odd ⇒ no rational 2-torsion ⇒ `y_R ≠ 0` ⇒ `deg G = 7`. **`G` is squarefree of degree 7,
unconditionally**, so `C : w² = G(λ)` is a hyperelliptic curve of genus 3 with `#C(F_p) = p + 1 + Σχ₂(G)`.

## 3. The reduction (elementary, and re-verified)

For `λ` with `D(λ) ≠ 0`, the pair `{P₁,P₂}`, `P₁+P₂ = R`, is rational iff `χ₂(D(λ)) = +1` and a
conjugate pair iff `−1`; in both cases `y₁y₂ = F(λ) ∈ F_p`. Hence

`Σ_λ χ₂(D·F) = Σ_rational,distinct χ₂(y₁y₂) − Σ_conjugate χ₂(y_P y_{φP})`,

which is the reduction doc's S1–S3 target. Verified independently at 8 curves (`jac26_endtoend_v6`, L1).

## 4. The branch locus is two free `E[2]`-orbits

`λ(P)` = slope of the line through `P`, `R−P`, `−R`; it is the quotient map for `ι(P) = R − P`.

- roots of `F` ⟺ `y₁y₂ = 0` ⟺ `P₁ ∈ E[2]\{O}`; and `λ(O) = ∞`.
- roots of `D` ⟺ `P₁ = P₂` ⟺ `2P₁ = R`, i.e. `P₁ ∈ P₀ + E[2]`.

`λ` is injective on each set (`E[2]` meets each `ι`-orbit once since `R ∉ E[2]`; `P₀+E[2]` are the
four distinct fixed points of `ι`). Therefore

> **`B = λ(E[2]) ⊔ λ(P₀ + E[2])`** — eight points, two disjoint 4-element sets.

Verified exactly (`jac26_quotient_v4`, T5: `|λ(E[2])| = |λ(P₀+E[2])| = 4`, disjoint, union `= B`).

## 5. The automorphisms, and why they are forced

For `T ∈ E[2]`, `τ_T(P) = P+T` commutes with `ι` (as `2T = O`), so it descends to `σ_T ∈ PGL₂`.
`T ↦ σ_T` is injective, giving `V ≅ (ℤ/2)² ⊂ PGL₂`. `τ_T` preserves `E[2]` and preserves `P₀+E[2]`
(since `2(P₀+T) = R`), and acts **simply transitively** on each. Hence:

> each `σ_T` (`T ≠ O`) acts on `B` as **four transpositions — fixed-point-free**.

**The lift is automatic.** Let `M` represent `σ_T` with `M² = δ·I`, and let `Φ` be the degree-8 form
with root set `B`. The eight linear forms of `B` split into four `M`-swapped pairs `{L, L'}` with
`L∘M = αL'`, `L'∘M = α'L`, and `L∘M² = δL` forces `αα' = δ`. Therefore

> **`Φ∘M = δ⁴·Φ`, i.e. `ν = (δ²)²` is a square — always.**

So `σ̃_T : (λ,w) ↦ (σ_T(λ), δ²w/(cλ+d)⁴)` is defined over `F_{p³}`, and `σ̃_T² = id` (using
`cσ_T(λ)+d = δ/(cλ+d)`). *[Verified: `ν` a square and `M² = id` in 100% of computed cells.]*

*The one link resting on construction + verification rather than a symbolic identity:* that the three
canonical lifts **close into a Klein four-group** `Ṽ ≅ V`. Geometrically this is forced —
`B` being two free `V`-orbits makes `C` the pullback of a double cover of `P¹/V` branched at the two
image points, on which `V` acts through the base — and it is verified in every computed cell
(7 cells × 3 lifts, `p = 43,67,79`, both `j` classes). It is stated here rather than buried.

## 6. Genus, and the trace

`H¹(C,Q_ℓ)` is 6-dimensional and decomposes under `Ṽ` into the four characters, with
`dim H¹_triv = 2g(C/V)` and `dim H¹_{χ_i} = 2g(C/σ̃_i) − 2g(C/V)`. Since `σ_T` is fixed-point-free
on `B`, its two `P¹`-fixed points are unbranched, so Riemann–Hurwitz gives
`g(C/σ̃_i) = (8 − r)/4` with `r ∈ {0,4}`, i.e. `g(C/σ̃_i) ∈ {1,2}`. The three are Galois-conjugate,
hence share a genus `g'`, and `6 = 6g' − 4g(C/V)`:

- `g' = 2` ⇒ `g(C/V) = 3/2`, **impossible**;
- `g' = 1` ⇒ `g(C/V) = 0`. ∎

So `dim H¹_triv = 0` and `dim H¹_{χ_i} = 2` for each `i`, and `H¹ = H¹_{χ₁} ⊕ H¹_{χ₂} ⊕ H¹_{χ₃}`.

**`n` odd ⟺ `x³+Ax+B` irreducible over `F_p`** (a cubic has no rational root iff irreducible; a
rational root is a rational 2-torsion point). Its splitting field is then `F_{p³}` with
`Gal ≅ ℤ/3` permuting `T₁,T₂,T₃` **cyclically**. Frobenius conjugates `σ̃_{T} ↦ σ̃_{Frob(T)}`, so it
permutes the three eigenspaces cyclically. **A linear map permuting three summands of a direct sum
cyclically has zero diagonal blocks, hence trace 0:**

> **`Tr(π | H¹(C)) = 0` ⇒ `#C(F_p) = p+1` ⇒ `Σ_λ χ₂(G_R(λ)) = 0`.** ∎

Everything above is confirmed numerically: `Ch(T) = T⁶ − c₃T³ + p³` (so `c₁ = c₂ = 0`),
`#C(F_{p³}) = p³+1−3c₃`, and the three quotients are genus 1 with
**`a(E_i/F_{p³}) = c₃` for all three** — i.e. `Jac(C) = Res_{F_{p³}/F_p}(E₁)`.

## 7. Evidence table

| test | scope | result |
|---|---|---|
| `c₁ = c₂ = 0` (P1, P2) | **749 cells**, 15 curves, `p ≤ 211`, `j=0` + generic `j`, all `p≡3 mod 4` | **0 violations** |
| `c₁ = c₂ = 0`, `p ≡ 1 mod 4` | **265 cells**, 10 curves | **0 violations** |
| `Ch(T) = T⁶ − c₃T³ + p³`, `#C(F_{p³}) = p³+1−3c₃` | 4 curves × several `R` | exact |
| three genus-1 quotients, `a(E_i/F_{p³}) = c₃` | 7 cells × 3 lifts | exact, all three |
| branch group order 4, `ν` square, `M² = id`, Frobenius 3-cycle | 4 curves | exact |
| full chain L1–L5 → `V₂ = V₁² − 2εp` | 8 curves, both `ε`, **516 frequencies** | **0 failures** |
| **CONTROL: even `n` ⇒ trace ≠ 0** | **117 cells**, 5 curves | **0 pass; 109 have `c₁ ≠ 0`** |
| integer-only independent path (no division) | 18 cells | reproduces Sage exactly |

**The control is the point.** The proof says the vanishing comes from Frobenius 3-cycling `E[2]`.
If `n` is even, some `T_i` is rational, the 3-cycle degenerates, a diagonal block survives, and the
trace must be nonzero. It is — in every one of 117 even-`n` cells. The mechanism predicts its own
failure mode and the failure mode occurs.

## 8. What this settles, and what it does not

**Settles.** #26 — *"the one genuinely open structural link"*, *"the load-bearing open fact"* — is
proved, uniformly in `a` and `p`. The cap chain `120° ⇒ V₂ = V₁²−2εp ⇒ S_y ≤ 2 ⇒ |V| ≤ 2√p` now has
**no open link on the 120° side**. The 2464 census cells graded `[PROVED-exact], conditional` are
unconditional on this input. The Kronecker/Stickelberger ideal route is **not needed** and should not
be pursued: the mechanism is Galois descent on `E[2]`, not an abelian ideal relation.

**Explains a prior measurement.** `RESULT_jclass_B_relevance_check_v1.md` measured generic-`j` odd-`n`
**30/30 pass** and generic-`j` even-`n` **0/12**, concluding *"prime order was never the requirement —
ODD CYCLIC `n` is."* That is exactly the hypothesis of this theorem and exactly the control's failure
mode. The data was collected before the mechanism was known.

**Explains why five elementary mechanisms failed.** §1 of `NOTE_26_status_v1.md` ruled out pointwise
antisymmetry, simple characters, multiset bijections, coset characters, and the `s₁` setup. The
mechanism is a **Galois-descent statement about `Jac(C)`**, not a pointwise pairing on `F_p`-points —
the `σ_T` are not `F_p`-rational, so no pairing of rational points can exist. Those searches were
correct and were looking for an object that provably is not there.

**Does not settle.** This is a statement about `E` over `F_p` for a single `p`; it proves the
*rigidity*, and it says nothing about any statistic outside the `V₁/V₂` collapse. It does not touch
the non-algebraic index channel (`d ↦ d⁻¹`, `d ↦ d^k`), the `2^128` incomplete-sum regime, or the
`μ₃`-forced subspace. It is not a claim about `2^256`, and it is not a cryptographic result in
either direction. It closes one named mathematical question: object = the twisted L-polynomial
coefficients `e₁,e₂`; class = the 120° eigenvalue configuration; power = exact, symbolic; scope =
every nonsingular `E/F_p`, `p > 3`, with `n` odd.

## 9. Process notes

- **Gates.** No `experiment-designer` prereg: this is a verification of a proof, not a leakage test,
  sweep or drill. `citation-verifier` is **not owed** — the final proof uses only Riemann–Hurwitz and
  the character decomposition of `H¹` under a finite group; the Kani–Rosen route was drafted and then
  **removed** as unnecessary, so no grade rests on it.
- **`check_no_float.py`** flags the finite-field `/` in the Sage scripts (AST cannot distinguish exact
  field division). Rather than exempt them, `jac26_intonly_crosscheck_v1.py` recomputes the headline
  quantities with **no division at all**, passes the guard, and reproduces the Sage numbers exactly.
- **Two bugs were caught by controls, not by reading.** (i) `0.is_square()` is `True` in Sage, so a
  pair with `y₁y₂ = 0` scored `+1`; only reachable with rational 2-torsion, so the **even-`n` control
  found it** and the odd-`n` arm never would have. (ii) `tuple(P)` on a Sage curve point is the
  *projective triple*, so a 2-tuple index silently matched nothing and zeroed a whole stratum. Both
  produced loud failures rather than plausible numbers.
