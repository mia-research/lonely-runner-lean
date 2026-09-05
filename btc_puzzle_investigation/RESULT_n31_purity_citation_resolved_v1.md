# RESULT — N31: the citation is REAL but MIS-STATED (the record quotes the *definition* of ι-purity as "théorème 3.2.3"); the theorem's actual hypothesis is checkable and HOLDS here by an elementary divisor-parity argument. N31 discharges as `[PROVED | Weil II 3.2.3(3)]`, uniformly in p. (A route replacing Weil II with Weil I exists but is NOT new — it is Kohel–Shparlinski's own method; corrected §5.)

**Date:** 2026-09-01.
**Grade:** `[PROVED — modulo the single cited input Weil II 3.2.3(3), citation VERIFIED VERBATIM this
session]` on the purity of `H¹_c(U, L_{χ₂(y)}⊗L_{χ_a})`, **uniform in `p>3, p≠7` and in `a`** —
therefore reaching secp. `[VERIFIED — exact]` on the refutation of
`RESULT_nonarchimedean_purity_statement_v1.md` §2. `[STANDARD — no novelty]` on the
Weil-I replacement route (§5; corrected same day against the KS primary source).
**Scripts:** `scratchpad/n31/newton_polygon_check_v1.py`, `scratchpad/n31/purity_citationfree_widen_v1.py`,
`scratchpad/n31/sweep_v1.py`. Exact integer arithmetic throughout; no float (`check_no_float` register).
**Supersedes in part:** `RESULT_nonarchimedean_purity_statement_v1.md` (§2 retracted, §5 verdict
survives on a different argument).

---

## 0. What N31 is

The cap chain (`RESULT_n1_cap_reduces_to_one_identity_v1.md` §1–2) consumes exactly one analytic input:

> **(N31)** the four Frobenius eigenvalues `α₁..α₄` of the char-poly `L*(a,T)` satisfy `|α_i| = √p`
> — i.e. `H¹_c(U, F)` with `F = L_{χ₂(y)} ⊗ L_{χ_a}` is **pure** of weight 1, not merely mixed of
> weight ≤ 1.

Purity is what puts the roots of the normalised `P(W)` on `|W|=1`; combined with the (now proved, P32)
identity `e₂ = e₁² − χ₂(−1)p` it yields `|ε| ≤ 2`, i.e. the cap `|V_y(a)| ≤ 2√p`. Mixed-of-weight-≤1
is **not enough**: it would give `|α_i| ≤ √p` and the palindromic/discriminant step fails.

The record graded this `[CITED — TO VERIFY, ×4 failed]`.

## 1. Why the verifier failed four times: the record quotes a DEFINITION as the theorem

`RESULT_nonarchimedean_purity_statement_v1.md` §2 states:

> *"Deligne, Weil II (1980), théorème 3.2.3. Let `F₀` be a pure ℓ-adic sheaf of weight `w` on a variety
> `X₀/F_q`. For every closed point `x∈|X₀|` and every embedding `ι:Q̄_ℓ↪C`, every eigenvalue `α` of the
> geometric Frobenius `Frob_x` acting on `F_x̄` satisfies `|ι(α)| = q_x^{w/2}`."*

**That is not théorème 3.2.3. It is the definition of ι-purity.** Compare Katz, *L-functions and
monodromy: four lectures on Weil II* (AWS 2000 / Princeton), Lecture 1, verbatim:

> *"we say that `Ï` is `“`-pure of weight `w` if the following condition holds. For every finite
> extension field `E/k`, for every point `x` in `(X/k)(E)`, we have `|every eigenvalue of
> ρ_Ï(Frob_{E,x})|“ = Sqrt(#E)^w`."*

Identical content. So the record's "citation" is a **tautology applied to the wrong object**: it says a
pure sheaf has pure stalks, and says nothing whatever about the Frobenius eigenvalues on the
**cohomology group** `H¹_c`, which is what the cap consumes. A verifier looking for that statement at
3.2.3 will not find it — four times. **The ×4 failure is diagnosed: the citation was unfindable because
it was not a theorem.**

## 2. What Weil II 3.2.3 actually says `[CITATION VERIFIED — verbatim, this session]`

Katz, *op. cit.*, Lecture 1, verbatim:

> **Target Theorem (Deligne).** *`U/k` a smooth, geometrically connected curve over a finite field, `…` a
> prime invertible in `k`, `Ï` a lisse `Q̄_…`-sheaf on `U` which is `“`-pure of weight `w`. Then
> `H¹_c(U⊗_k k̄, Ï)` is `“`-mixed of weight `≤ w+1`.*
>
> **Corollary [De-Weil II, 3.2.3]**
> *1) `H¹(U×_k k̄, Ï)` is `“`-mixed of weight `≥ w+1`.*
> *2) If the "forget supports" map `H¹_c(U×_k k̄, Ï) ≅ H¹(U×_k k̄, Ï)` is an isomorphism, then
> `H¹_c(U×_k k̄, Ï)` is `“`-pure of weight `w+1`.*
> *3) For `C/k` the complete nonsingular model of `U/k`, `j: U → C` the inclusion, and every
> `0 ≤ i ≤ 2`, `H^i(C⊗_k k̄, j_*Ï)` is `“`-pure of weight `w+i`.*

and, in the same lecture,

> *`H¹(C⊗_k k̄, j_*Ï) = Image(H¹_c(U⊗_k k̄, Ï) → H¹(U⊗_k k̄, Ï))`, `H⁰_c(U⊗_k k̄, Ï) = 0` [for `U`
> affine], `H²(U⊗_k k̄, Ï) = 0`.*

**So the theorem number in the record is the right one to reach for — but the usable statements are
3.2.3(2)/(3), and both carry real content the record never engaged.** 3.2.3(2) in particular has a
**hypothesis** — the forget-supports isomorphism — which nobody in this corpus has checked. N31 was
never a bare citation debt; it was an unchecked hypothesis wearing a citation's clothes.

## 3. The hypothesis holds here — elementary, and uniform in `p` `[PROVED-here]`

**The object.** `E: y²=x³+7` over `F_p`, `p>3`, `p≠7`. `div(y) = (P₁)+(P₂)+(P₃) − 3·(O)` with `P_i` the
three geometric 2-torsion points (`x³=−7`, distinct since `disc(x³+7)=−27·49 ≠ 0`). So `L_{χ₂(y)}` is
lisse exactly on

> `U = E ∖ E[2]` — **four** geometric punctures: `O, P₁, P₂, P₃`,

and `L_{χ_a}` (the **Lang-torsor** sheaf of the character `χ_a` of `E(F_p) ≅ Z/n`) is lisse on all of `E`
— the Lang isogeny `Frob−1` is finite **étale**, so `L_{χ_a}` is unramified at every point. Put
`F = L_{χ₂(y)} ⊗ L_{χ_a}`, rank 1, lisse on `U`, pure of weight 0.

**Dimension check (GOS).** All ramification is tame (Kummer), so
`χ_c(U,F) = 1·(2−2g−#punctures) − Σ Swan = (2−2−4) − 0 = −4`, and with `H⁰_c = H²_c = 0`
(`F` geometrically nontrivial) this gives **`dim H¹_c(U,F) = 4`** — matching the record's degree-4
char-poly `L*(a,T)`, independently.

**The local invariants vanish.** The stalk of `j_*F` at a puncture `x` is `F^{I_x}`. Here `I_x` acts on
the rank-1 `F` through the tame character `χ₂^{ord_x(y)}` (the `L_{χ_a}` factor contributes trivially,
being unramified). And

| puncture | `ord_x(y)` | parity | `χ₂^{ord_x(y)}` |
|---|---|---|---|
| `O` | `−3` | odd | `χ₂ ≠ 1` |
| `P₁,P₂,P₃` | `+1` | odd | `χ₂ ≠ 1` |

**Every `ord_x(y)` is odd, so `I_x` acts non-trivially at all four punctures, so `F^{I_x} = 0` at all
four.** This is a divisor-parity fact about `y` on a Weierstrass curve — it holds for **every `p>3,
p≠7` and every `a`**, with no measurement and no scale dependence.

**Conclusion.** From the stalk-level exact sequence
`0 → j_!F → j_*F → ⊕_{x∈C∖U} i_{x*}(F^{I_x}) → 0` and `H^i(C, j_!F) = H^i_c(U,F)`, the long exact
sequence with `H⁰_c(U,F) = 0` and `H⁰(U,F) = F^{π₁^{geom}} = 0` gives

> `0 → ⊕_x F^{I_x} → H¹_c(U,F) → H¹(C, j_*F) → 0`.

With `⊕_x F^{I_x} = 0` this is an isomorphism `H¹_c(U,F) ≅ H¹(C, j_*F)`, which is **ι-pure of weight 1
by Weil II 3.2.3(3)**. Hence `|α_i| = √p` for all four eigenvalues, every `a`, every `p`. ∎

> **N31 regrade proposed: `[CITED — TO VERIFY, ×4 failed]` → `[PROVED | Weil II 3.2.3(3)]`,** the cited
> input now verified verbatim (§2), the previously-unstated hypothesis discharged by §3.
> **This is a form-level claim in the sense of the v3 scale banner** — the argument contains no measured
> input and no `p`-dependence, so it reaches `2²⁵⁶`. The cap `|V_y(a)| ≤ 2√p` therefore joins the
> carve-out list, *conditional on the second input* — see §6.

## 4. `RESULT_nonarchimedean_purity_statement_v1.md` §2 is REFUTED (exactly) `[VERIFIED — exact]`

That document asserts:

> *"Non-archimedean / `p`-adic places: the same `|α_i|_ν = p^{1/2}` at every finite place `ν`. …
> Equivalently, the Newton polygon of the char-poly `L_a(T)` at the prime `p` has all slopes `= 1/2`
> (the slopes of a pure-weight-1 Frobenius), and at every `ℓ≠p` the `α_i` are `ℓ`-adic units."*

Three defects, in increasing severity:

1. **Category error.** In Weil II, `ι` ranges over embeddings `Q̄_ℓ ↪ C` — these are **archimedean**
   absolute values. ι-purity has **no non-archimedean content whatever.** "Purity at every embedding"
   is not "purity at every place."
2. **Internal contradiction.** The passage asserts `|α_i|_ν = p^{1/2}` at *every* finite place and, one
   clause later, that the `α_i` are `ℓ`-adic **units** (`|α_i|_ℓ = 1`) for `ℓ≠p`. Both cannot hold.
   (The unit half is the correct one — `∏α_i = e₄ = p²`.)
3. **The Newton-polygon claim is FALSE, and is refuted exactly.** With the record's own forced
   coefficients (`e₄=p²`, `e₃=χ₂(−1)p·e₁`) and the P32 identity (`e₂=e₁²−χ₂(−1)p`), the Newton polygon
   of `L_a(T)` at a prime `π | p` of `Z[ζ_n]` has vertices `(0,2),(2,0),(4,0)` whenever `v_π(e₁)=0`,
   i.e. **root valuations `{0,0,1,1}` — the ordinary shape, not `{½,½,½,½}`.** "All slopes `1/2`" is the
   *supersingular* condition; it is an extra, and generically false, assertion.

   `v_π(e₁)=0` for **every** `a` and every `π|p` iff `p ∤ N(e₁) = Res(Φ_n, f)`, an exact integer
   (`newton_polygon_check_v1.py`, exact, no float):

   | `p` | `n` | `v_p(N(e₁))` | `v_π(e₁)=0` for all `a`? |
   |---|---|---|---|
   | 43 | 31 | 0 | **yes** |
   | 67 | 79 | 0 | **yes** |
   | 79 | 67 | 0 | **yes** |
   | 127 | 127 | 3 | no (holds for all but a few conjugates) |
   | 163 | 139 | 0 | **yes** |

   So at 43/67/79/163 the claimed all-`½` Newton polygon fails for **every single `a`**.

**Disposition.** §2 of that document is **RETRACTED**. Its §5 verdict ("no non-trivial finite-place
computation remains") **survives**, but on a different and correct ground: *no finite-place condition is
posited or consumed anywhere in the programme*, so there is nothing to compute — **not** because purity
supplies one for free.

**A fourth, minor defect** in the same document, §1: it writes the object as
`H¹_c(E_{F̄_p}, L_{χ₂(y)}⊗L_{χ_a})` — cohomology of the **whole** `E`, where the sheaf is not lisse
(§3: it is lisse only on `E∖E[2]`) — and describes `L_{χ_a}` as *"the Kummer (Artin–Schreier–Witt)
sheaf for the order-`n` character `χ_a` of `(Z/n)^×`"*. It is the **Lang-torsor** sheaf of a character of
`E(F_p) ≅ Z/n` — not Kummer, not Artin–Schreier–Witt, and not a character of `(Z/n)^×`.
`weil_deligne_character_bound_v1.md` §2 gets this right; the two documents disagree and the earlier one
is correct.

## 5. The Weil-I replacement route (the triage's "Move 1", now sharpened) `[HYPOTHESIS]`

`F = L_{χ₂(y)} ⊗ L_{χ_a}` has **finite** monodromy: its `π₁(U)`-representation lands in `μ₂ · μ_n`, of
order `2n`. A rank-1 sheaf with finite monodromy is the `χ`-isotypic component of `π_*Q̄_ℓ` for `π` the
corresponding finite abelian cover — here the fibre product of the Lang-torsor cover of `E` (degree `n`,
étale) with the double cover `w² = y`, i.e. `w⁴ = x³+7`. By §3, `H¹_c(U,F) = H¹(C, j_*F)`, and this is
the `χ`-isotypic piece of `H¹(Ṽ, Q̄_ℓ)` for `Ṽ` the smooth projective model of that cover. **Purity
there is Weil's 1948 Riemann Hypothesis for curves** — Weil I, not Weil II, with elementary
(Stepanov–Bombieri) proofs available.

**⚠ CORRECTED 2026-09-01 (same day), on reading the primary source — this route is NOT new.** Kohel &
Shparlinski, *On Exponential Sums and Group Generators for Elliptic Curves over Finite Fields* (ANTS-IV,
LNCS 1838, 2000), **already use exactly this method** for the sibling (additive) sum: their Proposition 1
is the conductor/degree formula for the L-function of a divisor-group character (citing Bombieri Thm A /
Weil, *Basic Number Theory* Ch. 7 Thm 6), and their **Proposition 2 is the Riemann Hypothesis for function
fields** — *"each zero satisfies `|ϑ_i| = q^{1/2}`"*. So "replace Weil II by Weil I" is not a discovery;
it is the published approach, and the record's own `weil_deligne_character_bound_v1.md` is a cohomological
re-derivation of it. **Regrade of this §5: `[HYPOTHESIS — citation-verifier owed]` → `[STANDARD — KS
Prop. 1 + Prop. 2; no novelty]`.** The route is *correct* and does discharge N31 without Weil II; it is
simply not new, and must not be presented as such.

## 6. What is still owed — do not over-read this document

- **The cap is not yet unconditional at secp.** It rests on **two** inputs: purity (this document,
  now `[PROVED|3.2.3(3)]` and scale-free) **and** the identity `e₂ = e₁² − χ₂(−1)p`. The identity is
  `[PROVED — symbolic, uniform]` via P32 (`RESULT_26_PROVED_weil_restriction_v1.md`), whose own
  **owed isolated re-run** is still outstanding. Until that is discharged the cap does **not** join the
  v18 carve-out list. This document moves one of the two legs, not both.
- **The Katz–Sarnak citation is still unverified.** `RESULT_nonarchimedean_purity_statement_v1.md` §1
  cites *"Katz–Sarnak, Random Matrices, Prop. 2"*. I could not locate a "Prop. 2" matching this use and
  did **not** verify it. It is **not refuted** — it is unverified, and it is now also **unnecessary**
  (§3 uses only Weil II 3.2.3(3)). Recommend striking it rather than chasing it.
- **No grade is moved in any master by this document.** The N31 regrade in §3 and the retraction in §4
  are *proposed*; folding either into `POSITIVE_FINDINGS_MASTER_v18.md` requires the `compile-diff`
  gate, and the N31 up-move requires `citation-verifier` on §2 (CLAUDE.md §2 — a grade resting on a
  citation), notwithstanding that §2 is quoted verbatim here.
- **This says nothing about ECDLP.** It bounds a character sum over the public curve. The cap is a
  statement about `|V_y(a)|`; the indexical→operational barrier is untouched.

## 7. Independent empirical leg (citation-free), widened

`RESULT_item6_D2_and_purity_v1.md` §3 established a **decidable, citation-free** purity test on the
Galois-stable `R(T) = ∏_{a=1}^{n−1} P_a(T) ∈ Z[T]` and explicitly noted the scope "can be widened by
compute rather than by reading." It never was. `purity_citationfree_widen_v1.py` reimplements it
independently (exact: `R = Res_X(Φ_n, P(X,T))`; functional equation `R = T^m Q(T+p/T)`; Sturm
real-root count on the squarefree part; band test via `Q̂(V) = Res_S(Q, V−S²)` with the **integer**
endpoint `4p`), reproduces `p=43` (`deg R = 120`, PURE) and is sweeping upward.

Landed so far: `p = 13, 43, 61` — **PURE**, both `χ₂(−1)` branches. (`p=13` is the `χ₂(−1)=+1`
palindromic branch, absent from item 6's `{43,67,79,127}`.) Sweep in flight.

*This leg is corroboration only. The §3 argument is uniform in `p`; no finite sweep adds to it.*

---

## 8. Grades

| item | grade |
|---|---|
| Weil II 3.2.3 statement (parts 1/2/3) as quoted in §2 | `[CITATION VERIFIED — verbatim, Katz AWS-2000 Lecture 1]` |
| the record's §2 form of "théorème 3.2.3" is the *definition* of ι-purity | `[VERIFIED — documentary]` |
| `F^{I_x} = 0` at all four punctures (odd divisor parity of `y`) | `[PROVED-here]`, uniform in `p, a` |
| `dim H¹_c(U,F) = 4` by GOS | `[PROVED-here]` (independently reproduces the record's quartic) |
| **N31: `H¹_c(U,F)` pure of weight 1, all `a`, all `p>3, p≠7`** | **`[PROVED \| Weil II 3.2.3(3)]`** |
| `…nonarchimedean_purity…v1` §2 Newton-polygon claim | **`[REFUTED — exact, 4 primes, every `a`]`** |
| `…nonarchimedean_purity…v1` §1 sheaf identification | `[REFUTED — documentary]` |
| Weil-I replacement route (§5) | `[STANDARD — no novelty; = Kohel–Shparlinski Prop. 1 + Prop. 2]` |
| cap `\|V_y(a)\|≤2√p` unconditional at secp | **still `[OPEN]`** — second leg (P32 isolated re-run) owed |

*Register: purist. No ECDLP content. Exact arithmetic; no float.*
