# MAP — the supersingular cover object `A_new`, at secp, as an ECDLP lever candidate

**Date 2026-07-19.** Corrects a dismissal in `RESULT_external_review_idea_tests_v1.md` §1 (which closed
the χ₂(y)-cohomology thread as "geometric, not CM, bound-irrelevant"). Per the anomaly-drill protocol:
below is a **characterization + a lever candidate + the exact scope of each obstruction + next probes**,
**not** a verdict either way. Supersingular ≠ dismissable — it is the classical ECDLP weakness.
Computation: inline Sage (recorded in session log); `mu6_cohomology_split_v2.py` (P-A geometric law).

---

## 1. The object, and that it is SECP-REAL `[VERIFIED]`

The DLP-relevant χ₂(y) sum `V(a) = Σ_{P∈E} χ₂(y_P) e_n(a·d(P))` lives on the cover
**`C : w⁴ = x³ + 7`** (`w² = y`), whose Jacobian is isogenous to **`E × A_new`**, `A_new` an abelian
surface (`dim 2`, `= H¹_new`).

- **P-A `[VERIFIED, geometric]`:** `A_new` is **supersingular ⟺ `p ≡ 3 mod 4`** — forced by
  `Q(i) ⊂ End⁰(A_new)` from the μ₄ automorphism `w→iw` (holds for **any** cubic; a geometric fact, so
  it holds at **every** `p`, including `2²⁵⁶`).
- **secp:** `p = 2²⁵⁶−2³²−977`, `p ≡ 3 (mod 4)`, `p ≡ 1 (mod 3)`. Therefore **at secp: E is ORDINARY,
  `A_new` is SUPERSINGULAR.** Not a small-`p` artifact — the scale banner does **not** neutralize this.
- **`A_new`'s internal DLP is easy `[VERIFIED small p]`:** MOV embedding degree `k = ord_ℓ(p) = 3` at
  every tested supersingular prime (`p = 31,43,67,79,103,127,139`; `p=19` degenerate). So the DLP in
  `A_new(F_p)` reduces via the pairing to `F_{p³}*` — subexponential (NFS), vastly below the generic
  `√p ≈ 2¹²⁸` of `E`. **A supersingular, easy-DLP surface sits in the Jacobian of a degree-4 cover of E,
  at the real curve.**
- **Exact eigenvalues, not a bound.** Supersingular ⇒ the `H¹_new` Frobenius eigenvalues are **exactly**
  `√p·ζ` (roots of unity), not merely `|·| ≤ 4√p`. The χ₂(y) cohomology is maximally rigid at secp.

## 2. The lever candidate (what would make it a search-space reduction)

A cover `C → E` with an **easy-DLP** factor `A_new` in `Jac(C)` is the shape of a cover / Weil-descent
transfer: if a point `P = [d]G ∈ E(F_p)` can be moved to `A_new(F_p)` by an efficiently computable map
that carries the discrete-log information, then `d` is recovered in `A_new` (via the `k=3` pairing) at
`F_{p³}`-cost. The raw material is present and secp-real (§1). The question is the **transfer map**.

## 3. What is CLOSED, and its exact scope (a named mechanism, killed — not the lever)

**Homomorphic transfer `E → A_new` is zero `[PROVED, secp-valid]`.** `E` ordinary has Frobenius
eigenvalues `π, π̄` with `|π|=√p`, `π+π̄=a_p≢0`; `A_new` supersingular has eigenvalues `√p·ζ`
(supersingular Weil numbers). They **share no Frobenius eigenvalue**, so by Tate's isogeny theorem
`Hom(E, A_new) ⊗ ℚ_ℓ = 0`, hence `Hom(E, A_new) = 0`. Equivalently: incompatible Newton slopes
(`{0,1}` vs `{½,½}`). **A group homomorphism from `⟨G⟩` into the easy group does not exist.**

**Scope of this closure — and only this.** It kills exactly the *homomorphic* cover attack. It says
**nothing** about (i) a non-homomorphic set-correspondence, or (ii) the character-sum-value route (§4).
This is the **same shape as the OPEN §X.3 amicable lever**: there too the homomorphic case is zero for a
stated reason and the non-homomorphic correspondence is unanalyzed. **Two open leads, one structure.**

## 4. What is OPEN (the doors the closure does not touch)

- **(D1) The non-homomorphic lift correspondence.** `P=(x,y) ↦ (x, w=√y) ∈ C(F_p)` (defined on the
  `y`-QR half of `E(F_p)`) `↦` its `A_new`-component `Q(P)`. This is a **set map, not a homomorphism**,
  so the slope/Tate obstruction of §3 does not constrain it. **Open question:** does `Q(P)` retain
  enough of `d` that `A_new`'s easy DLP recovers a partial `d` (a coset / a bit-band / a modular
  constraint)? `[GAP — no analysis in hand]`.
- **(D2) The Lang-torsor twist bridge.** §1's supersingular rigidity is on the **untwisted** `H¹_new`.
  The DLP sum `V(a)` uses the **twisted** sheaf `L_{χ₂(y)} ⊗ L_{χ_a}`. **Open question:** does the
  supersingular / exact-`√p·ζ` structure survive the twist? If yes, `V(a)` takes **exact algebraic
  values** at secp (not just `≤4√p`), and their `a`-dependence is a structured object to invert. This is
  the review's un-asked bridge question. `[OPEN]`.

## 5. Next probes (find, not verdict)

1. **Compute D1 at a small `p ≡ 7 mod 12` with `E` prime-order** (`E` ordinary, `A_new` supersingular):
   build the cover, the Prym projection `Jac(C)→A_new`, and the lift `P↦Q(P)`; measure whether `Q(P)`
   as a function of `d` is structured — e.g. constant on cosets, or its `A_new`-discrete-log correlates
   with `d`. Decidable: matched null = random relabeling of `d`.
2. **Compute D2** — the twisted eigenvalues of `L_{χ₂(y)}⊗L_{χ_a}` (Sage étale/`L`-function of the
   twisted sheaf, or direct `V(a)` values across `a` at small supersingular `p`): are they exact
   `√p·ζ`, and structured in `a`?
3. **Fraction that lifts.** Quantify `#{P∈⟨G⟩ : y_P is QR}` and whether the lift is usable on a
   generator's orbit.
4. **Unify with §X.3.** Run D1 and the amicable non-homomorphic correspondence with the *same*
   instrument; if both are the "supersingular/easy factor + non-homomorphic map" shape, one analysis
   covers both.

## 6. Grades / scope
`[VERIFIED]` secp `p≡3 mod4`, `A_new` supersingular at secp, embedding degree 3 (small `p`), exact
`√p·ζ` eigenvalues. `[PROVED]` `Hom(E,A_new)=0` (Tate, secp-valid) — closes the homomorphic transfer
**only**. `[GAP/OPEN]` D1 non-homomorphic correspondence, D2 twist bridge — no analysis in hand, both
secp-relevant, neither closed. **No claim that ECDLP is broken; no claim it is safe.** The map says: a
supersingular easy-DLP object is provably present in the cover at secp; the homomorphic route to it is
provably shut; the non-homomorphic and character-sum-value routes are open and unmapped.
