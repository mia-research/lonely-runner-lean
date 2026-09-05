# Uniformity of the 120° law: why cross-cell translation cannot prove it, and the CM-type step it isolates

**Date:** 2026-08-10 · Precise problem statement (Option B). **No grade promotion; nothing closed;
no leakage/ECDLP claim.** Purpose: define the obstruction formally so the one missing step is isolated.
Carries the 2026-08-10 self-audit corrections (esp.: the known symmetries are horizontal — this does
**not** assert no within-fiber mechanism exists; existence of one is the open target).

## 0. Object (fixed conventions)

`p` prime, `p ≡ 7 mod 12` (⊇ secp; forces `ω=ζ₃ ∈ F_p` and `p ≡ 3 mod 4`); `E: y²=x³+7`;
`n = #E(F_p)` prime, `n ≡ 1 mod 3` (record L3). For `a ∈ (ℤ/n)`, the sheaf
`F_a = L_{χ₂(y)} ⊗ L_{χ_a}` on `E` minus its four tame points, where `χ₂` is the quadratic character of
the `y`-coordinate and `χ_a` the Lang-torsor character of `E(F_p) ≅ ℤ/n` at frequency `a`. Then
`dim H¹_c(E,F_a) = 4`; Frobenius has eigenvalues `α₁(a),…,α₄(a)`, Weil numbers of weight 1
(`|α_i|=√p`), and `L*_a(T) = ∏(1−α_i(a)T)`. Power sums `p_k(a) = Σ α_i(a)^k = −V_k(a)`,
`V_k(a) = Σ_{P∈E(F_{p^k})} χ₂(y_P) χ_a(Tr_{k/1}P)`. (Object verified identical to `n1_twisted_eigenvalues_v1.sage` — construction and `|V₁|/√p` multiset, p=43.)

## 1. What is proven (graded)

- **(Per-cell law)** `[REPRODUCED-exact, p ≤ 211, all cells]` The multiset is `{α, ωα, −ᾱ, −ω̄ᾱ}`;
  equivalently `α₂/α₁ = ζ₃`; equivalently `g(a) := deg gcd(L*_a(T), L*_a(ζ₃T)) = 2`; equivalently
  `L*_a` base-changed to `F_{p³}` is a perfect square `Q_a(T)²`, `Q_a(T)=1−(p₃(a)/2)T−p³T²`.
- **(ω-descent)** `[PROVED — this session + record]` `V_k(a) = V_k(λa)` for all `k`, where `λ ∈ (ℤ/n)*`
  has order 3. Hence `L*_a = L*_{λa}` **as polynomials**.
- **(Ordinary type)** `[VERIFIED, p=43, a=1]` `P`-adic Newton polygon of `L*_a` at `P | p` is `{0,0,1,1}`
  (ordinary). **(At `a=0`:** `A_new` is `[CITED — record L1/v2]` supersingular, `√p·μ₁₂`; not recomputed
  here.)
- **(CM field)** `[VERIFIED — Sage]` `End(E)=ℤ[ω]`; `π_E = w+7 = 𝔭`, `N(π_E)=p`; `p` splits in `ℚ(ω)`
  as `𝔭·𝔭̄` and is **inert** in `ℚ(ζ_n)`.

Uniformity (OPEN): `α₂/α₁ = ζ₃` for **all** `a ∈ (ℤ/n)*`, **all** `p ≡ 7 mod 12`, to `p ≈ 2²⁵⁶`.

## 2. The three cross-cell symmetries, formally

Each is a genuine symmetry; each is **horizontal** — it moves cell `a` to cell `λa`, never fixing `a≠0`.

1. **Geometric CM automorphism `[ω]`.** `[ω]:(x,y)↦(ωx,y)` is the order-3 element of `Aut(E,O)=⟨ζ₆⟩`,
   i.e. the CM endomorphism `ω ∈ ℤ[ω]=End(E)` (this identification is exact — the ratio `ζ₃` and the
   CM unit `ω` are the *same* endomorphism as an automorphism of `E`; what is **not** yet shown is that
   this endomorphism *induces the ratio* on the fiber, §4). Since `[ω]` fixes `y`,
   `[ω]^*L_{χ₂(y)}=L_{χ₂(y)}`; and `[ω]_*` acts on `E(F_p)≅ℤ/n` as multiplication by `λ` (order 3), so
   `[ω]^*L_{χ_a}=L_{χ_{λa}}`. Therefore
   > `[ω]^* : H¹_c(F_a) ⟶ H¹_c(F_{λa})`, Frobenius-equivariant, **an isomorphism, not an endomorphism**
   > (it is an endomorphism of `H¹_c(F_a)` iff `λa=a` iff `a=0`).

2. **Arithmetic Galois `σ_λ`.** `V_k(a)=Σ_d h_k[d]ζ_n^{ad}`, so `σ_k(V_k(a))=V_k(ka)` for
   `σ_k:ζ_n↦ζ_n^k ∈ Gal(ℚ(ζ_n)/ℚ)`. Thus `σ_λ` sends the coefficients of `L*_a` to those of `L*_{λa}`.
   Combined with ω-descent (`V_k(a)=V_k(λa)`), each `V_k(a)` is `σ_λ`-fixed:
   > `L*_a ∈ K_0[T]`, `K_0 = ℚ(ζ_n)^{⟨σ_λ⟩}` the index-3 subfield.

3. **Twist shift `a↦λa`.** The identity on the index set, sending cell `a` to cell `λa`.

## 3. The obstruction, stated precisely

Let `U(a)` be the proposition "`α₂(a)/α₁(a)=ζ₃`". Two facts:

**(H) Horizontal transport is free and total-within-orbit.** ω-descent gives `L*_a = L*_{λa}` **as
polynomials**, so the eigenvalue multiset at `a` equals that at `λa`. Hence
> `U(a) ⟺ U(λa) ⟺ U(λ²a)`, trivially — the three cells of a `λ`-orbit carry **one** `L*`.

**(V) No horizontal fact supplies a base case.** The symmetries of §2 are exactly the edges of the
orbit graph on `(ℤ/n)*`; its connected components are the `(n−1)/3` orbits `⟨λ⟩·a`. Proving `∀a U(a)`
by these edges requires `U(a₀)` at **one representative per orbit** — `(n−1)/3` base cases — and the
edges supply **none** of them. They reduce the cell count `n−1 → (n−1)/3`; they do not decide the law
at a single orbit.

**(V′) Even the strongest horizontal fact — `σ_λ`-descent of the whole `L*` (§2.2) — is silent on the
ratio.** `L*_a ∈ K_0[T]` constrains the *field of definition of the coefficients*. A degree-4
polynomial with coefficients in any field `K_0` may have arbitrary root configuration; "coefficients in
the index-3 subfield" does not force two roots into a `ζ₃`-ratio. (Numerically confirmed downstream:
`deg gcd(L*_a(T), L*_a(ζ₃T)) = 2`, not `4` — the eigenvalue *set* is **not** `ζ₃`-invariant, so no
operator `T` with `T·Frob = ζ₃·Frob·T` acts on the fiber; the ratio links **two of four** roots, not
all four.)

**Formal reason the two directions are independent.** Write `α_i(a)` as a function of the cell index
`a` (horizontal direction) and index `i` (within-fiber direction). The cross-cell symmetries act
**purely in `a`** (they permute cells / act on `ζ_n`); the law `U(a)` is a relation **purely in `i` at
fixed `a`** (the ratio of two eigenvalues of one Frobenius). Horizontal data — how `α_i(a)` transforms
under `a↦λa` and `σ_λ` — is orthogonal to the vertical relation among `{α_i}` at fixed `a`. This is
why every horizontal symmetry, however strong, cannot output the law: it is the wrong direction.

## 4. The isolated step: a CM-type Hecke input (vertical)

What is needed is a **vertical** mechanism — internal to a single fiber `H¹_c(F_{a₀})` — that forces
`U(a₀)` for one representative per orbit; (H) then propagates it, and if the mechanism is uniform in `p`
it reaches `2²⁵⁶`. The natural candidate is CM/Hecke, isolated as three sub-questions:

> **(CM-i)** Does the ordinary rank-2 "unit-root" part of `H¹_c(F_a)` (Newton slopes `0,0`) carry CM by
> an order in a field containing `ℚ(ω)`? *(The `{0,0,1,1}` polygon is consistent with CM but does not
> establish it — this is exactly the unproven vertical fact.)*
>
> **(CM-ii)** If so, its Frobenius is a value of a Hecke Grössencharacter `ψ` of that CM field, twisted
> by the finite-order `χ_a`. `ψ` is defined by an infinity-type and a conductor/congruence condition on
> the ideles of the CM field — **data independent of `p`**. Isolate which part of `ψ` is `a`-dependent
> (the `χ_a` twist) and which is not (the CM-type).
>
> **(CM-iii)** Does the CM-type — through the action of `ω ∈ ℤ[ω]` on the split prime `𝔭=(π_E)` — force
> the two unit-root eigenvalues to differ by `ω`, i.e. `α₂(a)=ω·α₁(a)`?

**Why this, and only this, gives uniformity in `p`.** `ψ` is not attached to one prime; it is a
character of the idele class group. If (CM-i)–(CM-iii) hold, `α₂/α₁=ω` is a statement about `ψ`'s
CM-type valid at **every** split prime `𝔭` (every `p ≡ 1 mod 3`) at once — the `p`-independence is the
definition of a Hecke character, not an extrapolation. The horizontal symmetries then reduce the
per-`p` work to one orbit-representative, which the CM-type already covers. This is the precise sense in
which the CM-type Hecke step is the *whole* remaining content.

## 5. Honesty ledger (audit-consistent)

- The claim "the ratio is CM" is a `[LEAD]`: the ratio `ζ₃` and the CM endomorphism `ω` coincide as
  automorphisms of `E` (`[VERIFIED]`), but that this endomorphism *induces the eigenvalue ratio on the
  fiber* is (CM-iii) — **open**, not shown.
- This document does **not** claim no within-fiber operator exists. §3 proves the three *known*
  symmetries are horizontal and that `σ_λ`-descent is ratio-silent; the vertical mechanism is posed as
  the open target (§4), with CM/Hecke as the candidate — not the only conceivable one.
- Nothing here reaches any `p` beyond the finite sample; uniformity's grade is unchanged (OPEN).
- The horizontal/vertical split is the deliverable: it shows the cross-cell tooling (proved, exact) is
  structurally incapable of the law, so effort should target (CM-i)/(CM-iii), not more descent.
