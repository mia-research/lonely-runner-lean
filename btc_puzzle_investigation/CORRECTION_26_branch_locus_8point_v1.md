# CORRECTION — the `#26` "exhaustive over `F̄`" negative was exhaustive over the wrong set

**Date:** 2026-08-01. **Corrects:** `RESULT_26_G_explicit_and_symmetry_group_trivial_v1.md` §2 (and
its §4 instruction *"Do NOT run another symmetry search — closed at grade"*).
**Superseded by:** `RESULT_26_PROVED_weil_restriction_v1.md`. **Grade of the correction:** `[PROVED]`.

---

## What was claimed

> *"A Möbius `σ` with `G∘σ = ν·G` must permute `G`'s 7 roots, and 3 points pin a Möbius map ⇒ the
> `7·6·5 = 210` triple-correspondences are the COMPLETE candidate list. Result: stabilizer =
> {identity} … **no Möbius symmetry of `G` exists at all**, over the algebraic closure."*
>
> *"⇒ The odd-symmetry programme is dead, completely."* … *"This also retires the specific
> `E[2]`-translation candidate."*

Stated with object, class, power and scope, and marked closed at grade.

## What is wrong

`deg G = 7` is **odd**. The branch locus of `C : w² = G(λ)` is therefore the **eight** points

`B = {7 roots of G} ∪ {∞}`,

and the reduced automorphism group of `C` is the stabiliser of **`B`**, not of the seven finite
roots. An element of that stabiliser need not fix `∞`.

The framing `G∘σ = ν·G` silently restricts to affine `σ`, i.e. to the point stabiliser of `∞`, and
the implementation enforces it: `tors2_fp3_symmetry_v2.py:71` reads

```
if u is None or u not in Rset: bad = True; break
```

`u is None` is exactly "this root maps to `∞`" — so every candidate that moves a root to `∞` is
discarded. Those are precisely the ones carrying the mechanism.

## The correct computation

Over all `8·7·6 = 336` triples from `B`, the stabiliser has **order 4**, not 1
(`p = 43, 67, 79`; `j = 0` and generic `j`; `jac26_zeta_and_branch_v2.sage`). Its three nontrivial
elements are the `E[2]`-translations `σ_T`, and each acts on `B` as **four transpositions** —
fixed-point-free — swapping `∞` with the root of `F` belonging to `T`.

So the retirement of the `E[2]`-translation candidate is also reversed. The prior file's reason was
*"they permute `D`'s roots but not `G`'s"*, which is true and not the relevant condition: `τ_T` moves
the pair `{T, R−T}` to `{O, R}`, whose λ-value is `∞`. Preserving the **branch locus** is what makes
an automorphism, and `τ_T` does that.

## Why this matters beyond the bookkeeping

The order-4 group is the whole mechanism of #26. `B = λ(E[2]) ⊔ λ(P₀+E[2])` is two free
`E[2]`-orbits; the three lifts generate a Klein four-group over `F_{p³}`; `n` odd makes Frobenius
3-cycle them; the induced permutation of the three 2-dimensional `H¹`-eigenspaces has zero diagonal
blocks, so `Tr(Frob) = 0`. That is the proof.

## The transferable lesson

The negative was **mechanically executed, exhaustive within its enumeration, and correctly reported**
— 210 of 210 candidates, three curves, exact arithmetic. It failed at the **frame** layer: the
candidate set was derived from a formula (`G∘σ = ν·G`) rather than from the object (the branch
divisor of the double cover). `CLAUDE.md §2a` names this split precisely — *isolation is load-bearing
against **frame** errors and buys nothing against mechanical ones*; here the mechanics were flawless
and the frame silently deleted the answer.

Concretely, for any hyperelliptic `w² = G` with **odd** `deg G`: the branch locus includes `∞`, and
`deg G + 1` is the number of branch points. An automorphism search that enumerates only the finite
roots is a search over the stabiliser of `∞`, which is a **proper subgroup** — and the parity of
`deg G` decides whether that subgroup is the whole group.

**A closure written as "exhaustive over `F̄`" was exhaustive over a set that provably could not
contain the object.** The phrase named the field correctly and the candidate set incorrectly.
