# Masked-Structure — Findings v12: the amicable CM correspondence, constructed

**Date:** 2026-07-16 · Line 2 pushed to the real object (not the group-hom strawman of v11).
Script: `cm_amicable_correspondence_v1.py`. Pair (p,n)=(907,967), `E: y²=x³+7`, exact integers.
Goal (the user's ask): not "it's hard" but **construct the correspondence and locate WHY**.

## The correspondence is EXACT and REAL

CM theory, made explicit and verified on (907,967):
- Frobenius `π_p = (−33,−7)` in `ℤ[ω]`: `N(π_p)=907=p`, trace `2a−b = −59 = p+1−n`, and
  `a + b·λ ≡ 1 (mod n)` with the GLV eigenvalue `λ=824` (`λ³≡1`) — so `[π_p]G = G`
  (Frobenius acts as identity on `F_p`-points, a theorem, here checked).
- Hence `(π_p − 1)` annihilates `E(F_p)`, and `N(π_p−1)=967=n` is prime, so
  > **`E(F_907) ≅ ℤ[ω]/(π_p−1) ≅ F_967`.**  The amicable partner's field **is** the CM
  > coordinate ring of the point group.
- Partner closes by the `(1−π)−1 = −π` identity: `π_n = 1−π_p = (34,7)`, `N(π_n)=967=n`,
  `N(π_n−1)=N(−π_p)=907=p`, so `#E(F_967)=p` and `E(F_967) ≅ F_907`.

So the DLP "`P=[d]G`, find `d`" **is** "find the `F_n`-coordinate `φ(P)` of `P`" under an
exact, real isomorphism. This is genuine structure, not a heuristic.

## WHY it transfers no advantage — the boundary, with grades

| operation | cost | grade |
|---|---|---|
| forward `[α]G`, the `[ω]`-action `(βx,y)`, GLV `λ`, `π_p`, the iso *exists* | poly | cheap |
| **coordinate map `φ: E(F_p)→F_n`** (place `P` in `ℤ[ω]/(π_p−1)`) | = the DLP | **PROVED DLP-equivalent** — `φ([d]G)=d`, so computing `φ` *is* the discrete log |
| **canonical lift** `E(F_p)→` global CM point `→` reduce mod `π_n` | — | **heuristically hard, NOT proven** — no known efficient lift; height-growth / xedni-calculus obstruction (Silverman 1998; Jacobson–Koblitz–Silverman–Stein–Teske 2000). *Citation from memory — verify before relying.* |
| partner `E(F_n) ≅ F_p` as an easier target | — | it's a **same-size independent DLP** (order `p≈2²⁵⁶`), no field map `F_p↔F_n` |

**The precise "why":** the amicable/CM correspondence is an **abstract module isomorphism**.
The two standard ways to make an abstract iso concrete are (a) compute the coordinate/index —
which *is* the DLP, provably — or (b) lift to a global object — which has no known efficient
realization. The partner group is not an easier place to land. So an *exact* structural
correspondence yields *zero* computational leverage, and we can name exactly which step
absorbs the hardness (the coordinate map = DLP; grade PROVED) versus which is only
heuristically blocked (the lift; grade OPEN-but-obstructed).

## The genuine remaining unknown (fence, honestly)

Both bypasses above route through a known-hard step. **Untested / not ruled out:** a
**non-lift, non-coordinate** use of the joint ideal `(π_p−1)(π_n−1)` — i.e. a structural
computation in `ℤ[ω]/((π_p−1)(π_n−1)) ≅ E(F_p)×E(F_n)` that extracts information about `d`
without first computing `φ(P)`. I did **not** find such a computation and I do **not** claim
one is impossible. Concrete sub-questions it opens:
- Is there a *canonical* computable element of the joint object whose two components
  constrain `d`? (The GLV eigenvalues `λ_p∈F_n`, `λ_n∈F_p` are computable but `d`-independent.)
- Does the CRT splitting expose any `d`-bit that is cheaper than the full coordinate?

These are real unknowns, not walls. This is where Line 2 actually lives.

## Net (and the correction it completes)

v11 rigorously walled only *abstract group homs* — a strawman. v12 constructs the *actual*
object: an **exact** CM correspondence `E(F_p)≅F_n`, computationally vacuous through both
known routes, with the hardness located precisely (coordinate map = DLP, PROVED; lift =
heuristic obstruction, OPEN). The honest headline is **not** "amicable is a wall" — it is
"the amicable correspondence is real and exact, transfers no advantage by any *known* route,
and the structural (joint-ideal) route is genuinely unexplored." Fence, mapped from the
inside.
