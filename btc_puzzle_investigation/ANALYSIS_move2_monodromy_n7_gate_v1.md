# ANALYSIS — Move 2 object-identity gate: P32's monodromy is NOT the a-family monodromy (#28); the character-table→N7 prediction is a category error

**Date:** 2026-08-24
**Author:** ZCode (Claude). Move 2 of `ANALYSIS_supervisor_intersection_menu_triage_v1.md`.
**Gate (pre-committed in the triage):** before computing the character table of P32's finite
monodromy to predict N7's sub-Rayleigh deficit, confirm P32's group **is** the a-family monodromy
(#28) — which the v14 ledger flags three times as "a distinct open object."
**Sources read:** `RESULT_26_PROVED_weil_restriction_v1.md` (P32, full),
`RESULT_subrayleigh_deficit_scaling_v1.md` (N7, full), v14 master (N8 residue, B2.2, do-not-close #2).
**Verdict:** **GATE FAILS.** P32's Klein-four×ℤ/3 is the *within-fiber* (vertical) descent group;
N7 needs the *family* (horizontal) monodromy #28. They are different objects. The supervisor's
specific move — character table of the order-12 group ⇒ N7 deficit profile — is a **category error**
and does not work as stated. The underlying *lead* (N7 is arithmetic ⇐ finite family monodromy)
survives, reframed to the correct object.

---

## 1. What P32's monodromy actually is (vertical / within-fiber)

P32 proves, for a **fixed** E/F_p (n odd) and **every** R (=a): `V₂(a) = V₁(a)² − 2χ₂(−1)p` and
`e₂(a) = e₁(a)² − χ₂(−1)p`. For **each fixed a** it builds the genus-3 curve `C_a : w² = G_R(λ)`
and shows `Tr(Frob | H¹(C_a)) = 0` because `Gal(F_{p³}/F_p) ≅ ℤ/3` cyclically permutes the three
`E[2]`-translation eigenspaces `H¹_{χ_i}` (Klein four `V ≅ (ℤ/2)²`), giving zero diagonal blocks
(§6). `Jac(C_a) = Res_{F_{p³}/F_p}(E₁,a)`.

The Klein-four×ℤ/3 is therefore the automorphism/Galois structure **inside a single fiber `C_a`**.
It forces a **relation between the two coefficients `e₁(a)` and `e₂(a)` at the same `a`** — a
*rigidity* ("the V₁/V₂ collapse"), not a law about how `e₁(a)` is distributed.

**P32 §8 says this in as many words:** *"This is a statement about E over F_p for a single p; it
proves the rigidity … and it says nothing about any statistic outside the V₁/V₂ collapse."* And §8's
closure-grade: *object = the twisted L-polynomial coefficients e₁,e₂; class = the 120° eigenvalue
configuration; scope = every nonsingular E/F_p, p>3, n odd.* Distribution over `a` is not in scope.

## 2. What N7 needs (horizontal / family)

The sub-Rayleigh deficit (N7) is a property of the **distribution** — `mean|U|` systematically below
a Hermitian-matched null, "arithmetic scatter" no smooth (random-matrix) model fits. Do-not-close #2
ties its mechanism to "the distribution of the traces `V₁(a)` as `a` varies." `V₁(a)` is fixed by
`c₃(a) = a(E₁,a / F_{p³})` (§6: `Ch = T⁶ − c₃T³ + p³`), so the N7-relevant object is the
**geometric monodromy of the family `{E₁,a}_a` over `F_{p³}`** — a *horizontal* monodromy in the
`a`-parameter. Finite ⇒ arithmetic/discrete trace distribution (the supervisor's mechanism);
connected ⇒ Sato–Tate. This is exactly #28, and P32 does not compute it.

## 3. Why the two are different (the category error, precisely)

| | P32 (vertical) | #28 (horizontal) |
|---|---|---|
| group | Klein-four×ℤ/3 = `E[2]`-translations × Frobenius-on-cubic-roots | geometric monodromy of `{E₁,a}` / `{c₃(a)}` as `a` varies |
| acts on | `H¹(C_a)` of **one** fiber | the local system over the `a`-parameter space |
| gives | the relation `e₂(a)=e₁(a)²−εp` (rigidity, per a) | the **distribution** of `e₁(a)` (Sato–Tate vs arithmetic) |
| status | PROVED (P32) | OPEN (#28) |

Computing the character table of Klein-four×ℤ/3 predicts the multiplicities/eigenvalues **within a
fiber** (it re-derives the trace-0 rigidity), not the spread of `e₁(a)` across fibers. Feeding that
table into a "predicted deficit profile of `V₁(a)`" mislabels the within-fiber group as the family
monodromy. The move's claim — *"P32 establishes that the monodromy of the relevant family is finite
(Klein four × ℤ/3)"* — conflates the two.

## 4. The lead survives, reframed (refuting the mechanism ≠ refuting the lead)

The supervisor's *thesis* — N7's deficit is a forced consequence of **finite** monodromy giving an
arithmetic (non-Sato–Tate) trace distribution — is a live, well-posed hypothesis. It just does not
follow from P32, and its group is not yet known. The correct next object:

> **Is the geometric monodromy of `{E₁,a}_a` (equivalently the distribution of `c₃(a)=a(E₁,a/F_{p³})`)
> finite/arithmetic or Sato–Tate?** If finite, identify the group *from the family's structure* (its
> character table is then the object to compare against the 30-prime deficit); if connected, the
> supervisor's mechanism for N7 is refuted and N7's arithmetic scatter needs a different source.

**Why this is NOT the "purely symbolic, no new data, one afternoon" task the menu advertised.** The
order-12 character table is trivial to compute but predicts the wrong object. The real work —
determining the family monodromy of `{E₁,a}` — is research-level and its empirical proxy (is the
`V₁(a)` distribution discrete vs continuous?) needs its own `experiment-designer` pre-registration
with a matched null: at the model primes p is small, so a raw histogram looks "discrete" from
granularity alone, independent of the monodromy — a naive afternoon check would mis-conclude.

## 5. Disposition

- Move 2 as framed: **does not discharge N7.** No character-table computation is warranted against
  P32's group. No grade moves.
- #28 (a-family monodromy) remains OPEN and is now stated as the concrete object: the monodromy of
  `{E₁,a}/F_{p³}`. do-not-close #2 unchanged; its mechanism question is sharpened, not closed.
- The supervisor's item-2 "collapses into #6 (purity)" claim also does not hold: purity (N31) is a
  bound on eigenvalue *sizes* within a fiber; it says nothing about the family distribution either.
- Recommended, if N7's mechanism is pursued later: a pre-registered discrete-vs-Sato–Tate test of
  `c₃(a)` across a, with a granularity-matched null, at the largest feasible model p — a distinct
  investigation, not this move.

*Scope: a reading-level structural gate on P32 and N7. No numerical claim, no 256-bit/ECDLP claim.*
