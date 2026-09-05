# OPEN — LBE isotypic projection onto W ⊆ A_new (doc 11 vetting)

**Status: OPEN, come back to.** Interesting idea, interesting results — NOT closed.
Source doc: `~/Downloads/lbe-isotypic-projection.md`. Sage machinery:
`scratchpad/session_2026-08-11/lbe_full_test2.sage`, `.../lbe_dlog.sage` (function-field Jacobian of C: w⁴=x³+B).

## What was built and verified (over F₄₃, E: y²=x³+7, |E|=31; Jac order 58683=3·31·631; A_new part 1893=3·631)

- **χ₃-bridge (§1)** — CORRECT on real secp256k1: F(P)=χ₃(x_P)·y_P transforms as
  F(φP)=χ₃(β)·F(P), χ₃(β) a primitive cube root; GLV φ(G)=[λ]G verified. Type-coherence fix is real.
- **M3 (D1 lift)** — Q(P)=[P⁺−P⁻] constructed; lands in the **A_new part** (order | 1893), misses E.
  F_p-rational only when y_P is a QR (15/30 of [d]G here); else needs F_{p²}.
- **M4** — [ζ₃]Q(P) = Q(φP): holds (all tested).
- **M5 (isotypic projection)** — S = Q₀+β²Q₁+βQ₂ is a **genuine ζ₃-eigenvector**:
  σ(S)=[k]S with k=1849 for every tested d, k³≡1 mod 1893, k≠1. (Eigenvalue scalar is 1849=43²
  in the order-1893 group — NOT the doc's β=36, which is a cube root mod 43, a different ring.)

## The I1 table (dlog of S([d]G) in A_new(F₄₃)) — the interesting open object

d→dlog: 3→1, 4→206, 6→1715, 7→401, 12→820, 13→1849, 15→43, 17→903(ord631), 20→1286,
21→1780, 22→21(631), 23→969(631), 26→260, 29→1186, 30→1811. (other d: no F₄₃-rational lift)

- **Injective** on the 15 rational-lift d.
- **Not linear** in d: e(6)=1715 ≠ 2·e(3)=2; S([d]G) ≠ [d]·S(G). (Lift is non-homomorphic — expected.)

## OPEN questions to test on return (concrete, not verdicts)

1. Is e(d) **affine**, or does it factor through the **GLV halves** (d₁,d₂) of d = d₁+d₂λ?
2. Is e(d) **constant on μ₃-orbits** {d, λd, λ²d}? (S is the β-eigenvector, so a covariance is expected.)
3. Does the χ₃-orbit coordinate (public) **compose** with a carry object (docs 14–16) to narrow d? —
   the "partial info is useful" bar: even a few bits of d matter for the puzzle. NOT yet tested with
   the real carry object; generic-carry proxy was null but that's the wrong object.
4. Behaviour of the whole pipeline at scale (embedding degree k=3 ⇒ F_{p³} dlog): what, if anything,
   does dlog_{A_new}(S(P)) reveal about d that isn't the E-dlog itself?

## Standing tension (record, don't treat as closing anything)

E ordinary, A_new supersingular ⇒ Hom(E,A_new)=0 (verified doc 10) ⇒ the lift is non-homomorphic
(admitted). Whether a **non-homomorphic** readout can still carry **partial** d-information is exactly
the open question — do NOT restate the null as "no leak." Per project stance: a scoped null ≠ closure.
