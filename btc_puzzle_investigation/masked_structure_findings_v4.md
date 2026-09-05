# Masked-Structure — Findings v4: "zero arithmetic content" was a declaration

**Date:** 2026-07-16 · corrects **v2 §R2** (and the memory line derived from it).
v2's R1/R3 and v3's R4 stand. Script: inline test in this session; extends
`masked_structure_harness_v1.py`.

---

## R5. CORRECTED — "pure lattice geometry with **zero arithmetic content**"

Challenged with: *"Or lattice geometry with no **detected** arithmetic content?"* — and
that is the correct phrasing. v2 R2 conflated two different statements.

### What is actually proved

```
    ε(x) ≠ 0  ⟺  |u+v| > ½        (z = u·R₁ + v·R₂, u,v ∈ [−½,½))
```

a fixed, **prime-independent region indicator in coefficient space**. So:

> **ε is a fixed LENS. It carries no arithmetic of its own.**   [PROVED]

### What was claimed but NOT proved

That ε-**observables** carry zero arithmetic. They do not, in general. An ε-observable
over a set `S` is determined by **the distribution of (u,v) over S**, and that
distribution is arithmetic whenever `S` is arithmetically defined (curve points, an
orbit, a key set). *The lens carries nothing; what it is pointed at may.*

### The error that made this invisible

**Every constant in v1/v2 was measured over the FULL FIELD** (`for x in range(1,p)`). But
`eis` is a **bijection** `𝔽_p → (lattice ∩ P)` — it is the reduction of `X ∈ ℤ ⊂ ℤ[ω]`
mod `Λ=(π_p)`, and `ℤ[ω]/Λ ≅ 𝔽_p`. So over the full field the (u,v) distribution is not a
finding, it is **forced**: it is exactly the complete lattice ∩ P.

> **I measured the one set on which the answer was structurally guaranteed to be
> geometry, and concluded there is no arithmetic anywhere.**

Same vacuity as A@N=82 (v2 R3) in a different costume: a test that could not have
returned anything else.

---

## The live question, now tested: is (u,v) equidistributed over CURVE points?

Full enumeration over `{x : x³+7 ∈ QR}` (the arithmetically-defined set), all shape
observables, exact. **Generic ⇒ `dev·√p = O(1)` and does not grow with p.**

| p | flapfrac | dev·√p | E[N]/p | dev·√p | aniso_flap | λmax/Tr(all) |
|---|---|---|---|---|---|---|
| 523 | 0.29508 | 1.031 | 0.17128 | 0.106 | 31.10 | 0.78713 |
| 643 | 0.27181 | 0.553 | 0.17351 | 0.173 | 33.42 | 0.76110 |
| 1063 | 0.25251 | 0.082 | 0.16309 | −0.117 | 32.10 | 0.75805 |
| 2281 | 0.22071 | **−1.399** | 0.15731 | −0.447 | 31.69 | 0.73384 |
| 5323 | 0.25626 | 0.457 | 0.16747 | 0.059 | 36.99 | 0.75503 |
| 12613 | 0.26306 | 1.467 | 0.16984 | 0.356 | 33.01 | 0.75814 |
| 59971 | 0.25664 | 1.626 | 0.16812 | 0.356 | 32.79 | 0.75442 |
| *shape* | *0.25* | — | *1/6 = .16667* | — | *33* | *0.75* |

`dev·√p` fluctuates in `[−1.4, +1.6]` while `√p` itself grows 10× (23 → 245). **O(1) ⇒
the deviation is `O(p^{−1/2})`: square-root, generic.** Same for `E[N]/p`; `aniso_flap`
scatters around 33; `λmax/Tr(all) → 0.754`.

### The corrected statement

- **NOT** "zero arithmetic content."
- **The arithmetic content is exactly the `O(p^{−1/2})` equidistribution defect of (u,v)
  over the set in question** — nonzero, bounded, and at the *generic* (Weil / √-cancel)
  scale over curve points.
- **Scope:** full enumeration, `p ≤ 59,971`, these observables, the curve-point set. Not
  a proof; not at secp's `p`; not for orbits or key sets, which remain unmeasured.

### What "closing the panel" may and may not mean

v2 said the ε/norm-band/frame-operator panel is *"closed BY PROOF."* Overreach. Correct:

- **Proved:** the *lens* is inert — no ε-observable can carry arithmetic that is not
  already in the (u,v) distribution. This is a genuine **reduction**: it collapses three
  panels (ε, norm band, frame operator) into **one object**, the map `x ↦ (u,v)`.
- **Measured (scoped):** for the curve-point set at small p, that distribution's defect
  is generic.
- **Open:** the defect at secp's p; the defect over orbits / key sets / difference sets;
  and any *joint* (2-D) structure in `(u,v)` beyond the 1-D projections tested
  (`z³` in v2 §A2 ⇒ generic; the observables here ⇒ generic).

---

## Pattern across v2–v4 (the same error, four times)

| claim | grade claimed | grade earned |
|---|---|---|
| χ₂ doubling "transport law" | PROVED, new | CITED — textbook duplication formula |
| Cap Law constants | "zero arithmetic content" | shape *lens* proved inert; **content = the O(p^{−1/2}) defect**, measured generic |
| A @ N=82 "null, well-controlled" | null | **zero power** (f_min = 1.0) |
| G "stands" | tests the blind corner | **proxy** (`d mod k`; already a known theorem) |

Every one: **a statement made at a higher epistemic grade than the evidence supports.**
Every one caught by external challenge; **none** by my own review passes. That asymmetry
is the finding of this session.

## Method rules (cumulative)

1. A null needs a **power number** (`f_min`) or it is not a result.
2. Never let the tested set define the baseline (tautology).
3. A constant universal across all primes is a **red flag, not a trophy**.
4. Verifying an identity your code implements verifies **your code**, not nature.
5. Naming the right test is **not running it** — the substitution happens when the
   harness you have fits a *proxy* of the test you posed.
6. **NEW — check whether the test set could have returned anything else.** The full field
   is a bijective image of the lattice: measuring "shape constants" there was
   structurally guaranteed. Before running, ask *what result is this set capable of
   producing?*
7. **NEW — "no detected X" ≠ "zero X".** Say which set, which observable, which scale,
   and which power. A distribution-free claim ("carries no arithmetic") needs a proof
   about *all* sets, not a measurement on one.
