# RESULT — μ₆-quotient relation multiplication: a clean 3× CM lever (one PIECE of the μ₆ framework)

**Framework note (binding on how to read this file).** This is one facet of a single lever — the μ₆ CM
structure of secp256k1's curve family — being built up incrementally. A result here is useful as a PIECE;
it does NOT need to beat generic `√n` or solve ECDLP to count. Disparate real findings compound; recording a
real constant-factor lever with its exact scope is progress, not a failed attempt at a total break.

**Grade: `[VERIFIED — exact, clean measurement]`.** Date 2026-08-17. Small-scale (p≈4000, m=3).

## The measurement (factual)
μ₆-invariant factor base `F` (closed under `φ` = GLV endomorphism, order 3, and negation), ordered 3-term
relations `P₁+P₂+P₃=O`, orbits under the diagonal μ₆-action:

| curve | `|F|` | eff. base `|F/aut|` | relations | orbit size | rel/`|F|²` |
|---|---|---|---|---|---|
| CM j=0 (μ₆) | 1404 | **234** (`|F|/6`) | 655,596 | **exactly 6.00** | 0.33 |
| non-CM (μ₂) | 460 | **230** (`|F|/2`) | 24,090 | **exactly 2.00** | 0.11 |

At **matched effective factor base** (~230 orbit-reps), CM multiplies each found relation into **6** vs
non-CM's **2** — a clean **3× advantage**, from the extra μ₃ (GLV). Orbit sizes are exact integers (the full
automorphism orbit of each relation lies in the μ₆-invariant `F` by construction).

## What it connects to (contextual — the μ₆ lever)
- **slope² identity** (`x₁+x₂+x₃=m²`, PROVED, `NOTE_k3_analytic_reduction_v2`): φ-covariant, so relations
  arrive **pre-sorted into φ-orbits** — the 6× multiplication is structural, "one relation IS six."
- **CM yield excess** (`RESULT_semaev_cm_relation_yield_v3_scaling`: `T1(j0)` linear in `|V|`, `perm_p=0`,
  ratio `~exp(|V|)`): the μ₆ multiplication is its mechanism.
- **μ₆ characters** (k=3 channel PROVED un-normalized; `cubic-e↔χ₂(d)` flicker): same structure, other facet.

## Scope (what it is NOT)
- A **constant-factor** lever (≤6×), NOT a change of exponent — does not alone make index calculus
  subexponential or beat generic `√n`. Automorphism-accelerated index calculus is a **known technique**;
  the piece here is the clean μ₆-vs-μ₂ measurement + its link to the covariant slope² relations.
- p≈4000, `|F|≈1400`, m=3, prime-order CM curve. **No secp-scale cost claim.**
- The `d_LF` solving-degree component gets **no** CM help (`RESULT_mu6_solving_degree_v1`, Δ=0); this lever
  lives on the yield/factor-base side, not the linear-algebra-degree side.

## Why it counts (framework, restated)
A lever that is real, exactly measured, and connected to other real pieces (slope², yield) is a building
block. The μ₆ CM structure is the connecting thread across yield, coordinate identities, and characters. The
working hypothesis (project stance): built across these facets, the μ₆ lever is a step — and each step is
recorded on its own terms, not graded against a total break. This file adds the exact relation-multiplication
figure to that build. Next steps live in the same frame (feed slope²-covariance into relation collection;
test whether the character correlations index the μ₆ orbits) — none required to solve everything to be useful.
