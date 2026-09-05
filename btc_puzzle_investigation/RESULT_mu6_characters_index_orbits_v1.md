# RESULT — μ₆ characters index the relation-orbits: a real weak grading (next piece of the μ₆ framework)

**Framework note (binding).** One more facet of the μ₆ CM lever, recorded on its own terms. A weak-but-real
grading is a PIECE; it does not need to give an exploitable linear-algebra speedup to be logged. Extends
[RESULT_mu6_quotient_relation_multiplication_v1.md](RESULT_mu6_quotient_relation_multiplication_v1.md).

**Grade: `[EMPIRICAL — real skew, exploitability untested]`.** Date 2026-08-17. CM curve `y²=x³+7`, p=4159,
|F|=1140, 352,794 three-term relations `P₁+P₂+P₃=O`, m=3.

## Measurement (factual)
- **`e₁+e₂+e₃ mod 3` is μ₆-INVARIANT** (φ shifts each `eᵢ` by 1 ⇒ sum shifts by 3≡0; negation fixes `e`), so
  it labels the μ₆ orbit. Distribution over relations: `{0: 123528, 1: 117054, 2: 112212}`. NOT uniform —
  skew toward class 0 (0.350 vs 0.318). Orbit-level (~58,800 orbits): ~988 dev vs ~114 std ⇒ **~9σ**. Real.
- **`χ₂(x₁)·χ₂(x₂)·χ₂(x₃)`**: `{−1: 178794, +1: 174000}`, ~8σ skew toward −1. Real.
- **`χ₂(x₁+x₂+x₃) = χ₂(m²)`**: `{+1: 350514, 0: 2280}` = **99.4% +1** — the PROVED slope² identity showing up
  as a per-relation character constraint (the 0.6% zeros are the `m=0` degenerate cases).

## What it connects (contextual)
The character findings and the relation-collection findings are the **same μ₆ structure on two sides**:
- character side (this file + `cubic-e↔χ₂(d)` flicker, k=3 channel) → grades the relation-orbits (weakly, but
  significantly);
- coordinate side (slope² identity, PROVED) → constrains every relation's `χ₂(x-sum)=+1`;
- relation side (μ₆-quotient, 6× multiplication) → the orbits being graded.

## Scope (what is NOT shown)
- The grading is **weak** (~5% excess on `e-sum`, ~1% on `χ₂`-product). Real (≥8σ) but small.
- **Exploitability untested**: whether this grading yields usable BLOCK STRUCTURE in the index-calculus linear
  algebra (the one component where μ₆ gave no help, `RESULT_mu6_solving_degree`) is the open next question.
  A weak skew is a real grading; it is not yet a demonstrated linear-algebra speedup.
- Small scale (p≈4000, m=3). No secp-scale claim.

## Why it counts (framework)
The character findings were previously "per-point/scalar correlations" with no home on the relation side.
This locates them: they grade the μ₆ relation-orbits, significantly. That is a connection between two prior
real pieces — logged as a step, not adjudicated against a break.

## FOLLOW-UP (2026-08-17) — does the grading BLOCK the relation matrix? Scoped NULL (boundary located)
Built the relation matrix over the μ₆-orbit-reps; column label = `χ₂(x)` (μ₆-invariant since `χ₂(β)=+1`,
`6|p−1`), row label = `χ₂`-product. Result:
- **Block incidence `B[row χ₂-prod][col χ₂]` = {(1,1):145,(1,−1):97,(−1,−1):116,(−1,1):147}** — all four
  blocks populated, roughly uniform. **No block-diagonal/triangular structure.**
- **Fill-in (elimination-cost proxy): graded 940 vs random 1008** (~7%, inside the random baseline's noise).
  **The grading does NOT reduce elimination cost meaningfully.**
**Boundary located (consistent across two independent instruments):** the μ₆ lever lives on the
relation-collection side (6× multiplication, yield edge — measured) and **stops at the linear-algebra side**
— this fill-in null AND `RESULT_mu6_solving_degree` (`d_LF` Δ=0) agree. **Scoped** to {this construction,
p≈4000, `χ₂`/`e-sum` gradings}; does NOT close "no linear-algebra structure ever," but says this grading
isn't it. A mapped boundary is a useful piece.
