# PREREG — Route A live lead: does the S_3-symmetric (elementary-symmetric-variable) reduction COLLAPSE the last-fall degree, and is any collapse secp-SPECIFIC or generic?

**Status:** FROZEN before any reduced-system degree is read. Model scale.
**Date:** 2026-08-31. **Follows** `RESULT_semaev_structure_firstfall_vs_m_v2.md` (first-fall degree is a
forced support invariant — coefficient- AND symmetry-invariant at m=2,3; the m=4 wall killed the brute
compute-push arm). **Harness:** `semaev_elimination_v1.py` + new runner
`semaev_symmetric_reduction_lastfall_v1.py` (exact GF(p); `check_no_float` must pass).
**Gate:** `experiment-designer` read owed BEFORE the run (matched-control test). No grade promotes.

## 0. Why this is the one viable arm
The prior result showed the FIRST-fall degree carries no lever (coefficients and S_m symmetry both
Δ=0). The remaining place a lever could hide is the SOLVING / last-fall degree (Caminata–Gorla: solving
≥ last-fall ≥ first-fall), which sits above first-fall and is where symmetry-reduction (FGHR mechanism)
acts. The un-reduced last-fall was censored above any session Dmax for m≥3, and the m=4 run (114 min →
censored) proved brute-forcing it is hopeless. The elementary-symmetric reduction shrinks the m=3 system
to 3 low-degree variables — making the last-fall degree COMPUTABLE — and lets us test the lever directly.

## 1. Object
For the m=3 prime-field relation system, build the S_3-symmetric reduction in elementary-symmetric
variables e₁,e₂,e₃ and measure its last-fall / solving degree:
- **Ŝ(e₁,e₂,e₃,t)** = S₄(x₁,x₂,x₃,t) rewritten in e_i (S₄ is symmetric; obtained by Gröbner elimination
  of x₁,x₂,x₃ from ⟨e₁−σ₁, e₂−σ₂, e₃−σ₃, S₄⟩, σ_k the elementary symmetric polynomials — exact).
- **Factor-base condition (divisibility encoding):** with factor base V, |V|=6 (>3 for non-degeneracy),
  g(X)=∏_{v∈V}(X−v); the multiset {x₁,x₂,x₃}⊆V ⟺ (X³−e₁X²+e₂X−e₃) | g(X) ⟺ the degree-≤2 remainder
  rem(g, X³−e₁X²+e₂X−e₃) ≡ 0 — its 3 coefficients give 3 polynomial equations in e₁,e₂,e₃.
- **Reduced system:** {Ŝ, r₀(e), r₁(e), r₂(e)} in ℚ… GF(p)[e₁,e₂,e₃].

## 2. Statistic (pre-committed)
Primary: **d_LF^red** = last-fall degree (binding solving-degree invariant) of the reduced system, exact
GF(p) Macaulay ranks (`first_fall_and_solving`, quo target = `I.vector_space_dimension()`). Compared
against:
- **d_LF^unred** = last-fall of the un-reduced {S₄, g(x₁), g(x₂), g(x₃)} at the SAME |V|=6 (measured to
  whatever Dmax is reachable; may CENSOR — if so, "reduction makes it computable" is itself the finding).
- Ranked in a **2-rung ladder in the reduced variables** (the semi-regular rung has no symmetric
  reduction, so it drops out here): **Semaev-reduced** (Ŝ from the true S₄) vs **symmetric-random-
  reduced** (Ŝ_rand = a random S_3-symmetric polynomial on Ŝ's support in e-variables, SAME factor-base
  remainder equations), K_null=12 draws.

## 3. Decision rule (pre-committed — three outcomes, all named up front)
Let Δ_coeff = d_LF^red(symmetric-random median) − d_LF^red(Semaev), and note whether d_LF^red < d_LF^unred.
- **SECP-SPECIFIC LEVER (escalate — counter-prior target):** Δ_coeff > 0 (Semaev strictly below the
  symmetric-random spread, min(symmetric-random) ≥ d_LF^red(Semaev)). ⇒ the specific secp group-law
  coefficients lower the solving degree of the symmetric-reduced system beyond generic symmetry. A
  genuine curve-specific lever — do NOT close; prereg an m=4 confirmation.
- **GENERIC SYMMETRIZATION (known, not a new lever):** Δ_coeff = 0 (Semaev inside the symmetric-random
  spread) AND d_LF^red < d_LF^unred. ⇒ symmetrization collapses the solving degree, but generically (any
  symmetric coefficients do it equally) — this is the known FGHR-type prime-field speedup, curve-
  independent, already inside best-known IC complexity. Record magnitude + scope; NOT a secp lever.
- **NO COLLAPSE:** d_LF^red ≥ d_LF^unred (reduction does not lower the solving degree). ⇒ scoped null on
  the symmetrization mechanism at m=3. Record; the m≥4 regime stays open.
- **VOID:** the reduction is mis-built (Ŝ does not reproduce S₄ under back-substitution — verified by an
  exact identity check in §5; or the remainder encoding admits spurious solutions not in V^3 — checked
  by counting the reduced variety vs the true # of V-multiset decompositions).

## 4. Controls
- **Reduction-correctness check (MUST pass or VOID):** back-substitute e_i=σ_i(x) into Ŝ and assert it
  equals S₄ exactly (integer polynomial identity over GF(p)). And: the reduced variety size must equal
  the number of size-3 sub-multisets of V that decompose t (cross-checked against the un-reduced variety
  size / m! for the ordered count).
- **Firing control:** a symmetric system with a hand-known low last-fall (e.g. {e₁−c, e₂−d, e₃−f} → a
  point, d_LF=1) must return 1 — read-out calibration in the e-variables.

## 5. Scope & power (frozen)
- m=3 only (the reduction makes m=3 tractable; m=4 reduction is the next step IF m=3 shows a lever).
  |V|=6. p ∈ {307, 2069}. Curve A=0,B=7. K_null=12. Dmax(reduced)=20; Dmax(unreduced)=16 (may censor).
- **Power ceiling:** one m value; this tests the mechanism's PRESENCE and its secp-specificity at m=3,
  NOT the asymptotic growth. No grade above `[EMPIRICAL, model scale]`. A single-m result cannot settle
  route A; it can only (a) surface a secp-specific lever to escalate, or (b) locate the effect as generic.
- **Honest prior (not a pre-deflation — the test still runs):** by the first-fall result's logic, the
  most likely outcome is GENERIC symmetrization (Δ_coeff=0), i.e. curve-independent. This is stated so
  that a Δ_coeff=0 is NOT written up as a fresh discovery, and so that a Δ_coeff>0 (which would CONTRADICT
  this prior) gets the escalation + independent re-check it deserves rather than being smoothed away.

## 6. Exactness / fence
All arithmetic exact GF(p) integers; PRNG/generation boundary untouched (pure summation-polynomial +
invariant-theory structure).
