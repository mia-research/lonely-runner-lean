# RESULT — L-mono GKR sub-brick 2 (v2): the fingerprint, the coset discriminator, and a correction of v1's scope overreach

**Date 2026-08-24.** Supersedes `RESULT_lmono_gkr_moment_fingerprint_v1.md`. v1's §0/§2 concluded that
*"the discriminating moment cannot be read off the j-fixed cell data … pinning diagonal-vs-independent
needs the geometric Kummer variation or route B."* **That was a negative-bias overreach**
(`feedback_negative_bias_enlarge_nulls`): it enlarged a true, narrow fact — the cells cannot measure
the *full-group number* `M₂₂=12` because they never visit `j=0` — into a false closure that the cells
cannot discriminate at all. They can, and do. This v2 keeps v1's (correct) fingerprint and adds the
decidable coset discrimination that exposes the error.

**Scope line.** Group theory + real-curve check on the n=1 (A_new/twist) channel of `y²=x³+7`.
**No leakage / ECDLP claim.** Grades: `[VERIFIED]` exact/decidable. New artifact:
`lmono_gkr_coset_discriminator_v1.py`. Retains `lmono_gkr_moment_fingerprint_v1.py`. Predecessors:
`RESULT_lmono_gkr_rank4_eigenderiv_v1.md`, `RESULT_n1_120deg_exact_v1.md`,
`RESULT_monodromy_sato_tane_at_scale_v1.md`, `NOTE_cross_j_relevance_v1.md`.

---

## 0. Headline

- **Full-group GKR fingerprint of `G = SL₂·μ₃·{±}`** (unchanged from v1, exact + MC-confirmed):
  `M₁₁=2, M₂₂=12, M₄₀=10, M₃₃=110`. `M₁₁=2` excludes ψ-trivial `W⊕W` (4), Sym³-irreducible (1),
  U(2)-det-free (4). `[VERIFIED — exact]`
- **The two 4th-moment statistics are different objects** — v1 conflated them:
  - *full-group Haar* `⟨|tr|⁴⟩` (averages all j incl. j=0): candidate **12** vs independent **8**.
    NOT measurable from cells (no cell has j=0). v1's true, narrow fact.
  - *coset-restricted* `⟨|tr|⁴ | j∈{1,2}⟩` (the coset the cells DO occupy): candidate **2** vs
    independent **7**. MEASURABLE — and this is the one that matters.
- **The cells DO exclude the independent SL₂×SL₂ alternative.** Measured `⟨|e₁/√p|⁴⟩` over all 672
  cells (6 primes) = **1.84**, selecting diagonal (predicts 2; resid 0.16) over independent (predicts
  7; resid 5.16); the residual to 2 is finite-p (p=127 already reads 1.92, converging to the banked
  semicircle at scale). `[VERIFIED — exact prediction + real-data match]`
- **Even without the moment, the exact 120° law alone excludes independent SL₂×SL₂**: the diagonal
  locus (roots(g₂)=ζ₃·roots(g₁)) is a positive-codimension, Haar-measure-zero subvariety of the
  independent group, so an independent monodromy would put ~0% of Frobenii there — yet the law holds
  at **100%** (672/672 here; 3585/3585 banked, `RESULT_n1_120deg_exact`). The coset moment is the
  smooth quantitative form of this.

## 1. What v1 got right, and the one error

**Right (retained):** the exact fingerprint table (§1 of v1), `M₁₁=2` ruling out the reducible-to-one,
irreducible, and det-free alternatives; the exact fact that the cells occupy `j∈{1,2}`, never `j=0`.

**The error (§2 of v1):** from "cells miss the `j=0` term, so cell `⟨|tr|⁴⟩→2≠12`" it inferred "cells
cannot separate diagonal from independent." The inference is false because the independent alternative,
*restricted to the same `j∈{1,2}` coset*, gives `⟨|tr|⁴⟩=7`, not 2 — so the coset statistic the cells
DO measure separates them at 2 vs 7. The full-group number 12 was never needed. This is the
`feedback_negative_bias_enlarge_nulls` tell: a real magnitude bound ("can't get the number 12") was
read as an absence of discriminating power.

## 2. The coset discriminator (decidable)

`lmono_gkr_coset_discriminator_v1.py`. Model: `tr_V = ε(1+ζ₃^j)χ`, `χ=2cosθ` (diagonal, one angle) vs
`tr_V = ε(χ₁+ζ₃^j χ₂)` (independent, two angles); restrict `j∈{1,2}`; unitarized `tr_norm = e₁/√p`.

| statistic | diagonal (candidate) | independent SL₂×SL₂ | measured cells |
|---|---|---|---|
| `⟨|tr|² \| j∈{1,2}⟩` | 1 (exact; MC 1.001) | 2 (exact; MC 2.000) | 0.94 → 1 |
| `⟨|tr|⁴ \| j∈{1,2}⟩` | **2** (exact; MC 2.001) | **7** (exact; MC 7.007) | **1.84 → 2** |

Exact coset values: diagonal `1·C_k` (`|1+ζ₃^j|=1`), so `⟨|tr|⁴⟩=C₂=2`. Independent, with
`2Re(ζ₃^{1,2})=−1`: `E[(χ₁²+χ₂²−χ₁χ₂)²] = 2+2+1+2 = 7`. The measured pooled 1.84 (per-prime 1.27–2.43,
rising with p toward 2) sits on the diagonal prediction and 5σ-scale away from independent.

## 3. Corrected scope — what the data settles, what the theorem still owes

**Settled by data (at the tested primes, both arms):** the monodromy is consistent with `G =
SL₂·μ₃·{±}` and **inconsistent with** each named alternative — ψ-trivial (`M₁₁`), Sym³-irreducible
(`M₁₁`), U(2)-det-free (`M₁₁`+odd), and **independent SL₂×SL₂ (coset `⟨|tr|⁴⟩` 2 vs 7, and the exact
120° law directly)**.

**Still owed for a PROOF that `G_geom = G` (hence the 120° law uniform in p — the prize):**
1. **Larsen/GKR theorem** — the statement that matching moments through the required degree forces the
   identity component. A theorem; needs `citation-verifier` (route-A note, next).
2. **Constancy in p** — the empirical exclusions are at 6 primes ≤ 349. Upgrading to "for all p incl.
   secp" needs the geometric monodromy to be a fixed ℓ-adic object independent of p (a specialization
   argument on the sheaf), not a per-prime average. This is the substance of route A and is NOT
   discharged by the finite-prime moment match.
3. **Geometric vs arithmetic μ₃** — whether the `μ₃` is geometric (Kummer-sheaf monodromy) or a fixed
   arithmetic twist (`NOTE_cross_j_relevance` flags this open). Either way the Frobenii carry the ζ₃
   relation; the distinction sets whether we have pinned `G_geom` or `G_arith`. To be resolved in the
   route-A construction.

## 4. Scope / what this does NOT do

- `[VERIFIED — exact]` group theory; real-data match at 6 primes ≤ 349, all cells — secp banner
  governs any extrapolation (item 2 above is exactly why finite-prime evidence is not the uniform
  proof).
- Does **not** prove `G_geom = G`; it removes the named alternatives and fixes the coset statistic that
  a proof's moment-match must hit. No closure of the L-mono gap is claimed.
- v1 remains on disk as the superseded record; this v2 is the one to read.
