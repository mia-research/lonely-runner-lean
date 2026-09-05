# Vertical-ZFR Appendix B rank-2 common mode — does NOT reproduce (2026-07-10)
Faithful reproduction of the paper's exact construction (`zfr_rank2_reproduce.py`).
Paper: Palelei & Palelei, *A Vertical Zero-Free Region for Families of Dirichlet
L-Functions* (Feb 2026 draft), §2.4–2.5 + Appendix B.

## Construction (verbatim from the paper)
- Q=100, moduli q prime in [Q/2,Q] = {53,59,61,67,71,73,79,83,89,97}.
- ALL non-principal χ_j mod q; feature g_{p₀}(q,j) = (χ_j(p₀) − μ_{p₀}(q))/√(q−1),
  μ_{p₀}(q) = −1 if p₀|q else 0  ⇒ 0 for the small primes.
- Feature matrix F: rows = (q,j) ∈ I_Q (712 rows), columns = P₀ = {2,3,5,7,11,13,17,19,23,29}.
- SVD; r=2 projector claimed from top-2 singular subspace.

## Result — flat spectrum, NOT rank 2
| quantity                         | paper (Table 4 / §8.2) | faithful reproduction |
|----------------------------------|:----------------------:|:---------------------:|
| σ_i/σ₁ (i=1..4)                  | 1, 0.987, 0.312, 0.298 | 1, 1, 1, 1 (all ≈1)   |
| variance in top-2 subspace       | 0.97                   | **0.20**              |
| participation ratio PR           | 1.97                   | **9.98**              |
| Gram F*F eigenvalues             | (rank-2 implied)       | nine at 10.00, one at 8.57 |

The spectrum is FLAT (σ_i/σ₁ = 1×9, 0.926×1; PR≈10). Analytically exact: by character
orthogonality Σ_{j≠0} χ_j(p)χ̄_j(p') = (q−1)δ_{pp'} − 1, so F*F = (#q)·I − (Σ_q 1/(q−1))·(J−I),
giving nine eigenvalues at #q=10 and one all-ones mode DEPRESSED to
10 − 9·mean(1/(q−1)) = 8.57 (matches to the digit). Effective rank = |P₀| = 10, not 2.

## Interpretation
- There is **no rank-2 finite-rank common mode** in the low-prime features. The ten
  features are ~orthonormal; the only shared mode is the all-ones/principal-exclusion
  direction, which is a single (rank-1) DEPRESSED mode, not a rank-2 elevation.
- Appendix B Table 4 (σ₃ drop to 0.312, PR 1.97) and Table 1's "4–9% MP uplift" do not
  reproduce; the uplift is ordinary finite-N Marchenko–Pastur fluctuation.

## Impact (constructive)
- **Main theorem likely survives.** Remark 8.1 states the Appendix B numerics are
  motivational and "no numerical claim is used in the proofs," and Lemma L (Stage 3) is
  proved for a GENERAL finite-rank projector Π = I − P_r^{(P₀)} — it holds for any fixed r.
- **But the r=2 evidence and the projector's motivation need revision.** The projector
  built from F's top-2 singular vectors removes 2 essentially-arbitrary directions from a
  flat spectrum; there is no genuine low-rank common mode among the small-prime features
  to remove. If the projection is needed for the BV/BDH step, the correlation it targets
  must live in the LARGE-prime coefficient system (Table 1/K, Table 3 ρ), not here —
  worth a separate faithful check (are those also orthogonality-flat?).

## SCOPE — this is about the paper's construction, NOT the curve
The CM analogue of the PAPER'S feature-covariance construction is also flattened by
orthogonality on (ℤ[ω]/𝔮)*, so the narrow "rank-6 sextic common mode" proposed for the
I–III bridge does not appear in that construction. That is the entire claim. It says
NOTHING about the curve's genuine sextic structure — the μ₆ Grossencharacter decoration,
the amicable pair, the sextic identities, CM=ℤ[ω], Q3/Q4 — which are exact curve
computations, established independently and untouched by anything in this paper. Do not
let "the ZFR feature construction is flat" widen into a statement about the curve.

## Re-examination with a MATCHED RANDOM NULL (2026-07-10) — cut confirmed rigorously
- Small primes (Table 4): real chars PR=9.98 vs random unit-modulus null PR=9.88 — real≈null,
  both flat. Flatness is not a construction artifact.
- Large primes (Table 1): real top eigenvalue 1.73 vs null top 1.90 → real/null=0.91<1. The real
  spectrum is MORE uniform than random noise — the opposite of a common mode. The paper's 4–9%
  MP uplift not only fails to reproduce, the real top sits BELOW the null. (Resolves the earlier
  hedge about a possible weak real mode: there is none in the full covariance.)
- Weak rank-1 background IS real: the modulus-averaged means ā_q share the −1/√p direction
  (Table 3 ρ≈0.1 reproduces). So the projector removes a genuine but ONE-dimensional background;
  the rank-2 and the flat-97% Table 4 are the erroneous parts.
- **Bug localized:** feeding |χ(p)| instead of χ(p) collapses F to PR=1.00 (rank-1), since |χ|≡1.
  A magnitude- or real-part-variant in the Appendix B feature code is the plausible source of a
  spurious low rank.

## Likely Appendix B bug (for the author to check)
The stated construction cannot yield σ₃/σ₁=0.312. Plausible code divergences: features
built from |χ(p)| or Re χ(p) (introduces a real common mode), missing the /√(q−1) or a
per-prime rescale, an SVD of a transposed/relabeled matrix, or a very small character
sample. Sharing the Appendix B script would let this be pinned exactly.
