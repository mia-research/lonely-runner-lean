# RESULT — L-mono GKR sub-brick 1: the rank-4 eigenvalue bookkeeping FROM the L-polynomial, symbolic + decidably verified

**Date 2026-08-24.** First substantive brick of the L-mono GKR campaign
(`PLAN_lmono_monodromy_campaign_v1.md` §5A/§7.1, sub-brick 1). Discharges the item the predecessor
NOTE recorded as **owed**: *"a from-scratch symbolic re-derivation of why `Im(V₁)/(2√p)` reduces to
the W half-trace `cos θ` … is owed before any such relation is stated as an identity"*
(`NOTE_lmono_gkr_input_1point_v1.md` §2). It is done here and cross-checked decidably.

**Scope line.** curve `y²=x³+7` over `F_p` (j=0, μ₆ CM); the n=1 (A_new / twist) channel; `V₁(a)` the
exact twisted character sum in `Z[ζ_n]`. **No leakage / key-recovery / ECDLP claim.** Output is the
eigenvalue *structure* GKR consumes as input — it does **not** yet pin the monodromy group (that is
the discriminating sub-brick 2, still owed; §4). Grades: `[VERIFIED]` exact/decidable; `[BANKED]`
inherited established fact.

Artifact: `lmono_gkr_rank4_eigenderiv_v1.py` (reuses the D2 module's exact `V₁(a)`; float only in the
degree-4 root readout, error-floor argument as in the D2 certificate). Reproduces STAGE A + STAGE B
PASS. Predecessors: `RESULT_d2_twist_rigidity_certificate_v1.md`, `NOTE_lmono_gkr_input_1point_v1.md`,
`RESULT_n1_120deg_exact_v1.md`, `NOTE_anew_subgroup_structure_map_v1.md`.

---

## 0. Headline

- **The rank-4 spectrum is the tensor form** `H¹ ≅ W ⊕ (W⊗ψ)`, ψ acting as the scalar `ζ₃`, derived
  from the L-polynomial coefficient laws + the banked ζ₃-multiset. `[VERIFIED — exact symbolic]`
- **Tensor-trace identity (new, exact):** `V₁ = −(1+ζ₃)·tr(W) = −ζ₆·tr(W)`. Holds **pointwise on real
  curve data at every one of 672 cells** across 6 primes / both mod-12 arms, residual ≤ 3.7e-14·√p.
  `[VERIFIED — exact + decidable]`
- **Half-trace reduction (the owed piece), exact:** `t := Im(V₁)/(2√p) = −cos θ` (p≡3 mod 4),
  `Re(V₁)/(2√p) = −cos θ` (p≡1 mod 4), where `cos θ = tr(W)/(2√(det W))` is the det-normalized W
  half-trace — **verified REAL** (imag part ≤ 8.2e-15) and pointwise equal at all 672 cells.
  `[VERIFIED — exact + decidable]`
- **Convention slip corrected.** The predecessor NOTE's informal `t = −sin(θ+π/3)` is wrong only in
  the overall sign/reality: `sin(θ+π/3) = cos(θ−π/6)`, and the true relation is `t = −cos θ` (the
  minus is the D2 convention `V₁ = −Σγ`; distributionally `−cos = cos` on the symmetric semicircle,
  which is why the 1-point MC still matched `cos θ`). This is exactly the failure mode
  `feedback_verify_root_system_against_defining_polynomial` names — caught here by the decidable check,
  not repeated.

## 1. The derivation

**Input (banked).** `L*(a) = T⁴ − e₁T³ + e₂T² − e₃T + e₄` with the P32-verified coefficient laws
`e₁=−V₁`, `e₂=e₁²−εp`, `e₃=εp·e₁`, `e₄=p²`, `ε=χ₂(−1)` (`d2_twist_rigidity_certificate`); and the
exact ζ₃-multiset (D2, 0 failures / 1030 cells):
`{α, ρα, −ᾱ, −ρ̄ᾱ}` for p≡3 mod 4, `{α, ρα, ᾱ, ρ̄ᾱ}` for p≡1 mod 4, `ρ=ζ₃`, `|α|=√p`. `[BANKED]`

**W-plane (Claim 1).** By the `g = deg gcd(L*(T), L*(ζ₃T)) = 2` law (`RESULT_n1_120deg_exact`),
exactly two roots have their ζ₃-multiple again a root: `{α, −ζ₃⁻¹ᾱ}` ↦ `{ζ₃α, −ᾱ}`. Set
`W = {α, β}`, `β = −ζ₃⁻¹ᾱ` (p≡3) / `+ζ₃⁻¹ᾱ` (p≡1); then `W⊗ψ = ζ₃·W`. Writing `α = √p e^{iφ}`, the W
eigenvalues are `√p e^{iφ}` and `√p e^{i(π/3−φ)}` (their arguments sum to π/3).

**Tensor-trace (Claim 2).** `V₁ = −(sum of 4 eigenvalues) = −[tr(W) + tr(W⊗ψ)] = −(1+ζ₃)tr(W)`.
Since `1+ζ₃ = ζ₆ = e^{iπ/3}`, and `tr(W) = 2√p e^{iπ/6} cos(φ−π/6)`, this gives
`V₁ = −2√p·e^{iπ/2}cos(φ−π/6) = −2i√p cos(φ−π/6)` — **purely imaginary** (p≡3), reproducing M4 as a
*consequence*, not an input.

**Half-trace (Claim 3).** `det W = αβ = ζ₆ p`, `√(det W) = √p e^{iπ/6}`, so
`cos θ = tr(W)/(2√(det W)) = cos(φ−π/6)` — real, θ = φ−π/6. Hence `t = Im(V₁)/(2√p) = −cos(φ−π/6) =
−cos θ`. The p≡1 arm is identical with θ = φ+π/3 and `t = Re(V₁)/(2√p) = −cos θ`. `det(H¹) =
ζ₃²·det(W)² = p²` closes consistently.

## 2. Decidable verification (the binding check)

`lmono_gkr_rank4_eigenderiv_v1.py`, two independent stages:

| stage | scope | worst residual |
|---|---|---|
| **A** abstract ansatz | 40 000 random φ × {43,61,349,100003} × both arms | e₂/e₃/e₄ laws ≤ 3.3e-15; Claim 2 ≤ 8.5e-16; Claim 3 ≤ 6.7e-16; half-trace imag ≤ 3.1e-16 |
| **B** REAL curve `V₁(a)` | p∈{43,67,79,127,349,61}, **all 672 cells**, both arms | g=2 W-plane found 672/672; Claim 2 ≤ 3.7e-14·√p; Claim 3 `t=−cosθ` ≤ 1.2e-14; half-trace imag ≤ 8.2e-15 |

STAGE A proves the multiset ansatz is coefficient-law-consistent for arbitrary α on `|α|=√p` (so any
real cell, whose `(V₁,L*)` satisfies those banked laws, is of this form) **and** that Claims 2–3 follow.
STAGE B confirms Claims 1–3 hold pointwise on the exact `V₁(a)` of real curves — including the
anomalous-order prime 61 and the non-squarefree-M primes 67, 79. A false identity would read O(1); the
observed residuals sit at the np.roots degree-4 conditioning floor.

## 3. What this delivers to the GKR argument

The candidate group is `G = SL₂ (diag on W) · μ₃ (Kummer on W⊗ψ) · {±1}` on `H¹ = W ⊕ (W⊗ψ)`. Sub-brick
1 supplies the two inputs GKR needs *before* the moment computation:
1. the **explicit rank-4 eigenvalue coordinates** `{α, β, ζ₃α, ζ₃β}` with the W-plane pinned from the
   L-polynomial (not informally) — the object over which the det-twisted moments are computed;
2. the **exact dictionary** measured↔group: `V₁ = −ζ₆ tr(W)`, `t = −cos θ` = the SL₂ half-trace of W.
   This is why the 1-point marginal is the SU(2) semicircle (`RESULT_monodromy_sato_tane_at_scale`) —
   now derived, not just measured — and fixes the normalization for every higher moment.

## 4. Scope / what this does NOT do (owed, per §2 discipline)

- **Does NOT pin the group.** A 1-point/trace dictionary is shared by `SU(2)`, `SU(2)×{finite center}`,
  and any group with the same W-trace. The **discriminating** step — the `⟨det⊗⟩`-masked 4th/higher
  moment invariants of `G` in the rank-4 rep, matched against the FFT-measurable cell statistics — is
  **sub-brick 2, OWED**. This brick makes that computation well-posed (it gives the eigenvalue
  coordinates symbolically, as sub-brick 2 requires) but does not perform it.
- `[VERIFIED]` at 6 primes ≤ 349, all cells — **not** a uniform-in-p proof (secp banner governs). The
  eigenvalue *form* is banked exact-at-8-primes (D2); the tensor-trace/half-trace identities are new
  and verified at these 6.
- The tensor split `H¹ ≅ W ⊕ (W⊗ψ)` is here a **numeric [2,2]** fact (trace-level), not yet an
  isomorphism of sheaves — that is route B (sheaf-isomorphism), separately owed.
