# RESULT — L-mono GKR sub-brick 2: the discriminating moment-invariant fingerprint of the candidate group, and the coset the cells actually sample

**Date 2026-08-24.** Second brick of the L-mono GKR campaign
(`PLAN_lmono_monodromy_campaign_v1.md` §5A/§7.1, sub-brick 2). Builds on sub-brick 1
(`RESULT_lmono_gkr_rank4_eigenderiv_v1.md`), which pinned the rank-4 eigenvalue coordinates
`tr_V = ε(1+ζ₃^j)χ(u)` symbolically + decidably. Delivers the group-side GKR fingerprint AND — the
load-bearing finding — establishes that the discriminating moment is **not** directly measurable from
the j-fixed cell data, which redirects the completion to the geometric/Katz input (route A §4) or the
sheaf isomorphism (route B).

**Scope line.** Group-theoretic + real-curve check on the n=1 (A_new/twist) channel of `y²=x³+7`.
**No leakage / key-recovery / ECDLP claim.** Output is a CHARACTERIZATION (moment fingerprints +
which coset the Frobenii occupy), never an avenue verdict. Grades: `[VERIFIED]` exact/decidable;
`[BANKED]` inherited. Artifacts: `lmono_gkr_moment_fingerprint_v1.py` (exact integer moments +
4M-sample Haar MC), and the coset check inline (reuses the D2 exact `V₁(a)`).

---

## 0. Headline

- **The candidate group's exact GKR fingerprint** (integer invariant dims `M_{a,b}=dim(V^{⊗a}⊗V^{∨⊗b})^G`):
  `M₁₁=2, M₂₀=1, M₂₂=12, M₃₁=10, M₄₀=10, M₃₃=110`. Confirmed by independent Haar MC. `[VERIFIED — exact]`
- **The discriminating invariant is the det-masked 4th moment `M₂₂ = ⟨|tr|⁴⟩ = 12`.** It is the ONLY
  low moment that separates the candidate (diagonal SL₂) from the "two independent SL₂ planes"
  alternative (`M₂₂ = 8`), which shares the candidate's entire 1-point / 2nd-moment signature
  (`M₁₁ = 2` both). `[VERIFIED — exact]`
- **`M₁₁ = 2` rules out the other natural alternatives** at the 2nd moment: ψ-trivial `W⊕W` (`M₁₁=4`),
  Sym³-irreducible (`M₁₁=1`), U(2)-diagonal / det-free (`M₁₁=4` + nonzero odd moments). `[VERIFIED — exact]`
- **LOAD-BEARING SCOPE FINDING.** The measured cells realize the μ₃ character at **j ∈ {1,2} only,
  never j = 0** (checked exactly, all 672 cells / 6 primes). Since `|1+ζ₃^j| = 1` for j∈{1,2} but `= 2`
  for j=0, the cell-measured `⟨|tr|⁴⟩` normalizes to `C₂ = 2`, **not** the full-group `M₂₂ = 12` (which
  is dominated by the j=0, weight-`|1+ζ₃⁰|⁴=16` term the cells never sample). **Therefore the
  discriminating moment cannot be read off the j-fixed cell data**; pinning diagonal-vs-independent
  needs the geometric Kummer variation (all j, via Katz — route A) or the sheaf isomorphism (route B).
  `[VERIFIED — exact]` This is a scope bound on the empirical route, stated with its object + power.

## 1. The fingerprint (exact, MC-confirmed)

Element `g = (u, j, ε)`, `u∈SU(2)`, `j∈Z/3`, `ε∈{±1}`; `tr_V(g)=ε(1+ζ₃^j)χ(u)`, `χ=2cosθ` (sub-brick 1).
Since χ is real and `E_u[χ^{2k}]=Catalan(k)`, `E_u[χ^{odd}]=0`:
$$M_{a,b}=[a{+}b\text{ even}]\cdot C_{(a+b)/2}\cdot \tfrac13\textstyle\sum_{j=0}^2 (1+\zeta_3^{j})^a(1+\zeta_3^{-j})^b.$$
`{±1}` kills every odd-total-degree moment; the `1/3 Σ_j` factor is the μ₃ average (integer-valued).

| model | M₁₁ | M₂₀ | M₂₂ | M₃₁ | M₄₀ | M₃₃ | reading |
|---|---|---|---|---|---|---|---|
| **G = SL₂·μ₃·{±}** (candidate) | **2** | 1 | **12** | 10 | 10 | 110 | 2 pieces; diagonal |
| ψ-trivial `W⊕W` | 4 | 4 | 32 | 32 | 32 | 320 | W′≅W (End dim 4) |
| Sym³ irreducible | 1 | 1 | 4 | 4 | 4 | 34 | irreducible |
| **indep SL₂×SL₂·μ₃** | **2** | 1 | **8** | 5 | 2 | 46 | 2 pieces; **un**correlated |
| U(2)-diag (det free) | 4 | 0 | 36 | 0 | 0 | 440 | χ complex; center U(1) |

MC (4×10⁶ Haar samples/model) reproduces every exact entry; max |MC−exact| over the three closed-form
models = 0.78 (at `M₃₃`, the 6th moment — MC variance; `M₁₁,M₂₀,M₂₂,M₄₀` land within 0.06).

**Why M₂₂ is the discriminator.** `M₁₁ = dim End_G(V)` counts irreducible pieces (2 for the candidate:
`W ≇ W⊗ψ`). The candidate and "independent SL₂×SL₂" both have two pieces, so both give `M₁₁=2`; they
differ only in whether the SL₂ acting on the two planes is the **same** element (diagonal) or two free
elements. That correlation is a 4th-moment effect: `⟨|tr|⁴⟩ = 12` (diagonal) vs `8` (independent).
This is exactly the "1-point marginal does not pin the group" gap flagged in
`NOTE_lmono_gkr_input_1point` §3, now made quantitative.

## 2. The coset the cells occupy (the scope finding)

By the 120° law (`RESULT_n1_120deg_exact`), every cell's spectrum contains a ζ₃-related pair — i.e. the
Kummer character takes a **nontrivial** value `ψ(Frob) = ζ₃^{±1}` at every cell. Checked exactly here:
all 672 cells (p∈{43,67,79,127,349,61}) carry both a ζ₃-neighbor and a ζ₃²-neighbor and **no cell has
j=0** (that is the a=0 baseline `√p·μ₆` alone). So:
- cell-sampled `⟨|tr_V|²⟩ = |1+ζ₃^{±1}|²·⟨χ²⟩ = 1·C₁` → the SU(2) semicircle (banked 1-point);
- cell-sampled `⟨|tr_V|⁴⟩ = 1·C₂ = 2` → the banked `m₄=1/8` in χ-normalization;
- the full-group `M₂₂=12 = C₂·(16+1+1)/3` needs the **j=0** term (weight 16), which the cells never visit.

**Consequence for the argument.** The discriminating full-group moment is carried by the geometric
Kummer monodromy (the μ₃ realized by *varying the twist parameter's geometric point*), not by the
arithmetic Frobenius values at the cells (which sit in the fixed `j=±1` coset). The empirical
cell-statistics route (sub-brick 3) can confirm the **coset** (cells match the `j=±1` slice of the
candidate — a genuine consistency check) but **cannot by itself** separate diagonal from independent.
That separation is the GKR completion and is owed to route A (geometric monodromy of the Kummer sheaf,
Katz — needs `citation-verifier`) or route B (establish `W′≅W⊗ψ` as sheaves).

## 3. What is done vs owed

**Done (this brick):** the exact candidate fingerprint; the exact fingerprints of 4 named alternatives;
the identification of `M₂₂` as the minimal diagonal-vs-independent discriminator; the exact proof that
the cell data occupies the `j=±1` coset and therefore does not carry `M₂₂`.

**Owed (sub-brick 3 / 4):**
1. **The geometric moment computation** — the moment of the sheaf over the *geometric* π₁ of the
   twist-parameter line (all j), the object GKR/Katz actually consumes. Requires the family's
   Kummer/hypergeometric presentation (`PREREG_D2_lang_hypergeometric_relin_v1`) and the Katz rigidity
   citations verified. This is where `M₂₂=12` becomes measurable/derivable.
2. **Route B alternative** — `W′≅W⊗ψ` as an isomorphism of sheaves (the 22-prime `[2,2]` certificates
   are its numeric shadow); this bypasses the moment match.
3. The `citation-verifier` gate on the Katz/GKR statements (project rule) before any grade promotion.

## 4. Scope / what this does NOT do

- `[VERIFIED — exact]` group theory; the "cells occupy j=±1" fact is exact at 6 primes ≤ 349, all
  cells — the secp banner (uniform-in-p) governs any extrapolation.
- Does **not** prove `G_geom = G`. It computes the fingerprint that a proof must match and shows which
  part of it the data can and cannot supply. No closure of the L-mono gap is claimed — the gap is
  precisely relocated to the geometric/Katz input.
- No monotone-statistic or float-threshold verdicts; all moment claims are exact integers (MC is
  confirmation only). No key/secret in any path.
