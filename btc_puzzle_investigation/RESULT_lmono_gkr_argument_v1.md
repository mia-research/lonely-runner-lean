# RESULT — L-mono GKR argument (routes A+B unified): the ζ₃-rigidity reduced to a named sheaf-construction gap, citation gate DISCHARGED

**Date 2026-08-24.** Capstone of the L-mono GKR campaign this session
(`PLAN_lmono_monodromy_campaign_v1.md` §5A/§5B). Assembles sub-bricks 1–2 + the route-B certificate +
the geometric/arithmetic resolution into one argument, with every Katz/GKR step carrying its
`citation-verifier` verdict and load-bearing condition. **Grade: `[VERIFIED-scope — reduction with one
named gap]`.** This is NOT a `[PROVED]` of the monodromy; it is a proof that the ζ₃-rigidity
(T1/T2/T3) follows from a single, explicitly stated hypothesis (the sheaf exists on a geometrically
connected base with `G_geom` constant in p), given theorems whose applicability is now verified.

**Scope line.** n=1 (A_new/twist) channel of `y²=x³+7`. **No leakage / ECDLP claim.** The prize is a
statement UNIFORM in p (incl. secp) — which finite-prime data cannot give and which the named gap is
exactly about. Grades: `[VERIFIED]` exact/decidable; `[CITED✓]` citation-verifier-passed;
`[BANKED]` inherited; `[OWED]` the gap. Predecessors: `RESULT_lmono_gkr_rank4_eigenderiv_v1`,
`RESULT_lmono_gkr_moment_fingerprint_v2`, `lmono_routeB_geom_iso_certificate_v1.py`,
`RESULT_monodromy_sato_tane_at_scale_v1`, `RESULT_n1_120deg_exact_v1`, `NOTE_cross_j_relevance_v1`.

---

## 0. Headline

- **The citation gate is DISCHARGED.** All four Katz/GKR theorems the argument uses were verified
  against primary sources (Katz LAMMLF Thm 1.1.6; ESDE 1.8.2 via FKM's verbatim reproduction; Kummer
  monodromy via Michel/Perret-Gentil; Deligne equidistribution = GKM Thm 3.6 = Weil II 3.5.3). Two
  clean SUPPORTS (Larsen, Kummer), two SUPPORTS-WITH-EXTRA-HYPOTHESIS (GKR, equidistribution) with the
  extra conditions named below. `[CITED✓]`
- **The geometric/arithmetic status of μ₃ is resolved** (was open, `NOTE_cross_j_relevance`): det(W_a)
  = ζ₆·p is **a-constant** (verified exactly, 968 cells / 8 primes) ⟹ the ζ₃ is an **arithmetic**
  twist ⟹ **G_geom⁰ = SL₂**, and the candidate **G_arith = SL₂·μ₃·{±1}**. `[VERIFIED]`
- **The {±1} in G is not ad hoc** — it is the GKR centre fibre-product {(g₁,g₂)∈SL₂×SL₂ : g₁g₂⁻¹∈{±1}}
  (FKM Rmk 2.5), i.e. the order-2 piece of the rank-1 twist relating the two planes. Structural, not a
  fudge factor.
- **The argument is a REDUCTION.** Every alternative monodromy is excluded (moment fingerprint +
  coset discriminator + the exact 120° law), the eigenvalue coordinates are pinned (sub-brick 1), and
  the theorems apply — CONDITIONAL on one gap: that the a-family is a lisse sheaf on a smooth
  geometrically-connected curve with geometric monodromy constant in p. `[OWED]` (§4).

## 1. Target and object

**Target (the prize, PLAN §1).** For every cell a and every p≡7 mod 12 (⊇ secp): the eigenvalue
multiset is a single ω-orbit-plus-negative-conjugate (T1) ⇔ roots(g₂)=ζ₃·roots(g₁) (T2) ⇔ the
Frobenius class lies in the ζ₃-saturated locus of the monodromy group (T3). The content beyond the
banked exact-at-22-primes 120° law is **uniformity in p**.

**Object.** The rank-4 `H¹_c(E, L_{χ₂(y)}⊗L_{χ_a})` as `a` varies; numerically `V = W ⊕ (W⊗ψ)`, ψ the
order-3 Kummer character (sub-brick 1). W rank-2; the two planes ζ₃-related.

## 2. The argument chain (each step: statement · citation verdict · condition status)

**(S1) G_geom⁰(W) = SL₂.** From Larsen's Alternative (LAMMLF Thm 1.1.6): W rank-2, reductive, 4th
moment M₄ = M_{2,2} = 2 ⟹ G ⊇ SL₂ **or** G finite mod scalars. `[CITED✓ SUPPORTS]`. The finite horn is
killed **directly**: a finite π₁-image gives finitely many Frobenius traces, contradicting the
continuous semicircle at 49,833 cells (`RESULT_monodromy_sato_tane_at_scale`, max dev 8.4e-4). So
G_geom⁰(W)=SL₂. *Condition — non-finiteness:* ESTABLISHED (at-scale continuity). *M₄=2:* the measured
`m₄=1/8` for the half-trace = C₂ (sub-brick 1 dictionary). `[BANKED]`

**(S2) The two planes are NOT independent** (monodromy ≠ full SL₂×SL₂). Coset 4th moment: diagonal→2,
independent→7; measured cells→1.84 (`RESULT_lmono_gkr_moment_fingerprint_v2`). Equivalently the exact
120° law puts 100% of Frobenii in the measure-zero diagonal locus of the independent group — impossible
if the monodromy were the full product. `[VERIFIED]`

**(S3) Hence W′ ≅ W ⊗ L, L rank-1** (GKR contrapositive). Goursat–Kolchin–Ribet: monodromy in
SL₂×SL₂ not the full product ⟹ ∃ rank-1 χ with W′≅W⊗χ **or** D(W′)≅W⊗χ (Katz ESDE 1.8.2, FKM Def
2.1/Lem 2.4). `[CITED✓ SUPPORTS-WITH-EXTRA-HYPOTHESIS]`. *Conditions:* (a) the dual branch collapses
because SL₂ is self-dual (Sp₂: `J g J⁻¹=(g⁻¹)ᵀ`) — APPLIES; (b) geometric irreducibility of W, purity,
simple-normalizer, Goursat-adaptedness — purity BANKED (Weil); irreducibility supported by the
non-abelian eigenvalue field + non-root-of-unity (`RESULT_anew_twisted_eigenvalues_nonabelian`,
route-B F3), stated as a condition to be pinned in the sheaf construction.

**(S4) L is geometrically trivial ⟹ μ₃ arithmetic, W′≅W geometrically.** det(W_a)=ζ₆·p is a-constant
(route-B certificate F1, 968 cells) ⟹ L's determinant-level content is a constant scalar ⟹ L is
geometrically trivial with arithmetic Frobenius value ζ₃. So geometrically the two planes coincide;
the ζ₃ (and its order-2 companion, the {±1}) live in G_arith. `[VERIFIED]` This is route B's conclusion
(the sheaf isomorphism), reached by Frobenius-trace rigidity, NOT by ω (see §5).

**(S5) Frobenii equidistribute in the arithmetic coset; the coset is ζ₃-saturated ⟹ T1/T2/T3 for all
cells.** Deligne equidistribution (GKM Thm 3.6): Frobenii equidistribute for Haar on the conjugacy
classes of (the maximal compact of) the monodromy group. `[CITED✓ SUPPORTS-WITH-EXTRA-HYPOTHESIS]`.
*Conditions:* (i) arithmetic vs geometric — here G_arith⊋G_geom, so the Frobenii live in the **coset**
(the j∈{1,2} slice we measured) — the theorem's coset form is exactly ours; (ii) weight-0
normalization (divide by √p) — APPLIES; (iii) base smooth geometrically connected, ℓ≠p — part of the
gap (§4). Every element of G_arith=SL₂·μ₃·{±} has ζ₃-saturated rank-4 spectrum by construction
(sub-brick 2), so T3 holds for the whole group ⟹ T1/T2 for every cell at once.

## 3. Alternatives excluded (the fingerprint, §2 of moment_fingerprint_v2)

| alternative | excluded by |
|---|---|
| ψ-trivial `W⊕W` (M₁₁=4) | M₁₁=2 (two distinct pieces) |
| Sym³ irreducible (M₁₁=1) | M₁₁=2 |
| U(2)-diagonal, det-free (M₁₁=4, odd moments) | M₁₁=2 + det(W) constant (S4) |
| independent SL₂×SL₂ (coset ⟨\|tr\|⁴⟩=7) | coset moment 1.84→2, and the exact 120° law (S2) |

## 4. The one remaining gap (`[OWED]`, the genuine hard core)

Every theorem in §2 is about a lisse sheaf `F` on a smooth geometrically-connected curve `U/F_q`. The
argument is complete **modulo** constructing that sheaf and controlling it uniformly in p:
1. **Sheaf realization.** Exhibit the a-family `{V₁(a)}` as (the trace function of) a lisse ℓ-adic sheaf
   `F` on a geometrically-connected base — the DFT-over-(Z/n) index a must be organized as an algebraic
   parameter (Kummer/hypergeometric presentation). Until this is pinned, S1–S5 are applied to a
   presumed sheaf.
2. **Constancy in p.** The exclusions and moment values are verified at ≤ 8 primes ≤ 349. Upgrading to
   "all p incl. secp" needs `G_geom` to be a fixed object across the specialization p→∞ (a rigidity /
   specialization argument on `F`), NOT a per-prime empirical average. **This is the uniformity the
   prize demands and finite-prime data cannot supply.**
3. **Geometric connectedness of the base** (Claim-4 condition iii) and **Goursat-adaptedness** (Claim-2)
   are properties of that same construction.

No part of §2 closes this gap; the session's finite-prime evidence is consistent with it but is not it.

## 5. Routes A and B unified; PLAN corrections

- **Route A = S1+S2+S3+S5** (Larsen + coset moment + GKR + equidistribution). **Route B = S3+S4** (the
  sheaf isomorphism W′≅W). They are the same argument viewed from the group side (A) and the sheaf side
  (B); B's conclusion (S4) is what makes A's coset (S5) ζ₃-saturated.
- **PLAN §5B correction.** §5B proposed producing W′≅W⊗ψ from the ω-intertwining. PLAN §3 itself
  retracts within-cell μ₃-equivariance (ω is a CROSS-cell map on the orbit {a,λa,λ²a}). So ω cannot
  furnish the within-cell isomorphism; the route that does is **Frobenius-trace rigidity** (S4,
  det-constancy + proportional traces + irreducibility), needing no ω. Recorded in
  `lmono_routeB_geom_iso_certificate_v1.py` header.
- **PLAN §7.1-item-1 correction** (from moment_fingerprint_v2): "match the FFT-measurable cell
  statistics" is sufficient to EXCLUDE the alternatives (coset moment), but the discriminating
  *full-group* number 12 is not cell-measurable; the pin uses the coset value + the theorems, not the
  full-group average.

## 6. Scope / grade

- **`[VERIFIED-scope — reduction]`**: given the §4 sheaf construction (the named gap), S1–S5 with the
  cited theorems yield G_geom⁰=SL₂, G_arith=SL₂·μ₃·{±}, and T1/T2/T3 uniform in p. The eigenvalue
  derivation (sub-brick 1) is decidably verified; the citations pass `citation-verifier`; every
  exclusion carries object+power+scope.
- **NOT `[PROVED]`**: the sheaf realization + constancy-in-p (§4) is open; without it the argument is a
  conditional reduction, and the 120° law remains `[PROVED-exact]` only at the 22 tested primes.
- **Citation-completeness debt:** Katz ESDE Prop 1.8.2 was verified through FKM's published verbatim
  reproduction, not the AM-124 original (not freely available); the primary-text pin is a minor owed
  item, not a gap in the logic.
- No key/secret in any path; no ECDLP consequence claimed or implied.
