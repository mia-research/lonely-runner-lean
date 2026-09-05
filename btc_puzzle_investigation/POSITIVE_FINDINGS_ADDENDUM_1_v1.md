> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# secp256k1 — Positive-Findings ADDENDUM 1 (v1, 2026-07-23)

**This document is ADDITIVE. It supersedes nothing.** It records only what was found **after**
`POSITIVE_FINDINGS_MASTER_v4.md` (frozen 2026-07-20 11:58) and is to be read **alongside** it, not
in place of it. Every Part, ledger row, frontier and retraction of v4 stands unless a numbered entry
below names the artifact that changes it.

**Why an addendum and not a v5.** The v3→v4 lineage carries a measured degradation failure mode
(`DEGRADATION_AUDIT_H3_TO_MASTER_v1.md`: live frontiers 5→0 across one consolidation, invisible to
tag counts). An additive document cannot lose a predecessor item, because it does not restate one.

**Reading order:** `POSITIVE_FINDINGS_MASTER_v4.md` → this file → the named `RESULT_*` artifact.

---

> ## ⚠ ALL FOUR v4 BANNERS APPLY VERBATIM AND ARE NOT RESTATED
> The **SCALE BANNER** (nothing measured at `p ≈ 2²⁵⁶`; ~239 binary orders of gap; a `[VERIFIED]` or
> `[EMPIRICAL]` row has **no power** against structure at cryptographic scale), the **LANGUAGE RULES**
> (`secure`/`closure`/`proven hard`/`unbreakable` forbidden; `flat`/`generic` is a statement about one
> statistic in one basis, never a verdict of absence), the **COMPILE RULE**, and the **ANOMALY-DRILL
> RULE** (output = characterization, never a verdict; every bound carries power and scope) govern
> every line below.
>
> **Two exceptions to the scale banner are claimed in this addendum and are marked where they occur:**
> §A1.1 (`A_new` supersingular — an algebraic proof with no measured input) and §A1.2 (the amicable
> pair — computed at the **actual** 256-bit `p` and `N_ord`, not extrapolated). §A3.2/§A3.3 are also
> full-scale (secp itself), but they are **nulls**, and their scope limit is the statistic family,
> not the curve size.

---

## 0. Source artifacts (2026-07-20 → 2026-07-23)

| artifact | object |
|---|---|
| `RESULT_d1_information_extraction_v1.md` | bits extracted by the D1/Aut-quotient transfer, measured |
| `RESULT_orbit_bit_ladder_v1.md` | the μ₂/μ₃/μ₆ bit ladder and its proved ceiling |
| `RESULT_localized_bit_extraction_v1.md` (+ `PREREG_…_DEVIATIONS.md`) | 30 local features × 25 scalar targets, 5 primes, exhaustive |
| `RESULT_mu6_cohomology_supersingular_v2.md` | **N2 closed** — `A_new` supersingular, proved |
| `RESULT_mu4_eigenvalue_individual_v1.md` (+ DEVIATIONS) | the four Frobenius eigenvalues individually; the `m`-law |
| `RESULT_jacobi_closed_form_m_law_v1…v4.md` | closed-form reduction of the `m`-law; v4 = self-audit |
| `RESULT_N1_P1_gate_and_tail_localization_v1.md` | N1: parity refuted, bulk moment blind, tail localization |
| `RESULT_joint_set_structure_map_v1.md` | full symmetry map of the joint `(x,y)` object |
| `RESULT_nkd_validity_topology_v1.md` | `(n,k,D)` validity domain as a static manifold |
| `RESULT_nkd_dterms_subsurface_v1.md` / `_v2.md` | the complexity filtration and its exact mechanism |
| `RESULT_lambda3_arm0_gate_v1.md` / `_arm1_subspace_v1.md` (+ DEVIATIONS) | the λ₃-eigenvector drill, Arms 0–2 |
| `RESULT_secp_amicable_pair_v1.md` | secp is a Silverman–Stange amicable pair (full-scale) |
| `RESULT_flap_lemmas_P1P2_proofstatus_v1…v3.md` | P1 theorem; P2 = class-number identity |
| `RESULT_harmonic_support_pattern_v1.md` (+ DEVIATIONS) | per-harmonic profile of `\|U(a₀,b,c)\|` |
| `RESULT_subrayleigh_deficit_locus_v1.md` (+ DEVIATIONS) | the deficit: mechanism refuted, locus found |
| `islands_jointset_run_v1.out`, `islands_glv_g1/g2_run_v1.out` | island curve-image joint-set tests, **at secp** |
| `flap_grouplaw_run_v1.out`, `flap_density_glv_run_v1.out` | flap ε under the group law, **at secp** |
| PREREGs: `harmonic_support_pattern`, `subrayleigh_deficit_locus`, `mu4_eigenvalue_individual`, `localized_bit_extraction`, `lambda3_eigenvector_isotype`, `N1_eigenvalue_starvation`, `islands_curveimage_jointset`, `islands_glv_beta_crossset`, `flap_grouplaw_transition`, `D2_lang_hypergeometric_relin`, `isotypic_faction_projection` | frozen specs |

---

# PART A1 — NEW PROVED RESULTS

## A1.1 `A_new` is supersingular at every `p ≡ 3 mod 4`, for every separable cubic — **including secp** `[PROVED — scale-free, curve-independent]`

*Artifact: `RESULT_mu6_cohomology_supersingular_v2.md`; decidable shadow `supersingular_mu4_mechanism_v1.py` / `.log`.*
*Closes v4 §A.3 row **N2** and v4 frontier **§XI.11**.*

Object: `A_new` = new part of `Jac(C)`, `C : w⁴ = f(x)`, `f` any separable cubic; `Jac(C) ~ E × A_new`,
`dim A_new = 2`.

**The proof, in three steps.**
1. `ζ₄ : (x,w) ↦ (x, i·w)` is an automorphism of `C` for **any** cubic, fixes `E = C/⟨ζ₄²⟩`, and acts
   on `H¹_new` with eigenvalues `±i` ⇒ `ζ₄² = −1` on `A_new` ⇒ `Q(i) ↪ End⁰(A_new)`, acting on the
   **whole** surface.
2. For `p ≡ 3 mod 4`, `σ(i) = i^p = −i`, so the Frobenius-twist relation `π φ = φ^σ π` gives
   **`π · ζ₄ · π⁻¹ = ζ₄⁻¹`** — non-commutative (commutativity would force `ζ₄² = 1`).
3. That relation is incompatible with both non-supersingular `p`-rank strata: ordinary (`End⁰` a
   commutative quartic CM field), and `p`-rank 1 in both its forms (simple with `End⁰` a field; or
   `E_ord × E_ss`, where disjoint Newton slopes give `Hom = 0` so **both** `i` and `π` preserve each
   factor and the ordinary factor's imaginary-quadratic field again forbids the conjugation). Only
   `p`-rank 0 remains. ∎

**Inputs: `p ≡ 3 mod 4` and `ζ₄ ∈ Aut(C)`. Both exact and scale-free. No CM input, no `j=0` input, no
measured input. Valid at `p = 2²⁵⁶−2³²−977`.** The mirror holds: at `p ≡ 1 mod 4`, `π` and `ζ₄`
commute and `A_new` is ordinary.

**Decidable shadow `[VERIFIED 42/42, 6 cubics × 42 primes 13→199]`:**
- **Fact 1 — `b₁ = 0` at every `p ≡ 3 mod 4`** (`b₁ = −tr(π|A_new)`; the `V_i ↔ V_{−i}` swap makes `π`
  block-off-diagonal). Generically `b₁ ≠ 0` at `p ≡ 1 mod 4`.
- **Fact 2 — supersingular at every `p ≡ 3 mod 4`:** `b₂ = m·p`, `m ∈ {−2,−1,0,1,2}`, every Frobenius
  root `= √p ·` (root of unity). With `b₁ = 0`, `L_new(T) = 1 + m·p·T² + p²T⁴` is a polynomial in `T²`
  ⇒ `A_new` is up to isogeny the **Weil restriction of an elliptic curve `E'/F_{p²}`**.
- **Curve-independence is the tell that the mechanism is the μ₄ cover and not CM:** CM cubics
  (`x³+7, x³+2, x³+11`) and non-CM cubics (`x³+2x+5, x³+x+1, x³−x+3`) behave identically —
  supersingular at every `p≡3 mod 4`, ordinary at every `p≡1 mod 4`. Only **which** supersingular
  class (`m`) varies.
- Independent 8/8 point-count check with sharp controls (`RESULT_joint_set_structure_map_v1.md` §5):
  `p = 29, 53` have `b₁ = 0` yet are **ordinary** ⇒ trace-zero is necessary, not sufficient; the
  switch is `p mod 4`.

**Two scope statements attached at source, carried here unchanged.**
- The reason previously given for this conclusion is **withdrawn** (§A4.27): "`p` inert in `Q(i)` ⇒
  supersingular" is the criterion for an **elliptic curve** with CM by `Q(i)`, applied to a surface
  where it does not directly hold. The old *conclusion* stands; the old *reason* does not.
- **Independent adversarial re-derivation of the two external inputs — the Frobenius-twist relation
  `π φ = φ^σ π`, and the surface `p`-rank/`End⁰` dichotomy — has not been run.** Both are standard.
  The artifact records this as the remaining diligence. The first draft of Step 3 used the false
  slogan "non-commutative `End⁰` ⇒ supersingular" (refuted by `E_ord × E_ss`) and was corrected.

**What follows and what does not.** P13 (`Hom(E,A_new) = 0` at secp, via Tate) no longer inherits an
unproved dimension-2 extrapolation. **Every downstream scope caveat of v4 §VII is unchanged.** Route 1
blocked (254-bit), Route 2 `Hom = 0`, **Route 3 OPEN** (`Õ(p^{4/3})`, one cover, not a family bound),
**D1 and D2 OPEN**, **N1 OPEN**. No security statement is made or implied.

## A1.2 secp256k1 is a Silverman–Stange **amicable pair**: `#E(F_p) = N_ord` **and** `#E(F_{N_ord}) = p` `[PROVED by verification — at the actual 256-bit primes]`

*Artifact: `RESULT_secp_amicable_pair_v1.md`.*

- Forward: `#E(F_p) = N_ord` (given; cofactor 1).
- **Return, verified here:** `E : y² = x³+7` reduced mod `N_ord` has `#E(F_{N_ord}) = p`. Test:
  `p·P = O` for **3 independent points** `P ∈ E(F_{N_ord})`; `p` prime ⇒ this forces the order.
  **Discriminating control:** the alternative sextic-twist candidate `N+1−2x` does **not** annihilate
  ⇒ the annihilation is not a small-subgroup artifact.
- **⇒ `(p, N_ord)` is an aliquot 2-cycle for `y²=x³+7`:** `p → N_ord → p`. Exact integers, no float in
  the arithmetic, full scale.

**The enforcing structure, named (not "chance"):**
- `t_p = p+1−N_ord` (129-bit) `= x_p + 3y_p` from `p = x_p² + 3y_p²`.
- The user's `t_N = 2 − t_p` is **correct but forced** by the universal identity `(π_n) = (π_p − 1)`
  (i.e. `#E(F_p) = N(Frob−1)`), which holds for **every** elliptic curve. Not special to secp.
- `t_N = 2 − t_p = x − 3y` **exactly** — one of `N`'s six sextic-twist traces `{±2x, ±(x+3y), ±(x−3y)}`
  ⇒ `p` is an *admissible* `#E(F_N)` a priori.
- **The unforced part is the twist selection:** admissibility does not force the return; the actual
  curve had to land on the `x−3y` twist, and it does. **Enforcing group = CM(ℤ[ω]) × the sextic-twist
  class of `b = 7`.**
- **Calibrated magnitude:** amicable pairs in this CM family have positive density; this project's own
  measurement is `13/50 ≈ 26%` (Silverman–Stange Conjecture 40, `secp256k1_arithmetic_v4.md` thread B).
  A ~1-in-4 CM event with a named cause.

**Bound:** curve-side / CM fact. **No d-side content, no private-key content, no ECDLP consequence.**
Whether the d-side Dirichlet island lattice (§A2.9) correlates with sextic parities across this bridge
is a separate, untested question — claimed in neither direction.

**Relation to the killed mechanism (unchanged):** `masked_structure_findings_v36` killed the
twist-as-*self*-symmetry mechanism for the `p≡7 mod 8` conservation (the reflection lands on the
conjugate prime `π̄` and does not descend to `F_p`). This result **confirms the amicable partner is a
real object that secp reaches**; it does **not** revive the killed self-symmetry.

## A1.3 The flap χ₂-imbalance **is a class number**: P1 is a theorem, P2 reduces to one identity

*Artifacts: `RESULT_flap_lemmas_P1P2_proofstatus_v1/v2/v3.md`; `scratchpad/prove_P2_hard_v1.py`.
`p ≡ 7 mod 12`, `H = (p−1)/2`, `ρ` a primitive 6th root; `h(−p)` by reduced-form count (validated).*

**Headline, verified at 134 primes `p < 4000`:**
```
S′ := Σ_{s∈T⁺} χ₂(s) = (3/2)·h(−p)·(1 − χ₂(2)),      O₊ − O₋ = h(−p)·(1 − χ₂(2))/2
```
so **`S′ = 0 ⟺ χ₂(2) = +1` (P2)**, and where it does not vanish (`p ≡ 3 mod 8`) the imbalance is
**exactly `h(−p)`**, the class number of `Q(√−p)`, split `O₊ − O₋ = h`.

| item | grade |
|---|---|
| **P1: `(−1)^N = χ₂(2)`** | **`[PROVED — THEOREM]`** (v2) |
| `S′ = A + C`; `C + C′ = A` | `[PROVED]` |
| **`A = Σ_{s=1}^{H} χ₂(s) = (2 − χ₂(2))·h(−p)`** (bijection `t = ρs` with `χ₂(ρ) = −1`, reflection `s ↔ p−s`, then Dirichlet's class-number formula) | **`[PROVED]`** |
| P2 structure `S′ = (3/2)h(1−χ₂(2))`, `O₊−O₋ = h·[p≡3 mod 8]` | `[VERIFIED, 134 primes]` |
| **(†) `C′ − C = Σ_{s=1}^{H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`** | **`[VERIFIED 134 primes, NOT PROVED]` — the single open step** |
| P2 easy direction `S′ = 0 ⇒ χ₂(2) = +1` | `[PROVED]` (via P1, unconditional) |
| P2 hard direction `χ₂(2) = +1 ⇒ S′ = 0` | reduced to (†); **not yet a theorem** |

Recorded at source: elementary character-sum manipulation of (†) is **circular** (every `s ↔ p−s` /
`t = ρs` step returns an equivalent form); (†) is a character-twisted class-number identity — the `3`
is the `Q(√−3)` (6th-root `ρ`) contribution — and needs analytic class-number / generalized-Dedekind-sum
machinery. No leakage or ECDLP content: pure CM / analytic number theory.

*Bearing on v4: this is the proof route for v4 §X.1's `p≡7 mod 8` conservation (`35/35` unforced) and
sits directly under v4 frontier §XI.8 (`L1`).*

## A1.4 The `Aut(E)` orbit bit-ladder has a **constant** ceiling `log₂ 6` `[PROVED]`

*Artifacts: `RESULT_orbit_bit_ladder_v1.md`, `RESULT_d1_information_extraction_v1.md`, `d1_bitmap.py`.*

`n` prime ⇒ `E(F_p)` has **no proper subgroups** ⇒ the only fibres any group-quotient map can have are
`Aut(E) = μ₆` orbits ⇒ **the whole family tops out at `log₂|Aut(E)| = log₂ 6 ≈ 2.585` bits, a constant
independent of key length.** No member of the family scales with `n`.

Measured ladder `[VERIFIED — 6 primes]` (image size → bits `= log₂ n − log₂ |image|`):

| p | n | μ₂ (negation) | μ₃ (GLV) | μ₆ (Aut) |
|---:|---:|---|---|---|
| 43 | 31 | 16 → 0.954 b | 11 → 1.495 b | 6 → 2.369 b |
| 67 | 79 | 40 → 0.982 b | 27 → 1.549 b | 14 → 2.496 b |
| 79 | 67 | 34 → 0.979 b | 23 → 1.543 b | 12 → 2.481 b |
| 127 | 127 | 64 → 0.989 b | 43 → 1.562 b | 22 → 2.529 b |
| 163 | 139 | 70 → 0.990 b | 47 → 1.564 b | 24 → 2.534 b |
| 211 | 199 | 100 → 0.993 b | 67 → 1.571 b | 34 → 2.549 b |

`μ₆ = μ₂ × μ₃`, coprime orders ⇒ the bits **chain additively**, `1 + log₂3 = log₂6`; the finite-`n`
deficit is the fixed-point/identity class.

**Where the D1 lift sits `[VERIFIED]`.** `ψ(P) = [get_place(x₀,v)] − [get_place(x₀,−v)]` on the quartic
Kummer cover `L = K[T]/(T⁴ − (x³+7))` has image `16/31` at `p=43` under plain linear equivalence **and**
up to sign — **identical**, so the 2-to-1 collapse is intrinsic to `ψ`, not an artifact of the "up to
sign" convention. `ψ` realises the **μ₂ rung ≈ 1 bit** — the bottom of the ladder. Separately `ψ` is
**not** a homomorphism even up to sign (`D₁+D₁ ≁ ±D₂`).

**Two objects, both measured, neither refuting the other `[VERIFIED]`:** for `d` uniform in `[1,n)`
the μ₆ orbit has 6 distinct members (20000/20000); for `d ∈ [2¹³⁴,2¹³⁵)` the μ₆ orbit meets the
interval in **exactly 1** member (200000/200000) — `−d ≡ n−d ≈ 2²⁵⁶` is outside the window and `λd`,
`λ²d` are multiplications by 256-bit constants, missing a 135-bit window with probability `1 − 2⁻¹²²`.
An automorphism folds an interval only if it maps that interval into itself; for `[2¹³⁴,2¹³⁵)`
recentred about 0, **negation does** (Galbraith–Ruprai PKC 2010, `≈√2`, 1.36× measured), `λ` does not.

**Conversion convention, recorded to prevent double-counting:** a quotient dividing the *search space*
by `k` divides a *square-root-time* runtime by `√k`. Full-group rho `2¹²⁸ → 2^126.7`; 135-bit interval
kangaroo `2^67.5 → 2^67.0` with recentred negation. Writing `2⁶⁷ → 2^64.4` applies a space factor to a
runtime and double-counts by `√6`.

**Scope:** the bound covers **only** maps that factor through an `Aut(E)`-quotient. `ψ` is
non-homomorphic and its image nonetheless factored through μ₂ — **one instance, not a bound over the
class of non-homomorphic set-maps.** v4 §X.3 (the non-homomorphic correspondence) stays **OPEN**;
`d1_bitmap.py` is a *partial* artifact for it. Higher-degree covers (`w^k = x³+7`, `k ≠ 4`), other
place-combinations, and non-Kummer constructions are unmeasured and outside every number above.
**Untested complement:** any non-group-symmetry map that is interval-compatible.

## A1.5 The low-complexity `(n,k,D)` stratum is exactly the **Dirichlet reciprocal-floor lattice** `[PROVED + VERIFIED identical sets]`

*Artifact: `RESULT_nkd_dterms_subsurface_v2.md`, `nkd_dterms_mechanism_v1.py`. d-side object; no leakage
or ECDLP claim. Exact integers.*

From the `d_terms` recursion, one greedy step on residual `D > 0` gives `err₁ = D − ⌊lo/⌊lo/D⌋⌋`, hence
```
T(D) = 1   ⟺   D = ⌊ lo / ⌊ lo / D ⌋ ⌋              (lo = 2^{N−1})
```
The fixed points of `f(D) = ⌊lo/⌊lo/D⌋⌋` are **exactly** the reciprocal-floor set `{⌊lo/q⌋ : q ≥ 1}`
(the Dirichlet hyperbola; `f` is idempotent, image = fixed-point set). Verified as **identical sets**
against direct `d_terms` enumeration: `N=28 (2,1)` → 22 150 = 22 150; `N=26 (3,1)` → 10 061 = 10 061.

**⇒ the `T=1` stratum is `{ base ± ⌊lo/q⌋ }` — a closed-form classical object, not an empirical set.**

**Exact island boundary at `√lo` `[PROVED + VERIFIED]`.** For `v ≤ √lo`, `⌊lo/⌊lo/v⌋⌋ = v`, so the
whole block `[1, ⌊√lo⌋]` is `T=1` — **one solid continent**; above `√lo` the reciprocal-floors are
spaced `~lo/q² > 1` apart and are **isolated singletons**. Measured at `N=28 (2,1)`, `√lo = 11 585`:
11 585 points ≤ √lo forming exactly **1 run**; 10 565 above, of which 7 762 are singletons;
`#components = 8 579` positive-side (×2 for `±` ⇒ 17 157, matching the v1 total). **`√lo = 2^{(N−1)/2}`
is the exact merge/island boundary.**

## A1.6 A gauge-free, basis-invariant covariant-weight form `[PROVED — re-derived]`

*Artifact: `RESULT_lambda3_arm1_subspace_v1.md`, prereg §0 (reduces to it at `m=1`).*
```
W_cov(V) = ⅔ − (1/3m)·tr( (UᴴDU)⁻¹ Uᴴ(N₁+N₂)U ),        V = span(U), dim m
```
with **exact-integer, walk-independent** matrices over the support `S`:
`N_k[c,c'] = #{x∈S : cell(x) = c, cell(β^k x) = c'}`, `D = diag(#{x : cell(x) = c})`. It is a trace,
hence invariant under `U → UR` — it needs only the subspace, never a gauge choice of eigenvector. The
walk enters only through **which** span is tested against this static μ₃-covariant geometry.
Machinery validated: R1 split identity `2·Σ_S = FIELD + CURVE + (χ₂=0 ledger)` exact to the integer,
6/6 primes; firing fires (known-covariant span → `1.000`; known-invariant span → `0.143`).

## A1.7 Three exact conservations of the joint object `U(a,b,c)`

*Artifacts: `RESULT_harmonic_support_pattern_v1.md`, `RESULT_subrayleigh_deficit_locus_v1.md`.
`U(a,b,c) = Σ_d e_p(b x_d + c y_d) e_n(−a d)`.*

1. **The alignment is an `l¹` norm.** With the phase-only aligned readout `F̂ = U/|U|` there is no
   cancellation, so `Corr(a₀) = (1/(n−1))·Σ_{(b,c)∈S} |U(a₀,b,c)|` — verified two ways (point-space
   reconstruction vs direct sum) to `rel ≤ 2.3e−16` at all 7 primes. **The per-harmonic contribution is
   the exact nonnegative number `|U(a₀,b,c)|`,** so "active vs starved" is a decidable statement about
   the distribution of those numbers, which no sector total can see.
2. **`Σ_{b,c} |U|² = p²(n−1)`, exactly** — *identically for the character and for every random
   unit-phase target* (`|char − rand|/pred ≤ 1.3e−16`). The `l²` budget is pinned and is
   **basis-invariant**: any unitary change of basis on the frequency space preserves it, so **no
   unitary transformation can create concentration** — it can only redistribute a fixed total. (A
   non-unitary/oblique transformation is a different class and is untested.)
3. **`Σ_{a mod n} |U(a,b,c)|² = n(n−1)`, exactly** at every fixed frequency `(b,c)` (since
   `Σ_a e_n(a(d−d')) = n·[d = d']`). The `n` character rows share a fixed per-frequency budget, of
   which the trivial row `|U(0,b,c)|²` (untwisted, `≤ (2√p+1)²` by Weil) takes a piece. **A random
   target is a single draw and satisfies no such constraint** — this is the one conservation the nulls
   do not carry. (Named as the next probe, §A5.17.)

Also verified exactly: `Σ|U|⁴ = p²·Σ_Δ H[Δ] e_n(a₀Δ)` (`rel ≤ 1.4e−15`) — the quadruple histogram
**is** the fourth moment, so any "quadruple-coincidence" arm and any "fourth-moment" arm are one test,
not two. `H[Δ]` was validated **integer-identical** to `O(n⁴)` brute force at `(p,n) = (13,7)` and
`(43,31)`, with `H_diag = (n−1)(2n−3)` matching its closed form.

---

# PART A2 — NEW MEASURED LAWS AND CHARACTERIZATIONS
*(The scale banner governs every row in this Part.)*

## A2.1 `m = b₂/p` is the quantum number naming all four Frobenius eigenvalues of `A_new` `[VERIFIED table + EMPIRICAL law]`

*Artifact: `RESULT_mu4_eigenvalue_individual_v1.md` + DEVIATIONS.*

At `p ≡ 3 mod 4` the μ₄ argument forces `b₁ = 0`, so `char(t) = t⁴ + m·p·t² + p²`; substituting
`t = √p·z` gives `z⁴ + m z² + 1 = 0`. **The integer `m` names all four eigenvalues individually:**

| `m` | eigenvalues | angles `θ` (units of π) | root order | minimal `k` with `π^k` scalar |
|---|---|---|---|---|
| `−2` | `√p·{1,1,−1,−1}` | `0,0,1,1` | 1, 2 | `k = 2`, `π² = +p·id` |
| `−1` | `√p·` primitive **12th** | `±1/6, ±5/6` | 12 | `k = 6`, `π⁶ = −p³·id` |
| `0` | `√p·` primitive 8th | `±1/4, ±3/4` | 8 | `k = 4`, `π⁴ = −p²·id` |
| `1` | `√p·{ω, ω², −ω, −ω²}` = primitive **3rd/6th** | `±1/3, ±2/3` | 3, 6 | `k = 6`, `π⁶ = +p³·id` |
| `2` | `√p·{i,i,−i,−i}` | `±1/2` (doubled) | 4 | `k = 2`, `π² = −p·id` |

Angles are taken by **table lookup on the integer `m`** (the floating-root-finding path is banned from
the verdict path by the prereg). `k(m)` is the smallest extension `F_{p^k}` over which Frobenius
becomes scalar — the first place the 2+2 splitting produces a **field**, not just a magnitude.

**The measured law `[EMPIRICAL]`, out-of-sample window `p ≡ 3 mod 4`, `200 < p < 500`, 26 primes,
`f = x³+B`, `B ∈ {7,2,11}` — strictly disjoint from the `13 ≤ p ≤ 199` rows that generated it:**
> **H1 — `p ≡ 11 mod 12` ⇒ `m = 2`.** 42/42 rows, `K1 = 26` **distinct configurations**, 0 violations.
> **H2 — `p ≡ 7 mod 12` ⇒ `m = −2` if `B^{(p−1)/3} ≡ 1` (cubic residue), else `m = 1`.** 36/36 rows,
> `K2 = 22` pre-committed (script computed 26; the **smaller pre-committed** number is used), 0 violations.

Null (frozen pre-run): `m` uniform on the in-sample CM support `{−2,1,2}`, independent across
**distinct configurations, not rows** ⇒ `3⁻²⁶` and `3⁻²²`.

**What carries H2 is the within-prime `B`-dependence:** at 10 of the 12 `p ≡ 7 mod 12` primes the three
cubics do **not** share an `m`, and the cubic-residue symbol picks the split every time
(`p=211 → (1,1,−2)`, `223 → (−2,−2,1)`, `283/307/499 → (1,−2,1)`, `331 → (−2,1,1)`, `439 → (−2,−2,1)`).
**No rule keyed to `p` alone can produce this.** Mandated per-`B` breakdown of the `m = −2` cell:
`{B=7: 6, B=2: 5, B=11: 1}` — **the `B=11` corner rests on a single row.**

**Controls, all fired before any verdict was read:** independent `χ₄` route `m = Re(S)/p`,
`S = Σ_{x∈F_{p²}} χ₄(f(x))`, computed by a separate function with its own enumeration and forbidden
from reading `b₂`/`P₂`/`a_C`/`a_E`/`L_new` — **155/155 out-of-sample + 30/30 in-sample agree exactly**;
Plant 1 (false `H1'`) fired with 42 violations; Plant 2 (`χ₄` on `f+1` vs `b₂` on `f`) fired 1/3;
Plant 3 (four `p ≡ 1 mod 4` rows) fired 2/4. Forced columns (`b₁=0`, `p|b₂`, `|m|≤2`) reported and
**not counted as evidence**.

**Scope, verbatim from source.** `[EMPIRICAL]`, not `[PROVED]`. **It does not transfer to
`p = 2²⁵⁶−2³²−977`; no statement about that prime's `m`, angles, or `k` is made there.** The scale-free
μ₄ argument covers `b₁ = 0` only — the *value* of `m` is exactly what it leaves open. **Zero power**
against any rule agreeing with H1/H2 on this window (e.g. keyed to `p mod 24`, or to the sextic rather
than cubic character). H2b (does `m` depend on `B` only through the cubic character?) had only **3**
testable configurations, not the 7 its prereg expected — **reported as consistent, `K = 3`, below its
own prereg's expectation and far below the `K ≥ 10` bar; not a confirmed independence.**
Recorded observation, not a hypothesis: `b₁ = 0` also occurs at `p = 233, 257` (`p ≡ 1 mod 4`) — the
converse of the μ₄ implication is **false**.

## A2.2 The `m`-law reduces to a single Jacobi sum; one sign law is the whole remaining gap

*Artifact: `RESULT_jacobi_closed_form_m_law_v4.md` (v4 = self-audit of v1–v3); `jacobi_closed_form_m_law_v2.sage` / `.log`; `m_branch_secp_v1.py`; `eig_check2.sage`; `distinct_config_recount_v1.py`.*

**The reduction `[PROVED — UNREVIEWED]`** (graded so at source: it is the author's own derivation plus
the author's own numerics; the CLAUDE.md §3/§7 independent adversarial pass has **not** been run).
With `q = p²`, `p ≡ 3 mod 4`, cubing 3-to-1 on `F_q^*`, and `Σ_u χ₄(u+B) = 0`:
```
S = Σ_{x∈F_q} χ₄(x³+B) = χ₃(B)·J(χ₃,χ₄) + χ̄₃(B)·J(χ̄₃,χ₄)                    (★)
```
- **(F1) `χ₄` is trivial on `F_p^*`** whenever `p ≡ 3 mod 4` (`(q−1)/4 = (p−1)(p+1)/4`, `4 | p+1`) —
  the quartic character of `B` drops out. `[PROVED]`
- **(F2) `χ₃` on `F_p^*` splits by `p mod 3`:** at `p ≡ 7 mod 12`, `χ₃(B) = χ₃'(B)²` (norm-lift),
  **nontrivial** ⇒ `B`-dependence via the cubic-residue symbol; at `p ≡ 11 mod 12`,
  `(q−1)/3 = (p−1)(p+1)/3` ⇒ `χ₃(B) = 1`, **trivial** ⇒ `S` is **independent of `B`**.
  *Source-flagged defect (A3): the norm-lift step `χ₃ = χ₃'∘N` was **asserted, not checked**, and the
  verification script's `χ₃` is defined by discrete log against an arbitrary generator, so which of the
  two cubic characters it realizes was never pinned. The conclusion is insensitive (the two enter (★)
  symmetrically), but the step as written is not established.*

**The single gap `[EMPIRICAL 12/12]`:**
```
J(χ₃,χ₄) = −p   for p ≡ 1 mod 3   (with p ≡ 3 mod 4);      J(χ₃,χ₄) = +p   for p ≡ 2 mod 3
```
`|J| = √q = p` is automatic; the content is that `J` is **real**, with sign set by `p mod 3`.
Verified `J = −p` at `p = 7,19,31,43,67,79` and `+p` at `p = 11,23,47,59,71,83`.
**Partial proof `[PARTIAL — not closed]`** via the Frobenius substitution `t ↦ t^p` with `χ₄∘φ = χ̄₄`:
at `p ≡ 2 mod 3`, `J = conj(J)` ⇒ **`J` real** ⇒ `J = ±p` (sign not derived); at `p ≡ 1 mod 3`,
`J = σ₇(J)` ⇒ **`J ∈ Q(ζ₃)`**, and rationality would additionally need `σ₅`-invariance — observed
numerically, **not derived**. Gauss-sum decomposition `J = G(χ₃)G(χ₄)/G(χ₃χ₄)` (exact, `gauss_id.sage`)
localizes the sign into `G(χ₄) = ±p` and `G(χ₃χ₄) = ∓G(χ₃)`. **Caveat carried:** the observed `G(χ₄)`
sign rule (`+p` at `p≡7 mod 8`, `−p` at `p≡3 mod 8`) is fitted to **three primes**, not retested
out-of-sample, and by drill rule **may not be named or used in a proof** until it is.

**Feeding the gap into (★) reproduces the whole measured law of §A2.1:**

| `p mod 12` | `χ₃(B)` | `J` | `S` | `m = Re(S)/p` | §A2.1 measured |
|---|---|---|---|---|---|
| 7 | 1 (cubic residue) | `−p` | `−2p` | **`−2`** | ✓ |
| 7 | `ω` (non-residue) | `−p` | `+p` | **`+1`** | ✓ |
| 11 | 1 (always) | `+p` | `+2p` | **`+2`** | ✓ (42/42) |

**Verification tally, corrected `[VERIFIED 15/15 DISTINCT]`.** v1–v3 reported "34/34 configurations".
34 `(p,B)` evaluations were run and all agreed, but **19 (56%) were algebraically forced and carry zero
information**: at `p ≡ 11 mod 12`, **F2 itself predicts `B`-independence**, so the three `B` at each
prime are **one** cell — counting them is circular, using the derivation's own prediction to confirm
the derivation (12 of the 19); and at `p = 7, 67, 79` all available `B` fall in the same cubic-residue
class (7 of the 19). Within-prime discrimination reproduced at `p = 19,31,43`; `B`-independence
confirmed at every `p ≡ 11 mod 12`; `S` an exact rational integer (`Im S = 0`) in every case.

**Why this would reach `2²⁵⁶` — and its exact standing.** Every input to (★) is `p mod 12` plus one
cubic-residue symbol; **neither grows with `p`**. *If* the sign law is proved, the `m`-law becomes
scale-free and applies at secp directly, with power/detection-floor arguments irrelevant because
nothing is being estimated. **The secp branch, exact** (`m_branch_secp_v1.py`): `p mod 12 = 7`,
`7^{(p−1)/3} mod p ≠ 1` ⇒ **`B = 7` is a cubic NON-residue** ⇒ under (★) with the gap, **`m = 1`**,
`π⁶ = +p³`, `k = 6`, eigenvalues `√p·{ω, ω², ζ₆, ζ₆⁵}` (primitive **3rd and 6th** roots, from
`u⁴+u²+1 = (u²+u+1)(u²−u+1)`), root orders `[3,3,6,6]`.
> **Status of that number: `[CONDITIONAL on the sign law]`. The predecessor's hard-scope line — "says
> nothing about `m` at `2²⁵⁶`" — STANDS.** Proving the sign law is exactly what would retire it.

**What this is not:** it pins the Frobenius eigenvalues of a supersingular abelian surface. **No ECDLP
or security claim; it extracts and approaches no bit of any scalar `d`.** Naming the eigenvalues of a
lift's *target* says nothing about whether the lift transports a discrete logarithm.

## A2.3 The joint `(x,y)` object: complete symmetry map `[VERIFIED exact]`

*Artifact: `RESULT_joint_set_structure_map_v1.md`; `joint_shadow_decompose_v1.py`, `joint_map.py`,
`joint_battery2.py`, `recon_sup.py`.*

**Reproduction `[VERIFIED, 2 independent implementations]`.** `ρ_inf = |Corr|/‖F‖_∞` with aligned
`F̂ = conj(U)/|U|`: `p=349` 0.9534 / 0.9530; `p=433` 0.9523 / 0.9453; `p=577` 0.9597 / 0.9555 — two
separately-written implementations agreeing to ~0.005; x-only reproduces the published 0.29–0.36; a
planted perfect character pins `ρ_inf = 0.997`. **The 0.93–0.96 joint magnitude is real.**

**…and the magnitude is generic in BOTH norms `[VERIFIED]`** — this session added the sup-norm control
M14 did not compute:

| p | `ρ₂` char / random | `ρ_inf` char / random |
|---|---|---|
| 163 | 0.9992 / 0.9993 | 0.9342 / 0.9325 |
| 349 | 0.9996 / 0.9997 | 0.9534 / 0.9567 |
| 433 | 0.9997 / 0.9997 | 0.9523 / 0.9449 |
| 577 | 0.9997 / 0.9997 | 0.9597 / 0.9448 |

**M14's control failure is therefore stronger than recorded: it holds in both normalizations.** The
0.93 is the coordinate geometry's phase-only reconstruction quality, in the sup-norm basis as well as
the `L²` basis. *(This does not touch H3's separate `[PROVED, by construction]` claim that a leaking
readout **exists** at DLP cost — that is a construction, not a discrimination statistic.)*

**The complete symmetry group, exact to 1e-11 at `p = 163…823`:**
`U(−a,b,c) = U(a,b,−c)` (x even, y odd); `U(a,b,c) = U(aλ, βb, c)` (GLV/μ₆, on **both** parity halves);
GLV phase rigidity `arg Uₒ(aλ,βb) − arg Uₒ(a,b)` has mean 0.000 and **std 0.000** — the μ₆ character
acts as a rigid phase, no residual phase freedom. **Exactly `{parity ℤ/2} × {GLV μ₆}`; everything else
tested is generic.**

**Forced energy layer:** parity split → ½ / ½ (0.4964/0.5036 at 163 → 0.4994/0.5006 at 823), odd half
exactly 0 on the `c = 0` line; the **6-cell budget (parity × μ₃) is equipartitioned**, each cell
0.1655–0.1679 ≈ 1/6.

**Statistical layer, all at the floor:** `|U|/√n` Rayleigh to 3 dp (mean 0.884 vs 0.886, var 0.216 vs
0.215); top-k mass and support overlap at chance (0.050); `max|U|/√p = 3.0–3.4` (odd half 2.1–2.5, even
2.0–2.5), **all under the Weil ceiling 4.0, no spike, odd-half max does not exceed even** — i.e. in the
tested range **no exceptional non-cancelling `(b,c)` was found** for H3's `T_y` max corner; odd-half
aligned phase carries no hidden `d`-encoding (best linear slope `s = a₀`, `R ≈ 0.64` = the known
alignment, residual std 2.40 vs random 1.81).

**Characterization `[SCOPED]`:** the character-specific content of the joint object is *exactly* the two
symmetries; within the 6 isotype cells energy is equipartitioned, magnitude Rayleigh, symmetry-phase
rigid. Those two symmetries **are** M16's barrier (μ₆-symmetric ⇒ constant on `{±d, ±λd, ±λ²d}`). **A
bounded characterization at `p ≤ 823` — an exact fence, not a "nothing here".**

## A2.4 The per-harmonic profile is **Rayleigh at `π/4`** `[EMPIRICAL, 7 primes 163…2089]`

*Artifact: `RESULT_harmonic_support_pattern_v1.md` + DEVIATIONS.*

**Question:** is the 0.93–0.96 joint alignment carried by a few "active" harmonics above "starved"
sectors — i.e. is there an active/starved split for a basis transformation to isolate?

| `p` | top1% mass | floor top1% | ratio | `N_eff/|S|` | `max/√p` |
|---|---|---|---|---|---|
| 163 | 0.0274 | 0.0265 | 1.033 | 0.7805 | 3.047 |
| 211 | 0.0263 | 0.0266 | 0.989 | 0.7851 | 3.147 |
| 349 | 0.0266 | 0.0266 | 1.001 | 0.7835 | 3.250 |
| 433 | 0.0266 | 0.0266 | 0.999 | 0.7836 | 3.049 |
| 577 | 0.0268 | 0.0266 | 1.007 | 0.7840 | 3.404 |
| 991 | 0.0267 | 0.0266 | 1.005 | 0.7836 | 3.412 |
| 2089 | 0.0268 | 0.0266 | 1.007 | 0.7839 | 3.549 |

**The positive identification.** `N_eff/|S| = 0.7805 → 0.7839` converging to **`π/4 = 0.785398`** — the
exact value for Rayleigh-distributed magnitudes (complex-Gaussian coefficients), `E|U|/√(E|U|²) =
√π/2 = 0.8862`. **The harmonic profile is Rayleigh: a sharp law, not an absence.** The alignment is an
aggregate of `~p²` harmonics each at `≈0.8√p`, with the shape fixed by the Gaussian ensemble. The same
holds **within each `χ₃` sector separately** (top1% = 0.0270, 0.0275, 0.0273 at `p=163`) — a
within-sector statement, not a re-measurement of the known `1/6` equipartition.

**In the `(b,c)` frequency basis there is no active/starved split to isolate:** the top 1% of harmonics
carry 2.7% of the alignment, exactly what the diffuse floor gives at every prime; removing the top 1%
removes 2.7%, as it does for a random target. Top-5% support Jaccard between character and random is
`0.0256 ± 0.0003` vs the chance value `0.05/1.95 = 0.02564` — equal to three decimals: **no common
active set exists.** Forced/consistent with the ceiling: `max/√p` climbs 3.05 → 3.55 against `4 + 1/√p`
while **random targets are not bound by it and exceed it** (`4.03√p` at `p=2089`).

**Scope of the null half, tightly:** *in the `(b,c)` Fourier basis, at these `p`, for the pre-committed
statistics.* Explicitly untested and outside it: **non-unitary/oblique transformations** (§A1.7-2 rules
out only unitary ones), bases other than `(b,c)` Fourier, higher-degree (non-linear) readouts,
concentration below the power floor, and `p > 2089`.

**A structural fact recorded in the deviations, not a result:** a realizable target `g` lives on only
`n−1 ≈ p` curve points, so `{U_g}` spans an `(n−1)`-dimensional subspace of the `p²` frequencies —
once `p²/100 > n−1` (true at every prime here) **no realizable target can concentrate on 1% of `S`**.
This forced the prereg's single planted control to be split into a synthetic-array plant (tests the
detector) and a realizable matched plant (tests separation); both fire.

## A2.5 The **sub-Rayleigh deficit**: real, survives the exact value-multiset control, and lives in the low tail

*Artifacts: `RESULT_harmonic_support_pattern_v1.md` §2 (discovery), `RESULT_subrayleigh_deficit_locus_v1.md` (drill) + DEVIATIONS.*

Because `Σ|U|² = p²(n−1)` is pinned (§A1.7-2), `N_eff/|S| = (mean|U|)²/mean(|U|²)` can differ from the
null **only** through `mean|U|` — so the whole effect is **one scalar**, `M1 = mean r`,
`r = |U|/√(mean|U|²)`, with `M2 = 1` by construction.

**Discovery `[EMPIRICAL, 7/7 primes]`:** the character's harmonics are on average **smaller** than a
random target's — a `0.06–0.10%` deficit, one-directional at all 7 primes, significance growing in `p`
(`−3.7σ` at 163 → **`−13.9σ`** at 2089). Opposite in direction from an "active harmonic": the character
is slightly **sub**-Rayleigh. Two candidate causes excluded numerically at discovery: the `(0,0)`
exclusion (a `2.3e−7` relative effect, four orders too small) and the ceiling (which bounds the max,
not the mean).

**Drill result 1 — it is NOT the value-multiset artifact `[EMPIRICAL]`.** Control MC2 permutes the
character's values, preserving the exact multiset (each non-trivial `n`-th root once), hence
`Σ_d g(d) = −1` and `U(0,0) = −1` exactly, destroying only the `d`-alignment.

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 |
|---|---|---|---|---|---|---|---|
| deficit vs MC1 | 0.358% | 0.046% | 0.149% | 0.129% | 0.096% | 0.119% | 0.098% |
| deficit vs MC2 | 0.351% | 0.045% | 0.145% | 0.131% | 0.097% | 0.118% | 0.098% |
| `z(M1)` vs MC2 | −3.78 | −0.63 | −3.32 | −4.35 | −3.60 | −8.06 | **−13.27** |

MC1 and MC2 agree to the third decimal at every prime. **Pooled Stouffer `Z(M1) = −13.99`, sign test
7/7 negative.** Sampling-without-replacement — the single most likely benign explanation — is
**excluded, not assumed away.**

**Drill result 2 — the pre-committed mechanism is REFUTED `[REFUTED]`.** The frozen prediction was
that lower `l¹` at fixed `l²` ⇒ more unequal magnitudes ⇒ **excess fourth moment**, carried by
quadruples where the group law and naive coordinate addition coincide (`Δ = d₁+d₂−d₃−d₄ ≡ 0`),
quantitatively frozen at `δlog M4 ≈ −4.4·δlog M1` (a `+0.35%` `M4` excess).
- **No `M4` excess:** pooled `Z(M4) = +0.95`, sign test **3/7** positive; only `p=163` gave `z = +4.37`.
- **No `Δ=0` enrichment:** `E = 1.88, 1.10, 1.37, 0.59, 0.57, 0.92, 1.19` with `z = +3.0, +0.3, +2.0,
  −2.7, −4.1, −1.1, +3.0` — **the sign alternates**; the `+3.0` at the smallest prime and the `−4.1` at
  `p=577` are both the small-prime chance patterns the drill rule exists to catch.
- Arms 2 and 3 are **one test**, by the exact identity of §A1.7.
- The derived candidate cause dies with it: `H[Δ]` is forced constant on orbits of `⟨λ,−1⟩` (negation
  `Δ→−Δ`, GLV `Δ→λΔ`), making `Δ=0` the unique fixed point, and at fixed group-law sum the chord
  relation `x₁+x₂ = m²−x_S` makes the slope involution `m ↦ −m` preserve the x-sum automatically.
  **The data say this is not what carries the deficit.**

**Drill result 3 — the locus IS found: the LOW tail `[EMPIRICAL]`.** Arm 1 decomposes the deficit into
three zones summing to it by construction:

| `p` | LOW (`r<0.5`) | MID (`0.5–1.5`) | HIGH (`r>1.5`) |
|---|---|---|---|
| 349 | **+137.5%** | −64.2% | +26.7% |
| 433 | **+136.4%** | −79.0% | +42.6% |
| 577 | **+166.5%** | −140.9% | +74.4% |
| 991 | **+129.3%** | −61.3% | +32.0% |
| 2089 | **+146.0%** | −89.4% | +43.4% |

Carried by the **LOW tail (dominant)** and the **HIGH tail (secondary)**, offset by a MID excess. Both
tails are sub-Rayleigh: the character has **more near-zero harmonics and fewer very large ones** (the
latter consistent with the Weil ceiling, which random targets do not obey). Direct count — an **~8%
excess of near-zero harmonics, stabilizing**: `#{r<0.10}` char vs MC2 = +14.3, +7.8, +9.2, **+7.8**,
**+7.9** %; `#{r<0.05}` = +6.2, +14.1, +7.6, +8.7, +8.0 %.
**This is why the `M4` arm came back null, and the two arms are consistent rather than contradictory:**
`r⁴ ≈ 0` for `r < 0.1`, so a deficit carried by the low tail is **invisible** to the fourth moment.
(`p=211` is uninformative in this decomposition — `z = −0.63`, no signal to decompose.)

**Drill result 4 — it is EVERY character, not `a₀` `[EMPIRICAL]`.** Over sampled orbit representatives
of `⟨λ,−1⟩` (distinct configurations, not rows), 24 sampled per prime: `z < −3` at 10/24 (`p=349`),
15/24 (433), 14/24 (577), **24/24** (991), **24/24** (2089); median `z` −2.50 → **−12.58**. Unanimous
at the two largest primes. **The finding is "characters are sub-Rayleigh relative to random targets" —
a property of the curve+character system, not of `a₀ = 1`.** Smaller primes fire less because
per-character power is lower, not because those characters differ. Forced check `P5`: an orbit-mate
`a = λa₀` reproduces `a₀`'s `mean r` to `≤ 2.5e−16` — exact equivariance, zero evidence.

**Scaling `[UNDERPOWERED — pre-declared]`.** Measured slope `s = −0.163` against the four pre-committed
candidates only, **no free exponent fit**: `1/log p` (−0.15, `Δ=0.013`), `const` (`Δ=0.163`), `1/√p`
(`Δ=0.337`), `1/n` (`Δ=0.837`). **`1/√p` and `1/n` are excluded; `const` vs `1/log p` cannot be
separated** (they differ by `≈1σ_s`, declared underpowered before the run). **No decay law is claimed.**

**All controls fired:** C-M2, C-EQ (integer pairing exact; relative equivariance `≤7.8e−13`), C-X
(`Σ|U|⁴` float-FFT vs exact integer, `rel ≤ 1.4e−15`), P1, P2, P3 (`H[Δ]` integer-identical to brute
force), P4 (`E_plant = 13.6–15.5` vs bar 4), P5.

**Scope:** model curves `y²=x³+7` only, `p ≤ 2089`, these statistics, these controls. Nothing about
`p = 2²⁵⁶−2³²−977` (the object requires a full group sum over all `d`). No ECDLP, extraction, or
security claim.

## A2.6 N1 (the ½ saturation): parity refuted as cause, bulk moment shown blind, anomaly localized to the extremal tail

*Artifact: `RESULT_N1_P1_gate_and_tail_localization_v1.md`; `chi2y_parity_saturation_v1.sage`,
`n1_P1_calibrator_gate_v1.sage`, `n1_P1_positive_control_v1.sage`. **This file yields no verdict on N1;
N1 is as unexplained after it as before it.***

**1. The parity mechanism: claim correct, consequence REFUTED `[MEASURED]`.** `−P = (x,−y)` so
`χ₂(y_{−P}) = χ₂(−1)·χ₂(y_P)`: at `p ≡ 3 mod 4` `χ₂(y)` is **odd** in `d`, at `p ≡ 1 mod 4` **even** —
verified exactly 10/10 primes, and this correctly accounts for M4 (`V(a)` purely imaginary vs purely
real). But the mechanism "oddness forbids coupling with even eigenspaces, starving two channels"
predicts `p ≡ 1 mod 4` must **not** sit at ½:

| `p mod 4` | primes | `χ₂(y)` parity | saturation `max|V(a)|/(4√p)` |
|---|---|---|---|
| 3 | 991, 1051, 1303, 1831, 2143 | **odd** 5/5 | 0.4966, 0.4944, 0.4879, 0.4975, 0.4959 |
| 1 | 1237, 1249, 1669, 2089, 2281 | **even** 5/5 | 0.4999, 0.4977, 0.4893, 0.4987, 0.4890 |

**Identical in both classes ⇒ parity as cause is refuted.** (These values, 0.488–0.500 at
`n ≈ 1000–2200`, sit above the recorded 6-prime figure 0.470 and are consistent with the recorded
sequence `0.432, 0.455, 0.477, 0.459, 0.500, 0.499` tending to exactly ½. **The tightness of that
convergence is a datum in its own right** and points at something exact rather than statistical.)

**2. The bulk 4th moment is structurally blind to the question `[MEASURED + REASONED]`.** The prereg's
run-blocking gate P1 (known-rank calibrators must separate) **FAILED**: `M4/n²` = 2.0234 (`χ₂(y)`,
dim 4), 2.0260 (`χ₂(x)`, dim 2), 2.0418 (`bx`, dim 3), 1.9948 (`bx+cy`, dim 4), **1.9211 random** at
`p=1303` — no separation. Per the pre-committed outcome cell: **PIPELINE DEFECT, no N1 verdict in
either direction.** The statistic is sound — positive control at `n=1249` gives `M4/n² = 156.13` (true
spectral rank 1), `312.25` (rank 2, exactly linear), `2.03` (random), a ~150× margin. **The failure is
a specification error:**
> "dim 4" is a **Weil bound on `max|V(a)| ≤ 4√p`. It is not a statement about DFT support.** `χ₂(y_d)`
> has full-support, random-looking spectrum with `|V(a)| ~ √p` at typical `a`; the dimension manifests
> only in how few frequencies approach the ceiling — `O(1)` out of `n`, contributing `O(n)` against a
> bulk of `O(n²)`. **No bulk average over all frequencies can ever detect it.** Any future statistic of
> that form is disqualified a priori.

**3. What this establishes: N1 is an extremal-tail phenomenon `[MEASURED]`.** Max **separates** the
readouts (`χ₂(y)` 0.470 vs `bx+cy` 0.876 — identical dimension, ceiling, frequency count, estimator);
bulk 4th moment **does not** (2.02 vs 1.99, both equal to random). The readouts are therefore **not**
noise — they demonstrably differ — and **the entire difference lives in the extremal tail of the
distribution of `|V(a)|/√p`.** This is the sharpest statement N1 has had.

**4. A candidate mechanism for the 2+2, with a live counterexample `[CANDIDATE — not confirmed]`**
(`RESULT_joint_set_structure_map_v1.md` §4). Two ½'s from the same coordinate's parity, both now shown
parity-class-independent: additive `e_p(cy)` odd-half energy of `U` is exactly ½ (§A2.3);
multiplicative `χ₂(y)` saturates ≈½ at **both** `p mod 4` classes (8 primes). **Candidate:** the
involution `[−1] : P ↦ −P` splits `A_new`'s 4-dimensional `H¹` into 2+2 by parity, and a
*definite-parity* `y`-readout couples to only its own 2-dim half ⇒ saturates a `4√p` (dim-4) ceiling at
exactly ½ — class-independent because *either* parity yields a 2-dim half, which is why the "odd causes
it" reading failed and the correct statement is "definite-parity ⇒ ½". This names N1's "2 of 4
eigenvalues" as the `[−1]`-eigenspace split, and §A1.1 Fact 1 names the same decomposition as the
`V_i ⊕ V_{−i}` Frobenius swap. **Unresolved tension keeping it a candidate:** `bx` (x-only, even
parity) saturates **0.909, not ½**. The resolution would have to be dimensional (`bx` against a dim-3
ceiling) and **has not been verified**. **Decidable test that would confirm or kill it:** compute the
dimensions of the `[−1] = ±1` eigenspaces on `H¹(A_new)` and whether `χ₂(y)`'s sum projects onto one
2-dim half. Not run.

**Correction carried from the source file (§A4.34):** the section originally concluded from the flat
bulk that there is "no concentrated sector to target". **Withdrawn as stated** — every readout in the
table (`χ₂(y)`, `χ₂(x)`, `bx`, `bx+cy`) is a **misaligned** readout, and H3 point 3 `[PROVED + CITED:
Weil/KS]` says a misaligned readout sees exactly `√p` noise *provably*, regardless of the curve. What
survives is the **differential between two misaligned readouts** (the misalignment cancels in the
comparison): a 1.86× max gap at identical dimension with identical bulk. M15/M20 are cited as context
and **inherit the same caveat — they must not be quoted as bounding aligned structure.**

## A2.7 The λ₃-eigenvector anomaly dissolves: the individual vector is **gauge**, the subspace shows **no covariant excess**

*Artifacts: `RESULT_lambda3_arm0_gate_v1.md` (Arm 0), `RESULT_lambda3_arm1_subspace_v1.md` (Arms 1–2),
DEVIATIONS D1–D10. Object: the `d→d+1` cell-walk transfer operator `M`, K=4 (16 states),
`p ∈ [2503, 3571]`.*

**Arm 0 (gate) `[VERIFIED, p ≤ 3571]`:**
1. **There is no isolated λ₃.** After a large Perron drop (`λ₁=1 → |λ₂| ≈ 0.11–0.15`) the subdominant
   `|λ|` pack into a narrow band with pairwise gaps **0.0005–0.024, every one inside the 3σ bootstrap
   noise (≈0.04–0.05)**; `Δ₂₃ < 3σ₂₃` at **8/8** powered primes; `Im λ₃ = 0` everywhere (a real band,
   not a conjugate pair).
2. **The individual λ₃ vector is unstable across half-orbits**, `S(v₃) = 0.002–0.571`, all `< 0.9` —
   **and so is the 2-dim `{v₂,v₃}` pair** (`S_sub = 0.30–0.78`), so the cluster is **more than
   2-dimensional**. Firing proves this is not generic underpower: at the same `n`, the SEP plant's
   genuinely well-defined vector reached `S > 0.9`.
3. **Firing calibration** used two analytic plants through the identical pipeline — SEP (gap 0.153) and
   an exactly-degenerate tensor chain DEGEN (gap 4.4e−16) — establishing `n* ≈ 2500` for a gap ≈0.15
   and reading DEGEN correctly as `S_sub ≫ S`.
4. **Power caveat (stated, stronger than the prereg anticipated):** the real subdominant gaps are
   **~0.02**, ≈7× smaller, and individual-eigenvector resolution scales `n ∝ 1/gap²` ⇒ resolving a real
   individual vector needs **`n ~ 10⁵–10⁶`**, at or beyond accessible prime-order range. The band is
   **near-degenerate/unresolved at accessible `n`** — neither "proven exactly degenerate" nor
   "well-defined".
5. Corroborating: the covariant weight is **K-dependent** — `w_cov(K=4,6,8,10) = 0.862, 0.729, 0.701,
   0.651` at `p=3571`, drifting down 0.21 (slowing). The K=4 "0.85" is K-inflated even before the gauge
   problem. *(Itself computed on the gauge `v₃`, so reported as color, not an independent invariant.)*

**Arms 1–2 (on the pre-committed redefined object) `[VERIFIED, p ≤ 3343, K=4]`:**
1. **The gauge "0.85" is not reproduced gauge-free.** On the only stably-defined slow-space object —
   the full non-Perron space (`m=15`, `S_sub = 1.000` exactly) — **`W_cov ≈ 0.667 ± 0.005` across 6
   primes: `⅔`, the trivial covariant dimension fraction.** The `m=1..5` modes show variable `W_cov`
   (0.53–0.78) but their spans are gauge-unstable (`S_sub = 0.005–0.80`) and are not interpretable.
   **No gauge-free "slower ⇒ more covariant" gradient exists**; the v25 `0.48→0.85` gradient was gauge.
2. **The one reproducible "excess" was a NULL-MISMATCH PHANTOM.** The first-pass unrestricted-random
   null flagged `W_cov(m=15) = 0.668 > 0.638` at **6/6** primes. But that null includes the stationary
   `π`-direction the non-Perron object excludes, and `w_cov(π) = 0` exactly, so
   `W_cov(non-Perron) = (16/15)·W_cov(full) = (16/15)·0.625 = 0.667` — **arithmetic, not structure**.
   With a **π-orthogonal matched null** the excess **vanishes at every `m`** (`m=8`: 0.663 vs 0.672;
   `m=12`: 0.654 vs 0.667; `m=15`: identical); if anything the slow modes sit marginally **below** it.
3. **FIELD/lattice, not CURVE/Weil.** `f_FIELD ≈ W_cov` at every `(p,m)`, differences `< 0.02`;
   removing the `χ₂(x³+7)` twist changes nothing. **H_FIELD confirmed, H_CURVE rejected.**
4. **Exact structural fact:** `w_cov(stationary) = 0.000` exactly, 6/6 — the Perron/cell-marginal vector
   is purely μ₃-invariant (the x-support is β-symmetric). This is what produces the `(16/15)` rescaling.

**Characterization:** the v25/v27 item "the λ₃ eigenvector is 85% μ₃-covariant, broadband, no closed
form" **dissolves** — there is no canonical λ₃ vector (Arm 0), and the well-defined slow-space
covariant weight is the ⅔ dimension fraction with **no excess** over a matched null, FIELD/lattice.
This **explains** v27's "no simple closed form": a non-canonical vector in a near-degenerate cluster
cannot have one. Consistent with the PROVED tensor structure (`C_T = C₁⊗C₁` has `λ₂ = λ₃ = 1/3`
**exactly** degenerate, v4 §X.10) and with `σ` being μ₃-invariant `[PROVED]`.

**Scope:** `p ≤ 3571` / `≤3343`, `K=4`, `y²=x³+7`, `p≡1 mod 3`, `#E` prime, first-generator orbit, this
walk operator. Nothing at `2²⁵⁶`. "No gradient" is scoped to **"no gradient in the stably-defined
range"** — the small-`m` (slowest) modes remain gauge-unresolved at accessible `n`.

## A2.8 The `(n,k,D)` validity domain is a **contractible Farey solid** realized as a 1-dimensional coprimality net

*Artifact: `RESULT_nkd_validity_topology_v1.md`, `nkd_topology_v1.py`. **d-side object; no leakage /
ECDLP claim.** Exact integers, `check_no_float` passes. **Complete up to the true cap `n ≤ 256`** — not
a scale-limited sample.*

**1. The surface is a contractible disk `[PROVED — exact, all Q]`.** Farey tessellation of order `Q`:
`χ = 1, β₀ = 1, β₁ = 0` at `Q = 32, 64, 128, 256` (at `Q=256`: `V=19949, E=39895, F=19947`). Simply
connected — no holes, no handles, no disconnected components.

**2. The fiber is a solid segment ⇒ the 3-D domain is a contractible solid `[PROVED — full
enumeration]`.** For fixed canonical `(n,k)`, `D = d − base` with `base` fixed ⇒ consecutive `d` give
consecutive `D`. Verified by complete enumeration (every key): `N = 14, 16, 18` → 8192, 32768, 131072
keys, **0 non-contiguous `D`-columns**. At `N=18` the realized-label count **= 19 949 = the Farey-256
vertex count: the domain has saturated.** Contractible base × contractible interval fiber ⇒
`β₀ = 1, β₁ = 0, β₂ = 0`.
**⇒ the hypothesis of non-trivial topology (holes / components) enforced by μ₆ is not borne out at the
surface/solid level.** Reported as the measured shape.

**3. Where rigidity does live: the domain is intrinsically 1-dimensional `[PROVED]`.** Among the 4
corners of any unit square, exactly one has both coordinates even ⇒ `gcd ≥ 2` ⇒ **no unit square is
ever fully coprime, `F = 0` in the grid realization at every `Q`.** At unit resolution the valid set is
a **net/filament network, never a filled sheet** — the precise sense in which it is a "fragmented
lattice": not holes in a surface, but the **absence of any 2-cell**. The domain is a graph.

**4. The net connectivity is arithmetic-structured, not generic `[VERIFIED — matched control, Q=128]`.**

| set | V | β₀ | β₁ |
|---|---|---|---|
| **coprime (VALID)** | 5022 | **116** | **396** |
| full triangle (no sieve) | 8256 | 1 | 0 |
| random, density-matched (8 seeds) | ~5020 | 206–246 | 105–157 (mean 129) |
| odd–odd-forbidden (one congruence) | 6176 | 1 | 1953 |

The valid net is **both more connected (116 vs ~226) and ~3× more cyclic (396 vs ~129)** than a
density-matched random set — not a generic consequence of the `6/π²` density. Control fires cleanly.
*Power/scope: global-density-matched null; a per-`n`-density null is the natural refinement.*

**5. The actual symmetry is a ℤ/2, and μ₆ is not on this object `[PROVED]`.** μ₆/GLV acts on the curve
side (`(X,Y) ↦ (βX,Y)`, `d ↦ λd mod N_ord`, `λ ~ 2¹²⁸`); on the band-position side `λd` scrambles the
band ⇒ **no μ₃/μ₆ action on this domain** — μ₆ sits on the `(X,Y)` image, across the ECDLP bijection.
The domain's symmetry is `k ↦ n−k` (`u ↦ 1−u`): preserves coprimality, free except the single center
`(2,1)`, acts on the disk as a reflection; any β₁ cycles come in ℤ/2-symmetric pairs.

## A2.9 The complexity filtration is where the d-side fragments — and the fragmentation is sub-generic

*Artifact: `RESULT_nkd_dterms_subsurface_v1.md` (+ `_v2.md` for the mechanism, §A1.5). Exact
enumeration; matched permutation control. Fibers 4·10⁴–7·10⁵ wide, `n ∈ {2,3,5,8}`, `N ∈ {26,28,30}`.*

**1. Exactly three complexity levels `[PROVED — exact, all fibers probed]`.** Every wide fiber has
`T ∈ {0,1,2}` — **max D-terms = 2** up to width 7·10⁵ (`N=30 (3,1)`: `{T=0}=1`, `{T=1}=89 619`,
`{T=2}=612 183`). `T=0` is the single base point, `T≤2` is the whole contiguous fiber, so **the only
non-trivial level is `t=1`.** *Scope: max-T may grow past 2 for wider fibers — untested above 7·10⁵.*

**2. At `t=1` the sub-surface shatters `[PROVED — exact]`.** `{D_terms ≤ 1}` breaks into tens of
thousands of disconnected components: `N=30 (3,1)` β₀ = **35 332**; `N=28 (2,1)` **17 157**;
`N=28 (5,2)` **14 147**; `N=26 (2,1)` **7 559**. **This is the non-trivial topology the full domain
lacks** — bounding reconstruction complexity to one term turns the smooth fiber-interval into a rigid,
fragmented object. Located precisely: it is the `T=1` stratum, not the full domain.

**3. The fragmentation is arithmetic-structured `[VERIFIED — matched permutation control, 20 seeds]`.**
Control permutes the `T`-multiset within the fiber (fixes `|A₁|`, randomizes arrangement):
real/ctrl = **0.465, 0.452, 0.527, 0.560, 0.600, 0.684** — **always `< 1`, stable across a 16× width
range.** The low-complexity points **cluster into ~2× longer contiguous runs** than a random
arrangement of the same multiset. Control fires cleanly (random ≈2× more components). Weak `n`-trend:
clustering strongest at small `n` (≈0.46 at `n=2`), relaxing toward `n=8` (≈0.68).

**4. The mechanism, and the correction `[PROVED + VERIFIED]`** (from `_v2`, see §A1.5): the clustering
is **the contiguous block `[1,√lo]` collapsing `~√lo` points into ONE component** where a random
arrangement of the same `|A₁|` would give `~√lo/2` runs. That single block is what halves the count.
**v1's guessed 2-adic mechanism is REFUTED** (§A4.36): recomputing `A₁` for a matched **odd prime**
`L ≈ 1.33·lo` gives the same block-plus-islands shape (`|A₁| = 25 394`, components 9 724, islands
12 017 vs `2²⁷`'s 22 150 / 8 579 / 10 565) — counts differ only through `L`'s size. **The law is the
Dirichlet reciprocal lattice, generic in `L`, with NO special role for the power of two.**

---

# PART A3 — NEW SCOPED NULLS (every one with a fired firing-control)

> Language rule, binding: each entry below is **at the matched floor for that readout / statistic /
> scale**, never "nothing there". A hidden aligned readout, another basis, or `2²⁵⁶` is consistent with
> every one of them.

## A3.1 Localized Bit Extraction battery — 30 local DLP-free features × 25 scalar targets, 5 primes, exhaustive over all `d`

*Artifact: `RESULT_localized_bit_extraction_v1.md` + DEVIATIONS D1–D3; `lbe_harness_v1.py`,
`lbe_run_v1.py`, `lbe_results_v1.pkl`. `p = 127 … 100003`, `n ≤ 99667`.*

**Design:** feature stage sees only the point, target stage only the scalar (**disjoint construction**,
enforced mechanically by a permutation-equivariance gate, not by a shuffle control). Pooled `G`-test per
cell, Holm–Bonferroni at FWER 0.01 over a frozen grid, plus a family omnibus. Matched null = the
group-automorphism relabel `F(P_{t·d}) ↔ T(d)`.

**Controls all behaved:** plant ladder fires at every prime; `E5`,`E6` forced-null silent at all 5;
random-feature row silent at all 5; `β` majority vote unanimous (1.0000) at all 5;
permutation-equivariance gate passes. **Measured power** (`e_min`, agreement bias): 0.50, 0.25, 0.10,
0.05, **0.02** at `p = 127, 1051, 10477, 46261, 100003` — consistently ~1.4× the analytic
`√(20/N)`, inside the 3× attenuation flag. **The pipeline is sensitive and the floor is known.**

**Primary outcome N1 (scoped bounded null).** Holm rejections at the discovery prime `p=100003`: **0**.
One rejection at `p=127` (the weakest prime, `e_min = 0.5`, 85% of cells failing χ² calibration) fires
at 1 of 5 ⇒ **outcome H2, chance pattern, not named, no mechanism proposed**. **No cell reaches the
replication criterion** (amended pre-data to ≥4/5 primes); the maximum is 2/5, reached by two cells,
and **both fail residual-structure consistency** — `B4_sign_y × T-b0` has the leading standardized
residual of **opposite sign** at its two firing primes; `C1_mu3pos × T-m7`'s leading residual cell
**moves** across primes.

**Pre-committed conclusion, verbatim:** *"Across the 30 enumerated local DLP-free features × 25
enumerated scalar targets, on 5 prime-order curves `y²=x³+7` with `p ≡ 1 mod 3`, `n < 10⁵`, exhaustive
over all `d`, no feature–target dependence was detected at family-wise `α = 0.01`. The detection floor
was `e_min = 0.02` at `p = 100003`, degrading to `0.50` at `p = 127`; dependencies with per-sample bias
below `e_min` are not excluded."* **This may not be written as "there is no leakage" and may not be
generalized beyond `p ≤ 10⁵` or beyond the enumerated grid.**

**A calibration finding that changes how the family is read.** χ²-based p-values show a consistent
**2–4× excess** of cells below nominal 0.01 at every prime — the signature one would naively read as
diffuse structure, and the reason the omnibus reached `P = 5.6e−05` at `p=1051`. **It is an artifact.**
The assumption-free matched-null **integer rank** shows no excess at any prime:

| `p` | 127 | 1051 | 10477 | 46261 | 100003 |
|---|---|---|---|---|---|
| χ² raw, ratio to chance | 3.81 | 3.63 | 2.35 | 3.36 | 2.97 |
| χ² Bartlett-corrected | 2.38 | 3.45 | 1.76 | 3.90 | 1.29 |
| **empirical rank** | **0.48** | **1.54** | **0.29** | **0.54** | **0.39** |

340–487 of 775 cells fail the KS calibration check against `chi2_df` and Bartlett rescaling does not
repair it. **Consequence (a):** the diffuse-dependence arm is **ABSTAINED, not closed** — the empirical
rank resolves only to `emp_p ≈ 0.005–0.012` and cannot test the family-wise level `1e−5` at all.
**Consequence (b):** any future run on this grid must report the empirical rank; **χ² Holm alone would
have produced a false positive here.**

**Object-level positives from the same run:**
1. **Cap Law verified exactly at 5 primes** — `flap ⟺ 2|A₁+s·A₂| > |DET|` matches `ε ≠ 0` on
   126/126, 1092/1092, 10638/10638, 46548/46548, **99666/99666** points. **Unforced content stated
   honestly:** the basis-orientation constant `s ∈ {±1}` is calibrated per prime, so each prime spends
   **1 bit** — the unforced agreement is `(p−1) − 1` bits, not `p−1`. Without that bit the naive
   `|u−v|` reading agrees on only ~49% at half the primes, where **the two flap sets are disjoint**.
2. **Core density → ¾:** 0.7619, 0.7802, 0.7535, 0.7449, **0.7488** — the `¾ : ⅛ : ⅛` spine law (P12)
   at every prime, converging with `n`.
3. **`P_d^{[7]G} = P_{7d}^{G}` exactly** — the identity that makes any two-generator "replication"
   arm a matched-null draw rather than an independent replicate. **Any design that replicates a
   scalar-leakage claim "across generators" is testing the wrong thing:** with `G' = [s]G` the run pairs
   `F(P_{sd})` with `T(d)`, which is precisely the relabel null, so a genuine leak would fire on `G`
   and **not** on `G'` and be discarded. (Deviation D1; the arm was re-purposed as a control row.)
4. **A forced exact symmetry, correctly not named:** in the exploratory μ₆ orbit-rank tables column 0 ≡
   column 2 entry-by-entry at every prime — **forced** (orbits pair as `O ↔ −O`, `x(−P) = x(P)`,
   negation reverses scalar ranks ⇒ `c_σ = c_{σ∘(0 2)}` identically; verified all 6 permutation classes,
   364 orbits, 0 self-negative). **Zero information**, logged because it is exactly the kind of
   exact-looking zero the count-only-unforced-hits rule exists to catch.

**Exploratory (not pre-registered), reported as such:** the frozen grid is **symmetry-mismatched** —
every enumerated target is an additive/digit function of `d` while the μ₆ action on scalars is
multiplicative. One post-hoc symmetry-matched pair (feature = rank of `x_d` among its GLV orbit's
x-coordinates, computable from `P`; target = rank of `d` among those scalars) gave
`emp_p = 0.122, 0.027, 0.928` at `p = 1051, 10477, 46261` — inconsistent, **null at the highest-power
prime**. A candidate that did not survive out-of-sample retest — **not a finding, and not a closure of
the μ₆-matched direction, which remains untested at `n > 5·10⁴`.**

**What this experiment does not test:** single-point features only; 2-way dependence only; the
enumerated grid only; `y²=x³+7` with `p≡1 mod 3` only; `p ≤ 10⁵` only. Named untested scalar subspaces:
high-bit windows above `k0+2`, non-binary Hamming statistics, multiplicative-order-indexed functions,
any μ₆-adapted target beyond the single probe. **Nothing here bears on secp256k1 itself.** Restated at
source: a leak of size `O(p^{−1/2})` is a bias `~2^{−128}` at cryptographic scale needing `~2^{256}`
samples; **a positive at `10⁵` would be fully consistent with total undetectability at `2²⁵⁶`, and the
null obtained here is evidence about `2²⁵⁶` in neither direction.** **Four arms open, none closed.**

## A3.2 Dirichlet-island curve image — joint-set structure, **at the real secp256k1**

*Artifacts: `PREREG_islands_curveimage_jointset_v1.md` (designed by the context-isolated
`experiment-designer`), `islands_curveimage_jointset_v1.py`, `islands_jointset_run_v1.out`.*

**Object, full-scale:** `E : y²=x³+7` over `p = 2²⁵⁶−2³²−977`, prime `N_ord`, standard `G`. Island
scalars `S_islands = { base ± ⌊lo/q⌋ : q ≥ 2 } ∩ [2^{N−1}, 2^N)` for `(n,k) = (2,1)` (§A1.5); point set
`𝒫 = { d_q·G }`. `N ≤ 255` ⇒ **no scalar wraps mod `N_ord`** (deliberate artifact avoidance), and
`X_i = X_j ⟺ d_i ≡ ±d_j` is band-impossible ⇒ **all island x-coordinates are distinct**, so any
off-diagonal collision is a genuine relation. **Tautology check passed before the run:** features read
the field-coordinate map `x(·), y(·)`, which is not part of the island (scalar-reciprocal)
construction ⇒ disjoint construction. **There is no `p ≈ 10⁵ → 2²⁵⁶` scale gap here** — the scope limit
is the statistic family and the island subset, not curve size.

**Statistics (each chosen to evade the single-point Weil/KS first-moment floor — all are fourth-moment
energies or quadratic windowed functionals):** `S1` additive energy of `x` (primary), `S2`
multiplicative energy of `x`, `S3` additive energy of `y`, `S4` windowed pair-difference concentration
of `x`; `S0` group additive energy = **control only, tautological** (it equals the additive energy of
the scalar multiset, computable without the curve, so a firing is never leakage).

**Result, `N ∈ {64, 128, 252}`, `M = 1024`, `B = 999` Null-B draws, `α* = 5/1200`:** `S1 = S2 = S3 =
2 096 128` = the baseline `2M²−M` **exactly, with excess `+0` and the null a point mass at the same
value** (`p_MC = 1000/1000`); `S4 = 2112 / 1982 / 2058` (in `N`-order 64 / 128 / 252) inside the null
range `[1828, 2298]` (`p_MC = 172 / 860 / 424 / 1000`). **All four arms null; the
arithmetic-progression comparison arm is null too.**

**Planted positives all fire:** `PC-2` (curve ±-pair) excess `+8186`, `p_MC = 1/1000`; `PC-3`
(residue AP) and `PC-4` (residue GP) excess `+7.1e8`, `p_MC = 1/1000`. Tautological control `S0` behaves
as designed (islands 3 333 284 / AP 715 828 224, both above the nulls).

**Scope:** these four statistic families, `M = 1024` islands from the `(n,k) = (2,1)` fiber, `N ∈ {64,
128, 252}`, this null. Untested: other Farey labels, other island subsets, larger `M`, higher-order or
non-energy joint statistics.

## A3.3 Dirichlet-island curve image — GLV/μ₃ β-cross-structure, **at the real secp256k1**

*Artifacts: `PREREG_islands_glv_beta_crossset_v1.md`, `islands_glv_beta_crossset_v1.py`,
`islands_glv_g1_run_v1.out`, `islands_glv_g2_run_v1.out`.*

**Tautology check recorded in the spec:** `X_i ≡ βX_j ⟺ d_i ≡ ±λ^{±1}d_j (mod N_ord)`; the islands are
**additive** in the reciprocal-floor lattice while `λ` is a **full-width multiplicative** cube root
unrelated to that construction (`λd_j mod N_ord` ranges over all of `[0,N_ord)`, not the ≤252-bit band)
⇒ **no identity forces a hit** ⇒ G1/G2 are non-tautological. The **additive** family (`d_i ± d_j ± d_k
≡ 0`: slopes, collinearity, group-additive energy, the `d⁺_q + d⁻_q = 2·base` anchor) **is** the
construction's own lattice ⇒ control only. `X_i = βX_i ⟺ X_i = 0` ⇒ **G1 has no diagonal**.

**Result at `N ∈ {64, 128, 252}`, `M = 1024`:** `G1` (exact pairwise GLV-orbit collision
`X_i ≡ β^{±1}X_j`) **= 0** for islands and for the AP arm, `B = 999` Null-B draws all 0 (the null is a
point mass at ≈`2M²/p ≈ 0`); `G2` (3-island GLV-additive closure, `B = 199`) **= 0**, null all 0.
**Plants fire:** `PC-φ` and `PC-φ²` give `G1 = 2` (expected 2); `PC-G2 = 1` (bar ≥1). Tautological
`C-add` = 0, band-impossible as predicted.

**Scope:** exact-algebraic GLV-orbit detectors on this island set at these `N`. Recorded object-level
fact from the spec: the μ₃/GLV action is multiplicative/projective, so **every exact GLV-orbit detector
is value-invariant under the global dilation `X ↦ βX`** — a literally non-invariant exact GLV statistic
does not exist (non-invariance needs an inhomogeneous reference: `Y`, a cube-character value, or the
additive lattice — all first-moment-floored, tautological, or metric).

## A3.4 The flap classifier `ε` under the group law, **at the real secp256k1**

*Artifacts: `PREREG_flap_grouplaw_transition_v1.md`, `flap_grouplaw_transition_v1.py`,
`flap_grouplaw_run_v1.out`. Established ARM-0 gates given: `CORE:FLAP = 3:1`; `ε(βX) = ε(X)`,
`ε(−X) = ε(X)` (μ₆-invariant); `ε ⊥` all multiplicative characters.*

**ARM-0 gate PASSED on secp itself:** μ₆ exceptions **0/65536**; flap density **16 273/65 536** (in
band). **The ε classifier is ARM-0-validated at the 256-bit prime.**

**Not-forced check in the spec:** `ε(2P) = ε(P)` would be forced only if `2P ∈ {±P, ±ωP, ±ω²P}`, i.e.
`2 ≡` a unit mod `N_ord`; `2` is not a `ℤ[ω]` unit, so it fails except the ≤2 three-torsion abscissae,
which are guard-excluded. Baselines: `2` invertible mod `N_ord` ⇒ `P ↦ 2P` is a bijection ⇒ `ε(2P)` is
¼-Bernoulli with the same marginal.

**T1 (doubling 2×2, primary/headline), `n = 10⁶` random valid abscissae:** `[CC=562083, CF=187173,
FC=188099, FF=62645]`; `P(F|F) = 0.24983` vs marginal 0.25000; `n_FF = 62 645` against
`E[n_FF | indep] ≈ 62 640`; **Fisher two-sided `p_MC = 9810/10000` → null.**

**Power calibration (the scope of that null, measured not asserted):** injecting `α·n` forced-equal
pairs fires at `α = 1/2¹` (`p = 1/10⁴`), `1/2³` (`p = 1/10⁴`), **`1/2⁶` (`p = 1/10⁴`)**, and is null at
`1/2⁹` (`p = 441/10⁴`). `PC-max` (`X ↦ βX`, forced diagonal) fires with `CF = FC = 0`.
**⇒ the null bounds group-law-induced flap dependence to below ~`2⁻⁶`–`2⁻⁹` of forced-equal pairs at
`n = 10⁶`, for the doubling map, with this 1-bit ε readout.** Dependence below that injection level is
not excluded.

## A3.5 Flap density is the same for 130-bit and 256-bit scalars

*Artifact: `flap_density_glv_prereg_v1.py`, `flap_density_glv_run_v1.out`, `N = 100 000`.*
`S130 = 0.24871`, `S256 = 0.25036`, true fraction `SREF = 0.24763`.
`gap(130−256) = −0.00165`, **`z = −0.85` → null**; `|S130 − ref| z = +0.56`, `|S256 − ref| z = +1.41`.
**The earlier 6000-sample gap was noise** (§A4.37). Scope: this density statistic, `N = 10⁵`, these two
bit-lengths.

## A3.6 No `d`-free selector predicts the per-harmonic magnitude

*Artifact: `RESULT_harmonic_support_pattern_v1.md` Arm C. Six selectors with a runtime tautology guard
(`args ⊆ {b,c,p,n}`; none may read `a₀`, `d`, `xs`, `ys`, or `U`), permutation null `R = 200`, 7 primes.*

`s1_legendre(b)` in-band 7/7 (AUC 0.498–0.502); `s5_c_zero` in-band 7/7; `s6_noise` (the negative plant)
in-band 7/7 — **comparator calibrated**. `s2_chi3(b)` hit `H = 27.9` at `p=163` (`p = 0.005`) and
**died at every larger prime** (5.05, 5.84, 5.00, 5.35, 1.12, 2.22 against null mean ≈2.1) — the
smallest prime in the set, failing to replicate at all six larger ones: a **small-prime chance
pattern**, not named. `s3_small_b` out-of-band 2/7 with **opposite signs**; `s4_glv_sector` out-of-band
2/7, in-band at the 3 largest primes. Effect sizes `|AUC − 0.5| ≤ 0.009`; 6 selectors × 7 primes at 95%
bands predicts ≈2 such hits by chance and 4 were seen.

**Scoped null:** no pre-committed `d`-free selector predicts `|U(a₀,b,c)|` above the permutation floor
**on these curves, at these `p`, for this selector list**. Bound to method + sample + floor — **not a
statement that no cheap selector exists.**

---

# PART A4 — RETRACTION LEDGER, CONTINUED  *(numbering continues v4 §XII; 1–26 there are unchanged and are not restated. Do not re-claim any of these.)*

27. **"`A_new` supersingular because `p` is inert in `Q(i)`"** → **the REASON is withdrawn; the
    CONCLUSION now has a proof (§A1.1).** `Q(i)` has degree 2 acting on a **dimension-2** surface —
    exactly the configuration v4 §XII.18 flags as *not CM and not decisive*. "`p` inert in `Q(i)` ⇒
    supersingular" is the criterion for an **elliptic curve** with CM by `Q(i)`. Replace every
    occurrence with the μ₄/quaternion argument. *(Master v4 L2 / P-A language and v4 §XI.11 are stale
    accordingly; the record was internally inconsistent because the master had not been updated, not
    because the result was shaky.)*
28. **"`m = 1` ⇒ eigenvalues `√p·{±ζ₁₂, ±ζ₁₂⁵}`"** → **FALSE.** Those are the primitive **12th** roots,
    which are the **`m = −1`** case (`Φ₁₂(u) = u⁴−u²+1`, `π⁶ = −p³`, root orders `[12,12,12,12]`).
    `m = 1` gives primitive **3rd/6th** roots, orders `[3,3,6,6]`. The error was inherited from an
    external pasted specification, propagated without being checked against the defining polynomial
    `u⁴ + m u² + 1 = 0`, into **two versions of the Jacobi result file and multiple conversational
    turns**, while **contradicting a correct memory the entire time**. **Caught by an object-level root-
    order computation (`eig_check2.sage`), not by rereading.** *Standing rule: derive a root system from
    its defining polynomial before repeating it, especially when it arrives from an external source; and
    when a new claim contradicts an existing memory, check the memory.*
29. **"34/34 configurations confirm the Jacobi reduction"** → **corrected to 15 distinct.** 19 (56%)
    were algebraically forced, and **12 of those were forced by step (F2) of the derivation being
    tested** — the hypothesis confirming itself. Recount: `distinct_config_recount_v1.py`.
30. **"the λ₃ eigenvector is 60→85% μ₃-covariant, broadband"** (v25/v27) → **retracted twice over.**
    (a) `[was EMPIRICAL, now GAUGE]` — it depends on which representative the eigensolver returns from a
    near-degenerate band and drifts with `K` (0.862 → 0.651 across `K = 4→10`); it is **not a property
    of a well-defined object**. (b) Even as a *subspace* claim there is **no covariant excess** — the
    apparent 6/6 excess was a **null mismatch**, the `(16/15)` rescaling from excluding a
    purely-invariant stationary vector. The load-bearing algebra `w_cov = ⅔(1−Re A)` is independently
    re-derived and reproduces v25's `p=433` number (0.596 vs 0.60): **the formula and the measurement
    agree; it is the interpretation as an individual-vector invariant that fails.**
31. **The D1 non-additivity was mis-scoped — in both directions, within one session.** (a) The claim was
    used at secp having dropped `d1_fast_affine_v1.log`'s own scope line (*"…at `p=43`"*); a multi-prime
    version with a torsion/defect-order test was written, **killed before emitting output, and never
    re-run**, while its conclusion was kept. (b) It was then over-corrected: M18's `0/666 additivity` was
    described as a `p=43`-only artifact, but **M18 records it at `p ∈ {43,67,79}`, 666 triples, controls
    fired — M18 stands.** Correct status: the `p=43` affine measurement is one small prime, one lift
    construction, no torsion test; M18 is three primes with controls.
32. **"the transfer map is public, so any inversion of it is an ECDLP solver"** → **invalid, withdrawn.**
    It proves too much: it would equally "refute" MOV/Frey–Rück, which are real attacks built from
    exactly such a public map. Data processing bounds **information** (`Q(P)` carries no more about `d`
    than `P` does), but transfer attacks never claim extra information — they claim the **target group
    is easier to invert in**. Information-preservation is not inversion-hardness.
33. **"DLP in `F_{p³}` at `p ~ 2²⁵⁶` is far above `2¹²⁸` and not feasible"** → **wrong, and wrong in the
    direction that favoured the conclusion it was used for.** Published prime-field DLP records reach
    ~795 bits, so a ~768-bit DLP sits at or near the feasible boundary. Small embedding degree is a
    genuine attack surface — it is why supersingular curves are avoided in cryptography. The real
    obstruction on that route is the **absence of a homomorphism** (`Hom(E,A_new) = 0`, P13), which is
    now unconditional at secp (§A1.1) but is **not** established by any `p=43` measurement.
34. **"the energy is flat, so there is no concentrated sector to target"** (`RESULT_N1_P1_gate…` §4) →
    **withdrawn as stated.** All four readouts in that table are **misaligned**, and H3 point 3
    `[PROVED + CITED]` says a misaligned readout sees exactly `√p` noise regardless of the curve — so
    the measurement is largely a fact about the instrument. **What survives is the differential between
    two misaligned readouts** (§A2.6-3). **M15/M20 inherit the same caveat and must not be quoted as
    bounding aligned structure.**
35. **"the 4th moment will settle starvation vs spreading in one integer"** → **wrong.** The statistic is
    **blind to the distinction** — both readings produce the same max and the same flat bulk. The
    pre-committed calibrator gate caught this **before** it produced a false answer, and the class is now
    disqualified a priori (§A2.6-2).
36. **"the D-term `T=1` clustering is 2-adic (because `lo = 2^{N−1}`)"** → **refuted by a matched
    control.** An odd prime `L ≈ 1.33·lo` reproduces the same block-plus-islands structure. The law is
    the **Dirichlet reciprocal lattice, generic in `L`** (§A2.9-4).
37. **The 6000-sample flap-density gap between 130-bit and 256-bit scalars** → **noise.** At
    `N = 10⁵`: `z = −0.85` (§A3.5).
38. **The prereg-frozen sub-Rayleigh mechanism (fourth-moment excess carried by `Δ = 0` quadruples,
    including the slope-involution derivation)** → **REFUTED by its own pre-committed quantitative
    threshold** (§A2.5). *Recorded as a retraction because it was a named derivation, and as a positive
    because the refutation was pre-committed rather than assessed after the fact.*

---

# PART A5 — FRONTIER LEDGER DELTA  *(v4 §XI.1–14 stand unless named here; new items continue the numbering)*

**Status changes to existing v4 frontiers:**

- **§XI.11 (N2 — is `A_new` supersingular at secp?)** → **RESOLVED-BY `RESULT_mu6_cohomology_supersingular_v2.md`**
  (§A1.1). *Attached caveat: independent adversarial re-derivation of the two standard external inputs
  is still outstanding.* v4 §A.3 row **N2 is discharged**; **N3, N4, N5, N6 are unchanged and open.**
- **§XI.10 (mechanism of the ½ saturation, N1)** → **STILL OPEN, now sharper.** Parity-as-cause
  **refuted** at 10 primes; the bulk-moment class of statistics **disqualified a priori**; the anomaly
  **localized to the extremal tail** of `|V(a)|/√p`. A candidate mechanism (the `[−1]`-involution 2+2
  parity split, matching §A1.1 Fact 1's `V_i ⊕ V_{−i}` swap) exists **with a live counterexample**
  (`bx`, even parity, saturates 0.909 not ½). **Decidable next test named:** dimensions of the
  `[−1] = ±1` eigenspaces on `H¹(A_new)`, and whether `χ₂(y)`'s sum projects onto one 2-dim half.
- **§XI.1 (a cheap partial of the joint (x,y) shadow)** → **STILL OPEN; one named sub-item is now
  bounded.** The **frequency-support / μ₃-grading pattern** — v4 listed it as "set up, pre-registration
  required, NOT YET RUN" — **has been run** (§A2.4): in the `(b,c)` Fourier basis the profile is
  Rayleigh at `π/4` with no active/starved split, and §A1.7-2 proves **no unitary basis change can
  create concentration**. **Everything else under §XI.1 is untouched and open**, and two new exclusions
  are explicit: **non-unitary/oblique transforms** and **higher-degree (non-linear) readouts**.
- **§XI.2 (the odd-half / `T_y` max corner)** → remains `RESOLVED-BY` KS; §A2.3 adds a direct
  measurement consistent with it (`max|U|/√p ≤ 3.4 < 4`, odd-half max not exceeding even, `p ≤ 823`).
- **§XI.3 (non-homomorphic amicable map)** → **OPEN, and its ambient object is now a verified fact**:
  the amicable partner is real and secp reaches it (§A1.2). The correspondence itself remains
  **UNANALYZED**; the protecting lift obstruction is still `[HEURISTIC]`.
- **§XI.8 (`L1`) / the `p≡7 mod 8` conservation** → **OPEN, narrowed to one identity.** P1 is a theorem
  and `A = (2−χ₂(2))h` is proved; the whole of P2 now hangs on **(†) `C′−C = 3h(−p)`** (§A1.3).
- **v4 §XI "Also live": "the λ₃ eigenvector ~85% μ₃-covariant, broadband, no closed form"** →
  **RESOLVED-BY `RESULT_lambda3_arm0_gate_v1.md` + `_arm1_subspace_v1.md`: gauge + trivial dimension
  fraction, no covariant excess, FIELD/lattice** (§A2.7). *The `λ₂ ~50% μ₃-covariant` item inherits the
  same gauge question and has not been separately re-run.*
- **v4 §X.3 (the non-homomorphic correspondence)** → **OPEN**, with `d1_bitmap.py` added as a **partial**
  artifact: one worked instance measured (§A1.4), the class not bounded.

**New frontiers:**

15. **The Jacobi sign law `J(χ₃,χ₄) = ∓p`** `[EMPIRICAL 12/12]`. **This single identity is the whole
    remaining gap** between the measured `m`-law and a scale-free one. Proving it (Gauss sums +
    Hasse–Davenport + subfield-trivial evaluation, both signs) makes the `m`-law apply at `2²⁵⁶`
    directly and promotes `m = 1` at secp from `[CONDITIONAL]` to `[PROVED]`. Sub-items: the `σ₅`
    -invariance step at `p ≡ 1 mod 3`; the `G(χ₄)` sign rule currently **fitted to three primes** and
    barred from use until retested out-of-sample; and the unverified norm-lift step `χ₃ = χ₃'∘N`.
16. **(†) `C′ − C = Σ_{s=1}^{H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`** `[VERIFIED 134 primes]`. The single
    open step of P2 (§A1.3). Elementary manipulation is provably circular; needs analytic class-number /
    generalized-Dedekind-sum machinery.
17. **The per-frequency conservation `Σ_{a mod n} |U(a,b,c)|² = n(n−1)`** — the one exact constraint the
    random-target nulls do **not** satisfy (§A1.7-3). **Decidable test:** is the ~8% near-zero excess at
    row `a₀` compensated by an excess of *large* `|U(a,b,c)|` at other `a` for the same `(b,c)` — i.e. is
    the low tail the shadow of this row-wise conservation? A joint statistic over `(a,b,c)`, not a
    marginal at fixed `a`; needs its own prereg.
18. **The `(b,c)`-locus of the sub-Rayleigh deficit and its equivariance.** Whether the
    character-minus-null magnitude difference has support equivariant under the exact `(a,b) ↦ (λa,βb)`
    action (available as an exact partition, `1e−12`). Distinct from every statistic frozen so far.
19. **The curve-side image of the `T=1` Dirichlet island lattice, beyond the tested families.** §A3.2/
    §A3.3 are null for four energy/windowed statistics and two exact GLV-orbit detectors, `M = 1024`,
    `(n,k) = (2,1)`. Open: other Farey labels, larger `M`, higher-order joint statistics, and the
    d-side↔curve-side question across the now-verified amicable bridge (§A1.2).
20. **μ₆-matched feature/target pairs at `n > 5·10⁴`.** The LBE grid is symmetry-mismatched by
    construction (additive/digit targets vs a multiplicative μ₆ action); the one exploratory probe was
    inconsistent and null at the highest-power prime. Needs its own pre-registration.
21. **Diffuse family-wise dependence in the LBE grid — ABSTAINED, not closed.** The empirical rank
    cannot resolve below `~5e−3` and therefore cannot test the family-wise level `1e−5`. Next step is
    **more null draws, not re-analysis of the existing data.**
22. **The `T=2` stratum and whether `T=3` ever opens.** Is there a *second*, nested reciprocal lattice
    `⌊lo/q₁⌋ ± ⌊lo/q₂⌋` inside `T ≤ 2`, with its own finer islands? And does a `T=3` stratum open past
    fiber width `10⁷`? (`max T = 2` is verified only up to `7·10⁵`.)
23. **Resolution of the individual slow-mode eigenvectors of the walk operator.** Requires
    `n ~ 10⁵–10⁶` by the measured `n ∝ 1/gap²` scaling — at or beyond accessible prime-order range.
    Until then the band is **near-degenerate/unresolved**, which is neither degenerate nor well-defined.
24. **A per-`n`-density null for the `(n,k)` coprimality net.** §A2.8-4's non-genericity is established
    against a **global**-density-matched null; the natural refinement is per-`n`. Also open: *which*
    cycles carry the ~3× β₁ excess — are the loops organized by Stern–Brocot depth / the
    continued-fraction tree? (A structured-vs-random **location** test, not a count.)
25. **The two untouched hunts** named at the close of the λ₃ drill: the **ε carry-trajectory**, and the
    **≥3-key / amicable joint-SET** object. Neither is addressed by anything in this addendum.

---

# PART A6 — METHOD NOTES THAT BIND FUTURE RUNS

Recorded because each was established by an artifact in this window, not by exhortation.

1. **Any design that "replicates a scalar-leakage claim across generators" is testing the wrong
   thing.** `P_d^{[s]G} = P_{sd}^{G}` exactly ⇒ the second generator **is** the matched relabel null. A
   genuine leak fires on `G` and **not** on `[s]G`, so a `≥k of 2k` replication rule across generators
   **selects against the hypothesis under test**. (§A3.1, deviation D1.)
2. **On this grid, χ²-based p-values are miscalibrated by 2–4× and Bartlett rescaling does not repair
   it; the assumption-free matched-null integer rank shows no excess.** Report the empirical rank.
   χ² Holm alone would have produced a false positive. (§A3.1.)
3. **A null must carry the object's own symmetry.** Excluding one purely-invariant vector rescales the
   statistic by `(16/15)` and an unrestricted null reads that arithmetic as a 6/6 "excess".
   (§A2.7, deviation D9 — the same class as v17's soft-shadow phantom.)
4. **A bulk average over all frequencies cannot detect a Weil-dimension effect** — the dimension lives
   in `O(1)` of `n` frequencies contributing `O(n)` against a bulk of `O(n²)`. The whole statistic class
   is disqualified a priori. (§A2.6-2.)
5. **`r⁴ ≈ 0` for `r < 0.1`:** a fourth moment is blind to inequality carried in the **low** tail. A
   null `M4` arm and a positive low-tail finding are **consistent**, not contradictory. (§A2.5.)
6. **No realizable target can concentrate on a small fraction of the frequency space:** `{U_g}` spans
   an `(n−1)`-dimensional subspace of `p²` frequencies. A plant that tests a *detector* and a plant that
   tests *separation from a realizable null* are two different objects and must be built separately.
   (§A2.4, deviation D1.)
7. **Count distinct configurations, never rows** — and check whether the derivation under test itself
   *predicts* the invariance being counted (§A4.29: 12 of 19 forced agreements were circular).
8. **Derive a root system from its defining polynomial before repeating it**, especially from an
   external source; when a new claim contradicts an existing memory, check the memory (§A4.28).
9. **The unforced content of a calibrated law is `(bits) − (calibration bits)`.** The Cap Law spends
   1 bit per prime on basis orientation; report `(p−1) − 1`, not `p−1`. (§A3.1.)
10. **A null's scope is its measured power, stated as an injection level, not asserted.** §A3.4 bounds
    group-law flap dependence below ~`2⁻⁶`–`2⁻⁹` of forced-equal pairs *because the injection ladder was
    run*, not because the p-value was large.

---

*Every claim above is traceable to a named artifact in `btc_puzzle_investigation/`. Grades are carried
verbatim from those artifacts; where an artifact grades its own work `[PROVED — UNREVIEWED]` or
`[PROVED — pending independent review]`, that qualifier is reproduced here and must not be dropped on
promotion. Nothing in this document is promoted into `POSITIVE_FINDINGS_MASTER_*` — that promotion is
gated by `compile-diff` (CLAUDE.md §2).*

*No ECDLP, key-recovery, or security claim is made or implied anywhere in this addendum.*
