# Findings v20 — S₄⁺ elimination complexity: the first-fall degree is curve-independent

**Date:** 2026-07-17 · `semaev_elimination_v1.py` (SageMath 10.9, exact GF(p)/QQ, no float in the
signal path). Item #1 of the ranked menu — the elimination / Gröbner / first-fall structure of the
Semaev point-decomposition **system** an index-calculus attacker faces over a prime field. Prior repo
work (v9/v10/v11) counted relation/decomposition **yield** (generic) and v13 analysed a **single**
polynomial (S₃ discriminant); nothing built or solved a Semaev **system** or measured a first-fall /
solving degree. This does, with matched CM / non-CM controls.

(v19 is reserved for the dangling critical-exponent note cited in `cap_law_proofs_v1.md`; this is v20.)

---

## Headline (graded)

**The first-fall degree of the prime-field summation-polynomial decomposition system is
curve-independent — so secp256k1's CM/GLV structure gives no index-calculus elimination lever beyond
the trivial |Aut|≤6 factor.** This is *proved* at the first-fall level (leading-form / isobaric
argument, general m) and *confirmed numerically* at the solving-degree level in a rigorously matched
control. It advances the hardness picture one honest step past "yield is generic": there is a
structural reason no CM lever appears where index calculus actually spends its cost.

---

## Setup

The faithful prime-field decomposition (Semaev-2015 / Kosters–Yeo): factor base `F={P : x(P)∈V}`,
`|V|=B`; decompose target `R` (x-coord `t`) by `S_{m+1}(x₁,…,x_m,t)=0` with all `x_i∈V`. As an
algebraic system with `V = roots of g(x)` (deg B):
> **{ S_{m+1}(x₁,…,x_m,t)=0, g(x₁)=0, …, g(x_m)=0 }**  — m+1 eqns, m unknowns.
Its first-fall / solving degree governs the per-decomposition Gröbner cost, which dominates the
index-calculus running time.

**Construction verified** `[VERIFIED]`: S₃ (deg 4, 9 terms), S₄ (deg 12, deg-4/var, 191 terms), S₅
(deg 32) built by resultants; group-law check = 0 failures on 30 random real m-tuples per curve
(`P₁+…+P_m+P_tgt=O ⇒ S_{m+1}=0`), p=211 and 307.

---

## 1. `[PROVED, general m]` The leading form of S_{m+1} is curve-independent (isobaric)

**Lemma (isobaric homogeneity).** Under the grading `wt(x_i)=1, wt(A)=2, wt(B)=3`, every Semaev
polynomial `S_m` for `y²=x³+Ax+B` is isobaric (weighted-homogeneous). *Proof.* `S₃` is isobaric of
weighted degree 4 (direct check — all monomials have weight 4). The recursion
`S_{k+1}=Res_X(S_k(…,X), S₃(…,X))` with `wt(X)=1` is a resultant of isobaric forms, and the resultant
of weighted-homogeneous polynomials is weighted-homogeneous; by induction every `S_m` is isobaric. ∎
*Verified symbolically over ℚ[A,B]:* S₃ weight 4, S₄ weight 12 (single weighted degree present).

**Corollary (leading form is A,B-free).** In an isobaric `S_m`, a monomial `x^α A^a B^b` has ordinary
total degree `|α| = W_m − 2a − 3b ≤ W_m`, with equality iff `a=b=0`. So the **top-total-degree form of
`S_m` contains no A,B** — it is the summation polynomial of the degenerate curve `y²=x³`, the same for
every curve. *Verified numerically:* the leading form of S₄ (deg 12, 35 monomials) and S₅ (deg 32, 495
monomials) is **identical across 4 distinct curves** (secp-form, a non-CM curve, j=1728, another).

**Consequence for first-fall degree** `[PROVED given the cited definition]`: the field equations
`g(x_i)` have leading form `x_i^B` (curve-independent), so the whole system's leading forms are
curve-independent. The first-fall degree — equivalently the degree of regularity of the top-degree
homogeneous system `[CITED: Bardet–Faugère–Salvy]` — is a function of the leading forms alone. Hence
**the first-fall degree of the decomposition system is identical for secp256k1 and every elliptic
curve over F_p of the same (B, m). No CM/GLV first-fall lever exists.**

---

## 2. `[EMPIRICAL, matched control]` Numerical confirmation — degrees identical across curves

Rigorously matched control: **identical** random factor-base roots `V` and target `t` across all
three curves, so the only difference is `(A,B)` inside `S_{m+1}`'s lower-order terms.

| p=211, m=3 | | secp (j=0, CM ℤ[ω]) | non-CM generic | j=1728 (CM ℤ[i]) |
|---|---|---|---|---|
| B=2 | d_ff / d_solv | **12 / 15** | **12 / 15** | **12 / 15** |
| B=3 | d_ff / d_solv | **12 / 18** | **12 / 18** | **12 / 18** |

Identical to the last digit — first-fall **and** solving degree are curve-independent in the matched
control. (`d_solv = deg S_{m+1} + m(B−1)`: field-equation-driven, curve-blind; targets are the typical
inconsistent case — a failed decomposition attempt, quotient dim 0 — which is what index calculus
spends most of its time on.)

**Non-matched consistent targets (per-curve decomposable R):** solving degrees cluster at 17–20 with
**target-draw noise, no stable secp advantage** — across seeds 1–4 the solution *count* wanders with
the random factor base (secp quo = 12, 6, 12, 9; j=1728 once 10) while `d_solv` stays 19–20 for all
curves. The apparent |V|=4 "secp lower d_solv" at one seed does **not** replicate. `[SCOPED: p=211,
m=3, these draws]`

**μ₃-lever test** `[EMPIRICAL]`: a β-invariant factor base `V` (closed under `x↦βx`, so the system
inherits the μ₃ symmetry of S₄) vs a random `V` of the same size (|V|=9), on secp, consistent target.
**Same first-fall degree d_ff = 17 for both** (p=211 and p=307). The β-invariant base changes only the
solution *count* (quo 30 vs 6), not the first-fall degree. **The μ₃ symmetry gives no first-fall
lever** — consistent with the v17 result that the only cheaply-usable reduction is |Aut|≤6.

---

## 3. `[VERIFIED-scope, negative]` Piece A: v13's fibre-smoothness does NOT climb to S₄

v13 proved, for S₃, `Δ(t)=−86704128·(t³+7)⁴` ⇒ the fixed-target curve `C_t:S₃(x₁,x₂,t)=0` is smooth
genus-1 for **every** target under prime order. The analogous question for S₄ (the m=3 relation
variety `V_t = {S₄(x₁,x₂,x₃,t)=0}`): eliminating `x₁,x₂,x₃` from `(S₄, ∂S₄/∂x₁, ∂S₄/∂x₂, ∂S₄/∂x₃)`
returns the **zero ideal** over GF(211) — i.e. the singular-fibre locus is all of `t`. Direct check:
**12/12 random fibres V_t have a singular affine point.**

**So v13's clean statement is special to m=2.** For m≥3 the relation variety is ≥2-dimensional and
carries diagonal / degenerate-summand singular configurations present for *every* target; the naive
"smooth fibre for all t" non-degeneracy does not extend. (Singular fibres here are benign coincidence
degeneracies, not a computational lever — if anything they make elimination harder, not easier.) The
correct m≥3 non-degeneracy notion (restricting to the main component off the diagonals) is **OPEN**.
This does not affect §1–§2, which are the hardness-relevant results.

---

## Grades (locked — do not upgrade)

- **§1** isobaric homogeneity + leading-form curve-independence: **PROVED, general m** (weight
  argument; symbolic-verified m≤4 (S₄/S₅), numeric leading form m≤5). First-fall = leading-form
  invariant: **CITED** (BFS). ⇒ first-fall degree curve-independent: **PROVED given the cited
  definition**.
- **§2** solving-degree curve-independence: **EMPIRICAL**, matched control (identical) + non-matched
  clustered-with-noise; μ₃ no first-fall lever: **EMPIRICAL** (p=211, 307, m=3).
- **§3** S₄ fibre non-smoothness: **VERIFIED-scope** (GF(211); elim ideal =(0) + 12/12 sample).
- **"first-fall degree ⇒ actual index-calculus complexity"** and **"no lever ⇒ ECDLP hard"**:
  **HEURISTIC / CITED** (Diem 2011; Semaev first-fall conjecture; Petit–Quisquater; FGHR for binary
  fields). **Security conclusion unchanged.** This work rigorously kills the specific hope that secp's
  CM lowers the summation-polynomial first-fall degree; it does not prove ECDLP hard, and does not
  bound entirely different attack systems.

**Scope caveats:** small p (100–2000; first-fall/solving degree are degree-combinatorial and
near-p-independent, but secp's actual `p≈2²⁵⁶` is untested); m∈{2,3,4}; B∈{2,3,4}; the "first-fall ⇒
complexity" bridge is the standard heuristic, not proved here. An empirical null is a scoped fact, not
a closure.

## Files
Engine: `semaev_elimination_v1.py`. Prior: `masked_structure_findings_v9/v10/v11/v13.md`,
`summation_and_formalgroup_v1.py` (built S₄=Res(S₃,S₃), β-weight 0, no system). Handover:
`POSITIVE_FINDINGS_HANDOVER_3_v1.md` (frontier item #4).
