> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS — ADDENDUM 4 (session 2026-08-25)

**Feeds the next master compile** (current head `POSITIVE_FINDINGS_MASTER_v15.md`, 2026-08-24).
**Additive: records this session's results; changes nothing in v15.** Fold into master is
`compile-diff`-gated (a separate promotion step, NOT done here).

**Provenance.** Audit of a batch of 20 external-agent reports (the `~/Downloads` set, worked
oldest→newest). Each was tested at the level of its method AND its underlying idea — reproductions,
matched-control checks, stress sweeps, and one ground-truth leakage test on real secp256k1 keys.
Verification scripts banked at `audit_external_reports_v1_scripts/` (21 files). Every item below carries
its grade, its measured numbers, and its scope. Language-shrink audit applied per
`feedback_negative_bias_enlarge_nulls` / `feedback_closure_grade` (a prior draft compressed several of
these with words like "trivial/forced/small"; each is now graded to object+power+scope, not a verdict).

**Standing-asymmetry note.** This session is dominated by cross-checks of existing frontiers plus
scoped nulls on the external reports' crypto-payoff claims. No new frontier opened; two existing
frontiers (ζ₃-rigidity, sub-Rayleigh deficit) get independent confirmation and a sharper source-location.

---

## A — Reinforcements / independent cross-checks of standing frontiers

**A1. The 120° (ζ₃) eigenvalue phase-lock on A_new — independent point-count confirmation, two regimes.**
`[VERIFIED — exact, point-counted]` · script `audit_phaselock.py`
Point-counted the cover `C: w⁴=x³+Ax+B` over F_p, F_{p²}, F_{p³}; extracted A_new's four Frobenius
eigenvalues by dividing out E's quadratic. Result:
- **non-CM, p≡1 mod 4** (p=13 x³+3x+7; p=29 x³+4x+9; p=37 x³+3x+15): the two conjugate eigenvalue-pairs
  sit **120.0° apart** (ζ₃ relation), on curves with **no CM** — the rigidity is cover-borne, not
  base-curve-borne.
- **p≡3 mod 4** (p=11, 23, 43): eigenvalues on the **√p·ζ₆ / imaginary-axis lattice** (superspecial),
  angles {60,120,240,300} or {90,90,270,270}.
This is an independent (finite-prime, point-count) witness of the L-mono GKR campaign's analytic ζ₃
result (`RESULT_lmono_gkr_*`, det(W_a)=ζ₆·p a-constant). **Adds:** the p mod 4 split — ζ₃-pairing
(ordinary p≡1) vs √p·ζ₆ superspecial (p≡3) — is one object seen in two regimes. Source doc
(`verify-p1-spectral-cap.md`, `verify-hasse-davenport-reduction.md`) over-generalized to "universal 120°
law"; the two regimes are distinct.

**A2. The half-Weil spectral cap |V(a)| ≤ 2√p — verified for prime-order, fails composite-order.**
`[VERIFIED — empirical, scope-pinned]` · scripts `d18_shears_cap.py`, `d20_capsweep.py`, `d20b_primeorder.py`
V(a)=Σ_d χ₂(y_d)·e_n(ad). Over **prime-order** non-CM curves, p up to ~180, all A,B swept: **0/317
violations, max ratio 1.996** (approaches but does not reach 2). Over **composite-order** curves the
cap fails, max ratio **2.824** (p=193). The source's 13-curve table (all prime-order) reproduces exactly
(e.g. p=113 ratio 1.9960). This is the consequence of A1's ζ₃ lock (cap = half the 4√p A_new ceiling).
**Scope:** cap is a prime-order phenomenon; the source's "universal, no exceptions" needs the prime-order
qualifier. Grade is empirical, not PROVED — the trig derivation assumes the eigenvalue pairing, which A1
confirms but does not prove uniformly in p.

**A3. Semaev collinearity of β-orbits.** `[VERIFIED — exact identity]` · script `d18_shears_cap.py`
{P, λP, λ²P} satisfy S₃≡0 at **100% (CM, F₆₇) / 0% (non-CM)**, forced by 1+λ+λ²≡0. This is the SAME
object as v15's **H2 RESOLVED (M26, x-closure lever IS β/CM-specific)** — an independent reproduction,
consistent with that resolution. Structured relation family (GLV relation-triples), not noise.

**A4. Cartier–Manin vanishing / superspecial A_new.** `[VERIFIED — reproduced, scope as tested]` · `d04_cartier.py`
A_new's Cartier block = 0 for all p≡3 mod 4 tested (12 primes × {CM, x³+x+3, x³+x+5}). CM p≡1 mod 4:
diagonal (p≡1 mod 12) / off-diagonal (p≡5 mod 12) by residue; entry positions basis-convention-dependent.
Consistent with the superspecial-A_new premise used across the corpus and with A1's p≡3 regime.

**A5. Jacobi sign law J(χ₃,χ₄) = −p.** `[VERIFIED — exact]` · script `d10_jacobi.py`
Over F_{p²}: J = −43 exactly at p=43 (real integer, |J|=p). Φ₁₂ mod 43 = (x²+6)(x²−7), mod 1831 =
(x²+672)(x²−673). Same object as `POSITIVE_FINDINGS_ADDENDUM_2` B1.5 / Frontier 15 (Jacobi sign law) —
independent reproduction.

---

## B — Characterizations: where the sub-Rayleigh / row-budget structure is and is NOT

**B1. Doc-12 y-only deficit source located — negation-parity realness (the wrong-null lesson, again).**
`[CHARACTERIZATION — matched-control]` · scripts `d12_ydeficit.py`, `d12b_control.py`, `audit_deficit.py`
On the **b=0 (y-only) line**, U(1,0,c) is **exactly real** (max|Im|≈6×10⁻¹³) because y_{n−d}=−y_d. The
source's −9%…−18% "deficit" and +12%…+27% "low-tail excess" are measured against an **arbitrary
permutation** null (which yields COMPLEX sums) — a real-vs-Rayleigh mismatch. Against a
**±-antisymmetry-preserving** control the low-tail excess vanishes (40.4% vs 40.7% at p=163) and the
residual deficit is **z ∈ [−0.76, +1.58] over 6 primes (K=300), consistent with 0**.
**Reconciliation (does NOT contradict the standing frontier):** this is the b=0 SLICE with a
±-antisymmetry null. `RESULT_subrayleigh_deficit_scaling_v1` is the **full 2-D U(a,b,c)** against a
**Hermitian-symmetric** matched null, ~0.1% surviving across 30 primes. B1 re-confirms the wrong-null
lesson of `RETROSPECTIVE_FINDING_01` on Doc-12's specific numbers; it does not touch the ~0.1% full-2D
Hermitian-null deficit, which stands.

**B2. Row-budget M₄ excess — reproduced, universal (CM ≈ non-CM), scale-crossover.**
`[VERIFIED — matched-shuffle control]` · script `d13c.py`
Σₐ|U(a,b,c)|² = n(n−1) exact (machine precision, P30). Row-wise M₄ excess vs coordinate-shuffle null:
−0.79% (p=43) → +0.23% (p=163), **T≈+3.3 at p=163**, and **CM +0.23% vs non-CM +0.24%** at p=163
(universal, parity-driven). Magnitude ~0.2%; statistically nonzero. Reproduces the source's crossover
and its own (later-doc) deflation of the CM-specific reading.

**B3. Linear-shear M₄ invariance — exact.** `[VERIFIED — exact]` · script `d18_shears_cap.py`
Total M₄ invariant under x→x+sy, relative difference **0.0** across s∈{0,1,10,37,78} (bijection
c→c+bs). No basis-shear concentrates the row budget.

**B4. Nonlinear-shear M₄ break — reproduced, L² preserved.** `[VERIFIED]` · script `d18_shears_cap.py`
x→x+sy² changes total M₄ by +1.37%/+1.82%/+0.91% (s=1,2,5) while Σₐ|U|²=n(n−1) holds to 10⁻¹²
(y² even under [−1], not absorbable as a c-translation). Characterization only; the object U(a,b,c) is a
whole-group sum (no per-key secret).

**B5. Amicable-pair E3 cross-match = noise floor.** `[NULL — matched]` · (report `amicable_reference_beam_audit.md`)
Cubic-character match across the Silverman–Stange pair: 33.17% vs 33.33% expected. Amicable-pair M₄:
one significant cell (CM E₂, p=79, +0.56%, T=+2.6) of four, single curve per cell; contradicted as a
"CM-accelerates" law by B2's universal crossover.

---

## C — Exact structural facts (verified this session)

**C1.** Formal-parameter linearity: the GLV order-3 automorphism (x,y)→(βx,y) acts as **exactly** z→βz
(all orders) on z=−x/y; L(βz)=βL(z) exact (β⁶=1). `[EXACT]` · `d01_formalgroup.py`, `d01b_truelog.py`
The hypergeometric series `Σ Bʲ C(3j,j)/(6j+1) z^{6j+1}` is the true formal-group log (coeffs 1, 3B/7,
15B²/13, …). **Source error noted:** the report's inline expansion "3B·z⁷+40B²z¹³" drops the
denominators (should be 3B/7, 15B²/13).

**C2.** CM 3-orbit → cyclic C₅ number field (p=43, x³+7): the 15 squared twisted sums reduce to 5
distinct roots (mult 3); Q₅ = T⁵+155T⁴+6138T³+92070T²+555861T+1060975; disc = 56858430668800² (perfect
square); Galois group **C₅** (sympy galois_group + Chebotarev census: only (1⁵),(5) cycle types).
`[VERIFIED — exact]` · `d03_galois.py`, `d03b_gal.py`

**C3.** Parity-protected Kummer descent splitting (E′:x³+x+3/F₄₃, n=47): odd-parity coordinate readouts
give complete splitting [1²³] at ℓ=281 and 283; the parity-mixing shear gives 1/23 at ℓ=281.
`[VERIFIED]` · `d09_splitting.py`

**C4.** Weil pairing at p=11 (E′:y²=x³+1/F_{11²}): order 144=(p+1)²; e₁₂ primitive 12th root;
bilinear + alternating pass; embedding degree 2. `[VERIFIED — p=11]` · `d05_weil.py`

**C5.** Public substrate (Doc 7): Puzzle-140 pubkey satisfies y²=x³+7 mod p; p = a²−ab+b² with the
report's Eisenstein basis. `[EXACT]` · `d07_farey.py`

---

## D — Crypto-payoff claims of the external reports: scoped nulls

*(Stance per MEMORY: an empirical null ≠ a closed avenue. These bound the SPECIFIC constructions the
reports advanced; they do not close the curve project.)*

**D1. d mod {2,3,6} extraction from a public key — 0.00 bits.** `[NULL — ground truth, matched]` ·
scripts `idea_dmod6.py`, `idea_dmod6b.py`
Real secp256k1 keypairs, d known. χ₃(x_P)→d mod 3, y-parity→d mod 2, joint→d mod 6: mutual information
at the permutation-null floor (all z<1), for full-range AND the 2¹³⁴–2¹³⁵ (Puzzle-135) range, N=6000.
The reports' claimed "2.585-bit reduction" would need MI≈2.585 bits; measured ≤0.006 bits, indistinct
from 0. **Scope:** bounds the χ₃/y-parity/Core-Gate channel as specified; a conditioning event
computable from public data cannot manufacture MI these raw channels lack.

**D2. "D2 island-sieve / bisection" is an algebraic identity.** `[NULL — structural]` · `d02_bisection.py`
The reconstruction returns d from d0, where d0 was defined as d·λʲ mod n; the "1000/1000" survivors are
the candidate built from d. Recovering d0 from the public point φʲ(P) is itself an ECDLP instance.

**D3. secp256k1 is not the pairing-soft object.** `[computed]` · `d05_weil.py`
E has trace ≢ 0 mod p (ordinary); embedding degree ord_n(p) is a 256-bit integer ≈1.9×10⁷⁶. The
supersingular embedding-degree-2 property is A_new's / the auxiliary E'/F_{p²}'s, and A_new is the NEW
part (complement of E in Jac(C), dim 2 vs 1) — no dimension-preserving map carries E's DLP into it. The
reports' "non-homomorphic transfer bridge" is named, not constructed.

---

## E — For the next master compiler

- A1/A2 attach to the **ζ₃-rigidity / L-mono GKR** frontier as an independent point-count witness + the
  p mod 4 regime split. A3 = H2 (already resolved v15). A5 = ADDENDUM_2 Frontier 15.
- B1 attaches to **sub-Rayleigh deficit (Frontier #15)** as a source-location on the b=0 slice; the
  full-2D ~0.1% Hermitian-null deficit is untouched and stands.
- D-items bound the external reports' extraction claims; grade EMPIRICAL/NULL, not closure.
- Nothing here promotes a master row. Compile-diff gate owed before any fold.
