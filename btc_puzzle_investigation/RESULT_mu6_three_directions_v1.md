# Three rigorous follow-ons to the μ6-isotype result (E1/E2/E3)

Date: 2026-07-18. Pre-registered by `experiment-designer` (E1/E2/E3 specs). Theorem parts
exact (integer); empirical parts = magnitudes ranked against matched nulls, verdict = integer
exceedance count; out-of-sample on ≥2 curves/primes. Scripts in `scratchpad/`: `mu6_curve.py`,
`e1_e2_v2.py`, `e3_gaussian.py`, `e3_v2.py`. Model curves: C1 y²=x³+7/F_2143 (n=2089),
C2 y²=x³+13/F_3001 (n=3079). **Every empirical claim carries POWER + SCOPE; nulls are bounded
magnitudes, not "no structure."**

Two implementation bugs were caught by the results and fixed BEFORE anything was reported (logged
below); one apparent E1 "anomaly" dissolved under a properly matched control — the protocol working.

## E1 — μ6 fundamental domain of the leak spectrum U(a,b,c)=Σ_d e_q(b x_d+c y_d) e_n(a d)
**THEOREM (exact, both curves).** Value symmetries `U(a,b,c)=U(λa,βb,c)` (τ) and `U(a,b,c)=U(−a,b,−c)`
(ρ) hold exactly; the magnitude adds conjugation `|U(a,b,c)|=|U(−a,−b,−c)|` (κ). The magnitude-
symmetry group ⟨τ,ρ,κ⟩ has order 12 (Z/3 × Z/2 × Z/2). Generic orbit size **12**; on the b=0 locus
it drops to **6**. Only the origin is fully fixed; b=0 and c=0 are short-orbit strata. So the
independent |U|-spectrum is ~1/12 of naive (not 1/6 — conjugation adds the extra factor).
**EMPIRICAL (both curves).** KS ceiling 4√q+1; global max|U| over the twisted spectrum sits on the
b=0 real short-orbit at **0.935·KS (C1), 0.981·KS (C2)** — but against a MATCHED double-max null
(max over q−1 random conj-symmetric real sequences) it is `exc=200/200` (curve *below* matched
random). **Scoped result:** "max on b=0" is the forced real-sum tail geometry, not a curve anomaly;
no excess beyond the symmetry structure. POWER: matched null resolves ≥1.5σ tail excess; none seen.
**Correction:** my earlier "only origin fixed / 6-fold" (that was the 2-index U(a,b)) and "b=0 tail
EXCEEDS null" (an UNMATCHED single-draw null) were both wrong — fixed here.

## E2 — μ3-weight ceiling beyond parity
**THEOREM (exact, both curves).** For a₀≠0 the six translates {±a₀,±λa₀,±λ²a₀} are distinct
characters of Z/n, hence L²-orthogonal; each μ6-isotypic projection of e_n(a₀·) has mass exactly
n/6. So a definite-type readout's alignment `A(R,a₀)=|⟨R,e_n(a₀·)⟩|²/(‖R‖²n)` obeys: complex
single-isotype ≤ **1/6**; real weight-0 ≤ 1/6; real weight-±1 pair ≤ **1/3**; parity (GLM) ≤ 1/2.
The μ3 (CM) grading is a genuine √3-amplitude sharpening of GLM's parity ceiling. A complex single-
isotype control achieves A*=**0.1667** exactly.
**EMPIRICAL (both curves).** Actual cheap coordinate readouts — lsb(x), sign(y), Legendre(x),
sextant, ε — all sit at the random floor (~log n/n ≈ 0.003), 0.3–1.3× floor, far below every
ceiling. **Scoped result:** the μ3 refinement is a real theorem but NOT the operative constraint at
this scope (these readouts leak nothing regardless). ε at the floor re-confirms trivial-isotype /
zero DLP-alignment. POWER: floor≈log n/n; a leak ≥ a few× floor would show — none did.
**Correction:** the positive control was buggy — `Re(P_{(w,s)}e)` spans a conjugate pair → 0.25;
fixed to a complex single-isotype readout → exactly 1/6.

## E3 — CM-type dependence (j=1728, Aut=μ4, Gaussian Z[i] lift)
**STRUCTURAL finding.** The equivariance-defect *flap* DEGENERATES for μ4 (constant: all-core or
all-else), because the square lattice's 90° rotation is an exact symmetry of its fundamental domain
— unlike the hexagon's 120°, which needs the flap correction. **The flap phenomenon is specific to
the hexagonal (j=0) geometry.** So the μ4-invariant object to test is the norm band `nb_i`.
**THEOREM (both lattices).** An H-invariant function is ⊥ every character nontrivial on H (χ²=0
exact, equal counts per class). Verified:
- **Gaussian nb_i (μ4-invariant, verified nb_i(ιx)=nb_i(x)):** χ2 (p≡5 mod8) → χ²=0.00 exact;
  χ4 (nontrivial on μ4) → 0.00 exact; **χ3 → never 0** (55.6 at p=90373, 22.9 at p=90001). χ2/χ4
  stop being forced exactly when p mod 8/16 makes them trivial on μ4 (p=90001≡1 mod16: both fire).
- **Eisenstein ε (μ6-invariant):** **χ3 → χ²=0.00 exact** (forced by μ6); χ2,χ6 null at q≡1 mod4.
**CONCLUSION.** The forced-orthogonality group = the characters nontrivial on Aut(E)'s image in
F_p* — {χ2(cond),χ3,χ6} for j=0, {χ2(cond),χ4} for j=1728. **χ3 is forced-zero for j=0 but not
j=1728: Aut(E) fixes the orthogonality group.** SANITY: p≡3 mod4 (inert in Z[i]) correctly rejected
(no lift). SCOPE/CAVEAT: the *unforced* Gaussian χ3 correlation is weak and non-replicating (fires
p≡5 mod8 V=0.017, not p≡1 mod16 V=0.011) → NOT named as a real arithmetic effect; the load-bearing
fact is only that it is never *forced* to exact 0, unlike the μ6 case.

## Net — exact scope (no "lever" claim is made or implied)
Three scoped facts about three specific objects. What each proves and, precisely, does NOT:
- **E1.** PROVED (algebraic, transfers to secp256k1): the exact order-12 symmetry of |U(a,b,c)|.
  This is a REDUNDANCY of the spectrum, not a bound: it does not say |U| is small anywhere, does not
  locate/exclude a large corner, says nothing about the magnitude of the d-carrying part. The
  "≤KS, within matched-random" empirics are 2 small curves, a SAMPLED (b,c) grid, one max-statistic —
  not a claim about secp256k1.
- **E2.** PROVED: a readout confined to ONE μ6-isotype aligns ≤1/6 (complex)/1/3 (real pair). Bounds
  ONLY isotype-confined readouts; a readout mixing isotypes is not bounded by 1/6. Silent on joint /
  multi-coordinate readouts (the class that survives the ECDLP scramble), on unbounded-degree
  readouts, and beyond the 5 readouts × 2 curves × single-frequency statistic actually measured.
- **E3.** PROVED: an H-invariant function has χ²=0 exactly against multiplicative characters
  nontrivial on H; so the flap's forced-orthogonality group fingerprints Aut(E). Concerns SINGLE
  multiplicative characters and these specific invariant functions only — not non-character readouts,
  joint readouts, or functions outside the invariant class; does not say the flap carries no info.

**No proof about "levers" in general was produced or attempted.** The programme's strongest analytical
closure (KS) is itself scoped — bounded-degree, single-coordinate, additive characters — and leaves
joint / two-point / χ₂-Artin–Schreier / unbounded-degree open; NONE of E1/E2/E3 touched those. These
three results add exactly-characterized CM symmetry to the map and close none of the open frontier.
