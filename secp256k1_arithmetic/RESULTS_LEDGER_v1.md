# secp256k1 arithmetic — clean results ledger

**2026-07-11.** The single clean record of what has been established, separated
into **confirmed positive results** (graded by evidence) and **scoped negative /
null results** (each bound to the exact probe, parameters, and scale tested — never
an absolute claim). Companion to the canonical `secp256k1_arithmetic_v4.md`.
Rule followed: a null is a fact about *a test*, not about *reality* — every
negative below names its method, its parameters, and the scale at which it was run.

---

## A. Confirmed positive results

Grades: **[exact]** exact integer/Fraction/rational, re-run this session ·
**[LMFDB]** matched against LMFDB · **[math]** argument herein · **[relayed]**
recorded prior-session, not re-run.

### Exact arithmetic (Ledger A — not spectral/statistical)

| # | Result | Grade | Evidence |
|---|---|---|---|
| A1 | `End(E)=ℤ[ω]`, `4p=t²+27M²`, `(π_n)=(π_p−1)` | exact/math | `verify_v1.py` |
| A2 | Formal log `Σ7^kC(3k,k)/(6k+1)T^{6k+1}`, μ₆-sparse, exact ₃F₂ | exact | to T⁴⁹ |
| A3 | `[2],[3],[5](T)∈ℤ[[T]]` (integrality, all primes) | exact | to T³⁷ |
| A4 | ASD `7^kC(3k,k)≡a_ℓ (mod ℓ)`; three-term mod ℓ² | exact | **all 147 split ℓ<2000** |
| A5 | mod-ℓ³ upgrade locus `= {a_ℓ=±1}` = {37,61,127,397,547} | exact | on ℓ<2000 (scope in B1) |
| A6 | Radius `T_c=(4/27b)^{1/6}`; critical point non-torsion | exact | symbolic |
| A7 | **χ(π)=−(4k/π)₆⁻¹ DERIVED** (Jacobi-sum + sextic recip.) | exact | 1442/1442, split p<3000 |
| A8 | Conductor `𝔣=(2²)(√−3)²(7)`, `N_E=21168` | math/relayed | conductor–disc |
| A9 | Amicable pair `#E(𝔽_p)=n`, `#E(𝔽_n)=p`, `π_n=π_p−1` | exact | both directions + Hasse |
| A10 | **Closure = 13/50 = Silverman–Stange Conj 40** | exact | all 12 classes mod 36 |
| A11 | Per-b `ρ_b={½,13/50,18/101,1/10}` order-predict pair counts | exact | b=2,3,5,7 |
| A12 | GLV lattice basis `{π_n,ω²π_n}`, det n | exact | `verify_v1.py` |
| A13 | Unit equidistribution 72/432 per μ₆ unit | exact | χ²=3.26, df 5 |
| A14 | `L(1)=Ω=Γ(1/3)Γ(1/6)/(2√π·7^{1/6})` | exact/LMFDB | **28 digits vs LMFDB** |
| A15 | BSD closes: `L(1)/Ω=1`, all `c_ℓ=1`, `Ш=1`, Kodaira II | math+numeric | globally minimal |
| A16 | Unit root `α≡t (mod p)`, Hensel to p² | exact | `test_claims_v1.py` |
| A17 | `A(ψ)=N/(4π²)=536.19` | exact | analytic conductor |

### Zeros (computed + externally checked)

| # | Result | Grade | Evidence |
|---|---|---|---|
| A18 | `Λ(s)=WΛ(2−s)` to 30 dps; `L(1)` matches LMFDB 28 digits | LMFDB | `thread_E` |
| A19 | First zero `γ₁=0.8173126364` = **LMFDB 0.8173126364220043** | LMFDB | 10 digits |
| A20 | Verified-complete zero list to height 22 (mean spacing 0.991) | math | bisection + completeness assert |

### One robust spectral mechanism

| # | Result | Grade | Evidence |
|---|---|---|---|
| A21 | The "dilution" `λ_max/Tr` common mode **is the χ₋₃ conductor shadow** (rank-1, align 0.997; from `a_ℓ=0` on inert; split-only removal collapses it 0.575→0.120) | math+numeric | envelope-independent mechanism; see B7 for its scope limit |

---

## B. Scoped negative / null results

**Each is a statement about the test run, not about reality.** Form: *probe →
parameters/scale → outcome.* None of these should be read as "X does not exist."

- **B1 — mod-ℓ³ ASD upgrade beyond {a_ℓ=±1}.** *Probe:* scan the three-term
  congruence to mod ℓ³ for split ℓ. *Scale:* ℓ < 2000 (147 primes). *Outcome:* the
  upgrade locus coincided with `{a_ℓ=±1}` on this range; **not verified beyond
  ℓ=2000**, and the *mechanism* (why a=±1) is not proven — only observed on ℓ<2000.

- **B2 — closed form for δ_ℓ = (b_ℓ−a_ℓ)/ℓ.** *Probe:* fit δ_ℓ to (i) integer/half-
  integer combinations of Fermat quotients q_ℓ(2), q_ℓ(3), q_ℓ(7); (ii) `a·H_{(ℓ−1)/6}`;
  (iii) `a·(x·H_{(ℓ−1)/6}+y·H_{(ℓ−1)/2})`, `|x|,|y|≤6`. *Scale:* split ℓ < 2000.
  *Outcome:* **no fit found among these families**; consistent with Gauss-sum /
  Bernoulli content (Coster–van Hamme). Not "δ_ℓ has no closed form" — only these
  elementary families were searched.

- **B3 — length-≥3 amicable/aliquot cycles.** *Probe:* iterate `q↦#E_b(𝔽_q)`.
  *Scale:* b≤40, prime starts < 60k, ≤7 iterations (~228k starts). *Outcome:* **none
  found**; a conditional null consistent with Silverman–Stange rarity. Length-2
  (amicable) pairs are abundant. Not "no 3-cycles exist."

- **B4 — a genuine sextic (rank-≥2) spectral common mode (Finding 3).** *Probe:*
  character-correlation of `F_{q²}` (μ₆) characters on Eisenstein primes vs Dirichlet
  (μ₂), tested against a **same-sample, envelope-preserving, random-character null**.
  *Scale:* 8 inert / 8 split moduli in [10,200], 500 sample primes, 120 null draws.
  *Outcome:* real top eigenvalue **below** the matched null (z=−1.5 CM, −1.1 Dirichlet);
  **no sextic common mode detected by this test** — the apparent mode was the `1/√p`
  envelope. Scope: this construction and null only; the exact `F_{q²}` character subset
  of the source draft was inferred.

- **B5 — the ZFR Appendix-B rank-2 low-prime common mode.** *Probe:* faithful
  reconstruction of the paper's low-prime feature Gram. *Scale:* Q=100, P₀={2..29},
  712 characters. *Outcome:* spectrum **flat** (PR≈9.98, ratio max/min≈1.2); the
  rank-2 mode **did not reproduce** in this reconstruction (character orthogonality
  forces near-flatness). Likely source: a `|χ(p)|` / `Re χ(p)` variant in the
  original code (a specific candidate, not confirmed).

- **B6 — Moment-Pumping "growth" from the curve/twist.** *Probe:* moment ratio
  `MR=‖f^⊥‖₈/‖f^⊥‖₂` of the forcing vector `f(p)=χ(p)p^{−iγ}w_X(p)p^σ`, comparing the
  CM twist (`a_p`) to generic |χ|=1. *Scale:* γ=14.13, σ=0.5, X up to 32000, rank-5
  projection. *Outcome:* the CM twist is a constant ~1.5× more concentrated but
  **delocalizes at the same asymptotic slope (−0.327 vs generic −0.33)** — **no
  growth observed in this range/construction**; the Moment-Pumping forcing is not
  repaired by twisting here. (A first run with a `p^{σ−1}` envelope falsely showed
  concentration; that envelope did not reproduce the drafts' −0.36 baseline and was
  corrected.)

- **B7 — exact numeric reproduction of the reported dilution table.** *Probe:* match
  `λ_max/Tr` = {0.806,0.704,0.583,0.458} with an inferred feature map
  `f_q(ℓ)=cos(2π a_ℓ/q)`. *Scale:* X=500–2000, Q=5–50. *Outcome:* reproduced the
  *shape* and the χ₋₃ mechanism (A21) but **the Q=50 value is ~25% off** (0.58 vs
  0.46) — the exact construction of the source table was not pinned; the mechanism
  is solid, the exact-numeric match is not.

---

## C. Downgraded claims (were over-stated; now conjecture or scoped)

- **C1 — "the spectral/Gram axis is exhausted; only χ₋₃ ever shows."** Now a
  **[conjecture]**, not a result. It rested on Gram tests that flip on confounds
  (the `1/√p` envelope, sample-set choice); the Finding-3 verdict reversed twice
  before the clean null (B4) settled it. The *dilution* mechanism (A21) survives; the
  "nothing else exists anywhere" generalization does not, pending same-sample /
  matched-null re-tests of the split-only residual modes.
- **C2 — μ₆ = μ₂ × μ₃ "role split" (μ₂ visible, μ₃ invisible).** A **[conjecture]**
  motivated by A21 and B4; not proven. Where μ₃ would appear (Sym² L(ψ²)) is untested.

---

## D. Open (defined, not yet run)

- **D1 — Formal group → Katz p-adic L (thread α).** Compute the p-adic unit root
  from the formal group; test `{a_ℓ=±1}` (A5) against the p-adic special/trivial-zero
  locus; test `δ_ℓ` (B2) against Gross–Koblitz p-adic Γ. *Not started.*
- **D2 — Amicable dynamical system (thread β).** Exact expected 3-cycle density from
  the mod-84 class census²; is B3's null structural or rarity? *Not started.*
- **D3 — χ₋₃-only second-moment as a theorem (thread γ); μ₃ in Sym².** *Not started.*

---

## E. Ledger B (separate work) — status, scoped

The φ(n)-residue RH programme is bridged only via `L(ψ,s)` and is kept separate.
**It does not prove RH**, on two grounds each scoped to what was checked:
- **E1:** the Moment-Pumping forcing requires the projected moment to grow; on the
  tested forcing class it **delocalizes** (power-law decay, MR~X^{−0.36}) — verified
  numerically for the tested (X,γ,σ,χ); see B6 for the curve-twist variant.
- **E2:** `Ĥ=πA²` on the stated space `[1,∞)` has deficiency indices **(1,1)**, not
  (0,0) (independently re-derived); the full-line fix empties `D_φ` under the
  normalized multiplier. A structural fact, implementation-independent.
Solid pieces of Ledger B (verified): coercivity `1/12=min 1/φ(q)`; the Eisenstein–
Ramanujan survival law (μ₆ survives); `ζ_K=ζ·L(χ₋₃)`; the function-field
Hilbert–Pólya instance.

---

## F. Method rule (so negatives stay honest)

Any spectral/Gram common-mode test: **same sample set, envelope preserved, matched
random-character null** (not the iid Marchenko–Pastur edge, not an independent-column
shuffle), **and reproduce the source's baseline before dismissing it.** Every null
above is reported with its probe, parameters, and scale; none is stated as an
absolute. Positives are graded [exact]/[LMFDB]/[math]; nothing ungraded is asserted
as fact.
