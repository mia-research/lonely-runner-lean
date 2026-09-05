# Second review — everything tested (2026-07-10)
Each claim of the second review, tested from scratch or marked external. Scripts in session.

## VERIFIED EXACT
- Frobenius digits: a=367917413016453100223835821029139468249,
  b=303414439467246543595250775667605759171, t=432420386565659656852420866390673177327 — all match.
- n_t/φ(n_t) = 1.6255615565 (10-digit match). φ(n_t)=7.123×10⁷⁶ (10⁷⁶ not 10⁴⁰). ✓ agrees w/ prior fix.
- p mod 3 = 1 ⇒ p splits in ℚ(√−3). ✓
- Conductor 𝔣=(1−ω)²(3+ω)(2−ω), N(𝔣)=441; curve conductor 21168=2⁴3³7². ✓
- Review AGREES with prior corrections on: φ exponent, 3/7-vs-2/7 being unjustified, |τ|² convention.

## CORRECTED (review still off)
- **Frame ratio.** Review upgraded max|c| from 936 to 70,305,659,424 (=6·156·3318·22638) and ratio²~3.3×10¹⁸.
  Still omits the P−1 factor: that 70bn is the max over modes with P∤k. The TRUE max nontrivial |c| = φ(n_t)/2
  (at k=n_t/3, where P|k), so the real frame ratio² = 2⁴⁹⁸ ≈ 10¹⁵⁰, not 3.3×10¹⁸. Loose either way; the exact
  number is ~10¹⁵⁰.
- **Root-number reasoning is a non-sequitur.** Claim: "π≡−1 mod 𝔭_ℓ ⇒ local root numbers at ℓ|n_t all +1 ⇒
  global W=+1." Among ℓ|n_t = {3,13,3319,22639,C}: **3 is a BAD prime** (3³|21168), local root number NON-trivial —
  the claim is false for ℓ=3. For 13,3319,22639,C the local w=+1 is automatic (good primes), NOT caused by π≡−1.
  Global W is fixed by the bad primes {2,3,7} + archimedean, unrelated to the sieve. W(E)=+1 is consistent with
  rank 0 (L(E,1)≠0), but not "forced" by the sieve.

## CONVENTION / UNPROVEN
- **Gauss sum |τ|:** |τ|²=N(𝔣)=441 (self-dual char, standard, |τ|=21) vs 1323=441·|D_K| (un-adjusted char).
  Convention-dependent; 441 is the standard primitive value.
- **Gauss sum PHASE (τ=21√3·i): UNPROVEN.** Tested on Dirichlet analogues: |τ|²=conductor always, but the phase
  is a character-dependent root of unity — quadratic χ give ±i (χ₋₃→i, χ₋₄→i), but cubic/sextic χ give other
  phases (−26.4°, 157.3°). ψ_E is a weight-1 sextic-type Hecke character; W=+1 alone does NOT pin the phase to i.
  The exact phase needs the explicit character, not computed here.

## EXTERNAL THEOREM vs UNTESTED SPECULATION (not dismissed, not endorsed)
- **Rubin's μ=0 for CM curves** (1991, Katz p-adic L / Iwasawa module at ordinary primes): a REAL theorem that
  would apply to y²=x³+7/ℚ. I cannot compute the specific μ-invariant here (not a finite computation); I neither
  verify nor refute the specific value — I cite the theorem.
- **HEADLINE ("rank-1 Fourier correlation = computational signature of μ=0; inverted sieve computes μ directly"):
  UNTESTED.** No demonstrated basis; it is a hopeful analogy connecting the weak rank-1 background to the
  Iwasawa invariant. Not shown, not disproven — currently speculation.
- **Category slip:** the review conflates secp256k1's FIELD prime p (curve over F_p, Frobenius π_p) with the
  Iwasawa/p-adic-L prime (curve over ℚ, p-adic L at a chosen prime). These are different objects; the p-adic
  L-function/μ-invariant lives over ℚ.
- **Inverted-sieve θ-reconstruction:** re-affirmed FAILS (per-prime errors 2–220°); "π_ℓ≈−1 exact p-adically"
  conflates π_p (whose arg is θ) with π_ℓ (a generator above ℓ). θ = t = n_t−p−1 trivially; no reconstruction engine.

## Net
Arithmetic spine: exact. Frame ratio: review under-corrected (real ~10¹⁵⁰). Root-number chain: non-sequitur (3 is
bad). Gauss phase: unproven. p-adic-L / Iwasawa μ layer: real theorems exist (Rubin μ=0), but the specific
"sieve computes μ" claim is untested speculation resting on a field-prime/Iwasawa-prime conflation.

## Third-review round (2026-07-10) — new claims tested
- **Euler factor (1−π/p)(1−π̄/p)=n/p, v_p=−1:** TRUE but TRIVIAL (any ordinary curve). "⟹ μ=0, confirmed by
  archimedean data" is a NON-SEQUITUR — μ is the leading-coeff valuation over the Iwasawa algebra, not the s=1
  Euler factor; and μ is p-adic (archimedean data can't confirm it). Rubin μ=0 is a theorem; this does not confirm it.
- **"SNR ~10³⁷" of the rank-1 ρ~0.1:** FALSE. Observed cross-modulus ρ mean 0.03 vs random-vector null 0.085±0.045
  ⇒ z=−1.1σ, at/below the noise floor. Real SNR ≈1. Off by ~37 orders.
- **72 = φ(117)** (117=3²·13): count correct; W-selection + Euler-system link uncomputed/speculative.
- **K-matrix / φ(n_t) conflation:** the ZFR K-matrix does NOT depend on φ(n_t) or the n_t frame — separate objects;
  "reanalyze K at the corrected φ(n_t) scale" is a category error. Eigenvalues-below-MP-edge stands.
- **"angle encoded in the factorization":** overclaim; θ=t=n_t−p−1 (value); per-prime angular recovery fails.
- **Self-correction:** the rank-1 background is a real DETERMINISTIC direction but its correlation signal is
  at/below the noise floor (~1σ) — I earlier overstated it as "real but weak"; it is mathematically real,
  statistically marginal.
