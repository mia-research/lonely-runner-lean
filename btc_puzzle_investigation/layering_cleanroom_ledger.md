# The four-layer "structural fingerprint" — clean-room test (2026-07-10)
Every claim re-derived from raw p, n only; each verdict scoped to exactly its test.
No claim inherited. Script: session `layering_cleanroom`.

## LAYER 1 — ARITHMETIC.  STATUS: SOLID (all exact)
π_p=(a,b): N(π_p)=p ✓, Tr=2a−b=t ✓, n=N(π_p−1)=p+1−t ✓, n_t=N(π_p+1)=p+1+t ✓.
n_t = 3²·13²·3319·22639·P, P a 220-bit prime.

## LAYER 2 — SPECTRAL.  STATUS: MIXED (3 true claims, 1 false, 1 liability)
- **Frobenius sieve** (ℓ∣n_t ⟺ π_p≡−1 mod a prime above ℓ): **TRUE** — verified π_p+1≡0
  mod a prime above 13, 3319, 22639 (and it's identically ℓ∣N(π_p+1)).
- **Elevated φ-ratio** n_t/φ(n_t)=1.6256 and **1.5× mod-3 CM support** (densities 1/2 vs 1/3,
  from first-principles residue count): **TRUE**. Fractions are 1/2 & 1/3, not 3/7 & 2/7.
- **Tight frame / ratio 576 / "spectrally optimal"**: **FALSE**. Full frame |λ|² ratio = 2⁴⁹⁸
  (min nonzero |c|=39, max nontrivial |c|=φ(n_t)/2 at k=n_t/3). 576 is only the typical-mode
  spread on the sub-family {3319,22639,P ∤ k}; it is not a frame bound.
- **Survival**: μ(n_t)=0 ⇒ c_{n_t}(±1)=0. The squared primes **annihilate** the k=±1
  survival mode — a liability for the framework, the opposite of "optimal".

## LAYER 3 — RECONSTRUCTION.  STATUS: BROKEN (as a reconstruction)
- Per-prime θ_ℓ ≈ arg(π_ℓ)+180° gives errors **2°–220°** (θ=50.551°) — fails.
- The only true angular fact: θ=arg(π_p)=arg(π_p+1)=50.551°; but π_p+1=∏(correct generators)
  requires knowing π_p to pick them (circular). θ is fully determined by **t=n_t−p−1** (exact),
  so the factorization/angles add NO information beyond the value n_t. Not a reconstruction engine.

## LAYER 4 — ANALYTIC.  STATUS: PARTLY CHECKED
- Conductor 𝔣=(1−ω)²(3+ω)(2−ω), **N(𝔣)=441 EXACT**; curve conductor 3·441·16=21168=2⁴3³7² ✓.
- Gauss sum |τ|²: **441 (self-dual char) or 1323 (unadjusted char) — convention-dependent**.
- Gauss-sum PHASE (τ=21√3·i) and Iwasawa μ=0: **external, NOT tested here**.

## THE LAYERING ITSELF (the connections)
- L1→L4: **real** (CM correspondence; conductor/𝔣 check exactly).
- L1→L2: **real for** the sieve + φ-ratio + mod-3 support; **false for** frame optimality.
- L2→L3: **broken** — the sieve does not reconstruct θ; θ is trivially t=n_t−p−1.
- "Triple alignment": it is a **DOUBLE** alignment — (i) arithmetic determination of n_t's
  factors by the Frobenius sieve, (ii) mod-3 CM support 1.5×. Both real. The third leg
  ("spectral optimality") is false and inverts to a liability (μ=0). The reconstruction payoff
  does not exist.

## DEFENSIBLE CORE (what survives the clean room)
n_t = N(π_p+1) has (a) prime factors arithmetically pinned by the Frobenius sieve, (b) an
elevated φ-ratio 1.6256, and (c) a 1.5× mod-3 CM support density. Real. It is NOT a tight
frame, NOT spectrally optimal, and NOT a θ-reconstruction engine; and the squared primes
make it a poor modulus for the survival mechanism (μ=0).

## IDEA-LEVEL TEST (2026-07-10) — real CM imprint, but GENERIC not a fingerprint
Tested the underlying idea, not the implementation:
- **Layers are one datum re-expressed:** n=p+1−t, n_t=p+1+t ⇒ everything is a function of
  π_p (t/θ). CM rigidity, not independent multi-level structure.
- **3∣n_t is a 76% CM effect, NOT a 1/3 coincidence** (CORRECTION to earlier framing):
  across 1434 primes for y²=x³+7, freq(3∣n_t)=0.762, freq(9∣n_t)=0.256 (vs random 0.333/0.111).
  Driven by inert primes (a=0 ⇒ n_t=q+1≡0 mod3). So the mod-3 support enhancement is a
  robust CM feature — I under-credited it before.
- **But it is GENERIC to the curve, not unique to secp256k1:** 74.5% of sampled twist orders
  have φ-ratio ≥ 1.625; secp256k1's n_t is a typical member of the y²=x³+7 family, not a
  distinguished one. So "unique multi-layer fingerprint" is FALSE; "CM rigidity imprints the
  twist order's small factors (curve-wide)" is TRUE.
