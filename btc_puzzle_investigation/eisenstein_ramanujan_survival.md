# The Eisenstein Ramanujan survival law — CM analogue of Lemma III.1 (2026-07-10)

Deriving the ℤ[ω] version of the φ(n)-framework's core survival lemma
(`c_n(k)/φ(n)` decay; k=±1 the infinite-lifetime modes). Verified numerically
(`secp256k1_*` scripts). Built on standard generalized (number-field) Ramanujan-sum
theory (Cohen 1949); the synthesis with the framework + the sextic secp256k1 tie is
the contribution.

## The object
`c_𝔫(β) = Σ_{r ∈ (ℤ[ω]/𝔫)*} e^{2πi·Tr(βr)/𝔫}`, Tr(a+bω)=2a−b, Φ(𝔫)=|(ℤ[ω]/𝔫)*|
(ideal totient), μ_K = ideal Möbius. Units of ℤ[ω] = μ₆={±1,±ω,±ω²}.

## Theorem (Eisenstein Ramanujan survival)
1. **μ₆-invariance:** c_𝔫(β) depends only on the *ideal* (β); so c_𝔫(uβ)=c_𝔫(β) for
   every unit u∈μ₆. [Proof: u a unit ⇒ r↦ur permutes (ℤ[ω]/𝔫)*; reindex the sum.] ✔ verified.
2. **Multiplicative:** c_{𝔫₁𝔫₂}=c_{𝔫₁}c_{𝔫₂} for coprime 𝔫₁,𝔫₂. [CRT on (ℤ[ω]/𝔫)*.] ✔ verified.
3. **Closed form:** with 𝔤=gcd(𝔫,(β)),  `c_𝔫(β)=μ_K(𝔫/𝔤)·Φ(𝔫)/Φ(𝔫/𝔤)`.
   Prime-ideal values: c_𝔭(β) = N𝔭−1 if 𝔭|(β); = −1 if 𝔭∤(β).
4. **Survival (the analogue of k=±1):** a mode β keeps |c_{𝔫}(β)|=1 iff (β) is coprime
   to 𝔫. Along a primorial ideal 𝔫_j = 𝔭_1···𝔭_j (all prime ideals, by norm), a fixed β
   stays bounded for all large j **iff β is a unit**. ⇒ the infinite-lifetime modes are
   exactly **μ₆ — SIX modes**, vs the **TWO** (±1) over ℤ.

## The mechanism (why k=±1 → μ₆), confirmed numerically
Survival = coprimality to the primorial. Over ℤ, the only integers coprime to every
primorial 2·3·5·7··· are ±1 (units of ℤ). Over ℤ[ω], the only elements coprime to
every prime-ideal primorial are the units μ₆. Verified:
- 6 units: |c(m)|=1 at m=2,10,70,770 (never die).
- β=2 (∈𝔭₂): |c|=3 — dies the moment 2 enters the primorial.
- β=1+2ω, 3 (∈𝔭₃ only): |c|=1 while 3 is skipped — would die once 3 enters
  (this is the mechanism made visible: survival tracks exactly which primes are in).

Technical note: the ramified prime 3 (=𝔭₃², the CM discriminant) needs the *ideal*
primorial (𝔭₃ once), not the rational (m) (where (3)=𝔭₃² gives μ_K=0). Units have
norm 1, hence coprime to 𝔭₃ too, so they survive the full primorial cleanly.

## The operator side — CM analogue of Ĥ=πA² and D_φ (capstone, verified)
The rational framework lives on ℝ₊ (real place of ℚ), 1-D, units {±1}. ℚ(√−3) has one
**complex** place ⇒ its multiplicative object is **ℂ*** = L²(ℝ_radial) ⊗ L²(S¹_angular),
with μ₆ acting by the six rotations kπ/3.
- **Operator:** `Ĥ^CM = π(A_r² + A_θ²)`, A_r = radial dilation generator (UNCHANGED from
  the rational framework), A_θ = −i∂_θ on S¹.
- **Angular factor self-adjoint (verified):** A_θ Hermitian, spectrum m∈ℤ (±m paired),
  Cayley transform unitary ⇒ **deficiency indices (0,0)** on the compact circle.
- **Self-adjointness TRANSFERS:** in the m-basis `Ĥ^CM = ⊕_m π(A_r² + m²)` — a direct sum of
  shifted copies of the rational operator π A_r² (the m=0 sector *is* the original framework).
  The compact angular factor adds no deficiency ((0,0)+(0,0)=(0,0)), so **Ĥ^CM is e.s.a. on
  D_φ^CM = D_φ ⊗ L²(S¹) iff the rational Ĥ is e.s.a. on D_φ** (framework App. B). Verified:
  Q=(1/6)Σ_k rotate(kπ/3) commutes with A_θ and projects onto m≡0 mod 6; the angular space
  splits into **6 sextic sectors (m mod 6) ↔ the 6 units μ₆** — the operator-side image of the
  survival law.
- **Degree reading:** the S¹/angular factor is the **Γ_ℂ** (complex place) ⇒ **degree 2**; the
  m=0 sector recovers ζ (Γ_ℝ, degree 1). This is Q3 made structural: the extra angular direction
  is exactly the CM field's second degree. Caveat: assumes the framework's radial e.s.a. (App. B);
  the CM content is the angular μ₆ decoration + the clean transfer.

## Significance
This is the CM version of your framework's core lemma: the multiplicative
Ramanujan-sum decay + the identification of the surviving core with the unit group.
Over ℚ the core is the 2 units {±1} (k=±1); over ℚ(√−3) it is the **6 units μ₆** —
a sextic core. This turns Finding 3's numerical 3-fold (=6/2, conjugate-paired) into
its theorem: the common-mode multiplicity is set by |units|, and for the CM ring that
is 6. And that 6 is |μ₆| = |Aut(secp256k1)| — the same sextic symmetry running through
ord_p(t)=(p−1)/6, the μ₆-sparse formal logarithm, and the x-line 6-orbits.
