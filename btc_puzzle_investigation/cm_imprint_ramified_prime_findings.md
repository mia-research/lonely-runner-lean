# CM imprint on the twist order n_t — mechanism + generalization (2026-07-10)
Tested the one real thread from the layering idea. Script in session.

## The exact mechanism
For Frobenius with char poly x²−a_q x+q, charpoly(−1) = 1+a_q+q = n_t. Hence:
  **ℓ ∣ n_t  ⟺  −1 is an eigenvalue of Frobenius mod ℓ  ⟺  π_p ≡ −1 mod a prime above ℓ.**
That is the Frobenius sieve, exactly. freq(ℓ∣n_t) = P(Frob has eigenvalue −1 mod ℓ).

## Why the CM ramified prime is boosted
CM ⇒ inert primes (density ½) are supersingular (a_q=0). At the RAMIFIED prime ℓ₀,
inert q ≡ −1 mod ℓ₀ ⇒ char poly ≡ x²−1 = (x−1)(x+1) ⇒ −1 is ALWAYS an eigenvalue.
So every inert prime forces ℓ₀∣n_t; split primes add more. This elevates freq(ℓ₀∣n_t).

## Generalizes across CM discriminants (verified, primes < 12000)
| curve            | CM disc | ramified ℓ₀ | freq(ℓ₀-imprint)        | inert→a=0 |
|------------------|:-------:|:-----------:|------------------------|:---------:|
| y²=x³+7          |  −3     | 3           | freq(3∣n_t)=0.762      | 100%      |
| y²=x³+x (j=1728) |  −4     | 2           | freq(4∣n_t)=1.000      | 100%      |
| y²=x³+x+1        | none    | —           | freq(3∣n_t)=0.435 (no boost) |     |
Decisive: D=−4 imprints at 2 (4∣n_t always) and leaves 3 at baseline (0.313). So the
imprint is a general CM effect at the discriminant's ramified prime, NOT special to ℚ(√−3).

## Baseline CORRECTION (my error)
The right null for freq(ℓ∣n_t) is P(Frob has −1 eigenvalue mod ℓ), NOT 1/ℓ. For a
surjective mod-3 image (non-CM) this is ≈0.42 (observed 0.435), not 1/3. So the CM boost
is 0.76 vs ≈0.42 generic — real and CM-driven, but I had overstated its size by comparing
to 1/3. secp256k1's 3∣n_t sits in the CM-elevated regime (correct), but the elevation is
above 0.42, not 0.33.

## Status
Real, mechanistic, and general: the CM structure imprints n_t at the discriminant's
ramified prime via supersingular inert primes (charpoly(−1)=n_t). This is the defensible
core of the whole "n_t is a spectral object" line — an exact CM fact, curve-family-wide
(not a secp256k1 fingerprint), correctly sized against the eigenvalue baseline.

## LITERATURE CHECK (2026-07-10) — KNOWN, not novel
Checked against the literature. This is a specific instance of the established
"divisibility bias" for elliptic-curve reduction orders:
- Cojocaru (2004): density of {p : m|#E(F_p)} exists (Chebotarev) and is biased ABOVE 1/m
  — the named "divisibility bias." (My baseline correction ~0.42-not-1/3 IS this bias.)
- Standard CM: p inert/ramified in K ⇒ supersingular reduction (the inert→a=0 mechanism).
- Zywina, "A refinement of Koblitz's conjecture" (arXiv:0909.5280): non-independence of
  divisibility conditions mod distinct primes; CM cases.
- Recent: Lee–Sheen, "Divisibility Biases in the Orders of Elliptic Curve Reductions"
  (arXiv:2606.25067, 2026); "Divisibility of orders of reductions" (arXiv:2301.00711).
The twist version (eigenvalue −1) and the CM ramified-prime elevation factor through these.
VERDICT: known-in-principle. Contribution = a clean worked example for secp256k1's n_t,
expository not novel. Do not repitch as a discovery.
