# CM twist-order divisibility: a sign-definite dependence law (2026-07-10)
Pulled the "non-independence of divisibility conditions" thread (Zywina's gap) for the
CM twist order. Found a clean, general, sign-definite law. Scripts in session.

## The law (verified 24/24 across two CM fields)
For a CM elliptic curve E/K-CM, twist order n_t = #E'(F_q) = q+1+a_q:
- **Supersingular primes** (q inert in K ⇒ a_q=0): n_t = q+1, so P(ℓ∣n_t)=1/(ℓ−1),
  independent of ℓ's splitting type.
- **Ordinary primes** (q split in K): P(ℓ∣n_t) elevated if ℓ SPLITS in K, suppressed if ℓ INERT.
- **Reversal law:** P(ℓ∣n_t | supersingular) > P(ℓ∣n_t | ordinary)  ⟺  ℓ inert in K.
Verified: D=−3 (ℚ(√−3), y²=x³+7) 12/12; D=−4 (ℚ(i), y²=x³+x) 12/12. Non-CM curve: no
such structure (divisibility ≈ independent, ratios ≈1.0).

## Corollary (the sign rule first observed)
Conditioning on the ramified prime ℓ₀ dividing n_t over-weights the supersingular half, so
  dep(ℓ₀, ℓ) = P(ℓ₀&ℓ)/(P(ℓ₀)P(ℓ)) > 1 ⟺ ℓ inert in K   (D=−3, ℓ₀=3: 16/16).

## Mechanism (fully explicit)
ℓ∣n_t ⟺ Frobenius has eigenvalue −1 mod ℓ. The CM Galois image at ℓ is a split Cartan if
ℓ splits in K, nonsplit Cartan if ℓ inert. The −1-eigenvalue rate in the ordinary regime is
governed by that Cartan type (higher for split), while the supersingular regime gives the
fixed 1/(ℓ−1). The sign of the bias is the difference. This is the CM bimodality
(supersingular vs ordinary) crossed with the mod-ℓ Cartan type.

## HONEST STATUS — likely known-in-principle; needs a lit check
All ingredients are standard: supersingular = inert primes (Deuring); mod-ℓ CM Galois image
= Cartan normalizer (classical); non-independence of divisibility conditions = Zywina's
refinement of Koblitz. So the law is DERIVABLE from known theory and is probably
known-in-principle.

## LITERATURE CHECK RESULT (2026-07-10, read the actual PDF): KNOWN — it is THEOREM 4.3
Pajaziti–Sadek, "Divisibility of orders of reductions of elliptic curves" (arXiv:2301.00711):
- Prop 3.1 / Cor 3.3 (p.6): uses the exact twist order **2p+2−|E_p| = n_t**; reduction order
  over K=ℚ(√d) is |E_p| if p SPLITS, |E_p|·n_t if p INERT.
- p.2: the CM-by-√−3 case explicitly (supersingular ⟺ p≡2 mod3; |E_p|≡0 mod3 inert vs 0/1
  split) via the character sum Σ(f(x)/p) — named as the main tool. = our ramified imprint.
- **Theorem 4.3 (p.9): for ℓ∣M_K(E),  |E_p|≡0 mod ℓ if (d/p)=1 (split),  ≡ 2p+2 mod ℓ if
  (d/p)=−1 (inert)** — i.e. split → ℓ∣group order, inert → ℓ∣n_t. THIS IS our split/inert →
  group/twist divisibility, as a DEFINITE statement.
Our sign-reversal law = Theorem 4.3 seen statistically. Theirs is sharper (definite, general
K, torsion-growth ℓ); ours is the statistical shadow for general ℓ on the specific CM curves,
which is exactly what their character-sum method outputs.
VERDICT: KNOWN — it is Theorem 4.3 of Pajaziti–Sadek. Our contribution = a worked example /
statistical reformulation. NOT novel. Cite Pajaziti–Sadek Thm 4.3.
