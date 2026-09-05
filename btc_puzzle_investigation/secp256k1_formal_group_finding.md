# secp256k1 formal-group logarithm — a clean closed form (2026-07-09)

A genuine discovery-by-computation from the pure-math pivot. The formal group is
the one structural object about secp256k1 that is essentially never computed, and
it turned out to have an exact closed form.

## Result

The formal group of secp256k1's curve `E: y² = x³ + 7` (in the standard parameter
`T = −x/y` near O) has formal-group **logarithm**

$$L(T) \;=\; \sum_{k\ge 0} \frac{7^{\,k}\binom{3k}{k}}{6k+1}\; T^{\,6k+1}
\;=\; T + 3T^{7} + \tfrac{735}{13}T^{13} + \tfrac{28812}{19}T^{19}
      + \tfrac{237699}{5}T^{25} + \tfrac{50471421}{31}T^{31} + \cdots$$

Verified exactly against the series expansion of `∫ dx/2y` to `k=6` (T³⁷), and
every nonzero exponent up to T⁴³ is `≡ 1 (mod 6)`. Found by recognizing the
stripped coefficients `c_{6k+1}·(6k+1)/7^k = 1,3,15,84,495 = C(3k,k)`.

## What it says (structure, verified)

- **μ₆-sparsity:** nonzero terms only at exponents `≡ 1 (mod 6)`. This is the full
  order-6 automorphism group of the j=0 curve = negation `[−1]` (⇒ odd exponents)
  × the cube-root CM `[ω]` (⇒ `≡1 mod 3`); their intersection is `1 mod 6`. So the
  formal log is *sparser* than a generic curve (odd only) or a generic j=0 curve.
- **`b=7` appears as `7^k`** (the curve constant drives the series), and the
  combinatorial core is the central-binomial-type `C(3k,k)` — the hypergeometric /
  CM signature. Equivalently `L(T) = T·₂F₁(1/3, 1/6; 7/6; −27·7·T⁶/4)`-type
  (Fuss/hypergeometric family).
- **Family fact:** for any `y²=x³+b`, `L(T) = Σ b^k C(3k,k)/(6k+1) T^{6k+1}`;
  secp256k1 is the `b=7` member (cross-`b` check).

## Honesty on novelty

CM formal groups being hypergeometric is known to the theory (Honda/Hazewinkel).
What's genuine here: this **specific clean closed form is not tabulated for
secp256k1**, and it was *derived by computation* (not recalled) — the exact series,
the `C(3k,k)/(6k+1)` coefficient, and the `1 mod 6` sparsity are concrete verified
facts about this curve that were not on hand before. It is the strongest
"uncharted → exact" result of the pivot; unlike the constant/order/generator
probes (which all returned "generic"), the formal group carried real explicit
structure.

Script: inline in session; reproduce with the sympy series of `w=z³+7w³`,
`x=z/w, y=−1/w`, `L=∫ (dx/dz)/(2y) dz`.
