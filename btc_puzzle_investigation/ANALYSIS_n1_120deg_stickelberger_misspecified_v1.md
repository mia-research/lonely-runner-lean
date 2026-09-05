# The classical Stickelberger (L-Stick) framing is mis-specified for the `a≠0` twist — and where it relocates

**Date:** 2026-08-10 · Sage computation, exact. **No leakage/ECDLP claim.** Resolves the L-Stick
premise v3 §4 flagged as "must be verified before the citation is used." Outcome: for the classical
form, the premise is **false at the setup level**; the structure relocates to the CM field `ℚ(ω)`.

## The test that was requested, and why the firing control cannot fire

Requested (user, 2026-08-10): factor the ideal `(α₁)` at `p=43, a=1`, compute the Stickelberger element
for the character orders, compare valuations. Executed in Sage (`stick3.sage`, `stick_cm.sage`) on the
honest `e_k` (from the C-computed `V₁..V₄`). The comparison **cannot be set up**, for two independent
Sage-verified reasons — not because the numbers disagree, but because the object is not of the type
Stickelberger governs:

1. **`χ_a` is not a multiplicative character of `F_p`.** It is a character of `E(F_p) ≅ ℤ/n`, `n=31`,
   and **`31 ∤ p−1 = 42`**. Stickelberger factorizes Gauss/Jacobi sums of characters of `F_p^*`
   (order `| p−1`). The `a≠0` eigenvalues involve the curve character `χ_a`, so **they are not
   classical Gauss/Jacobi sums** — there is nothing for Stickelberger to factorize.
2. **`p` is inert in `ℚ(ζₙ)`.** `ord(43 mod 31)=30`, so `(43)` is a single prime `P` of `ℚ(ζ₃₁)`
   (`f_res=30`, `e=1`). Classical Stickelberger's discriminating content is the *distribution* of
   valuations across the `g=φ(m)` primes above a **split** `p`; with `p` inert there is one prime and
   no distribution to test. `[VERIFIED — Sage]`

So the "firing control" (computed valuations vs Stickelberger weights) **has no Stickelberger element to
fire against.** `[CLOSED — scoped]` for the *classical* framing: object = "the `a≠0` eigenvalue is an
`F_p^*` Gauss/Jacobi sum Stickelberger factorizes over `ℚ(ζₙ)`"; power = decisive at setup, Sage-checked;
**scope = the classical framing only** — it does *not* close the CM version (below) or uniformity.

## The actual factorization data `[VERIFIED-exact, p=43, a=1]`

- Charpoly `f(T)=T⁴ − e₁T³ + e₂T² − e₃T + e₄` with `e₃ = −p·e₁`, `e₄ = p²`.
- `f` is **irreducible over `ℚ(ζ₃₁)`** ⇒ `ℚ(α₁)` has degree **120** over `ℚ` (not 4–8; the coefficients
  live in `ℚ(ζ₃₁)`, so the "small field" expectation was wrong).
- **Newton polygon of `f` at `P | 43`: slopes give `P`-adic valuations `{α_i} → {0,0,1,1}`** — the
  **ordinary** pattern (two unit roots, two of valuation 1). `v_P(c₀..c₄)=[2,1,0,0,0]`. Within each
  `ι`-pair `{α,−ᾱ}`, `v(α)+v(−ᾱ)=v(p)=1`, so one unit + one non-unit; the `ζ₃`-partner shares the
  valuation of its source (`ζ₃` a unit).

## Where the structure actually lives — the redirect `[LEAD]`

The `ζ₃` in `α₂/α₁=ζ₃` is **`ω`, the CM unit of `End(E)=ℤ[ω]`**. And the field where `p` splits is the
CM field, not the twist field:

> **`43` is INERT in `ℚ(ζ₃₁)` but SPLITS in `ℚ(ω)=ℚ(ζ₃)`:** `(43)=(w+7)(w−6)=π·π̄`, `43=4²+3·3²`,
> `N(π)=43`. `[VERIFIED — Sage]`

So the correct home for a Stickelberger/Hecke-character factorization is the **CM field `ℚ(ω)`** (and the
CM field of the abelian surface `A_new` built over it), where `p` splits as `π π̄` — a
**Gross–Koblitz / CM-Hecke-character** story, not classical Stickelberger over `ℚ(ζₙ)`. The ordinary
Newton polygon `{0,0,1,1}` is exactly the CM-ordinary reduction signature, and the unit roots are the
`π`-adic (Hecke-character) eigenvalues. This is where `α₂=ω·α₁` should be *forced*: `ω` acting through
`ℤ[ω]` on the `π`-part.

## Ledger effect

- v2 §5's Stickelberger success was for `J(χ₃,χ₄)` with `χ₃,χ₄` characters of `F_{p²}^*` (orders `3,4 |
  p²−1`) — genuine field characters. It **does not transfer** to the `a≠0` twist family, whose character
  `χ_a` is a curve character. v3 §4's "`a≠0` premise unverified" is now **resolved: the classical
  premise is false; L-Stick must be taken over the CM field `ℚ(ω)`, not `ℚ(ζₙ)`.**
- **Uniformity remains OPEN.** This eliminates one framing and sharpens the target; it proves nothing
  about all `a`/all `p`. Next well-posed step: express Frobenius of `A_new` (twisted) as a Hecke
  character of `ℚ(ω)` and test whether `ω`-multiplication on the `π`-part forces `α₂=ω α₁` uniformly.
