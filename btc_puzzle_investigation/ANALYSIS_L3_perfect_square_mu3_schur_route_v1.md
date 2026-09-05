# Assessment: the "L^(3) perfect square via μ₃/Schur/Frob³" universality argument

**Object:** the superelliptic curve `C_a : w^4 = x^3 + a`, its genus-3 Frobenius
polynomial `L(T)`, the degree-4 "new" (μ₄-primitive) factor, and the claim that
`L^(3)(T)` (base-change to `F_{p^3}`) is a perfect square **for all `a` and all `p`**,
elevated by a Schur's-lemma block-diagonalization argument.

Grades: residue-class facts = **VERIFIED-scope** (computed, Sage `CyclicCover.frobenius_polynomial`,
28 primes, `a=1..40`). Mechanism = **CITED** (standard supersingular / Jacobi-sum theory).
Refutation of "universal, `a`- and `p`-independent" = **PROVED** (explicit counterexample class).

---

## 1. What is actually true (verified)

Split `L(T) = E_a(T) · N_a(T)`, `E_a` = deg-2 factor of the elliptic quotient
`E_a : y^2 = x^3+a`, `N_a` = deg-4 "new" part (the μ₄-primitive `j∈{1,3}` piece).
Across `a` the new part `N_a` takes **exactly two shapes**, keyed by the cubic-residue
class of `a`:

| class of `a` | `N_a(T)` over `F_p` (p≡7 mod12) | already square? | `N_a^{(3)}` (cube roots) |
|---|---|---|---|
| A | `T^4 − 2p·T^2 + p^2 = (T^2−p)^2` | **yes**, at Frob¹ | `(T^2−p^3)^2` |
| B | `T^4 + p·T^2 + p^2` (roots `√p·ζ`, ζ⁶=1) | no | `(T^2−p^3)^2` |

The empirical `L^(3)` square is real: for the four cited primes, `~2/3` of twists give
`N_a^{(3)} = (T^2 − p^3)^2`. **But note the square value is a fixed scalar**
`(T^2 − p^3)^2` — identical for every `a` in the class (verified: p=43, a=3,5,7 → all
`(x^2−79507)^2`). It carries **zero** information about `a`.

## 2. The real mechanism (what the sketch was groping toward)

For `p ≡ 1 mod 3`, ω ∈ F_p, so the μ₃ automorphism `(x,w)↦(ωx,w)` is F_p-rational and
**commutes with Frobenius**. That much of the sketch is correct: Frob preserves the
μ₃-eigenspaces `V_ω, V_{ω²}` and is block-diagonal `diag(A,B)` over `F_p` (not just over
`Q(ω)`). The eigenvalues are **Jacobi sums** `J(χ₄^{±1}, ω^{±1}) ∈ Z[ζ_{12}]`, of absolute
value `√p`. Base-change to `F_{p^3}` cubes them; when the eigenvalue is `√p·ζ` with `ζ` a
6th root of unity (class B), cubing gives `√p³·ζ³ = ±p^{3/2}`, collapsing the block to a
scalar → perfect square. **This "ζ³ kills the phase" intuition is correct in class B.**

## 3. Where the sketch's proof fails (named defects)

- **D1 — "independent of `a`" is false.** The property splits by the cubic-residue class of
  `a` (3 classes; ≈2/3 give the square). Verified: within a prime, some `a` give
  `(T²−p)²` (square already at Frob¹), others `T⁴+pT²+p²` (square only after Frob³). There
  is no `a`-uniform statement.

- **D2 — "independent of `p`" is false.** For `p ≡ 2 mod 3` (i.e. `p ≡ 5, 11 mod 12`), ω∉F_p,
  Frobenius **swaps** `V_ω ↔ V_{ω²}`, the block structure is off-diagonal, and
  `L^(3)` is a perfect square for **0/40** twists at every such prime tested
  (5,11,17,23,29,41,53,59,71,83). The phenomenon requires `p ≡ 1 mod 3`. It is a
  **residue-class theorem, not a universal one.**

- **D3 — "B(g)=Ā(g) ⟹ square" is a non-sequitur.** Conjugate blocks give
  `char(Frob) = P·P̄` (a **norm form** in `Z[ω][T]`), which is generically **not** a square.
  Squareness after cubing needs the sharper fact `ᾱ_i³ = α_{σ(i)}³` — a specific
  Jacobi-sum coincidence (supersingularity / CM by Q(ζ_{12})), which must be proved, not
  inferred from conjugacy. The sketch also conflates the *within-block* ratio `α₂/α₁`
  with the *between-block* phase `ᾱ/α`; these are different quantities.

- **D4 — the proposed Sage command computes the wrong object.** The **Cartier–Manin /
  Hasse–Witt matrix** is the action of Frobenius on `H¹(O_C)` and reduces the L-polynomial
  **mod p**; it captures the p-rank, not the integer eigenvalues whose char poly is `L(T)`.
  For `p ≡ 7 mod 12` the new part is **supersingular** (p-rank 0), so its Cartier–Manin
  block is **nilpotent/zero** — it can never witness `(T²−p^k)²` over Z. "Symbolic
  block-diagonalization of Cartier–Manin over F_p(a)" would confirm the μ₃-grading and the
  p-rank, but **cannot** prove the perfect-square statement it is aimed at.

## 3a. ERRATA (self-review, `rootcheck.sage`)
§4 below said the supersingular eigenvalues are "√p·ζ_{12}". **Wrong — verified against
the defining polynomial:** for `N_a = T⁴+pT²+p²`, put `s=T/√p` → `s⁴+s²+1 =
Φ₃(s)Φ₆(s)`, roots = primitive 3rd/6th roots; for `N_a=T⁴−2pT²+p²=(T²−p)²`, `s=±1`.
So `N_a/√p` has multiplicative orders **{1,2,3,6} — all 6th roots of unity**, not 12th
(confirmed p=43,163). The `ζ_{12}` figured in the μ₄ character *before* the `p≡3 mod4`
quartic→quadratic collapse; on the actual eigenvalues it is 6th roots. Read every
"ζ_{12}" in §4 as "6th root of unity."

## 4. Correctly stated theorem

> Let `p ≡ 1 mod 3`. Then the μ₄-primitive part `N_a` of `Jac(w^4=x^3+a)` acquires the
> μ₃-eigenspace grading over F_p, its Frob eigenvalues are Jacobi sums `J(χ₄^{±1},ω^{±1})`,
> and for `a` in the appropriate cubic-residue class(es) `N_a^{(3)}(T) = (T²−p³)²`.
> If additionally `p ≡ 3 mod 4` the part is **supersingular** (eigenvalues `√p·ζ_{12}`),
> making the collapse a scalar. For `p ≡ 2 mod 3` the statement is **false for every `a`**.

This is provable properly via Davenport–Hasse + Stickelberger on the Jacobi sums — the
established route for diagonal/superelliptic curves — not via Schur + "conjugation phase".

## 5. secp256k1 scale — what transfers, and the leak question

`secp256k1 p = 2^256−2^32−977 ≡ 7 mod 12` (`≡1 mod 3`, `≡3 mod 4`) — **exactly the cited
class** (this is the same `p≡1 mod 3` that gives secp its GLV endomorphism). So the
correctly-stated theorem **does** apply at 256-bit scale: for the right cubic class of `a`,
`N_a^{(3)}` is the fixed square `(T²−p³)²`.

**But this is not a lever on ECDLP, for a concrete reason, not a mood.** The square is the
`a`-independent scalar `p^{3/2}` — a supersingular/CM fact about an *auxiliary* superelliptic
curve's L-polynomial. It is maximally *un*-informative about any particular `a`: everything
in the class maps to the *same* polynomial. A leak requires a feature that **varies with**
the secret and can be inverted; this collapses the secret's dependence to nothing. It is
consistent with the standing ledger ([[secp256k1_eisenstein_twin_density_2026_07_12]],
"No ECDLP consequence") and with the μ₃-subspace null work already in this folder
(`AUDIT_mu3_subspace_residual_v1.md`, `CONSEQUENCES_mu3_subspace_null_v1.md`).

## 6. Foreseeable iterations (worth / not worth chasing)

1. **Prove the correct residue-class theorem** via Jacobi sums (Davenport–Hasse). Clean,
   real, publishable-as-arithmetic — but already essentially classical (Fermat/superelliptic
   L-functions). Value: closes the μ₃ line rigorously; **zero** ECDLP bearing. *Worth doing
   only to retire the frontier honestly.*
2. **The `p≡1 mod 12` ordinary sub-case** is the only genuinely open-looking thread:
   `frac_sq3 ≈ 0.66` there **without** supersingularity — so the square is NOT purely a
   supersingular artifact. Characterize which `a` (cubic-residue split) and confirm the
   eigenvalues are still `√p·(root of unity)` in a CM sense. This is the one place the
   "why 2/3, not all" question has content. *Characterization, not closure — per drill protocol.*
3. **Higher base-change `L^(k)`** for other `k`: the collapse power is `lcm(order of ζ)`;
   mapping `k ↦ which classes collapse` is a finite character computation. Mildly interesting,
   no leverage.
4. **DO NOT** pursue this as a 256-bit "phase-lock ⇒ structure ⇒ attack" chain (D-class
   errors + collapse-to-scalar make it a dead lever), and **DO NOT** route it through
   Cartier–Manin (D4).

## Reproduce
`btc_puzzle_investigation/` scratch scripts `l3_test{,2,3}.sage`
(genus/L-poly via `CyclicCover(4, x^3+a).frobenius_polynomial()`; elliptic factor via
`EllipticCurve(GF(p),[0,a])`; cube roots over CC; `is_square()`; residue sweep 28 primes).
