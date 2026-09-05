# The 120° certificate by EXHIBITION — and the `χ₂(−1)` branch the collapse identity was missing

**Date:** 2026-08-01.
**Targets:** item A of `NEXT_SESSION_PROMPT_2026-08-01_v2.md`;
`CORRECTION_120deg_census_certification_direction_v1.md` §5 (the repair spec);
`ANALYSIS_n1_charpoly_collapse_v1.md` §2 (the collapse identity).
**Scripts:** `verify_120deg_symbolic_factorization_v1.py` (+ `.log`),
`verify_120deg_exact_certificate_v2.py` (+ `.log`, `RESULT_120deg_exact_certificate_v2.json`).
Both pass `check_no_float.py`.

---

## 0. Summary

Two things, one of which was not asked for.

1. **The repair, done by a different route than the one specified.** The CORRECTION asks for a
   resultant + first-subresultant certificate computed in `ℤ[ζ_M]`, `M = lcm(N,k)`. That is not
   needed. The common quadratic factor can be **written down in closed form** and its divisibility
   verified as a *polynomial identity* in `ℤ[e₁, p, ω]/(ω²+ω+1)` with `e₁, p` free indeterminates.
   Exhibiting a divisor is a **lower** bound on `deg gcd` — exactly the direction the multi-modular
   census cannot certify. §1–§2.

2. **A branch error in the collapse identity, found by doing (1).** `e₂ = e₁² + p` is not the
   general law. The general law is
   > **`e₂ = e₁² − χ₂(−1)·p`**
   so `e₂ = e₁² + p` holds only at `p ≡ 3 mod 4`. At `p ≡ 1 mod 4` the relation is
   `e₂ = e₁² − p`, equivalently `V₂ = V₁² − 2p`. §3.

---

## 1. The exhibited factorization (PART 1 — symbolic, exact, both branches)

Write `ε = χ₂(−1) = legendre(−1,p)` and `ω = ζ₃`. Take as premises the two coefficients that
`ANALYSIS_n1_charpoly_collapse_v1.md` §1 derives from the closure (graded there `[PROVED — FORCED]`):

> `e₃ = ε·p·e₁`,  `e₄ = p²`

Then, **as an identity in `ℤ[e₁, p, ω]/(ω²+ω+1)` with `e₁` and `p` free**:

> `L(T) = T⁴ − e₁T³ + (e₁² − εp)T² − εp·e₁T + p² = D(T)·D̄(T)`
>
> `L(ωT) = ω·(T² + e₁T + εp)·D(T)`
>
> where **`D(T) = T² + ω·e₁·T + ε·p·ω²`**, `D̄(T) = T² + ω²·e₁·T + ε·p·ω`

`D` is **monic of degree 2 for every value of `e₁` and `p`** — there is no degeneracy locus, no
genericity hypothesis, no "for all but finitely many". Therefore

> **`e₂ = e₁² − εp` ⟹ `deg gcd(L(T), L(ωT)) ≥ 2`, unconditionally.**

**Verified:** `verify_120deg_symbolic_factorization_v1.py`, both `ε = ±1`, exact integer arithmetic
in the ring (no float, no resultant, no `ℤ[ζ_M]`). **Negative control:** perturbing `e₂` off the
relation by `+1, +2, −3` breaks the divisibility in all 6 cases — the identity is not vacuous.

### Why this is better than the specified repair, not merely different

The CORRECTION's §5 spec is correct but expensive and hazardous:

| | spec'd route (`Res_T` + `S₁` in `ℤ[ζ_M]`) | this route |
|---|---|---|
| ring | `ℤ[y]/Φ_M(y)`, `M = lcm(N,3) = 3n`, degree `φ(3n) = 2(n−1) ≈ 5000` | `ℤ[e₁,p,ω]/(ω²+ω+1)`, degree 2 |
| joint pinning of `ζ_N`, `ζ_k` | load-bearing, easy to get wrong | not needed — `ω` is the only root of unity present |
| `reduce_phi_prime` rewrite for general `Φ_M` | required (CORRECTION §5) | not needed |
| zero-ring hazard | the reason §5 was retracted once already | structurally absent |
| cost | per cell, per prime | **once, for all `e₁`, all `p`, all cells, both branches** |

The quantifier is the point. The spec'd certificate is a computation *per cell*; the identity is
proved once with `e₁` and `p` free, so it covers every cell of every prime — including primes never
enumerated.

## 2. What the certificate now certifies, and what it still does not

The CORRECTION's §5 demand — **state and use the conjunction** — is met:

| half | source | direction |
|---|---|---|
| `g ≥ 2` | §1 above, given `e₂ = e₁² − εp` | **lower** bound — NEW, this is what was missing |
| `g ≤ 2` | `min_l g_l = 2`, census, 22 primes (`RESULT_n1_120deg_exact_v1.json`) | **upper** bound — already had |

Conjoined: **`g = 2` exactly**, at every cell where the measured premise `e₂ = e₁² − εp` holds.

**Two premises are inherited, not proved here**, and the grade must say so:

- `e₃ = ε·p·e₁` and `e₄ = p²` are `[PROVED — FORCED]` *from the closure* per
  `ANALYSIS_n1_charpoly_collapse_v1.md` §1. They are not independently re-measured in this work:
  doing so needs `V₃, V₄`, i.e. `O(p³)`/`O(p⁴)` point counts. The record reports them
  `[CONFIRMED-independent]` at `p = 43, 67, 127` only.
- `e₂ = e₁² − εp` is **measured** (§3), not derived. Deriving it is the open item — unchanged.

**This does not prove uniformity in `p`.** It converts "the law holds at these 2464 cells, on
non-certifying odds over 5 ells" into "the law holds at these 2464 cells, exactly, *given one
measured integer per prime*". The remaining gap is the same one the record already names: prove
`e₂ = e₁² − εp` for all `p`. §1's identity sharpens what must be proved, and now also fixes its
statement (§3).

## 3. The branch correction — `e₂ = e₁² + p` is the `p ≡ 3 mod 4` case only

`ANALYSIS_n1_charpoly_collapse_v1.md` §2 derives `e₂ = e₁² + p` from a trigonometric parametrization
`α₁ = √p·e^{iθ}`, `s₁ = 2i√p·sin θ` — which is the `α ↦ −ᾱ` closure, i.e. the **`p ≡ 3 mod 4`**
case. §1 of that same file notes the closure changes to `α ↦ ᾱ` at `p ≡ 1 mod 4` and works out the
consequence for `e₃` — but **never revisits `e₂`**. The `ε = +1` value of `e₂` is stated nowhere in
the record.

Redoing the §1 derivation on the `ε = +1` closure (roots pair with product `+p`, factors
`T² − sT + p`) and matching coefficients gives `e₂ = e₁² − p`. The symbolic run confirms this is the
*only* sign for which `D` divides `L` at `ε = +1`, and that `e₂ = e₁² + p` **fails** there.

Equivalently, in the `V` variables (`e₁ = −V₁`, `e₂ = (V₁² + V₂)/2`):

> **`V₂ = V₁² − 2·χ₂(−1)·p`** — i.e. `V₂ = V₁² + 2p` at `p ≡ 3 mod 4`, `V₂ = V₁² − 2p` at `p ≡ 1 mod 4`.

**Why this was never caught.** Every prime at which the `V₂` identity has been verified is
`p ≡ 3 mod 4`: `RESULT_e2_identity_extended_verification_v1.md` sweeps 43, 67, 79, 127, 163, 211,
547 — all `≡ 3 mod 4`, and scopes itself to `p ≡ 7 mod 12`. The census's stratum C (577, 733, 1237,
1249, 1669) is `p ≡ 1 mod 12` and *did* exercise the `ε = +1` branch — but only through
`run_n1_120deg_v1.py`, which computes `e₂` from the histograms and never tests it against a
predicted value. So the branch was exercised without ever being read.

The `[VERIFIED]` grade on the `V₂` identity therefore carries scope `p ≡ 3 mod 4` and should say so.

## 4. Measured premise — result (PART 2)

`verify_120deg_exact_certificate_v2.py`, all 22 census primes, exact integer convolution:

> **22/22 primes satisfy `e₂ = e₁² − χ₂(−1)·p` exactly, at every cell.**
> `f[d]` is constant `= 0` off `d = 0` at every prime, so `V₂(a) − V₁(a)²` is a **single integer per
> prime, independent of `a`** — uniformity over cells is not a sweep result, it is structural.

| stratum | primes | `ε` | target `V₂ − V₁²` | result |
|---|---|---|---|---|
| IN | 43, 67, 79, 127, 163, 211, 547 | −1 | `+2p` | 7/7 hold |
| S | 823 … 2503 (10 primes) | −1 | `+2p` | 10/10 hold — **`e₂`-relation never checked at these before** |
| C | 577, 733, 1237, 1249, 1669 | +1 | `−2p` | **5/5 hold — the new branch, predicted before measurement** |

**Controls.** Four plants on `h₂` (`+1` at `d=0`; `+1` at `d=3`; `−2` at `d=1`; `+2p` at `d=0`) are
all rejected — two by the constancy test, two by the value test. The checker is not vacuous.
**Sign control:** the flipped-branch target `+2εp` matches at 0/22 primes, so the test discriminates
the branch rather than passing on either.

The stratum-C result is the load-bearing one: `e₂ = e₁² − p` at `p ≡ 1 mod 4` was **derived in §1/§3
and then measured**, not fitted. It is the only genuinely out-of-sample prediction in this work.

### 4a. An uncharacterized diagnostic — recorded, NOT named

`sum(h₂) − 2p` is exactly `0` at all 17 `p ≡ 3 mod 4` primes and nonzero at all 5 `p ≡ 1 mod 4`
primes: `−4, −16, −4624, −4096, −5776` — every one a negative perfect square
(`−2², −4², −68², −64², −76²`). Writing `p = a² + b²`, `2·(even part)` reproduces `√|·|` at 4 of the
5 (733, 1237, 1249, 1669) and **fails at 577** (`2·24 = 48`, observed `2`). No `p = c² + 3e²`
parametrization tried fits either.

**Not a finding.** One clean break in five, on a partial pattern, at `n = 5`. Per the drill protocol
(retest out-of-sample before naming; count only unforced hits) this is a candidate for a probe, not
a law. It is also **off-object**: `sum(h₂) = V₂(0)` is the `a = 0` frequency, which `mu6_reps`
excludes and which no claim here covers. It cannot affect §4 — the identity is tested on `a ≠ 0`
only, and `f` is constant off `d = 0` at every prime including all five.

Recorded so it is not rediscovered as a surprise, and so the record does not keep carrying
`sum(h₂) = 2p` as a branch-free constant. It is not.

## 4b. Independent cross-check of §1 (the ring arithmetic is hand-rolled — so it was checked twice)

`ℤ[e₁,p,ω]/(ω²+ω+1)` in `verify_120deg_symbolic_factorization_v1.py` is a bespoke implementation; a
bug there would fake the whole certificate. `xcheck_120deg_identity_vs_census_gcd_v1.py` re-tests the
prediction through **`run_n1_120deg_v1.deg_gcd` — the census's own Euclid routine** — at
`l = 1000003`, on random `(e₁, p)`:

| arm | n | result |
|---|---|---|
| on-relation `e₂ = e₁² − εp`, `ε = +1` | 400 | `g = 2` at **all 400**, no other value seen |
| on-relation, `ε = −1` | 400 | `g = 2` at **all 400** |
| off-relation `e₂ = e₁² − εp + δ`, `δ ∈ {1,2,−1,−3,7}`, both `ε` | 800 | `g ≥ 2` at **0/800** |

Two independent code paths agree. The off-relation arm additionally shows the relation is not merely
sufficient but **necessary** at these `(e₁,p)` — so `e₂ = e₁² − χ₂(−1)p ⟺ g ≥ 2` is bidirectional
here, not just the one direction §1 proves.

## 5. Error class

Same class as the CORRECTION it repairs, one level up: a derivation performed in one branch of a
case split and then quoted branch-free. The collapse identity's own §1 *sets up* the case split
(`χ₂(−1)`) and applies it to `e₃`; §2 then drops it for `e₂`. Nothing in the record contradicted the
over-general statement because the only primes ever tested were on the branch where it is true —
**a scope that was inherited by every downstream file, including this session's starting prompt.**
