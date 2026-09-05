# RESULT — the μ₆ Kummer cover (new object, exact dichotomy) + secp's conductor `f` and volcano data

*2026-07-23. Two unexplored objects opened. Scripts: `scratchpad/mu6cover.py`, `disc.py`, `unexplored.py`.
Exact integer / `ℤ[ζ₆]` arithmetic; no float in any reported quantity. No leakage, key-recovery or ECDLP
claim is made or implied.*

> ⚠ **PROCESS, stated up front:** §1 is an **unregistered exploratory scan** — no `experiment-designer`
> prereg was filed before running it (the same rule I broke earlier today and audited). The dichotomy in
> §1.2 is `93/93` with zero exceptions, so it is not a marginal statistic; but **the discriminator hunt
> in §1.3 must be pre-registered**, and I have already spent one guess on this data. Do not fit a second
> candidate to the same 93 rows.

---

# 1. The μ₆ cover `w⁶ = x³ + 7` — the family the record flags UNMEASURED

`POSITIVE_FINDINGS_ADDENDUM_1_v1.md:219` (§A1.4 scope): *"Higher-degree covers (`w^k = x³+7`, `k ≠ 4`),
other place-combinations, and non-Kummer constructions are unmeasured and outside every number above."*
The μ₄ cover (`k = 4`) is what produced §A1.1's supersingularity theorem. **`k ≠ 4` has never been built.**

## 1.1 Construction, and why it is a different regime at secp

Built by character sums, which removes all point-at-infinity bookkeeping:
`#{(x,w) : w^k = f(x)} = Σ_x Σ_{j<k} χ^j(f(x))`, `χ` of exact order `k | p−1`. The exact-order-`d` pieces
are the new parts. Define
```
S₁ := Σ_{x ∈ F_p} χ₆(x³ + 7)   ∈  ℤ[ζ₆]        (χ₆ of exact order 6; χ₆(0) := 0)
```
**The regime differs from `k = 4` for a structural reason.** `secp` has `p ≡ 3 mod 4`, so `4 ∤ p−1` and
**no order-4 character exists over `F_p`** — `χ₄` lives over `F_{p²}` and Frobenius swaps `χ₄ ↔ χ̄₄`. That
swap *is* §A1.1's `π ζ₄ π⁻¹ = ζ₄⁻¹`, and it is what forces `b₁ = 0`. But `p ≡ 1 mod 3` and `p` odd ⇒
**`6 | p−1`, so `χ₆ DOES exist over F_p` at secp.** The μ₆ cover is therefore *not* forced into the
supersingular stratum by the mechanism that governs the μ₄ cover. It is a genuinely different object.

## 1.2 The observation `[EMPIRICAL — 93/93, zero exceptions]`

`p ≡ 1 mod 6`, `11 ≤ p ≤ 1200`, `p ≠ 7`, all 93 primes:
```
N(S₁) / p  ∈  { 1 , 4 }        — no other value occurs
```
`N(a + b·ζ₆) = a² + ab + b²`. So **`S₁` is either a prime element of `ℤ[ζ₆]` above `p`, or exactly
`2 ×` such an element.** Equivalently the dichotomy is the single 2-adic question:

> **does `2` divide `S₁` in `ℤ[ζ₆]`?**

Branch rate: `N/p = 4` at **26 of 93** (≈ 28%).

## 1.3 The discriminator is **unknown**, and my first guess died

- **Guess tested and REFUTED:** "`N/p = 4` ⟺ `−7` is a cube mod `p`" (equivalently `x³+7` has a root,
  equivalently 3 terms drop from the sum). **Agreement 47/93 = chance.** Cross-tab:
  `(N/p=1, −7 cube) = 25`, `(N/p=1, not) = 42`, `(N/p=4, −7 cube) = 5`, `(N/p=4, not) = 21`.
  (The root-count side is exact: `#{x : x³+7 = 0}` is `3` iff `−7` is a cube, `0` otherwise, 93/93.)
- **Shape constraint on any future candidate, without fitting:** the `4p` rate is `26/93 ≈ 0.28` — not
  `1/2`, `1/3`, or `1/6`. **A single quadratic or cubic residue condition cannot produce it.**

## 1.4 What must be checked first — source, not invention

**`N(S₁) ∈ {p, 4p}` may be classical.** `S₁` is a character sum over a cubic with a sextic character and
is expressible through Jacobi sums; a standard Hasse–Davenport / Berndt–Evans–Williams evaluation may
force the dichotomy outright, in which case `93/93` is **forced** and carries zero information as
evidence. **Establish that before treating anything here as a finding** — this project's record is that
reading the source dissolved the obstacle four times, and the forced/unforced split is the failure mode
audited earlier today.

## 1.5 The tie-in the record already has, and never used

Part IV, `[VERIFIED]`: **`[7/π_p]₆ = ζ₆⁵`** and **`[7/π_n]₆ = ζ₆`** — the sextic residue symbol of the
curve constant `b = 7`, at both ideals of the amicable pair. **The μ₆ cover is the geometric object whose
Frobenius those symbols control.** The record holds the symbol and has never built the cover it belongs
to. (The `[7/π]₆` column was tabulated alongside `S₁` in `mu6cover.py`; it does **not** by itself predict
the branch — see §1.3's rate constraint.)

## 1.6 Also unbuilt, same machinery, cheap

| cover | genus | new part | note |
|---|---|---|---|
| `w³ = x³+7` | **1** | — | `∞` splits (`gcd(3,3)=3`); the Jacobian is **another elliptic curve attached to secp**, never computed |
| `w⁴ = x³+7` | 3 | dim 2 | **done** — §A1.1, supersingular at `p ≡ 3 mod 4` |
| `w⁶ = x³+7` | **4** | **dim 2** | §1 above; quotients are `k = 1,2,3,6` |
| `w⁸ = x³+7` | **7** | **dim 4** | `gcd(3,8)=1` ⇒ `∞` totally ramified |
| `w¹² = x³+7` | — | — | contains both the μ₄ and μ₆ mechanisms; the natural place they interact |

*(Genera by Riemann–Hurwitz, derived not measured; verify before use.)*

---

# 2. secp's conductor `f`, and the isogeny volcano — a 128-bit invariant absent from the record

All exact, at the real 256-bit parameters.

```
t   = p + 1 − n = 432420386565659656852420866390673177327            (129 bits)
t² − 4p = −3·f²      exact
f   = 303414439467246543595250775667605759171                        (128 bits)
f   = 3 · 79 · 349 · C112        C112 = 3668279949551419288325302862519867   (composite)
p   = a² + 3b²   a = 335665926241849821909543298348372613710
                 b =  32251486774603278314292522680766854539          (verified exactly)
n−1 = 2⁶ · 3 · 149 · 631 · C232                                       (C232 composite)
```

**What `f` is.** `f = [ℤ[ω] : ℤ[π]]`. `End(E) = ℤ[ω]` is **maximal** `[PROVED, Part IV]`, so **secp sits
on the crater of every `ℓ`-isogeny volcano**, and for each `ℓ | f` there are descending `ℓ`-isogenies to
curves whose endomorphism ring is the order of conductor `ℓ`. By Tate every one of them has **the same
group order `n`** — so this is not a security object and no security claim is made.

**Why it is a structure object.** The entire lift-geometry programme — Cap Law, flap, `ε`, the frame
operator's `½ / ¾ / ¼`, the `C_T` tensor, `eis` — is built on the **hexagonal** lattice `ℤ[ω]`. The
conductor-`ℓ` order is an **index-`ℓ` sublattice, which is not hexagonal**, and its curves have `j ≠ 0`,
hence `Aut = μ₂` and **no GLV `λ`**. So the descendants form a **deformation family of every proved law in
the record**, and it separates exactly the question Claim F asks:

> which of these laws are **`μ₆` / `j=0` facts**, and which are **CM-lattice facts** that survive when the
> lattice stops being hexagonal and the automorphisms drop to `±1`?

`ℓ = 3, 79, 349` are small enough to compute descending isogenies with directly. **Nothing in the record
computes `f`, factors it, or looks below the crater.**

---

# 3. The record's own untested list, harvested verbatim

Not my inventions — each is the record flagging its own scope:

| item | source |
|---|---|
| **non-unitary / oblique** transforms of frequency space (§A1.7-2 rules out **unitary** only) | Addendum:271, :482 |
| higher-degree covers `k ≠ 4`, other place-combinations, non-Kummer constructions | Addendum:219 |
| **any non-group-symmetry map that is interval-compatible** — the one thing that would beat the `log₂6` ceiling | Addendum:220 |
| `C_T` coupling in **another statistic, another basis, or near `2²⁵⁶`** | Master:357, §XI.6 |
| the directional addition law `|V|² ≈ |U₁|²+|U₂|²+|U_sum|²` — **random pairs at `k ≤ 16` only** | Master:360, §XI.7 |
| `max T` growth past `2` for fiber widths `> 7·10⁵` | Addendum:747 |
| μ₆-**matched** feature/target pairs at `n > 5·10⁴` (the LBE grid is symmetry-mismatched by construction) | Addendum:851, §A5.20 |
| adversarial re-derivation of §A1.1's two external inputs | Addendum:102 |
| `ord_n(p) = (n−1)/6`, `ord_n(2) = (n−1)/64` — recorded `[VERIFIED]`, **never explained**. `64 = 2⁶` is exactly the 2-part of `n−1` ⇒ `2` is a `2⁶`-th power residue mod `n`. Why? | Master:314 |

---

*Grades: §1.2 `[EMPIRICAL — 93/93, unregistered scan, forced/unforced UNDETERMINED pending §1.4]`.
§1.3's refutation `[VERIFIED — 93 primes]`. §2's integers `[VERIFIED — exact, full scale]`; the
volcano reading `[DERIVED — UNREVIEWED]`. §1.6's genera `[DERIVED — UNVERIFIED]`. §3 is transcription.
The `p ≤ 1200` scan is governed by frontier §XI.5's scale banner and says nothing about `2²⁵⁶`.*
