# CORRECTION — the 120° census certifies `g ≤ 2`, not `g = 2`: the multi-modular argument is one-sided

**Date:** 2026-07-31. **Target:** `RESULT_n1_120deg_exact_v1.md` / `.json`, its grade
`[PROVED-exact]`, and the reasoning stated at `run_n1_120deg_v1.py:8-9` and carried into
`PREREG_n1_120deg_exact_ideal_v4.md`.

**Found by:** the `experiment-designer` gate audit of a successor spec, which flagged the direction of
the inequality; independently re-derived and re-witnessed here before being recorded.

**This does not retract the 120° law.** See §3 — the law has independent corroboration and the
failure probability of the stated argument is negligible. What is corrected is the **certification**,
and therefore the **grade**.

---

## 1. The claim as stated, and why it is one-sided

`run_n1_120deg_v1.py:8-9`:

> *"Reduction only RAISES gcd degree, so true `g` = **min** over `l`."*

The first clause is correct. Let `D = gcd(A,B)` over the characteristic-0 fraction field. `D | A` and
`D | B` imply `D̄ | Ā` and `D̄ | B̄`, hence

> **`deg gcd_{F_l}(Ā,B̄) ≥ deg D` for every `l`, hence `min_l g_l ≥ g_true`.**

**`min_l g_l` is therefore an UPPER bound on `g_true`, not an equality.** The consequences are
asymmetric, and in exactly the unhelpful direction for this result:

| computed | certifies |
|---|---|
| `min_l g_l = 0` | **`g_true = 0` exactly** (a null cell is exactly certified) |
| `min_l g_l = 2` | **only `g_true ≤ 2`** — consistent with `g_true ∈ {0,1,2}` |

The census's headline is the `= 2` direction. That direction is the uncertified one.

## 2. The inflation is real, and the witness is the gate's own pinned control

`run_n1_120deg_v1.py:155` builds PLANT-B from `α = 3+2i`, `β = 2+3i`, both of norm 13, with
**true `g₃ = 0`** (their ratio is `i`, not a cube root of unity — and see
`PREREG_jclass_120deg_discriminator_v1_DEVIATIONS.md` D6, where this plant turns out not to be
generic either). Reduced mod `l ≡ 1 mod 12`:

```
l with deg_gcd(L, L(ζ₃T)) > 0, l < 400 :   l = 13 → 2,   l = 37 → 2
```

**A true `g = 0` object reads `g = 2` after reduction, at two small `l`.** The inflation mechanism is
not hypothetical.

## 3. Why the RESULT is nonetheless almost certainly correct — stated so this is not over-read

Three independent mitigations, none of which is the stated argument:

1. **Five ells must inflate simultaneously.** The census takes `min` over 5 primes `l ≡ 1 mod 3n`,
   so every `l > 3n ≈ 3p`. Inflation requires a root collision modulo a prime above `l`, of
   probability `O(1/l)` per pair. Five independent ells ⇒ `O(l^{-5})`; the observed witnesses sit at
   `l = 13, 37`, far below any `l` the census uses.
2. **An independent route confirms `g ≥ 2` directly.** `ANALYSIS_n1_charpoly_collapse_v1.md` §3
   computes the four eigenvalues at 160-bit precision from `V₁, V₂` and reports
   `max` ratio-to-`ζ₃^k` `≤ 4.5e−44` at **every** `a ≠ 0`, `p = 43, 67, 127`. That exhibits the
   `ζ₃` ratio rather than bounding it, i.e. it is a **lower**-bound observation — the direction the
   census lacks. Scope: 3 small primes, numerical not exact.
3. **The `≤ 2` half is exact and is not nothing.** It rules out `g ∈ {3,4}` at all 2464 cells —
   the degenerate corners (`g₄ = 4` at `e₁ = 0`, `g₆ = 3` on `√p·{1,ζ₆,ζ₃,−1}`) are exactly excluded.

## 4. What changes

| item | before | after |
|---|---|---|
| census statistic, `g = 0` cells | `[PROVED-exact]` | **unchanged — exactly certified** |
| census statistic, `g = 2` cells (2464 of them) | `[PROVED-exact]`, 22 primes | **`[VERIFIED — exact upper bound `g ≤ 2`; `g = 2` at overwhelming but non-certifying odds over 5 ells]`** |
| the 120° law itself | `[PROVED-exact]` at 22 primes | **`[VERIFIED]`** — corroborated independently at eigenvalue level, `p = 43,67,127` (§3.2). Not retracted; regraded. |
| `run_n1_120deg_v1.py:8-9` wording | *"true `g` = min over `l`"* | **`min_l g_l ≥ g_true`** |

**Downstream:** every file that leans on *"`g = 2` at every cell of 22 primes `[PROVED-exact]`"* — the
Kronecker/Stickelberger route's premise, `ANALYSIS_n1_charpoly_collapse_v1.md`'s item 1,
`RESULT_120deg_anchor_from_mlaw_v1.md` §5 — inherits `[VERIFIED]` in place of `[PROVED-exact]`. The
*targets* those files identify are unaffected; only the strength of the premise moves.

## 5. The repair — ⚠ the ring named in the first revision of this file was WRONG

**RETRACTED (2026-07-31, same day):** this section first specified the certificate as computed in
`ℤ[x]/(Φ_n(x), Φ_k(x))`. **That ring is the ZERO RING.** Both generators are polynomials in the
*same* variable `x`, so the quotient demands one element be simultaneously a primitive `n`-th and a
primitive `k`-th root of unity. Computed: `Res(Φ_n, Φ_k) = 1` for every `(n,k)` in scope
(`n ∈ {26,31,58,79,127,146,163}`, `k ∈ {3,4,6}`), and `Res` lies in the ideal, so the ideal is `(1)`
and **every element is zero — including a non-vanishing resultant. The certificate would have passed
unconditionally and certified nothing.** Caught by the `experiment-designer` gate on the successor
spec that inherited it.

**The correct object.** `L* ∈ ℤ[ζ_N][T]` and `L*(ζ_kT) ∈ ℤ[ζ_N, ζ_k][T] = ℤ[ζ_M][T]` with
`M = lcm(N,k)`. Work in

> **`ℤ[ζ_M] = ℤ[y]/Φ_M(y)`, with `ζ_N := y^{M/N}` and `ζ_k := y^{M/k}` PINNED JOINTLY.**

The joint pinning is load-bearing whenever `d = gcd(N,k) > 1` — e.g. `N = 2n'`, `k = 4`, `d = 2` —
because then `ζ_N^{N/d} = ζ_k^{k/d}` is a genuine constraint and independent choices do not define an
embedding. `Φ_M` is irreducible over `ℚ`, so `ℤ[ζ_M]` is a **domain**: `Res_T = 0` ⟺ a common factor
over `ℚ(ζ_M)`, and `Res_T = 0` together with the first subresultant `= 0` ⟺ `deg gcd ≥ 2`.

**Also wrong in the first revision:** `reduce_phi_prime` (`audit_n1_vsign_v2_core.py:198`) reduces mod
`1 + x + … + x^{n−1}`, which is `Φ_n` **only for `n` prime** (`Φ₂₆ = 1 − x + x² − … + x¹²`). It cannot
be reused where `N` is composite — i.e. on exactly the cofactor-2 arms of the successor spec.
`polymul_mod_cyc` (189) is fine; the reduction step must be rewritten for general `Φ_M`.

**And the conjunction must be stated:** `Res = 0 ∧ S₁ = 0` gives `g ≥ 2`; the multi-modular
`min_l g_l` gives `g ≤ 2`. **Neither alone yields `g = 2` — the two halves must be conjoined.** The
first revision of this file supplied only the lower-bound half and did not say so.

**Minimum acceptable interim** (if the certificate is not computed): report the per-cell spread
`max_l g_l − min_l g_l` alongside every `g`, so a reader can see whether the ells agreed or whether
the min was carried by one.

## 6. Error class

A correct lemma (*"reduction raises gcd degree"*) stated as an equivalence, in a script docstring, and
inherited unexamined by the prereg that the gate signed off. It is the **subtle analytical-closure
shape named in `btc_puzzle_investigation/CLAUDE.md`** — a true fact applied one quantifier too
generously — pointed at a *positive* claim rather than at a closure. Neither the gate nor five
subsequent files caught it; it was found only when the statistic was ported to a new `k`, where the
same reasoning had to be re-justified from scratch.
