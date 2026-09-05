# Findings v13: a PROVED structural theorem at the S₃ index-calculus level (general p, covers secp)

**Date:** 2026-07-16 · the "ways to determine proof" branch. Script:
`summation_poly_structure_v1.py` + the symbolic discriminant. First result of the
investigation that is a **proof general in p** (covers secp), not a small-p empirical null.

## The theorem (proved), and its exact scope

For `E: y²=x³+7` over `F_p`, the Semaev 3rd summation polynomial `S₃(x₁,x₂,x₃)` (verified
numerically: 0/53138 nonzero on real collinear triples — not cited from memory):

1. **`S₃` is irreducible over ℚ.** [PROVED — exact factorization] No global factorization lever.
2. **`S₃` has exact β-covariance of weight 1:** `S₃(ωx₁,ωx₂,ωx₃) = ω·S₃` (`ω³=1`). [PROVED —
   each monomial scales by ω³ᵏ⁺¹; sample-verified over F_p]. The **only** extra algebraic
   structure of the CM curve, and it is exactly the automorphism (`Aut(E)=μ₆`). The non-CM
   control `y²=x³+x+1` has no such weight (mixed) — confirming this is the CM signature.
3. **The fixed-target relation curve** `C_t: S₃(x₁,x₂,t)=0` (the `(2,2)` curve whose F-points
   are the 3-point relations for target x-coord `t`) has branch discriminant
   > **`Δ(t) = −86704128·(t³+7)⁴`**  [PROVED — exact symbolic discriminant].
   So `C_t` is singular **iff** `t³+7=0` **iff** `(t,0)` is a **2-torsion point**.
4. **Prime order kills it.** `#E` prime ⇒ odd ⇒ no 2-torsion ⇒ `t³+7=0` has no root in `F_p`
   ⇒ `Δ(t)≠0` for **every** `t∈F_p` ⇒ **`C_t` is smooth genus 1 for every target.** [PROVED,
   general p]. Verified: p=907, 2089 (prime order) have 0 degenerate targets, and the numeric
   run showed all `C_t` smooth (0 singular points, Hasse-band point counts).

**secp256k1 has prime order**, so this applies directly: at secp's actual `p`, every S₃
3-point relation curve is smooth genus 1.

## What it proves — and what it does NOT (the discipline)

**Proved (general p, incl. secp):** at the **S₃ (3-point, m=2) level**, the relation curve is
smooth genus 1 for *every* target — hence **non-parametrizable**, so there is **no
index-calculus lever from fixed-target curve geometry**, and **no special "easy target"**
(the only degenerate locus, 2-torsion, is empty in prime order). The CM structure contributes
**only** the β-covariance = the bounded automorphism factor (matching v9's measured ~1.5×,
`≤|Aut|`). This is the rigorous "**why** it's hard here" at this level: prime-field + prime
order ⇒ uniformly genus-1 relation curves, no rational structure to enumerate, no CM lever
beyond the automorphism.

**NOT proved (honest scope — this is a fence result, not an ECDLP wall):**
- Only the **S₃ / m=2** rung. Higher summation polynomials `S₄, S₅, …` (`m≥3` decompositions)
  are a **separate, heavier** question; this says nothing about their genus/first-fall-degree.
  That is the remaining frontier (v10/v11 measured yields there = generic, but not proved).
- "Smooth genus-1 relation curve" ⇒ no *parametrization* lever; it does **not** prove the
  decomposition problem has no other structure, and does **not** prove ECDLP is hard.
- It is a statement about *this* curve family (`j=0`, `b=7`) and the standard `S₃`.

## Why this matters for the programme

Every prior result this session was a scoped empirical null at `p ≤ 10⁵`. This one is a
**proof that holds at secp's `p`**, and it is a *positive* structural statement (an exact
discriminant, an exact irreducibility, an exact covariance weight) rather than a null. It
demonstrates the "determine proof" method works: take the recurring empirical pattern
(v9/v10: generic decomposition, bounded β-lever) down to the summation polynomial's algebraic
geometry, where it becomes a theorem — irreducible `S₃`, `Δ(t)=c(t³+7)⁴`, genus-1 for all `t`
under prime order. **We proved a specific wall (no S₃ fixed-target lever, general p) without
calling "where it gets hard" the wall** — the scope is pinned to S₃, and S₄⁺ is left open.

## Next, if pushed

The natural continuation of the *proof* branch: compute the analogous discriminant / first-fall
structure for **`S₄`** (the 3-point decomposition, `m=3`). If `S₄`'s decomposition variety is
likewise uniformly non-degenerate for prime order, the "no index-calculus lever" statement
climbs a rung — and each rung proved is a real, general-p wall, not an empirical null. That is
the honest way to keep converting fence into proven wall, one summation polynomial at a time.
