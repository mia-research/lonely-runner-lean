# NOTE: GLV-orbit carry conservation, the exact carry law, and the complete public orbit-invariant statistics (v1)

**Date:** 2026-08-16
**Grade:** `[PROVED + EXACT]`
**Builds on:** `NOTE_core_gate_exact_carry_region_v1.md` (the hexagon zero-carry region).
**Script:** `glv_orbit_carry_conservation_v1.py` (exact integer path; T1 100k, T2/T3 20k orbits; passport + 82-key check).

---

## 1. Theorem (closed form and exact law of the carry)

In b-coordinates (basis b₁ = π, b₂ = ωπ), the element c·π has b-coordinates exactly
(c₀, c₁), and z(βX) has b-coordinates (−v, u−v) − (c₀, c₁). Since −v ∈ (−½, ½]
automatically, **c₀ = 0 always**, and u−v ∈ (−1, 1) gives

$$c(X) \;=\; \bigl(0,\ \lfloor u - v + \tfrac12 \rfloor\bigr) \;\in\; \{0,\ \omega,\ -\omega\}.$$

The carry is the integer overflow of the single linear form u−v, and is always 0 or a
unit. Exact law for uniform X: **Pr[c = 0] = 3/4, Pr[c = ±ω] = 1/8 each** (hexagon
3/4; two corner triangles 1/8 each). Empirical (100k): 0.749170 / 0.125660 / 0.125170.

## 2. Theorem (orbit conservation law and trichotomy)

Telescoping z(β³X) = z(X) through z(β^{k+1}X) = ω·z(β^kX) − c(β^kX)·π:

$$\omega^2\,c(X) \;+\; \omega\,c(\beta X) \;+\; c(\beta^2 X) \;=\; 0 \quad \text{in } \mathbb{Z}[\omega].$$

With each carry in {0, ±ω}, writing c_i = ε_i ω (ε_i ∈ {−1,0,1}) forces ε₁ = ε₂ = ε₃.
**Trichotomy:** the carry triple around any GLV orbit is one of
(0,0,0), (ω,ω,ω), (−ω,−ω,−ω) — the carry is a GLV-orbit invariant, and the two corner
triangles (equivalently the three carry classes) are orbit-invariant sets.
Verified: 20,000 random orbits + all 82 solved keys + all 6 exposed puzzles.

## 3. Theorem (norm orbit-invariance and exact shift)

- c = 0 ⟹ z(βX) = ω·z(X) and z(β²X) = ω²·z(X), so **s(βX) = s(β²X) = s(X) exactly**
  — the lift norm is an orbit invariant on the 3/4-locus.
- c = εω ⟹ z(βX) = ω(z − επ), and by polarization of the norm:

$$N(z(\beta X)) \;=\; N(z) + p - \varepsilon\,\mathrm{Tr}(z\,\bar\pi), \qquad
s(\beta X) \;=\; s(X) + 1 - \varepsilon\,\mathrm{Tr}(z\bar\pi)/p .$$

Both directions verified exactly (20k samples; real-key instances below).

## 4. Corollary (complete exact statistics of the public orbit invariants)

The public orbit invariants are the label (j, s_label) and the carry c.
- negation label: exactly uniform (negation pairs (x, ±y); no y = 0 or y = p/2 points);
- orbit index j: exactly uniform (p ≡ 7 mod 9, φ cycles the χ₃ classes — RESEARCH.md 2026-08-16 item 6);
- carry: exactly 3/4, 1/8, 1/8 (Theorem 1);
- **label ⊥ carry, provably**: the carry classes are orbit-invariant (Theorem 2) while
  the orbit cycles the idx classes transitively, so each carry class contains exactly
  equal idx counts; the carry depends on x only, the negation label on the y-branch.

Hence the joint law of (j, s_label, c) over uniform keys is exactly the product:
6 × {3/4, 1/8, 1/8} — 18 classes, fully exact, nothing measured.

## 5. Structural remark (why this geometry — the ramified prime)

The strip direction governing the carry is b₁ − b₂ = (1−ω)π, and 1−ω is the unique
ramified prime of Z[ω] (3 = −ω²(1−ω)²). The hexagon is the fundamental square clipped
by the two translates orthogonal (Eisenstein metric) to the ramified direction. The
"3-flavored" constants throughout this programme — automorphism order 3; threshold
3/16; tangent point (1/4, −1/4) along direction (1,−1); n ≡ 1 (mod 3); λ ≡ −1 (mod 3);
exact χ₃ balance iff p ≢ 1 (mod 9) — are all shadows of the prime 3 in the CM order:
split at p (β ∈ F_p), ramified in the lattice geometry (this note), and governing the
residue arithmetic of n and λ.

## 6. Public-geometry passport of the exposed PUBKEY_ONLY puzzles

| pz | idx | j | y<p/2 | s | gate s<3/16 | c(X)=c(βX)=c(β²X) | s(βX)=s(X) |
|---|---|---|---|---|---|---|---|
| 135 | 1 | 2 | T | 0.058933 | PASS | 0 | T |
| 140 | 0 | 0 | F | 0.019792 | PASS | 0 | T |
| 145 | 0 | 0 | T | 0.403487 | FAIL | −ω (all three) | F (shifted, per Thm 3) |
| 150 | 1 | 2 | F | 0.160282 | PASS | 0 | T |
| 155 | 2 | 1 | F | 0.141498 | PASS | 0 | T |
| 160 | 2 | 1 | F | 0.113463 | PASS | 0 | T |

3/4 law on the 82 verified solved keys: 65/82 = 79.3% carry-zero (expected 75.0%,
binomial sd 4.8% — within 1 sd); orbit conservation holds on all 82. P145 remains the
sole exposed puzzle with ε ≠ 0, and it exercises both branches of Theorem 3.

## 7. Demarcation

Everything above is orbit-level public structure: a now-complete exact description of
the public geometry (invariants, conservation law, exact joint law, independence). No
scalar-side information is produced, derivable, or claimed — the boundary of
AUDIT_d2_bridge_mod6_reduction_v1.md §6 stands.

## 8. Negative consequences (what D cannot be — exclusion ledger)

The positive theorems above convert into PROVABLE EXCLUSIONS:

**(a) Aut₆-relation obstruction.** The carry is constant on GLV orbits (Theorem 2) and
negation-invariant (c is a function of x alone; ±P share x). Hence **equal carry is a
necessary condition for any key relation d_a ≡ ±λ^k d_b (mod n)**. Concrete (82 solved
keys split 65 / 8 / 9 over carries 0 / +ω / −ω; puzzles per §6):
- **d₁₄₅ ≢ ±λ^k·d_solved for 73 of the 82 solved keys, by carry mismatch alone** —
  no conjugate points computed. The definitive test (x_a ≟ β^k x_b, k = 0,1,2 — the
  full Aut₆ test since negation preserves x) excludes the remaining 9 (and everything
  else): no solved key is an Aut₆-relative of any exposed puzzle.
- The five carry-0 puzzles exclude 17 solved keys a priori; all excluded definitively.
- No puzzle–puzzle Aut₆ relations exist.
Any future artifact claiming "target = ±λ^k × (known key)" for a carry-mismatched pair
is dead on arrival.

**(b) Fiber exclusion: indexical, not operational.** The public passport pins d to a
fiber of (label, carry): measure 1/6 × 3/4 = **1/8** for the carry-0 puzzles (87.5% of
the keyspace provably not d) and 1/6 × 1/8 = **1/48** for P145 (97.9% provably not d).
This exclusion is INDEXICAL: the per-candidate membership test costs exactly a full
candidate evaluation (compute x([d']G) and reduce). Zero work reduction. **The DLP is
precisely the barrier between indexical and operational exclusion** — every construction
in the audited Downloads stream is a failed attempt at this conversion through the word
"carry"; the closure of this layer proves the conversion cannot occur within it.

**(c) Information ceiling of the orbit-geometry layer.** With the exact joint law
(§4) and the conservation law (§2), the total discrete indexical content of ALL
orbit-level public geometry is capped at log₂6 (label) + H(3/4, 1/8, 1/8) ≈ 2.585 +
1.061 = **3.65 bits indexical, 0 bits operational**. Any claim to extract more from
orbit geometry is impossible by no-go (closed layer), not merely untested: the joint
carry channel carries log₂3, not 3·log₂3; s carries no orbit-discriminating
information for 75% of keys; label and carry are provably independent.

**(d) Methodological rule for future probes.** GLV conjugates are NOT three
independent samples: for c = 0 keys the lift statistics of β^k x are IDENTICAL
(s-orbit invariance); for c ≠ 0 they differ by the exact shift of Theorem 3. Any
experiment design that orbit-averages lift statistics claiming 3× power is
mis-specified; the exact correlation is now known and must be used.
