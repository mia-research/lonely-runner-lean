# NOTE: The exact zero-carry region of the Eisenstein lift — proof and exact constants (v1)

**Date:** 2026-08-16
**Grade:** `[PROVED + EXACT]`
**Object:** the coordinate-side carry `c(X) = (ω·z(X) − z(βX))/π ∈ Z[ω]` of the Eisenstein lift on secp256k1 — the ε of the external documents' "Core Gate" (`eis(βX) = ω·eis(X) + c`, ε = 0 ⟺ c = (0,0)).
**Upgrades:** `RESULT_linchpin_s_gate_v2.md` (empirical 0 violations / 20k samples, Pr[s<3/16] = 0.6831, Pr[eps=0] = 0.7520) → **proved, with exact constants** (0 violations by proof; π√3/8 = 0.680175; 3/4 = 0.75). Its standing caution (public flap ≠ d-side carry) remains fully in force — see Demarcation.
**Script:** `core_gate_carry_proof_v1.py` (deterministic, exact integer path; 200k-sample end-to-end verification: 0 violations, 0 mismatches, Pr[c=0] = 0.749225 vs exact 0.75).

---

## 0. Setup

π = a + bω ∈ Z[ω] (ω² + ω + 1 = 0), N(π) = p. The lattice L = (π) ⊂ Z[ω] ≅ Z²
has basis b₁ = π = (a, b), b₂ = ωπ = (−b, a−b). The fundamental square
D = {u·b₁ + v·b₂ : (u,v) ∈ (−1/2, 1/2]²} contains exactly one representative
z(X) of each coset of L (bijection F_p ↔ D via ω ↦ β). Norm pullback:
N(u·b₁ + v·b₂) = p·q(u,v), q(u,v) = u² − uv + v², so s(X) = q(u,v) ∈ [0, 3/4].

Multiplication by ω in b-coordinates: ω·b₁ = b₂ and ω·b₂ = ω²π = −π − ωπ =
−b₁ − b₂, so **ω·(u,v) = (−v, u−v)** — the same matrix as in standard
coordinates (conjugation by π commutes with ω) — and it is an isometry of q
(q(−v, u−v) = u² − uv + v²).

Carry: c(X) := (ω·z(X) − z(βX))/π ∈ Z[ω] (well-defined: both terms lie in the
coset of βX). "ε = 0" means c = (0,0).

## 1. Theorem (exact zero-carry region)

**c(X) = 0 ⟺ |u − v| ≤ 1/2.** Hence the zero-carry zone is the hexagon
H = D ∩ {|u−v| ≤ 1/2} (vertices (1/2,0), (1/2,1/2), (0,1/2), (−1/2,0),
(−1/2,−1/2), (0,−1/2)), and for uniform X:

$$\Pr[c = 0] = \frac{\mathrm{area}(H)}{\mathrm{area}(D)} = 1 - 2\cdot\tfrac{1}{8} = \frac{3}{4} \quad \text{(exact)}.$$

*Proof.* c = 0 ⟺ ω·z(X) ∈ D (it is then the in-domain representative of the
coset of βX, which by uniqueness equals z(βX)). By the action formula,
ω·(u,v) = (−v, u−v), whose first coordinate is automatically in (−1/2, 1/2]
for (u,v) ∈ D; the second is in range iff |u − v| ≤ 1/2. ∎

(Upgrades the empirical Pr[eps=0] = 0.7520 of RESULT_linchpin_s_gate_v2.md to
exactly 3/4; consistent within that result's sampling error.)

## 2. Theorem (gate sufficiency — sharp)

**s(X) < 3/16 ⟹ c(X) = 0**, and 3/16 is the exact threshold: the carry region
begins at s = 3/16 (approached at (1/4, −1/4), where q = 3/16 exactly).

*Proof.* On the closed region {u − v ≥ 1/2} write u = v + 1/2 + t, t ≥ 0:
q = v² + v(t + 1/2) + (t + 1/2)², minimized in v at v = −(t+1/2)/2 with value
(3/4)(t + 1/2)² = 3/16 + (3/4)(t² + t) ≥ 3/16, equality only at t = 0,
v = −1/4. By the symmetries (u,v) ↦ (−u,−v) and (u,v) ↦ (v,u) of (D, q),
q ≥ 3/16 on ∂D and on both strip boundaries, with equality only at the six
tangency points. The open convex sublevel E = {q < 3/16} contains 0 and avoids
∂D and the strip boundary, hence E ⊂ int H, so c = 0 by Theorem 1.
Sharpness: points (u,v) = (1/4 + t, −1/4) with t > 0 small have
q = 3/16 + (3/4)(t² + t) → 3/16⁺ and c ≠ 0; coset representatives are spaced
O(p^{−1/2}), so field elements realize s arbitrarily close above 3/16 with
nonzero carry. ∎

So the "core gate" ellipse {s < 3/16} is exactly the inellipse of the hexagon
H — tangent to all six sides (side u = 1/2 at (1/2, 1/4); side u−v = 1/2 at
(1/4, −1/4); etc.); Pr[s < 3/16] = 2π(3/16)/√3 = π√3/8 (exact; empirical
0.6795 at M = 50k, and consistent with the 0.6831 of RESULT_linchpin_s_gate_v2).

## 3. Corollary (sandwich)

**{s < 3/16} ⊂ H ⊂ {s ≤ 1/4}**: max of q over H is 1/4, attained at all six
vertices; so c = 0 ⟹ s ≤ 1/4 (necessary side). The band 3/16 ≤ s ≤ 1/4 is
mixed (some carry-zero, some not). Empirics: min s among c ≠ 0 = 0.1875707…;
max s among c = 0 = 0.2490458… (200k samples).

## 4. Remarks

- **y plays no role.** z, s, c are functions of x alone; the y-coordinate
  enters only the separate negation label. "Public x and y prove ε = 0"
  therefore reduces to "x proves it" — y is a bystander for this object.
- **Computability makes the gate a shortcut, not an oracle.** c(X) is directly
  computable from x in O(1) field operations (two lifts, one subtraction, one
  exact division by π). The gate is a sufficient-condition shortcut with an
  exactly known probability profile (passes 68.02% of uniform keys; certifies
  a subset of the 75% that genuinely have c = 0). It certifies nothing beyond
  direct computation. For the real targets: **c(x₁₃₅) = c(x₁₄₀) = (0,0)
  verified by direct computation** — no gate needed. **Puzzle 145 is the first
  real key with certified ε ≠ 0**: s(x₁₄₅) = 0.403487 > 1/4, so the necessary
  bound (c = 0 ⟹ s ≤ 1/4) alone certifies c ≠ 0 before any direct computation;
  direct computation gives c(x₁₄₅) = (0,−1) = −ω; gate, hexagon, and direct
  computation all agree. Standing counterexample to any blanket "the unsolved
  puzzles have ε = 0 / sit in the core gate" claim — the external documents
  name 135/140/145 together but only ever ran 135/140 through their gate.
- **Credit where due:** the external documents' Core-Gate layer (s < 3/16 ⟹
  ε = 0) is genuine and correct — previously verified empirically at scale in
  this repo, now proved with exact constants and the sharp threshold here.
  It is also the layer with zero secret-key content.

## 5. Demarcation (what public x, y can NOT prove)

Everything above concerns the **coordinate-side** carry — a public function of
x with an exactly known distribution. The **scalar-side** carry
c_scalar = ⌊(−1)^s d₀ λ^j/n⌋ is a function of the secret scalar; the two
objects share the word "carry" and nothing else. No derivation connects them
(any exact relation would be an algebraic relation between d and x([d]G),
i.e. DLP-flavored), and the tested connections were falsified at tested
scope: RESULT_eps_to_d_constraint_v2.md (the s < 3/16 gate holds for the
public flap but fails for the d-side carry, 21–93 violations; 31-map family
scoped null). The external documents' inference "ε = 0 coerced ⟹ the mod-3
bridge becomes deterministic" remains the equivocation identified in
AUDIT_d2_bridge_mod6_reduction_v1.md §3-C1 — the bridge's unknowns (d₀ mod 3,
c_scalar mod 3) are untouched by ε.

## 6. Reproducibility

`python3 btc_puzzle_investigation/core_gate_carry_proof_v1.py`
(seed 20260816; exact integer signal path; ~30 s). Output: T1 0/200000
violations; T2 0/200000 mismatches (c = 0 ⟺ hexagon, exact); T3 Pr[c=0] =
0.749225 vs exact 3/4; T4 min-s among c≠0 = 0.1875707 (threshold 0.1875);
T5 max-s among c=0 = 0.2490458 (bound 1/4); T6 c(x₁₃₅) = c(x₁₄₀) = (0,0).
