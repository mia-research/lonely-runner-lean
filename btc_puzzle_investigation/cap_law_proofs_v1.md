# Two proofs — Cap Law ω-matrix, and σ's μ₃-invariance (promoting VERIFIED → PROVED)

**Date:** 2026-07-16. Setup: p ≡ 1 mod 3; `L = (π_p) ⊂ ℤ[ω]` the prime ideal above p (a rank-2
ℤ-lattice, index p in ℤ[ω]); `𝔽_p ≅ ℤ[ω]/L`. `eis(x)` = the representative of `x ∈ ℤ[ω]/L` in
the fundamental domain `P = {u R₁ + v R₂ : u,v ∈ [−½,½)}` for a **reduced** ℤ-basis `{R₁,R₂}` of
`L`. `β = (ω mod L) ∈ 𝔽_p` (a cube root of unity), and `eis(βx) = ω·eis(x)` reduced into `P`.

---

## Theorem A (Cap Law) — PROVED

**Claim.** In a reduced basis with `⟨R₁,R₂⟩ = −p/2` (the 120° orientation), multiplication by ω
on `L` is the *fixed integer matrix* `M = [[0,−1],[1,−1]]`, independent of p, and
> `ε(x) ≠ 0  (flap)  ⟺  |u − v| > ½`,  where `eis(x) = uR₁ + vR₂`.
(The other orientation `⟨R₁,R₂⟩=+p/2` gives `|u+v|>½` via `R₂ ↦ −R₂`.)

**Proof.**
1. *ω is an order-3 lattice automorphism with basis-independent invariants.* `ω ∈ ℤ[ω]^×` and
   `L=(π_p)` is an **ideal**, so `ωL = L`: multiplication-by-ω is a ℤ-linear automorphism of `L`,
   with `ω³ = 1`. Its trace and determinant are basis-independent and equal the field trace/norm:
   `det(×ω) = N_{ℚ(ω)/ℚ}(ω) = 1`, `tr(×ω) = Tr_{ℚ(ω)/ℚ}(ω) = ω + ω² = −1`. Hence *in every basis*
   the matrix `M` of `×ω` satisfies `M² + M + I = 0` (its char. poly. is `t²+t+1`).
2. *`L` is hexagonal, so the reduced basis is two shortest vectors at 120°.* `L = π_p·ℤ[ω]` is the
   image of the hexagonal lattice `ℤ[ω]` under the similarity `×π_p` (rotation+scaling by `√p`),
   hence hexagonal. Its shortest vectors have norm `p` and are `{±π_p, ±ωπ_p, ±ω²π_p}` (the six
   units × π_p), spaced 60°. A Gauss-reduced basis picks two of them; take `R₁, R₂` with
   `⟨R₁,R₂⟩ = |R₁||R₂|cos120° = −p/2` (WLOG; the other sign is `R₂↦−R₂`).
3. *The matrix is forced.* With `R₁` at 0° and `R₂` at 120°, the six shortest vectors sit at
   `R₁(0°), R₁+R₂(60°), R₂(120°), −R₁(180°), −(R₁+R₂)(240°), −R₂(300°)` (note `|R₁+R₂|² =
   2p+2⟨R₁,R₂⟩ = p`, so `R₁+R₂` is also shortest; `|R₁−R₂|² = 3p` is the *long* diagonal). Rotation
   by 120° (=`×ω`) sends each shortest vector two steps: `R₁ ↦ R₂`, `R₂ ↦ −(R₁+R₂)`. So in the
   basis `{R₁,R₂}`, `M = [[0,−1],[1,−1]]` (columns = `ωR₁, ωR₂`). Check: `tr M = −1`, `det M = 1`,
   `M²+M+I=0`. ✓ (consistent with step 1, and now with explicit entries).
4. *The flap condition.* `ε(x)=0 ⟺ ω²·eis(x) ∈ P`. Now `M² = −M−I = [[−1,1],[−1,0]]`, so
   `ω²·(u,v)ᵀ = (−u+v, −u)`. Both coordinates lie in `[−½,½)` iff `|−u| ≤ ½` (automatic, since
   `u∈[−½,½)`) **and** `|v−u| ≤ ½`. Hence `ε(x)=0 ⟺ |u−v| ≤ ½`, i.e. `flap ⟺ |u−v| > ½`. ∎

**Corollary.** The core/flap densities and the shape constants (¾, ⅛, ⅛, and the Int.1 values
½, ¾, 33, and E[N]/p = 1/6) are exact areas/moments of this fixed hexagonal geometry, hence
θ-independent and carrying no p-dependent (secp) arithmetic. `[PROVED]`

---

## Theorem B (σ is μ₃-invariant) — PROVED

**Claim.** `σ(βx) = σ(x)` for all x (the flap sign is constant on GLV/μ₃ orbits).

**Proof.** Let `R : P → P` be `z ↦ (ω·z mod L)` (rotate by 120°, reduce into `P`); `R` is a
bijection with `R³ = id` (since `ω³=1` in `ℤ[ω]/L`), and `eis(βx) = R(eis(x))`.
1. *The core is R-invariant.* Define `core = P ∩ ωP ∩ ω²P` (the μ₃-symmetric center). `R`
   corresponds to cyclically permuting `P, ωP, ω²P`, so it fixes their common intersection setwise:
   `R(core) = core`, hence `R(flap) = flap`, where `flap = P∖core`. *(Lemma C below verifies the
   ε-flap `{|u−v|>½}` equals this `P∖core`.)*
2. *The flap has exactly two connected components (the ± caps).* `flap = {z∈P : |u−v|>½}` splits
   into `u−v > ½` and `u−v < −½` — two disjoint convex regions (the two triangular caps at the
   ends of the long diagonal `R₁−R₂`). `σ = sign(u−v)` is constant `+1` / `−1` on them.
3. *R fixes each cap.* `R` permutes the 2 connected components of `flap`. `R` has order 3. The
   only order-3 element of the symmetric group `S₂` on 2 objects is the identity (`3 ∤ 2`), so `R`
   fixes each cap setwise.
4. *Conclusion.* `σ` is constant on each cap and `R` maps each cap to itself, so `σ(R(z)) = σ(z)`,
   i.e. `σ(βx) = σ(x)`. ∎

Combined with `σ(−x) = −σ(x)` (from `eis(−x) = −eis(x) ⇒ (u,v)↦(−u,−v) ⇒ u−v ↦ −(u−v)`), σ is
exactly the **μ₂-isotypic (sign) part of the μ₆ = Aut(E) action**. `[PROVED]`

**Lemma C — now PROVED (was: verify numerically).** `flap = {|u−v|>½} = P ∖ (P∩ωP∩ω²P)`.
*Proof.* For `z=uR₁+vR₂ ∈ P` (so `|u|,|v|≤½`), using `M=[[0,−1],[1,−1]]` (Thm A):
- `z∈ω²P ⟺ ωz∈P`; `ωz` has coeffs `M(u,v)ᵀ=(−v, u−v)`, in `P ⟺ |−v|≤½ (auto) ∧ |u−v|≤½`.
- `z∈ωP ⟺ ω²z∈P`; `ω²z` has coeffs `M²(u,v)ᵀ=(−u+v, −u)`, in `P ⟺ |v−u|≤½ ∧ |u|≤½ (auto)`.

Both conditions are **`|u−v|≤½`**, so `P∩ωP∩ω²P = {z∈P : |u−v|≤½}` and its complement is
`{|u−v|>½}` = the flap. ∎  **⇒ Theorem B is now UNCONDITIONAL (no numerical dependence).**

---

## Note (critical exponent, `masked_structure_findings_v19`) — a CORRECTION, not a promotion
Porter–Thomas makes the aligned-leak numerator exact: `Corr(a₀) = √(πn)/2` `[DERIVED + VERIFIED ~2%]`.
But the leak *fraction* `Corr/‖F‖_∞` is ~0.29 and **roughly FLAT** over n=547→7069 (13×), NOT the
`1/√log p` decay I had claimed — the data lean *shallower* (`|F|` is sub-Rayleigh, `E[I²]≈1.82<2`).
The exponent is **UNRESOLVED** (log too slow to pin); prior "1/√log p" is DOWNGRADED — it decays
too fast for the data. Crypto conclusion unchanged (aligned readout ⇒ DLP either way).
