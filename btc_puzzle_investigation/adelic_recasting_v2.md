# Adelic recasting of the φ(n)-framework — v2 (2026-07-11)

**Supersedes `adelic_recasting_v1.md`** (v1 frozen). v2 corrects one imprecision
found in the 2026-07-11 spectral check (`secp256k1_arithmetic/SPECTRAL_CHECK_v1.md`):
v1 placed μ₆ on the **archimedean** S¹, but the μ₆ that decorates the Hecke
character ψ is the **finite** ray-class character χ (now *derived*, not fit —
`thread_A_reciprocity_v2.py`). The two are Pontryagin-**dual**, not equal. The
correction does not break the recasting — it **pins which circle μ₆ lives on** and
explains why the conductor cannot be recast away.

Unchanged from v1 and re-verified: the circle/line obstruction is real
(deficiency indices confirmed, `radial_selfadjointness.md`); `C_ℚ = ℝ_{>0}×Ẑ^*`;
`ℂ^* = ℝ_{>0}×S¹` for K=ℚ(√−3); `a_ℓ = 2Re(u·π)`, `u∈μ₆`.

---

## 0. The obstruction (unchanged, correct)

`B` = D_φ = span{e^{±iy}} (arithmetic averaging) wants the compact **circle**;
`C` = Mellin probes `x^s` (the zeros) want the archimedean **line**. On the
half-line ℝ_{>0}, Ĥ=πA² has deficiency indices (1,1); no boundary condition
merges two different spaces. **Resolution: they are different *places* of the same
idele class group** — Connes' adele class space.

## 1. C_ℚ = ℝ_{>0} × Ẑ^* (unchanged, correct)

- `ℝ_{>0}` (archimedean scaling) = the LINE = home of Ĥ and the zeros.
- `Ẑ^* = ∏_p ℤ_p^*` (finite units) = the CIRCLE(S) = home of the P_n averaging.

Two direct factors of one locally compact group. The framework split one object
across places; on C_ℚ the halves are reunited.

## 2. K = ℚ(√−3): TWO circles, not one — the v2 correction

v1 said: K's complex place gives `ℂ^* = ℝ_{>0} × S¹`, so "line and circle sit at
one place, and μ₆ ⊂ S¹ carries ψ's decoration; no finite places needed." **The
first clause is right; the rest conflates two distinct circles.** There are two:

| circle | where | what it carries | nature |
|---|---|---|---|
| **archimedean S¹** | complex place, `ℂ^* = ℝ_{>0}×S¹` | the ∞-type angle `e^{iθ}` of `ψ_∞(z)=z` | **continuous** |
| **finite ray-class S¹** | non-arch. ideles `Ẑ_K^*`, mod conductor `𝔣` | the sextic character `χ = −(28/π)₆⁻¹` | **discrete, μ₆-valued** |

`ψ = ψ_∞ · ψ_fin`: `ψ_∞` lives on the archimedean S¹ (continuous angle),
`ψ_fin = χ` lives on the finite ray-class circle (discrete μ₆). The global units
`ℤ[ω]^* = μ₆` embed in the archimedean S¹ **but are quotiented out** in
`C_K = 𝔸_K^*/K^*` — they are not a subgroup of the class group. Triviality of ψ on
global units *links* the two circles (`ψ_∞(u)ψ_fin(u)=1` for `u∈μ₆`) but does not
identify them; they are **Pontryagin-dual** roles of μ₆.

**Concrete proof they are different circles** (`SPECTRAL_CHECK_v1.md`): the
256-bit Frobenius has archimedean ∞-type angle `θ_p = arccos(t/2√p) = 50.55°` —
**generic, not a multiple of 60°** (a continuous point of the archimedean S¹) —
while χ takes **discrete μ₆ values** (order exactly 6). A continuous generic angle
cannot equal a discrete order-6 character.

**So μ₆ (the survival-law sextic core) is the FINITE ray-class character**, now
pinned by the derived `χ = −(4·7/π)₆⁻¹`, not the archimedean angle.

## 3. Consequence: the conductor cannot be recast away

v1's stronger claim — "the complex place carries both line and circle, so B and C
need no finite places to be bridged" — **overreaches for the zeros.** The conductor
`𝔣 = (2²)(√−3)²(7)`, `N = 21168`, lives at the **finite places 2, 3, 7**, and it
sets the zero *density*:

```
mean spacing of zeros = π / log(√N · γ̄ / 2π),   N = 21168 (finite-place conductor)
```

verified on the computed zeros (`secp256k1_arithmetic`, thread E). The archimedean
`ℂ^*` does not carry `N`; the `log N` in the spectral wall
`E(σ) ≥ (4/π²)κ(L)σ²log N` is exactly the finite-place data. **The CM complex
place is a cleaner home for the line + ∞-type angle, but the finite places remain
essential** — the survival μ₆ and the conductor both live there.

## 4. The corrected dictionary

| φ(n)-framework | adelic object (K = ℚ(√−3)) |
|---|---|
| Ĥ=πA² on L²(ℝ_{>0}) | archimedean scaling ℝ_{>0} (LINE, zeros) |
| ∞-type of ψ, angle `e^{iθ}` | archimedean **S¹** (continuous) |
| P_n averaging / survival | finite units `Ẑ_K^*`, ray class mod 𝔣 |
| **μ₆ survival core = χ** | **finite ray-class character** `−(28/π)₆⁻¹` (derived) |
| conductor / `log N` in the wall | ramification at finite places 2, 3, 7 |
| zeros of L(ψ,s) | spectrum of scaling on `L²(𝔸_K^*/K^*)`, ψ-isotypic |

## 5. Scope (unchanged, and tightened)

Still a recasting + structural observation, **not** a proof of RH/GRH. What v2
fixes: μ₆ is the *finite* ray-class character (pinned by the derived χ), the two
circles (archimedean ∞-type vs finite ray-class) are dual not equal, and the
conductor at 2,3,7 is essential to the zeros and cannot be absorbed into the
archimedean place. The honest open problem is unchanged: realize the zeros of
L(ψ,s) as the spectrum of the scaling operator on `L²(𝔸_K^*/K^*)` in the
ψ-isotypic sector — Connes' program, positivity open. See
`secp256k1_arithmetic/SPECTRAL_REALIZATION_v1.md` for the full proven/open map.

**v1 → v2 change:** the one substantive correction is §2–§3 (which circle μ₆ is,
and that the conductor stays finite). v1's §4b twisted-circle numerics stand as a
consistency-model result about the *archimedean* completion S¹, but that S¹ is the
∞-type circle, **not** where χ/μ₆ lives — so "μ₆ picks the distinguished
completions" is a modeling choice on the archimedean circle, distinct from the
finite μ₆ character. Keep the numerics; drop the identification.
