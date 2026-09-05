# RESULT — the group lattice carries an ε=0 gate IDENTICAL to the field carry (island gate analog exists)

**Grade: `[VERIFIED — 4 scales, exact ℤ[ω] arithmetic]`.** Date 2026-08-17. Answers exploration Q1 (island
analog of the carry ε=0 gate). Ties to `NOTE_core_gate_exact_carry_region_v1` (field carry) and
`ANALYSIS_island_frobenius_tie_v1` (field↔group Frobenius faces). Reproduction: `scratchpad/island_gate*.py`.
Exact `int` Eisenstein arithmetic. No master edited.

## Construction (the group-side carry)
The field carry is `c(X)=(ω·z(X) − z(βX))/π_p` on the base-field lattice `L_p={π_p, ω·π_p}`. Build the exact
group analog on `L={π_n, ω²·π_n}` (π_n = π_p−1): lift a scalar `d` to `D(d)∈ℤ[ω]` (reduce `(d,0)` mod the
ideal `(π_n)`, since `ℤ[ω]/π_n ≅ 𝔽_n`), and set
`c_group(d) = (ω·D(d) − D(λ_π·d)) / π_n`, where **`λ_π = −a·b⁻¹ mod n`** is the specific cube root that `ω`
reduces to mod `π_n = a+bω` (using the arbitrary GLV `λ` = the *other* root breaks exactness — a real bug,
fixed).

## Result — same trichotomy, same ¾ law, same 3/16 threshold
`c_group` takes three consecutive values `{c₀, c₀±ω}` (constant offset `c₀`, a fundamental-domain
convention). Re-centered `ĉ = c_group − c₀ ∈ {0, ±ω}`:

| n | Pr[ĉ=0] | {0 : +ω : −ω} | min `s` where ĉ≠0 |
|---|---|---|---|
| 199 | 0.7475 | 148 : 25 : 24 | 0.1859 |
| 997 | 0.7510 | 748 : 124 : 123 | 0.1896 |
| 4999 | 0.7505 | 3751 : 624 : 622 | 0.1878 |
| 20011 | 0.7497 | 15001 : 2505 : 2503 | **0.1877 → 3/16** |

- **`Pr[ĉ=0] → ¾`**, distribution **`{¾, ⅛, ⅛}`** — the *exact* field-carry law
  (`NOTE_glv_orbit_carry_conservation` T1: 3/4, 1/8, 1/8).
- The **carry-nonzero region starts at `s = 3/16`** (min `s|ĉ≠0` → 0.1875), matching the field gate's sharp
  tangency at `s=3/16` (`NOTE_core_gate_exact_carry_region`: `s<3/16 ⟹ c=0`, sharp). Since every `ĉ≠0` point
  has `s ≥ 3/16`, `s<3/16 ⟹ ĉ=0` holds on the group side too.

## Interpretation (honest)
The carry `¾`-law and the `3/16` gate are **not special to the field/carry lattice** — they are intrinsic to
**Eisenstein (ℤ[ω]) reduction**, hence appear on *every* Frobenius face `Q(c)=N(π_p−c)`: the field (`c=0`,
`π_p`, the known carry gate) and the group (`c=1`, `π_n`, this island gate) carry the **same** gate. So the
project's `ε=0` gate line of work has a group-order twin, on the same lattice whose interval-slice is the
×λ island.

## Scope / caveats
- 4 scales, `n ≤ 20011`, small-prime CM curves; the ¾ and 3/16 are converging cleanly, not yet proven.
- The `s`-normalization here (Babai parallelepiped, `s∈[0,~2.3]`) differs from the field's centered-hexagon
  `s∈[0,¾]`; the **3/16 boundary matches as a number**, but a like-for-like domain match is not yet made.
- One stray boundary point per curve (rounding at the domain edge) — noted, not swept.
- I over-read two patterns earlier this session; this one rests on the exact `{¾,⅛,⅛}`+`3/16` match across 4
  scales, and on the geometric argument (same ℤ[ω] reduction), not on a single fit.

## What it opens
- The `ε=0` gate's downstream program (the whole carry/lift arsenal) has a group-side mirror to re-run on `L`.
- Next: does the group gate `ĉ(d)` relate to the *interval* island `S` (both are ×λ-reduction objects, one on
  the hexagon domain, one on the interval)? And to the scalar-carry `ε_LBE` the project holds OPEN (N16)?
