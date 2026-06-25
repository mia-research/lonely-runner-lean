/-!
# n = 7 (Barajas–Serra 2008) — `p = 7` apparatus

Source: `sources_barajas_serra_2008.txt`, §1–§4 (lines 40–264).

7-adic apparatus shared by the whole n = 7 proof:
- `ν = ν₇` : 7-adic valuation (mathlib `padicValNat`/`padicValInt`).
- `q`, `r` : position / residue functions (use `ZMod (7^(m+1))`, `ZMod 7`).
- `Λ_j`    : multiplier sets `1 + k·7^m`.
- `D₇(i)`  : `{d ∈ D : ν(d) = i}`.
- `A_s`    : residue classes `{d ∈ A : (d)₇ = s}`, `s ∈ {1,2,4}`.
- `ℓ(X)`   : length of the smallest unit-difference AP in `ℤ₇` containing `q(X)`.

Reuse `LonelyRunner.LRC.Defs` (circDist, badSet, goodSet, intLRC).

Status: not started (draft pending). See `docs/n7_bs/ROADMAP.md`.

Planned imports: `import LonelyRunner.LRC.Defs`,
`import Mathlib.NumberTheory.Padics.PadicVal`.
-/
