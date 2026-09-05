# RESULT — the curve ×λ island, MAPPED as an object (structure, not attack-value)

**Grade: `[VERIFIED — exact, enumerated on n=100003; small scale]`.** Date 2026-08-17. Pure structural
mapping of the object `S = {d ∈ I : λd mod n ∈ I}` — what it *is*, not what it is worth to anyone. No
leakage / cost / reduction framing. Reproduction: `scratchpad/island_explore.py`, `_2.py`, `_3.py`.
Exact `int`. Accumulates toward a future v13; no master edited.

## The object
`S = {d ∈ I : λd mod n ∈ I}` for an interval `I` and `λ` = cube root of unity mod `n`. Generatively:
**`S = I ∩ (λ⁻¹·I)`** = the **return set of the ×λ rotation of `ℤ/n` to the interval `I`** (verified
identity). It is a rotation-return set, hence a classical three-gap object — here for the *GLV* rotation.

## Structure 1 — Sturmian / three-gap, self-similar along `CF(λ/n)`
- **Two or three gap sizes only.** e.g. `|I|=3160` → gaps `[14, 183]`; `|I|=6320` → `[14, 43, 57]` with
  **57 = 14+43** (three-gap theorem: the large gap is the sum of the two small ones).
- **Gap sizes are consecutive convergent denominators of `λ/n`.** `CF(λ/n)` denominators `[1,14,309,7121,…]`;
  the small gap sits at a convergent (14) and stays pinned while the large gap grows as `|I|` shrinks
  (`183→253→295`).
- **The gap WORD is Sturmian:** `(A^a B)` periodic — e.g. `A⁹B` — with `BB` forbidden (exactly one forbidden
  transition), and `a·(small)+(big) =` the **next** convergent (`9·14+183 = 309`). So the island
  **renormalizes like a continued fraction**: grow `|I|` past a convergent and the whole gap scale drops one
  rung (`[14,183] → [1,13,14]`).

## Structure 2 — the full-orbit island `S₃ = I ∩ λI ∩ λ²I` has a PHASE TRANSITION

> **`[CORRECTION 2026-08-17 — see RESULT_curve_island_eisenstein_v1]`.** The "saturates at ~3.0 = |⟨λ⟩|"
> claim below is WRONG as a universal statement: the concentration factor is **placement-dependent**,
> periodic in the interval offset with period n/3, ranging **0.00–3.44 (mean 0.69)** — the 3× was one
> offset near a peak. The phase-transition (empty below a CF threshold) is real; the "= |Aut|" reading is not.
The triple overlap of the three 120°-rotated strips (`λ` acts as `(d₁,d₂)→(−d₂,d₁−d₂)` in GLV coordinates,
so `I, λI, λ²I` are three strips at 120°; `S₃` is their common core):
- **Empty below a threshold, switches on sharply at `n/|I| ≈ 7`** (a `CF(λ/n)` scale — about half the first
  large partial quotient `a=14`). Below it the three strips do not meet at all.
- **When on, `S₃` is ~3× OVER-POPULATED** vs the independence estimate `|I|³/n²`: the ratio climbs
  `0.08 → 0.57 → 1.23 → 1.89 → 2.51 → 2.88 → 3.01 → 2.99` and **saturates at `~3.0 = |⟨λ⟩|`**. The order-3
  symmetry **concentrates the triple intersection by exactly the order of the automorphism** — the overlaps
  are correlated, not independent.
- `S₃` is itself a finer multi-gap set (gaps `[1,12,13,14,29,43]` at `|I|=20000`) built from the same
  convergent values — a three-gap set inside three-gap sets.

## What is mapped (the whole claim)
`S` is the ×λ-rotation return set of the interval: a self-similar Sturmian/three-gap set whose gaps are
consecutive `CF(λ/n)` convergents, and whose full-orbit core `S₃` switches on at a CF threshold and
concentrates at `|⟨λ⟩| = 3×` the independent density. All enumeration-verified.

## Open threads for FURTHER mapping (exploration, not attack)
- Is the `S₃` over-population factor **exactly 3** (= |Aut| for μ₃; would it be **6** including negation, μ₆)?
- The exact CF formula for the switch-on threshold `n/|I|` in terms of the partial quotients.
- The GLV-coordinate `(d₁,d₂)` strip geometry rendered explicitly (orientation from `λ`, strip width,
  the hexagonal `S₃` core).
- Whether the `S₃` concentration ties to the **Eisenstein factorization** `n = π·π̄` in `ℤ[ω]` (the CM
  structure) — does `π` set the threshold and the 3× factor?
- The relation between this curve ×λ island and the **source best-approximation island** — same set, dual,
  or independent structures on the same interval?
- Map the gap hierarchy at real secp scale (the convergent ladder of the actual `λ/n`).
