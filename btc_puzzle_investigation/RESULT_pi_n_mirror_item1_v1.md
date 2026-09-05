# RESULT — ITEM 1: the `(π_n)` mirror. The rhombus law mirrors; the pinned-pair bridge is NOT WELL-DEFINED as stated

**Date:** 2026-08-01. **Scripts:** `pi_n_mirror_v1.py` (found the gap), `pi_n_mirror_v2.py` (canonical).
**Grade:** rhombus mirror `[VERIFIED — exact]`; bridge defect `[PROVED — structural]`.

## 0. The item

`SYNTHESIS_curve_structure_and_new_directions_v1.md` §2.4, flagged *"unrun and cheap"*: does the
pinned-pair ↔ Frobenius-angle bridge (`{1,4}` if `θ<30°` else `{0,3}`, *"0 violations / 69 primes"*)
give the **same** pinned pair on `(π_n)` as on `(π_p)`? Its own falsifier: *"pinned pair differs ⇒
the two ideals are not interchangeable and the mirror is a different object."*

## 1. What mirrors cleanly

**The rhombus theorem holds on `(π_n)`.** Both reduced basis vectors have norm exactly `n`, and the
fundamental parallelogram has area exactly `n` — verified in exact integer arithmetic. The
`t_n = n+1−p = 2 − t_p` relation holds exactly, and both satisfy Hasse.

**Structural note worth recording:** `eis_n(d) = d mod π_n` **IS the GLV decomposition** `d ↦ (k₁,k₂)`.
The `n`-side lift and the GLV lift are the same map — which ties this item directly to the
`2^128` / Voronoi work of this session.

## 2. The defect — the pinned pair is not a property of the ideal

A reduced basis of an ideal `(π)` is defined only up to the **six Eisenstein units** (and conjugation).
Multiplying `π` by a unit rotates the fundamental parallelogram by 60°, which **cyclically permutes**
the pinned pair `{0,3} → {1,4} → {2,5} → {0,3}`. So "the pinned pair" is not determined by the ideal
until a **generator** is fixed — and the record never states the convention.

Evidence, three independent ways:

1. An arbitrary Cornacchia generator gives pinned pair **`[2,5]`** for `(π_p)`, where the record
   reports `[0,3]`. Same ideal, different associate.
2. Under that arbitrary choice the bridge rule scores **19/40**, against the record's claimed
   *"0 violations / 69 primes"*.
3. `eisenstein_lift_sextant_exact_v1.py` **hardcodes** `aP, bP` for secp with `aP²−aP·bP+bP² = p`
   and supplies **no general rule** for other primes. That generator is a different associate from
   the canonical one — `bP = aP − b_canonical` — which is exactly why it reports `[0,3]`.

## 3. Under a canonical normalization the bridge carries no information

Every ideal of `ℤ[ω]` of norm `M` has **exactly one** generator with `arg(π) ∈ [0°,60°)` — in
`(a,b)` coordinates, `b ≥ 0` and `a > b`. Fixing that, and building the rhombus deterministically as
`R₁ = π`, `R₂ = πω`:

> **the pinned pair is `[1,4]` for every prime tested — 60/60, `q = 7 … 700+`, and for both
> `(π_p)` and `(π_n)` at secp scale.** It does **not** depend on `θ`.

The bridge's `θ`-dependence therefore predicts `[0,3]` on the 28/60 primes with `arg ≥ 30°` and is
wrong on every one of them. A statistic that is **constant across the whole family carries zero
information** — the 7th logged forced-statistic instance on this project.

## 4. Item 1 verdict

- **The falsifier does not fire:** pinned pair on `(π_p)` = pinned pair on `(π_n)` = `[1,4]`.
  But the agreement is **vacuous**, because the statistic is constant for every ideal.
- **The named check cannot discriminate.** As specified it is either constant (canonical
  normalization) or an artifact of an undocumented generator choice (the record's convention).
- **⇒ "pinned pair ↔ Frobenius angle", listed among three `[VERIFIED]` bridges in `MASTER_v4`,
  is not well-defined as stated** and should not be carried forward, in the `(π_n)` mirror or
  anywhere else, until the generator convention is written down. It may well be a true statement
  about a specific normalization; nothing here shows it false, only that it is unstated.

## 5. What of §2.4 remains

The rhombus/area laws mirror exactly (§1). **Not** run: the norm band, Cap Law, `σ`, frame operator
and `C_T` on `(π_n)`; and the `h(−n)` analogue of `|FLD| = 6h(−p)` (class numbers at `2^256` are not
computable directly — that one is a small-prime study, not a secp computation).
