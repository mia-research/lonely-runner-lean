# RESULT — #26: the reduction is CONFIRMED as a computed object; the odd-involution mechanism is REFUTED exhaustively

**Date:** 2026-08-01. **Scripts:** `tors2_involution_test_v1/v2/v3.py` (+ the PGL₂ sweep).
**Grade:** phenomenon `[VERIFIED — exact, 2 primes × 5 values of R]`; mechanism
`[REFUTED — exhaustive search of the full PGL₂(F_p), 2 primes]`.
Per the drill protocol a killed named mechanism is a valid output. **The vanishing itself is
untouched and is now stated more sharply than before.**

---

## 1. The reduction is now an actual computed object

`RESULT_26_reduction_to_character_sum_v1.md` derived #26 ⟺ `Σ_t χ₂(g(t)F(t)) = 0` but never
constructed `g·F`. It is constructed here, via the **degree-1 coordinate**: pairs `{P₁,P₂}` with
`P₁+P₂ = R` are exactly the lines through `−R`, so the coordinate on `E/ι ≅ P¹` is the **slope `λ`**
of that line. (`x₁+x₂` is *not* usable: `x₁+x₂ = λ²−x_R` is 2:1 and collides — this cost one wrong
run, caught by the built-in sum check.)

Term function `T(t) = s(t)·χ₂(F(t))`, `s = +1` split (rational pair) / `−1` inert (conjugate pair):

| curve | `p` | `n` | `#t` (branch excl.) | `Σ T(t)` | `+1` | `−1` |
|---|---|---|---|---|---|---|
| `y²=x³+7` | 43 | 31 | 42 | **0** | 21 | 21 |
| `y²=x³+7` | 67 | 79 | 66 | **0** | 33 | 33 |

every `R = [e]G`, `e = 1..5`, both primes.

**Two things are pinned that the derivation had only gestured at:**
- **The boundary term is exactly `+1`.** Including the branch fibre the sum is `1`, not `0`, at every
  `R` and both primes. It is the tangent fibre at `P₀` with `2P₀ = R`, contributing
  `χ₂(y_{P₀}²) = +1`. The derivation said "branch points handled separately"; the separate handling
  is a single `+1`.
- **The vanishing is EXACT BALANCE, not cancellation-on-average.** `T` takes value `+1` on exactly
  `(p−1)/2` points and `−1` on exactly `(p−1)/2`. That is stronger than `Σ = 0`.

## 2. The mechanism is refuted — exhaustively

`RESULT_26_reduction…v1.md` §4 hypothesised an **odd symmetry**: an involution `σ` of `P¹` with
`G∘σ = ν·G`, `χ₂(ν) = −1`, pairing terms `+1`/`−1`. The natural candidates were the `E[2]`-translations
`τ_T`, which do descend to `E/ι` (they commute with `ι` since `2T = O`) and are non-`F_p`-rational
exactly when `n` is odd — the same condition under which the identity holds.

**Searched, and not found:**

| search space | size (`p=43` / `p=67`) | result |
|---|---|---|
| all involutions in `PGL₂(F_p)` | 77 658 / 296 274 reps | **NONE** |
| **all of `PGL₂(F_p)`, any order** | 79 464 / 300 696 reps | **NONE** |

**⇒ the exact balance of `T` is NOT induced by any linear-fractional symmetry of the `t`-line.**
This is exhaustive over the whole automorphism group of `P¹`, not a sample.

**A methodological note worth keeping:** the first two runs of this test *also* returned "NONE", and
both were invalid — a 2:1 coordinate, then a branch point that provably cannot be paired, each of
which makes the search vacuously fail. Both were caught by the **built-in `Σ = 0` check**, not by
inspection. A negative from a search whose validity condition has not fired is not a negative.

## 3. What this does and does not close

**Does not close #26.** The vanishing is confirmed and sharpened; only one candidate explanation died.

**Does close, at grade:** *"the balance of `T` is produced by a Möbius symmetry of `E/ι` over `F_p`"* —
object: the term function `T` on `P¹(F_p)∖{branch}`; class of observable: all of `PGL₂(F_p)` acting
by `t ↦ σt` with `T∘σ = −T`; power: exhaustive, exact arithmetic, no sampling; scope: `p = 43, 67`,
`y² = x³+7`, `R = [e]G` for `e = 1..5`.

## 4. Where the mechanism must live instead — sharper than before

The balancing structure is **not on the `t`-line**. It must come from the covering or the curve:
- the Galois action on `E[2]`, which lives over `F_{p³}` when `n` is odd (`x³+Ax+B` irreducible —
  no rational root, else `n` even). The `τ_T` are permuted cyclically by Frobenius; no single one is
  rational, which is consistent with §2's negative and may be the actual source.
- a **non-Möbius** correspondence on `P¹`, or a symmetry visible only after base change to `F_{p³}`.

**Next test, concrete:** repeat the search for `σ` over `F_{p³}`, allowing `σ` to be one of the three
`τ_T`-induced involutions and asking not for `T∘σ = −T` on `F_p`-points, but for the induced action
on the `F_{p³}`-points of the cover. That is the first place the odd/even-`n` hinge and the vanishing
can meet, and it is the same object flagged in `RESULT_26_reduction…v1.md` §4.
