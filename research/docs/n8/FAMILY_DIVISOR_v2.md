# The per-family structure — v2, with v1's transfer claim corrected

`FAMILY_DIVISOR_v1.md` closed by saying every result scoped to "divisor-closed profiles" should be
re-read as scoped to "one candidate family, hence every profile". **That was too strong**, and the
correction sharpens what the composition actually gives.

## The correction

`divisor_reduces` sends a *dividing* reading to a **unit** numerator: `blocks s A m ↔ blocks 1 A (m/s)`.
The general per-family reduction sends an arbitrary reading to a **coprime** numerator, `blocks aⱼ A bⱼ`
with `aⱼ ≠ 1`. Those are not the same object, and the results proved for `blocks 1` do not
automatically transfer.

**Tested directly.** `small_b_blocks_iff` says `blocks 1 (8q+1) b ↔ b ∣ q` for `2 ≤ b ≤ 7`. With a
general coprime numerator it **fails**: 24,533 exceptions over `b < 12`, `a < 200`, `q < 60`, the
first at `a = 3, b = 2, q = 0`. It fails for **every** modulus `2 ≤ b ≤ 13` — not a boundary effect.

So the honest split of what the composition transfers:

| result | transfers to arbitrary `aⱼ`? |
|---|---|
| `common_factor_reduces`, `reduced_modulus_dvd` | **yes** — that is the composition itself |
| `Involution.clear_reflect` and the two centres | **yes** — stated on the residue and the interval, not on `a` |
| `Degenerate2` | **yes** — a statement about `L`, `U` |
| `EdgeWitness`, `SolutionPair` | **yes** — abstract over `(modulus, L, U)` triples |
| `small_b_blocks_iff` | **no** — `α = 1` only |
| `divisor_reduces` | **no** — requires the reading to divide |

The v1 sentence covered the first four rows and silently included the last two.

## What does survive to arbitrary readings

The residue-class rigidity, now proved:

> **`Rescale.blocker_class`** (Lean, axioms `[propext]` only): `((a·(8q+1)) mod 8b) mod 8 = a mod 8`.

At every candidate, a reading's residue modulo `8b` lies in the class of `a` modulo `8` — whatever
the opening `q`, whatever the modulus `b`. **Each blocker occupies one fixed class mod 8 across the
entire candidate family**; only its position within that class moves.

Writing the residue as `8t + α` with `α = a mod 8`, clearance becomes a condition on `t` alone, with
the admissible band shifting by `α`:

```
    clear  ⟺  t ∈ [ ⌈(b − α)/8⌉ , ⌊(7b − α)/8⌋ ]
```

**Verified: 0 exceptions over 273,440 cases** (`b < 30`, `a < 400`, `q < 40`). At `α = 1` the band is
`t ≥ 1`, which is `small_b_blocks_iff` — so that law is exactly the `α = 1` slice of this one.

## Why the `α`-band is the useful object

It replaces a law that held for one numerator with a formula that holds for all of them, and it says
where the `α`-dependence lives: **entirely in the endpoints of the `t`-band**, not in the structure.
The `8`-fold rigidity is uniform; only the window slides.

That also explains the `24,533` failures without appeal: `α = 3, b = 2` gives band `⌈−1/8⌉ = 0` to
`⌊11/8⌋ = 1`, so `t = 0` is clear — whereas `α = 1` excludes it. The exception at `a = 3, b = 2,
q = 0` is that single shift.

## Status

**`[PROVED]`**: `common_factor_reduces`, `reduced_modulus_dvd`, `blocker_class` — axiom-clean; witness
now 59 declarations.
**`[VERIFIED]`**: the `α`-band formula (273,440 cases, 0 exceptions) and the 12.4M-instance divisor
check.
**Corrected**: v1's claim that the divisor-closed results transfer wholesale. Four of six transfer;
two do not, and the two that do not are the ones that mention the numerator.
