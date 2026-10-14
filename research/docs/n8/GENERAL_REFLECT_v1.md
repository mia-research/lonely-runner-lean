# The reflection obstruction at every order — verified became proved

Another item off the owed list, by the technique that closed the split law: **separate the endpoints
at `b = n·j + r` and the order-dependence collapses to `r`.**

## What was owed

`Involution.clear_reflect` holds for `b mod 8 ∈ [2,7]`, with `reflect_fails_zero` and
`reflect_fails_one` exhibiting the two failures — all proved, **at order 8**. Computation then said
the same two residues govern every order `4 ≤ n ≤ 13` (`degenerate_range_v1.py`). That was
`[VERIFIED]` and carried forward as such in `CONSOLIDATION_v1` and §14D of the manuscript, explicitly
flagged "proved at order 8 only".

## Proved

At order `n` the clear interval is `Iₙ(b) = [⌈(b−1)/n⌉, ⌊((n−1)b−1)/n⌋]`, and the reflection
`r ↦ b − r` preserves it exactly when the endpoints sum to `b`.

> **`GeneralReflect.L_split`** — `L(n·j + r) = j + L(r)`
> **`GeneralReflect.U_split`** — `U(n·j + r) = (n−1)·j + U(r)`
> **`GeneralReflect.sum_split`** — hence `L + U` at `b` is `n·j + (L(r) + U(r))`
> **`GeneralReflect.obstruction_iff`** — for `0 ≤ r < n` and `n ≥ 2`: `L(r) + U(r) = r ↔ 2 ≤ r`

All four Lean, axiom-clean; `obstruction_iff` on `[propext, Quot.sound]` only.

> **The two obstructing residues are `0` and `1` modulo `n`, at every order — proved, not computed.**

The mechanism in one line: the upper quotient is `r − 1` for every admissible `r`, and the lower is
`1` exactly when `r ≥ 2`. So the sum reaches `r` precisely when `r ≥ 2`, and the `j` part contributes
`b`'s own `n·j` and cancels.

Cross-checked against direct computation after proving: `n < 40`, `b < 2000`, **76,000 cases, 0
mismatches**.

## Why this one mattered

The two residues are the framework's own: `b ≡ 0` is the **collision** residue that splits Branch A
from Branch B, and `b ≡ 1` is the **guard** residue `s·R ≡ 1`. Their appearance at order 8 could have
been an accident of `8`; it is not. The whole reflection apparatus — `clear_reflect`, the two centres
`c ≡ 0` and `c ≡ −1`, and the obstruction — is now an order-general fact with a proof, so it
transfers to the general-`n` programme of §8 rather than needing re-derivation there.

Contrast with the neighbouring result: `TwoPatterns.unit_on_both` and the AP's four coincidences are
special to `n ∣ 24` (`THEOREM_TIERS_v1.md`, Tier 3) and do **not** transfer. Two adjacent facts, one
order-general and one not — which is exactly why each needed checking rather than assuming.

## The technique, now used twice

| result | separation | what collapsed |
|---|---|---|
| `SplitLaw.split_law` | `b = 8j + r` | all `α`-dependence into 32 integers |
| `GeneralReflect.obstruction_iff` | `b = n·j + r` | all order-dependence into `r` |

Both were `[VERIFIED]` measurements that became proofs once the endpoints were separated. Where a
statement is a floor/ceiling identity over a modulus, this separation is the thing to try first.

## Status

`[PROVED]`: four theorems, axiom-clean; witness now 67 declarations. Existence at order 8 unchanged.

**Still owed on the reflection line**: the surviving-orbit result — `|S| ≥ 2` holds on all 19,880
profiles measured, proved only on the 34% admitting a reflection centre. The mixed case (66%) has no
centre, and the orbit survives for a reason not yet identified.
