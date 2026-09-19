# Where the separation technique reaches — and the `n − 1` constant generalised

Tracing the three separation results outward. The technique had one more thing in range, and it is
the constant that has been recurring since §13.

## What was still order-8

`GeneralReflect` made the interval, its obstruction, and its degeneracy order-general. The one piece
still stated at order 8 was the constant itself: `Rescale.small_b_blocks_iff` is
`blocks 1 (8q+1) b ↔ b ∣ q` for `2 ≤ b ≤ 7`, and its break at `b = 8` was **identified** with
Theorem 4.8's `n − 1` — an identification, not a theorem.

## Proved

> **`GeneralOrder.small_b_general`** — for `2 ≤ b ≤ n − 1`: `blocksN n 1 (n·q+1) b ↔ b ∣ q`.

Lean, axiom-clean. The `n − 1` bound is **sharp**: the law fails at `b = n`.

The derivation names both endpoints. A candidate `n·q+1` has residue `n·ρ + 1` with `ρ = q mod b`, and
clearance asks `b ≤ n·ρ + 1 ≤ (n−1)·b`:

* the **lower** bound fails at `ρ = 0` — that is the `b ∣ q` case, and it is why blocking *is*
  divisibility;
* the **upper** bound is tightest at `ρ = b − 1`, where it reads exactly `n − 1 ≥ b`.

So `n − 1` is not a coincidence of `8`: it is the upper endpoint of the clear interval evaluated at
the last residue. Checked at every order `4 ≤ n ≤ 19` before proving — the largest `b` for which the
law holds is `n − 1` in every case, and the first failure at `b = n` is at `q = b − 1`, the upper
endpoint, exactly as derived.

## The technique, four for four

| result | separation | what it closed |
|---|---|---|
| `SplitLaw.split_law` | `b = 8j + r` | the antisymmetric half of the pair law |
| `GeneralReflect.obstruction_iff` | `b = n·j + r` | the two obstructing residues, every order |
| `GeneralReflect.width_pos` | `b = n·j + r` | the degenerate modulus, every order `≥ 4` |
| `GeneralOrder.small_b_general` | `q = b·k + ρ` | the `n − 1` constant, every order |

The fourth separates the **candidate** rather than the modulus, which is the variation worth noting:
the same move applies to whichever variable carries the floor.

## What this consolidates

Four facts that were order-8 statements with computational support are now order-general theorems:

- the clear interval's endpoints and their separation;
- the reflection and its two obstructing residues — the **collision** residue `b ≡ 0` and the
  **guard** residue `b ≡ 1`;
- the unique degenerate modulus `b = 2`, for `n ≥ 4`;
- the small-modulus law and its sharp bound `n − 1`.

Together with Branch A at every order (`GeneralOrder.spine_all_or_nothing`) and the 25 order-free
Tier 1 declarations, **the general-`n` programme of §8 now inherits the interval apparatus with
proofs rather than with re-derivation owed.**

## Where it does not reach

The Tier 3 boundary stands: `klein_self_inverse` holds exactly for `n ∣ 24`, so `TwoPatterns` and the
AP's four coincidences do **not** generalise. The separation technique cannot help there — the
obstruction is the structure of the unit group, not a floor.

Nor does it touch the open frontiers. Every result above is about the *interval*; none is about
whether a witness exists. **Existence at order 8 is unchanged.**

## Status

`[PROVED]`: `small_b_general`, axiom-clean; witness now 71 declarations.
`[VERIFIED]`: the sharpness check, orders `4 ≤ n ≤ 19`.
