# Consolidating the 26 new theorems: interactions, and three extensions not previously drawn

Inventory of everything added since `MANUSCRIPT_v12`, where it meets the existing infrastructure, and
what follows that had not been noticed.

## Inventory — 26 theorems, all axiom-clean

| file | n | declarations |
|---|---|---|
| `BlockerCount_v1` | 3 | `self_residue`, `self_never_blocks`, `unit_never_blocks` |
| `Rescale_v1` | 5 | `rescaled_residue`, `rescaled_blocks_iff`, `gcd_covariant`, `divisor_reduces`, `small_b_blocks_iff` |
| `Involution_v1` | 3 | `clear_reflect`, `reflect_fails_zero`, `reflect_fails_one` |
| `EdgeWitness_v1` | 4 | `tight_of_step`, `edge_witness`, `tight_of_step_up`, `edge_witness_both` |
| `TimeReversal_v1` | 2 | `bad_reflect`, `clear_reflect_x` |
| `TwoPatterns_v1` | 3 | `unit_on_both`, `reflected_reading`, `blocked_reflect` |
| `Degenerate2_v1` | 3 | `two_degenerate`, `two_both_patterns`, `contains_two_coincides` |
| `SolutionPair_v1` | 3 | `two_of_reflect`, `not_singleton`, `zero_not_sat` |

Witness: `experiments/n8/v12_new_axioms_v1.out`, 54 declarations, 0 errors.

## How they meet the existing infrastructure

Several of these are not new facts but old ones seen properly:

- **`clear_reflect` is `TimeReversal.bad_reflect` on residues.** `q ↦ m−q` is `x ↦ 8−x` under
  `x = 8q/m` (0 exceptions, all `m < 300`). Not two results.
- **`blocked_reflect` is the same symmetry at the level of counts**, proved by the involution
  `v ↦ 8b−v`.
- **`self_never_blocks` is `rescaled_blocks_iff` at `c = 1`**, and `divisor_reduces` is
  `gcd_covariant` at `a = 1`. The family has two roots, not five.
- **`small_b_blocks_iff` breaks at `b = 8` because of `n−1`** — Theorem 4.8's constant, reappearing
  where it was not expected.
- **`Degenerate2` explains an exception set**: `b = 2` is the unique modulus with `L = U`, so a
  profile containing it has every witness on both patterns. Measured: 0 of the 595 exceptional
  profiles contain it.
- **`EdgeWitness` complements `ReachRule.witness_normalised`**: the latter locates *extremal*
  witnesses, the former *interior* ones. Together they cover the two families, and the extremal
  supply is provably exhausted at 38.83%.

## Three extensions not previously drawn

### 1. Seven of the theorems are not about order 8 at all

`EdgeWitness.Sat` is an arbitrary list of `(modulus, lower, upper)` triples — **no order appears in
the definition or in any of its four theorems**, and `SolutionPair` (3 more) has no definitions at
all. So those **7 theorems apply to any finite system of congruence-interval constraints**, at any
order, and outside the Lonely Runner setting entirely.

Instantiated and checked at orders `7, 8, 9, 11, 13` — 991 profiles each: **0 with no edge witness,
0 singletons, at every order.**

This matters beyond `n = 8`: they apply to the general-`n` programme and to the `n = 11` work as they
stand, with no adaptation.

### 2. The reflection obstruction is order-general

`Involution.reflect_fails_zero` / `_one` were derived at order 8, where the obstruction sits at
`b ≡ 0, 1 (mod 8)`. Computed at every order `4 ≤ n ≤ 13`: the residues with `L(b)+U(b) = b−1` are
**always exactly `{0, 1} mod n`**, and no other sum ever occurs.

So *the two reflection centres* — `c ≡ 0` for good moduli, `c ≡ −1` for obstructed ones — is a
general-`n` law, and the two obstructing residues remain the collision residue (`b ≡ 0`) and the
guard residue (`b ≡ 1`) at every order.

### 3. `b = 2` is the unique degenerate modulus at every order

`L(b) = U(b)` holds for `b = 2` and **no other `b < 600`, at every order `4 ≤ n ≤ 13`**. The
degeneracy that explains exception set A is therefore a fact about the modulus `2`, not about the
order.

## What `16` is

`R < 16` is `R < 2n`. Since `⌊R/n⌋` counts the complete laps `d_min` makes before isolation,

> **`R < 2n` says exactly: `d_min` completes at most one full lap.**

Not a numerical accident. Whether one lap suffices at other orders is **not settled here** — random
sampling cannot reach band 1 by construction (the manuscript records that no random cascade does),
and a hill-climb for depth was abandoned as the wrong use of time.

## Correction carried forward

An earlier claim that `R < 16` is "a different handle" on Existence is **withdrawn**. `R` is the least
clear point `≥ 1` (Theorem 11.1), band 1 is a `+8` shift of band 0 for integer readings
(`Guard.block_periodic`), so `R > 7` forces non-integer readings. **`R < 16` and the rational
frontier are one problem**, confirmed on every deep case on file.
