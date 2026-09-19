# Time reversal: the reflections were always one symmetry

The reflections that kept recurring — `r ↦ b − r`, `q ↦ m − q`, the `L`/`U` pairing, the U-shaped
witness distribution — are **one symmetry seen at four levels**. Identifying it explains the
obstruction we had only ever computed.

## The symmetry

**`TimeReversal.bad_reflect`** (Lean, axiom-clean): for an **integer** reading `s`, the bad condition
`dist(s·x, 8ℤ) < 1` is invariant under `x ↦ 8 − x`, since `s(8−x) − 8k = −(sx − 8(s−k))` and
`k ↦ s − k` is a bijection of `ℤ`.

**`TimeReversal.clear_reflect_x`**: hence the clear set of any finite integer reading family is
symmetric about `x = 4`. *Checked before proving: 176,775 samples, 0 exceptions.*

This is elementary — it is time reversal, running the race backwards. **No novelty is claimed.** What
matters is where it goes.

## The four levels are the same map

| level | the map | status |
|---|---|---|
| the race | `t ↦ 1 − t`, i.e. `x ↦ 8 − x` | `bad_reflect` |
| residues, via `x = 8q/m` | `q ↦ m − q` | `Involution.clear_reflect` |
| a single modulus | `r ↦ b − r` | same theorem |
| the witness supply | `L` ↔ `U`, measured `49.8 / 50.2` | `EdgeWitness.edge_witness_both` |

`Involution.clear_reflect` is **not a separate phenomenon**. It is time reversal expressed on
residues, and `q ↦ m − q` is literally `x ↦ 8 − x` under `x = 8q/m` (verified: 0 exceptions over all
`m < 300` and all `q`).

## Why the obstruction exists — not just where

The candidates carry numerators `8q + 1`. Under `q ↦ m − q` the numerator becomes
`8m − (8q+1) + 2`, whose residue mod `8` is **`−1`, not `+1`**.

> The continuum has the symmetry exactly. **The admissible lattice does not: the `+1` lattice maps to
> the `−1` lattice.**

`Involution.clear_reflect` holds precisely where that mismatch does not bite, and the two failures
are the two residues already central to the framework:

- **`b ≡ 0 (mod 8)`** — the collision residue splitting Branch A from Branch B. There the `+1` and
  `−1` lattices *coincide* mod `b`.
- **`b ≡ 1 (mod 8)`** — the guard residue `s·R ≡ 1 (mod 8)`. There the shift by `2` lands exactly on
  a boundary.

Verified: `I(b)` is symmetric under `r ↦ b − r` iff `b mod 8 ∉ {0,1}`, 0 exceptions for `b < 200`;
and `b = 8, 9, 16, 17` all break it, with `L+U = 7, 8, 15, 16` against `b`.

**This is the explanation that was missing.** `reflect_fails_zero` and `reflect_fails_one` were
computed, then verified, then proved — but never *explained*. They are the lattice failing a symmetry
the continuum has, at the framework's two distinguished residues. It also explains, in one line, why
the left-endpoint family covers 0%: it is the `−1` lattice, and integrality forces us onto the `+1`
one.

## What this does not do

It closes no frontier. It is a structural unification: four results that looked independent are one
symmetry, and the obstruction has a cause rather than a computation. Existence at order 8 is
unchanged.
