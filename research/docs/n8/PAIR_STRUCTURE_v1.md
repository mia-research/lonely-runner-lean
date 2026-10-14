# Two patterns inverted: how the AP's four isolation events spill down

An owner's structural claim, tested and made exact: *the four global isolation events in the AP are
two patterns inverted, and that structure spills down.*

## The two group actions

The AP's clear set is the odd spine `{1,3,5,7}` (`Guard.ap_clear_at_odd`). Two actions live on it:

- **reflection** `u ↦ 8 − u` — orbits `{1,7}` and `{3,5}`: **two inverted pairs**;
- **units** `u ↦ w·u` — one orbit of all four, because `8 ∣ s·u ⟺ 8 ∣ s` for odd `u`. Multiplication
  by `3` sends `1↦3, 7↦5`, i.e. it **swaps the pairs**.

So `spine_all_or_nothing` — all four clear together — is the *unit* action, and it is strictly
stronger than the reflection, which only pairs them. The pair structure is therefore invisible at the
AP. **The question is where it survives the merge.** It does.

## Where it survives, exactly

After `Rescale.gcd_covariant` the blocking of a reading with coprime parts `α, β` depends only on
those. Write `α' = α mod 8`. The residues `α(8k+1) mod 8β` run over the `β` values congruent to `α'`
mod `8`, each once, and block iff below `β` or above `7β`. Hence the **exact count**

```
   blocked(α', β) = #{ j ≥ 0 : α' + 8j < β }  +  #{ j : 7β < α' + 8j < 8β }
```

**Verified against direct enumeration: `β < 300`, all four `α'`, 0 mismatches.**

Reading the floors off that formula gives a clean law, with no exceptions for `9 ≤ β ≤ 600`:

| `β mod 8` | `α'=1` | `α'=3` | `α'=5` | `α'=7` | `{1,7}` vs `{3,5}` |
|---|---|---|---|---|---|
| 0, 1 | 80 | 80 | 80 | 80 | 0 |
| **2, 3** | **81** | 80 | 80 | **81** | **+2** |
| 4, 5 | 81 | 81 | 81 | 81 | 0 |
| **6, 7** | 81 | **82** | **82** | 81 | **−2** |

> **The pair `{1,7}` and the pair `{3,5}` always agree internally — that is the reflection. They
> differ from each other by exactly one lattice point per class, and only when `β ≡ 2,3,6,7 (mod 8)`.
> The favoured pair flips under `β ↦ β + 4`.**

Measured independently as rates over ~10⁶ candidates: `β ≡ 2,3` gives `+2.39` and `+2.32` percentage
points to `{1,7}`; `β ≡ 6,7` gives `−2.27` and `−2.20`; `β ≡ 0,1,4,5` give `±0.05`.

The cause is a single lattice point crossing an interval boundary — the arithmetic progression
`α' + 8j` has one more term below `β` for one pair than the other, depending on where `β` sits mod 8.

## What this settles

- The `β = 2` case found earlier (`±1` blocks at 50%, `±3` never) is **not special**. It is the
  extreme instance of a law covering every `β`.
- The pair structure is real and survives the unit action, but only on half the residues of `β`, and
  with a sign that alternates. That is the precise content of "it spills down".
- `α'=1` agreeing with `α'=7`, and `3` with `5`, is time reversal (`TimeReversal.bad_reflect`) seen
  at the level of counts.

## Status

`[VERIFIED — exact]`: the count formula matches direct enumeration with 0 mismatches, and the split
law holds with 0 exceptions on the ranges stated. **Not formalised** — the counting statement needs
a `Finset.card` argument in Lean, which is owed. Nothing here closes a frontier.
