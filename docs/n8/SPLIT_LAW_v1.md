# The split law, proved — and the failure that produced it

`PAIR_STRUCTURE_v2` proved the **symmetric** half of the pair law by an involution and left the
**antisymmetric** half — the split itself — owed. It is now proved. The route to it was a **failed**
generalisation, not a successful one.

## What did not work, and why that mattered

I claimed that the divisor-closed results transfer to every candidate family. `small_b_blocks_iff` is
`blocks 1 (8q+1) b ↔ b ∣ q`; with a general coprime numerator it **fails** — 24,533 exceptions, every
modulus `2 ≤ b ≤ 13`, first at `a = 3, b = 2, q = 0`.

Diagnosing *why* it failed is what produced the theorem. The residue at a candidate is
`8t + α` with `α = a mod 8` (`Rescale.blocker_class`, proved), so clearance is a band on `t`:

```
    clear  ⟺  t ∈ [ ⌈(b − α)/8⌉ , ⌊(7b − α)/8⌋ ]
```

At `α = 1` the band starts at `t = 1`, which is `b ∤ q` — the old law. At `α = 3, b = 2` the band is
`[0,1]`, so `t = 0` is clear where `α = 1` excluded it. **The counterexample is that single shift.**

So the failure was not noise. It was the `α`-dependence, and locating it gave the general law of which
the old one is the `α = 1` slice.

## What that then closed

Writing `b = 8j + r`, the band endpoints **separate**:

> **`SplitLaw.lo_split`** — `⌈(b−α)/8⌉ = j + ⌈(r−α)/8⌉`
> **`SplitLaw.hi_split`** — `⌊(7b−α)/8⌋ = 7j + ⌊(7r−α)/8⌋`

and **the `j` parts do not depend on `α`**. Hence

> **`SplitLaw.blocked_split`** — `blocked(α, b) = 2j + r − ⌊(7r−α)/8⌋ + ⌈(r−α)/8⌉ − 1`.

All the `α`-dependence sits in a function of `r` and `α` alone — **32 integers** — so the split
becomes a finite check:

> **`SplitLaw.split_law`** — `(blocked 1 + blocked 7) − (blocked 3 + blocked 5) = +2` at `r = 2,3`,
> `−2` at `r = 6,7`, and `0` otherwise. Everything in `j` cancels.

All four Lean, axiom-clean; the first three on `[propext, Quot.sound]` only. Checked against direct
enumeration before proving: 1,592 cases, `b < 400`, 0 mismatches.

## The pair law is now complete

| half | statement | status |
|---|---|---|
| symmetric | `blocked(α) = blocked(8−α)`, so `{1,7}` and `{3,5}` agree internally | **`[PROVED]`** — `TwoPatterns.blocked_reflect`, by involution |
| antisymmetric | the two pairs differ by `±2` exactly at `b ≡ 2,3,6,7 (mod 8)`, flipping under `b ↦ b+4` | **`[PROVED]`** — `SplitLaw.split_law`, by endpoint separation |

Both halves were measured months apart and each needed a different mechanism: a **symmetry** for one,
**floor arithmetic** for the other. Neither yielded to the other's method.

## The method note

The working loop has been *measure → ask why → the answer names a framework object*. This case adds
the other half of it, which had been implicit:

> **A failed generalisation is diagnostic. Locating why it fails often *is* the generalisation.**

Here the failure was a shift of one lattice point in a band endpoint. Recording "the law does not
transfer" and stopping would have lost the general law and the split proof with it. The five routes
in Appendix A that are closed **with stated reasons** are worth more than the same five closed without
them, for the same reason.

## Status

`[PROVED]`: four theorems, axiom-clean; witness now 63 declarations.
`[VERIFIED]`: the `α`-band formula (273,440 cases) and the blocked-count check (1,592 cases).
Existence at order 8 is unchanged.
