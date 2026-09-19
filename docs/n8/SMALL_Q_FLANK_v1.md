# Denominator `n − 1` closes a case of the flank problem, with an index bound

Working natively after the `H` refutation. The exhaustive enumeration that killed `H` also closed a
case, and the boundary is the framework's own constant.

## The table

Multisets of six movers with `p < q` — the largest-flank condition — enumerated **completely**:

| max `q` | 2 | 3 | 4 | 5 | 6 | **7** | **8** | 9 |
|---|---|---|---|---|---|---|---|---|
| multisets | 1 | 28 | 210 | 3,003 | 8,008 | **74,613** | 230,230 | 906,192 |
| shadowing | 0 | 0 | 0 | 0 | 0 | **0** | **21** | 33 |

**Shadowing is impossible for `q ≤ 7 = n − 1` and first appears at `q = 8 = n`.** That is the same
boundary at which `Rescale.small_b_blocks_iff` breaks, and `GeneralOrder.small_b_general` proves the
boundary is `n − 1` at every order.

The `H` counterexample sits exactly there: `((1,2),(1,2),(1,8),(3,8),(5,8),(7,8))`, which needs the
four eighths.

## With an index bound

Over all 74,613 multisets with `q ≤ 7`, the **largest first-clear index is 29**, attained at
`((1,2),(1,3),(4,5),(5,6),(2,7),(3,7))`.

That is existence **and** a bound on where — which is what the withdrawal of Proposition 6.11
required, and what every earlier candidate in this thread lacked.

**This is exhaustion over a complete finite space, not a sample.** The mover pool at `q ≤ 7` is 17
elements; `C(17+5, 6) = 74,613` is every multiset.

## Why `q ≤ 7` cannot shadow

`Rescale.blocker_class` gives the residue of `p` at a candidate as `≡ p (mod 8)`. With `p < q ≤ 7`
that means `α = p`, and `α < q` puts `t = 0` in the blocked band. Hence:

> **`SmallQFlank.blocks_zero`** — every mover with `0 < p < q` blocks the opening `k = 0`.
> **`SmallQFlank.blocks_zero_of_dvd`** — and blocks every `k` divisible by `q`.

Both Lean, axiom-clean. Computation gives the rest of each blocked set: every mover blocks `{0}`, and
seven of the seventeen block one further residue —

```
  4/5, 5/6, 6/7 : {0,1}    3/7 : {0,2}    2/7 : {0,3}    5/7 : {0,4}    4/7 : {0,5}
```

So six movers block at most twelve residues among moduli dividing `lcm(2..7) = 420`, and the
enumeration shows they never cover.

## What this does and does not settle

**Settles:** a flank all of whose movers have denominator `≤ n − 1` has a clear opening at index
`≤ 29`. Exhaustive, with a bound.

**Does not settle:** Existence. A flank may carry movers of denominator `≥ n`, and the `H`
counterexample shows those can shadow. The case closed here is the one where the framework's `n − 1`
constant applies; beyond it, `small_b_blocks_iff` has already been shown to fail.

## Status

`[PROVED]`: `blocks_zero`, `blocks_zero_of_dvd`, axiom-clean; witness now 79 declarations.
`[EXHAUSTIVE]`: the table, and the index bound 29 over all 74,613 multisets at `q ≤ 7`.
`[OPEN]`: flanks carrying a denominator `≥ 8`. Existence at order 8 unchanged.
