# The degenerate modulus, bounded — and the claim I nearly proved wrong

Third owed item closed by the endpoint separation. It also caught a false statement one step before
the proof.

## The claim was false at two orders

`FAMILY_DIVISOR` and §14F record that `b = 2` is the **only** modulus with `L(b) = U(b)`, checked at
every order `4 ≤ n ≤ 13`. I set out to prove it at general `n`, and the hand computation said `n = 3,
b = 3` should also degenerate. Checking before proving:

| `n` | degenerate moduli, `b < 400` |
|---|---|
| 2 | every odd `b` |
| **3** | **2 and 3** |
| 4–15 | 2 only |

**The uniqueness claim is false at `n = 2` and `n = 3`**, and true from `n = 4`. The earlier
computation ran `n ∈ [4,13]` and could not have seen it. Nothing downstream used `n ≤ 3`, so nothing
is withdrawn — but the statement now carries its hypothesis.

## Proved, for `n ≥ 4`

> **`GeneralReflect.L_small`** — for `0 ≤ r < n`: `L(r) = 1` if `r ≥ 2`, else `0`
> **`GeneralReflect.U_small`** — for `0 ≤ r < n`: `U(r) = r − 1`
> **`GeneralReflect.width_pos`** — for `n ≥ 4` and `b ≥ 3`: `L(b) + 1 ≤ U(b)`

All Lean, axiom-clean; the first two on `[propext, Quot.sound]` only. With `Degenerate2` supplying
`L(2) = U(2) = 1`, `width_pos` completes the statement: **at every order `n ≥ 4`, the clear interval is
degenerate exactly at `b = 2`.**

Cross-checked after proving: `n ∈ [4,60)`, `b ∈ [3,3000)` — **167,832 cases, 0 failures**.

## The mechanism, and why `n = 3` breaks

For `2 ≤ b < n` the interval is `[1, b−1]`, collapsing exactly at `b = 2`. For `b ≥ n`, writing
`b = n·j + r` with `j ≥ 1`, the width separates as

```
    U(b) − L(b)  =  (n−2)·j + (U(r) − L(r))  ≥  (n−2) − 1  =  n − 3.
```

Positive precisely when `n ≥ 4`. At `n = 3` the bound is `0`, and `b = 3` (`j = 1`, `r = 0`) attains
it — `L = U = 1`, width `0`. The exception is not an accident of small numbers; it is the bound
becoming vacuous.

## Three uses of one technique

| result | separation | what it closed |
|---|---|---|
| `SplitLaw.split_law` | `b = 8j + r` | the antisymmetric half of the pair law |
| `GeneralReflect.obstruction_iff` | `b = n·j + r` | the two obstructing residues, at every order |
| `GeneralReflect.width_pos` | `b = n·j + r` | the degenerate modulus, at every order `≥ 4` |

All three were `[VERIFIED]` measurements. All three became proofs by separating the endpoints so the
`j` part cancels and only `r` survives. **Where a statement is a floor or ceiling identity over a
modulus, separate first** — that is now three for three.

## And the discipline that caught the false version

The hand computation disagreed with the recorded range, so I extended the computation **before**
writing the proof. Had I trusted `n ∈ [4,13]` and generalised, I would have produced a theorem with a
false hypothesis and a proof that could not close — or worse, one that closed because the statement
was wrong.

The earlier range was not an error when it was written; it became one when its conclusion was
generalised past it. **A verified range is a claim about that range.**

## Status

`[PROVED]`: three theorems, axiom-clean; witness now 70 declarations.
`[CORRECTED]`: the degeneracy uniqueness claim now carries `n ≥ 4`.
Existence at order 8 unchanged.
