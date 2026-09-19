# `R < 16` is not a separate frontier — it is the rational one

I proposed `R < 16` as "a different handle" on the grounds that it was untouched. That was a reason
to look, not a mechanism, and the owner was right to challenge it. Reading §11 of the manuscript
rather than reasoning from the shape gives the actual answer, and it is a consolidation.

## What `R` is

**Theorem 11.1**: `R = min{ R ≥ 1 : ∀i, sᵢ·R mod 8 ∈ [1,7] }` — that is, **`R` is the least clear
point `≥ 1`** in exactly the coordinate this whole arc has worked in. `R < 16` says precisely that
`[1,7] ∪ [9,15]` contains a clear point.

So `R < 16` is **the same question over two bands instead of one.**

## Band 1 is the rational frontier, and nothing else

`Guard.block_periodic` makes band 1 an exact `+8` shift of band 0 **for integer readings**. So for
integer readings `R ≤ 7`, and the second band adds nothing whatever. Hence

> **`R > 7` forces the readings to be non-integer.**

And non-integer readings are exactly the rational frontier — shown earlier to be *integer speed sets
with no unit speed* (200,000 sets, 0 mismatches).

**Confirmed on every deep case on file:**

| disparities | `R` | band | readings integer? |
|---|---|---|---|
| `[2520, 5750, 8003, 10557, 13161, 14580, 18745]` | `44856/3749` | 1 | no |
| `[158, 367, 505, 664, 827, 918, 1179]` | `14062/1179` | 1 | no |
| `[46, 107, 146, 194, 241, 268, 344]` | `1127/97` | 1 | no |

The first reproduces the recorded value `44856/3749 = 11.964791` **exactly**.

**So the map's `R < 16` row and its `rational readings` row are one open problem, not two.** That is
the second such consolidation in this arc — the first being that integer and rational readings are
one question split by whether `1` survives reduction.

## A method note worth keeping

My first attempt scanned for clear points on a grid of step `1/480` and concluded that band 0 is
never empty — 0 of 3,132 profiles, and hill-climbing topped out at `R = 3.925`. **Both were artefacts
of the grid**: the deep case has `R = 44856/3749`, and a `1/480` grid cannot represent it.

The fix was our own theorem. `ReachRule.witness_normalised` says the least clear point is `1` or an
endpoint `(8k±1)/s`, so enumerating that family computes `R` **exactly** — and it reproduced the
recorded value on the first try.

A grid is an approximation of a set we have a proved exact description of. Using the approximation
produced two false negatives in a row.

## Where this leaves the target

Not a new handle, but a sharper statement of the old one:

> **Existence at order 8 reduces to: for every reading profile with `1 = s₁ < … < s₇`, some
> `R ∈ [1,7] ∪ [9,15]` has `dist(sᵢ·R, 8ℤ) ≥ 1` for all `i`.** Integer readings need only the first
> band and are `[VERIFIED]` exhaustively; the second band is needed exactly on the rational frontier.

The manuscript already records that counting is no help here — six combs at density `1/4` over 12
units give 18 units of bad measure, a factor of `1.5`. That matches the adverse-correlation finding
independently: **no counting argument will close this**, in either band.
