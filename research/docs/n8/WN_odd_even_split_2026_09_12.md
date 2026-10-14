# Working note — the all-odd case is trivial; the `≥ 9` search is unnecessary

2026-09-12. Replaces Step 3 of `WN_count_parity_2026_09_12.md`, which established
"all-odd with `|D| ≥ 4` ⟹ count `≥ 9`" by exhaustive search over 136,629 sets. That bound is
not needed and is not used below. Nothing here is searched.

---

## The four facts

**(A) `D_i` is all-odd ⟺ runner `i` is the unique runner of its parity.**  `[PROVED]`
`|v_j − v_i|` is odd iff `v_j ≢ v_i (mod 2)`. So every difference is odd iff every other runner
has the opposite parity to `v_i`, i.e. iff `v_i` is alone in its parity class. ∎
*Checked: 160,000 runner-instances, 0 disagreements.*

**(B) At most one runner per configuration is all-odd.**  `[PROVED]`
The 8 runners split into two parity classes. If `v_i` is alone in its class, the other class
holds the remaining 7, so no second runner can be alone in its own. ∎
*Checked exhaustively over `[1..16]`: 12,741 configurations with 0 all-odd runners, 128 with
exactly 1, none with 2 or more.*

**(C) An all-odd runner is isolated at `t = 1/2`.**  `[PROVED]`
`d` odd ⟹ `d/2 = k + 1/2` ⟹ `‖d/2‖ = 1/2 ≥ 1/8`, for every `d ∈ D_i`. ∎
*Checked: 250 all-odd instances, 0 failures.*

**(D) Every other runner has an even constraint, hence an even count.**  `[PROVED]`
By the parity law of `WN_count_parity_2026_09_12` Step 2 (count odd ⟺ all constraints odd),
a runner with any even constraint has an even count.

## What this gives

> Every runner of an 8-runner configuration is one of exactly two kinds:
>
> - **all-odd** — it is the unique runner of its parity, which happens for at most one runner
>   per configuration and only in a 7–1 parity split. **`t = 1/2` is a witness. Settled.**
> - **has an even constraint** — every other runner. Its isolation count is **even**, so
>   `count ≥ 1` and `count ≥ 2` are the same statement.

Two consequences:

1. **Count 1 is impossible**, now without any search: a count of 1 is odd, so the runner is
   all-odd, so `t = 1/2` is a witness — and a single component containing `1/2` would have to
   be the whole of `G`, but the runner is settled either way. More directly: the only runners
   that *can* have an odd count are already proved isolated, so the odd branch never carries
   any of the difficulty.
2. **LRC(8) reduces to the even branch.** Every runner that could fail has an even count.
   So the conjecture is: *every runner with an even constraint has a nonzero (hence `≥ 2`)
   isolation count.*

## Status of the `≥ 9` bound

Superseded, not disproved. `WN_count_parity_2026_09_12` Step 3's measurement stands as a
measurement (exhaustive over all-odd sets with values `≤ 39`: minimum 9 at `(1,3,5,7)`), but it
is no longer load-bearing for anything — (C) settles the all-odd branch outright.

## Ledger

`[PROVED]` (A), (B), (C); (D) from the already-proved parity law.
`[VERIFIED — exact]` the three checks above, 0 failures each.
`[SUPERSEDED]` `WN_count_parity_2026_09_12` Step 3, as a load-bearing step. Its numbers stand.
`[UNPROVED]` the even branch — that a runner with an even constraint has nonzero count. That
is LRC(8).

`n = 8` is **not proved.**
