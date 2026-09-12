# Working note — why an isolation count of 1 is impossible

2026-09-12. Scripts `experiments/n8/ok_worst_config_v1.py` + inline runs. Exact `Fraction`,
BSM good sets. Closes the "can a runner have exactly 1 event" item left open in
`WN_floor_search_2026_09_12`.

Working note. Data and three steps; the last is searched, not proved.

---

## Step 1 — `|D| ≥ 4`  `[PROVED]`

Runner `i` of an 8-runner configuration has 7 differences `v_j − v_i`. A value `w` appears
twice in `{|v_j − v_i|}` only if **both** `v_i + w` and `v_i − w` are runners, so each distinct
value occurs at most twice. Hence `#distinct ≥ ⌈7/2⌉ = 4`. ∎

Confirmed: over 320,000 runner-instances sampled from `[1..200]`, the smallest `|D|` observed
is exactly 4, e.g. `(38,71,95,104,113,137,142,170)` at runner 104, `D = (9,33,38,66)`.

## Step 2 — the parity law  `[PROVED + VERIFIED]`

`G = {t : ‖dt‖ ≥ 1/8 ∀d ∈ D}` satisfies `‖d(−t)‖ = ‖dt‖`, so `G` is symmetric under `t → −t`
and its components pair up unless a component is self-symmetric. A self-symmetric component
is centred at `t = 0` or `t = 1/2`.

- `t = 0` is **never** in `G` — `‖d·0‖ = 0 < 1/8`.
- `t = 1/2` is in `G` iff every `d` is **odd** — `‖d/2‖ = 1/2` for `d` odd, `0` for `d` even.

> **The count is odd ⟺ every constraint is odd.** Verified: 4000 constraint sets, 0
> disagreements.

## Step 3 — all-odd with `|D| ≥ 4` gives count `≥ 9`  `[VERIFIED — searched]`

Exhaustive over all-odd sets with `|D| ∈ {4,…,7}` and values `≤ 39` — **136,629 sets**:
minimum count **9**, attained at `D = (1,3,5,7)`. Random all-odd sets with values `≤ 199`
(60,000 of them): minimum 19, at `(1,5,11,23)` — larger values give more components, as the
periods shorten.

Count 1 occurs only at `|D| = 1`, `D = {1}`. For `|D| = 2,3` the all-odd minima are 3 and 7 —
both below 9, but neither size is realisable by Step 1.

## Consequence

For any runner of an 8-runner configuration: an **odd** count is `≥ 9`, an **even** count is
`≥ 2`. So **1 is unreachable, and so are 3, 5, 7.** The set of attainable counts is
`{0} ∪ {2,4,6,8,…} ∪ {9,11,…}`.

Which makes the distinction the owner flagged vacuous in a useful way:

> **`count ≥ 1` and `count ≥ 2` are the same statement** for 8 runners. Parity supplies the
> gap. The "floor is 2" observation is therefore not extra work beyond proving nonzero — it
> follows from it.

And `count ≥ 1` for every runner **is** LRC(8). That remains unproved; nothing here touches it.

## Ledger

`[PROVED]` Step 1; Step 2's parity law, with its derivation.
`[VERIFIED — exact]` Step 2's 4000-set check; Step 1's 320,000 runner-instances.
`[VERIFIED — searched]` Step 3, exhaustive for values `≤ 39` and sampled to `≤ 199`. The bound
`≥ 9` is not proved; a large all-odd set with few components is not excluded by argument.
`[UNPROVED]` `count ≥ 1`, which is LRC(8) itself.

`n = 8` is **not proved.**
