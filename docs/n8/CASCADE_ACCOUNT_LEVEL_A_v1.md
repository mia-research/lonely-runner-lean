# The complete account of the cascade — Level A: the step (v1)

2026-10-01. `CASCADE_DESIGN_v3` §8.2, approved by the owner: *"yes approved, start with the Level A catalogue"*. Log E221.

**What Level A is.** Everything one move of the cascade does, for every configuration, derived from the definition and
the proved lemmas. It is the definition unfolded. It is not progress on the obligation (map v3 §5), and every item is a
forced fact by design (map §6 F5: forced facts are checks, not findings). Its check (§A.13) should pass with no
exception; that is its test (M8).

**Grades.** `[PROVED]`: a Lean declaration, named with its file. `[derived]`: on paper here, from the definition and
earlier items. Every `[derived]` item is checked in §A.13 on exhaustive and seeded populations.

---

## A.0 Units and the definition

- A reading `d > 0` is a disparity (speed difference to the subject). At time `t` its **position** is `p_d(t) = 8·d·t`,
  in eighths of a lap. Positions advance linearly, each at its own speed: `p_d(t + Δ) = p_d(t) + 8·d·Δ`.
- **The slot of lap `k`** is the open interval `(8k − 1, 8k + 1)` of positions; **the clear block of lap `k`** is the
  closed interval `[8k + 1, 8k + 7]`. Every position lies in exactly one slot or one block.
- **In the way** (`MomentIterationN.inWay`, `Cascade/Iteration.lean:35`): `circDist(d·t) < 1/8`, that is `p_d(t)` lies
  in some slot. The inequality is strict, so a reading exactly on an edge (position `8k ± 1`) is clear: the BSM boundary
  convention.
- **Lonely at `t`** (`Lonely`, line 39): every reading clear.
- **Next opening** (`nextOpening`, line 37): `(⌈d·t − 1/8⌉ + 1/8)/d`, the first time at or after `t` that the position
  reaches a leaving edge `8k + 1`.
- **The move** (`move`, line 42): from `t`, the latest next opening among the readings in the way at `t`, or `t` itself
  if none is.
- **The cascade**: the iterates of the move from the bound `t₀ = 1/(8m)`, `m` the least reading.
- **R-units**: `R = 8·m·t`, positions relative to the slowest reading: `p_m = R`.

---

## A.1 The move strictly advances, and no lonely instant lies inside it `[PROVED]`

- If some reading is in the way at `t`, its next opening is strictly later (`lt_nextOpening`, line 83), so the move is
  strictly later than `t`. Otherwise the move is `t` (`le_move`, line 121; `move_eq_self_or_opening`, line 257).
- A reading in the way at `t` stays in the way until its own next opening (`inWay_until_opening`, line 68).
- If the subject is lonely at some `s ≥ t`, the move from `t` is at most `s` (`move_le_of_lonely`, line 107). So
  **no lonely instant lies in `[t, move(t))`**.
- A fixed point of the move is lonely (`lonely_of_fixed`, line 165). The cascade's fixed point is its **landing**.
- The cascade arrives exactly when the subject is lonely at some positive time (`lonely_iff_run_ends`, line 772;
  `Spec/Doors.lean` `doors_agree` for the order-eight doors). That every run ends is the obligation.

## A.2 Every cascade instant is an opening `[PROVED]`

The move from `t` is `t` or the next opening of some reading in the way at `t` (`move_eq_self_or_opening`). At its next
opening a reading sits exactly on a leaving edge, `circDist = 1/8` (`circDist_at_nextOpening`, line 245), so it is clear
there. Hence **every instant of the cascade after the bound is `(8K + 1)/(8h)` for the move's setter `h` and a lap
`K ≥ 0`**: a candidate scale `h/(8K+1)` (Theorem 6.15's object). The bound itself is `1/(8m)`, the slowest reading's
opening on lap 0 (A.10).

## A.3 The setter and the length of the move `[derived]`

Write a crowd member `c`'s position as `8k_c + x_c` with `x_c ∈ (−1, 1)` (it is in slot `k_c`). It reaches its leaving
edge `8k_c + 1` after `(1 − x_c)/(8c)` (A.0, positions advance linearly). So:
- the move's length is `D = max over the crowd of (1 − x_c)/(8c)`;
- **the setter** is the crowd member attaining it: the one whose remaining distance to its leaving edge is largest
  **relative to its speed**. Several may attain it together (a tie): they exit at the same instant;
- the setter is exactly on its leaving edge at the new instant, hence clear (A.2).

## A.4 Where every reading is at the end of the move `[derived]`

At `t + D` each reading `r` sits at `p_r(t) + 8·r·D`. That is the whole step: a rotation of every position by its own
speed times `D`, read at the setter's exit. Every statement below about the next instant is this formula.

## A.5 Who is in the way after the move `[derived]`

The next crowd is exactly the readings in the way at `t + D` (A.0). Split by where each was at `t`:
- **an arrival**: a reading clear at `t` (position `x ∈ [1, 7]` in its block, up to whole laps) that is in a slot at
  `t + D`: `x + 8rD ∈ (8j − 1, 8j + 1)` for some `j ≥ 1`. It crossed an entering edge during the move and has not
  reached the next leaving edge;
- **a re-entry**: a crowd member that left its slot during the move, crossed its next entering edge `8k_c + 7` and is
  in that slot at `t + D`. It requires `D > (7 − x_c)/(8c)`: only a reading fast against the setter re-enters;
- nothing else: a crowd member that left and did not re-enter is in a block at `t + D`.

This is the general form. `SeparationN.transport` `[PROVED]` is its special case for a separation from a reading at the
centre of the slot (`c·t₀` a whole number, `D = 1/(8c)`): every reading in the slot afterwards crossed its entering edge
during the shift, and a slower one was an edge push.

## A.6 The lap of the next setter: the three move types `[PROVED]`

At the setter `a`'s exit on lap `k ≥ 0` (position `8k + 1`, `R = (8k + 1)/s_a`), let `b` be any reading in the way, in
its slot `l`. Readings are distinct, so `b` is faster or slower than `a`:
- `b` faster: `l > k` (`SweepBridge.lap_lt_of_faster`, `Spec/SweepBridgeN.lean:24`): **bridge up**;
- `b` slower: `l ≤ k` (`lap_le_of_slower`, line 36): **sweep** if `l = k`, **bridge down** if `l < k`;
- a sweep step needs `s_a(8k − 1) < s_b(8k + 1)`, a consecutive ratio below `ρ_k = (8k+1)/(8k−1)` (`sweep_ratio`,
  line 49); `ρ_{k+1} < ρ_k` (`sweep_ratio_mono`, line 55), so a gap that stops a sweep on lap `k` stops it on every later
  lap (`sweep_stop_persists`, line 60).

The next setter is one of these readings, so every move after the first has exactly one of the three types relative to
the previous setter (ties of setters aside: tied setters share the instant and the classification applies to each).

## A.7 The setter itself is never in the way at its own exit `[PROVED]`

`circDist_at_nextOpening`: the setter sits on its leaving edge, at distance exactly `1/8`. So the next setter is always a
different reading (A.6 applies to `b ≠ a`).

## A.8 The landing and its certificate `[PROVED]` with one `[derived]` clause

The landing `τ` is a fixed point, hence lonely (A.1). By A.2 it is the opening of its setter `h` on a lap `K`:
`τ = (8K + 1)/(8h)`. At `τ` every other reading `d` sits at `(8K + 1)·d/h`, in a clear block `[8k_d + 1, 8k_d + 7]`. For
whole-number readings this is the band condition `d·(8K + 1) mod 8h ∈ [h, 7h]` (`OrderEightN.lonely_eight_of_opening`,
`Spec/OrderEightCasesN.lean:302`): **the certificate `(h, K, (k_d))`**.

`[derived]` **The setter is the slowest of its lap-`K` cluster.** If `K ≥ 1` and the reading `d` next below `h` in speed
had `s_h/s_d < ρ_K`, then `d`'s position `(8K + 1)·s_d/s_h` would lie in `(8K − 1, 8K + 1)`, in the way at the landing,
a contradiction. If `K = 0` then `h = m`: an opening of `h ≠ m` on lap 0 is `1/(8h) < 1/(8m)`, before the bound, and
moves never go below the bound (A.1).

## A.9 The landing is the first lonely instant at or after the bound `[PROVED]`, a by-product

`first_isolation_of_fixed` (line 213). Recorded because it is true; the owner's ruling (E200) is that nothing in the
argument rests on it.

## A.10 The bound and its captures `[derived]`

At `t₀ = 1/(8m)` the slowest reading is at position 1, on its leaving edge, so clear. Reading `d` is at position
`d/m` (in R-units `R = 1`). It is in the way iff `d/m mod 8 ∈ (7, 8) ∪ [0, 1)`: in grid slot 7 (just before a multiple of
8) or slot 0 (just past one) of the slowest reading's own grid. These are the **captures**, the first crowd. If there
are none, the bound is the landing (R1 when the spread is at most 7: every `d/m ∈ [1, 7]`).

## A.11 The BSM edge cases `[derived]`

- A reading exactly on an edge at an instant is clear (A.0). This happens only by an exact coincidence of positions; it
  never happens for readings in general position (fine shapes), and happens in whole-number sets.
- Two crowd members can tie for the setter (A.3); the move is the same instant either way.
- A fast reading can enter and leave a slot within one move (passing through): it is not in the way at the move's end and
  plays no part in the next step (A.5).

## A.12 What Level A does not say

It says what one move does in every configuration. It does not say which configurations occur in a chain, how moves
group into passages, bridges and relays (Level B), how the chain changes with the arrangement (Level C), or why the
chain ends inside the slow part's block (Level D, gaps D2–D5). In particular A.1's "that every run ends" is the
obligation, untouched here.

---

## A.13 The check (M8: the derivation checked, not discovered)

`LonelyRunner/experiments/nN/redo/cascade_level_a_check_v1.py`, exact. For every move of every chain:
- A.1: the move is later; the clear set (computed without the cascade, `clear_set`) has no point in `[t, move(t))`; at
  the landing the least clear point at or after `t` is the landing;
- A.2: every instant after the bound is `(8K+1)/(8h)` for its setter `h`, `K` a whole number `≥ 0`;
- A.3: the setter attains `max (1 − x_c)/c` over the crowd, and the move's length equals it;
- A.4–A.5: the next crowd computed from A.4's formula and split into arrivals and re-entries equals the crowd computed by
  the in-the-way test; every re-entry satisfies `D > (7 − x_c)/(8c)`;
- A.6: the next setter's lap against the setter's lap and their speeds: faster gives a later lap; slower gives the same or
  an earlier lap; a sweep has ratio below `ρ_k`;
- A.7: the setter is clear at its own exit;
- A.8: at the landing the setter sits at `8K + 1` exactly, every other reading in a clear block, and the setter is the
  slowest of its lap-`K` cluster;
- A.10: the first crowd equals the captures `d/m mod 8 ∈ (7, 8) ∪ [0, 1)`.

Populations: every 7-set of readings ≤ 20 (77,520, exhaustive); 1,000 seeded fine shapes (least reading 1,000, spread
uniform in `[2, 20]`); the 5,400 late band shapes (a record population, used here only as a check: it carries the longest
relays). Pass condition: 0 failures on every item. Result: log E221.
