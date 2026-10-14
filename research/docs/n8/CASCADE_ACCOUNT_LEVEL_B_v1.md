# The complete account of the cascade — Level B: patterns of moves (v1)

2026-10-01. `CASCADE_DESIGN_v3` §8.3. Owner: *"Yes we are not looking at lean until the map is complete"*. Log E222.

**What Level B is.** How consecutive moves fit together, for every configuration, derived from Level A
(`CASCADE_ACCOUNT_LEVEL_A_v1.md`). Every item is a forced consequence of the definition. The check (§B.12) should pass
with no exception (M8). Notation as in A.0: positions `p = 8·s·t` (eighths of a lap); slot `l` is `(8l − 1, 8l + 1)`,
block `l` is `[8l + 1, 8l + 7]`; `ρ_k = (8k + 1)/(8k − 1)` for `k ≥ 1`. Readings are written by their speeds `s`.

Grades: `[derived]` (on paper here, from Level A and earlier B items; checked in §B.12); `[PROVED]` where Level A's
anchor carries it. No item is new Lean (owner's ruling).

---

## B.1 The setter as a latest exit `[derived from A.3]`

A crowd member `c` in slot `l_c` exits at `(8l_c + 1)/(8s_c)`. So **the next instant is the largest of these exits over
the crowd, and the setter is the member attaining it.** (A.3's `t + (1 − x_c)/(8s_c)` with `x_c = p_c − 8l_c`.) Among
members in one slot, the slowest exits last.

## B.2 Where every reading sits at an exit: the junction `[derived]`

Let `a` exit on lap `k`, at `τ = (8k + 1)/(8s_a)`. Reading `b` sits at `(8k + 1)·s_b/s_a`. So `b` is in slot `l` at `τ`
iff

  `s_a(8l − 1) < s_b(8k + 1) < s_a(8l + 1)`.

At an exit, each reading's slot or block is decided by its ratio to the setter alone. The left inequality is E125's
junction `J = s_b(8k + 1) − s_a(8l − 1) > 0` (`b` has entered); the right one says `b` has not yet left. On any grid
`s = n + δ`, both sides split exactly into the grid's part and the deviation's (E208).

## B.3 The run below the setter `[derived]`

At `a`'s exit on lap `k`, a slower reading `b` is in slot `k` iff `s_a/s_b < ρ_k` (the right inequality of B.2 holds
automatically for `s_b < s_a`). So **the slower readings in slot `k` form an unbroken run directly below `a` in speed:
every reading with speed in `(s_a/ρ_k, s_a)`.** Readings slower than the run sit at positions at most `8k − 1`, in an
earlier slot or block. Readings faster than `a` sit above `8k + 1`.

## B.4 A sweep step jumps to the bottom of that run `[derived]`

If the next move is a sweep (next setter slower, same lap `k`; A.6), the next setter is the **slowest** reading of B.3's
run: all of them are in slot `k` and by B.1 the slowest of a slot exits last. So a sweep step does not go to the next
slower reading; it goes to the bottom of everything within ratio `ρ_k` below the setter.

## B.5 Passages `[derived]`

A **passage** is a maximal sequence of consecutive sweep steps on one lap `k`. By B.3–B.4, it descends through readings
joined by consecutive ratios below `ρ_k` (each step's new setter has its own run below it). It ends at the first of:
- a reading whose next slower reading has ratio at least `ρ_k`, or which is the slowest reading: **the bottom of its
  lap-`k` cluster** (the maximal run with consecutive ratios below `ρ_k`, E203). By A.6's `sweep_stop_persists`, a ratio
  that stops a sweep on lap `k` stops it on every later lap;
- a move whose next setter is on another lap, because some crowd member there exits later (B.1): a **bridge**.

## B.6 Bridges `[derived]`

At a passage's end the next move is the landing or a bridge:
- **bridge up**: the latest exit belongs to a faster reading, in a later slot (A.6). By A.5 it entered during the last
  move or is a re-entry;
- **bridge down**: the latest exit belongs to a slower reading below the run, in an earlier slot.
Between bridges up the setter's rank in speed strictly falls (sweeps and bridges down go to slower readings): a
description of order, never a budget (map §6 F1).

## B.7 The queue `[derived from A.5]`

At a move from `t` of length `D`, a reading `q` clear at `t` reaches its next entering edge after `T_q`, its distance to
that edge divided by `8s_q`. **The queue front** is the clear reading with the least `T_q`. Then `q` is in the next crowd
iff it is in a slot at `t + D` (A.5). In the usual case, `T_q < D < T_q + 1/(4s_q)`: it entered and has not left (a slot
lasts `2/(8s_q) = 1/(4s_q)`). If `T_q + 1/(4s_q) ≤ D`, it **passed through** the slot within the move (A.11). A fast
reading can also cross later slots within one move; A.5's general form covers that.

## B.8 The conveyor: gap B4 answered `[derived]`

By B.1 applied at the new instant, **the next setter is the member of the next crowd with the latest exit**, and a member
in slot `j` exits at `(8j + 1)/(8s)`. For an arrival that is entry time plus `1/(4s)`. Hence:
- **the next setter is the queue front iff the front is in the next crowd (it did not pass through) and no other member
  of the next crowd exits later.**
- An arrival `q` exits later than the front `f` iff `e_q − e_f > 1/(4s_f) − 1/(4s_q)`: its entry lag (both entries into
  the slots they occupy at the new instant) exceeds the difference of their stays in the slot. The lag is at least 0,
  because the front reaches an entering edge first, **unless the front itself lapped**: it passed through a slot and
  entered the next within the move, so its current entry is later than its first. The check found 35 such moves, all
  in the late shapes. Where the lag is at least 0:
  - **any arrival slower than the front outlasts it** (the right side is negative, the lag is not);
  - an arrival faster than the front outlasts it only by entering late enough: lag above `1/(4s_f) − 1/(4s_q)`.
- So the conveyor (E204) breaks exactly when the front is not in the next crowd (it passed through, or nothing it could
  reach arrived), or a slower reading arrived, or a faster arrival entered late enough, or a re-entry outlasts the
  front.
- (A first draft of this item said "only by being slower". That is false for a faster arrival entering late. It was
  corrected while the check was being designed, before it ran; log E222.)

## B.9 The end of the chain `[derived from A.5]`

The move from `t` ends the chain (its end is the landing) iff **no reading is in a slot at `t + D`**:
- every reading clear at `t` either has not reached its entering edge (`T_q ≥ D`) or has passed through;
- no crowd member has re-entered.

In particular, if the queue front has `T_front ≥ D`, nothing arrives: **a gap in the arrivals** (E204). The front passing
through (with everything behind it also clear at the end) is the only other way the chain can end. Both occur. Of the
landings after at least one move: every 7-set ≤ 20, 27,213 no arrival and 1,102 passed through; fine shapes, 515 and
30; late band shapes, 2,927 and 2,473 (E222; records, not a law). At that exit the setter is the bottom of its lap-`K` cluster (A.8).

## B.10 The first move `[derived from A.10]`

The chain starts at the bound with the captures as its crowd. A capture `d` sits in slot `l = round(d/(8m))`, exits at
`(8l + 1)/(8d)`, and by B.1 the first setter is the capture with the latest exit. With no captures the bound is the
landing.

## B.11 What Level B does not say

- Which patterns occur for a given arrangement: how the chain depends on the speeds is Level C (walls), and placement by
  grid plus deviation is Level D.
- Why a chain ends: gaps D2–D5.
- Nothing in A or B forbids a reading setting moves on several laps (revisits, E203). No law about revisits, passages
  per chain or move counts is claimed. Those counts are data (E203–E204), not part of the account.

---

## B.12 The check (M8)

`LonelyRunner/experiments/nN/redo/cascade_level_b_check_v1.py`, exact, on every move of every chain:
- B.1: the next instant is the largest `(8l_c + 1)/(8s_c)` over the crowd, and the setters attain it;
- B.2: every reading's slot or block at the setter's exit from B.2's inequalities equals the in-the-way test;
- B.3: the slower readings in the setter's slot at its exit are exactly those with ratio below `ρ_k`;
- B.4: at every sweep the new setter is the slowest of that run;
- B.5–B.6: at every move that is not a sweep, the run below the current setter is empty (a cluster bottom), or the next
  setter exits later than the run's bottom; at the landing the setter is a cluster bottom;
- B.7–B.8: the next setter is the latest exit of the next crowd; "the next setter is the queue front" holds exactly when
  B.8's condition holds; every break is one of B.8's four kinds (front not in the next crowd; a slower arrival; a faster
  arrival entering late enough; a re-entry outlasting the front); every slower arrival outlasts the front;
- B.9: at the last move every clear reading either does not reach its entering edge or passes through, and nothing
  re-enters;
- B.10: the first setter is the capture with the latest exit.

Populations as Level A: every 7-set of readings ≤ 20; 1,000 seeded fine shapes; the 5,400 late band shapes. Pass
condition: 0 failures on every item. Result: log E222.
