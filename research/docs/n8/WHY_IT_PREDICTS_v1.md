# Why the prediction works — and the bound that falls out of asking

2026-09-13. n = 8, individual isolation, threshold 1/8.

Written after the instruction: *when you hit a problem, ask why you can predict it.* Applied to
the open question "is the witness lattice `L` bounded", the inversion produces the structure the
direct attack did not.

---

## 1. Why a witness exists at all

Normalised: find `u ∈ [1/8, 7/8]` with `‖s_j u‖ ≥ 1/8`, where `s_1 = 1`. On lattice `L` the
candidates are `u = p/(8L)` with `p ∈ [L, 7L]` — about `6L` of them — and each constraint admits
a `3/4` fraction. Expected witnesses on lattice `L`:

    ~ 6L · (3/4)⁷  ≈  0.8 L

**The pool grows with `L` while the difficulty does not.** That is the mechanism, and it is why
the search terminates in practice. It also says a witness should usually appear by `L = 2`, which
matches the measured 80%.

## 2. When a lattice is entirely dead  `[PROVED]`

`‖s·p/(8L)‖ = 0` for **every** `p` exactly when `8L │ s`. So

> **lattice `L` is unusable ⟺ some `s_j ≡ 0 mod 8L`.**

Two consequences, both immediate:

- `L = 1` is dead ⟺ some `s ≡ 0 mod 8` — which is precisely the blocking condition. The spine is
  never partly damaged; one blocker kills all four points at once.
- **If `8L > max s`, no `s_j` can be divisible by `8L`, so `L` is live.** Hence

      first live lattice  ≤  ⌊ max(s)/8 ⌋ + 1                                    ∎

The dead lattices are a **divisor set** — the `L` dividing some `s_j/8` — which is finite and
typically tiny.

## 3. The witness sits on the first live lattice, or barely past it  `[VERIFIED — 12,000]`

| `L` − (first live lattice) | count | share | cumulative |
|---|---|---|---|
| **0** | 10,556 | **0.8797** | 0.8797 |
| 1 | 1,089 | 0.0907 | 0.9704 |
| 2 | 337 | 0.0281 | 0.9985 |
| 3 | 18 | 0.0015 | **1.0000** |

Never more than 3 past. The worst case found earlier —
`(175,180,263,270,276,277,296,312)`, r5 — has dead lattices `1, 2, 3, 4, 6` and its witness at
`L = 7`, one past the largest dead one.

## 4. The open question, decomposed

The bound on `L` now splits in two, and half of it is proved:

| piece | status |
|---|---|
| first live lattice `≤ ⌊max(s)/8⌋ + 1` | **proved** (§2) |
| gap from first live to witness `≤ 3` | **observed**, 12,000 instances, 88% zero |

So what remains is not "is `L` bounded" but **"how far past the first live lattice can the witness
be forced?"** — a much smaller question, on a quantity that was 0 in seven cases out of eight.

And §1 says why it should be small: on a live lattice the pool is `~6L` and the admitted fraction
`~(3/4)⁷`, so the expected count of witnesses exceeds 1 almost immediately.

## 5. Method note

The direct attack — "bound `L`" — produced two candidates (`L ≤ 6`, `L ≤ 7`) and both died within
minutes of adversarial search. The inverted question — "why does this work when it works" —
produced the dead-lattice criterion, which is proved, and reduced the unknown to a gap that is
zero in 88% of cases.

Recorded because the inversion, not more search, is what moved it.

## 6. Status

`[PROVED — arithmetic]` §2's dead-lattice criterion and the `max(s)/8` bound on the first live
lattice.
`[VERIFIED — 12,000]` §3's gap distribution.
`[OPEN]` a bound on the gap.

**n = 8 is not proved here.**
