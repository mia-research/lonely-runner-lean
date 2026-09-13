# The claim of §7.3 is false

2026-09-13. Scripts `experiments/nN/failure_hunt_v1.py`, `experiments/nN/failure_laps_v1.py`.

**This refutes the manuscript's open claim. It does not refute LRC(8), which is a theorem
(Rosenfeld 2025) and is untouched by anything below.**

---

## 1. The claim

> **MANUSCRIPT_v4 §7.3, Claim.** For every arrangement and every runner, the procedure
> returns the moment.

with, from §7.1:

> For each runner: form `d_min` from the two speed-neighbours; form the window
> `u ∈ [1/8, 7/8]`; read the other six inside it; return the first point at which all are
> clear.

---

## 2. The counterexample

**Speeds `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`** — eight distinct positive
integers, gcd `1`, no runner pinned at `0`.

**Subject: the runner at speed `1`.** Its speed-neighbour is `1975`, so `d_min = 1974`. Its
six readings are

    8/3,  7/2,  208/47,  34/7,  6,  23/3

and its window is `u ∈ [1/8, 7/8]`, in time `t ∈ [1/15792, 1/2256]`.

> **There is no instant in that window at which the runner is lonely.**
> The procedure does not return.

It *is* lonely at `t = 67/110544`, which is `u = 219/184 ≈ 1.19` — **in the second lap**,
outside the window the procedure searches.

### How it was found

Not by enumeration. The procedure's verdict for a runner depends only on its reading vector,
and **any multiset of positive reals is realisable as one runner's differences** — put the
subject at `0` and the others at those offsets. So the search ran over reading vectors
directly, with no bound on speeds and no integrality, annealing on the number of clear
components. The integer speed set above was reconstructed afterwards by clearing
denominators (`lcm(3,7,2,47) = 1974`).

---

## 3. Verification

Four independent routes, exact rational arithmetic throughout, plus one by hand.

| | method | result |
|---|---|---|
| 1 | reach-walk over sorted zones | window covered |
| 2 | every zone endpoint in the window tested for strict containment — 46 points | none clear |
| 3 | direct loneliness test **from the speeds**, 400,001 exact rational points | none lonely |
| 4 | from-scratch interval union, touching intervals not merged | one open component `(1/17296, 3/5264)` strictly containing `[1/15792, 1/2256]` |

By hand: the reading `23/3` at `u = 1/8` has phase `23/24`, circle distance `1/24 < 1/8`, so
even the window's left endpoint is blocked — and blocked from *strictly inside* a zone
running from `21/184 < 1/8`, so the boundary discipline is satisfied and the endpoint is not
clear-by-openness.

**A bug found during check 4, recorded.** The first version of that check clamped zone left
endpoints to the window start, which destroyed exactly the information the test needed and
reported the window as *not* covered. The clamp was the error. Without it, check 4 agrees
with the other three.

---

## 4. It is not an `n = 8` accident

Searching reading vectors at other orders with a modest budget (60 restarts each):

| `n` | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|
| failures found | 0 | 1 | 1 | 1 | 0 | 0 |
| lap that recovers | — | 2 | 2 | 2 | — | — |

Absence at `n = 5, 9, 10` is a statement about the search budget, not about those orders.
**Every failure found is recovered in lap 2.**

---

## 5. What this does and does not touch

**Refuted.** §7.3's Claim, as stated: one window does not always suffice.

**Untouched.** LRC(8), which is a theorem. The subject above is lonely at
`t = 67/110544`; the framework simply does not look there. That the counterexample is
lonely later is also a consistency check on this work — had it not been, the arithmetic
would have been wrong.

**Untouched.** §7.2, soundness. A returned `u` is still correct; `procedure_sound` is
unaffected. What fails is termination, not correctness.

**Untouched.** §§1–6 and §9, all of which are proved and machine-checked, and none of which
depends on §7.3. The negative results of §6 stand.

---

## 6. Consequences for the manuscript

These are corrections of fact, not editorial preferences.

1. **§7.3** presents the Claim as open — "It is not proved". It is now **false**, and
   an explicit counterexample exists.
2. **§7.2's closing line**, "the claim of §7.3 implies LRC(8)", stays true as an implication
   but is no longer a route: its hypothesis is false.
3. **§10**, "Not established. The claim of §7.3, and therefore LRC(8)" — the first half
   becomes "refuted", not "not established".
4. **§7.3's evidence** — 21,600 instances and the `v_8 ≤ 40` sweep, zero failures — is not
   wrong. The counterexample has `v_8 = 15135`, far outside both. The evidence was bounded
   and said so; the bound was where the failure lived.
5. **A corrected claim is available** and is worth stating in place of the old one: every
   failure found so far is recovered in the **second** lap. Whether "the procedure returns
   within `K` windows" holds for a fixed `K` is open, and is a sharper question than the
   one it replaces.

**This is the owner's call, and nothing in the manuscript has been changed.**

---

## 7. Addendum — does an AP or grid instant rescue it?  *(owner's question)*

Four checks on the counterexample `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`.

### The grid is never formed at all

`ConstructionN.isolation_iff_coprime` decides this: global isolation happens **iff** the
relative-speed residues mod `n` are all distinct. From the failing runner they are

    {0, 0, 0, 4, 4, 5, 6, 6}

— three zeros, two fours, two sixes. They collide from every runner's frame. **So this speed
set never forms the 8-grid, at any time.** There is no grid instant to find, and that is a
theorem about this configuration, not a search result.

### The AP's own instants are blocked, and stay blocked through lap 2

| lap | `u = 1/8+k` | `3/8+k` | `5/8+k` | `7/8+k` |
|---|---|---|---|---|
| 1 (`k=0`) | blocked | blocked | blocked | blocked |
| 2 (`k=1`) | blocked | blocked | blocked | blocked |
| 3 (`k=2`) | **clear** | **clear** | blocked | blocked |

In lap 1 each is blocked by a different reading: `23/3` at `1/8`, `8/3` at `3/8`, `6` at
`4/8`, `34/7` at `5/8`, `7/2` at `7/8`. **The `φ(8)` AP instants do not recover until the
third lap.**

### Lap 2 does work, but not at a coprime spine point

Lap 2 has 12 clear instants, the first at `u = 219/184`. Among grid points `p/8 + k`, the
clear ones are `7/4, 17/8, 19/8, 31/8` — and `7/4 = 14/8` has `gcd(6,8) = 2`, a
**non-coprime** grid point. Simple rationals also work in lap 2: `6/5`, `9/7`, `14/11`.

`219/184` has denominator `184 = 8 × 23`, and `23` is the denominator-free part of the
reading `23/3` — the reading that blocks `u = 1/8`. The instant that rescues the runner is
set by the reading that defeated it.

### Only one runner fails

| runner | speed | `d_min` | verdict |
|---|---|---|---|
| 0 | 1 | 1974 | **does not return** |
| 1–3, 6, 7 | 1975, 5265, 6910, 11845, 15135 | — | returns at `u = 1/8` |
| 4 | 8737 | 852 | returns at `u = 1917/12796` |
| 5 | 9589 | 852 | returns at `u = 71/564` |

Seven of eight return, six of them at the first spine point. Part 7 is stated per runner, so
one failure refutes it — but the arrangement is not pathological as a whole.

### What this means for a repair

The two natural repairs need different budgets:

- **"search the full window of laps `1…K`"** needs `K ≥ 2` here.
- **"search the spine points `p/n` of laps `1…K`"** needs `K ≥ 3` here.

Neither is rescued by the grid, which this configuration never reaches.
