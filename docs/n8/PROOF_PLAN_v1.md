# n = 8 — proof plan

2026-09-13. Eight runners, distinct constant speeds, circle of circumference 1, threshold 1/8.

**What governs.** `PROOF_CANDIDATE_v3.md` is canonical. `HANDOVER_2026_09_13_v1.md` explains and
guards it, and its §6 register is binding. This file is the order of work, not an argument; it
promotes nothing.

---

## 1. The seven parts

| | part | status | in Lean |
|---|---|---|---|
| 1 | Loneliness is a two-neighbour condition; there are no end runners | `[PROVED]` | — |
| 2(a) | All eight lonely ⟺ every gap is exactly `1/8` | `[PROVED]` | `gaps_all_eq` |
| 2(b) | The instants are `{δt} = r/n`, `gcd(r,n) = 1`; `φ(n)` of them | `[PROVED]` — `lrc_ap_phi_n_law_v1` Thm 3.1(a)(b) | — (cited, not re-derived) |
| 3 | `d_min` from the two neighbours is exact; nothing before `1/(8·d_min)` | `[PROVED]` | `nearest_below`, `nearest_above`, `before_floor` |
| 4 | One window, `u ∈ [1/8, 7/8]` | `[PROVED]` | — |
| 5 | Every other runner's lap count and phase at every `u` | `[PROVED]` | — |
| 6(a) | The AP part is a permutation: `n` runners on `n` distinct eighths | `[PROVED]` | — |
| 6(b) | The deviation displaces runner `k` by `e_k·r/d` eighths | `[PROVED]` | `displacement` |
| 6(c) | The instant survives iff whole eighths **and** the map is a bijection | `[PROVED]` | — |
| **7** | **The claim: the procedure returns the moment** | **`[CLAIMED]`** | **not stated, deliberately** |

**One external debt in the whole construction**, and it is the owner's own prior work: 2(b).

## 2. Lean — done, and next in order

`LonelyRunner/LRC/Construction8/` on branch `n7-case-a5-repr-cases`. **39 theorems, zero `sorry`,
no `native_decide`, no `unsafe`, no `admit`, every one `[propext, Classical.choice, Quot.sound]`.**

| file | count | contents |
|---|---|---|
| `Parts.lean` | 5 | parts 2(a), 3, 6(b) — handover §7 item 2's cheap independent batch |
| `LemmaPass.lean` | 24 | the supporting lemmas of §3 below |
| `Coords.lean` | 10 | the `(a,m)` condition, stretch overlap, wide-gap, clear-interval bound |

**Next, in this order** — handover §7 item 2 names the first two:

1. **6(a)** — `k ↦ kr (mod n)` is a bijection for `gcd(r,n) = 1`, so the `n` runners occupy the
   `n` distinct eighths, pairwise at distance `≥ 1/n`. Needs `ZMod n` and `Nat.Coprime`.
   *Must not claim:* that anyone is lonely — that is part 1. That the instant is first.
2. **6(c)** — pairwise distances all `≥ 1/n` **iff** every `x_k = k·r + e_k·r/d` is an integer and
   the `x_k` are distinct mod `n`. The forward direction routes through `gaps_all_eq`; the
   normalisation `e₀ = 0` is what turns "differences are integers" into "each `x_k` is an integer".
   *Must not claim:* global isolation as such — that is this composed with part 1.
3. **Part 1** — the two-gap criterion. The cyclic-order argument is the work; state adjacency mod
   `n` so the end runners are not special.
4. **Part 4** — one window. Care with `Int.fract`; prefer routing through `coord_iff`, which has no
   `Int.fract` in its statement.
5. **Part 5** — the reading. Follows part 4.

**Part 7 is not to be stated in Lean.** No `theorem claim`, not even with `sorry`. Writing it down
invites an attack with whatever machinery closes it, which is the failure mode this plan exists to
prevent.

**Geometric wrappers still owed.** `wide_gap_core` and `wide_gap_end` are index-free; stating them
on `Fin 8` speeds needs `nearest_below`/`nearest_above`. Short, and worth doing when part 1 lands.

## 3. Supporting lemmas — what they are and what they are not

All proved. **None of them produces a moment**, which is why none closes part 7.

| | statement | source |
|---|---|---|
| the band identity | a reading is in the way at `u = 1/8` iff `dist(s, 8ℤ) < 1` | `GRID_THEOREM_v1` §1, `OWNER_PROCEDURE_v1` A8 |
| the grid theorem | a grid with `d_min = g` throughout: every moment is `1/(8g)` | `GRID_THEOREM_v1` §1 |
| the ceiling | no step above `7·d_min(i)` clears runner `i` | `SKETCH_v7` §7c |
| dead lattices | a divisor-closed set; `L_0` the first live one | `SKETCH_v7` §7c |
| window-widening | a set with period `1/h` meets any interval of length `≥ 1/h` | `SKETCH_v7` §7d |
| the wide-gap lemma | two adjacent speed gaps at or above `S/7` put the runner between them in Branch A; end runners need one | `WIDE_GAP_LEMMA_v1` |
| stretch overlap | lap `k` of `s` meets lap `k'` of `s'` iff `s/s' < (8k+1)/(8k'−1)`; `9/7` is `k = k' = 1` **only** | `Coords.lean` |
| the clear-interval bound | a reading reaches contiguously at most `1/(4s)`; no single reading closes a clear interval of the smallest | `Coords.lean` |
| the `(a,m)` condition | `‖d·a/m‖ ≥ 1/n` iff `m ≤ n·R` and `n·R + m ≤ n·m`, `R = (d·a) mod m` | `Coords.lean` |

## 4. Part 7 — stated correctly

> **Claim.** For every arrangement and every runner, the procedure — `d_min` from the two
> neighbours, the window, read the other **six** inside it — **returns the moment.**

It is a property of the procedure. No existential quantifier, no witness, no set, no complement.
`PROOF_CANDIDATE_v3` change (iii) removed the existence form; it must not come back.

**Already proved, from parts 1–6 alone:** `d_max ≤ 7·d_min` (35,467/35,467); every grid and
dilate (485/485); any runner with no `s_j` within 1 of a multiple of 8; the same at `u = r/8`.

**Checked where not proved:** 21,600 runner-instances across seven populations; exhaustively every
integer arrangement with `0 = v_1 < … < v_8 ≤ 20`, gcd 1 — 77,400 arrangements, 113,145 distinct
profiles, no failure to return.

**The obligation is per runner, not per configuration.** A runner outside the proved cases needs
its moment whether or not some other runner in the same arrangement is inside them. Over random
8-sets the share of **runners** outside is 56% at span 50 and 70% at span 5000. Any programme that
names one runner per configuration leaves the rest untouched.

**Scope choice, deliberate.** Confining to the first window is stronger than LRC(8), which asks
only for some time. Keeping the first-window form buys the closed time `t* = u*/d_min` from the two
neighbours; relaxing to any lap `k` would leave `t* = (k + u)/d_min` with `k` unsupplied. The
stronger form is kept on purpose and is marked as a choice, not mistaken for the target.

## 5. Routes closed — do not re-enter

Each was tried and failed for a stated reason. Re-entering one is the commonest failure here.

| route | why it is closed |
|---|---|
| measure, density, covering, complements | The AP's own reading inside the window is **four isolated points**. A bound on how little the in-the-way set can amount to is bounding a quantity that is zero in the case that matters. Dead at any strength. Also register items 4 and 5. |
| Weyl equidistribution | Register item 9. A real theorem, an outside debt, excluded from the candidate. |
| LRC at another order | Register item 10. Not circular, but a debt inside the conjecture. |
| primes / prime search | Register item 11. |
| the 2-adic ladder | `DYADIC_DEPTH_RESULT_v1` — depth grows with the speed bound. |
| bounding a lattice or denominator on a sample | Retracted three times: `q ≤ 2n` (handover §6), `L ≤ 6` and `L ≤ 7` (`WHY_IT_PREDICTS_v1` §5), and a `q ≤ 19` attempt. A bigger sample breaks each. |
| repairing one in-the-way reading and re-testing | Three closed forms each landed near 46%; in 3,234 of 3,234 the reading in the way after a repair is a different one. |
| the relay / stretch-ratio fracture | Refuted by counterexample: a reading of `11/5` is in the way at `u = 7/8` on its second lap, so `s_end ≤ 9/7` fails; the hop bound `9/7` is the first-stretch case only, with `17/7` and `25/7` at later laps; seven readings give 24 stretches and an 11-hop chain with readings recurring, so counting runners is not counting hops; and `s = 8` is in the way at **both** ends alone, so there is no ratio to accumulate. |
| the 5-against-6 count at `s = 8` | Not established. Readings collaborate on one gap, and one reading touches many gaps. |

**The superseded line.** `BRICK_LEDGER_v1`, `WHY_IT_PREDICTS_v1`, `FIRST_INTERVAL_PROOF_STATUS_v1`
and `LRC8_ANALYTIC_v1/v2` predate the handover and carry register vocabulary. Read them for
history; do not build on them.

## 6. Working rules

- The register of handover §6 is binding: fourteen items, none expressible in the construction.
- **BSM is mandatory.** In-the-way zones are **open**; their endpoints are clear. Open cells and
  boundary points are evaluated separately and touching zones are never merged. Closing the
  brackets makes `u = 1/8` in the way for `s = 7` and destroys the spine.
- Exact rationals. No floats, no cell midpoints, no sampling.
- **Six**, not five: `d_min` comes from the nearer neighbour; the second neighbour is read like
  everyone else. Handover §5 trap 3.
- Nobody is pinned. Positions are `frac(v_j·t)`; subtracting the subject's speed puts it at 0 and
  makes every lap count read zero.
- Grid ⊋ AP. Part 6 decomposes against an AP; part 2 is about grids.
- Versioning: never overwrite a `.md`; the Lean tree is the exception, edit in place and commit per
  change.

## 7. Done-checks

- Lean: `lake build LonelyRunner.LRC.Construction8.<module>` — the default target never enters
  `LRC/`, so a plain `lake build` is **not** a gate. Then `#print axioms` on each new declaration,
  expecting `[propext, Classical.choice, Quot.sound]`, and a scan for `sorry`, `native_decide`,
  `unsafe`, `admit`.
- Documents: the labels are the first thing to check and should not move — parts 1–6 `[PROVED]`,
  part 7 `[CLAIMED]` with `[VERIFIED]` counts, LRC(8) not proved.

---

**n = 8 is not proved. Part 7 is the whole of what is open, and nothing in §3 produces a moment.**
