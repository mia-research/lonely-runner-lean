# n = 8 — proof plan

2026-09-13. Eight runners, distinct constant speeds, circle of circumference 1, threshold 1/8.

**What governs.** `PROOF_CANDIDATE_v3.md` is canonical. `HANDOVER_2026_09_13_v1.md` explains and
guards it, and its §6 register is binding. This file is the order of work, not an argument; it
promotes nothing.

---

## 1. The seven parts

| | part | status | in Lean |
|---|---|---|---|
| 1 | Loneliness is a two-neighbour condition; there are no end runners | `[PROVED]` | `lonely_iff_flanks`, `_first`, `_last` |
| 2(a) | All eight lonely ⟺ every gap is exactly `1/8` | `[PROVED]` | `gaps_all_eq` |
| 2(b) | The instants are `{δt} = r/n`, `gcd(r,n) = 1`; `φ(n)` of them | `[PROVED]` — `lrc_ap_phi_n_law_v1` Thm 3.1(a)(b) | — (cited, not re-derived) |
| 3 | `d_min` from the two neighbours is exact; nothing before `1/(8·d_min)` | `[PROVED]` | `nearest_below`, `nearest_above`, `before_floor` |
| 4 | One window, `u ∈ [1/8, 7/8]` | `[PROVED]` | `window_iff` |
| 5 | Every other runner's lap count and phase at every `u` | `[PROVED]` | `reading_clear_iff`, `lap_and_phase` |
| 6(a) | The AP part is a permutation: `n` runners on `n` distinct eighths | `[PROVED]` | `ap_reference` |
| 6(b) | The deviation displaces runner `k` by `e_k·r/d` eighths | `[PROVED]` | `displacement` |
| 6(c) | The instant survives iff whole eighths **and** the map is a bijection | `[PROVED]` | `survives_of`; `int_of_pairwise_sep`, `not_dvd_of_sep` |
| **7** | **The claim: the procedure returns the moment** | **`[CLAIMED]`** | **not stated, deliberately** |

**One external debt in the whole construction**, and it is the owner's own prior work: 2(b).

## 2. Lean — the target list is complete

`LonelyRunner/LRC/Construction8/` on branch `n7-case-a5-repr-cases`. **81 theorems, zero `sorry`,
no `native_decide`, no `unsafe`, no `admit`, every one `[propext, Classical.choice, Quot.sound]`.**

| file | count | contents |
|---|---|---|
| `Parts.lean` | 5 | parts 2(a), 3, 6(b) |
| `LemmaPass.lean` | 24 | the supporting lemmas of §3 |
| `Coords.lean` | 10 | the `(a,m)` condition, stretch overlap, wide-gap, clear-interval bound |
| `Reference.lean` | 4 | 6(a); 6(c) forward |
| `Gaps.lean` | 6 | cyclic gaps, conservation, the adjacent bridge |
| `Sorted.lean` | 4 | the sorting permutation, equal spacing from pairwise separation |
| `Grid.lean` | 3 | the regular `n`-gon, explicitly |
| `Integrality.lean` | 8 | 6(c) converse — integrality and the bijection |
| `Flank.lean` | 14 | part 1, both directions, all indices |
| `Window.lean` | 3 | parts 4 and 5 |

**Every target of this list is complete.**

| target | state |
|---|---|
| 1. **6(a)** | **done** — `ap_reference` |
| 2. **6(c)** | **done, both directions** — `survives_of`; `int_of_pairwise_sep`, `not_dvd_of_sep` |
| 3. **part 1** | **done, both directions, interior and both ends** — `lonely_iff_flanks`, `_first`, `_last` |
| 4. **part 4** | **done** — `window_iff` |
| 5. **part 5** | **done** — `reading_clear_iff`, `lap_and_phase` |

So parts 1, 2(a), 3, 4, 5, 6(a), 6(b), 6(c) are all formally verified. Part 2(b) stays cited to
`lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b) — the construction's only external debt, and the owner's
own prior work.

**Part 7 is not stated in Lean, and stays unstated.** No `theorem claim`, not even with `sorry`.
Writing it down invites an attack with whatever machinery closes it.

**Infrastructure built along the way**, needed by more than one target and not on the original
list: the cyclic gap structure and its conservation law (`Gaps.lean`); the sorting permutation, so
a pairwise hypothesis reaches the gaps (`Sorted.lean`); and the regular `n`-gon in explicit form
(`Grid.lean`).

**Still owed, and small.** `wide_gap_core` and `wide_gap_end` are index-free; stating them on
`Fin 8` speeds needs `nearest_below`/`nearest_above` and part 1, all of which now exist.

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
| **the relay / stretch-ratio fracture** | **Refuted, four counterexamples.** (i) `s = 11/5` is in the way at `u = 7/8` on its **second** lap — `‖(11/5)(7/8)‖ = 3/40 < 1/8` — so `s_end ≤ 9/7` fails. (ii) The hop bound `9/7` is the lap-1-against-lap-1 case only; in general it is `(8k+1)/(8k′−1)`, giving `17/7` and `25/7` at later laps. (iii) Seven readings supply **24 stretches**, and an observed chain ran **11 hops** with readings recurring — a relay is built from stretches, not runners, so `N` runners do not give `N−1` hops. (iv) `s = 8` is in the way at **both** ends by itself (`8·(1/8) = 1`, `8·(7/8) = 7`), so the ends do not force two readings and there is no ratio to accumulate. Each successive draft corrected the bookkeeping and left all four in place. |
| **the `s = 8` runner count (Regime A pigeonhole)** | **Invalidated.** `s = 8` does fragment the window into 7 in-the-way zones and 6 clear gaps of `3/32` — that part is right. But "5 readings cannot fill 6 gaps" assumes one reading per gap, and both halves fail: readings **collaborate** on a single gap, and one reading has many stretches so it **serves several gaps**. A search over 300,000 draws of five readings closed **3 of the 6**, which is neither 0 nor 6 and refutes the counting directly. The conclusion (gaps survive) held throughout with margin; the mechanism did not. |

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

## 8. Supervisor review — handover §7 item 3, done 2026-09-13

Performed against the binding register and the label discipline. **No theorem changed.**

**Register.** All ten `Construction8` files scanned for the fourteen items. Clean — the single
grep hit is `LemmaPass`'s own sentence saying it uses none of them.

**Labels.** No file claims part 7, the Claim, `LRC(8)` or `intLRC`; every mention of part 7 is a
disclaimer. Parts 1–6 sit at `[PROVED]`, part 2(b) at cited, part 7 unstated. `Parts.lean` and
`LemmaPass.lean` — the two files predating this pass — lacked the explicit *nothing here states or
attempts part 7* line the eight newer files carry; added.

**Citation defects found, all pre-existing, all fixed:**

| | defect | resolution |
|---|---|---|
| `LemmaPass` | cited `SKETCH_v6.md`, superseded by v7 | repointed |
| `LemmaPass` | cited `LEMMAS_v1.md` L2 — **not on disk** | recorded in the header, not deleted: `LEMMA_L3_v2.md` also refers to it, so it existed once, and removing the reference would hide that a source is missing |
| `LemmaPass` | cited `LEMMA_L3_v1` for an argument `LEMMA_L3_v2` replaced | notes v2 is current and carries the elementary proof |
| `Gaps` | cited `GAP_FRAME_v1` §0; v2 is current | repointed, with §0's unchanged-ness stated so the citation can be checked |

**Module docstrings.** Every file carries its own scope note naming what it does *not* establish —
`Gaps` that its conservation is a telescoping identity until `p` is sorted; `Sorted` that it gives
the permutation but finishes neither target alone; `Grid` that the integrality step is separate;
`Coords` that `9/7` is the first-stretch case only. Those notes are the reason the tree cannot be
read as claiming more than it proves, and they should not be trimmed.

---

**n = 8 is not proved. Part 7 is the whole of what is open, and nothing in §3 produces a moment.**
