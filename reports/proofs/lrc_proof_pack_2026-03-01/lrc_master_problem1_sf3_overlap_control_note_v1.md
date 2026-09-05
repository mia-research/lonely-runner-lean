# Master Problem 1 SF3 Overlap-Control Note (v1)
**Date:** 2026-03-07  
**Purpose:** first theorem note for SF3.2, the hard subclaim in the distributed safe-fiber budget route.

## 0) Position in the program
Route SF3 rewrites MP1.7 as:

`sum_{j in S} N_j >= n`

where `S` is the set of safe event cells in a `B_div` component `C`.

The remaining difficulty is not existence of safe cells. It is **overlap control**:
many obstruction runs might terminate into the same short safe event cell, so naive counting of one safe opening per run can overcount the safe occupancy.

This note isolates that obstruction precisely.

## 1) Setup
Let `C` be a `B_div` component, decomposed into event cells

`J_1, ..., J_m`

with occupancies

`N_1, ..., N_m`.

Let the maximal obstruction runs in `C` be

`R_1, ..., R_q`

in their natural order along the event path.

By MP1.6, each `R_i` ends either:
- at the boundary branch, or
- at an interior exit attached to a theorem-controlled safe opening.

So each interior-ended run determines at least one safe event cell immediately following its terminal obstruction cell.

## 2) The overlap-collapse problem
Naive counting would say:
- each run contributes one safe opening,
- therefore there should be many safe cells.

The diagnostics already show this is too weak:
- `n_safe_cells >= n` fails often,
- yet `B_safe` remains large.

So the correct statement must be weighted:
- a few safe cells may carry large occupancy,
- but repeated run endings into the **same** small safe block are the real danger.

## 3) External-update input adopted
The external draft in [lrc_proofs.md](/Users/trentpalelei/Downloads/lrc_proofs.md) is not adopted as a theorem proof, but it does isolate the right obstruction model:

> overlap collapse can only happen if the exposed residue/coset at one run end is quickly re-covered by other runners in a way that persists across successive exits.

Call this the **permanent-cover obstruction**.

This is useful and consistent with SF3.2.

## 4) Candidate reduction lemma

### Lemma SF3.2-R1 (overlap collapse -> permanent-cover chain)
Suppose `k >= 2` successive maximal obstruction runs

`R_i, R_{i+1}, ..., R_{i+k-1}`

all discharge into the same safe event-cell block `B_safe^*` of total occupancy `W`.

Then the exposed residue or coset element created at each run end must be re-covered before the path leaves `B_safe^*`.

Consequently, there exists a chain of runners

`e_1, e_2, ..., e_t`

such that each newly exposed object is inherited by the next coverer without producing a new disjoint safe occupancy block.

Interpretation:
- repeated counting collapse implies a genuine cover-inheritance mechanism,
- not just accidental adjacency of safe cells.

### Proof sketch
If a run end produced a genuinely new safe block disjoint from the previous ones, then occupancy would accumulate and there would be no overlap collapse.
So the only way multiple run ends can be absorbed into the same short safe block is if the exposed object from one run is re-covered quickly enough that the path returns to obstruction without generating a new disjoint occupancy contribution.
Iterating this over successive runs yields a cover-inheritance chain. □

## 5) The real hard subclaim

### Lemma SF3.2-R2 (bounded permanent-cover lifetime)
Any permanent-cover chain for a fixed residue/coset element has bounded lifetime along the event path.

Candidate reasons:
1. A unit runner can only cover a fixed residue for a bounded interval of floor states before its own event changes the covered pair.
2. A non-unit runner can only cover a fixed subgroup coset pattern for a bounded interval before a coset transition or transparency event occurs.
3. Once a coverer changes state, either a new safe opening appears or the burden transfers to another runner, which can happen only finitely many times before accumulating new safe occupancy.

This is the first serious theorem target for SF3.2.

Unit-side theorem note now attached:
- `lrc_master_problem1_sf3_unit_permanent_cover_note_v1.md`
- proved content: for a fixed residue, a unit runner covers only two consecutive floor states modulo `n`, so any single-runner unit cover episode has bounded lifetime.

Non-unit-side theorem note now attached:
- `lrc_master_problem1_sf3_nonunit_permanent_cover_note_v1.md`
- proved content: a non-unit runner supports each fixed residue and each fixed support coset on only one two-state floor block; for `gcd(e,n) >= 3` these blocks are separated by transparent gaps.

So the non-unit analogue is now also packaged at the single-runner level.

## 6) What this would buy
If SF3.2-R2 is proved with explicit overlap constant `K`, then:

- each cluster of repeated run endings contributes at least one safe block of occupancy comparable to the spacing budget,
- clusters can overlap only `K` times,
- total safe occupancy is bounded below by

`(certified safe-opening mass + boundary safe mass) / K`.

That is exactly the kind of statement needed for MP1.7.

## 7) Immediate theorem-writing direction
The runner-type specialization is now done:

1. **Unit permanent-cover bound**
   - isolated in `lrc_master_problem1_sf3_unit_permanent_cover_note_v1.md`
   - status: single-runner bound proved.

2. **Non-unit permanent-cover bound**
   - isolated in `lrc_master_problem1_sf3_nonunit_permanent_cover_note_v1.md`
   - status: single-runner bound proved.

So the next theorem target is the transfer layer:

3. **Chain-transfer control**
   - bound how many times a fixed exposed object can be handed from one coverer to another inside one short safe block.

Then combine the three ingredients into a bounded-overlap theorem for the whole event path.

## 8) Status
`OPEN-PROGRAM-TARGET`, with both unit and non-unit single-runner subclaims now packaged.
