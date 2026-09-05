# LRC Gap Registry Master-Bucket Overlay v1

## Purpose

This note does **not** replace the existing gap registries.

It is an overlay that preserves the legacy gap IDs and source files while compressing the frontier into the two synthesis buckets identified in:

- [lrc_master_theorem_synthesis_v1.md](/Users/trentpalelei/Documents/Claude%20Library/lrc_master_theorem_synthesis_v1.md)
- [lrc_master_theorem_frontier_map_v1.md](/Users/trentpalelei/Documents/Claude%20Library/lrc_master_theorem_frontier_map_v1.md)

The audit rule is:

- old gap registries remain intact and citable;
- this overlay only reclassifies them into the master-theorem picture;
- no legacy identifier is deleted or renamed.

---

## The Two Master Buckets

### Bucket I — Torus-Intersection Geometry

Master question:

> If the irrational orbit closes up to a proper subtorus with full coordinate projections, must that subtorus hit the open safe box?

This is the ambient-torus version of “some safe state must exist.”

This bucket is currently the right home for the irrational intermediate-rank problem and any exposition gap that is really hiding that theorem.

### Bucket II — Dynamic Residue Transport Failure

Master question:

> Can the rational obstruction system maintain full residue support forever under the exact boundary handoff schedule, or must some residue eventually become uncovered?

This is the rational Case-2 core:

- one-divisible composite no-dropped-unit branches,
- B2/B3b,
- multi-divisible composite branches,
- O1 run-cap forcing,
- O2 quantitative safe-count forcing.

It is the residue-transport / finite-repair-capacity theorem problem.

---

## Legacy Registry Preservation

This overlay is keyed against the current live registry sources:

- [lrc_open_gaps_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_open_gaps_v1.md)
- [lrc_gap_status_n_all_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap_status_n_all_v1.md)
- [lrc_n_all_forced_conclusion_memo_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_n_all_forced_conclusion_memo_v1.md)
- [lrc_proof_v5_3_draft.md](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v5_3_draft.md)

Nothing below should be read as deleting any of their existing statuses.

---

## Legacy-to-Bucket Map

| Legacy item | Legacy statement | Bucket | Role inside bucket | Current status |
|---|---|---|---|---|
| `F` | Irrational branch large-class / `m=1` exposition gap | Bucket I | Surface manifestation of the missing torus-intersection theorem | Open / expository in draft form |
| Irrational intermediate-rank branch (`2 <= r <= n-2`) | Need `T ∩ B != empty` for proper subtori with full projections | Bucket I | Core theorem problem | Open |
| `A` — B3b | Composite `n = p^k`, `p >= 5`, one-divisible, both dropped non-units | Bucket II | Pure dynamic transport + non-unit sparsity problem | Open |
| `A` — multi-divisible composite | Composite Case-2 with multiple divisible/non-unit channels | Bucket II | Same transport problem with larger repair network | Open |
| `P6` | B2 floor-state achievability / target-state realization | Bucket II | Access-to-exposure sublemma inside the transport bucket | Open |
| `G4B-COMP-CAP` / complementarity cap | Blocked-run cap in composite rational regime | Bucket II | Local geometric / dynamic-transport manifestation | Open |
| O1 forcing (`D3`) | Bounded-time deficit overflow on blocked chains | Bucket II | Core forcing theorem candidate | Open |
| O2 safe-count forcing | Quantitative safe-cell / safe-fibre lower bound | Bucket II | Quantitative version of the same transport failure | Open |
| `CB` | Composite counting bridge for `x_0 >= phi(n)` in dropped-unit branches | Bucket II | Quantitative strengthening, not existential frontier | Open but non-blocking for LRC existence |
| `B` | `L = 2n` analytic writeup gap | Outside frontier | Base-case housekeeping, not a master-bucket theorem problem | Low-priority writeup / certification gap |

---

## What Actually Defines the Frontier

Not every legacy gap is frontier-defining.

### Frontier-defining

These are the real `n=all` blockers:

1. **Bucket I core theorem**
   - irrational intermediate-rank torus intersection.

2. **Bucket II core theorem**
   - dynamic transport failure in the unresolved composite rational regimes.

### Important but secondary

These are real gaps, but they do not define the deepest frontier:

- `P6`: realization / achievability sublemma for B2.
- `CB`: strengthening from existence to `x_0 >= phi(n)` in composite dropped-unit branches.

### Housekeeping / writeup / support

- `B`: `L=2n` analytic writeup.
- exposition-only irrational wording issues that do not change the actual theorem frontier.

---

## Bucket I Detail

### Legacy view

The draft currently records the irrational issue as `F`, largely in terms of the class-product argument failing for large classes or `m=1`.

### Master-bucket view

The real issue is more geometric:

> given a proper subtorus `T ⊂ T^(n-1)` with full coordinate projections, prove `T` meets the safe box.

So `F` should be read as the draft’s visible symptom of the deeper missing theorem, not as the final formulation of the problem.

### Bucket-I closure target

A theorem of the form:

> Every closure subtorus arising from an irrational LRC orbit either
> 1. has rank `1` and reduces to the rational case,
> 2. has full rank and is handled by Kronecker density,
> 3. or, in intermediate rank, still intersects the open safe box.

That would close the irrational frontier cleanly.

---

## Bucket II Detail

### Legacy view

The rational composite frontier currently appears under several names:

- Gap `A`
- `G4B-COMP-CAP`
- B2 / `P6`
- B3b
- multi-divisible composite
- O1 and O2

### Master-bucket view

These are all versions of the same theorem:

> full residue support cannot be maintained forever by the exact handoff schedule.

In branch language:

- B3b: non-unit sparsity plus unit handoff cannot keep every residue covered.
- Multi-divisible composite: same problem with more non-unit channels.
- O1: local forced deficit overflow.
- O2: enough total miss mass / safe cells to force the quantitative bound.
- B2 / `P6`: a target exposure state exists, but the route to it still needs realization.

### Bucket-II closure target

A theorem of the form:

> In the unresolved composite rational Case-2 regimes, the residue transport ledger must become insolvent in bounded time (or bounded measure), so a safe cell appears.

This may be proved via:

- thin-residue existence,
- non-unit coset sparsity,
- bounded-time deficit overflow,
- or a positive average miss theorem.

But whichever route succeeds, it should be recognized as one bucket theorem rather than many local branch closures.

---

## Old Registry vs. Master Overlay

The correct working practice is:

### Keep the old registry for audit

Use the legacy files for:

- exact historical claim wording,
- original branch labels,
- theorem-promotion provenance,
- certification trail.

### Use the overlay for strategy

Use this overlay for:

- deciding where a new lemma belongs,
- avoiding duplicated branch-local programs,
- checking whether a proposed result is
  - a Bucket I theorem,
  - a Bucket II theorem,
  - or merely a strengthening / housekeeping result.

---

## Strategic Reprioritization

Under the master-bucket view, the current priority queue becomes:

1. **Bucket II core**
   - dynamic transport failure in composite rational Case-2.

2. **Bucket I core**
   - intermediate-rank torus-intersection theorem.

3. **Bucket II secondary**
   - `P6` achievability / realization.
   - `CB` quantitative strengthening.

4. **Housekeeping**
   - `L=2n` analytic writeup and other low-priority certification-to-proof promotions.

This is a much cleaner queue than the raw legacy list.

---

## Suggested Use in the Proof Program

When a new note or lemma is created, classify it immediately into one of four labels:

- `Bucket I core`
- `Bucket II core`
- `Bucket II secondary`
- `Housekeeping / audit`

That one discipline should sharply reduce fragmentation in the remaining program.

---

## Bottom Line

The old registries should stay exactly where they are.

But strategically, the live frontier now compresses to:

1. **one geometric theorem** on the irrational side, and
2. **one transport theorem** on the composite rational side.

Everything else is either a sublemma inside one of those buckets or a strengthening / housekeeping item.
