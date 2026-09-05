# Master Problem 1 Safe-Fiber Budget Note (v1)
**Date:** 2026-03-07  
**Purpose:** isolate the exact remaining theorem content of MP1.7 after the run-end coverage package is in place.

## 0) Current state
By the current Master Problem 1 program:
- boundary-ending runs are already capped,
- every genuine interior exit is now partitioned and routed in theorem form,
- every maximal obstruction run ends at a theorem-controlled safe opening.

So the remaining unresolved content of `G4B-Branch-Closure` is no longer exit taxonomy or event-local exposure.

It is the component safe-fiber budget:

`B_safe(C) >= n`.

## 1) Exact theorem target

### MP1.7 (safe-fiber budget)
For every `B_div` component `C` in the declared composite Case-2 large-`L` scope,

`B_safe(C) >= n`.

Equivalent form:

`|O cap C| <= |C| - n`.

This is the quantitative ingredient still missing before the final aggregation theorem.

## 2) What is already available

### Available theorem pieces
- lower-band safety theorem (`T3(b)`-type safe fibers),
- boundary-ending run cap,
- pure non-unit exit theorem,
- unit/mixed routing theorem,
- run-end coverage theorem (`MP1.6`).

### What these pieces do **not** yet give by themselves
They do not yet provide a theorem-grade lower bound on the **total** number of safe fibers in a component.

They show how runs end, but not yet how much safe mass must accumulate across the whole component.

## 3) Ruled-out shortcut

The note [lrc_g4b_lower_bound_universal_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_g4b_lower_bound_universal_v1.md) already rules out the naive universal lower-band route:

- claim tested: `safe_before >= n` for every obstruction run,
- result: failures occur (`7320 / 56160` runs in the recorded `n=6` sweep).

So the theorem still needed is **not**:

> the first `n` fibers of every component are always safe.

That route is empirically false as a universal proof mechanism.

## 4) Correct remaining theorem shape
The safe-fiber budget must be **distributed**, not prefix-only.

Selected first theorem route:
- **SF3: distributed event-spacing / safe-cell occupancy transfer**

Reason for choosing SF3 first:
- SF1 is too weak if treated as pure safe-cell counting,
- SF2 is too weak if treated as lower-band-only,
- the diagnostics show the safe mass is distributed across event-cell occupancies.

Working route note:
- `lrc_master_problem1_safe_fiber_budget_sf3_v1.md`

## 5) What MP1.7 is **not**
MP1.7 is not:
- a local exit witness theorem,
- a lower-band-only theorem,
- a re-statement of NZ0,
- a certification result.

It is a quantitative component-level counting theorem.

## 6) Immediate program consequence
The next theorem-writing move should not revisit local exposure.
It should develop the chosen SF3 route and, in particular, isolate the overlap-control subclaim for safe event-cell occupancies.

## 7) Status
`OPEN-TARGET`.
