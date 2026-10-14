# First gate: formal scope and missing implication

2026-10-04. `FirstGateN.lean`, audit `first_gate_axioms_v1.lean`.

All Lean times are ordinary t; the map uses R=8t after normalising d_min=1.

## Unconditional results

- A rho-zone has R-width 2/rho, strictly less than 2 if rho>1.
- A captured reading's exit is strictly less than one zone-width after
  the current state.
- If every reading is at least 1, a max-exit move from R≤7 ends strictly
  below 9. This includes R=7; the capturing zones are open.
- Reading 1 is captured throughout (7,9), with next exit exactly 9.
- A lonely endpoint above 7 must be at least 9.
- A move from (7,9) reaches AT LEAST 9. Equality needs an upper bound on
  the exits of the other currently captured readings.

The sentence "only d_min's zone spans that jump" needs care: (7,9) does
not contain R=7, so d_min cannot make a captured move from R≤7 to R=9.
It becomes captured after the first crossing of 7.

## Conditional full equivalence

`terminal_gate_equivalences` proves all three events equivalent for a finite
lonely iterate from R=1, provided every non-minimum reading is at least 2:

1. the landing is above 7;
2. an iterate is exactly 9;
3. reading 1 is captured and attains the maximum exit on some move.

Why: the first crossing of 7 ends below 8 (other zones have width ≤1),
and from there all other exits are below 9 while reading 1 exits at 9.
Termination is not proved or assumed for arbitrary input: the theorem
explicitly takes a lonely finite iterate. `crossing_iff_visits_nine` needs
no termination assumption and relates the two events along the iterates.

E364 reports rho_2≥2.21 among its sampled gate crossers, so this hypothesis
covers those reported examples. It has not been derived for all crossers.

## Why width alone is insufficient

Lean checks the actual max-exit moves for readings (1,45/44,9/5), starting
LOCALLY at R=7:

    7 -> 44/5 -> 85/9.

The setters are 45/44 and 9/5. The second move beats reading 1's exit at 9.
All non-minimum zones have width under 2, yet this path skips 9.
This is NOT a counterexample to E340's full seven-reading assertion from
R=1: these three readings are already clear at R=1. It identifies the
missing reachability argument when trying to infer E340 from width alone.

## Verification

Targeted build passes. All 17 printed declarations (including the actual
two-move regression) use only standard Lean axioms. Full Spec gate not run.
No claim of an unrestricted gate equivalence or a global n=8 proof.
