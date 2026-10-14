# The complete account, Levels A–C, against the record: a crosswalk (v1)

2026-10-01. Log E226. Owner: *"Documentation is only good if you bother reading it"* (E225).

**Why this exists.** Levels A–C (`CASCADE_ACCOUNT_LEVEL_A_v1.md`, `_B_v1.md`, `_C_v1.md`, log E221–E223) were derived
from the definition and checked. They are correct as far as the checks go. But most of their content was already in the
record, proved or verified, and the catalogues did not cite it. That is map §6 F7: the record not read. This file maps
every item to where the record already has it, so the account is read as a consolidation with citations, not as new
work. The catalogues are left unchanged (versioning); this file is their citation layer, to be folded into their next
versions.

**Method.** I read manuscript v21 §6.1–§6.6 and §6.9–§6.15 in full, and the log's E142–E143, E178–E183, E202–E204 and
E115 headers. I grepped the log up to E220 and v21 for each item. "Not found" means not found by that grep (terms
listed). It does not mean new to mathematics.

| account item | already in the record | anchor | standing of the account's version |
|---|---|---|---|
| A.0–A.1 the move; no lonely instant inside; landing lonely | v21 §6.1, Theorem 6.2(a), Theorem 6.3(b) | `Cascade/Iteration.lean` | restatement |
| A.2 every instant is an opening | v21 §6.1 (`move_eq_self_or_opening`); §6.2 the scale recursion; Corollary 6.24 (every scale visited is a candidate scale) | `Iteration.lean`, `ScaleCandidates.lean` | restatement |
| A.3 setter = largest remaining distance over speed | Theorem 6.23 (the lap is exact; `λ = max over blockers of (8M+1)/s`) | `MoveRule.move_lap` | restatement in position form |
| A.4 the step as a rotation of positions | §6.2 "A step is one dilation" (`dilation_factor`, `other_reading_shift`, `setter_reading_at_nextScale`) | `Iteration.lean` | restatement (positions advance linearly = readings dilate) |
| A.5 next crowd = arrivals + re-entries | `SeparationN.transport` (centred case); E204's edge cases (6 re-entries, 2,293 pass-throughs) | | general split stated; a restatement of the definition |
| A.6 three move types | E142; `SweepBridgeN` | | restatement |
| A.7 setter clear at its exit | §6.2 "the setter lands exactly on `8N+1`"; Theorem 6.16 | `circDist_at_nextOpening` | restatement |
| A.8 the certificate; setter slowest of its lap-`K` cluster | Theorem 6.19 (clearance criterion), 6.12, 6.14; E143 (forced, 42,013 + 103,355 + 5,400) | `DminClearance.clear_at_scale_iff`, `Flanks.*` | restatement |
| A.9 first isolation | Theorem 6.2(b) | `first_isolation_of_fixed` | restatement |
| A.10 captures at the bound | §6.6's spine pattern (near-sharers are in the way at spine 1); E202 | | restatement |
| B.1 setter = latest exit | Theorem 6.23 | | restatement |
| B.2 junction by ratio to the setter | Theorem 6.17 (in the way at scale `D` iff `D ∈ (d/(nM+1), d/(nM−1))`); Theorem 6.12 (the band at every opening); E125, E208 | `inWay_at_scale_interval`, `clear_at_opening_of_band` | restatement |
| B.3, B.5 the run below the setter; passages to the cluster bottom | E142–E143; E203; `sweep_ratio` | | restatement |
| **B.4 a sweep jumps to the bottom of the run in one move** | E203 says a sweep "stops at its bottom"; the one-move jump is not found (grep: "bottom of the run", "jumps to the") | | **not found in the record**; `[derived; checked E222]` |
| B.6 bridges; rank falls between bridges up | E142, E183 | | restatement |
| B.7 the queue | E204 | | restatement |
| **B.8 the conveyor's exact condition** (front in the next crowd and no later exit; a slower arrival always outlasts it; a faster one only if late enough) | E204 recorded the conveyor as data, "not forced" | | **not found** (grep: "outlast", "queue front iff"); `[derived; checked E222]`; closes gap B4 |
| B.9 the end: no arrival, or the front passing through | E204 ("a gap in the arrivals"; pass-throughs counted as edge cases) | | restatement; the split of landings by pass-through is new data |
| C.1–C.2 walls; finite chain decided by edge forms | E124 ("cut only along walls"); E179 (for a fixed lap assignment each condition is linear) | | restatement in general form |
| **C.3 a tie is a leaving-side edge wall; at the final move a hand-off** | | | **not found** (grep: "tie … edge"); `[derived; checked E223]` |
| C.4 intermediate walls change the route, not the landing | E182 ("the cascade's landing changes only at pinches (E178)"); Theorem 6.2(b) | | restatement |
| C.5 the landing's faces: leaving = hand-off, entering = one more move to the entering reading's exit | E178–E182 (every event a pinch; a birth jumps to the newborn instant; "a death restarts the cascade, which passes `b`'s exit", log l.5964); `PathRouteN.margin_or_pinch`; `PinchOpenN`; local stability for one-runner moves (`segment_lonely`, `move_one_period`) | `Spec/PathRouteN.lean`, `PinchOpenN.lean` | restatement; **the resolution of E219's 243/106/153/281 cases as effects of moving a reading a finite distance (other walls crossed) is new analysis of E219** |
| C.6 the landing's region | E219; Theorem 6.17 (bad scales are explicit intervals, candidates their left endpoints) | | restatement |

**What the account adds** (not found in the record by the greps named):
- B.4;
- B.8, which closes the conveyor question E204 left as data;
- C.3;
- the E219 resolution;
- the landing counts by pass-through.

Everything else is the record restated in positions, now checked again on new populations (E221–E223). The checks are
not wasted: they confirm the restatements and the code. But nothing in A–C should be cited as new.

**Where Level D starts, read from the record.** The re-aimed Level D target (E224: where the relay from an entering-face
crossing lands, named by the readings) is, in the record's terms, Theorem 6.15 locally: the largest clear candidate scale
below the crossing's scale (§6.10: "the cascade is a sort and a scan"). The record's native machinery for it is the flank
framework:
- v21 §6.9: Theorem 6.8 (loneliness is a flank statement); Theorem 6.9 (one fractional ratio clears); Proposition 6.10
  (a pair, lattice cases); Theorems 6.12–6.14 (the band; the finite search; the congruence); the U/K calculus for a
  family with a free difference (`class_killer_int`, `lonely_of_flank_unkillable`, `lonely_of_some_flank_unkillable`).
- v21 §6.11: Theorem 6.18, the run-length criterion for two walkers; the eight half-integer shadowing configurations.

Its open items, as the record states them:
- "the derivation at a general flank is not written down" (§6.9);
- the full list of shadowing triples (§6.9);
- "both on a common lattice, run-length failing" (§6.11's case table);
- the index bound, measured and not proved (§6.10).

Level D is to be designed from these and from v21 §6.7 (Existence) and §17, read in full first. It should not be derived
afresh.
