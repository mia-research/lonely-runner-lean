# Eight Lonely Runners

[One-fast rejection](N8_ONE_FAST_REJECTION.md) proves that at most two slow
cells certify incompatibility of the rejected phases and derives endpoint
conditions forcing such a certificate. An exact sweep covers the full
fast-rate range for each of the replayed cores, and the phase-zero
witnesses simplify the hardest controls.

[Moving the fifth reading](N8_MOVING_FIFTH_READING.md) proves a full product
of real intervals with independent motion of the readings at 3, 4, and 5.

[Moving both edges](N8_MOVING_CORE_EDGES.md) extends this argument to
independent movements of the readings at 3 and 4.

[Replacement cells](N8_REPLACEMENT_CELLS.md) derives new openings and
closings as the slow reading at 3 moves, while two rates vary freely.

[Two independent deviations](N8_TWO_DEVIATIONS.md) applies the rollover
rule to two variable readings across the full initial span.

[Radius growth from the outer span](N8_RADIUS_FROM_SPAN.md) gives the sharp
initial-lap bounds and the exact AP-outlier transitions.

The [neighbour dispatch](N8_CASCADE_NEIGHBOURS.md) derives the current
radius and the forced next opening directly from the readings and phases.

The [cascade replay](N8_CASCADE_ANCHOR_REPLAY.md) develops a direct
cascade reduction for fixed slow cells and fast directions. It gives
an exact residue-class rule, with rational controls and checked Lean.

The [effective classical reduction](N8_EFFECTIVE_CLASSICAL_REDUCTION.md) gives an explicit Fourier cube
and height bound. It incorporates the existing integer dispatch so the
remaining classical obligation is restricted to bounded primitive sets
that survive the arithmetic rules.

Research handoff for a new model. 11 November 2026, revision 2.

[Classical finite reduction](N8_CLASSICAL_FINITE_REDUCTION.md) is the shortest route
for unrestricted-time isolation. Lean reduces the arbitrary-real problem and
the cascade termination statement to one finite family of modular certificates.
An explicit bound is now available. The two-window classification has additional
obligations described below.

**Task.** Prove that every runner in every arrangement of eight distinct positive real speeds is isolated at some positive time. The preferred route is to show how the cascade sends arbitrary arrangements into finitely many types, and how those types account for the displacement of an isolation from an arithmetic progression or grid. This is an open proof obligation in this corpus. Lean now has a three-premise existence assembly and a separate window-specific assembly for the stronger classification goal.

Read [Research brief](N8_RESEARCH_BRIEF.md), then [Lean kernel and open obligations](N8_KERNEL_AND_GAPS.md). The [fresh obligation tests](N8_OBLIGATION_TESTS.md) record which statements survived exhaustive replay and which interpretations failed. The [source appendix](N8_SOURCES_ON_REQUEST.md) names the larger trees, handovers, and exact artifacts. The included Lean project uses only Mathlib. The brief gives the definitions, exact calibration examples, and results needed to start without access to those sources. Computations can be reimplemented independently.

The [symbolic coalescence audit](N8_SYMBOLIC_COALESCENCE.md) gives one time formula for the 509 pinch leaves, a minimal bank of fixed times for M1, and short restoration rules for part of M4.

The [symbolic extension audit](N8_SYMBOLIC_EXTENSION.md) gives the full pinch region, a two-cell continuation with a free coordinate, exact benchmark counterexamples, and a tail rule that drops three lap numbers.

The [X24 two-gap proof](N8_X24_GAP_PAIRS.md) covers the entire closed X24 slice with a Lean theorem using native arithmetic evaluation and a separate independent integer replay.

The [four-fast tail reduction](N8_FAST_TAIL_ENTRY.md) handles a block of four diverging readings over three bounded ones. It derives finitely many harmonic slopes from the input and rules out a limiting four-fold tiling.

The [common-rate fast-block proof](N8_COMMON_RATE_FAST_BLOCK.md) closes the five- and six-fast common-leading-rate sectors with explicit sufficient speed ratios.

The [mixed fast rates proof](N8_MIXED_FAST_RATES.md) forces four bounded independent relations in any escaping obstruction and checks the first mixed harmonic slope families in Lean. The [harmonic cutoff follow-up](N8_HARMONIC_CUTOFF.md) gives an effective arbitrary-input reduction for the buffered five- and six-fast sectors, and a separate cutoff for large five-reading primitive slopes.

The [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md) give a numerical four-fast window bound, shorter relations for the five-fast slope problem, and a reduction of six-reading plane phases to five-reading circles. The new exact replay covers all additional five profiles through maximum 18.

The [Lean finite relation reduction](lean_kernel/FINITE_RELATIONS.md) reduces arbitrary arrangements to a finite catalogue of exact relation types for unrestricted isolation, or bounded relation types for the cascade windows. It includes the checked rank-three phase theorem, the four-stage rank ladder, and the determinant implication for the 424,200 cutoff. It includes the checked construction of the projected test and the buffered theorem forcing four rows.

Lean now applies the buffered theorem to the actual five- and six-fast cascade windows, with a finite family of line and plane types for the residuals. The same finite tests prove a qualitative cutoff for exact primitive five-reading profiles.

The checked four-fast theorem now uses the same buffered reduction. Its combined dispatch reduces normalized inputs to a window witness, a finite line or plane type, or a sector with four bounded smallest readings.

The three-fast branch is also checked. The current dispatch leaves a window witness, a finite line or plane type, or a sector with five bounded smallest readings.


The [proof route audit](N8_PROOF_ROUTE_AUDIT.md) compares the classical
and two-window obligations. It records the exact rank-four reduction
for classical isolation, the strict slow-window equivalence, and the
bounded reduction and exact tests for five slow readings.
