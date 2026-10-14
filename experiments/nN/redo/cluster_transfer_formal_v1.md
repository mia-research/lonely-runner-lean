# Phase-aware cluster reduction — 2026-10-05

## What is proved

`ClusterTransferN.lean` uses ordinary time, not R=8*d_min*t. For a cluster
reading c*x and c>0, set t=A+u/c. Its reading becomes A*c*x+x*u.
Keeping that starting phase (modulo an integer) preserves clearance exactly.
The nextOpening formula transforms with the same ceiling/lap selection.

`window_transfer_iff` proves equivalence between a clear point of the full
arrangement in [A,B] and a clear point of the phased cluster in [0,c(B-A)],
provided all the discarded slow readings are clear throughout [A,B]. The
interval is closed; singleton windows are retained. If A>0, any such point
is a positive-time isolation witness. Existence is not assumed or concluded
unconditionally: the two existence statements are equivalent.

`move_union_clear` and `iterate_union_clear` remove an entire slow set from
a cascade state/prefix when those readings are clear at every relevant state.
These extend the single-reading inert lemmas. They do not justify deleting
arbitrary fast moves from a path word.

## Scope

This proves the coordinate/window bookkeeping for a genuine cluster reduction.
It does not prove that the phased cluster stops inside the permitted interval,
that all configurations reduce to finitely many transfer patterns, or that the
whole deformation preserves isolation. Full affine conjugacy of the maximum
over all phased exits is not yet packaged as a Lean theorem; the per-reading
exit formula and inert-union prefix statements are proved separately.

## Verification and delegation

Targeted build: `lake build LonelyRunner.LRC.Spec.ClusterTransferN` passed.
Audit source: `experiments/nN/cluster_transfer_axioms_v1.lean` (six declarations).
No full Spec gate or commit/push requested in this turn.

Claude received `cluster_transfer_claude_brief_v1.md`: exact Fraction checks,
counterexamples to discarded phases/intervals, endpoint-order conditions and
recognition of existing train-collapse families. One foreground computation,
at most 2,000 arrangements/60 seconds/300 moves per cascade; unfinished cases
must be reported, not treated as proof. Its experiments remain discovery,
independent of the symbolic proof above.
