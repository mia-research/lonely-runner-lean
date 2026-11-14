# Cascade replay and finite phase classes at a slow cell

The [neighbour dispatch](N8_CASCADE_NEIGHBOURS.md) derives the current
radius and the forced next opening directly from the readings and phases.

The replay uses the project's move rule. Start at (1/(8d_{\min})).
At each step take the latest next opening of the readings that are in
the way, with strict blocking and closed clearance at (1/8).

## What the cascade showed

The eight controls include the AP, two tight profiles, the sole-free-flank
example, the fixed-grid miss, the recorded 28-move example, and two
large primitive residual diagnostic controls. The replay also changes
the physical gap order and perturbs one reading at a time. A pure
relabelling preserves the disparity set for a fixed subject. Permuting
physical gaps changes that set.

| Exact replay | Runs | Raw move count changed | Slow-cell count changed |
| --- | ---: | ---: | ---: |
| Gap permutations | 24 | 15 | 6 |
| Single-reading rational perturbations | 224 | 31 | 13 |

For all controls and variations, the full cascade and the split
cascade landed at the same time. In the 28-move control the six
slow readings proposed six cells. The fastest reading's first opening
after the cell starts fell beyond the right endpoint on the first
five. The sixth accepted at (49/1872). The 12-move residual control
required only two slow cells. The replay prints the exact cells.

The block shortcut generalizes the older experiments in
`experiments/n8/block_rule_cascade_v1.py`. Given a start, let (a)
be the first slow clear time, and let (u) be the first fast clear
time from (a). Every joint clear time from the original start is
at least (u). If (u) is in the slow clear cell, (u) is the first
joint clear time. If the cell is rejected, the calculation can resume
at (u). The Lean proof uses the existing fixed-point and
no-overshoot theorems.

## The finite classification inside a cell

Fix a slow clear cell ([a,b]) and a fast rate direction (F).
Suppose the fast rates are multiplied by (c>0) with
((cd-d)a\in\mathbb Z) for every (d\in F). The identity
[
 cd\left(a+\frac{t-a}{c}\right)=dt+(cd-d)a
]
preserves each fast phase and transports every fast cascade move from
anchor (a). Thus if the fast cascade first clears at (u), the
dilated block first clears at (a+(u-a)/c). The cell accepts exactly
when (u-a\le c(b-a)).

For integer scales of a rational fast direction, let (D>0) clear the
denominators of all (da). For (n=r+Dk) with (1\le r\le D), let
(u_r) be the first clear time for (rF) started at (a).
The first clear time of (nF) from that same anchor is
[
 a+\frac{r}{n}(u_r-a),
]
and the cell accepts exactly when (r(u_r-a)\le n(b-a)).
One replay per residue class determines the answer at all scales in
that class. A singleton cell accepts precisely when the anchor itself
clears in that class. With one fast reading, a cell of width at least
(1/(4d)) accepts for every anchor phase.

The residue threshold matched 182 exact checks. In 72 phase-preserving
dilations of one, two, or three fast readings, the fast-only trace
matched the time contraction step for step. The transported witness
was the full cascade landing in 54 cases. The other 18 found a
joint clear time earlier. The phase condition matters. Doubling
12 to 24 in the tight profile ((1,2,3,4,5,7,12)) closes the old
point at (1/8).

The control ((2,3,4,5,6,7,16)) also gives a checked infinite family.
For every integer (c\ge1), the first landing of
((2,3,4,5,6,7,16c)) is (1/16+1/(128c)). The six slow readings
share ([1/16,1/8]), and the fast phase at its start is always an integer.

## Remaining entry theorem

The modulus and slow cell depend on the input. These results reduce
each fixed-cell, fixed-direction family, and they permit earlier
landings under transport. They leave open how to force all inputs into
a common finite catalogue of cell and phase types. For the
cascade-specific route, a useful target is a bound on the slow cells
and directions needed in the surviving regimes, or a witness-preserving
reduction of those data. The exact replay should be used to test
proposed reductions against tight singleton cells and changes in which
cell first accepts.

Lean source is `Fresh/CascadeAnchor.lean`. Run
`python3 cascade_anchor_audit.py` to reproduce the controls without
the larger corpus. The two large diagnostics come from
`experiments/n8/fast_pair_resumption_2026_10_20/residual_controls.json`.
Their classification as diagnostic controls carries no formal
`OpenResidual` membership assertion.

[One-fast rejection across several cells](N8_ONE_FAST_REJECTION.md)
proves that at most two slow cells certify incompatibility of the
rejected phases. It derives endpoint conditions that force such a
certificate, including a first-window pinch with a singleton cell.
