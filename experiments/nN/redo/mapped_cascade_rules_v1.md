# From the cascade map to symbolic mechanisms

2026-10-03. Source observations/derivations: outer-repo running log E333 and E344.
Implementation: `LonelyRunner/LRC/Spec/MappedCascadeRulesN.lean`.

Role of this branch: extract parameterised mechanisms from the mapping work,
prove them uniformly, and connect them to the existing Lean chain. Experiments
identify the structure; no experiment is a premise of these theorems.

## E333: which reading closes an isolation window

Use positive subject disparities and positions measured in eighths. If a reading
d has clear position p in [1,7], its next entering edge is (7-p)/d later.
An opener a is at position 1, so its own next entering edge is 6/a later.

For d>a, (7-p)/d <= 6/d < 6/a. Therefore an opener can be its own closer only
if it is a largest disparity. This is independent of the number of readings,
the lap labels and any bounded survey window. The exact integer-lap identity
behind the displacement is also proved.

Declarations: `closing_displacement`, `faster_closes_before_opener`,
`own_closer_maximal`.

### The excluded K2s1 class

Suppose a last opener is on lap 1, at 9/a, and a previous positive-lap setter d
exited earlier at (8j+1)/d, j>=1. Then

    9/d <= (8j+1)/d < 9/a,

so d>a. At the final clear event, d therefore closes strictly before a does.
Thus a cascade with at least two such moves and a lap-1 final opener cannot
have that opener as its own closer. The map's class is excluded by the mechanism,
not by absence from a sample or an infeasible numerical LP.

Declarations: `earlier_setter_faster`, `previous_setter_closes_first`.
The application uses the cascade's positive-lap and increasing-state properties;
the theorem states those needed hypotheses directly rather than assuming a
particular stored path.

## E344: transport of an earlier capture constraint to a later opening

Two observed constraints suffice:

1. At state G, reading c is beyond the entering edge of lap H:
   (8H-1) <= G*c.
2. At c's lap-k opening, reading b is beyond the entering edge of lap L:
   (8L-1)*c <= (8k+1)*b.

For H,L>=1 they imply a lower bound on b, hence the symbolic opening bound

    (8J+1)/b <= G*(8J+1)*(8k+1) / ((8L-1)*(8H-1)).

This is uniform in all four lap numbers and in the speeds. Closed inequalities
retain boundary configurations. `opening_bound_of_zone_link` obtains the second
constraint directly from the existing `ZoneLink.InZone`, rather than asking for
an independent certificate. Only the lower capture edges are needed for the bound.

### The mapped late cell

Substitute G=9, k=4, L=H=6, J=11. The hypotheses become

    47 <= 9*c,       47*c <= 33*b.

Therefore b >= 2209/297 and

    89/b <= 26433/2209 < 12.

`mapped_late_bound` proves this exact rational bound. The numerical tree is not
used. Equality in both closed constraints gives equality in the rational bound;
this algebraic boundary regression does not assert that the limiting arrangement
follows the open-cell cascade history.

## Consequence for the whole attempt

These are proofs of mechanisms applying to infinite families, not merely checks
of selected configurations. The closer theorem removes an impossible outcome
class. The capture-product theorem explains which earlier relations force the
specific mapped late bound and generalises the calculation to arbitrary labels.

It remains unproved that every relevant cascade supplies earlier captures with
lap factors giving a useful common conclusion. Neither a universal bound of 12
nor global order-eight isolation is asserted. This theorem identifies precisely
what data the mapping must explain next: why the required earlier relationships
occur, and how the remaining cases differ.

The lap-update bookkeeping already exists in `LapDeadlineN` and was deliberately
not re-proved. Its changed labels, `ZoneLinkN`'s successor restrictions, and these
capture-product relations can be used together in subsequent replacement proofs.

## Verification

Targeted module build and `experiments/nN/mapped_cascade_rules_axioms_v1.lean`:
9 module theorems plus 2 exact regressions. No full Spec gate. Saved locally;
not committed or pushed.
