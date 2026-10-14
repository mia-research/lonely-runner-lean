# Symbolic AP-window transport: eliminate the pinch parameter

2026-09-29. This develops the previous 64-path experiment into a symbolic
transport test and a six-parameter family. It does not complete order 8.

## General algebra

Fix a subject, the seven positive AP disparities a_i, and arbitrary positive
target disparities d_i. Ordered speed deformation gives

    d_i(s) = (1-s) a_i + s d_i,    0 <= s <= 1.

For a proposed lap vector q, each window constraint has slack

    F_q,ij(s) = (1-s) C_q,ij + s G_q,ij,
    C_q,ij = (8q_j+7)a_i - (8q_i+1)a_j,
    G_q,ij = (8q_j+7)d_i - (8q_i+1)d_j.

All 49 slacks nonnegative is exactly feasibility of that lap window, including
a singleton time. The C values are constants; the G values are linear in the
target disparities (hence in the six ordered speed factors).

Suppose an old constraint has AP value A>0 and target value E<0. Its pinch is
tau=A/(A-E), strictly between 0 and 1. For ANY replacement slack with endpoint
values C,G, cancellation gives

    (A-E) F(tau) = A G - C E.

Thus replacement feasibility at the pinch is exactly the 49 LINEAR conditions
A G_q,ij - C_q,ij E >= 0. Strict inequalities give a positive common-window
margin there. This is not a quadratic test: A,C are fixed AP constants.

Two pinch locations A/(A-E) and C/(C-G), with positive denominators, are ordered
exactly when A G-C E >= 0 as well. Checking the two ends of a parameter interval
then establishes all intermediate real parameters because each slack is affine.

Important: A,E must come from an identified old constraint to call tau its
pinch. The algebra does not prove it is the earliest old constraint to vanish;
that needs the other constraints, or the existing WindowPinch first-pinch theorem.
It also does not select a universally successful replacement vector.

## A full six-dimensional family, not another parameter mesh

Fix endpoints 0 and 199. Allow arbitrary real target speeds

    |y1-1| <= 1/192,   |y2-50| <= 1/192,
    |y3-105| <= 1/192, |y4-106| <= 1/192,
    |y5-136| <= 1/192, |y6-189| <= 1/192.

Normalize by 7/199 and deform from 0,1,...,7. For the endpoint subject 0,
the SAME four lap vectors cover the WHOLE deformation for EVERY target in this
box:

| Vector q | Sufficient closed parameter interval |
| --- | --- |
| (0,0,1,1,1,2,2) | [0, 2/3] |
| (0,1,2,2,3,4,5) | [2/3, 6/7] |
| (0,4,9,9,12,17,18) | [6/7, 49/50] |
| (0,6,13,13,17,23,25) | [49/50, 1] |

At shared endpoints both assignments are feasible. Therefore these are
overlapping availability regions, not an assumption that a cascade terminates.
No continuous choice of isolation time is asserted; switching assignments can
switch to a distant time.

The symbolic derivation first uses moving pinch locations. Its 355 affine
conditions include validity of the old and replacement vectors at each of three
pinches, ordered pinches, final feasibility, and positive target gaps.
At the central target 352 are strictly positive and three vanish identically.
For an affine condition H(y), a uniform box radius r is safe if

    H(centre) - r * sum_i |coefficient_i(H)| >= 0.

The smallest positive margin-to-coefficient ratio is 1/96. Choosing r=1/192
gives strict margins for every nonzero condition. This proves the whole box by
the triangle inequality. The script also checks all 64 corners as regressions;
those checks are not substituted for the symbolic whole-box bound.

The simpler fixed intervals in the table satisfy the same family bounds and
are used in Lean. Endpoint constraints there reduce to rational linear
inequalities in the six y variables. Their interpolation handles every real s.

## Files and limitations

- `SymbolicWindowTransportN.lean`: pinch cancellation, exact sign and ordering
  criteria, interpolation of all lap inequalities, replacement-window existence,
  and positive-time band witnesses over whole parameter intervals.
- `SymbolicWindowFamilyN.lean`: the six-variable family and all four intervals.
- `symbolic_window_transport_axioms_v1.lean`: declaration audit and regressions.
- `symbolic_pinch_transport_v1.py`: exact derivation of the target region and box.

Verification completed: both new Spec modules build; the family target build
finished successfully (8,264 jobs including replayed dependencies). The audit
compiles and all 20 declarations use only propext, Classical.choice, and
Quot.sound (some use fewer). This includes `family_lonely`, which connects to
the existing `Arrangement.LonelyAt` predicate, and the necessary lap-budget
bound below. The exact Python derivation and all 64 corner regressions pass.
No full Spec gate was run. Files are saved locally, not committed or pushed.

The four vectors were seeded by the earlier numerical discovery. The new proof
is universal over this box, but it is NOT a rule selecting replacement vectors
for arbitrary targets, and it concerns this endpoint subject, not every subject
of every arrangement. The remaining global obligation is to derive label
selection/coverage from arbitrary target constraints. Merely assuming the 49
replacement conditions would not discharge that obligation.

There is also a necessary design constraint on a global selector. In span-7
coordinates for the endpoint subject, let m be the smallest disparity. Any
positive isolation time satisfies m*t >= 1/8. If the farthest runner is in lap K,
then 7*t <= K+7/8. Multiplying gives

    7 <= m*(8K+7).

Therefore no single finite list of fixed natural lap vectors can cover the
whole simplex as m tends to zero. A global symbolic rule must allow its lap
indices to depend on the speeds, or supply a justified rescaling and transport
that accommodates these unbounded labels. This does not contradict finiteness
of the reference-level categories; those categories do not fix future laps.

No new Prop definition, conjectural axiom, or universal termination statement
is introduced. No unrelated framework is used: these are the existing AP
deformation and lap-window equations.
