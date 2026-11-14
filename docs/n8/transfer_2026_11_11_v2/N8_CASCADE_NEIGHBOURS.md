# A systematic neighbour rule for the cascade

[Radius growth from the outer span](N8_RADIUS_FROM_SPAN.md) gives the sharp
initial-lap bounds and the exact AP-outlier transitions.

At the current time (a), each positive disparity (d_i) determines
its own lap (k_i=\lfloor d_i a\rfloor). At radius (r), the clear
interval for that lap is

[
 [L_i(r),U_i(r)]=
 \left[\frac{k_i+r}{d_i},\frac{k_i+1-r}{d_i}\right].
]

The overlap is the extension allowed by all the neighbours. It needs
one latest opening and one earliest closing. Lean proves that its
maximum feasible radius, with these laps fixed and time at or after
(a), is the minimum of

[
 \frac{d_i(k_j+1)-d_j k_i}{d_i+d_j}
 \quad\text{over all ordered pairs }(i,j),
 \qquad
 k_j+1-d_j a
 \quad\text{over all }j .
]

The second term is the forward-time restriction. An equality gives an
allowed endpoint. All inequalities use current input data. In relative
time the opening and closing offsets are respectively
((r-\phi_i)/d_i) and ((1-r-\phi_i)/d_i), where
(\phi_i=\{d_i a\}). This formulation removes the absolute lap
labels from the tests.

The distinction between position and time to the boundary matters.
At (1/8) for ((1,2,3,4,5,6,13)), the reading (6) has the
greatest fractional position. Its closing is (1/48) later. Reading
(13) reaches its closing after only (1/52), so it limits the
forward extension.

## An exhaustive decision at radius 1/8

Set (L=\max(a,\max_i L_i(1/8))). Every future joint clear
time must be at least (L). There are two outcomes.

1. If (L\le\min_j U_j(1/8)), it is the first joint clear time
   from (a). Equality gives a singleton in the forward cell.
2. If a closing (U_j(1/8)<L), every future joint clear time
   is at or after the next opening ((k_j+1+1/8)/d_j).
   Take the largest forced opening over all such (j).

The second rule works even if the closer is currently clear. A
witness at or beyond (L) would be past its closing, so it has to
wait for the next opening. Ties between closers are handled in the
same batch. Each jump increases the chosen reading's lap. If (j)
is (d_{\min}=m) in lap zero, a required opening beyond
(7/(8m)) forces the next possible time to be at least (9/(8m)).
That is an exact rule for exiting the first minimum-reading window.

If all readings are at most (M), every forced jump advances more
than (1/(8M)). This gives a finite bound for the number of jumps
before leaving any supplied time band. The tests apply at every
state. Global entry into a bounded list of such states still
requires a proof across bands and speed scales.

## Exact controls

The replay uses the same ordinary cascade as the previous anchor
audit. In 192 representative inputs and variants, the neighbour
dispatch and ordinary cascade had the same first landing. The replay
verified 545 forced jumps, including 121 that advanced a currently
clear reader and 13 with tied earliest closings. It also checked 58
singleton forward cells.

- The recorded 28-move example takes 23 forced jumps and lands at
  (49/1872).
- In ((1,2,3,4,7,8,15)), readings (7) and (15) close
  together at (1/8). Reading (8) cannot clear before
  (9/64), so both are forced to their next lap. Their next
  openings are (9/56) and (17/120). The later one is already
  the first joint clear time, in one jump.
- The AP ((1,2,3,4,5,6,7)) has maximum radius (1/8) in
  its first lap cell, attained by the pair (1,7).

Run `python3 cascade_neighbour_audit.py` with the existing
`cascade_anchor_audit.py` alongside it. The new checked statements
are in `Fresh/CascadeNeighbours.lean`. The radius formula extends
the fixed-threshold endpoint formulas in `SymbolicWindow`, and
the forced jump uses the existing distance-to-integer and
no-overshoot facts.
