# How far can the clearance radius grow?

[Two independent deviations](N8_TWO_DEVIATIONS.md) applies the rollover
rule to two variable readings across the full initial span.

Let (m=d_{\min}) and (M=d_{\max}) for the chosen runner. The
initial-lap question concerns the positive disparities before any
wrap. A time clears at radius (r) in those laps exactly when

[
 r\le dt\le1-r\quad\text{for every disparity }d .
]

The lower edge that matters is (r/m). The upper edge that matters
is ((1-r)/M). All the intermediate readings are between the same
two extremes at every positive time. The greatest achievable
radius in the initial laps is therefore

[
 r_{\max}=\frac{m}{m+M},\qquad t_{\max}=\frac{1}{m+M}.
]

This is the exact tolerance for uneven spacing in that cell. The
(1/16) radius is possible exactly when (M\le15m), and (1/8)
is possible exactly when (M\le7m). At the arithmetic progression
(1,\ldots,7) in units of (m), the target radius is attained at the
equality (M=7m). Any increase of (M) at fixed (m) closes that
initial cell at radius (1/8). The other gaps may vary freely as
long as the outer ratio stays within the stated bound.

## After the first reading wraps

Suppose the slower readings still have maximum (B\le7m), and the
fastest reading (x) lies in (7m<x<9m). The slow cell is
([1/(8m),7/(8B)]). The phase of (x) at its left endpoint is inside
the blocked interval around lap one. So the first candidate is
(9/(8x)), which is in the slow cell exactly when (9B\le7x).
This calculation works for arbitrary spacing of the slow readings
between (m) and (B). For (9m\le x\le15m), the reading (x)
already clears at (1/(8m)) and the slow readings still clear there.

There is also an exact test for several deviating readings within the
same initial span. If a reading (x\in(7m,9m)) forces the candidate
(t=9/(8x)), a reading (d\in[m,15m]) clears there precisely when
its ratio (d/x) lies in one of

[
 [1/9,7/9],\qquad [1,5/3],\qquad [17/9,23/9].
]

The lower endpoint (1/9) and the upper endpoint (23/9) are
automatic from the span hypotheses. A reading in either of the two
open gaps gives the next blocking constraint. The candidate is the
first isolation exactly when all readings pass that test.

## One deformation worked through completely

Normalize (m=1) and keep the six readings (1,2,3,4,5,6) fixed.
Let the seventh reading (x) vary through ([7,15]). The first
three slow cells are ([1/8,7/48]), ([9/32,7/24]), and the point
(3/8). To get the second cell, readings (6,5,4) block in sequence
after the first cell closes. Reading (3) blocks from the end of
the second cell to the third.

| Range of (x) | First joint clear time |
| --- | --- |
| (x=7) or (9\le x\le15) | (1/8) |
| (54/7\le x<9) | (9/(8x)) |
| (68/9\le x<54/7) | (9/32) |
| (51/7\le x<68/9) | (17/(8x)) |
| (7<x<51/7) | (3/8) |

The boundaries come from comparing openings and closings. For
example, the first cell accepts the outlier's opening exactly when
(9/(8x)\le7/48), giving (x\ge54/7). If it fails, the next
opening in the second slow cell is (17/(8x)) until (x=68/9).
It fits before (7/24) exactly when (x\ge51/7). For smaller
(x>7), the point (3/8) clears. The project had already observed
these transitions in E307–E308. The checked formula derives each
case from the same endpoint rule.

This gives an exact answer for the initial cell and for a complete
one-reading deformation, including all boundary points. Moving
several readings can change the later slow cells, including the
singleton at (3/8). For that situation the three-band theorem
is exact at the first rollover candidate, and the general neighbour
dispatch supplies the next forced transition when the candidate fails.

Run `python3 cascade_radius_audit.py` alongside
`cascade_anchor_audit.py` for exact boundary controls.
