# Two independent reading deviations

[Replacement cells](N8_REPLACEMENT_CELLS.md) derives new openings and
closings as the slow reading at 3 moves, while two rates vary freely.

Keep the five normalized readings (1,2,3,4,5) and let the other
two readings (x,y) vary independently in ([1,15]). Lean proves
that the chosen runner clears at radius (1/8) between (1/8)
and (5/8). All times are in units of the inverse minimum reading.
The argument also works for any slower block retaining the same
clearance intervals and points.

## How rejection reduces the possibilities

The first slow cell is ([a,b]=[1/8,7/40]). If (x) and (y)
both clear at (a), use (a). Otherwise call a blocker (p).
Its rate lies in (7<p<9). Its next opening is (u=9/(8p)),
inside the slow cell, and (p) is also clear at (b).

Check the other reading (q) at (u) and (b). If it is clear
at either point, use that point. If it blocks both, then the
phase of (q) at (b) gives just two possibilities

[
5<q<45/7
\qquad\text{or}\qquad
75/7<q<85/7 .
]

The rest of the proof uses these inequalities.

- If (p\ge51/7), both rates clear at (7/24).
- If (p<51/7), it clears at (3/8). A (q) in the higher
  band must also satisfy (q>11), since it blocked at (u).
  That puts it in the clear interval at (3/8). In the lower
  band, (q\ge17/3) clears at (3/8) as well.
- If the lower band has (q<17/3), both rates clear at (5/8).
  This branch is impossible if both variable readings are at
  least (17/3).

These are witness times, and the cascade can arrive earlier. For
((p,q)=(71/10,111/20)) with the five fixed readings, the exact
cascade first clears at (5/8).

## Tolerance for uneven spacing in the retained block

Any slow reading in
([1,7/3]\cup\{3\}\cup[27/7,5]) clears throughout the first
cell and at (7/24) and (3/8). This allows independent changes
to several slower readings. For the branch that needs (5/8),
the slow block also has to clear there. One sufficient subfamily
within the displayed bands is
([1,7/5]\cup[9/5,7/3]\cup\{3\}\cup[27/7,23/5]\cup\{5\}).

The scope is two unrestricted rates in the initial span and a
retained slow block. The next structural question is which
replacement cells can be forced when perturbations also remove
one of these slow cells.

The checked theorem is `five_ap_two_deviations` in
`Fresh/CascadeTwoDeviations.lean`. The standalone Python audit
`cascade_two_deviations_audit.py` uses exact arithmetic with the
previous cascade replay. Its 2,010 checks exercise all six
witness choices across three slow blocks.
