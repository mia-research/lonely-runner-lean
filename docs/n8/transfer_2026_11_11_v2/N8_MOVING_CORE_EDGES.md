# Moving both edges of the second slow cell

Keep the normalized readings (1,2,5). Let the readings at (3)
and (4) move to (s) and (v) independently, with

[
s\in[17/7,23/7],\qquad v\in[27/7,31/7].
]

The two other readings can still vary independently in ([1,15]).
Lean proves a (1/8)-clear time in ([1/8,7/8]) for every such
profile.

## The moving opening and the cell that replaces it

In the second cell the original opening was (9/32), set by
reading (4). When (v) moves, take

[
 a=\max\left(\frac9{32},\frac9{8v}\right).
]

The moving slow reading (s) imposes the closing (7/(8s)).
If (a\le7/(8s)), the adjusted cell accepts at (a) in the
relevant fast branch.

The cell may disappear. This matters in the branch where the
first rejected cell gave a left blocker (p\ge68/9) and a low
right blocker (q\in(5,45/7)). The overlap from that rejection
also gives (7p<9q). These two inequalities place the fast
readings in clear phases at both of the following candidates.

- At (17/40), (p) clears in lap 3 and (q) in lap 2.
  The moving reading (v) clears in lap 1 when (v\le75/17).
- At (9/16), (p) clears in lap 4 and (q) in lap 3.
  The inequality (7p<9q) is what supplies (q)'s lower
  clearance edge there. The moving reading (v) is clear in lap 2
  throughout its allowed range.

The proof chooses the first of these when (v\le75/17) and the
second otherwise. The bound (s\le23/7) keeps (s) clear there
and throughout the late cell used by the other branches.
No comparison between (s) and (v) is required in the final
input hypotheses.

The earlier moving candidate (17/(8s)) is now tested against
the whole core. If moving (v) destroys it, the already checked
late-cell comparison supplies the witness.

## Exact replay

There were 26,208 rational checks across both moving edges and the
two fast rates. They include 60 instances using the adjusted
second opening, 80 using a backup after loss of that cell, and
eight where the moving candidate (17/(8s)) is blocked by the core.
Each selected witness was checked and compared with the ordinary
cascade's first landing.

For (s=151/50, v=39/10, p=39/5, q=31/5), the old opening
(9/32) is blocked by (v). The exact first landing is
(15/52=9/(8v)). For (s=31/10, v=39/10, p=8, q=25/4),
the second cell is empty and the exact first landing is (17/40).

The checked theorem is `third_fourth_readings_replacement` in
`Fresh/CascadeFourthReading.lean`. The generic theorem
`replacement_of_adjusted_core` takes the adjusted opening and the
backup cell property as inputs. Run
`python3 cascade_fourth_reading_audit.py` alongside the previous
audit scripts to replay the controls.

This closes the indicated four-parameter family. For a direct
cascade classification of arbitrary inputs, one open step is
forcing the remaining core cells or suitable replacements when
the other core readings move.

[Moving the fifth reading](N8_MOVING_FIFTH_READING.md) extends this
family to independent motion of all three readings at 3, 4, and 5.
