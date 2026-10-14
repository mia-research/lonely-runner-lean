# Moving endpoints cross the old core-region boundary

4 October 2026. Module: `MovingCoreWindowsN.lean`.

## What changed

The previous variable-core theorem kept four fixed subwindows. Its rectangular
speed bounds could fail even though the actual core windows still existed.
The new theorem moves the endpoints with three parameters b,c,e:

| Window | R interval | Core lap vector |
|---|---|---|
| 0 | [1,7/b] | (0,0,0,0,0,0) |
| 1 | [17/c,31/b] | (0,1,2,2,3,3) |
| 2 | [33/e,47/b] | (0,2,3,4,5,5) |
| 3 | [9,63/b] | (1,3,4,5,7,7) |

R=8t. Natural choices are b=d_5, c=d_2, e=d_3; the theorem permits any positive
parameters satisfying its constraints, so these identifications are not hidden
hypotheses. It requires V>=b for the inserted reading, without an upper cap.

## Explicit core region

Write a=(1,17,33,9), f=(1,c,e,1), z=(7,31,47,63), and let q be the table.
The whole window w is core-clear if, for each of the six readings,

    (8q_wi+1)*f_w <= a_w*d_i,
    z_w*d_i <= (8q_wi+7)*b.

These are linear inequalities in d,b,c,e. They carry all intervening readings
and allow the endpoints to move. Window 0 in particular bounds every core
reading between 1 and b.

Additional sufficient conditions are

    0<b<=7,   0<c,   e>=101/20,   1105b<=1953c.

They guarantee nonempty positive windows and the label/replacement argument.
They are not asserted to be necessary for all isolation mechanisms.

## Labels are still derived

If V swallows all three early windows, their endpoint inequalities imply

    (K_1,K_2,K_3)=(1,4,6),
    31c/17 < V < 49b/47.

This is `obstruction_labels`, uniform in b,c,e and V. The proof first derives
K_3>5 from V>=b. The third window and bounds b<=7,e>=101/20 force V<15, so
K_1=1. The ratio bound implies 51b<=91c, forcing K_2=4, and then K_3=6.
No numerical label enumeration supplies this conclusion.

## Ratio-controlled rescue

Set R=max(9,65/V), expressed in Lean as two explicit choices. It belongs to
the late core window and clears V whenever

    b<=7,    1105b<=1953c.

Indeed 65/V<=63/b follows from V>31c/17 and 65b<=63*(31c/17). At R=9 the
upper clearance edge follows from V<49b/47 and b<=7. Thus 65<=VR<=71.

`family_isolated` combines early survival with this forced late replacement.
All displayed constraints remain hypotheses; the theorem does not assume a
successful cascade or a pre-existing full isolation witness.

## Verified extension beyond the previous rectangle

Take core

    (1,73/25,397/100,253/50,321/50,699/100).

Its largest reading is 6.99, strictly ABOVE the old upper bound 2350/337.
The regression `outside_old_region` proves this comparison. The regression
`neighbouring_family` verifies every moving-window hypothesis and proves
isolation for this core plus EVERY V>=699/100. This is not merely a recheck of
the old region, nor a check at a single V.

## Remaining classification

The new region retains the four core lap vectors and the obstruction labels.
It extends the old boundary by moving endpoints, not by changing labels.
It is not an exhaustive union of regions for all cores.

The ratio face 1105b=1953c has a precise meaning: at the lower residual speed,
the inserted reading's lap-8 exit reaches the core's late closing edge. On
the other side this rescue is not guaranteed by these bounds. A new window
or changed labels must be derived there; merely reusing this theorem would
assume the missing step.

## Delegation and validation

Claude independently checked the obstruction interval and the rescue algebra,
including the open-speed-interval endpoints. This returned useful algebra,
not a proof of core clearance or global coverage. The complete conditions and
label derivation were proved independently in Lean here.

Targeted build; axiom audit of nine module declarations and three regression
declarations. Only standard Lean axioms. No full Spec gate, commit or push in
this turn. No delegated process remains running.
