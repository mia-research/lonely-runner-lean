# Why the four cells fail, and whether failure persists

Fix the base `D={9,13,28,45,87,125}`. Its cells are independent of the added
disparity `x=8c`. The four consecutive cells previously exhibited have indices
5,6,7,8, starting with index zero, in the exact cell list for one period.

## Cause at x=32

An added disparity is blocked when its phase relative to an integer is strictly
between `−1/8` and `1/8`. Here are the **unwrapped** phase intervals for the four
whole cells:

| Base cell | Exceptional phase over the cell | Next clear opening of x | Base reading blocked at that opening |
|---|---|---|---|
| `[41/696,63/1000]` | `2 + [−10/87,2/125]` | `17/256` | 45 |
| `[65/696,19/200]` | `3 + [−1/87,1/25]` | `25/256` | 9 |
| `[97/1000,7/72]` | `3 + [13/125,1/9]` | `25/256` | 9 |
| `{1/8}` | `4` | `33/256` | 125 |

Each displayed phase interval lies strictly inside the blocked band about its
integer. Thus **every point of each closed cell fails**, not just its opener or
a tested grid point. Every next exceptional opening lies strictly after the
cell's right endpoint.

The widths, required forward steps, and excess steps are respectively:

| Cell | Width | Required step | Step minus width |
|---|---|---|---|
| 1 | `89/21750` | `167/22272` | `109/32000` |
| 2 | `7/4350` | `95/22272` | `17/6400` |
| 3 | `1/4500` | `21/32000` | `1/2304` |
| 4 | `0` | `1/256` | `1/256` |

The base's endpoint constraints explain why the available intervals stop there:
the opener/closer disparities are `(87,125)`, `(87,125)`, `(125,9)`, and `(9,87)`.
At the next exceptional openings the circular distances of the indicated base
blockers are `3/256`, `31/256`, `31/256`, and `29/256`, all below `1/8=32/256`.

The second and third cells have the same next exceptional opening `25/256`.
Moving between them reduces the distance to that exit, but even the third cell
closes before the exit is reached. This is why progress within one band does not
by itself guarantee success at the next cell.

## Persistence: several different meanings of 'always'

**Within each specified cell at x=32:** yes, every point fails, as proved above.

**In subsequent integer periods of the same input:** yes. All disparities are
integers, so translating a cell by an integer preserves all circular distances.
The same local failure repeats. This is not failure of every cell in the period.

**When c varies and the base stays fixed:** no for the positive-width cells. The
exact unbounded classifications are:

* Cell 1 fails exactly for `c∈{2,4}`; succeeds for every `c≥5`.
* Cell 2 fails exactly for `c∈{4,8,12}`; succeeds for every `c≥13`.
* Cell 3 fails exactly for
  `c∈{4,5,9,13,18,22,27,31,36,40,45,49,54,58,63,67,76,85,94,103,112,121,130}`;
  succeeds for every `c≥131`.
* The touch cell `{1/8}` fails for **every** natural `c`, because
  `(8c)*(1/8)=c` is an integer and has circular distance zero.

Consequently **all four cells fail together if and only if c=4**, for positive
natural c. This is a proved classification, not a sampled guess. It does not
say that no different base can have four failures at another exceptional speed.
Failure of a fixed positive cell is not monotone in c before its eventual cutoff.

The classifications are unbounded because a failed cell must satisfy
`x*(w−u)<1/4`. For `x=8c`, this requires `c<1/(32*(w−u))`. The respective
width-based success cutoffs are 8,20,141. Only the finitely many smaller values
need exact phase checks, which sharpen the cutoffs to 5,13,131. For an arbitrary
fixed positive-width cell this same width bound ensures eventual success.
It does not settle variable bases whose cell widths also change with x.

**Does the full x=32 input fail?** No. Its first survivor is `1/72`, before this
four-cell run; after the run it also succeeds at `129/1000`. Both are
kernel-verified witnesses for all seven disparities. The four failures concern
local candidate cells and refute a universal local next-cell claim. They are not
an obstruction to existence for this input, nor evidence of arbitrarily long
initial failure chains. A separate example in E459 has three initial failures.

## Verification and scope

`LonelyRunner/LonelyRunner/LRC/Spec/OrderEightCellFailureExampleN.lean` proves
the three exact cofactor classifications, permanent touch failure, the iff c=4
claim, blocked-band containment, the base blockers at the next openings, and the
two full-input witnesses. These are eight public theorems.

Run `python3 scripts/check_order_eight_cell_failure_example.py` from the nested
Lean repository. The audit prints their axioms and excludes the listed classical
seven-runner endpoints for three proof dependency traversals. Exact cell
adjacency, endpoint roles and displacement traces are independently reproduced
by `python3 experiments/n8/four_failed_cells_explanation_v1.py` from the parent
workspace, writing its companion JSON. These traces are exact diagnostics;
the unbounded cofactor classifications are proved in Lean.

No existing source or gate is changed. This work is local and unpushed. Full
primitive one-multiple existence and n=8 remain unresolved.
