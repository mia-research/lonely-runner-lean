# One-fast rejection across several slow cells

Let \(d>0\) be the fast reading. Allow an additive fast phase \(\theta\),
with \(\theta=0\) for the ordinary cascade. A closed slow cell \([a,b]\)
rejects precisely when
\[
db+\theta-\tfrac18<k<da+\theta+\tfrac18
\quad\text{for some }k\in\mathbb Z.
\]
This includes singleton cells and uses strict blocking at both ends.
The rejected phases form an open arc of length at most \(1/4\) modulo
one. A cell of width at least \(1/(4d)\) has an empty rejection arc.

For any finite collection of these cells, if their rejection arcs have
empty common intersection, one or two of the cells already suffice.
Lean proves this for arcs of length at most \(1/3\). Choose a reference
arc and lift every arc that meets it into the same real interval. These
lifts have total span strictly below one. Pairwise overlap modulo one
therefore implies ordinary pairwise overlap, and the largest lower
endpoint lies strictly below the smallest upper endpoint.

For two cells \([a,b]\) and \([c,e]\) with nonempty rejection arcs, a
common rejected phase exists exactly when
\[
d(e-a)-\tfrac14 < k < d(c-b)+\tfrac14
\quad\text{for some }k\in\mathbb Z.
\]
This is a test on the difference of the blocked laps. It removes the
absolute lap labels and the common phase from the comparison.

## Geometry that forces a certificate

For three slow cells \([a,b],[c,e],[f,g]\), Lean gives the sufficient
conditions
\[
3(f-e)\le e-a,\qquad \tfrac54\le d(g-c),\qquad
9(c-b)\le 23(g-c).
\]
If all three cells were rejected, the successive differences \(k,m\)
of their blocked laps would satisfy \(m\ge2\), \(k\ge3m\), and
\(9k<23m+8\le27m\). This contradicts \(k\ge3m\).

The conditions hold for the cells
\[
[1/8,7/(8w)],\quad [41/(8w),7/8],\quad [9/8,55/(8w)]
\]
whenever \(41/7\le w\le55/9\) and \(d\ge w\). Lean checks that
\(1,w\) and four independent readings within \(1/256\) of \(2,3,4,5\)
retain those cells. Either the second or third cell is a singleton at
the corresponding endpoint of the \(w\) range. The separate lap
inequalities in the Lean module let other readings retain these cells
in any laps, which includes bands outside the progression neighborhood.

A second theorem handles the first-window pinch. For any slow readings
in \([1,5]\), adjoin \(w\in[145/21,7]\) and one faster reading \(d\).
The slow core retains \([1/8,7/(8w)]\) and \([9/(8w),7/40]\).
If \(d\le3w\), rejecting both would require an integer strictly between
zero and one. If \(d>3w\), the second cell alone has sufficient width.
At \(w=7\) the first cell is a singleton.

## Exact checks and remaining obligation

The exact replay sweeps each phase endpoint and each intervening phase
interval for the anchored and pinch controls. Across 5,772 broader
core and fast-rate pairs, one wide cell sufficed in 5,534 cases.
The other 238 had incompatible pairs. The three-cell inequalities
forced the incompatibility in 146 of those, leaving 92 for other
arguments. For example the core \((1,2,3,4,5,7)\) with \(d=113/16\)
uses the pinch theorem.

For the core \((1,4/3,10/3,17/4,19/4,16/3)\), the shifted fast
reading \(d=65/12,\theta=1/5\) blocks all three first-window cells.
A second-window cell clears. This counterexample concerns the
arbitrary-phase strengthening in the first window. The ordinary
cascade has phase zero.

The general two-cell theorem compresses a certificate once the
common rejection phase has been ruled out. The remaining one-fast
problem is to force incompatible rejection arcs for arbitrary six-slow
cores in the two windows, or to exploit the actual phase when a common
rejection phase is possible. If a core has only singleton clear cells
in both windows, the existing finite-times obstruction allows one
arbitrarily fast reading to block them all.

Lean source is `Fresh/CascadeRejection.lean`. Run
`python3 cascade_rejection_audit.py` to replay the exact controls.

## Sweep the whole fast-rate range

For a fixed six-reading core, let \(W\) be the largest width of a slow
clear cell in the two windows. If \(W>0\), every rate \(d\ge 1/(4W)\)
accepts in that cell for every phase. Below that threshold, a pair of
ordered cells \([a,b]\), \([c,e]\) is certified whenever
\[
j+\tfrac14\le d(e-a),\qquad d(c-b)\le j+\tfrac34
\]
for an integer \(j\). The blocking integers would have to differ by an
integer strictly inside \((j,j+1)\). These inequalities describe a
closed interval of fast rates, so an exact union check covers whole
real rate ranges even though the slow cores used in the audit are
rational.

The most frequent nontrivial pattern uses \(j=0\). For rates \(d\ge d_0\),
the pair works up to the threshold of a third cell of width \(W\) when
\(d_0(e-a)\ge1/4\) and \(c-b\le3W\). Lean checks this handoff from the
pair to the wide cell. The pinch proof now uses this theorem and
extends down to \(w=145/21\). The cells \([9/40,15/64]\) and
\([17/64,15/56]\), followed by the wide cell \([9/56,7/40]\),
also cover every \(d\ge8\) for the core \((1,2,3,5,7,8)\).

| Exact batch | Cores | Wide at every rate | One \(j=0\) pair, then width | Higher integer gaps |
| --- | ---: | ---: | ---: | ---: |
| Original broad controls | 962 | 891 | 66 | 5 |
| Integer and perturbed controls | 8,839 | 7,274 | 1,350 | 215 |
| Perturbations near the hardest control | 1,791 | 337 | 845 | 609 |

The largest required \(j\) in the middle batch was 5. The last batch
found 204 cores for which using \(j\le5\) leaves an interval of rates.
The ordinary cascade starts with phase zero. With that phase, \(1/6\)
closes the omitted rates for 200 of the 204 cores. The other four also
use \(5/6\). Lean checks the two rate bands when the corresponding slow
witness is retained. The exact sweep checks retention and coverage for
these controls. This gives a way to test whether a difficult
arbitrary-phase case can be bypassed using the actual cascade phase.

Run `python3 cascade_fast_rate_audit.py` to reproduce the sweep.
