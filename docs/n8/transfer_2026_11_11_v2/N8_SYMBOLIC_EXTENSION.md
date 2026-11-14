# Extending symbolic certificates in the eight-runner proof

The original pinch certificate can be continued across its limiting boundary by changing two laps. On three groups of stationary readings, this removes the box restriction on the third reading altogether. This is an instance of a general two-cell argument. The same investigation produced exact counterexamples to restricting the choice of witness to a few predetermined readings.

## Full region of the original lap vector

Use sorted normalized readings $1=\rho_1\le\cdots\le\rho_7\le49$ and time $R$. The original lap vector is $(0,1,1,2,3,4,11)$. Write $A=(1,9,9,17,25,33,89)$ and $B=A+6$. The exact region is given by the following **26 irredundant rows**:

$$
A_i\rho_j\le B_j\rho_i,\qquad
i\in\{2,4,5,6,7\},\quad j\in\{1,3,4,5,6,7\},\quad i\ne j.
$$

The pinned first reading imposes $[1,7]$. Its lower endpoint is dominated by $89/\rho_7\ge89/49>1$. Readings 2 and 3 share a lap. In sorted order, only 2 can supply their larger lower endpoint and only 3 their smaller upper endpoint. The same-reading rows follow from the gap width. Comparing the remaining lower and upper endpoints proves the region formula. An exact ratio-constraint calculation gives a rational point violating each retained row while satisfying the others, and a point in the relative interior of the corresponding facet. The checker uses cross multiplication with the displacement parameter treated as positive and infinitesimal. This gives an exact one-sided test along the chosen ray.

At one such crossing per facet, all 26 probes had another first-window gap. All 509 crossings obtained by increasing $\rho_3$ from the recorded leaf centers had a common replacement lap vector $(0,1,2,2,3,4,12)$. This crossing test suggested the theorem below. It represents one ray per facet or leaf center.

## Two gap cells cover a full coordinate interval

Hold readings $1,2,4,5,6,7$ fixed and let $\rho_3$ vary. Let $[L_0,U_0]$ be the common gap of the stationary readings in the original laps, and $[L_1,U_1]$ their common gap in the replacement laps. Assume both are nonempty subsets of $[1,7]$.

- In the first cell, reading 3 shares its lower phase edge 9 with reading 2. Thus $L_0\rho_3\ge9$ follows from $\rho_2\le\rho_3$. This cell works at $R=L_0$ whenever $\rho_3\le15/L_0$.
- In the second cell, reading 3 shares its upper phase edge 23 with reading 4. Thus $U_1\rho_3\le23$ follows from $\rho_3\le\rho_4$. This cell works at $R=\max(L_1,17/\rho_3)$ whenever $\rho_3\ge17/U_1$.

The two conditions cover **every** $\rho_3\in[\rho_2,\rho_4]$ if $17L_0\le15U_1$. The condition depends only on the stationary readings. The argument also works for other gaps with compatible edge inequalities. Lean checks the general statement and its explicit selector in [GapSplice.lean](lean_kernel/Fresh/GapSplice.lean).

For the three original stationary groups, exact face arithmetic verifies this condition throughout the groups. Their bounds have denominator 512 and omit reading 3:

| Group | Lower faces of readings 1, 2, 4, 5, 6, 7 | Upper faces |
| --- | --- | --- |
| 1 | (512,1202,2027,2645,3615,9419) | (512,1218,2029,2648,3617,9427) |
| 2 | (512,1220,2058,2686,3670,9563) | (512,1236,2060,2688,3673,9570) |
| 3 | (512,1239,2089,2726,3725,9707) | (512,1244,2090,2728,3726,9712) |

A single stationary region also works. Take the coordinatewise hull of the displayed faces. Across it both stationary cells are nonempty and
$$
L_0=\max(25/\rho_5,89/\rho_7),\qquad
L_1=97/\rho_7,\qquad
U_1=\min(39/\rho_6,103/\rho_7).
$$
The overlap condition on this hull is exactly the three linear rows
$$
425\rho_6\le585\rho_5,\qquad
1513\rho_6\le585\rho_7,\qquad
425\rho_7\le1545\rho_5.
$$
In particular the three stationary groups satisfy the rows. These formulas give a region with a free coordinate and an explicit two-way selector. Immediately past the original upper limit $15/L_0$, the replacement time is set by reading 3 at $17/\rho_3$. It changes to the fastest reading at $\rho_3=17\rho_7/97$. Indeed $15/L_0\le15\rho_7/89<17\rho_7/97$.

A separate exact union check covers the entire original seven-coordinate bounding hull, including points outside the three stationary groups. Fourteen full lap vectors are compatible with its face relaxation. Five suffice and five is minimal among covers of that hull by fixed full lap vectors. The five are $(0,0,0,0,0,1,3)$, $(0,1,1,2,2,3,9)$, $(0,1,1,2,3,4,11)$, $(0,1,2,2,3,4,12)$, and $(0,1,2,2,3,5,13)$. A separate search allowing one lap to vary freely per type found no cover of the entire bounding hull with up to three such types. The two-cell theorem above uses the explicit overlap conditions on the stationary readings.

## What transferred to the difficult benchmarks

**X24.** Both ends of the fastest reading's gaps were tested as candidate times in both windows. This rule succeeded on 2,401 rational profiles, even when the fastest reading was allowed to vary continuously from 23 to 25 subject to ordering. An exact search in the ratios $\rho_i/\rho_7$ nevertheless found a counterexample. A simple interior control is
$$
(1,\;23/10,\;539/200,\;283/40,\;931/100,\;23/2,\;23001/1000).
$$
All 70 eligible endpoints of reading 7 fail at least one other reading. The tuple clears at $R=100/19$. For this search a fast endpoint $e/\rho_7$ is blocked by a slower reading exactly when $e\rho_i/\rho_7$ is in an open bad phase. At fixed top reading the candidates are a finite list, and one slow reading's blocking set is constant between consecutive phase thresholds. Testing whether five such sets cover all candidates produced the counterexample.

**Inside residual.** On 9,316 rational probes from the 2,329 residual boxes, there were 213 misses using only rank 7 endpoints, seven misses using ranks 5 and 7, and three misses even after adding the pinned reading. All probes have a first-window witness. The smallest rank sets that passed this particular test have three ranks, and this remains a sample verdict. Whole-box tests certifying a single adaptive cell by a width bound for up to three moving readings, or a single adaptive cell with a common fixed-time core and exact phase for one moving reading, discharged zero residual boxes.

**Width versus phase.** Removing the fastest reading and trying the longest remaining common cell worked for all 2,402 initial X24 probes. Exact interval tests also verified that choice over the entire admissible fastest-reading interval for each of the 2,401 original profiles. A search aimed at short slow cells then produced the exact X24 counterexample
$$
(1,\;997/50,\;21,\;22,\;229/10,\;24,\;969/40).
$$
Its unique longest slow cell across the two windows is $[27/2,3110/229]$. The fastest reading puts that entire cell in the open bad phase $(327,329)$, and the tuple clears at $R=1250/997$ in another cell. In the inside residual, the longest cell sufficed for 9,301 of 9,316 probes. Four probes needed the fifth cell under the tested width ordering.

A cell $[L,U]$ fails for a fastest reading $x$ precisely when $x$ is in one of the open intervals $((8j-1)/L,(8j+1)/U)$. If two slow cells have disjoint failure sets within the admissible fastest-reading interval, at least one restores a clear point for every fastest reading in that interval. On 883 fixed slow profiles, including the two X24 controls and a grid of near-arithmetic fast clusters, an exact whole-interval test found 742 profiles with one cell sufficient and 141 requiring two. The [subsequent two-gap proof](N8_X24_GAP_PAIRS.md) independently verifies this condition throughout X24 and the wider closed band $[22.5,25.5]$.

## A tail rule that drops three lap numbers

For an already clear slow interval $[L,U]$ and up to three fast readings $x\le y\le z$, run the usual maximum-of-current-exits step using just the fast readings. An increasing-exit chain for the two faster readings has at most three intervals in the order $z,y,z$. Two visits to $y$ would need one $z$-interval of length $2/z$ to bridge a separation of at least $6/y$. Its total length is therefore at most $2/y+4/z$. If a chain using all three returned to $x$, its intervening faster subchain would have to bridge $6/x$ with strict overlap. Its total length is at most $2/y+4/z\le6/x$, so this cannot happen.

It follows that the fast-only cascade makes at most seven jumps in a cell before clearing or leaving the cell. The bound applies at any starting phase and requires no upper bound on the three speeds. A fast-only covering chain has total length at most $2/x+4/y+8/z$. In particular, if $U-L$ is at least that length, there is a common clear point in the cell, including the equality case because the bad intervals are open. A separate 10,000-case exact rational stress test checked the width implication. The existing Lean forest has related seven-move results in Fresh.Ladder. The argument here uses interval widths and can start at the left endpoint of an arbitrary slow cell.

Apply this to the existing NStarK 5 result on the four slowest readings, whose largest is $M=\rho_4$. A $1/5$ witness in either of its specified windows gives a $1/8$-clear interval of length $6/(5M)$ in the corresponding $R$ window. The radius $3/(5M)$ follows by the Lipschitz bound on distance to the integers. The pinned window has margin at least $3/5$ to its $1/8$ endpoints, and $M\ge1$. Thus this handles any three faster readings satisfying
$$
2/\rho_5+4/\rho_6+8/\rho_7 \le 6/(5\rho_4).
$$
For example $\rho_5\ge(35/3)\rho_4$ suffices without requiring successive scale gaps among the three fast readings. This is a sufficient tail region. Inputs failing the inequality still need another argument.

A width condition in a designated window can degenerate. With slow readings $(1,4/3,5/3,7/3,3,13/3)$ the slow clear set in $[9,15]$ is exactly $\{9,15\}$. Every fast reading $8k/3$ blocks both points. This exact family is a control for any attempt to force positive width in that window.

## Replay

The independent rational programs and their saved output are in experiments/n8/symbolic_extension_2026_11_11 in the research repository. The full region, two-cell continuation, and whole-hull check are in pinch_region.py, pinch_strip.py, and hull_union.py. The phase-projection and benchmark tests are in phase_union.py, endpoint_benchmarks.py, adaptive_cells.py, adaptive_phase.py, x24_endpoint_cover.py, fast_fibers.py, longest_cell.py, and cell_pairs.py. Run them from the repository root. The 509 leaf records and the residual box list are replay inputs that can be requested separately.
