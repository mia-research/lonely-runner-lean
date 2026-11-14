# Symbolic coalescence in the eight-runner proof

## A single time formula for 509 band leaves

Use the normalized readings $\rho_i>0$ and time coordinate $R$ from the research brief. A reading is clear in lap $j_i$ when $8j_i+1\le R\rho_i\le8j_i+7$. Put $A_i=8j_i+1$. For fixed laps and a window $[a,b]$, the earliest possible common time is

$$R_*=\max\left(a,\max_i A_i/\rho_i\right).$$

For $a\le b$, the exact conditions for that time to work are

$$A_i\le b\rho_i,\qquad a\rho_i\le A_i+6,\qquad
A_i\rho_k\le(A_k+6)\rho_i\quad\text{for every }i,k.$$

These compare every lower endpoint against every upper endpoint of the intersecting intervals. All constraints are linear in the readings. On a rectangle, use the worst face of each distinct coordinate. The rows with $i=k$ follow from positivity and the gap width.

All 1,018 side certificates attached to the 509 recorded $h_3$ pinch leaves use the same seven laps $(0,1,1,2,3,4,11)$ in $[1,7]$. The maximum simplifies across the entire bounding hull to

$$R_*=\max(25/\rho_5,\ 89/\rho_7).$$

The two terms coincide on $25\rho_7=89\rho_5$. On that whole hull, the only joint-gap inequalities requiring more than the face bounds are $25\rho_3\le15\rho_5$ and $89\rho_3\le15\rho_7$. The hull intersected with these two half-spaces is one region for the formula. Three rectangles also suffice and each clears everywhere, including on the plane. Each coordinate below is divided by 512.

| Leaves contained | Lower faces | Upper faces |
| ---: | --- | --- |
| 236 | (512,1202,1576,2027,2645,3615,9419) | (512,1218,1577,2029,2648,3617,9427) |
| 243 | (512,1220,1600,2058,2686,3670,9563) | (512,1236,1602,2060,2688,3673,9570) |
| 30 | (512,1239,1624,2089,2726,3725,9707) | (512,1244,1625,2090,2728,3726,9712) |

[SymbolicWindow.lean](lean_kernel/Fresh/SymbolicWindow.lean) proves the generic time formula, the simplification to two terms, and soundness on the clipped hull and on each of the three rectangles. Exact integer checks verify the inclusion of the 509 recorded leaves in these rectangles. The surrounding band still needs an exhaustive cover.

## Inside the grid

The inside grid uses six moving readings with faces $[n-\tfrac12,n+\tfrac12]$ for $n>1$ and $[1,\tfrac32]$ for $n=1$. There is also a pinned reading of 1. In the first window $[1,7]$, M1 certifies a box by one time that clears the entire box. M4 denotes the 12,540 boxes assigned to the inside exclusion test. The 73 chain boxes have their own class.

**Fixed time.** For a reading face $[\ell,u]$, the allowed fixed times in lap $j$ form the interval $[(8j+1)/\ell,(8j+7)/u]$. For any collection of faces that clear at a common time, the earliest such time is the window start or one of the left endpoints. The exact scan over the 74,613 tuples yields 87 candidate times in $[1,7]$. Keep the times whose sets of allowed face indices are inclusion-maximal, with one representative per set. The resulting **29 times cover exactly the 62,000 M1 boxes**. For each of those 29 sets there is a tuple contained in that set alone among the maximal sets. Every feasible time's set is contained in some maximal set, so 29 is also a lower bound for fixed times clearing full faces in this window.

The 29 times are 34/33, 18/17, 34/31, 6/5, 34/27, 18/13, 34/23, 50/33, 18/11, 50/29, 34/19, 50/27, 2, 66/31, 50/23, 66/29, 22/9, 82/31, 66/23, 50/17, 98/33, 34/11, 22/7, 98/31, 10/3, 98/29, 66/19, 98/27, 114/31.

**One moving reading.** First find a common closed interval $[L,U]$ within the window in which all the other faces clear. A positive reading $x$ blocks all of it precisely when a single open bad interval contains it, which is equivalent to $(8j-1)/L<x<(8j+1)/U$ for some integer $j$. If its face avoids all these intervals, every possible $x$ has a clear time. The portable Lean module exposes this rule directly. It covers **1,547 M4 boxes** in the exact scan. A lower-face width bound $\ell(U-L)\ge2$ suffices in 1,145 cases. The other 402 use the phase inequalities. For example, at indices $(1,1,1,6,8,14)$ let the face at 8 move and use $[50/27,62/29]$.

**Two moving readings.** With $x\le y$, any strict increasing-exit chain covering $[L,U]$ has at most one zone from $x$. Otherwise the intervening $y$-zone would have to span the gap of at least $6/x$ between distinct $x$-zones. Its width is $2/y\le2/x$. Zones from a single reading are disjoint, so the only chain of length three has order $y,x,y$. Exact rational comparisons that exclude all these possible chains certify **625 additional M4 boxes**. This count uses the chain argument and the rational checker.

All **2,172** M4 boxes handled by the one- and two-reading rules belong to the existing $C_3$ class of 10,211. The $C_3$ residual still contains 2,329 boxes. These rules simplify certificates for a portion of the existing $C_3$ class.

## Existing coalescences and the remaining reduction

The native catalogue already has a useful parametrization. The two-block theorem packages nine families as two arithmetic-progression blocks with parameters $(p,A,b)$ under the permitted normalizations. Uniform opening cells also subsume the common opening grid bands. The full catalogue wrapper expresses the canonical witness equivalence. Entry from arbitrary normalized input into the listed geometric families still needs a proof.

On the bounded band $\rho_i\le49$, any feasible lap in $[1,7]$ is between 0 and 42 because $8j_i+1\le7\rho_i\le343$. For $[9,15]$ the corresponding cap is 91. Thus each window already has an exact finite description of its clearable region as a union of the linear regions above. The 509-leaf result shows how to merge certificates with the same lap vector and discard endpoint inequalities implied by the geometry. The remaining work is to prove that a manageable collection of these regions covers the bounded inputs and that the tail or a witness-preserving reduction handles the unbounded inputs. A terminating cascade selection rule would also have to prove entry into one of the selected types.

## Exact replay in the research repository

The scripts and recorded output are in the repository under experiments/n8/symbolic_coalescence_2026_11_11. Run each Python file from the repository root. The four scripts check the window masks and one-reader cases, the mask lower bound and overlap with $C_3$, the two-reader cases, and the pinch hulls. The data needed for those replays can be requested separately. The formulas, pinch hull data, and Lean proofs are included here.

The [extension audit](N8_SYMBOLIC_EXTENSION.md) continues this analysis beyond the original boxes. It gives a complete two-cell argument for a free third coordinate on three groups of stationary readings and checks broader selectors against X24 and the inside residual.
