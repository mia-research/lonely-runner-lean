# Tests of the open order-eight statements

11 November 2026. This report uses the predicates in the corrected assembly, with a reading fixed at 1 and closed box faces. Every exclusion below is an exact computation over the stated finite box population. Sampled rational inputs are reported separately. Lean checked the semantic band equivalence used in interpreting the tests. The box computations still need a Lean replay or an independent proof to discharge the hypotheses.

## Results on the four assembly hypotheses

| Lean hypothesis | Fresh test | Result and scope |
|---|---|---|
| `M4BoxNoCarvePinned` | Enumerated all 74,613 closed nearest-integer boxes with the minimum pinned and weak sorting. Separately intersected the exact fixed-point time intervals for the literal M1 condition on the full faces. | Exactly 73 boxes admit a first-window carve and they match the Lean chain table. Exactly 62,000 have an M1 fixed point. The other 12,540 match the M4 table and all exclude the first-window carve. No search caps. |
| `ChainBoxSoundPinned` | In each of the 73 boxes searched for a single open-zone chain across \([1,15]\), including zones of reading 1. Also searched \([9,15]\) on its own. | Zero double carves. A standalone second-window carve is possible in **72 of 73** boxes. Exact rational witnesses were reconstructed and independently replayed for all 73 first-window and 72 standalone second-window cases. |
| `BandCertData` | Replayed the entire continuum from top reading 17 through \(29.5\) using the same joint-chain test over closed boxes. Separately rechecked the \(h_3\) pinch data and its clipped sides. | Zero double carves in the tested band, including X24 and its endpoints. All 509 on-plane certificates and 1,018 clipped side certificates pass with the corrected side-label interpretation below. The full range through 49 was sampled and has earlier recorded finite-band evidence. The fresh exhaustive replay stops at \(29.5\). |
| `TailBelow17` | Searched all boxes with top reading in \([48.5,55.5]\) or \([94.5,100.5]\) and middle readings at most \(9.5\). Also ran exact stress tests over five tail bands reaching \(10^{12}\), plus phase-cluster and endpoint controls. | All 16,731 restricted boxes exclude a \(W_0\) carve. All 120,000 seeded tail samples reached \(W_0\), as did 4,000 further samples at top reading 95. The unbounded tail remains open. |

The tests include equal readings and half-integer faces. Sorting loses no tuples for these checks. Coordinates assigned different nearest-integer indices are ordered by their faces, possibly with equality. Coordinates in the same face can be permuted freely. Any coordinate equal to 1 has index 1 and can be placed first. The tests let the actual top reading reach the full upper face, including 17.5 in the J2 table.

### What the 68/5 split actually counted

The earlier stage-2 sweep enumerated second-window chains after adding the common bounds obtained from the first-window chains. Its 68 zero counts are for that **join-pruned domain**. The five remaining boxes had second-window chains after that pruning, and the original pair check excluded compatibility. In the bare boxes, 67 of those 68 admit a second-window carve.

For example, in box \((1,2,3,4,4,5,7)\) the readings
\[
(1,\;9147/5000,\;33703/10000,\;40247/10000,\;43333/10000,\;5647/1250,\;69997/10000)
\]
carve \([9,15]\) and clear at \(R=1\). The only one of the 73 that excludes a standalone second-window carve is \((1,3,5,6,7,8,8)\). The joint exclusion survives the correction.

### The clipped-plane dump has reversed labels

Let \(h_3=25\rho_7-89\rho_5\). The exporter returns its sides in the order \(h_3\ge0\), \(h_3\le0\), then appends the path labels `h3-`, `h3+` in that same order. Thus the stored **`h3-` means \(h_3\ge0\)** and **`h3+` means \(h_3\le0\)**. Equality is included in both sides and also has a separate pinch certificate. A Lean replay using these closed half-spaces can cover the 509 leaves with a two-way split. The pinch data give an independent check on the plane. The [symbolic coalescence audit](N8_SYMBOLIC_COALESCENCE.md) subsequently covered these leaves with a single time formula on three larger rectangles.

The checker rebuilt every clipped polytope from its actual corners and cut edges. It checked the shape of the 15 window inequalities per region and their exact values at the vertices. All 1,018 fail on the half-space suggested by the literal label and pass on the half-space selected by the exporter. The saved artifact was left intact. Decode its labels before replaying it in Lean.

### Why a double-carve test tests the band statement

In the physical normalization, reading 1 blocks \((7,9)\). Hence both \(W_0\) and \(W_1\) carved is equivalent to \([1,15]\) covered. The checker searches the latter and requires strict open-zone overlaps.

A separate Lean check proves
\[
\texttt{BandCertData}\quad\Longleftrightarrow\quad
\forall g,\ \texttt{BandRange}\ g\ \to\ \texttt{BandClearPoint}\ g.
\]
For the converse, a \(W_0\) point gives a fixed-point certificate on the degenerate box with faces equal to \(g\), and a \(W_1\) point gives the required gap indices. This tests the pointwise Lean hypothesis directly. A practical proof still needs reusable certificates or a checked enumeration.

## Further tests of the proposed routes

- **X24 calibration.** The saved rational X24 example lands at \(6500/683\) after 24 moves. All 1,000 small rational perturbations around it landed in \(W_1\). The exact all-box run for top index 23–25 covered \([22.5,25.5]\), with 297,765 boxes, 22,584,706 visited nodes, zero double carves and no caps.
- **Boundary tests.** At each exact top reading 17, 23, 25, 49 and 95, 4,000 separate seeded rational tests reached \(W_0\).
- **Level 6 and level 7 margin statements.** The exact point tests checked 32,000 cases at each threshold \(1/6\) and \(1/7\), respectively, with the required number of readings and top reading up to \(10^{12}\). Every tested point reached the first window. AP controls clear at the left endpoint, and the controls with one extra reading fail. See the run table for the independent continuous box tests.
- **Unrestricted block-gap bound.** The five-reading counterexample in the gap register is a proof for arbitrary interval length, including the case of six readings by adding a speed. The exact control for \([400,410]\) was reproduced. A constrained cascade-window statement remains a separate question.

### A proved obstruction to bounding the number of moves

For any integer \(B\ge2\), use the seven distinct readings
\[
1,\quad 2,\quad 8B+\frac{8i}{5}\quad (i=0,1,2,3,4).
\]
They are physically realized by an endpoint subject. On \(1\le R\le65/64\), the five fast phases at \(R\) differ from the evenly spaced phases \(8BR+8i/5\bmod 8\) by at most \(1/10\). Some equally spaced phase is within \(4/5\) of a multiple of 8, so some fast reading is strictly in the way. The two slow readings are clear throughout this interval. Each move from the interval has length less than \(2/(8B)=1/(4B)\), so crossing it takes more than \(B/16\) moves.

These same inputs have a clear point in \(W_0\) at \(R=5+1/(2B)\). Each fast product at that point is \(40B+8i+4+4i/(5B)\), in its closed clear gap, and the two slow readings are clear. The exact cascade controls for \(B=16,128,1024,8192\) took 2, 11, 81 and 641 moves just to cross \(65/64\). A finite reduction therefore needs a way to summarize unbounded histories, even for families with a witnessed first-window landing.

## How the exact box test works

A covering chain is encoded by exact upper bounds on ratios of two readings, with a strictness bit. The box faces supply closed bounds. Each next zone enters strictly before the current exit and exits strictly after it. A shortest covering chain can be chosen with the entry of each new zone at or after the exit two positions earlier. An earlier entry would allow deletion of the intervening zone. For the second zone the earlier exit is the window's left endpoint, with the same deletion argument. This pruning is independent of any observed maximum chain length.

The checker maintains exact closure of the ratio bounds. A cycle with product below 1, or product 1 with at least one strict bound, excludes the branch. The lap bounds are computed from the exact ratio bounds on the next possible entry and exit. For a fixed closed box and horizon there are finitely many laps and exits strictly increase. Tests that report a cap are unresolved. Each test below completed without a cap. The implementation uses checked integer arithmetic with arbitrary-precision comparison for longer intermediate products. It tests the continuum through inequalities, while the rational stress tests check individual inputs.

| Order | Rounded top index | Other restrictions | Boxes | Search | Hits |
|---|---:|---|---:|---|---:|
| 8 | 1–17 | Minimum pinned | 74,613 | First window and joint | 73 first-window boxes, zero joint |
| 8 | 18–22 | Minimum pinned | 221,397 | Joint | 0 |
| 8 | 23–25 | Minimum pinned | 297,765 | Joint | 0 |
| 8 | 26–29 | Minimum pinned | 751,129 | Joint | 0 |
| 8 | 25–29 | Minimum pinned | 869,884 | First window | 0 |
| 8 | 49–55 | Middle indices at most 9 | 9,009 | First window and joint in separate runs | 0 |
| 8 | 95–100 | Middle indices at most 9 | 7,722 | First window and joint in separate runs | 0 |
| 6 | 1–17 | Five readings, minimum pinned | 4,845 | First window and joint | 8 first-window boxes, zero joint |
| 7 | 1–17 | Six readings, minimum pinned | 20,349 | First window and joint | 24 first-window boxes, zero joint |

At orders 6 and 7 the finite box tests do find first-window carves even though the random tests missed them. A first-window-only statement for these levels is false. The two-window margin holds on the tested boxes. All eight first-window boxes at level 6 and 21 of the 24 at level 7 also admit a standalone second-window carve.

Reproduction sources and outputs can be requested from the workspace under `experiments/n8/obligation_audit_2026_11_11/`. They include the C++ box search, an independent Python reconstruction and replay of the positive witnesses, the clipped-plane checker, exact stress tests, and the Lean proof of the band equivalence. The legacy heuristic and data files were kept for provenance.
