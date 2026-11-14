# Which reductions move the eight-runner proof forward

The project has two targets. Classical isolation asks for a positive time with clearance at least (1/8). The cascade window theorem requires that witness in the first two windows of the smallest normalized reading. Rosenfeld's computer-assisted proof gives the classical result in the literature. The independent Lean proof and the stronger cascade window claim are the objectives here. [Rosenfeld's proof](https://arxiv.org/abs/2509.14111) · [Tao's finite reduction](https://arxiv.org/abs/1701.02048)

## What changed the proof obligations

| Work | What it discharged | What remained |
| --- | --- | --- |
| Landing labels and lap vectors | Describe an available witness and give finite lap bounds on a bounded input domain. | Establish entry from arbitrary inputs and cover the entire bounded domain. |
| Exact box and window certificates | Give local witnesses and expose how witness times move across boundaries. | Connect the certified regions to a complete cover. The count of certificates by itself measures neither implication. |
| Finite Fourier tests and four independent rows | Force a bounded integer row span from failure on buffered paired intervals. Applies before choosing a landing. | Five- and six-fast line and plane neighborhoods still need witnesses. |
| Periodic bad-length estimate and compactness | Close the three-fast sector and give a common append rule for one to three fast readings. | Slow prefix strict clearance in the allowed window. |
| Whole-input scaling | Gives the classical route four **exact** rows from the same buffered theorem. | Cover the seven-reading inputs in the resulting kernels. |

The last row is a consolidation we could have made as soon as the buffered four-row theorem checked. On unrestricted time, apply it to (Kv) on ([1,2]) and its double. A clear time transports to the original input by multiplying time by (K). A row (m) on the finite list with (mcdot v
e0) cannot remain bounded as (K) grows. Choose (K) large enough for the whole list at once. Lean then reduces classical isolation to the kernels of rank-four matrices in a finite row table. Each kernel has dimension three by rank-nullity. The row bound is existential, and inputs within each kernel still range over real parameters. [ExactFourReduction.lean](lean_kernel/Fresh/ExactFourReduction.lean)

For the two-window route, scaling speeds and transporting time changes the normalized window under consideration. Keep its outstanding coverage obligations separate from classical isolation. In particular the numerical cutoff 424,200 belongs to one way of organizing the harmonic profiles. A proof that treats the residual families directly can use the qualitative reduction.

## The last two fast sectors

For a fixed positive slow prefix with a pinned reading of 1, Lean proves an equivalence. A strict slow witness in the two windows exists exactly when every sufficiently fast block of a specified size from one through three can be appended within those windows. The reverse implication matters. If the strict witness is absent, every weak witness touches a boundary of a slow reading. A bounded time horizon has finitely many such touches. Simultaneous recurrence brings a single arbitrarily large integer reading within distance (1/8) of an integer at all of those times. That reading can be the first member of a block of distinct fast readings. The forward implication uses the open slow interval and the checked fast interval bound. [WindowObstruction.lean](lean_kernel/Fresh/WindowObstruction.lean)

For five slow readings, the existing append rules reduce the strict **first-window** question to a bounded box. Four fast readings over the pinned reading clear on a paired subinterval of the first window. For fewer fast readings, successively bound the slow prefix and append to the four-reading strict witness. This leaves a single bounded problem and the bound is existential. For six slow readings, an analogous plan must account for a five-fast line sector and, when the first five are bounded, the five-slow window problem. [SlowFiveReduction.lean](lean_kernel/Fresh/SlowFiveReduction.lean)

I checked 105,680 rational five- and six-reading tuples with exact lap intersections. Each had a strict first-window interval. The corpus's exact chain search also exhausted the first-window closed-cover search on the real five-slow box through maximum reading 49 and the six-slow box through 17. The six-slow run through 24 reached its time cap. The grid experiments and the chain search are distinct checks. Neither evaluates the cutoff in the Lean reduction or closes the six-slow problem. [Exact grid replay](slow_window_audit.py)

The real-box check used the corpus's `experiments/n8/chain_cover_v4.py` with `search(n, Fraction(B), Fraction(1), [(1, 7)], False, node_cap, deadline)`. The closed-cover convention tests for absence of strict clearance. The five-slow run through 49 finished after 10,730 search nodes and the six-slow run through 17 after 4,277. These search outputs are exact computational evidence and are outside the Lean proof.

The earlier E358 example defeats a first-window claim at (1/7), yet it has a strict (1/8) first-window witness. On the other hand, the four-slow proof's sum-of-bad-lengths argument already fails for five readings. For ((1,25/7,33/7,41/7,7)), the four individual losses in the first window sum to (402433/473550>3/4), although the common clear interval ((41/56,161/200)) has width (51/700). The remaining estimates need information about overlaps or about where the cover can make progress. [Exact grid replay](slow_window_audit.py)

## How to spend the next proof effort

Use the theorem whose conclusion matches the target. For classical Lean isolation, start with the exact three-dimensional kernels and ask for a witness construction or a further reduction that handles a whole class of row spaces. Test it first on tight integer profiles such as ((1,2,3,4,5,6,7)) and on actual residual row spaces. A criterion based on strict clearance alone cannot close an equality case. For the two-window claim, work on the bounded five-slow obstruction and seek a symbolic constraint on covering chains that survives beyond the checked box. A numerical cutoff is worth deriving when it is small enough to combine with an actual coverage certificate.

At each step, record the input domain removed, the quantified statement still owed, and one test that could refute the proposed mechanism. Before expanding a census, check whether its proof can be expressed in the variables of the downstream theorem. The Fourier rescaling and the append equivalence are examples of finding that implication using work already in the tree.
