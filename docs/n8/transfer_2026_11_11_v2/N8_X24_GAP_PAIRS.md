# Two slow gaps suffice throughout X24

Let $1=\rho_1\le\cdots\le\rho_6\le\rho_7$ be the seven normalized readings. For every fixed slow profile $(\rho_1,\ldots,\rho_6)$ that occurs with $\rho_7\in[23,25]$, **at most two common slow gaps suffice for the entire admissible interval of $\rho_7$**. The same statement holds on the wider closed band $\rho_7\in[22.5,25.5]$. A gap lies within $W_0=[1,7]$ or $W_1=[9,15]$. The choice of the gap pair depends only on the slow profile.

Lean now supplies the full X24 theorem, including the initial grid cover, dyadic subdivision, and the existence of two gaps independent of the fastest reading. The finite arithmetic is evaluated by Lean's native evaluator. The bundled integer verifier provides a separate exact replay.

## The two-gap rule

A common slow gap $I=[L,U]$ is blocked by a fastest reading $x$ precisely when

$$
x\in B(I)=\bigcup_{j\in\mathbb Z}
\left(\frac{8j-1}{L},\frac{8j+1}{U}\right).
$$

Indeed, $x[L,U]$ is an interval. If it contains no clear phase, it lies entirely in one open bad zone $(8j-1,8j+1)$. Both inequalities are strict because phase endpoints are clear. If $x\notin B(I)$, use $R=L$ when $xL$ is already clear. Otherwise take the right endpoint of its bad zone, which lies in $[L,U]$.

For a top range $[a,b]$, put $X=[\max(a,\rho_6),b]$. One gap suffices if $B(I)\cap X=\varnothing$. Two gaps suffice if $B(I)\cap B(J)\cap X=\varnothing$. The certificate is chosen before $x$ is known. [GapPairs.lean](lean_kernel/Fresh/GapPairs.lean) proves the two-gap implication and produces the existing BandClearPoint conclusion.

## Why two can be necessary

For the slow profile $(1,19,20,21,22,23)$, there are 44 maximal slow gaps across the two windows. Exact interval intersection shows that each has a blocker in $[23,25]$. The two gaps
$$
[25/19,31/23],\qquad [49/22,47/21]
$$
have blocking intervals $(589/25,759/31)$ and $(1210/49,1197/47)$, respectively, within the top domain after intersection with $[23,25]$. They are disjoint since $759/31<1210/49$. Thus the pair works for the entire top interval even though every single gap can fail. [Exact replay](x24_pair_certificate/one_cell_control.py)

## Coverage over the continuum

Cover the five unpinned slow readings by the closed nearest-integer faces with nondecreasing centers in $\{1,\ldots,25\}$. The first and last faces are clipped to the range. These 118,755 boxes cover every sorted profile for both top bands. On each box, the generator either certifies one or two fixed closed time cells for every slow profile in the box, or bisects a coordinate and visits both closed children.

The independent verifier reconstructs every root and split from the certificate stream. For each leaf it checks both endpoints of each time-times-face product interval against one closed clear gap. Then it independently enumerates every possible fast bad lap and checks the required empty intersection over the enlarged closed range $[\max(a,\mathrm{lo}_6),b]$, where $\mathrm{lo}_6$ is the lower face for the sixth reading. This range contains the admissible top interval for every actual profile in the box. The verifier includes boundary equalities. The maximum fast product is $15\cdot25.5=382.5$, so fast bad laps $j=1,\ldots,47$ suffice.

| Closed top band | Single-cell leaves | Two-cell leaves | Unresolved | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| $[23,25]$ | 492,826 | 341,737 | 0 | 26 |
| $[22.5,25.5]$ | 477,515 | 524,693 | 0 | 26 |

The leaf counts report the certificates selected by the generator. The exact example above establishes that two are sometimes necessary. Negative checks confirmed that the verifier rejects truncated trees, invalid split axes, out-of-window cells, invalid slow gaps, blockable single cells, and pairs sharing a blocker.

## Replay

From the handoff directory, compile the standalone C++ programs and stream the certificate. A compiler with 128-bit integer support suffices.

    cd x24_pair_certificate
    c++ -O3 -std=c++20 box_cover.cpp -o /tmp/x24-cover
    c++ -O3 -std=c++20 replay.cpp -o /tmp/x24-replay
    set -o pipefail
    /tmp/x24-cover 1 25 32 --certificate | /tmp/x24-replay
    /tmp/x24-cover 1 25 32 --certificate --wide | /tmp/x24-replay
    python3 one_cell_control.py

The archive includes the two programs and saved outputs. The certificate stream is generated on demand. The resulting X24 witnesses feed the existing two-window cascade bridge. The broader eight-runner proof still needs coverage outside this slice.

## Lean replay and trust boundary

The executable [X24Compute.lean](lean_kernel/X24Compute.lean) constructs candidate cells and checks them using integer arithmetic. Its final pair test independently scans all 47 possible fast bad laps. A successful leaf uses only those checked cells. The search's pruning rules need no correctness hypothesis.

[X24Sound.lean](lean_kernel/Fresh/X24Sound.lean) proves the leaf and split implications. [X24Total.lean](lean_kernel/Fresh/X24Total.lean) proves that the nearest-integer roots cover every sorted slow profile and that the pointwise conclusion transfers to any permutation of the readings. These implications use only Lean's standard axioms.

[X24Checked.lean](lean_kernel/Fresh/X24Checked.lean) evaluates the entire closed arithmetic statement with `native_decide`. Lean records one generated axiom for this computation. The resulting theorems `x24WideCells` and `x24WideBand` are in [X24Theorem.lean](lean_kernel/Fresh/X24Theorem.lean). The first gives cells uniform in the last reading, and the second gives `BandClearPoint` for any normalized order. The full replay by kernel reduction alone remains open.

The portable `check_kernel.sh` compiles the integer evaluator to a Lean plugin with `leanc` before running the native check. `lake build` also supports precompilation of this module. The Lean replay regenerates the cover directly from the arithmetic definitions. The separate C++ proof stream is optional.
