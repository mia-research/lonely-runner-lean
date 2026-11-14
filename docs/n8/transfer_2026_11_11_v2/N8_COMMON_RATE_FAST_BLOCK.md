# Explicit entry for five or six readings near a common rate

Use ordinary normalized time $t=R/8$ and the two windows $[1/8,7/8]$ and $[9/8,15/8]$. A reading $v$ is clear when $\|vt\|\ge1/8$, where $\|\cdot\|$ denotes distance to the nearest integer.

**Five-fast result.** For normalized readings $(1,a,\lambda+\beta_1,\ldots,\lambda+\beta_5)$ with $a\ge1$ and $0\le\beta_i\le B$, a common clear time in the two windows exists whenever
$$
\lambda\ge \max(40a,50B).
$$
We may take $\lambda$ to be the least fast reading and $B$ the difference between the largest and least fast readings.

**Six-fast result.** For readings $(1,\lambda+\beta_1,\ldots,\lambda+\beta_6)$ with $0\le\beta_i\le B$, the same conclusion holds if
$$
\lambda\ge \max(20,50B).
$$
This case supplies a witness in the first window.

In particular, the five-fast common-leading-rate escape case is closed when the two slow readings are bounded. The condition also permits drifting differences that diverge, provided the spread within the fast block is small enough relative to its least reading. These sufficient conditions depend only on the input speeds.

## Three dilations of five phases

For any five points on the circle, including repeated points, at least one of the dilations by $1,2,5$ has a largest cyclic gap strictly greater than $27/100$. For six points the same conclusion holds with multipliers $1,2,3,4,5$.

Here is the finite certificate. Translate one point to zero and sort the others $0\le z_1\le\cdots\le z_{n-1}\le1$. Translation only rotates each dilate. A covering at gap cap $q=27/100$ requires the $m=1$ consecutive gaps and the wrap gap to be at most $q$. For each subsequent multiplier $m$, order the $n-1$ remaining residues around the fixed zero and choose integers $k_i\in\{0,\ldots,m-1\}$ with residue $m z_i-k_i$. A point at zero modulo one can also be represented at the right endpoint by residue 1. For consecutive residues, with $(z_0,k_0)=(0,0)$, impose
$$
\frac{k_i-k_j}{m}\le z_i-z_j\le\frac{k_i-k_j+q}{m}.
$$
Impose that each residue is at most 1 and that the final residue is at least $1-q$. These are all difference inequalities with denominators dividing $100\operatorname{lcm}(m)$.

The exact search keeps the closed matrix of upper bounds on $z_i-z_j$. If a new inequality would close a negative cycle, the branch is impossible by summing the inequalities around that cycle. Every point pattern with all gaps at most $q$ would supply an ordering and lap choice at each step. The following exact counts are the distinct surviving bound matrices.

| Points | Multipliers applied successively | Surviving matrices |
| --- | --- | --- |
| Five | $1,2,5$ | $1,6,0$ |
| Six | $1,2,3,4,5$ | $1,52,52,52,0$ |

The [exact replay](fast_dilation_check.py) reproduces both rows with incremental closure and independently with full Floyd–Warshall closure.

## Keep both slow readings clear at all three times

Put
$$
I=(11/80,69/400),\quad J=(91/400,149/400),\quad K=(331/400,69/80).
$$
For a base time $t\in I\cup J$, the times $t,2t,5t$ lie in the two prescribed windows, each with distance at least $1/80$ to its window boundary. If $at$ lies in $J$, $K$, or an integer translate of $J$, each of $at,2at,5at$ has distance at least $11/80$ to the nearest integer. These bounds follow by multiplying the interval endpoints.

For $t\in(l,u)$ and $at\in(v,w)$, the two conditions can be satisfied simultaneously exactly when $a\in(v/u,w/l)$. The five rows below cover $[1,7]$ by overlapping intervals.

| $t$ range | $at$ range | Open range of $a$ |
| --- | --- | --- |
| $J$ | $J$ | $(91/149,149/91)$ |
| $I$ | $J$ | $(91/69,149/55)$ |
| $J$ | $K$ | $(331/149,345/91)$ |
| $J$ | $1+J$ | $(491/149,549/91)$ |
| $J$ | $2+J$ | $(891/149,73/7)$ |

For $a\ge7$, the interval $aJ$ has length greater than one. It therefore contains a point in an integer translate of $J$. Thus a base time $t$ is available for every real $a\ge1$. With just one slow reading, use the fixed base time $3/20$. Its first five multiples lie in the first window with distance at least $1/40$ to its boundary.

## Lift the free phase back to a time

At the base time $t$, apply the dilation lemma to the drift phases $-\beta_i t$. At one of the allowed multiples $T=mt$, their bad-arc centers have a gap greater than $27/100$. Take $\phi$ at the midpoint of the gap. Then $\|\phi+\beta_i T\|>27/200$ for every fast reading.

Choose an integer $k$ nearest to $\lambda T-\phi$ and set
$$
s=(k+\phi)/\lambda.
$$
The common fast phase at $s$ is exactly $\phi$ modulo one, and $|s-T|\le1/(2\lambda)$. The change in the remaining fast phase is at most $B/(2\lambda)\le1/100$. Their clear margin remains above $27/200-1/100=1/8$. In the five-fast case, the slow phases change by at most $a/(2\lambda)\le1/80$. In the six-fast case the pinned phase changes by at most $1/(2\lambda)\le1/40$. The same time buffers keep $s$ in the chosen window.

This proves both input-side rules. The exact script checks 2,000 lifted rational examples, including cases at the rate cutoffs. The finite phase lemma and the lifting argument have yet to be formalized in Lean. Five- and six-fast configurations with several leading rates, or with a substantial spread inside the fast block, still require an entry argument.
