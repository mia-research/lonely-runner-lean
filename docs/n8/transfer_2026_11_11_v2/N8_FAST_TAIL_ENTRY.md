# A finite entry reduction for four fast readings

Use ordinary normalized time $t=R/8$. A reading $v$ is clear when $\|vt\|\ge1/8$, where $\|\cdot\|$ is distance to the nearest integer. All phases are zero at $t=0$.

**Four-fast lemma.** Fix a nondegenerate bounded time interval $I$. There is a cutoff $C(I)$ such that any four positive readings with minimum at least $C(I)$ have a time in the interior of $I$ at which all four are strictly clear. The cutoff can be uniform over intervals of a fixed length contained in a compact range. The proof below uses compactness. A later endpoint argument gives an explicit cutoff in terms of the interval length and its maximum absolute endpoint. See [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md).

For the eight-runner filter, this discharges the asymptotic sector where the first three normalized readings stay bounded and all four remaining readings diverge. It also gives a finite family of harmonic slope types for any hypothetical limiting obstruction in that sector.

## A cover forces short relations

Write $L=|I|$. For one reading $v$, its closed bad phases have measure $L/4$ on $I$ up to an error at most $1/v$, by splitting into whole periods and one remainder. Boundary points have measure zero. If the four bad sets cover $I$, the measure of any pairwise intersection is at most the total excess multiplicity, hence at most $4/v_{\min}$.

Suppose $v_{\min}L\ge2400$. For a pair $u,v$ use the trigonometric polynomial
$$
P(t)=\cos^{80}(\pi ut)\cos^{80}(\pi vt).
$$
Outside the overlap of their bad phases, $P\le(6/7)^{40}$ since $\cos^2(\pi/8)=(2+\sqrt2)/4<6/7$. Thus the average of $P$ on $I$ is at most $(6/7)^{40}+4/2400$.

Expand the powers into exponentials. The zero-index coefficient is $(\binom{80}{40}/4^{40})^2$ and the sum of the absolute values of all coefficients is 1. The other frequencies have the form $mu+nv$ with $|m|,|n|\le40$. If all such frequencies had absolute value above $100/L$, their total contribution in absolute value would be at most $1/(100\pi)<1/300$, by direct integration of each exponential. The exact numerical inequality
$$
\left(\binom{80}{40}/4^{40}\right)^2-(6/7)^{40}>1/200
   = 1/300+4/2400
$$
gives a contradiction. Since each reading is at least $2400/L$, a small frequency must involve two coefficients of opposite signs. Therefore for **every pair** in a cover there are $1\le p,q\le40$ such that
$$
|pu-qv|\le100/L.
$$

In particular, compare each reading to the first. Taking a common denominator converts these finitely many choices into a representation $v_i=a_i\lambda+b_i$ with positive integer slopes $a_i$ from a finite set, bounded real drifts $|b_i|\le100/L$, and $b_1=0$. For example, if $p_i v_i-q_i v_1$ is bounded, take $P=\operatorname{lcm}(p_2,p_3,p_4)$, $\lambda=v_1/P$, $a_1=P$, and $a_i=q_iP/p_i$.

## Why the four-fold tiling cannot persist

If arbitrarily fast four-reading covers existed, pass to a subsequence with the same slopes $a_i$, with $b_i\to\beta_i$, and with $\lambda\to\infty$. For every $t$ in the interior of $I$ and $\phi\in\mathbb R/\mathbb Z$, the limiting phases have the form
$$
a_i\phi+\beta_i t.
$$
If all four were strictly clear for one such $(t,\phi)$, choose actual times $t_n=(k_n+\phi)/\lambda_n$ with $|t_n-t|\le1/(2\lambda_n)$. The phases converge to the chosen ones modulo 1, so all four readings eventually clear inside $I$.

Consequently a limiting obstruction would tile the phase circle by four closed bad sets at every $t$ in the interior of $I$. Each bad set has length exactly $1/4$ in $\phi$. The interiors are disjoint and the arcs meet at their boundaries.

There are just **three possible primitive sorted slope vectors** for such an instantaneous tiling. For two slopes $a_i,a_j$, reduce them by their gcd to $p,q$. Their pair of phases lies on an affine circle described by $q x-p y$ modulo 1. On the open bad square the range of this expression is the projection of $(-(p+q)/8,(p+q)/8)$. If $p+q>4$, that projection is the whole circle and the two bad interiors overlap for every offset. Thus unequal slopes can have reduced ratios only $1:2$ or $1:3$. Both ratios cannot occur relative to the minimum slope, since $2:3$ is forbidden. For a $1:q$ mix, rotate the tiling to put its boundaries on the grid of $4q$ equal slots. A slope-$q$ reading occupies one slot in each block of four and a slope-1 reading occupies $q$ consecutive slots. For $q=2$ the only mix that tiles has two of each slope. For $q=3$ one slope-3 reading leaves three consecutive slots per block, and two or more leave no run of three. The possible vectors are $(1,1,1,1)$, $(1,1,2,2)$, and $(1,1,1,3)$.

There is one argument against persistence for all three. Choose a time in the interior of $I$ that avoids every isolated coincidence of the affine arc endpoints modulo 1. There are finitely many such coincidences, since the interval is bounded and the endpoints are affine. At the chosen time any equality of endpoints therefore holds identically in time. Adjacent arcs in the tiling have the same endpoint velocity, so their readings have the same $\beta_i/a_i$. The cyclic adjacency of the tiling forces that ratio to be common to all four. At phase $\phi=-(\beta_i/a_i)t$ all four phases are then integers, contradicting disjoint interiors.

For a compact range of intervals of fixed length, any sequence of violating intervals has a subsequence containing a common positive-length subinterval. Applying the fixed-interval result to that subinterval proves the uniform version.

## Application to the normalized tail

Fix $M\ge1$ and assume $\rho_3\le M$. The checked lower-order margin result NStarK 5 applies to the first three readings. It gives a $1/5$-clear time in one of its narrower windows. By the Lipschitz bound for distance to an integer, the three slow readings stay $1/8$-clear on a closed interval of radius $3/(40M)$ about this time, within the corresponding ordinary-time window $[1/8,7/8]$ or $[9/8,15/8]$. The four-fast lemma now supplies a clear point in the same interval whenever $\rho_4$ exceeds a cutoff depending only on $M$. This result uses no upper bound on any of the four fast readings. The new analytic argument has yet to be formalized in Lean.

For ordinary positive isolation, the sectors with one, two, or three diverging readings can also be excluded by the lower-order margin and the existing one- to three-fast width argument. With $k$ fast readings and largest slow reading $M$, the ordinary-time slow cell has length $k/(4(8-k)M)$. The chain lengths for $k=1,2,3$ are at most $1/(4F)$, $3/(4F)$ and $7/(4F)$ when the least fast reading is $F$. Thus the sufficient ratios $F/M$ are $7$, $9$, and $35/3$. Any hypothetical escaping sequence for ordinary isolation would therefore have at least five diverging readings after passing to a subsequence. The analogous two-window exclusion for one or two fast readings still needs sufficient slow-clear intervals in those windows.

## Limits and exact controls

Five arbitrarily fast readings can cover a fixed time interval. For $v_i=\lambda+i/5$ with $i=0,\ldots,4$ and $t\in[19/20,21/20]$, their bad-arc centers in the common fast phase have largest cyclic gap at most $6/25<1/4$. Thus every time in the interval is blocked for every positive $\lambda$. This example concerns a chosen interval. It leaves open whether the slow readings have another clear interval that the same fast block fails to cover.

There is a further restriction when five fast readings share the same leading rate and have finite limiting drifts $\beta_i$, so their limiting phases are $\phi+\beta_i t$. If two drift phases coincide at an interior time of a slow-clear interval, the five-fast block has a strict witness in that interval. At the coincidence there are at most four distinct bad-arc centers. If the closed arcs fail to cover the phase circle, use a point outside them. If they cover it, there are exactly four distinct quarter-spaced centers, with one duplicated and three singletons. Choose two adjacent singleton centers. Their circular gap is $1/4$ at the coincidence and has nonzero derivative because their drifts differ. On one side of the coincidence the gap grows past $1/4$, while the other centers remain outside it by continuity. Its midpoint is strictly clear for all five. A permanent duplicate leaves at most four distinct affine phases, so the same four-arc argument gives a strict witness. In particular an obstructing equal-leading five-fast limit on an interval of length $L$ must have distinct drifts with $|\beta_i-\beta_j|\le1/L$ for every pair. A larger difference forces an interior coincidence. The [common-rate fast-block proof](N8_COMMON_RATE_FAST_BLOCK.md) subsequently closed the common-leading-rate cases across the full two-window domain, using a dilation of the slow time. General five- and six-fast configurations still need an entry argument.

The [exact replay script](fast_tail_entry_check.py) verifies the numerical Fourier bound, the pair projection on 1,728 rational controls, and all instantaneous tiling slope types by enumerating the grid placements. It also checks a four-fast family near an instantaneous tiling and a five-fast collision at three scales, along with the five-fast fixed-interval obstruction.

The argument yields a way to compute a cutoff. Rescale the interval length to one, retain the finite harmonic slopes from the short-relation lemma, and bound the drifts and the interval start. On that compact parameter domain, search for rational time and phase witnesses with positive margins. Strict clearance and compactness guarantee that a finite rational box cover eventually succeeds. Its smallest certified margin and smallest time buffer give a bound for lifting via the nearest aligned time. The direct endpoint calculation gives an alternative to that search. See [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md). The separate classical finite-checking literature gives reductions to bounded integer instances. The result here is an input-side reduction within the two cascade windows. [Tao](https://arxiv.org/abs/1701.02048) · [Malikiosis, Santos and Schymura](https://arxiv.org/abs/2411.06903)
