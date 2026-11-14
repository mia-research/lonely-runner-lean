# Large primitive harmonics: a finite reduction for the five-fast sector

Normalize the seven disparities so the slowest is 1. The pinned
windows are `[1/8,7/8]` and `[9/8,15/8]`. The five-fast sector
has two slow readings `1,a`; the six-fast sector has just `1`.
In a harmonic profile the fast rates are `p[i] λ + b[i]`,
with a common frequency `λ` and drifts bounded by `B`.

Let `dist` be distance to the nearest integer. A phase is clear if all its
coordinates have `dist > 1/8`. For a primitive positive integer slope vector
$p$, write $H_p=\{\phi p\bmod 1:\phi\in\mathbb T\}$.
The fast phase at a candidate slow time $t$ ranges over $x+H_p$, where
$x_i=b_i t\bmod 1$. At $2t$ it ranges over $2x+H_p$.

**Result (paper proof).** For five fast readings there are $P<\infty$ and
$\eta>0$ such that for every primitive positive $p\in\mathbb Z^5$ with
$\max p_i>P$ and every shift $x\in\mathbb T^5$, either $x+H_p$ or
$2x+H_p$ contains a phase with all distances at least $1/8+\eta$.
The cutoff is on the primitive slope, rather than the common frequency.
The argument gives a terminating procedure for obtaining bounds. A later proof supplies $P=424200$, $\eta=1/10000$, and a direct real-rate cutoff. See [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md).

### The new ingredient: a four-reading cover cannot survive doubling

On a connected four-reading harmonic circle with all slopes nonzero,
each coordinate's closed bad set has length $1/4$ at threshold $1/8$.
A cover of the entire circle therefore has pairwise disjoint bad
interiors. For two slopes, flip signs of coordinates if necessary and
divide both slopes by their gcd, obtaining coprime positive $a,b$.
If their shifts are $u,v$, the image circle in these two coordinates is
exactly the fiber of $b y_1-a y_2=b u-a v\bmod 1$. This is because
$(a,b)$ is primitive. On the open bad box
$(-1/8,1/8)^2$, the linear form $b y_1-a y_2$ has image the interval
$(-(a+b)/8,(a+b)/8)$ modulo one. Thus disjoint interiors require
`dist(bu-av) ≥ (a+b)/8`.

If the slopes differ, $a+b\ge3$. To cover at both shifts $x$ and
$2x$ would require both `dist(d) ≥ 3/8` and `dist(2d) ≥ 3/8` for
$d=bu-av$. The first puts $d\bmod1$ in $[3/8,5/8]$, so
`dist(2d) ≤ 1/4`. If all four absolute slopes agree, a cover consists
of four quarter circles that tile in the common phase coordinate.
Opposite bad centers differ by $1/2$; doubling makes them coincide.
In either case, at least one shift has a strictly clear phase. This
uses no bound on the harmonic slopes.

### Low rank phase fibers

Let $L\subset\mathbb R^k$ be a rational row space of rank at most three
with no coordinate vector in it. Put $H=L^\perp\bmod\mathbb Z^k$.
For any $x$, either $x+H$ or $2x+H$ contains a strictly clear point. Use a matrix
$A$ with integer rows forming a basis of the saturated lattice
$L\cap\mathbb Z^k$. Its torus kernel is $H$ (for example, by Smith
normal form). The columns of $A$ have no coloop: deleting one cannot
reduce the rank, since that would put the corresponding coordinate
vector in $L$.

Ranks zero to two can solve every target using the smaller clear
box $(1/7,6/7)^k$. Rank zero has no constraints. Rank one has two
disjoint column bases, since no column is a coloop. Rank two also
has two disjoint bases if at least four columns are nonzero: any
parallel class with at least two columns must have at least two
outside it, and if all classes are singletons any two pairs work.
Each basis maps its clear box to a set of measure at least
$(5/7)^r>1/2$ in the quotient torus, since the integer matrix with
those columns sends uniform measure to uniform measure. The sum
of two sets of measure greater than half is the whole torus: one
meets every translate of the negative of the other. Fix the other
coordinates at $1/2$. In the rank-two case with at most three
nonzero columns, each of their phases is uniform on a fiber (no
coordinate is frozen); the union bound for bad phases is at most
$3(2/7)<1$. Zero columns are free.

In rank three, a circuit of two or
three columns can be solved after solving the projected problem in the
quotient by its span. That quotient has rank at most two and inherits
the no-coloop property. The circuit has a connected circle component
with every coordinate moving, so its at most three bad sets have total
length at most $3/4$.

Otherwise any three nonzero columns are independent. Choose four of
them. The corresponding connected circle component can fail only by
tiling. For each cyclic order of its labeled arcs, their lengths fix
the centers up to rotation; one center per coordinate fixes all four
shifts up to the circle action. Hence there are only finitely many bad
targets in the circuit's quotient. If a fifth nonzero column exists,
vary that coordinate in the open clear interval. Its image under $A$
moves along a nonconstant segment, avoiding the finite set. All other
free coordinates can be chosen in the open clear interval as well.
If there are exactly four nonzero columns, use the four-reading
doubling argument on one component at $x$ and its doubled component
at $2x$. Zero columns give unconstrained coordinates.

### From low rank to a bound on slopes

Suppose there were unbounded primitive five-reading slopes $p_j$ and
shifts $x_j$ for which both candidate phases failed at thresholds
$1/8+1/j$. Pass to a subsequence with $x_j\to x$ and, for each
integer $m$, with the indicator of $m\cdot p_j=0$ eventually
constant. The integer modes eventually zero form a saturated lattice
with real span $L$ of rank at most three: four independent such
relations would pin $p_j$ to a fixed rational line, which contains
only one positive primitive vector. No coordinate vector belongs to
$L$: a nonzero integer multiple of it would then be an eventually
zero mode, whereas every coordinate of $p_j$ is positive.

Uniform measures on $H_{p_j}$ converge weakly to uniform measure on
$H$. Their Fourier coefficients are the mode indicators just
described, and trigonometric polynomials are dense in the continuous
functions. The same convergence holds for the translates at $x_j$
and $2x_j$. The low rank lemma supplies a strictly clear point on
one limiting translate. A small neighborhood in that fiber has
positive measure and a positive clearance margin. A continuous bump
supported in that neighborhood in the ambient torus has positive
limiting integral, contradicting failure on the corresponding
$H_{p_j}$. This proves the uniform high-slope result.

For an effective version, start at $N_0=1$. At stage $i=0,1,2,3$,
enumerate row spaces of rank at most three spanned by integer vectors
of sup norm at most $N_i$, excluding any containing a coordinate
vector. Find a common rational margin `δ > 0` for the low rank lemma
on this finite list. For each space, test decreasing dyadic margins:
the desired implication for every $x\in[0,1]^k$ is the union, over
$q=1,2$ and finitely many integer $z$, of projections of
$A y=q A x+z$, $y\in[1/8+\delta,7/8-\delta]^k$. These are
rational polytope coverage tests. Compactness and strict clearance
guarantee termination.

For the next frequency cutoff, let $g$ be the one-dimensional tent
with peak one at $1/2$ and support $[1/8,7/8]$, and put
$F(y)=\prod_i g(y_i)$. If the margin is `δ`, on a sup ball of radius
`δ/2` around the witness, $F\ge\delta^k$. The ball in any fiber has
Haar measure at least $M^{-k}$ for $M>2/\delta$: partition the
ambient torus into $M^k$ cubes, choose one with mass at least
$M^{-k}$, and translate one of its fiber points to the witness.
Thus the favorable fiber integral is at least
$\mu=(\delta/M)^k$. The absolute Fourier coefficients of $g$ sum
to one (all terms have the same sign at the tent peak); for $j\ne0$ they are bounded by
$1/((3/8)\pi^2 j^2)$ (integrate the two linear pieces). The tail
past $N$ has absolute sum less than $1/N$, so truncating all
coordinates of $F$ costs at most $k/N$ in sup norm. Choose
$N_{i+1}>\max(N_i,4k/\mu)$.

If the span of the exact relations for $p$ does not grow from
$N_i$ to $N_{i+1}$, the Fourier modes through $N_{i+1}$ agree
between $H_p$ and the fiber used at that stage. The favorable
translated integral on $H_p$ is then at least $\mu/2$, giving
margin at least $3\mu/16$ at a point. If the span grows at every
stage, there are four independent relations with coefficients at
most $N_4$. For five readings, the signed minors of those four
rows give a nonzero vector along $p$; primitivity implies
`max p_i ≤ 4! N_4^4`. The minimum of the four stage margins gives
a uniform computable `η` for slopes above this bound.

### What this closes in the cascade

The five-reading slow-time lemma for dilations $1,2,5$ in
[the Lean kernel](lean_kernel/Fresh/HarmonicSlow.lean) already clears
the slow readings $1,a$ with the required margin at $t$ and $2t$.
The phase rounding argument carries the new high-slope result to an
actual witness when the common frequency is at least $40a$ and
$B/(2\lambda)\le\eta$. Thus the primitive five-reading harmonic
profiles that still need a dedicated argument are a finite set.
The bound and additional exact profile checks are in [explicit fast cutoffs](N8_EXPLICIT_FAST_CUTOFFS.md).

The same low rank lemma works with six coordinates. The frequency
argument shows that a six-reading phase obstruction at a suitable
positive margin needs four independent bounded exact relations:
its leading direction lies in one of finitely many rational planes.
The new result leaves the clear-phase problem for general planes,
the two-leading-direction real-rate tail, and Lean formalization
of the short-relation reduction open. These remain separate
obligations for the global cascade cutoff.


### Exact controls

The [exact rational replay](harmonic_frontier_check.py) examined
444 primitive four-reading slope profiles through 9. Three survived
one dilation at threshold `1/8`; none survived both. None survived
both at `13/100` either. The latter margin check is limited to
those 444 profiles. The same replay closed 641 additional five-reading
profiles with maximum 10 and 125 six-reading profiles with maximum 5.
See [the recorded output](harmonic_frontier_check.out).

### A reusable test for six-reading planes

A rational plane containing a direction already covered by a six-reading
phase theorem inherits that theorem on each translate of the plane.
Indeed, the circle along that direction is contained in the plane.
For example, if the plane contains a positive primitive mixed vector
with maximum at most five, the phase result underlying
`Fresh.Harmonic.six_rates` applies to the circle at any shift and
the same five dilations, with margin at least `13/100 - 1/8`.
Coordinate permutations and sign flips preserve this argument.
A plane containing the all-ones vector similarly inherits the
six-point gap result at threshold `27/200`.

This test includes full-support planes. For instance, span the plane
by the all-ones vector and `(1,2,3,4,5,6)`. Any two coordinate
functionals restricted to this plane are independent. Nevertheless
one circle already supplies a witness in every shifted plane at one
of the five dilations. This certifies the phase-fiber step. For a
real rate vector, one still has to show that the actual trajectory
can reach such a phase with the necessary time and clearance margins.

### Effective short relations for arbitrary fast rates in these windows

The same argument gives a finite reduction for real rates before assuming
any harmonic form. Suppose there is an interval $J$ of length $\ell>0$
such that every time in $J$ and $2J$ is allowed and clears the slow
readings. For the five-fast case with $1\le a\le A$, use the buffered
$t$ and $2t$ from the slow-time lemma and take the radius of $J$ to
be $1/(320A)$. The slow phases and window boundaries change by at
most $1/160$. For the six-fast case use the first two multiples of
$3/20$, with $J$ of radius $1/160$.

There are computable $N,D,C$ (depending on $\ell$) such that, for
a real rate vector $v$ with all fast rates greater than $C$, one of
the following holds:

- Some time in $J\cup2J$ clears every fast reading strictly.
- Four independent integer rows $m_j$ satisfy
  $\|m_j\|_\infty\le N$ and $|m_j\cdot v|\le D$.

To obtain the bounds, use the same four stages as above, starting
with $N_0=D_0=1$. Choose $N_{i+1}>\max(N_i,16k/\mu_i)$ and
$D_{i+1}>\max(D_i,16/(\ell\mu_i))$, where $\mu_i$ is the uniform
lower bound from the low rank margin calculation at stage $i$.
Take $C=6N_4^2D_4$. Let $L_i$ be the span of the integer rows
within bounds $N_i,D_i$. If the conclusion with four rows does not
already hold, all $L_i$ have rank at most three and one transition
has $L_i=L_{i+1}$. No $L_i$ contains a coordinate vector: if it did,
a basis of $r\le3$ bounded rows and a nonsingular minor would
express that coordinate vector with coefficients of absolute value
at most $(r-1)!N_i^{r-1}$, by Cramer's rule. Its dot product with
$v$ would be at most $r! N_i^{r-1}D_i\le C$.

Let $H=L_i^\perp\bmod\mathbb Z^k$ at the stable transition and
let $G(y)$ be the Haar average of $F$ on $y+H$. For each $t\in J$,
the low rank lemma and its uniform margin give
$G(tv)+G(2tv)\ge\mu_i$. This holds pointwise, even if the preferred
dilation changes with $t$. Integrate over $J$ with normalized
length measure. For either $q=1,2$, the averages of $F(qtv)$ and
$G(qtv)$ differ by at most $2k/N_{i+1}+1/(\ell D_{i+1})$: truncate
both Fourier series as above, and then only modes outside $L_i$
remain in the difference. Each such mode in the cutoff has
$|m\cdot v|>D_{i+1}$ by stability, so its normalized time integral
has absolute value at most $1/(\pi q\ell D_{i+1})$; the sum of the
absolute coefficients of $F$ is one. The total error for the two
averages is less than $\mu_i$, so $F$ is positive at an allowed time.
This contradicts an obstruction and proves the two alternatives.

Four bounded rows give finitely many rational kernels. The real
rate vector is within a bounded additive error of one of them:
solve the four residual equations in four coordinates using any
nonsingular minor and set the other correction coordinates to
zero. Each correction coordinate has absolute value at most
$4!N^3D$, by Cramer's rule and the integer determinant bound.
With five fast readings, the kernel is a line; beyond that error
bound it has a positive primitive direction and the drift is
bounded. With six fast readings the kernel is a plane. This is
an effective arbitrary-input reduction in the stated slow
windows. It does not yet certify all the resulting line or plane
types, or cover the other slow regimes of the global cascade.
