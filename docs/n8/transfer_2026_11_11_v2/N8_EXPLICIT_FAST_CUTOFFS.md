# Explicit cutoffs for the fast sectors

Use normalized time and the clearance threshold \(1/8\). A phase of a
reading is its value modulo one. Write \(c=51/400=1/8+\delta\), where
\(\delta=1/400\). The analytic cutoff arguments below are paper proofs. Lean now checks the finite profile replay, the symbolic append and slicing rules, and their real-rate witnesses where stated in the [Lean finite-reduction note](lean_kernel/FINITE_RELATIONS.md).

## A uniform four-reading margin

On any harmonic circle with four nonzero integer slopes and any shift
\(x\), either the circle shifted by \(x\) or the circle shifted by \(2x\)
has clearance strictly greater than \(c\).

Each bad set at threshold \(c\) has measure \(2c\). In a cover every
pairwise overlap is at most \(8c-1=1/50\), since the excess multiplicity
has that integral. Work with absolute slopes by reflecting coordinates.
For unequal slopes, reduce a pair to coprime positive integers
\(a<b\). Rescaling the common circle parameter by their gcd preserves
measure. If \(b\ge4\), condition on the phase with slope \(b\). Its
preimages have the other phase on a grid of \(b\) equally spaced points.
At threshold \(1/8\), at least \(\lfloor b/4\rfloor\) of these points
lie in the closed bad arc. The joint measure is at least
\(\lfloor b/4\rfloor/(4b)\ge1/28>1/50\).

For \(b\le3\), let \(d\) be the difference of shifted phases after
applying the linear form \((b,-a)\). At least one of
\(\|d\|,\|2d\|\) is at most \(1/3\), where \(\|\cdot\|\) denotes
distance to an integer. Use that dilation. In the lifted bad square
\([-1/8,1/8]^2\), a fiber of \((b,-a)\) with representative
\(|d|\le1/3\) has \(b y_1\) ranging over the intersection of
\([-b/8,b/8]\) and \(d+[-a/8,a/8]\). Its length in the circle parameter
is at least
\[
 \frac{\min\{(a+b)/8-1/3,\ a/4,\ b/4\}}{ab}.
\]
The primitive pair \((a,b)\) parametrizes the entire fiber on the
two-torus. On this segment \(b y_1\) has derivative \(ab\) in the
circle parameter, which gives the formula. The three coprime pairs
have lower bound at least \(1/48>1/50\).

If all slopes have equal absolute value, reflect coordinates and use
the common phase. In a cover at the first dilation, consecutive bad
centers have gaps at most \(2c\). The clockwise separation of a pair
two places apart is between \(1-4c\) and \(4c\). After doubling the
pair has circular distance at most \(8\delta\). Its bad arcs overlap
by at least \(2c-8\delta>1/50\). In every case one dilation fails to
cover.

The same two-dilation statement holds at \(13/100\) by a small
exact replay. At that threshold the pair overlap budget is \(1/25\).
For an unequal pair with reduced maximum \(b\ge8\), the conditional
grid bound is at least \((26/100)\lfloor b/4\rfloor/b\).
For \(b=4m+r\) with \(m\ge2,\ 0\le r\le3\), the fraction is at
least \(2/11\), which exceeds the overlap budget after multiplying
by \(26/100\). Hence a cover can only occur when every reduced pair
has maximum at most seven. Normalize all slopes by the minimum.
Each of the other three ratios is in the finite list of reduced
\(a/b\ge1\) with \(a,b\le7\), and each quotient of two ratios
must meet the same bound. The denominators then determine the
primitive integer tuple by their least common multiple. The
exact endpoint replay checks all 313 such four-profiles, whose
largest maximum is 210. None survives both dilations at \(13/100\).

Two five-reading families follow directly. Suppose a primitive profile
has a subtuple of four slopes with gcd \(g>1\). Take the four-reading
witness and translate its common parameter by multiples of \(1/g\).
The four phases stay fixed and the remaining phase traverses a full
\(g\)-point grid, because primitivity gives coprimality with \(g\).
One grid point has distance at least \(1/4\) to an integer. Also,
if one slope is at least \(26\) times the largest of the other four,
use their \(13/100\)-clear phase. They stay strictly clear at
\(s=1251/10000\) in an interval of radius
\((13/100-s)/\max_{i\ne j}|p_i|\) about the witness. The interval
is longer than one bad arc of the remaining phase at \(s\), since
\(26(13/100-s)>s\). The gcd test keeps the full \(13/100\) margin.

## Explicit bounds for the five- and six-fast reduction

The same threshold \(13/100\) works for any torus fiber whose rational relation
space has rank at most three and contains no coordinate vector. For
rank zero, one or two, use the coloopless argument at threshold \(1/7\)
in the harmonic cutoff note. For rank three with a circuit of two or
three nonzero columns, solve the projected problem in the quotient at
\(1/7\). Along the circuit's one-dimensional fiber the bad sets at
\(13/100\) have total measure at most \(78/100<1\). In the remaining rank-three
case choose four nonzero columns. They have rank three and any three
are independent. Fix all other coordinates of the first translate
to \(1/3\). A particular point in that translate exists because the
chosen four columns span the relation quotient. They leave one
connected harmonic circle with four nonzero slopes. In the doubled
translate the fixed coordinates become \(2/3\). Apply the uniform
four-reading result to those two circles. This avoids computing a
margin separately for each row space.

Let \(k\) be five or six, and use the product tent from the harmonic
cutoff note. A fiber with clearance greater than \(13/100\) has tent
integral at least \(\mu=60000^{-k}\). In an ambient sup ball of
radius \(1/400\) around the witness each tent factor is at least
\(1/150\). Partition the torus into \(400^k\) half-open cubes and
translate a fiber point in a cube of greatest fiber mass to the
witness. This gives the ball Haar mass at least \(400^{-k}\).
The absolute Fourier coefficients of the product sum to one and the
tail beyond sup norm \(N\) is at most \(k/N\).

For arbitrary real fast rates \(v\), let \(J\) have length \(\ell\)
and suppose \(J\) and \(2J\) are both allowed slow-clear intervals.
Take \(N=8k\,60000^k,\ D=8\,60000^k/\ell,\ C=6N^2D\).
Span **all** integer rows through \(N\) with \(|m\cdot v|\le D\).
If there are four independent rows the finite reduction follows
directly. Otherwise rank is at most three. When \(\min_i v_i>C\),
Cramer's rule excludes coordinate vectors from the row space.
At each \(t\in J\), one projected fiber at \(tv\) or \(2tv\) has tent
average at least \(\mu\). Integrate the sum over \(J\). For either
dilation the averaged difference from the actual tent is at most
\(k/N+1/(\ell D)\). Modes outside the row space through \(N\) have
\(|m\cdot v|>D\) and each contributes at most
\(1/(\pi\ell D)\) times its absolute coefficient. The total error
for both dilations is at most \(\mu/2\). Hence the actual rates clear
some allowed time or have the four stated relations. The row
count and bounded correction via minors are as in the harmonic
cutoff note. No iteration over ranks is needed. For \(\ell=1/(160A)\)
in the five-fast windows one may take \(C<6\cdot10^{78}A\).
For \(\ell=1/80\) in the six-fast windows one may take
\(C<9\cdot10^{92}\).

## The exact harmonic cutoff is 424,200

The Fourier bound for real rates does not control the cost of
enumerating exact slope profiles. For the exact problem use
Banaszczyk's Euclidean transference inequality
\(\rho(\Lambda)\lambda_1(\Lambda^*)\le d/2\) for a rank-\(d\) lattice,
where \(\rho\) is covering radius and \(\lambda_1\) is shortest nonzero
length. [Banaszczyk, Theorem 2.2](https://doi.org/10.1007/BF01445125)

Set \(s=1251/10000\). Suppose neither shifted harmonic circle at
\(x,2x\) has clearance strictly greater than \(s\). Start with the
empty set of exact relations of the integer slope vector \(p\).
Given \(r\le3\) independent relations, let \(L\) be their real span,
\(V=L^\perp\), \(\Gamma=V\cap\mathbb Z^k\), and
\(W=V\cap p^\perp\). The lattice
\(\Lambda=\operatorname{proj}_W\Gamma\) has rank \(d=k-r-1\).
The projected difference between a target and its translated
harmonic circle measures distance to this lattice. Indeed, one
can move along the real line of \(p\) and add any element of
\(\Gamma\), and projecting onto \(W\) eliminates exactly the line
of \(p\).

For ranks \(0,1,2,3\), the larger fiber has a point with clearance
at least \(c_r=1/2,6/25,1/7,13/100\), respectively, at one of the
two shifts. In rank one, the two disjoint column bases each map
their open clear intervals to a set of measure at least
\(1-2(6/25)>1/2\). Their sum covers the quotient. The other ranks
use the previous arguments. The relation space contains no
coordinate vector since all slopes are nonzero. The larger fiber
witness must be at least \(c_r-s\) from the harmonic circle
within that fiber. Thus \(\rho(\Lambda)\ge c_r-s\).

Transference gives a nonzero \(\xi\in\Lambda^*\) of length at most
\(d/(2(c_r-s))\). It lifts to an integer vector \(m\) with
\(\operatorname{proj}_V m=\xi\): the functional on \(\Gamma\)
given by \(\xi\) is integer, and \(\Gamma\) is primitive in
\(\mathbb Z^k\), so that functional extends to \(\mathbb Z^k\).
Since \(\xi\) is perpendicular to \(p\), \(m\) is a new relation
independent of \(L\). Reduce its component in \(L\) modulo the
known rows \(m_1,\ldots,m_r\). In the coefficients of that
component, independently round up or down with probabilities
giving the original coefficient as the mean. The resulting
residual has zero mean and expected squared norm at most
\(\sum_j\|m_j\|_2^2/4\), since the cross terms average to zero.
Some choice of integer rounding achieves that bound. This gives
\[
 \|m\|_2^2 \le
 \left(\frac{k-r-1}{2(c_r-s)}\right)^2
       +\frac14\sum_{j=1}^r\|m_j\|_2^2.
\]
All squared lengths are integers. Taking floors at each of the
four stages gives \(28,177,3222,11269\) for \(k=5\), and
\(44,313,7224,43544\) for \(k=6\).

For five slopes, the signed minors of the four rows give a
nonzero multiple of the primitive slope. By Hadamard's inequality
every minor is bounded by the product of the four row lengths.
The integer bound on the maximum primitive slope is therefore
\[
 \left\lfloor\sqrt{28\cdot177\cdot3222\cdot11269}\right\rfloor
   = 424200.
\]
Every profile above 424,200 clears \(1251/10000\) at dilation 1
or 2. The result leaves a finite range below that value, with
additional gcd and separated-slope families already covered.
For six slopes the four rows instead specify a finite set of
rational planes. The first five-reading relation is one of 195 primitive signed row types up to permutation and overall sign. The count uses squared length at most 28 and both signs, since all slopes are positive.

## Slicing the six-reading planes

On a rational plane torus with all six coordinate characters nonzero,
call two characters parallel if their linear forms on the plane are
proportional. Fixing one character leaves a connected circle component.
Parallel characters are constant on it and every other character has
a nonzero integral slope.

If a parallel class has size two, first choose a point at which both
class phases clear \(c\) at both \(x\) and \(2x\), with \(x\) denoting
the phases of that point. To see existence, vary along a transversal
circle. Each class phase is uniform and the combined bad sets for a
phase and its double have length \(3c\). Their union is bounded by
\(6c<1\). Freeze the class on the remaining circle and apply the
four-reading lemma. For a class of size three, clear the class and
then the remaining three by the union bound, using the first dilation
only. For a class of size four, apply the four-reading lemma to the
class along a transversal circle and clear the remaining two along
the frozen-class circle at the chosen dilation. Thus every plane with
a parallel class of size two, three or four clears at \(c\).

For a singleton class, fixing its phase reduces the other five to a
full-support harmonic circle. If the normalized absolute slope of
that circle is certified for dilations \(1,2,5\), fix the singleton
at \(1/3\), which stays clear under each of those dilations. For the
exceptional five-profile certified for \(1,2,3\), fix it at \(1/6\).
The doubled or otherwise dilated circle covers the relevant connected
component of the sliced translate, so the five certificate applies to
arbitrary shifts. For a class of size five the class itself reduces
to a five-profile along the transversal circle, and the remaining
coordinate clears on the frozen-class circle at the selected
dilation. In either case a sufficiently large five-slope cutoff
can also be used, with dilations \(1,2\) and its smaller margin.

For example, parameterize a plane by the six rows
\((1,0),(0,1),(101,2),(2,3),(3,4),(4,5)\).
There is no full-support integer direction whose absolute coordinates
are at most five. Such a direction would have integer parameters
\(u,v\), and \(u\ne0,\ |v|\le5\) imply \(|101u+2v|\ge91\).
Freezing the first coordinate gives the certified slope
\((1,2,3,4,5)\). This proves the shifted phase statement for a plane
outside the prior small-direction test.

This also bounds the plane types that still need a phase proof.
If all six characters are pairwise nonparallel, each singleton
slice gives a primitive integer direction of the plane. When any
slice has maximum above 424,200, its five-profile clears by the
high-slope theorem. Otherwise any two distinct singleton slices
give independent primitive vectors with entries bounded by 424,200,
so the plane is among the spans of finitely many such pairs. For
a size-five class and a singleton, the plane is a direct sum of
the singleton axis and its five-reading harmonic direction, which
is covered above the same bound. The parallel class cases of
sizes two through four are already settled.

An explicit transport rule uses the same Fourier comparison.
Suppose \(J,2J,\ldots,5J\) all clear the slow readings. This holds
in the six-fast sector for an interval of radius \(1/400\) about
\(3/20\). If one of the plane criteria gives margin \(\eta>0\),
take \(M=\lceil2/\eta\rceil\), \(\mu=(4\eta/(3M))^6\),
\(N\ge20k/\mu,\ D\ge20/(\ell\mu)\). Whenever every integer mode
outside the plane's relation space through \(N\) has
\(|m\cdot v|>D\), projection onto that plane gives the stated
pointwise lower bound \(\mu\) for the sum of the five tent averages.
The total integrated error is at most \(\mu/2\). A certified plane
therefore gives an actual clear time under this frequency-separation
test. If the plane relation space already contains four independent
bounded rows, failure of the separation test supplies a fifth
independent bounded row.

## One interval with four fast readings

Let \(I\) have length \(L>0\) and maximum absolute endpoint \(T\).
Assume four fast readings cover \(I\) at threshold \(1/8\). The
existing short-relation lemma gives, when \(L\min v_i\ge2400\),
a representation \(v_i=p_i\lambda+b_i\) with positive integer
\(p_i\le P_4=40^4\), \(\lambda\ge\min v_i/P_4\), and
\(|b_i|\le B=100/L\). Work on the middle half \(I'\) of \(I\), of
length \(l=L/2\).

Put \(\Delta=1/(8P_4^2)\), \(Q=16P_4^2\), and
\[
 \epsilon=\min\!\left\{\frac1{64P_4},\frac{\Delta}{40},
                 \frac{l}{100Q(l+4T/\Delta)}\right\}.
\]
For some \(t\in I'\) the circle of phases \(p_i\phi+b_it\) has
clearance greater than \(1/8+\epsilon\). Suppose it is covered
at some \(t\). Each right endpoint of a bad arc lies in another
arc continuing to its right. The overlap budget is \(8\epsilon\).
Since each arc has length greater than \(8\epsilon\), the chosen
left endpoint is within \(8\epsilon\) of the right endpoint on its
left. Return to the endpoint formulas at threshold \(1/8\). Their
circular distance at \(t\) is now at most \(10\epsilon\). Each
difference is affine in \(t\), modulo one.

At least one chosen match has a noninteger intercept at \(t=0\).
If all intercepts were integers, the directed graph of matches
would have a cycle. At zero drift the lengths around such a cycle
sum to an integer. The sum of all arc lengths at threshold \(1/8\)
is one, so the cycle uses every arc and they tile the circle at
zero drift. At zero drift all four bad sets have the origin in
their interiors, a contradiction.

A noninteger intercept has distance at least \(\Delta\) to an
integer, by its denominator \(8p_ip_j\). Set \(w=10\epsilon\).
If the endpoint difference has absolute slope at most
\(\Delta/(2T)\), its distance on \(I'\) stays at least \(\Delta/2>w\).
Otherwise the times within \(w\) of an integer have total length
at most \(2w(l+4T/\Delta)\). There are at most \(Q\) endpoint pairs.
By the choice of \(\epsilon\) their union has length at most \(l/5\).
Choose a point of \(I'\) outside this union. Its phase circle cannot
be covered, as required.

Round to a time aligning the common phase. The time change is at
most \(1/(2\lambda)\) and the drift phase error is at most
\(B/(2\lambda)\). The original cover is impossible when
\[
 \min v_i>\max\{2400/L,\ P_4(2/L),\ P_4 B/(2\epsilon)\}.
\]
For the cascade application with three slow readings bounded by \(M\),
use \(L=3/(20M)\) and \(T=15/8\) from the slow-window lemma. This
gives an explicit cutoff for the four-fast sector within the two
windows. A simpler sufficient inequality is
\(\rho_4>5\cdot10^{40}M^2\) for \(M\ge1\). In this application the
third term sets \(\epsilon\). The lifting term in the cutoff is a
positive linear combination of \(M\) and \(M^2\), with sum of
coefficients less than \(5\cdot10^{40}\).

## Exact replay and the surviving gap

The exact endpoint replay closed all 22,939 additional primitive
mixed five-profiles with maximum from 11 through 18 at \(13/100\).
All cleared using only dilations 1 and 2. In those layers, 258
profiles could still cover at dilation 1. Of these, 234 have a
four-slope gcd greater than one and the other 24 all arise by
appending the maximum slope to one of
\((1,1,1,1),(1,1,1,3),(1,1,2,2)\).
This is an observed classification in the replayed range.

Those three append-one families can also be covered for every
maximum above 18. The exact four-profile replay gives clearance
\(13/100\) for each of the four-slope cores at one of the first two
dilations. Write \(M\) for the maximum slope in a core and \(n\)
for the appended slope. The four phases stay strictly
\(s\)-clear for an interval of radius \((13/100-s)/M\).
If \(n\ge26M\), the interval is longer than a bad arc of the
remaining phase at threshold \(s\), since
\(26(13/100-s)>s\). For the smaller maxima the exact replay
certifies every appended value from 11 through \(26M-1\) at
\(13/100\).

The unclassified five-profile range now starts at 19 and ends
at 424,200. The remaining profiles can be further restricted by
the four short rows, the gcd test, and the separated-slope test.
The six-reading phase problem transfers to this five-reading
problem by slicing, and the real-rate transport has a stated
frequency-separation condition. The global cascade cutoff still
requires the residual harmonic profiles and the other tail
regimes. The first relation reduction and the replay and symbolic rules listed in the [Lean finite-reduction note](lean_kernel/FINITE_RELATIONS.md) are formalized. The four-relation forcing argument and the high-slope cutoff remain paper proofs.
See the [exact replay](explicit_fast_cutoffs_check.py) and
[recorded output](explicit_fast_cutoffs_check.out).
