# Moving the fifth reading in both directions

For the seven readings $1,2,s,v,w,x,y$, the checked theorem gives
a $1/8$-clear time in $[1/8,7/8]$ throughout the independent ranges
$$
s\in[17/7,23/7],\qquad v\in[27/7,31/7],\qquad
w\in[49/10,46/9],\qquad x,y\in[1,15].
$$
The two anchor readings are $1$ and $2$.

## First-cell rejection and replacement

The first slow cell is $[1/8,7/(8w)]$. If $p$ is an extra reading
blocking at $1/8$, then $7<p<9$ and it reopens at $9/(8p)$
inside the cell. If the other extra reading $q$ blocks both that
opening and the cell's closing, one of its two possible blocked
intervals overlaps the first blocker's interval. The comparisons are
$$
(w<q,\; 7q<9w,\; 7p<9q)
\quad\text{or}\quad
(15w<7q<17w,\; 5p<3q).
$$
The high band clears at $7/8$. In the low band, $p\ge22/3$
gives $9/16$, and $25q>31w$ with $p<22/3$ gives $7/8$.

For the remaining low band, the first replacement is the moving
opening $25/(8w)$. The comparison $5s\le3w$ puts that opening
before $s$'s closing at $15/(8s)$. On the other side of the same
comparison, $s$ has already reopened at the earlier candidate
$15/(8w)$. This earlier closing works when $15q\ge17w$.
If $15q<17w$ and $9v\le7w$, use the opening $9/(8w)$.

In the residual case $15q<17w$ and $9v>7w$, the slow core
stays clear throughout $[33/(8w),7/8]$.
At its left endpoint $L=33/(8w)$, $q$ clears and $p$
clears if $33p\le47w$. Otherwise $p$ reopens by
$\max(L,49/(8p))$. The same rejection bound on $q$ guarantees
that it is still clear there, because
$$
\frac{49\cdot17}{15}<\frac{39\cdot47}{33}
\quad\Longrightarrow\quad 49q<39p.
$$
This is the comparison of the reopening of $p$ with the closing of
$q$. It uses only the two blockers and the reading that set the first
slow closing.

## Verification

The Lean theorem is `fifth_reading_moving_close` in
`Fresh/CascadeFifthReading.lean`. The generalized first-cell
rejection lemma is `first_slow_cell_at_moving_close` in
`Fresh/CascadeTwoDeviations.lean`. The previous fixed-fifth-reading
lemma is its specialization. Run `python3 cascade_fifth_reading_audit.py`
to reproduce 144,690 exact rational checks. The replay exercises
all eleven branches and compares each chosen witness with the
cascade's first landing. For $s=3, v=4, p=71/10, q=111/20$, moving
$w$ from $5$ to $101/20$ moves the first landing from $5/8$
to $125/202$. The theorem selects a clear time, which can be
later than the cascade's first landing.

The result covers a full product of real intervals. Arbitrary input
coverage still requires forcing suitable cells when the core leaves
these ranges or the anchors move.
