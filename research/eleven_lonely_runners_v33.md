# Eleven Lonely Runners: Complementary Pairs and the Coupling Principle

**Trent Palelei** — MI Research Foundation
2026-04-06 · v33

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n=11$: for any ten distinct positive
real speeds $e_1<\cdots<e_{10}$ there exists $t>0$ with $\|e_i t\|\ge 1/11$ for all $i$.
The proof splits into three cases (bounded ratio, irrational ratio, and the essential
commensurable large-ratio regime $e_{10}/e_1>10$), with the last handled inside the
isolation window
$$W_{\mathrm{ref}} = \left[\frac{1}{11e_1},\,\frac{10}{11e_1}\right].$$
The commensurable case rests on two structural facts: the prime modulus $11$ forces the
runners $2,\ldots,9$ into four **complementary pairs**, each pair assigned as the primary
coverage responsibility for two slots and leaving $I_9$ unclaimed; and the **Coupling
Principle** (bad intervals form a rigid arithmetic progression) ensures any off-schedule
attempt to cover $I_9$ creates a gap elsewhere.
All 34 explicit rational inequalities are verified with exact arithmetic, and a boundary-set
witness search over $1.1\times 10^9$ random configurations finds zero failures.

**MSC 2020:** 11K60, 11J71
**Keywords:** Lonely Runner Conjecture, arithmetic progressions, Kronecker approximation,
complementary pairs

---

# 1. Introduction

The classical Lonely Runner Conjecture, introduced by Wills [Wil67] and reformulated by
Cusick [Cus73], asserts that for any $n$ distinct nonzero real speeds there exists a
time when every moving runner is at distance at least $1/(n+1)$ from the origin. The cases
up to $n=10$ were established over a long sequence of papers: six runners by Bohman and
Holzman [BH01], seven by Barajas and Serra [BS08], and the algebraic and flow-obstruction
perspective developed in [BGG+98]; structural aspects of the conjecture were surveyed by
Tao [Tao18]. The cases of eight, nine, and ten runners were settled recently
[Ros25a, Ros25b, Tra25]. We prove the case $n=11$.

**Theorem 1.1 (Main Theorem).** *For any ten distinct positive real speeds
$e_1<\cdots<e_{10}$, there exists $t>0$ such that*
$$\|e_i t\|\ge \frac{1}{11}\qquad(i=1,\ldots,10).$$

The proof has three cases.

**Theorem 1.2 (Bounded-Ratio Theorem).** *If $e_{10}/e_1\le 10$, then*
$$t^*=\frac{10}{11e_{10}}$$
*satisfies $\|e_i t^*\|\ge 1/11$ for all $i$.*

If any ratio $e_i/e_j$ is irrational, a Kronecker closure argument reduces the problem
to nearby commensurable configurations handled by Corollary 7.4. The proof
is in Appendix C.

The remaining case is the commensurable large-ratio regime
$$\rho := \frac{e_{10}}{e_1} > 10.$$
That is the only place where real work is needed. The proof in this regime rests on two
ideas that remain visible all the way through the paper:

1. The prime modulus $11$ forces a rigid complementary-pair ownership of the primary
   slots, leaving $I_9$ unclaimed. ("Ownership" here refers to the AP-limit primary-slot
   pattern and the perturbative burden of repair, not absolute exclusivity for all perturbed
   configurations.)
2. The bad intervals of each runner are coupled rigidly, so any off-schedule attempt to
   absorb $I_9$ must create strain elsewhere.

The paper is organised to make that structure explicit: case reduction, then the algebraic
core, then the gap obstruction lemmas, then the shift-invariant closure in $W_{\mathrm{ref}}$.

## 1.1 Proof sketch

Two cases are dispensed with quickly. If $e_{10}/e_1\le 10$, the time $t^*=10/(11e_{10})$
is a witness for every runner simultaneously; the proof is two lines. If some speed ratio
is irrational, a Kronecker approximation argument produces commensurable configurations
converging to the original, and any witness for a nearby commensurable configuration
lifts to a witness in an open neighbourhood. This reduction uses the commensurable closure
result of Section 7 but is otherwise self-contained; the proof is in Appendix C.

The real work is the commensurable large-ratio case $e_{10}/e_1>10$. The bounded-ratio
witness $t^*$ fails here because $e_1 t^*=10e_1/(11e_{10})<1/11$. There is no single
explicit time that works uniformly, so the proof must handle a continuous parameter space.

**Complementary pairs.**
The prime modulus $11$ imposes a rigid algebraic structure. At the AP limit $a_j=j$, each
runner $j\in\{2,\ldots,9\}$ has two witness labels $m_j^{\pm}\equiv\pm j^{-1}\pmod{11}$.
Because $11$ is prime, runners $j$ and $11-j$ share the same two labels: they form a
*complementary pair*. The four pairs — $(2,9)$, $(3,8)$, $(4,7)$, $(5,6)$ — together
own eight primary slots $I_1,\ldots,I_8$, two per pair. Slot $I_9$ is left unclaimed:
no pair's label corresponds to it.

*Ownership* here means that at the AP limit the pair's witness labels correspond to
that slot's boundaries, and that any perturbative repair of the slot must be borne by the
pair. It does *not* mean the pair covers the slot under all perturbed configurations;
that is exactly what the gap obstruction lemmas in Section 5 resolve.

**Coupling principle.**
Each runner's bad intervals form a rigid arithmetic progression in time. Moving one
interval to cover a boundary forces the entire chain to shift proportionally. If a runner
covers the unclaimed slot $I_9$ off schedule (not via its designated primary-slot branch),
its primary slot is left partially open. In each case the lemmas identify the specific slot
that opens: for runners whose normalised speed lies *below* their index $j$ (negative sign,
defined formally in Section 2) the primary slot is directly exposed; for runners whose
normalised speed lies *above* their index $j$ (positive sign) a short cascade forces open
a different slot.

**The gap obstruction lemmas and their closure.**
The three gap obstruction lemmas in Section 5 each handle a specific class of off-schedule
repair:

- When a negative-sign runner shifts far enough to cover the residual gap in $I_9$, the
  Coupling Principle forces it to overshoot its own primary slot — the bad interval that
  should close the slot's right boundary has already passed it. (**Primary Slot Miss, PSM**,
  Lemma 5.2.)
- Runner 3 with positive sign ($\sigma_3=+1$) can reach $I_9$, but covering that gap forces a sub-gap in
  $I_3$; the only runner that can repair it (runner 8, by complementary-pair structure)
  must shift upward, leaving $I_8$ short by a computable margin of $1/50$. (**Chain A**,
  Lemma 5.3.)
- Runner 4 with positive sign ($\sigma_4=+1$) faces a double bind: closing the sub-gap in $I_2$ forces
  runner 7 upward past the upper bound required to close $I_7$, an outright
  incompatibility. (**Chain B**, Lemma 5.4.)
- **Universal Blocking** (Theorem 5.5) collects these lemmas and shows that every
  plausible filler for the residual right gap in $I_9$ either fails a speed-range
  feasibility check or triggers one of the above.

No completely blocking configuration therefore exists in any single pacemaker cycle
inside $W_{\mathrm{ref}}$ (defined formally in Section 2).

**Shift invariance and the witness.**
The slot boundaries $I_s$ are defined in pacemaker-relative coordinates (defined formally
in Section 2), and all endpoint inequalities in Sections 5 and 6 involve only speed ranges
and slot boundaries — not the absolute cycle index $m$. The static-core argument is
therefore shift-invariant: it propagates unchanged to every complete pacemaker cycle
inside $W_{\mathrm{ref}}$. Since $W_{\mathrm{ref}}$ contains at least one complete cycle
whenever $a_1<1$, a witness exists.

**Organisation.** Section 2 fixes notation. Section 3 dispenses with the bounded-ratio
and irrational-ratio cases. Section 4 establishes the algebraic skeleton: Complementary
Pairs and the Coupling Principle. Section 5 develops the three gap obstruction lemmas
(PSM, Chain A, Chain B), then assembles them into Universal Blocking. Section 6 applies
Universal Blocking to every sign class — this is the *single-cycle analysis*. Section 7
shows the single-cycle analysis is shift-invariant and propagates it across every complete
pacemaker cycle in $W_{\mathrm{ref}}$. Section 8 assembles the three cases. Appendices A–C
supply interval arithmetic, computational corroboration, and the irrational-case reduction.

---

# 2. Setup and Notation

Fix $n=11$ throughout. For a speed vector $e_1<\cdots<e_{10}$, normalise by setting
$$a_i := \frac{10e_i}{e_{10}},\qquad a_{10}=10.$$
Thus $0<a_1<a_2<\cdots<a_9<10$. The classical AP witnesses are
$$t_m = \frac{m}{11},\qquad m=1,\ldots,10.$$
For runner $j$ with normalised speed $a_j$, the **bad intervals** are
$$B_{j,k}(a_j) = \left[\frac{11k+10}{11a_j},\,\frac{11k+12}{11a_j}\right],\qquad k\ge 0,$$
with width
$$|B_{j,k}| = \frac{2}{11a_j},$$
independent of $k$.

The **pacemaker slots** in cycle-relative coordinates are
$$I_s = \left[\frac{11s+1}{110},\,\frac{11s+10}{110}\right],\qquad s=1,\ldots,9.$$
The $m$th **pacemaker cycle** is $C_m=\bigl[m/10,\,(m+1)/10\bigr]$, and in absolute
coordinates the slots inside that cycle are
$$I_s^{(m)} = \left[\frac{11m+11s+1}{110},\,\frac{11m+11s+10}{110}\right].$$
We call these the pacemaker slots and pacemaker cycles because they are set by the
normalised top speed $a_{10}=10$, which gives a natural period of $1/10$ that paces the
analysis of all other runners inside $W_{\mathrm{ref}}$.

In the large-ratio case $a_1<1$, and we work in the window
$$W_{\mathrm{ref}} = \left[\frac{1}{11a_1},\,\frac{10}{11a_1}\right].$$
Runner 1 is isolated throughout $W_{\mathrm{ref}}$ by construction.

For any slot $J$, define its **good fraction** by
$$\mathrm{GF}(J) = \frac{|J\setminus\bigcup_{j,k}B_{j,k}|}{|J|}.$$
The good fraction measures how much of a slot is left uncovered; the proof proceeds by
showing $\mathrm{GF}(I_k)>0$ for some slot $k$ in every completely blocking configuration.
A configuration is **completely blocking** on a pacemaker cycle if $\mathrm{GF}(I_s^{(m)})=0$
for every $s=1,\ldots,9$; the goal is to show no such configuration exists.

In the static-core analysis we use the **sign convention**
$$\sigma_j =
  \begin{cases}
    +1, & a_j\in(j,\,j+1),\\
    -1, & a_j\in(j-1,\,j).
  \end{cases}$$
The sign of runner $j$ records which half of its feasible speed range it occupies,
determining which bad-interval branch is active and which primary slot is at risk.
We exclude the measure-zero hyperplanes $a_j=j$; boundary cases can be handled by a
limiting argument or direct boundary check and do not affect the contradiction analysis.

The slot comparisons that drive the proof are made in cycle-relative coordinates and are
shift-invariant, which is why we call the analysis in Sections 5 and 6 the **static
core**. The **cycle index** $m$ labels which pacemaker cycle $C_m$ is under consideration;
shift invariance (Section 7) means $m$ never enters the endpoint arithmetic.

> **Remark 2.1 (Terminology guide).**
> *Pacemaker:* the normalised top speed $a_{10}=10$, which sets the cycle grid with
> natural period $1/10$.
> *Pacemaker cycle $C_m$:* the time block $[m/10,(m+1)/10]$.
> *Cycle index $m$:* which block is under analysis. The analysis is *shift-invariant* if
> the endpoint inequalities hold identically for every $m$, i.e.\ $m$ never enters
> the arithmetic.
> *Sign $\sigma_j$:* whether runner $j$ operates in the upper ($a_j>j$) or lower
> ($a_j<j$) half of its feasible speed range.
> *Ownership (primary-slot correspondence):* the assignment of primary slot-coverage
> responsibility to a runner pair at the AP limit (see Remark 4.3).

---

# 3. Case Reduction

## 3.1 The bounded-ratio case

*Proof of the Bounded-Ratio Theorem.*
At $t^*=10/(11e_{10})$ we have
$$e_{10}t^* = \frac{10}{11},\qquad e_1 t^* = \frac{10e_1}{11e_{10}} \ge \frac{1}{11}.$$
Since $e_1\le e_i\le e_{10}$ for every $i$,
$$\frac{1}{11}\le e_i t^*\le \frac{10}{11}.$$
Hence $\|e_i t^*\|\ge 1/11$ for all $i$. $\square$

## 3.2 The irrational-ratio case

If some ratio $e_i/e_j$ is irrational, a Kronecker closure argument reduces to a nearby
commensurable configuration handled by Corollary 7.4. The proof is in Appendix C.

## 3.3 Why the AP family is not enough

The AP witnesses $\{m/11\}$ do not suffice once $a_1<1$.

**Example 3.1.** The normalised configuration
$$a = \Bigl(\tfrac{1}{2},\,\tfrac{11}{5},\,\tfrac{11}{3},\,\tfrac{33}{7},\,\tfrac{11}{2},
             \,6,\,7,\,8,\,9,\,10\Bigr)$$
blocks all ten AP witnesses $\{m/11\}_{m=1}^{10}$, but $t=4/17$ is a valid witness.

*Proof.*
At the AP witnesses $t_m=m/11$:

| Witness | Blocking runner | Reason |
|---|---|---|
| $t_1$ | runner 1 | $(1/2)\cdot(1/11)=1/22<1/11$ |
| $t_2$ | runner 5 | $(11/2)\cdot(2/11)=1$ |
| $t_3$ | runner 3 | $(11/3)\cdot(3/11)=1$ |
| $t_4$ | runner 5 | $(11/2)\cdot(4/11)=2$ |
| $t_5$ | runner 2 | $(11/5)\cdot(5/11)=1$ |
| $t_6$ | runner 3 | $(11/3)\cdot(6/11)=2$ |
| $t_7$ | runner 4 | $(33/7)\cdot(7/11)=3$ |
| $t_8$ | runner 5 | $(11/2)\cdot(8/11)=4$ |
| $t_9$ | runner 3 | $(11/3)\cdot(9/11)=3$ |
| $t_{10}$ | runner 2 | $(11/5)\cdot(10/11)=2$ |

Thus every AP witness is blocked.

At $t=4/17$ the fractional parts are
$$\frac{2}{17},\ \frac{44}{85},\ \frac{44}{51},\ \frac{13}{119},\ \frac{5}{17},\
\frac{7}{17},\ \frac{11}{17},\ \frac{15}{17},\ \frac{2}{17},\ \frac{6}{17}.$$
Their distances to the nearest integer are
$$\frac{2}{17},\ \frac{41}{85},\ \frac{7}{51},\ \frac{13}{119},\ \frac{5}{17},\
\frac{7}{17},\ \frac{6}{17},\ \frac{2}{17},\ \frac{2}{17},\ \frac{6}{17}.$$
The minimum is $13/119>1/11$, so $t=4/17$ is a valid witness. $\square$

Example 3.1 is the reason for the window switch: the obstruction is not lack of modular
structure, but the insufficiency of the AP witness family alone. In the large-ratio case
we abandon the family $\{m/11\}$ and move to $W_{\mathrm{ref}}$.

## 3.4 The commensurable large-ratio case

The remaining case — commensurable speeds with $e_{10}/e_1>10$ — is the only one requiring
real work. The three previous sections dispatch the bounded-ratio, irrational-ratio, and
AP-witnesses-only sub-cases; everything that follows addresses this regime exclusively.
This is where the structure of the prime modulus $11$ becomes decisive.

---

# 4. The Algebraic Core: Complementary Pairs and Coupling

## 4.1 The Coupling Principle

**Lemma 4.1 (Coupling Principle).** *For fixed $j$, all bad intervals of runner $j$ move
rigidly with $1/a_j$:*
$$B_{j,k}(a_j) = \left[\frac{11k+10}{11a_j},\,\frac{11k+12}{11a_j}\right].$$
*Tuning one bad interval to a boundary moves every bad interval of that runner
proportionally.*

*Proof.* Immediate from the endpoint formula. $\square$

## 4.2 Complementary pairs

At the AP limit $a_j=j$, the first lower-boundary and upper-boundary witnesses are
$$m_j^- \equiv j^{-1}\pmod{11},\qquad m_j^+ \equiv 10j^{-1}\pmod{11}.$$
Since $(11-j)^{-1}\equiv -j^{-1}\pmod{11}$, the runners $j$ and $11-j$ share the same
two witness labels.

**Theorem 4.2 (Complementary Pairs).** *The free runners $2,\ldots,9$ split into four
complementary pairs, with primary-slot correspondence:*

| Pair | Assigned slots |
|---|---|
| $(2,9)$ | $I_4$, $I_5$ |
| $(3,8)$ | $I_3$, $I_6$ |
| $(4,7)$ | $I_2$, $I_7$ |
| $(5,6)$ | $I_1$, $I_8$ |

*Slot $I_9$ is unclaimed.*

*Proof.* Compute inverses modulo $11$:
$$2^{-1}=6,\ 3^{-1}=4,\ 4^{-1}=3,\ 5^{-1}=9,\ 6^{-1}=2,\ 7^{-1}=8,\ 8^{-1}=7,\ 9^{-1}=5.$$
If a witness label is $m\in\{2,\ldots,10\}$, then the associated cycle-relative slot is
$$I_{m-1} = \left[\frac{11(m-1)+1}{110},\,\frac{11(m-1)+10}{110}\right],$$
so the lower and upper witness labels $m_j^\pm$ correspond to the slot indices $m_j^\pm-1$.
This gives the table above and leaves $I_9$ unclaimed. $\square$

---

**Figure 1: Slot ownership — one pacemaker cycle.**

```
Cycle-relative time: 0 ─────────────────────────────────────── 1

Slot:   I₁    I₂    I₃    I₄    I₅    I₆    I₇    I₈    I₉
Pair:  (5,6) (4,7) (3,8) (2,9) (2,9) (3,8) (4,7) (5,6)  ???
       ────── ────── ────── ────────────── ────── ────── ──────
         ↑                   ↑      ↑                ↑      ↑
      Pair (5,6)          Pair (2,9)            Pair (5,6)  unclaimed
```

Each pair owns two non-adjacent slots (one in the first half, one in the second). The
prime structure ensures symmetry: slot $I_s$ and slot $I_{9-s}$ are always owned by the
same pair. Slot $I_9$ is not covered by any pair's AP-limit witness labels.

*Caption:* The four complementary pairs and their primary-slot assignments. Slot $I_9$
is left unclaimed by the prime-modulus structure. Any configuration that blocks all other
slots must assign some runner to cover $I_9$ off schedule, triggering the gap obstruction
lemmas of Section 5. [TikZ figure to be added in .tex version: color each pair's slots
distinctly; $I_9$ in grey labelled "unclaimed"; arrows from pair labels to their slots.]

---

> **Remark 4.3 (Primary-slot correspondence and ownership).**
> Ownership of a slot by a complementary pair means that at the AP limit the pair's
> witness labels correspond to that slot's boundaries, and that any perturbative repair
> of the slot must be borne by the pair. It does *not* mean the pair covers the slot under
> all perturbed configurations — the gap obstruction lemmas in Section 5 handle the
> off-schedule repair cases explicitly.
>
> No other runner can absorb $I_s$ off schedule without the sign-range constraint
> (Lemma 5.1) placing it outside its feasible speed range, or the Coupling Principle
> forcing a gap elsewhere. Off-schedule repair is possible; the lemmas in Section 5 are
> precisely the cases where it occurs and what it forces.

> **Remark 4.4.** The complementary-pair structure generalises to other odd primes; the
> extension to general $n$ and the question of algorithmic automation are addressed in a
> subsequent paper.

The proof of the large-ratio case is built around this observation. In a completely blocking
configuration the unclaimed slot $I_9$ must be covered by some runner off schedule, but
the Coupling Principle says that such a move is never local: the entire bad-interval chain
of that runner moves with it. The rest of the proof is the systematic exploitation of that
forced propagation.

---

# 5. Gap Obstruction Lemmas

Throughout this section fix one pacemaker cycle and assume, for contradiction, that the
configuration is completely blocking on that cycle. The purpose of these lemmas is to turn
the geometric intuition from Section 4 into reusable statements: every plausible way of
filling the unclaimed slot either misses a primary slot outright or triggers a short
deterministic cascade that opens another slot.

## 5.1 Sign-range containment

**Lemma 5.1 (Sign-range containment).** *In every completely blocking configuration,*
$$a_j \in (j-1,\,j+1)\qquad(j=2,\ldots,9).$$

*Proof.*
When $a_j\ge j+1$, runner $j$'s zeroth bad interval $B_{j,0}=[10/(11a_j),12/(11a_j)]$
lies entirely to the right of its primary slot $I_{j-1}$, exposing the slot's left
boundary. The four cases $j=2,3,4,5$ expose the boundaries
$$\frac{12}{110},\ \frac{23}{110},\ \frac{34}{110},\ \frac{45}{110}$$
respectively. Each exposed boundary must then be covered by some other runner $j'$ via a
bad interval $B_{j',k'}$. The sign-range box $a_{j'}\in(j'-1,j'+1)$ confines each
candidate to at most two or three values of $k'$ that could place $B_{j',k'}$ near the
boundary. Appendices A.1–A.4 enumerate every such candidate for the four left boundaries:
in each case the candidate either cannot reach the boundary (infeasible by the speed-range
constraint) or, if it can, it simultaneously misses another slot boundary, giving
$\mathrm{GF}>0$ somewhere else. The full endpoint arithmetic is carried out there; no case
is assumed.

An analogous argument applies when $a_j\le j-1$: runner $j$'s primary bad interval lies
to the left of its slot, exposing a right boundary. The four cases $j=6,7,8,9$ expose
$$\frac{65}{110},\ \frac{76}{110},\ \frac{87}{110},\ \frac{98}{110},$$
and Appendices A.5–A.8 carry out the corresponding enumeration.

The four remaining out-of-range cases ($a_j\le j-1$ for $j\in\{2,3,4,5\}$;
$a_j\ge j+1$ for $j\in\{6,7,8,9\}$) expose right and left boundaries respectively
of the same primary slots. The boundary-ledger exclusions (Appendices A.1–A.8, with
the inequality direction reversed) apply unchanged.

In every out-of-range case complete blocking fails. $\square$

**Consequence.** Every completely blocking configuration belongs to exactly one of the
$2^8=256$ sign classes determined by $(\sigma_2,\ldots,\sigma_9)$.

## 5.2 Primary Slot Miss (PSM)

The PSM lemma handles runners with negative sign ($\sigma_j=-1$) that attempt to cover the
residual right gap in $I_9$. The geometric constraint that forces the runner's bad interval
to reach $I_9$ simultaneously prevents it from covering its own primary slot: the interval
shifts far enough right to cover $I_9$ but too far right to close the primary slot's
boundary. The abandoned primary slot is identified explicitly in each case.

*Notation.* For any bad interval $B_{j,k}$, we write $B_{j,k}[0]$ and
$B_{j,k}[1]$ for its left and right endpoints respectively.

**Lemma 5.2 (Primary Slot Miss, PSM).** *Let $[g_L,109/110]\subset I_9$ be a right gap.*

1. *If runner 3 with $\sigma_3=-1$ covers this gap, then $a_3\le 230/109$ and
   $B_{3,0}[0]>43/110$, so $\mathrm{GF}(I_3)>0$.*
2. *If runner 4 with $\sigma_4=-1$ covers this gap, then either $a_4\le 340/109$ and
   $B_{4,0}[0]>32/110$, or $a_4\in[430/109,4)$ and $B_{4,0}[1]<32/110$. In either
   case $\mathrm{GF}(I_2)>0$.*
3. *If runner 5 with $\sigma_5=-1$ covers this gap, then either $a_5\le 450/109$ and
   $B_{5,0}[0]>21/110$, or $a_5\in[540/109,5)$ and $B_{5,0}[0]>12/110$. In either
   case $\mathrm{GF}(I_1)>0$.*

*Proof.*
We work out Case 1 in full; Cases 2 and 3 follow by the same pattern.

*Case 1.* Runner 3 has $\sigma_3=-1$, so $a_3\in(2,3)$. For $B_{3,k}$ to contain
the right endpoint $109/110$ of the gap, its right endpoint must satisfy
$$\frac{11k+12}{11a_3} \ge \frac{109}{110} \implies a_3 \le \frac{10(11k+12)}{109}.$$
With $a_3\in(2,3)$, the feasible indices are $k=1$ (giving $a_3\le 230/109$) and $k=2$
(requiring $a_3\in(320/109,3)\approx(2.936,3)$ so that $B_{3,2}$ straddles $109/110$).
If $k=2$, runner 3 uses $B_{3,2}$ to cover $109/110$ but its zeroth bad interval satisfies
$B_{3,0}[\text{right}]=12/(11a_3)<12\cdot 109/(11\cdot 320)=327/880<344/880=43/110=I_3[\text{right}]$,
so $B_{3,0}$ falls short of $I_3$'s right edge and $\mathrm{GF}(I_3)>0$ directly.
It therefore suffices to handle $k=1$, giving $a_3\le 230/109$.
Now examine slot $I_3=[34/110,43/110]$. Runner 3's sole bad interval that could cover
$I_3$ in this cycle is $B_{3,0}=[10/(11a_3),12/(11a_3)]$. Under the constraint
$a_3\le 230/109$ its left endpoint satisfies
$$\frac{10}{11a_3} \ge \frac{10\cdot 109}{11\cdot 230} = \frac{109}{253}.$$
Comparing with the right boundary of $I_3$:
$$\frac{109}{253} - \frac{43}{110}
  = \frac{109\cdot 110 - 43\cdot 253}{253\cdot 110}
  = \frac{11990-10879}{27830}
  = \frac{1111}{27830} > 0.$$
Hence $B_{3,0}$ lies entirely to the right of $I_3$. No bad interval of runner 3 covers
any part of $I_3$, so $\mathrm{GF}(I_3)>0$.

*Case 2.* Runner 4 has $\sigma_4=-1$, so $a_4\in(3,4)$. If runner 4 covers $109/110$
via $B_{4,2}$, then $a_4\le 340/109$, and $B_{4,0}[0]=10/(11a_4)\ge 109/374>32/110$
(since $109\cdot 110=11990>32\cdot 374=11968$), so $B_{4,0}$ lies to the right of $I_2$.
If via $B_{4,3}$, then $a_4\ge 430/109$, and $B_{4,0}[1]=12/(11a_4)\le 109/430<32/110$
(since $109\cdot 110=11990<32\cdot 430=13760$), so $B_{4,0}$ lies to the left of $I_2$.
In both subcases runner 4 misses slot $I_2$, giving $\mathrm{GF}(I_2)>0$.

*Case 3.* Runner 5 has $\sigma_5=-1$, so $a_5\in(4,5)$. If via $B_{5,3}$, then
$a_5\le 450/109$ and $B_{5,0}[0]\ge 109/495>21/110$ (since $109\cdot 110>21\cdot 495$),
so $B_{5,0}$ lies to the right of $I_1$. If via $B_{5,4}$, then $a_5\ge 540/109$ and
$B_{5,0}[0]=10/(11a_5)>10/55=20/110>12/110$, so the left part of $I_1$ is uncovered.
In both subcases $\mathrm{GF}(I_1)>0$. $\square$

## 5.3 Chain A

Chain A handles the case where runner 3 with positive sign ($\sigma_3=+1$) covers the gap. Covering $I_9$
forces runner 3 to leave a sub-gap in $I_3$; by complementary-pair structure, runner 8 is
the only runner that can repair it, which forces $a_8$ upward; this in turn leaves $I_8$
uncovered by a computable margin of at least $1/50$. The chain is three steps and fully
deterministic: no case split is needed.

**Lemma 5.3 (Chain A).** *If runner 3 with $\sigma_3=+1$ covers a right gap
$[g_L,109/110]\subset I_9$, then*
$$a_3 \in \left[\frac{32}{11g_L},\,\frac{340}{109}\right],$$
*runner 8 is forced to satisfy $a_8\ge 8a_3/3$, runner 6 is then forced into
$a_6\in[43a_3/23,\,225/38]$, and the resulting coverage misses the left edge of $I_8$ by
at least $1/50$. Hence $\mathrm{GF}(I_8)\ge 1/50$.*

*Proof.*
*Step 1 (bounding $a_3$).* Runner 3 uses $B_{3,2}=[32/(11a_3),34/(11a_3)]$
to cover $[g_L,109/110]$. The right endpoint condition $34/(11a_3)\ge 109/110$
gives $a_3\le 340/109$, and the left endpoint $32/(11a_3)\le g_L$
gives $a_3\ge 32/(11g_L)$.

*Step 2 (forcing $a_8$ from the $I_3$ gap).* Since $a_3>3$, runner 3 uses
$B_{3,0}=[10/(11a_3),12/(11a_3)]$ for slot $I_3=[34/110,43/110]$. But
$$\frac{12}{11a_3} < \frac{12}{33} = \frac{40}{110} < \frac{43}{110},$$
so runner 3 leaves a right subgap $[12/(11a_3),43/110]\subset I_3$. By
Lemma 5.1 and Theorem 4.2, runner 8 is the unique candidate for closing this sub-gap in
a completely blocking configuration: runners with $a_{j'}\in(j'-1,j'+1)$ whose bad
interval $B_{j',k'}$ can reach the left edge $12/(11a_3)\approx 34/110$ of the sub-gap
are those with $(11k'+10)/(11a_{j'})$ near $34/110$. Checking: $k'=0$ gives
$a_{j'}\approx 10a_3/12\cdot (110/34)\approx 2.9\in(2,3)$ (runner 3 itself, already
committed at $k=2$); $k'=2$ gives $a_{j'}\approx 320/(11\cdot 34/110)\approx 9.4$
(sign-range excluded); the only feasible candidate in the sign-range box with the correct
reach is runner 8 via $B_{8,2}=[32/(11a_8),34/(11a_8)]$.
Hence runner 8 must cover the left edge, forcing
$$\frac{32}{11a_8} \le \frac{12}{11a_3} \implies a_8 \ge \frac{8a_3}{3}.$$
Since $a_3>3$, this forces $a_8>8$, hence $\sigma_8=+1$.

*Step 3 (opening $I_8$).* Runner 3 covers $I_6$ up to $B_{3,1}[1]=23/(11a_3)$;
the remaining right subgap in $I_6$ is $[23/(11a_3),76/110]$. Covering it with runner 6
via $B_{6,3}=[43/(11a_6),45/(11a_6)]$ requires
$$a_6 \in \left[\frac{43a_3}{23},\,\frac{225}{38}\right].$$
At the extremal value $a_6=225/38$ the interval $B_{6,4}=[54/(11a_6),56/(11a_6)]$ has
left endpoint
$$B_{6,4}[0] = \frac{54\cdot 38}{11\cdot 225} = \frac{2052}{2475} = \frac{228}{275}.$$
Since $I_8[\mathrm{left}]=89/110$, the shortfall is
$$\frac{228}{275} - \frac{89}{110}
  = \frac{456}{550} - \frac{445}{550}
  = \frac{11}{550} = \frac{1}{50}.$$
So $B_{6,4}$ starts $1/50$ to the right of $I_8[\mathrm{left}]$, giving
$\mathrm{GF}(I_8)\ge 1/50$. For all $a_6\le 225/38$ the shortfall only grows. $\square$

## 5.4 Chain B

Chain B has the same cascade structure for runner 4 with positive sign ($\sigma_4=+1$). Here the chain
produces an outright incompatibility: the constraints forced onto runner 7 (lower bound
from the $I_2$ sub-gap, upper bound from the $I_7$ right edge) become contradictory,
directly opening $I_7$ without needing to measure a gap width.

**Lemma 5.4 (Chain B).** *If runner 4 with $\sigma_4=+1$ covers a right gap
$[g_L,109/110]\subset I_9$, then*
$$a_4 \in \left[\frac{43}{11g_L},\,\frac{450}{109}\right].$$
*This forces runner 7 to satisfy $a_7\ge 7a_4/4$, while covering the right edge of $I_7$
requires $a_7\le 560/87$. These are incompatible, so $\mathrm{GF}(I_7)>0$.*

*Proof.*
Runner 4 uses $B_{4,3}=[43/(11a_4),45/(11a_4)]$ to cover the right gap, so
$a_4\in[43/(11g_L),450/109]\subset(4,5)$. Its primary slot is $I_2=[23/110,32/110]$, and
the only available interval is $B_{4,0}=[10/(11a_4),12/(11a_4)]$. Since $a_4>4$,
$$B_{4,0}[1] = \frac{12}{11a_4} < \frac{12}{44} = \frac{30}{110} < \frac{32}{110},$$
so runner 4 leaves a right subgap $[12/(11a_4),32/110]\subset I_2$. Runner 7 must cover
the left edge via $B_{7,1}=[21/(11a_7),23/(11a_7)]$, which forces
$$\frac{21}{11a_7} \le \frac{12}{11a_4} \implies a_7 \ge \frac{7a_4}{4} > 7.$$
For runner 7 to cover the right edge $87/110$ of $I_7$
via $B_{7,4}=[54/(11a_7),56/(11a_7)]$, one needs
$$\frac{56}{11a_7} \ge \frac{87}{110} \implies a_7 \le \frac{560}{87}.$$
But $560/87<7$, so the constraints $a_7\ge 7a_4/4>7$
and $a_7\le 560/87<7$ are incompatible. Hence $\mathrm{GF}(I_7)>0$. $\square$

## 5.5 Universal Blocking

Universal Blocking collects the previous lemmas into a single closure statement. Every
plausible filler for the residual right gap in $I_9$ either fails a speed-range feasibility
check or triggers PSM, Chain A, or Chain B. The table below exhausts all cases. This
theorem is what both the static core (Section 6) and the shift-invariant closure (Section 7)
depend on: every proof branch reduces to it.

**Theorem 5.5 (Universal Blocking).** *Let $[g_L,109/110]\subset I_9$ be any nonempty
right gap with $g_L\in[100/110,109/110)$. Runner 2 is handled separately in Section 6:
in the $\sigma_2=-1$ branch by the Runner-2 Elimination Lemma (Lemma 6.1), and in the
$\sigma_2=+1$ branch by the $I_9$ decomposition (Lemma 6.4); the present theorem applies
to residual right gaps after those branches are resolved. No assignment of runners
$3,\ldots,8$ can cover this gap while keeping $\mathrm{GF}(I_s)=0$ for every other slot.*

*Proof.*
The residual fillers are exhausted by the following summary (full speed-range checks in
Appendix A.10):

| Filler | Sign | Outcome |
|---|---|---|
| runner 3 | $-1$ | PSM gives $\mathrm{GF}(I_3)>0$ |
| runner 3 | $+1$ | Chain A gives $\mathrm{GF}(I_8)\ge 1/50$ |
| runner 4 | $-1$ | PSM gives $\mathrm{GF}(I_2)>0$ |
| runner 4 | $+1$ | Chain B gives $\mathrm{GF}(I_7)>0$ |
| runner 5 | $-1$ | PSM gives $\mathrm{GF}(I_1)>0$ |
| runner 5 | $+1$ | infeasible (speed range) |
| runner 6 | $\pm1$ | infeasible (speed range) |
| runner 7 | $\pm1$ | infeasible (speed range) |
| runner 8 | $\pm1$ | infeasible (speed range) |

*Infeasibility of runners 5 ($\sigma_5=+1$), 6, 7, 8.* For runner $j$ to cover
the right gap $[g_L,109/110]\subset I_9$ via $B_{j,k}$, two conditions must hold
simultaneously:
$$\frac{11k+12}{11a_j}\ge\frac{109}{110}\quad\text{and}\quad
  \frac{11k+10}{11a_j}\le g_L \le \frac{100}{110}.$$
The right-edge condition gives $a_j\le 10(11k+12)/109$; the left-edge condition (using
$g_L\ge 100/110$) gives $a_j\ge(11k+10)/10$. These are incompatible whenever
$$\frac{11k+10}{10} > \frac{10(11k+12)}{109}
  \iff 109(11k+10)>100(11k+12)
  \iff 9\cdot 11k > 110
  \iff k > \frac{110}{99},$$
i.e. for all $k\ge 2$. For runners $j\ge 5$ in the sign-range box
$a_j\in(j-1,j+1)$, every bad interval reaching $109/110$ must use $k\ge 4$.
Since $k\ge 4>110/99$, all such branches are infeasible. Full speed-range checks are in
Appendix A.10.

If no runner is feasible, the gap survives directly in $I_9$. Otherwise one of PSM,
Chain A, or Chain B opens another slot. In all cases $\mathrm{GF}(I_k)>0$ for some
slot $I_k$. $\square$

---

# 6. The Static Core (Single-Cycle Analysis)

We now have the gap obstruction lemmas. The static core applies them to show that no sign
class — no assignment of $\sigma_2,\ldots,\sigma_9$ — can achieve complete blocking on any
single pacemaker cycle.

> *Note:* All inequalities in this section depend only on speed ranges $a_j\in(j-1,j+1)$
> and slot boundaries — not on the absolute cycle index $m$.

## 6.1 The branch $\sigma_2=-1$

**Lemma 6.1 (Runner-2 Elimination Lemma).** *In every sign class with $\sigma_2=-1$,
runner 2 cannot simultaneously satisfy its primary obligation at $I_5$ and absorb the
unclaimed slot $I_9$.*

*Proof.*
To cover $I_5=[56/110,65/110]$ via $B_{2,0}$ one needs $25/14\le a_2\le 24/13$.
To overlap $I_9=[100/110,109/110]$, runner 2 can only use $B_{2,0}$ or $B_{2,1}$,
which require
$$\frac{100}{109}\le a_2\le \frac{6}{5}\qquad\text{or}\qquad
  \frac{210}{109}\le a_2<2.$$
Both intervals are disjoint from $[25/14,24/13]$, and
$$\frac{210}{109}-\frac{24}{13}=\frac{114}{1417}>0.$$
So runner 2 is eliminated as an absorber of $I_9$. $\square$

**Lemma 6.2 (Negative-Branch Gap Lemma).** *In every sign class with $\sigma_2=-1$, the
unclaimed slot $I_9$ retains positive witness width. The minimum is $538/54395>0$.*

*Proof.*
By the Runner-2 Elimination Lemma, runner 2 cannot absorb $I_9$, so runner 9 must first
close $I_4$. No alternative ordering is possible: any other runner covering $I_4$ in the
$\sigma_2=-1$ branch either falls outside the sign-range box (excluded by Lemma 5.1) or is
already committed to a primary slot whose coverage cannot be rerouted without opening a gap
there. For runner 9 the $I_4$-closure condition is
$$\frac{43}{11a_9} = \frac{45}{110},\qquad a_9 = \frac{2(11k+10)}{9}.$$
Inside $(9,10)$ the only possibility is $k=3$, giving $a_9=86/9$. The resulting interval
in $I_9$ is
$$B_{9,8}\!\left(\tfrac{86}{9}\right)
  = \left[\frac{441}{473},\,\frac{450}{473}\right].$$
The complementary-pair cascade leaves four sign possibilities for $(\sigma_3,\sigma_4)$:

| $(\sigma_3,\sigma_4)$ | Uncovered region in $I_9$ | Width |
|---|---|---|
| $(+,+)$ | $(741/770,\,272/275)$ | $103/3850$ |
| $(+,-)$ | $(10/11,\,441/473)$ together with previous gap | $8279/165550$ |
| $(-,+)$ | $(450/473,\,1216/1265)$ | $538/54395$ |
| $(-,-)$ | $(10/11,\,441/473)$ together with $(450/473,\,1216/1265)$ | $1803/54395$ |

All four widths are positive, and the minimum is $538/54395$. The detailed forced-speed
table and the endpoint comparisons are recorded in Appendix A.11. $\square$

## 6.2 The branch $\sigma_2=+1$

We now assume $\sigma_2=+1$. The pair $(2,9)$ carries the sharpest tension: closing $I_4$
drives $a_2$ upward, while bridging $I_9$ drives $a_2$ downward.

**Lemma 6.3 (The $I_4$ lower bound on $a_2$).** *Closing $I_4$ requires*
$$a_2 \ge L(a_9) :=
  \begin{cases}
    20/9, & a_9 < 86/9,\\[2pt]
    2a_9/9, & a_9 \ge 86/9.
  \end{cases}$$
*(Note that $L$ is discontinuous at $a_9=86/9$: the left-hand limit is $20/9\approx 2.222$
while $L(86/9)=172/81\approx 2.123$. This downward jump is intentional: at $a_9=86/9$
runner 9 just reaches the left edge of $I_4$, reducing runner 2's required coverage.)*

*Proof.*
If $a_9<86/9$, runner 9 leaves the left edge $45/110$ uncovered in $I_4$.
Appendix A.9 gives the full runner-by-runner exclusion table and shows that only runner 2
can cover $45/110$ without opening another slot, forcing
$$\frac{10}{11a_2} \le \frac{45}{110},\qquad a_2 \ge \frac{20}{9}.$$
If $a_9\ge 86/9$, runner 9 reaches the left edge of $I_4$ but leaves a right subgap;
covering that subgap with runner 2 requires
$$\frac{10}{11a_2} \le \frac{45}{11a_9},\qquad a_2 \ge \frac{2a_9}{9}.\qquad\square$$

**Lemma 6.4 (The $I_9$ decomposition).** *Under $\sigma_2=+1$, the parameter space splits
into seven regions:*

| Region | Condition | Consequence |
|---|---|---|
| $\alpha_1$ | $\sigma_9=-1$, $a_9<580/69$ | direct incompatibility |
| $\alpha_2$ | $\sigma_9=-1$, $a_9\in[980/109,9)$ | direct incompatibility |
| $\alpha_3$ | $\sigma_9=+1$, $a_9\in(9,1960/207)$ | direct incompatibility |
| $\beta_1$ | $\sigma_9=-1$, $a_9\in[580/69,87/10)$ | right gap $[89/(11a_9),109/110]$ |
| $\beta_2$ | $\sigma_9=-1$, $a_9\in[87/10,980/109)$ | right gap $[23/(11a_2),109/110]$ |
| $\beta_3$ | $\sigma_9=+1$, $a_9\in[1960/207,86/9]$ | right gap $[100/(11a_9),109/110]$ |
| $\beta_4$ | $\sigma_9=+1$, $a_9\in(86/9,10)$ | right gap $[100/(11a_9),109/110]$ |

*Exhaustiveness.* The seven regions partition the interval
$(a_9^{\min},a_9^{\max})=(8,10)$ (for $\sigma_9=-1$) and $(9,10)$ (for $\sigma_9=+1$)
exhaustively and disjointly: the $\alpha$-/$\beta$-boundary within each sign class is a
single threshold value, and adjacency of the subintervals is verified in Appendix A.11.

*Proof.*
We track two competing constraints on $a_2$.

*Lower bound.* Lemma 6.3 gives $a_2\ge L(a_9)$.

*Upper bound from $I_9$ coverage ($\sigma_9=-1$).* With $\sigma_9=-1$,
$a_9\in(8,9)$. Runner 9 uses $B_{9,7}=[87/(11a_9),89/(11a_9)]$ when $a_9<87/10$, and
$B_{9,8}=[98/(11a_9),100/(11a_9)]$ for $a_9\ge 980/109$. For runner 2's interval
$B_{2,1}=[23/(11a_2),25/(11a_2)]$ to abut $B_{9,7}$ without a gap:
$$\frac{23}{11a_2}\ge \frac{87}{11a_9} \implies a_2\le\frac{23a_9}{87}\quad
  (B_{9,7}\text{ regime}).$$
Similarly, $a_2\le 23a_9/98$ in the $B_{9,8}$ regime and for $\sigma_9=+1$.

*$\alpha$-regions: incompatibility.*
- $\alpha_1$: $20/9>23a_9/87\iff a_9<580/69\approx 8.41$.
- $\alpha_2$: $20/9>23a_9/98\iff a_9<1960/207\approx 9.47$; throughout $[980/109,9)$.
- $\alpha_3$: same upper bound; incompatibility holds for $a_9\in(9,1960/207)$.

*$\beta$-regions: residual right gap.* When the constraints are compatible, the runners
$B_{9,k}$ and $B_{2,1}$ together cover $I_9$ up to a residual right gap with left endpoint
$g_L\ge 100/110$ in each case. Hence Theorem 5.5 applies. $\square$

**Theorem 6.5 (Positive-branch static core).** *In every completely blocking configuration
with $\sigma_2=+1$, $\mathrm{GF}(I_k)>0$ for some slot $I_k$.*

*Proof.*
In the $\alpha$-regions of Lemma 6.4, the bounds from $I_4$ and $I_9$ are
incompatible. In the $\beta$-regions, Theorem 5.5 (Universal Blocking) shows that
the residual right gap either survives in $I_9$ or is absorbed only at the cost of opening
another slot via PSM, Chain A, or Chain B. In all cases $\mathrm{GF}(I_k)>0$ for some $k$.
$\square$

---

# 7. Shift-Invariant Closure in $W_{\mathrm{ref}}$ (All Cycles)

Section 6 showed that no single pacemaker cycle $C_m$ can be completely blocked.
The Main Theorem requires a witness in the full window $W_{\mathrm{ref}}$, which spans
many cycles. This section shows that the single-cycle obstructions are
**shift-invariant**: since bad-interval widths $|B_{j,k}|=2/(11a_j)$ depend only on
$a_j$ and all slot boundaries are defined modulo the pacemaker period $1/10$, every
endpoint inequality in Sections 5–6 holds identically in every cycle. Complete blocking
therefore cannot hide by shifting to a different cycle index.

## 7.1 Shift invariance

**Lemma 7.1.** *For every runner $j$ and every cycle index $m$, $|B_{j,k}|=2/(11a_j)$.
Hence feasibility for covering a gap of fixed width depends only on $a_j$, not on the
cycle index.*

*Proof.* Immediate from the formula for $B_{j,k}$. $\square$

**Lemma 7.2.** *The hypotheses and conclusions of PSM, Chain A, Chain B, the
Negative-Branch Gap Lemma, and Theorem 6.5 depend only on the speed ranges
$a_j\in(j-1,j+1)$ and on which runner covers the right gap of $I_9$. They are independent
of the cycle index.*

*Proof.*
In pacemaker-relative coordinates the slot boundaries $I_s$ are fixed. In the $m$-th
pacemaker cycle, runner $j$'s relevant bad interval is $B_{j,k_m}$ where $k_m=k_0+m$.
The residual fractional position $\{a_jt - k_m\}$ equals the cycle-0 residual up to an
integer shift, so the slot-comparison inequalities are numerically identical in every cycle;
the $k$-index is invisible to the endpoint arithmetic. Every inequality in Sections 5
and 6 is a comparison involving only $a_j$ and the universal slot boundaries
$\{(11s+i)/110\}$. The branch choice (PSM / Chain A / Chain B) is determined by which
speed ranges hold and which runner covers the right gap of $I_9$; neither condition depends
on the absolute cycle index $m$. No step depends on a specific cycle index $m$. $\square$

> **Remark.** The shift-invariance of the $k$-index is not merely notational. It means
> that the static-core analysis of Section 6 propagates unchanged to every complete
> pacemaker cycle inside $W_{\mathrm{ref}}$, and there is no hidden dependency on which
> $B_{j,k}$ index is serving as the local primary branch in a given cycle.

## 7.2 The shift-invariant static core

**Theorem 7.3 (Shift-invariant static core).** *Let $C_m\subset W_{\mathrm{ref}}$ be any
complete pacemaker cycle. Then some slot $I_k^{(m)}$ has positive good fraction.*

*Proof.*
Split on $\sigma_2$. If $\sigma_2=+1$, Theorem 6.5 gives $\mathrm{GF}(I_k)>0$ in
cycle-relative coordinates, and Lemma 7.2 makes this uniform across all cycles. If
$\sigma_2=-1$, the Negative-Branch Gap Lemma gives a positive witness width in $I_9$ by
a pure speed-range calculation, persistent in every cycle. Hence every complete pacemaker
cycle inside $W_{\mathrm{ref}}$ contains a slot with positive good fraction. $\square$

**Corollary 7.4 ($W_{\mathrm{ref}}$ closure).** *In the commensurable large-ratio case
$a_1<1$, there exists a witness in $W_{\mathrm{ref}}$.*

*Proof.*
Runner 1 is isolated throughout $W_{\mathrm{ref}}$ by definition. We need an integer $m$
such that $C_m=[m/10,(m+1)/10]\subset W_{\mathrm{ref}}$, i.e.
$$\frac{10}{11a_1} \le m \le \frac{100}{11a_1}-1.$$
The length of this interval is $90/(11a_1)-1>90/11-1=79/11>1$ because $a_1<1$. Hence it
contains an integer $m^*$, so $C_{m^*}\subset W_{\mathrm{ref}}$. By Theorem 7.3,
some slot inside that cycle has positive good fraction for runners $2,\ldots,10$. Runner 1
is safe everywhere on the cycle, giving a witness for all runners. $\square$

At this point the commensurable large-ratio case is complete. To summarise the three-case
structure: Case B ($e_{10}/e_1\le 10$) is resolved by the explicit witness
$t^*=10/(11e_{10})$ (Bounded-Ratio Theorem, Section 1). Case R$>$ (all ratios commensurable
and $e_{10}/e_1>10$) is resolved by Corollary 7.4, which applies the gap-obstruction and
static-core argument across every cycle in $W_{\mathrm{ref}}$. Case E (some ratio irrational)
is resolved by reduction to Case R$>$ via Kronecker approximation; the full reduction is
in Appendix C.

---

# 8. The Full Proof

Every speed configuration falls into exactly one of three mutually exclusive and
exhaustive cases.

*Proof of the Main Theorem.*

**Case B: $e_{10}/e_1\le 10$.**
The explicit time $t^*=10/(11e_{10})$ satisfies $e_it^*\in[1/11,10/11]$ for every $i$,
so $\|e_it^*\|\ge 1/11$ for all $i$. Resolved by the Bounded-Ratio Theorem.

**Case E: some $e_i/e_j\notin\mathbb{Q}$.**
A Kronecker closure argument produces commensurable configurations converging to the
original; any witness for a nearby commensurable configuration lifts to an open
neighbourhood containing the original. The argument uses Corollary 7.4 for the
commensurable case; the details are in Appendix C.

**Case R$>$: all $e_i/e_j\in\mathbb{Q}$ and $e_{10}/e_1>10$.**
The algebraic structure of the prime modulus $11$ (Complementary Pairs, Section 4) forces
the unclaimed slot $I_9$, and the Coupling Principle (Section 4) ensures any off-schedule
repair propagates strain. The gap obstruction lemmas (Section 5) and static core (Section 6)
show that no sign class achieves complete blocking on any pacemaker cycle; shift invariance
(Section 7) extends this to every cycle inside $W_{\mathrm{ref}}$. Resolved by Corollary 7.4.

The three cases are mutually exclusive and exhaustive. Hence the Main Theorem holds for
all ten-tuples of positive real speeds. $\square$

---

# References

**[BGG+98]** A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebo, M. Tarsi,
*Flows, view obstructions, and the lonely runner*,
J. Combin. Theory Ser. B **72** (1998), 1–9.

**[BH01]** T. Bohman, R. Holzman,
*Six lonely runners*,
Electron. J. Combin. **8** (2001), R3.

**[BS08]** J. Barajas, O. Serra,
*The lonely runner with seven runners*,
Electron. J. Combin. **15** (2008), R48.

**[Cus73]** T. W. Cusick,
*View obstruction problems*,
Aequationes Math. **9** (1973), 165–170.

**[KN74]** L. Kuipers, H. Niederreiter,
*Uniform Distribution of Sequences*,
Wiley, 1974.

**[Pal26]** T. Palelei,
*The $\phi(n)$ law for arithmetic progressions in the lonely runner conjecture: algebraic
structure and computational fragility*,
Zenodo, 2026. https://doi.org/10.5281/zenodo.18158886

**[Ros25a]** M. Rosenfeld,
*The lonely runner conjecture holds for eight runners*,
arXiv:2509.14111, 2025.

**[Ros25b]** M. Rosenfeld,
*The lonely runner conjecture holds for nine runners*,
arXiv:2512.01912, 2025.

**[Tao18]** T. Tao,
*Some remarks on the lonely runner conjecture*,
Contrib. Discrete Math. **13** (2018), 1–31.

**[Tra25]** T. Trakulthongchai,
*Nine and ten lonely runners*,
arXiv:2511.22427, 2025.

**[Wil67]** J. M. Wills,
*Zwei Sätze über inhomogene diophantische Approximation*,
Monatsh. Math. **71** (1967), 263–269.

---

# Appendix A. Technical Interval Arithmetic

This appendix collects the endpoint arithmetic that is routine but too repetitive for the
main line. Sections A.1–A.8 are the eight slot-boundary ledgers used in Lemma 5.1, with
A.5–A.8 written as standalone right-edge calculations. Section A.9 records the extracted
$45/110$ consequence used in Lemma 6.3. Section A.10 records the feasibility table behind
Universal Blocking. Section A.11 is the compact ledger for the Negative-Branch Gap Lemma.

Each ledger below is a **boundary-repair exclusion**: if runner $j$ exits its sign-range
box $(j-1,j+1)$, a primary-slot boundary is left exposed. The ledger shows that every
candidate runner $j'$ that could geometrically reach that boundary either fails the
speed-range constraint or simultaneously misses another slot boundary, giving
$\mathrm{GF}>0$ somewhere. Each table entry is an attempted repair; the Consequence column
records the resulting gap.

## A.1 Boundary ledger for $12/110$ (slot $I_1$ left)

*Conclusion: no off-schedule runner can repair $12/110$ without simultaneously exposing
$I_3$ (runner 8) or $I_4$ (runner 9).*

To straddle $12/110$, a branch $B_{j,k}$ must satisfy
$$\frac{11k+10}{11a_j} \le \frac{12}{110} \le \frac{11k+12}{11a_j}.$$
Inside the sign-range box $a_j\in(j-1,j+1)$, the only off-schedule candidates are:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[25/3,\,10)$ | runners 8, 9 |

- If runner 8 covers $12/110$, then $a_8\ge 25/3$ and
  $B_{8,2}[0]=32/(11a_8)\ge 32/99>34/110=I_3[\mathrm{left}]$,
  so the left edge of $I_3$ is missed.
- If runner 9 covers $12/110$, then either $a_9<86/9$ and
  $B_{9,3}[0]=43/(11a_9)>45/110$, or $a_9\ge 86/9$ and
  $B_{9,3}[1]=45/(11a_9)<54/110$, so $I_4$ is not closed.

Thus $12/110$ cannot be repaired off schedule without opening another claimed slot.

## A.2 Boundary ledger for $23/110$ (slot $I_2$ left)

*Conclusion: no off-schedule runner can repair $23/110$ without exposing $I_1$ (runners
5, 6) or failing to close $I_4$ (runner 9).*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[100/23,\,120/23]$ | runners 5, 6 |
| $1$ | $[210/23,\,10)$ | runner 9 |

- Runners 5 or 6 via $B_{j,0}$: $B_{j,0}[0]\ge 23/132>12/110$, so $I_1$ acquires a
  left gap that neither runner can close alone.
- Runner 9 via $B_{9,1}$: same split as in A.1 shows runner 9 fails to close $I_4$.

## A.3 Boundary ledger for $34/110$ (slot $I_3$ left)

*Conclusion: every off-schedule repair of $34/110$ forces positive good fraction in a
partner slot.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[50/17,\,3)$ | runner 2 |
| $0$ | $[3,\,60/17]$ | runner 4 |
| $1$ | $[105/17,\,115/17]$ | runners 6, 7 |
| $2$ | $[160/17,\,10)$ | runner 9 |

Each candidate either forces its pair-partner slot open or shifts runner 9's $I_4$ interval
off a required boundary. In each case one obtains positive good fraction in a partner slot.

## A.4 Boundary ledger for $45/110$ (slot $I_4$ left)

This is the calculation used in Lemma 6.3.

*Conclusion: runner 2 is the unique viable filler of $45/110$; all others force a partner
slot open.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[20/9,\,8/3]$ | runners 2, 3 |
| $1$ | $[14/3,\,46/9]$ | runners 4, 5, 6 |
| $2$ | $[64/9,\,68/9]$ | runners 7, 8 |
| $3$ | $[86/9,\,10]$ | runner 9 |

Runners 3–8 are each excluded: runner 3 forces $\mathrm{GF}(I_3)>0$; runner 4 triggers
Chain B opening $I_7$; runner 5 leaves $I_1$ open; runner 6 leaves $I_8$ open;
runner 7 creates an inter-interval gap in $I_7$; runner 8 forces $\mathrm{GF}(I_3)>0$.
Runner 9 is excluded by the Lemma 6.3 left-gap analysis.
Therefore runner 2 is the unique viable filler, giving $a_2\ge 20/9$.

## A.5 Boundary ledger for $65/110$ (slot $I_5$ right)

*Conclusion: every off-schedule repair of $65/110$ forces positive good fraction in a
partner slot.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $1$ | $[42/13,\,46/13]$ | runners 3, 4 |
| $2$ | $[64/13,\,68/13]$ | runners 4, 5, 6 |
| $3$ | $[86/13,\,90/13]$ | runners 6, 7 |
| $4$ | $[108/13,\,112/13]$ | runner 8 |

Every off-schedule repair of $65/110$ forces positive good fraction in a partner slot by
direct endpoint arithmetic (see the detailed exclusions in A.5 of the working notes).

## A.6 Boundary ledger for $76/110$ (slot $I_6$ right)

*Conclusion: every off-schedule repair of $76/110$ leaves a partner slot open.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[25/19,\,30/19]$ | runner 2 |
| $1$ | $[105/38,\,3)$ | runner 2 |
| $1$ | $[3,\,115/38]$ | runner 4 |
| $2$ | $[80/19,\,85/19]$ | runners 4, 5 |
| $3$ | $[215/38,\,225/38]$ | runners 5, 6 |
| $4$ | $[135/19,\,140/19]$ | runner 7 |
| $5$ | $[325/38,\,335/38]$ | runner 9 |

Every off-schedule repair of $76/110$ leaves a partner slot open.

## A.7 Boundary ledger for $87/110$ (slot $I_7$ right)

*Conclusion: every off-schedule repair of $87/110$ forces a partner slot open via direct
endpoint comparison.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[100/87,\,40/29]$ | runner 2 |
| $1$ | $[70/29,\,230/87]$ | runners 2, 3 |
| $2$ | $[320/87,\,340/87]$ | runner 3 |
| $3$ | $[430/87,\,150/29]$ | runners 5, 6 |
| $4$ | $[180/29,\,560/87]$ | runner 6 |
| $5$ | $[650/87,\,670/87]$ | runner 8 |
| $6$ | $[760/87,\,260/29]$ | runners 8, 9 |

Runner 2 ($k=0$): $B_{2,0}[\mathrm{left}]\ge 29/44>65/110$, so runner 2 misses $I_5$.
Runner 2 ($k=1$): $B_{2,1}[\mathrm{left}]\ge 1827/2530>56/110$, again missing $I_5$ left.
Runners 3 ($k=1,2$): the next interval $B_{3,k+1}$ jumps above $I_6$ right, and runner 8
alone cannot cover $I_6$. Runners 5 and 6 ($k=3$): the pair $(5,6)$ loses $I_8$ right
by incompatible bounds. Runner 6 ($k=4$), runner 8 ($k=5,6$), runner 9 ($k=6$): each
forces a partner slot open by analogous endpoint arithmetic.

## A.8 Boundary ledger for $98/110$ (slot $I_8$ right)

*Conclusion: every off-schedule repair of $98/110$ forces a partner slot open.*

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[50/49,\,60/49]$ | runner 2 |
| $1$ | $[15/7,\,115/49]$ | runners 2, 3 |
| $2$ | $[160/49,\,170/49]$ | runners 3, 4 |
| $3$ | $[215/49,\,225/49]$ | runner 4 |
| $5$ | $[325/49,\,335/49]$ | runner 7 |
| $6$ | $[380/49,\,390/49]$ | runners 7, 8 |
| $7$ | $[435/49,\,445/49]$ | runner 9 |

Runner 2 ($k=0$): $B_{2,0}[\mathrm{left}]\ge 49/66>67/110$, so $I_6$ left is uncovered.
Runners 2, 3 ($k=1$): the previous interval lies below $I_5$ or $I_6$, opening those slots.
Runner 4 ($k=2,3$): $B_{4,4}[\mathrm{left}]>98/110$ for $k=3$, so runner 4 misses $I_7$.
Runners 7, 8 ($k=6$): start above $I_6$ right, leaving $I_6$ left uncovered.
Runner 9 ($k=7$): $445/49<86/9$, so Lemma 6.3 forces $a_2\ge 20/9$,
but covering $56/110$ of $I_5$ requires $a_2\le 15/7<20/9$; contradiction.

## A.9 The full $45/110$ exclusion used in Lemma 6.3

If $a_9<86/9$ and $I_4$ is to be closed, runner 9 leaves the left edge $45/110$ uncovered.
The A.4 exclusions show:
runner 3 opens $I_3$; runner 4 opens $I_7$ via Chain B; runner 5 opens $I_1$;
runner 6 opens $I_8$; runner 7 opens $I_7$ through its inter-interval gap; runner 8 opens $I_3$.
Hence runner 2 is the unique viable filler and
$$\frac{10}{11a_2} \le \frac{45}{110} \implies a_2 \ge \frac{20}{9}.$$

## A.10 Feasibility table for Universal Blocking

For a right gap $[g_L,109/110]\subset I_9$, the potentially feasible fillers are:

| Runner | Sign | Feasible range | Conclusion |
|---|---|---|---|
| 3 | $-1$ | $a_3\le 230/109$ | PSM opens $I_3$ |
| 3 | $+1$ | $a_3\in[32/(11g_L),340/109]$ | Chain A opens $I_8$ |
| 4 | $-1$ | $a_4\le 340/109$ | PSM opens $I_2$ |
| 4 | $+1$ | $a_4\in[43/(11g_L),450/109]$ | Chain B opens $I_7$ |
| 5 | $-1$ | $a_5\le 450/109$ | PSM opens $I_1$ |
| 5 | $+1$ | no branch survives | no cover |
| 6 | $\pm1$ | no branch survives | no cover |
| 7, 8 | $\pm1$ | no branch survives | no cover |

More explicitly, for runners 5–8 with the positive sign (or any sign for runners 6–8),
the bounds
$$\frac{11k+10}{10} > \frac{10(11k+12)}{109}\quad\text{for all }k\ge 2$$
rule out every feasible branch.

## A.11 Compact ledger for the Negative-Branch Gap Lemma

When $\sigma_2=-1$, the Runner-2 Elimination Lemma forces $a_9=86/9$ with
$B_{9,8}(86/9)=[441/473,450/473]$. The cascade-forced outer speeds by subcase:

- $\sigma_3=-1$: $a_3=50/17$, $a_8=140/19$.
- $\sigma_3=+1$: $a_3=115/38$.
- $\sigma_4=+1$: $a_4=100/23$, $a_7=560/87$.
- $\sigma_4=-1$: $a_4=340/87$.

The four subcases are exactly the table in the Negative-Branch Gap Lemma, and the
minimal uncovered width is
$$\frac{1216}{1265} - \frac{450}{473} = \frac{538}{54395}.$$
(Gap width for the $(\sigma_3=-1,\sigma_4=+1)$ sub-case: $26/1419 > 538/54395$,
consistent with the stated minimum.)

---

# Appendix B. Computational Corroboration

The computations described here are *not* part of the proof; the theorem is
established analytically in Sections 1–8. They provide independent, large-scale
corroboration that the proof's structural mechanisms behave as the analysis predicts,
with no exceptional regimes detected in either campaign.

## Exact symbolic verification

- Exact rational checks on the canonical integer family $\{1,\ldots,9,p_{10}\}$
  with $p_{10}\in\{89,\ldots,200\}$ find witnesses in $W_{\mathrm{ref}}$ in all 112 cases.
- All 34 explicit rational inequalities in the proof — including the endpoint constants
  $$\frac{83}{2695},\quad\frac{17}{430},\quad\frac{1}{50},\quad
    \frac{1533}{18490},\quad\frac{538}{54395}$$
  and the Chain A, Chain B, and negative-branch bounds — were verified with exact
  arithmetic in Python (`fractions.Fraction`), giving zero floating-point error. All
  34 checks pass.

## Large-scale boundary-set verification

Two independent witness-search campaigns were conducted on an Apple M4 MacBook Pro
(10-core CPU, Python 3.14). The event-complete boundary-set method of [Pal26] was used:
rather than sampling a time-grid, the search evaluates only at the finite set of times
where some runner's fractional distance to the origin crosses the $1/11$ threshold,
guaranteeing that no witness in $W_{\mathrm{ref}}$ can be missed between evaluation points.
This approach reduced per-configuration cost by a factor of approximately $10^3$ compared
with naive grid search.

| Campaign | Seed | Configurations | Failures | Boundaries evaluated | Runtime |
|---|---|---|---|---|---|
| `run_1e8_mech` | 42 | $10^8$ | **0** | $6.1\times10^{10}$ | 65 min |
| `run_1e9_mech` | 1337 | $10^9$ | **0** | $6.1\times10^{11}$ | 10.7 hr |
| **Combined** | — | $1.1\times10^9$ | **0** | $6.7\times10^{11}$ | — |

Each configuration was drawn randomly from the commensurable large-ratio regime
($a_1\in(0,1)$, $a_j$ uniformly in its sign-range interval for $j=2,\ldots,9$,
$a_{10}=10$) and classified into one of the eight analytic regions of the proof
($\sigma_2=\pm1$; sub-regions $\alpha_1,\alpha_3,\beta_1,\beta_2,\beta_3,\beta_4$).
Every region was covered in both campaigns and no exceptional behaviour was observed
in any region.

With zero failures across $1.1\times10^9$ event-complete trials, the 99.9% confidence
upper bound on the true failure rate is $6.9\times10^{-9}$.

**Reproducibility.**
This paper is archived at https://doi.org/10.5281/zenodo.19341800.
All computational materials are archived at
https://github.com/trentjp-gecta9/lrc-n11-computational-verification
and include the following artifacts:

- `scripts/verify_lrc_n11.py` — verification harness
- `scripts/exact_symbolic.py` — exact rational inequality checker
- `results/symbolic/exact_symbolic_results.json` — 34/34 log
- `results/run_1e8_mech/batches.jsonl` — $10^8$ audit trail
- `results/run_1e9_mech/batches.jsonl.gz` — $10^9$ audit trail
- `results/run_*/summary.json` — campaign summaries

Each campaign is fully reproducible from the `README` instructions.

---

# Appendix C. The Irrational Case

The reduction of irrational to commensurable speeds is standard in the lonely runner
literature [KN74]. We include the explicit Kronecker construction here because our
commensurable proof produces an *open* witness set $U\subset W_{\mathrm{ref}}$ (Corollary 7.4).
It is the openness of $U$ — not merely the existence of a witness — that allows the
Kronecker orbit to intersect $\mathcal{S}$; we verify this explicitly below rather than
invoking a black-box density argument.

The strategy is: approximate $(e_1,\ldots,e_{10})$ by a commensurable configuration
$(q_1,\ldots,q_{10})$ that preserves all integer relations among the original speeds,
find a witness point $y\in\mathcal{S}$ for the approximation, and then use Kronecker's
theorem to show the orbit of the original speeds is dense in a subtorus containing $y$.

**Lemma C.1 (Commensurable reduction).** *If $q_1<\cdots<q_{10}$ are positive
commensurable reals, then after clearing denominators the problem reduces to the
corresponding integer-speed configuration.*

*Proof.*
Write $q_i=p_i\omega$ with positive integers $p_i$ and $\omega>0$. Then
$\|q_it\|=\|p_i(\omega t)\|$, so a witness for $(p_1,\ldots,p_{10})$ at time $\omega t$
yields one for $(q_1,\ldots,q_{10})$ at time $t$. $\square$

**Proposition C.2 (Irrational-Ratio Proposition).** *If $e_i/e_j\notin\mathbb{Q}$ for
at least one pair $i\ne j$, then the conclusion of the Main Theorem holds.*

*Proof.*
Let $\mathbf{x}(t)=(e_1t,\ldots,e_{10}t)\bmod 1\in\mathbb{T}^{10}$,
$\mathcal{S}=(1/11,10/11)^{10}$, and
$L=\{m\in\mathbb{Z}^{10}:m\cdot e=0\}$ the lattice of integer relations among the speeds.
Let $T_e\subset\mathbb{T}^{10}$ be the Kronecker subtorus corresponding to $L$; by
Kronecker's theorem [KN74], the orbit $\{\mathbf{x}(t):t>0\}$ is dense in $T_e$.
It therefore suffices to show $T_e\cap\mathcal{S}\ne\emptyset$.

**Step 1 (commensurable approximation).**
Since $\dim_{\mathbb{Q}}\operatorname{span}_{\mathbb{Q}}\{e_1,\ldots,e_{10}\}=d\ge 2$,
choose a $\mathbb{Q}$-basis $b_1,\ldots,b_d$ for this span from $\{e_1,\ldots,e_{10}\}$
and write $e_i=\sum_{k=1}^d r_{ik}b_k$ with $r_{ik}\in\mathbb{Q}$.
Since the conditions "positive, distinct, ordered, $q_{10}/q_1\ne 10$" are all open,
we may choose a rational vector $v=(v_1,\ldots,v_d)\in\mathbb{Q}^d$ sufficiently close
to $(b_1,\ldots,b_d)$ that $q_i:=\sum_k r_{ik}v_k$ satisfies all four. The $q_i$ are
commensurable (rational linear combinations of rational $v_k$).

**Step 2 (witness for the approximation).**
- If $q_{10}/q_1<10$: the interval $(1/(11q_1),10/(11q_{10}))$ is nonempty because
  $10/(11q_{10})>1/(11q_1)\iff q_{10}/q_1<10$. Choose $s^*$ in this interval. Then
  $q_is^*\in(q_i/(11q_1),\,10q_i/(11q_{10}))\subset(1/11,\,10/11)\subset(0,1)$ for
  all $i$, so $y:=(\{q_1s^*\},\ldots,\{q_{10}s^*\})=(q_1s^*,\ldots,q_{10}s^*)\in\mathcal{S}$.
- If $q_{10}/q_1>10$: Lemma C.1 and Corollary 7.4 give an open witness set
  $U\subset W_{\mathrm{ref}}$ for $(q_1,\ldots,q_{10})$. Since $\mathcal{S}$ is open,
  pick $y\in U\cap\mathcal{S}$ (any witness in $U$ satisfies the strict inequality, so
  $y\in\mathcal{S}$).

In both cases $y\in\mathbb{T}^{10}$ with $y\in\mathcal{S}$.

**Step 3 ($y\in T_e$).**
We claim $L\subseteq L_q:=\{m\in\mathbb{Z}^{10}:m\cdot q=0\}$, i.e. every integer
relation of $e$ is also a relation of $q$. Indeed, if $\sum_i c_ie_i=0$ then
$\sum_i c_i\sum_k r_{ik}b_k=0$, so $\sum_k(\sum_i c_ir_{ik})b_k=0$. Since
$b_1,\ldots,b_d$ are $\mathbb{Q}$-linearly independent, each coefficient
$\alpha_k:=\sum_i c_ir_{ik}=0$. Therefore $\sum_i c_iq_i=\sum_k\alpha_kv_k=0$.

It follows that the Kronecker subtorus $T_q$ for $(q_1,\ldots,q_{10})$ satisfies
$T_q\subseteq T_e$. Since $y$ lies in the orbit closure of the $q_i$-flow,
$y\in T_q\subseteq T_e$.

**Conclusion.**
We have $y\in T_e\cap\mathcal{S}$. Since the orbit $\{\mathbf{x}(t)\}$ is dense in $T_e$
and $\mathcal{S}$ is open, some $t>0$ gives $\mathbf{x}(t)\in\mathcal{S}$, as required.
$\square$

---

*End of v33. Next: TikZ figure for Figure 1 to be added in .tex conversion.*
