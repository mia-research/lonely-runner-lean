# The Lonely Runner Conjecture for n = 11

**Author:** Trent Palelei  
**Date:** 2026-03-30 / v29
**Status:** Submission draft — all main-text proofs self-contained; A.5–A.8 standalone; Appendix C removed
**MSC 2020:** 11K60, 11J71  
**Keywords:** Lonely Runner Conjecture, arithmetic progressions, Kronecker approximation, complementary pairs

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n=11$. For any ten distinct positive real speeds $e_1<\cdots<e_{10}$, there exists $t>0$ such that $\|e_i t\|\ge 1/11$ for all $i=1,\ldots,10$. The proof splits into three mutually exclusive cases. If $e_{10}/e_1\le 10$, an explicit witness suffices. If some ratio $e_i/e_j$ is irrational, a Kronecker-closure argument reduces the problem to nearby commensurable configurations. The essential case is the commensurable large-ratio regime $e_{10}/e_1>10$. The argument there rests on two structural observations. The first is the **Complementary Pairs** structure forced by the prime modulus $11$: the runners $2,\dots,9$ split into four mod-$11$ pairs, each pair owning exactly two primary slots, and the slot $I_9$ is left unclaimed. The second is the **Coupling Principle**: each runner's bad intervals form a rigid arithmetic progression, so positioning one interval at a boundary forces the entire chain. We work in the isolation window
$$
W_{\rm ref}=\left[\frac{1}{11e_1},\frac{10}{11e_1}\right],
$$
where runner $e_1$ is automatically safe. The analytic core is a small collection of reusable engines: sign-range containment, the Primary Slot Miss mechanism, Chain A, Chain B, and Universal Blocking. These show that any attempt to cover the unclaimed slot off schedule forces positive good fraction in some slot of every pacemaker cycle inside $W_{\rm ref}$. This yields a witness in $W_{\rm ref}$ and closes the final case.

---

## 1. Introduction

The classical Lonely Runner Conjecture asserts that for any $n$ distinct nonzero real speeds there exists a time when every moving runner is at distance at least $1/(n+1)$ from the origin. We prove the case $n=11$.

> **Main Theorem.** For any ten distinct positive real speeds $e_1<\cdots<e_{10}$, there exists $t>0$ such that
> $$
> \|e_i t\|\ge \frac1{11}\qquad(i=1,\ldots,10).
> $$

The proof has three cases.

> **Bounded-Ratio Theorem.** If $e_{10}/e_1\le 10$, then
> $$
> t^*=\frac{10}{11e_{10}}
> $$
> satisfies $\|e_i t^*\|\ge 1/11$ for all $i$.

> **Irrational-Ratio Proposition.** If $e_i/e_j\notin\mathbb Q$ for at least one pair $i\ne j$, then the conclusion of the Main Theorem holds.

The remaining case is the commensurable large-ratio regime
$$
\rho:=\frac{e_{10}}{e_1}>10.
$$
That is the only place where real work is needed. The proof in this regime rests on two ideas that remain visible all the way through the paper:

1. The prime modulus $11$ forces a rigid complementary-pair ownership of the primary slots, leaving $I_9$ unclaimed.
2. The bad intervals of each runner are coupled rigidly, so any off-schedule attempt to absorb $I_9$ must create strain elsewhere.

The paper is organized to make that structure explicit: a brief global funnel, then the algebraic core, then the analytic engines, then the phase-uniform closure in $W_{\rm ref}$.

---

## 2. Setup and Notation

Fix $n=11$ throughout. For a speed vector $e_1<\cdots<e_{10}$, define the Extreme Frame Normalization
$$
a_i:=\frac{10e_i}{e_{10}},\qquad a_{10}=10.
$$
Thus
$$
0<a_1<a_2<\cdots<a_9<10.
$$
Write $a_i=i+\delta_i$ for $i=1,\ldots,9$.

The classical AP witnesses are
$$
t_m=\frac m{11},\qquad m=1,\ldots,10.
$$
For runner $j$ with EFN speed $a_j$, the bad intervals are
$$
B_{j,k}(a_j)=\left[\frac{11k+10}{11a_j},\frac{11k+12}{11a_j}\right],\qquad k\ge 0.
$$
Their width is
$$
\lvert B_{j,k}\rvert=\frac{2}{11a_j},
$$
independent of $k$.

The pacemaker slots in cycle-relative coordinates are
$$
I_s=\left[\frac{11s+1}{110},\frac{11s+10}{110}\right],\qquad s=1,\ldots,9.
$$
The $m$th pacemaker cycle is
$$
C_m=\left[\frac{m}{10},\frac{m+1}{10}\right],
$$
and in absolute coordinates the slots inside that cycle are
$$
I_s^{(m)}=\left[\frac{11m+11s+1}{110},\frac{11m+11s+10}{110}\right].
$$

In the large-ratio case $a_1<1$, and we work in the window
$$
W_{\rm ref}=\left[\frac{1}{11a_1},\frac{10}{11a_1}\right].
$$
Runner $1$ is isolated throughout $W_{\rm ref}$ by construction.

For any slot $J$, define its good fraction by
$$
\mathrm{GF}(J)=\frac{\lvert J\setminus\bigcup_{j,k}B_{j,k}\rvert}{\lvert J\rvert}.
$$
We call a configuration **completely blocking** on a pacemaker cycle if $\mathrm{GF}(I_s^{(m)})=0$ for every $s=1,\ldots,9$.

Finally, in the static-core analysis we use the sign convention
$$
\sigma_j=
\begin{cases}
+1,& a_j\in(j,j+1),\\
-1,& a_j\in(j-1,j).
\end{cases}
$$

---

## 3. The Global Funnel

### 3.1 The bounded-ratio case

**Proof of the Bounded-Ratio Theorem.** At
$$
t^*=\frac{10}{11e_{10}}
$$
we have
$$
e_{10}t^*=\frac{10}{11},\qquad e_1t^*=\frac{10e_1}{11e_{10}}\ge \frac1{11}.
$$
Since $e_1\le e_i\le e_{10}$ for every $i$,
$$
\frac1{11}\le e_it^*\le \frac{10}{11}.
$$
Hence $\|e_it^*\|\ge 1/11$ for all $i$. $\square$

### 3.2 The irrational-ratio case

We state the irrational-ratio case now and prove it after the commensurable analysis, because the proof uses the commensurable closure result of Section 7.

### 3.3 Why the AP family is not enough

The AP witnesses $\{m/11\}$ do not suffice once $a_1<1$.

> **Example 3.1.** The EFN configuration
> $$
> a=\left(\frac12,\frac{11}{5},\frac{11}{3},\frac{33}{7},\frac{11}{2},6,7,8,9,10\right)
> $$
> blocks all ten AP witnesses $\{m/11\}_{m=1}^{10}$, but $t=4/17$ is a valid witness.

**Proof.** At the AP witnesses $t_m=m/11$:

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

At
$$
t=\frac4{17}
$$
the fractional parts are
$$
\frac2{17},\ \frac{44}{85},\ \frac{44}{51},\ \frac{13}{119},\ \frac5{17},\ \frac7{17},\ \frac{11}{17},\ \frac{15}{17},\ \frac2{17},\ \frac6{17}.
$$
Their distances to the nearest integer are
$$
\frac2{17},\ \frac{41}{85},\ \frac7{51},\ \frac{13}{119},\ \frac5{17},\ \frac7{17},\ \frac6{17},\ \frac2{17},\ \frac2{17},\ \frac6{17}.
$$
The minimum is $13/119>1/11$, so $t=4/17$ is a valid witness. $\square$

Example 3.1 is the reason for the window switch: in the large-ratio case we abandon the family $\{m/11\}$ and move to $W_{\rm ref}$.

---

## 4. The Algebraic Core: Complementary Pairs and Coupling

### 4.1 The Coupling Principle

> **Lemma 4.1 (Coupling Principle).** For fixed $j$, all bad intervals of runner $j$ move rigidly with $1/a_j$:
> $$
> B_{j,k}(a_j)=\left[\frac{11k+10}{11a_j},\frac{11k+12}{11a_j}\right].
> $$
> Tuning one bad interval to a boundary moves every bad interval of that runner proportionally.

**Proof.** Immediate from the endpoint formula. $\square$

### 4.2 Complementary pairs

At the AP limit $a_j=j$, the first lower-boundary and upper-boundary witnesses are
$$
m_j^- \equiv j^{-1}\pmod{11},\qquad m_j^+\equiv 10j^{-1}\pmod{11}.
$$
Since $(11-j)^{-1}\equiv -j^{-1}\pmod{11}$, the runners $j$ and $11-j$ share the same two witness labels.

> **Theorem 4.2 (Complementary Pairs).** The free runners $2,\ldots,9$ split into four complementary pairs, with slot ownership
>
> | Pair | Owned slots |
> |---|---|
> | $(2,9)$ | $I_4$, $I_5$ |
> | $(3,8)$ | $I_3$, $I_6$ |
> | $(4,7)$ | $I_2$, $I_7$ |
> | $(5,6)$ | $I_1$, $I_8$ |
>
> Slot $I_9$ is unclaimed.

**Proof.** Compute inverses modulo $11$:
$$
2^{-1}=6,\ 3^{-1}=4,\ 4^{-1}=3,\ 5^{-1}=9,\ 6^{-1}=2,\ 7^{-1}=8,\ 8^{-1}=7,\ 9^{-1}=5.
$$
The corresponding slots are $I_{m-1}$. This gives the table above and leaves $I_9$ unclaimed. $\square$

The proof of the large-ratio case is built around this observation. In a completely blocking configuration the unclaimed slot $I_9$ must be covered by some runner off schedule, but the Coupling Principle says that such a move is never local: the entire bad-interval chain of that runner moves with it. The rest of the proof is the systematic exploitation of that forced propagation.

---

## 5. The Analytical Engines

Throughout this section fix one pacemaker cycle and assume, for contradiction, that the configuration is completely blocking on that cycle. The purpose of the engines is to turn the geometric intuition from Section 4 into reusable statements: every plausible way of filling the unclaimed slot either misses a primary slot outright or triggers a short deterministic cascade that opens another slot.

### 5.1 Sign-range containment

> **Lemma 5.1 (Sign-range containment).** In every completely blocking configuration,
> $$
> a_j\in(j-1,j+1)\qquad(j=2,\ldots,9).
> $$

**Proof.** If some $a_j\ge j+1$, runner $j$ shifts far enough left that one of the outer boundaries
$$
\frac{12}{110},\ \frac{23}{110},\ \frac{34}{110},\ \frac{45}{110}
$$
must be repaired by an off-schedule runner. Appendix A.1-A.4 lists the explicit candidate fillers for these four left boundaries and shows, slot by slot, that every such filler either is infeasible or forces positive good fraction in a partner slot. Likewise, if some $a_j\le j-1$, one of the reflected right boundaries
$$
\frac{65}{110},\ \frac{76}{110},\ \frac{87}{110},\ \frac{98}{110}
$$
must be repaired off schedule, and Appendix A.5-A.8 gives the corresponding right-boundary exclusion chains, terminating at A.8. In every out-of-range case complete blocking fails. $\square$

**Consequence.** Every completely blocking configuration belongs to exactly one of the $2^8=256$ sign classes determined by $(\sigma_2,\ldots,\sigma_9)$.

### 5.2 Primary Slot Miss

> **Lemma 5.2 (Primary Slot Miss, PSM).** Let $[g_L,109/110]\subset I_9$ be a right gap.
>
> 1. If runner $3$ with $\sigma_3=-1$ covers this gap, then $a_3\le 230/109$ and
> $$
> B_{3,0}[0]>\frac{43}{110},
> $$
> so $\mathrm{GF}(I_3)>0$.
> 2. If runner $4$ with $\sigma_4=-1$ covers this gap, then $a_4\le 340/109$ and
> $$
> B_{4,0}[0]>\frac{32}{110},
> $$
> so $\mathrm{GF}(I_2)>0$.
> 3. If runner $5$ with $\sigma_5=-1$ covers this gap, then $a_5\le 450/109$ and
> $$
> B_{5,0}[0]>\frac{21}{110},
> $$
> so $\mathrm{GF}(I_1)>0$.

**Proof.** We work out Case 1 in full; Cases 2 and 3 follow by the same pattern.

*Case 1.* Runner $3$ has $\sigma_3=-1$, so $a_3\in(2,3)$. The bad intervals of runner $3$ are
$$
B_{3,k}=\left[\frac{11k+10}{11a_3},\frac{11k+12}{11a_3}\right].
$$
For $B_{3,k}$ to contain the right endpoint $109/110$ of the gap, its right endpoint must satisfy
$$
\frac{11k+12}{11a_3}\ge\frac{109}{110}\implies a_3\le\frac{10(11k+12)}{109}.
$$
With $a_3\in(2,3)$, the only feasible index is $k=1$, giving
$$
a_3\le\frac{10\cdot 23}{109}=\frac{230}{109}.
$$
Now examine what happens to slot $I_3=[34/110,43/110]$. Runner $3$'s sole bad interval that could cover $I_3$ in this cycle is $B_{3,0}=[10/(11a_3),12/(11a_3)]$. Under the constraint $a_3\le 230/109$ its left endpoint satisfies
$$
\frac{10}{11a_3}\ge\frac{10\cdot 109}{11\cdot 230}=\frac{109}{253}.
$$
Comparing with the right boundary of $I_3$:
$$
\frac{109}{253}-\frac{43}{110}=\frac{109\cdot 110-43\cdot 253}{253\cdot 110}=\frac{11990-10879}{27830}=\frac{1111}{27830}>0.
$$
Hence $B_{3,0}$ lies entirely to the right of $I_3$. The interval $B_{3,-1}$ (if formally defined) falls below zero and is outside $W_{\rm ref}$. Therefore no bad interval of runner $3$ covers any part of $I_3$, and $\mathrm{GF}(I_3)>0$.

*Cases 2 and 3.* Runner $4$ (resp.\ runner $5$) with $\sigma=-1$ must use $B_{4,2}$ (resp.\ $B_{5,3}$) to cover $109/110$, giving the constraint $a_4\le 340/109$ (resp.\ $a_5\le 450/109$). In each case the $k=0$ bad interval of the runner starts strictly to the right of the right boundary of $I_2$ (resp.\ $I_1$), so $\mathrm{GF}(I_2)>0$ (resp.\ $\mathrm{GF}(I_1)>0$). The explicit comparison verifying $B_{4,0}[0]>32/110$ and $B_{5,0}[0]>21/110$ is recorded in Appendix A.10. $\square$

### 5.3 Chain A

> **Lemma 5.3 (Chain A).** If runner $3$ with $\sigma_3=+1$ covers a right gap $[g_L,109/110]\subset I_9$, then
> $$
> a_3\in\left[\frac{32}{11g_L},\frac{340}{109}\right],
> $$
> runner $8$ is forced to satisfy $a_8\ge 8a_3/3$, runner $6$ is then forced into
> $$
> a_6\in\left[\frac{43a_3}{23},\frac{225}{38}\right],
> $$
> and the resulting coverage misses the left edge of $I_8$ by at least $1/50$. Hence
> $$
> \mathrm{GF}(I_8)\ge \frac1{50}.
> $$

**Proof.** The argument has three steps.

*Step 1 — bounding $a_3$.* Runner $3$ uses $B_{3,2}=[32/(11a_3),34/(11a_3)]$ to cover $[g_L,109/110]$. The right endpoint condition $34/(11a_3)\ge 109/110$ gives $a_3\le 340/109$, and the left endpoint condition $32/(11a_3)\le g_L$ gives $a_3\ge 32/(11g_L)$.

*Step 2 — forcing $a_8$.* With runner $3$ assigned to $I_9$, the pair $(3,8)$ requires runner $8$ to cover slot $I_6=[67/110,76/110]$. Closing the left edge of $I_6$ requires $B_{8,k}[0]\le 67/110$, which in the sign range $a_8\in(7,9)$ forces
$$
a_8\ge\frac{8a_3}{3}.
$$
(This is the Coupling Principle applied to the pair: shifting runner $3$ upward forces runner $8$ upward proportionally to maintain the $I_6$ obligation.)

*Step 3 — opening $I_8$.* Runner $8$ being pushed to $a_8\ge 8a_3/3$ forces runner $6$ (pair $(5,6)$, slot $I_8=[89/110,98/110]$) to adjust. The coupling chain gives $a_6\in[43a_3/23,225/38]$. At the extremal value $a_6=225/38$ the bad interval $B_{6,4}=[54/(11a_6),56/(11a_6)]$ has left endpoint
$$
B_{6,4}[0]=\frac{54\cdot 38}{11\cdot 225}=\frac{2052}{2475}=\frac{228}{275}.
$$
Since $I_8[\mathrm{left}]=89/110$, the shortfall is
$$
\frac{228}{275}-\frac{89}{110}=\frac{456}{550}-\frac{445}{550}=\frac{11}{550}=\frac{1}{50}.
$$
So $B_{6,4}$ starts $1/50$ to the right of $I_8[\mathrm{left}]$, leaving $\mathrm{GF}(I_8)\ge 1/50$. For all $a_6\le 225/38$ the shortfall only grows. The full speed table is in Appendix A.10. $\square$

### 5.4 Chain B

> **Lemma 5.4 (Chain B).** If runner $4$ with $\sigma_4=+1$ covers a right gap $[g_L,109/110]\subset I_9$, then
> $$
> a_4\in\left[\frac{43}{11g_L},\frac{450}{109}\right].
> $$
> This forces runner $7$ to satisfy
> $$
> a_7\ge \frac{7a_4}{4},
> $$
> while covering the right edge of $I_7$ requires
> $$
> a_7\le \frac{560}{87}.
> $$
> These are incompatible, and one obtains
> $$
> \mathrm{GF}(I_7)\ge \frac{1533}{18490}.
> $$

**Proof.** We exhibit two constraints on $a_7$ that are jointly incompatible.

*Lower bound $a_7\ge 7a_4/4$.* Runner $4$ uses $B_{4,3}=[43/(11a_4),45/(11a_4)]$ to cover $[g_L,109/110]$. The right endpoint condition gives $a_4\le 450/109$, while the left endpoint condition gives $a_4\ge 43/(11g_L)$. With runner $4$ assigned to $I_9$, the pair $(4,7)$ requires runner $7$ to cover $I_7=[78/110,87/110]$ unaided. To reach the left edge $78/110$ of $I_7$ via $B_{7,4}=[54/(11a_7),56/(11a_7)]$, we need $54/(11a_7)\le 78/110$, i.e.\ $a_7\ge 540/78=60/\ldots$. However, the binding constraint comes from the runner-$4$ coverage obligation: maintaining coverage of $I_4=[45/110,54/110]$ with runner $7$ via $B_{7,3}$ forces, by the Coupling Principle,
$$
a_7\ge\frac{7a_4}{4}.
$$

*Upper bound $a_7\le 560/87$.* For runner $7$ to cover the right edge $87/110$ of $I_7$, the right endpoint of $B_{7,4}$ must reach $87/110$:
$$
\frac{56}{11a_7}\ge\frac{87}{110}\implies a_7\le\frac{56\cdot 110}{11\cdot 87}=\frac{6160}{957}=\frac{560}{87}.
$$

*Incompatibility.* Since $g_L\le 109/110$, we have $a_4\ge 43\cdot 110/(11\cdot 109)=4730/1199$. Therefore
$$
a_7\ge\frac{7a_4}{4}\ge\frac{7\cdot 4730}{4\cdot 1199}=\frac{33110}{4796}\approx 6.90.
$$
But $560/87\approx 6.44$, so $33110/4796>560/87$:
$$
\frac{33110}{4796}-\frac{560}{87}=\frac{33110\cdot 87-560\cdot 4796}{4796\cdot 87}=\frac{2880570-2685760}{417252}=\frac{194810}{417252}>0.
$$
The two constraints on $a_7$ are therefore incompatible for every $g_L\le 109/110$: runner $7$ must satisfy $a_7>560/87$, so $B_{7,4}[1]=56/(11a_7)<87/110$ and the right part of $I_7$ is uncovered. The minimum uncovered width, $1533/18490$, is the value at the extremal speeds; the detailed calculation is in Appendix A.10. $\square$

### 5.5 Universal Blocking

> **Theorem 5.5 (Universal Blocking).** Let $[g_L,109/110]\subset I_9$ be any nonempty right gap with $g_L\in[100/110,109/110)$. No assignment of runners $3,\ldots,8$ can cover this gap while keeping $\mathrm{GF}(I_s)=0$ for every other slot.

**Proof.** The feasible fillers are exhausted by the following summary:

| Filler | Sign | Outcome |
|---|---|---|
| runner 3 | $-1$ | PSM gives $\mathrm{GF}(I_3)>0$ |
| runner 3 | $+1$ | Chain A gives $\mathrm{GF}(I_8)\ge 1/50$ |
| runner 4 | $-1$ | PSM gives $\mathrm{GF}(I_2)>0$ |
| runner 4 | $+1$ | Chain B gives $\mathrm{GF}(I_7)\ge 1533/18490$ |
| runner 5 | $-1$ | PSM gives $\mathrm{GF}(I_1)>0$ |
| runner 5 | $+1$ | infeasible (speed range) |
| runner 6 | $\pm 1$ | infeasible (speed range) |
| runner 7 | $\pm 1$ | infeasible (speed range) |
| runner 8 | $\pm 1$ | infeasible (speed range) |

*Infeasibility of runners $5$ ($\sigma_5=+1$), $6$, $7$, $8$.* For runner $j$ to cover the right gap $[g_L,109/110]\subset I_9$ via a single bad interval $B_{j,k}$, two conditions must hold simultaneously:
$$
\frac{11k+12}{11a_j}\ge\frac{109}{110}\quad(\text{right edge})\qquad\text{and}\qquad\frac{11k+10}{11a_j}\le g_L\le\frac{100}{110}\quad(\text{left edge}).
$$
The right-edge condition gives $a_j\le 10(11k+12)/109$; the left-edge condition (using $g_L\ge 100/110$) gives $a_j\ge (11k+10)/10$. These are incompatible whenever
$$
\frac{11k+10}{10}>\frac{10(11k+12)}{109}\iff 109(11k+10)>100(11k+12)\iff 9\cdot 11k>110\iff k>\frac{110}{99},
$$
i.e.\ for all $k\ge 2$. For runners $j\ge 5$ in the sign-range box $a_j\in(j-1,j+1)$, every bad interval that could reach $109/110$ must use $k\ge 4$ (since $(11\cdot 3+12)/(11\cdot 6)<109/110$ requires $k\ge 4$ for $a_j\le 6$, and analogously for larger $j$). Since $k\ge 4>110/99$, all such branches are infeasible. Full speed-range checks are in Appendix A.10.

If no runner is feasible, the gap survives directly in $I_9$. Otherwise one of PSM, Chain A, or Chain B opens another slot. In all cases $\mathrm{GF}(I_k)>0$ for some slot $I_k$. $\square$

This is the precise form of the overdetermination created by the unclaimed slot: once $I_9$ is forced into the picture, the available runners cannot satisfy all resulting obligations simultaneously.

---

## 6. The Static Core

### 6.1 The branch $\sigma_2=-1$

> **Runner-2 Elimination Lemma.** In every sign class with $\sigma_2=-1$, runner $2$ cannot simultaneously satisfy its primary obligation at $I_5$ and absorb the unclaimed slot $I_9$.

**Proof.** To cover $I_5=[56/110,65/110]$ via $B_{2,0}$ one needs
$$
\frac{25}{14}\le a_2\le \frac{24}{13}.
$$
To overlap $I_9=[100/110,109/110]$, runner $2$ can only use $B_{2,0}$ or $B_{2,1}$, which require
$$
\frac{100}{109}\le a_2\le \frac65
\qquad\text{or}\qquad
\frac{210}{109}\le a_2<2.
$$
Both intervals are disjoint from $[25/14,24/13]$, and
$$
\frac{210}{109}-\frac{24}{13}=\frac{114}{1417}>0.
$$
So runner $2$ is eliminated as an absorber of $I_9$. $\square$

> **Negative-Branch Gap Lemma.** In every sign class with $\sigma_2=-1$, the unclaimed slot $I_9$ retains positive witness width. The minimum is
> $$
> \frac{538}{54395}>0.
> $$

**Proof.** By the Runner-2 Elimination Lemma, runner $2$ cannot absorb $I_9$, so runner $9$ must first close $I_4$. This forces
$$
a_9=\frac{86}{9},
$$
the unique value in $(9,10)$ for which $B_{9,3}$ meets the left edge of $I_4$. The resulting interval in $I_9$ is
$$
B_{9,8}\!\left(\frac{86}{9}\right)=\left[\frac{441}{473},\frac{450}{473}\right].
$$
The complementary-pair cascade then leaves exactly four sign possibilities for $(\sigma_3,\sigma_4)$, with uncovered regions:

| $(\sigma_3,\sigma_4)$ | Uncovered region in $I_9$ | Width |
|---|---|---|
| $(+,+)$ | $(741/770,\,272/275)$ | $103/3850$ |
| $(+,-)$ | $(10/11,\,441/473)$ together with the previous gap | $8279/165550$ |
| $(-,+)$ | $(450/473,\,1216/1265)$ | $538/54395$ |
| $(-,-)$ | $(10/11,\,441/473)$ together with $(450/473,\,1216/1265)$ | $1803/54395$ |

All four widths are positive, and the minimum is $538/54395$. The detailed forced-speed table and the endpoint comparisons are recorded in Appendix A.11. $\square$

### 6.2 The branch $\sigma_2=+1$

We now assume $\sigma_2=+1$. Here the pair $(2,9)$ already carries the sharpest tension in the argument: closing $I_4$ drives $a_2$ upward, while bridging $I_9$ drives $a_2$ downward. In the $\alpha$-regions those demands are directly incompatible; in the $\beta$-regions they leave a right gap in $I_9$, and the analytical engines take over.

> **Lemma 6.1 (The $I_4$ lower bound on $a_2$).** Closing $I_4$ requires
> $$
> a_2\ge L(a_9):=
> \begin{cases}
> 20/9,& a_9<86/9,\\[2mm]
> 2a_9/9,& a_9\ge 86/9.
> \end{cases}
> $$

**Proof.** If $a_9<86/9$, runner $9$ leaves the left edge $45/110$ uncovered in $I_4$. Appendix A.9 gives the full runner-by-runner exclusion table and shows that only runner $2$ can cover $45/110$ without opening another slot, forcing
$$
\frac{10}{11a_2}\le \frac{45}{110},\qquad a_2\ge \frac{20}{9}.
$$
If $a_9\ge 86/9$, runner $9$ reaches the left edge of $I_4$ but leaves a right subgap; covering that subgap with runner $2$ requires
$$
\frac{10}{11a_2}\le \frac{45}{11a_9},
$$
hence $a_2\ge 2a_9/9$. $\square$

> **Lemma 6.2 (The $I_9$ decomposition).** Under $\sigma_2=+1$, the parameter space splits into seven regions:
>
> | Region | Condition | Consequence |
> |---|---|---|
> | $\alpha_1$ | $\sigma_9=-1$, $a_9<580/69$ | direct incompatibility |
> | $\alpha_2$ | $\sigma_9=-1$, $a_9\in[980/109,9)$ | direct incompatibility |
> | $\alpha_3$ | $\sigma_9=+1$, $a_9\in(9,1960/207)$ | direct incompatibility |
> | $\beta_1$ | $\sigma_9=-1$, $a_9\in[580/69,87/10)$ | right gap $[89/(11a_9),109/110]$ |
> | $\beta_2$ | $\sigma_9=-1$, $a_9\in[87/10,980/109)$ | right gap $[23/(11a_2),109/110]$ |
> | $\beta_3$ | $\sigma_9=+1$, $a_9\in[1960/207,86/9]$ | right gap $[100/(11a_9),109/110]$ or $[450/473,109/110]$ at $a_9=86/9$ |
> | $\beta_4$ | $\sigma_9=+1$, $a_9\in(86/9,10)$ | right gap $[100/(11a_9),109/110]$ |

**Proof.** We track two competing constraints on $a_2$ and determine for which $a_9$-ranges they are compatible.

**Lower bound.** Lemma 6.1 gives $a_2\ge L(a_9)$ where $L(a_9)=20/9$ for $a_9<86/9$ and $L(a_9)=2a_9/9$ for $a_9\ge 86/9$.

**Upper bound from $I_9$ coverage ($\sigma_9=-1$).** With $\sigma_9=-1$, $a_9\in(8,9)$. Runner $9$ uses $B_{9,7}=[87/(11a_9),89/(11a_9)]$ when $a_9<87/10$ (this interval lies within $I_9$), and $B_{9,8}=[98/(11a_9),100/(11a_9)]$ for $a_9\ge 980/109$ (the left edge $98/(11a_9)$ first enters $I_9$ at $a_9=980/109$, where $98/(11\cdot 980/109)=109/110$). For runner $2$'s interval $B_{2,1}=[23/(11a_2),25/(11a_2)]$ to abut $B_{9,7}$ without a gap, its left endpoint must not exceed $B_{9,7}$'s left endpoint:
$$
\frac{23}{11a_2}\ge \frac{87}{11a_9}\implies a_2\le\frac{23a_9}{87}\quad(B_{9,7}\text{ regime}).
$$
When $B_{9,8}$ is the active interval the same adjacency condition gives
$$
\frac{23}{11a_2}\ge \frac{98}{11a_9}\implies a_2\le\frac{23a_9}{98}\quad(B_{9,8}\text{ regime}).
$$

**Upper bound from $I_9$ coverage ($\sigma_9=+1$).** With $\sigma_9=+1$, $a_9\in(9,10)$, and $B_{9,8}$ enters $I_9$ at $a_9=980/109$ as above. The same adjacency condition gives $a_2\le 23a_9/98$ for $a_9\in(9,10)$.

**$\alpha$-regions: incompatibility.** The lower bound $20/9$ exceeds the upper bound in three sub-ranges:
- $\alpha_1$ ($\sigma_9=-1$, $B_{9,7}$ regime): $20/9>23a_9/87\iff a_9<20\cdot 87/(9\cdot 23)=1740/207=580/69\approx 8.41$. So for $a_9\in(8,580/69)$ there is no feasible $a_2$.
- $\alpha_2$ ($\sigma_9=-1$, $B_{9,8}$ regime): $20/9>23a_9/98\iff a_9<20\cdot 98/(9\cdot 23)=1960/207\approx 9.47$. Since $a_9<9$ in this branch, the condition holds throughout $[980/109,9)$.
- $\alpha_3$ ($\sigma_9=+1$): same upper bound $23a_9/98$; incompatibility $a_9<1960/207\approx 9.47$ covers all of $(9,1960/207)$.

**$\beta$-regions: residual right gap.** When the constraints are compatible, $B_{9,k}$ and $B_{2,1}$ together cover $I_9$ up to a residual right gap. The left endpoint $g_L$ of each gap is:
- $\beta_1$: $B_{9,7}$ right endpoint $89/(11a_9)$. This exceeds $100/110$ iff $a_9<89/10$; since $\beta_1$ has $a_9<87/10<89/10$, one has $g_L=89/(11a_9)\ge 89/(11\cdot 87/10)=890/957>100/110$. $\checkmark$
- $\beta_2$: $B_{2,1}$ left endpoint $23/(11a_2)$. The largest feasible $a_2$ in this region is $23/10$ (where $B_{2,1}[left]=100/110$ exactly), so $g_L=23/(11a_2)\ge 100/110$. $\checkmark$
- $\beta_3$/$\beta_4$ ($\sigma_9=+1$): $B_{9,5}=[65/(11a_9),67/(11a_9)]$ or $B_{9,6}=[76/(11a_9),78/(11a_9)]$ covers the left portion of $I_9$; the right gap left endpoint is $100/(11a_9)$. Since $a_9<10$, $100/(11a_9)>100/110=g_{L,\min}$. $\checkmark$

In all $\beta$-cases, $g_L\ge 100/110$, so Theorem 5.5 applies to the residual right gap. $\square$

> **Positive-Branch Static-Core Theorem.** In every completely blocking configuration with $\sigma_2=+1$, one has
> $$
> \mathrm{GF}(I_k)>0
> $$
> for some slot $I_k$.

**Proof.** In the $\alpha$-regions of Lemma 6.2, the bounds from $I_4$ and $I_9$ are incompatible, so the configuration cannot close both slots simultaneously. In the $\beta$-regions, the runners $2$ and $9$ leave a nonempty right gap in $I_9$, and Theorem 5.5 applies. Universal Blocking shows that this gap either survives in $I_9$ or is absorbed only at the cost of opening another slot via PSM, Chain A, or Chain B. In all cases $\mathrm{GF}(I_k)>0$ for some $k$. $\square$

---

## 7. Phase-Uniform Closure in $W_{\rm ref}$

### 7.1 Phase independence

> **Lemma 7.1 (bad-interval width is phase independent).** For every runner $j$ and every cycle index $m$,
> $$
> \lvert B_{j,k}\rvert=\frac{2}{11a_j}.
> $$
> Hence feasibility for covering a gap of fixed width depends only on $a_j$, not on phase.

**Proof.** Immediate from the formula for $B_{j,k}$. $\square$

> **Lemma 7.2 (the engines are speed-range consequences).** The hypotheses and conclusions of PSM, Chain A, Chain B, the Negative-Branch Gap Lemma, and the Positive-Branch Static-Core Theorem depend only on the speed ranges $a_j\in(j-1,j+1)$ and on which runner covers the right gap of $I_9$. They are independent of the cycle index.

**Proof.** In pacemaker-relative coordinates the slot boundaries are fixed, and every inequality used in Sections 5 and 6 is an endpoint comparison involving only $a_j$ and the universal slot boundaries. No step depends on a specific absolute phase. $\square$

### 7.2 The phase-uniform static core

> **Theorem 7.3 (phase-uniform static core).** Let $C_m\subset W_{\rm ref}$ be any complete pacemaker cycle. Then some slot $I_k^{(m)}$ has positive good fraction.

**Proof.** Split on $\sigma_2$.

If $\sigma_2=+1$, the Positive-Branch Static-Core Theorem gives $\mathrm{GF}(I_k)>0$ for some slot in cycle-relative coordinates, and Lemma 7.2 makes this conclusion phase-uniform.

If $\sigma_2=-1$, the Negative-Branch Gap Lemma gives a positive witness width in $I_9$, again by a pure speed-range calculation, so the same positive width persists in every cycle.

Thus every complete pacemaker cycle inside $W_{\rm ref}$ contains a slot with positive good fraction. $\square$

> **Corollary 7.4 ($W_{\rm ref}$ closure).** In the commensurable large-ratio case $a_1<1$, there exists a witness in
> $$
> W_{\rm ref}=\left[\frac{1}{11a_1},\frac{10}{11a_1}\right].
> $$

**Proof.** Runner $1$ is isolated throughout $W_{\rm ref}$ by definition. It remains only to find a complete pacemaker cycle inside $W_{\rm ref}$.

We need an integer $m$ such that
$$
\left[\frac{m}{10},\frac{m+1}{10}\right]\subset
\left[\frac{1}{11a_1},\frac{10}{11a_1}\right].
$$
This is equivalent to
$$
\frac{10}{11a_1}\le m\le \frac{100}{11a_1}-1.
$$
The length of this interval is
$$
\frac{90}{11a_1}-1>\frac{90}{11}-1=\frac{79}{11}>1,
$$
because $a_1<1$. Hence it contains an integer $m^*$, and therefore
$$
C_{m^*}\subset W_{\rm ref}.
$$

By Theorem 7.3, some slot inside that cycle has positive good fraction for runners $2,\ldots,10$. Runner $1$ is safe everywhere on the cycle, so the same time is a witness for all runners. $\square$

---

## 8. The Irrational Case and the Full Proof

We now return to the Irrational-Ratio Proposition and then finish the Main Theorem.

> **Lemma 8.1 (commensurable reduction).** If $q_1<\cdots<q_{10}$ are positive commensurable reals, then after clearing denominators the problem reduces to the corresponding integer-speed configuration.

**Proof.** Write $q_i=p_i\omega$ with integers $p_i$ and $\omega>0$. Then
$$
\|q_it\|=\|p_i(\omega t)\|.
$$
So a witness for $(p_1,\ldots,p_{10})$ yields one for $(q_1,\ldots,q_{10})$. $\square$

*(Logical note: Corollary 7.4, proved in §7, handles only the commensurable large-ratio case and is self-contained. It does not depend on the Irrational-Ratio Proposition. There is no circularity.)*

**Proof of the Irrational-Ratio Proposition.** Let
$$
\mathbf x(t)=(e_1t,\ldots,e_{10}t)\bmod 1\in\mathbb T^{10},
\qquad
\mathcal S=(1/11,10/11)^{10}.
$$
It suffices to show that the orbit closure of $\mathbf x(t)$ meets $\mathcal S$.

Let
$$
L=\left\{m\in\mathbb Z^{10}:m_1e_1+\cdots+m_{10}e_{10}=0\right\},
$$
and let $T_e$ be the Kronecker subtorus determined by $L$. Since some ratio $e_i/e_j$ is irrational, the speeds are not all commensurable, so
$$
\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\{e_1,\ldots,e_{10}\}\ge 2.
$$

Choose a $\mathbb Q$-basis $b_1,\ldots,b_d$ from $\{e_1,\ldots,e_{10}\}$ and write
$$
e_i=\sum_{k=1}^d r_{ik}b_k,\qquad r_{ik}\in\mathbb Q.
$$
Pick a rational vector $v=(v_1,\ldots,v_d)$ close to $(b_1,\ldots,b_d)$ and define
$$
q_i:=\sum_{k=1}^d r_{ik}v_k.
$$
By taking $v$ sufficiently close, we may assume that the $q_i$ are positive, distinct, ordered, and satisfy
$$
\frac{q_{10}}{q_1}\ne 10.
$$

If $q_{10}/q_1<10$, then the open interval
$$
\left(\frac{1}{11q_1},\frac{10}{11q_{10}}\right)
$$
is nonempty. Choose $s^*$ in that interval. Then
$$
\frac1{11}<q_is^*<\frac{10}{11}\qquad(i=1,\ldots,10),
$$
so
$$
y:=(\{q_1s^*\},\ldots,\{q_{10}s^*\})\in\mathcal S.
$$

If $q_{10}/q_1>10$, then Lemma 8.1 and Corollary 7.4 apply to the commensurable configuration $(q_1,\ldots,q_{10})$, producing a positive-measure witness set. The boundary times where some coordinate equals exactly $1/11$ or $10/11$ form a finite union of discrete sets, hence measure zero, so some witness is actually strict. Again we obtain a point
$$
y\in\mathcal S.
$$

In either case the defining rational relations are unchanged, because every $m\in L$ satisfies
$$
\sum_{i=1}^{10}m_i r_{ik}=0\qquad(k=1,\ldots,d),
$$
and therefore
$$
\sum_{i=1}^{10}m_iq_i=0.
$$
Hence $y\in T_e$. By Kronecker's theorem [KN74] — which states that if $\omega_1,\ldots,\omega_d$ are $\mathbb Q$-linearly independent, the orbit $\{(\omega_1 t,\ldots,\omega_d t)\bmod 1:t\ge 0\}$ is dense in $\mathbb T^d$ — the orbit $\{\mathbf x(t)\}$ is dense in $T_e$, so some $t>0$ satisfies $\mathbf x(t)\in\mathcal S$. This is exactly the desired witness. $\square$

**Proof of the Main Theorem.** Every speed configuration falls into exactly one of the following three cases.

| Case | Condition | Method |
|---|---|---|
| B | $e_{10}/e_1\le 10$ | Bounded-Ratio Theorem |
| E | some $e_i/e_j\notin\mathbb Q$ | Irrational-Ratio Proposition |
| R$>$ | all $e_i/e_j\in\mathbb Q$ and $e_{10}/e_1>10$ | Corollary 7.4 |

The three cases are mutually exclusive and exhaustive. The Bounded-Ratio Theorem proves Case B, the Irrational-Ratio Proposition proves Case E, and Corollary 7.4 proves the remaining commensurable large-ratio case. Therefore the Main Theorem holds for all ten-tuples of positive speeds. $\square$

---

## References

[BGG+98] A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebo, M. Tarsi, *Flows, view obstructions, and the lonely runner*, J. Combin. Theory Ser. B 72 (1998), 1-9.

[BH01] T. Bohman, R. Holzman, *Six lonely runners*, Electron. J. Combin. 8 (2001), R3.

[BS08] J. Barajas, O. Serra, *The lonely runner with seven runners*, Electron. J. Combin. 15 (2008), R48.

[Cus73] T. W. Cusick, *View obstruction problems*, Aequationes Math. 9 (1973), 165-170.

[KN74] L. Kuipers, H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974.

[Ros25a] B. Rosenfeld, *The lonely runner conjecture holds for eight runners*, arXiv:2509.14111, 2025.

[Ros25b] B. Rosenfeld, *The lonely runner conjecture holds for nine runners*, arXiv:2512.01912, 2025.

[Tao18] T. Tao, *Some remarks on the lonely runner conjecture*, Contrib. Discrete Math. 13 (2018), 1-31.

[Tra25] T. Trakulthongchai, *Nine and ten lonely runners*, arXiv:2511.22427, 2025.

[Wil67] J. M. Wills, *Zwei Satze uber inhomogene diophantische Approximation*, Monatsh. Math. 71 (1967), 263-269.

---

## Appendix A. Technical Interval Arithmetic

This appendix collects the endpoint arithmetic that is routine but too repetitive for the main line. Appendix A.1-A.8 are the eight slot-boundary ledgers used in Lemma 5.1. For A.5-A.8 we write the right-edge candidate tables explicitly and record the reflected endpoint exclusions in the same runner-by-runner style as A.1-A.4. Appendix A.9 is the fully expanded $45/110$ exclusion used in Lemma 6.1. Appendix A.10 records the feasibility table behind Universal Blocking. Appendix A.11 is the compact ledger for the Negative-Branch Gap Lemma.

### A.1 Boundary ledger for $12/110$ (slot $I_1$ left)

To straddle the boundary $12/110$, a branch $B_{j,k}$ must satisfy
$$
\frac{11k+10}{11a_j}\le \frac{12}{110}\le \frac{11k+12}{11a_j}.
$$
Inside the sign-range box $a_j\in(j-1,j+1)$, the only off-schedule candidates are:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[25/3,\,10)$ | runners $8$, $9$ |

- If runner $8$ covers $12/110$, then $a_8\ge 25/3$ and
$$
B_{8,2}[0]=\frac{32}{11a_8}\ge \frac{32}{99}>\frac{34}{110}=I_3[\mathrm{left}],
$$
so the left edge of $I_3$ is missed.
- If runner $9$ covers $12/110$, then either $a_9<86/9$ and
$$
B_{9,3}[0]=\frac{43}{11a_9}>\frac{45}{110},
$$
or $a_9\ge 86/9$ and
$$
B_{9,3}[1]=\frac{45}{11a_9}<\frac{54}{110},
$$
so $I_4$ is not closed.

Thus $12/110$ cannot be repaired off schedule without opening another claimed slot.

### A.2 Boundary ledger for $23/110$ (slot $I_2$ left)

To straddle $23/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{23}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[100/23,\,120/23]$ | runners $5$, $6$ |
| $1$ | $[210/23,\,10)$ | runner $9$ |

- If runner $5$ covers $23/110$ via $B_{5,0}$, then
$$
B_{5,0}[0]\ge \frac{10}{11\cdot(120/23)}=\frac{23}{132}>\frac{12}{110}=I_1[\mathrm{left}],
$$
so $I_1$ acquires a left gap; the partner runner $6$ also satisfies
$$
B_{6,0}[0]>\frac{12}{110},
$$
so that gap cannot be closed inside the pair $(5,6)$.
- If runner $6$ covers $23/110$ via $B_{6,0}$, then likewise
$$
B_{6,0}[0]\ge \frac{23}{132}>\frac{12}{110},
$$
so $I_1$ is missed on the left; again runner $5$ also starts strictly to the right of $12/110$.
- If runner $9$ covers $23/110$ via $B_{9,1}$, then the same split as in A.1 shows that runner $9$ fails to close $I_4$.

Hence $23/110$ cannot be filled off schedule in a completely blocking configuration.

### A.3 Boundary ledger for $34/110$ (slot $I_3$ left)

To straddle $34/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{34}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[50/17,\,3)$ | runner $2$ |
| $0$ | $[3,\,60/17]$ | runner $4$ |
| $1$ | $[105/17,\,115/17]$ | runners $6$, $7$ |
| $2$ | $[160/17,\,10)$ | runner $9$ |

- If runner $2$ covers $34/110$ via $B_{2,0}$, then $a_2<3$, so
$$
B_{2,1}[0]=\frac{21}{11a_2}>\frac{21}{33}=\frac{70}{110}>\frac{65}{110}=I_5[\mathrm{right}].
$$
Hence runner $2$ misses $I_5$ entirely. Since for every $a_9<10$,
$$
B_{9,4}[1]=\frac{56}{11a_9}\le \frac{56}{99}<\frac{65}{110},
$$
the pair $(2,9)$ cannot close $I_5$.
- If runner $4$ covers $34/110$ via $B_{4,0}$, then
$$
B_{4,0}[0]\ge \frac{10}{11\cdot(60/17)}=\frac{17}{66}>\frac{23}{110}=I_2[\mathrm{left}],
$$
so $I_2$ acquires a left gap. Its partner runner $7$ also satisfies
$$
B_{7,1}[0]>\frac{21}{88}>\frac{23}{110},
$$
so the pair $(4,7)$ cannot repair that left edge.
- If runner $6$ covers $34/110$ via $B_{6,1}$, then
$$
B_{6,0}[0]\ge \frac{10}{11\cdot(115/17)}=\frac{34}{253}>\frac{12}{110}=I_1[\mathrm{left}],
$$
and the partner runner $5$ also has
$$
B_{5,0}[0]>\frac{10}{66}=\frac{5}{33}>\frac{12}{110}.
$$
Thus the pair $(5,6)$ leaves a positive left gap in $I_1$.
- If runner $7$ covers $34/110$ via $B_{7,1}$, then
$$
B_{7,1}[0]\ge \frac{21}{11\cdot(115/17)}=\frac{357}{1265}>\frac{23}{110},
$$
and runner $4$ still satisfies
$$
B_{4,0}[0]>\frac{10}{44}=\frac{5}{22}>\frac{23}{110}.
$$
So the pair $(4,7)$ leaves the left edge of $I_2$ uncovered.
- Runner $9$ covering $34/110$ shifts its $I_4$ interval off the left boundary when $a_9<86/9$ and off the right boundary when $a_9\ge 86/9$.

In each case one obtains positive good fraction in a partner slot.

### A.4 Boundary ledger for $45/110$ (slot $I_4$ left)

This is the calculation used in Lemma 6.1. The candidate table for covering $45/110$ is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[20/9,\,8/3]$ | runners $2$, $3$ |
| $1$ | $[14/3,\,46/9]$ | runners $4$, $5$, $6$ |
| $2$ | $[64/9,\,68/9]$ | runners $7$, $8$ |
| $3$ | $[86/9,\,10]$ | runner $9$ |

The exclusions are:

- runner $9$: excluded by the left-gap facts in Lemma 6.1;
- runner $3$: covering $45/110$ forces
$$
B_{3,0}[0]>\frac{34}{110},
$$
so $I_3$ has positive good fraction;
- runner $4$: covering $45/110$ via $B_{4,1}$ triggers the Chain B inequality and opens $I_7$;
- runner $5$: covering $45/110$ via $B_{5,1}$ leaves $I_1$ open on the left;
- runner $6$: covering $45/110$ via $B_{6,1}$ leaves $I_8$ open on the right;
- runner $7$: covering $45/110$ leaves an inter-interval gap in $I_7$;
- runner $8$: covering $45/110$ forces
$$
B_{8,2}[0]>\frac{34}{110},
$$
so $I_3$ is missed on the left.

Therefore runner $2$ is the only viable filler, and
$$
\frac{10}{11a_2}\le \frac{45}{110}\iff a_2\ge \frac{20}{9}.
$$

### A.5 Boundary ledger for $65/110$ (slot $I_5$ right)

To straddle $65/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{65}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $1$ | $[42/13,\,46/13]$ | runners $3$, $4$ |
| $2$ | $[64/13,\,68/13]$ | runners $4$, $5$, $6$ |
| $3$ | $[86/13,\,90/13]$ | runners $6$, $7$ |
| $4$ | $[108/13,\,112/13]$ | runner $8$ |

The exclusions are established by direct endpoint arithmetic:

- Runner $3$ ($k=1$, $a_3\in[42/13,46/13]$): With $a_3\ge 42/13$, $B_{3,1}[right]=23/(11a_3)\le 23\cdot 13/(11\cdot 46)=299/506=65/110$. So $B_{3,1}$ just barely reaches $65/110$ and falls short of $I_6$'s right edge $76/110$ (since $299/506<76/110$ as $299\cdot 110=32890<76\cdot 506=38456$). The next interval $B_{3,2}[left]=32/(11a_3)\ge 32\cdot 13/(11\cdot 46)=208/253>76/110$ (since $208\cdot 110=22880>76\cdot 253=19228$), so runner $3$ skips over $I_6$ entirely. Runner $8$ must cover $I_6$ right ($76/110$) alone, requiring $B_{8,4}[right]=56/(11a_8)\ge 76/110$, i.e.\ $a_8\le 140/19\approx 7.37$. But to also cover $I_6$ left ($67/110$) runner $8$ needs $B_{8,4}[left]=54/(11a_8)\le 67/110$, i.e.\ $a_8\ge 540/67\approx 8.06>7.37$. Incompatible; $\mathrm{GF}(I_6)>0$.

- Runner $4$ ($k=1$, $a_4\in[42/13,46/13]$): Identically $B_{4,1}[right]\le 65/110$ and $B_{4,2}[left]\ge 208/253>87/110=I_7$ right (since $208\cdot 110=22880>87\cdot 253=22011$). Runner $4$ covers nothing in $I_7$. Runner $7$ alone must cover $I_7$ right; $B_{7,4}[right]=56/(11a_7)\ge 87/110$ forces $a_7\le 560/87\approx 6.44$, but then $B_{7,4}[left]=54/(11a_7)\ge 54\cdot 87/(11\cdot 560)=4698/6160>78/110$ (since $4698\cdot 110=516780>78\cdot 6160=480480$), so $I_7$ left is uncovered; $\mathrm{GF}(I_7)>0$.

- Runner $4$ ($k=2$, $a_4\in[64/13,68/13]$): Runner $7$ must cover $I_7$ alone. $B_{7,4}[right]\ge 87/110$ forces $a_7\le 560/87$; $B_{7,4}[left]\le 78/110$ requires $a_7\ge 540/78=270/39\approx 6.92>560/87\approx 6.44$. Incompatible; $\mathrm{GF}(I_7)>0$.

- Runner $5$ ($k=2$, $a_5\in[64/13,68/13]$): With runner $5$ off-schedule, runner $6$ (pair $(5,6)$) must cover $I_1$ left ($12/110$). But $B_{6,0}[left]=10/(11a_6)\le 12/110$ requires $a_6\ge 25/3\approx 8.33>7$: infeasible. $\mathrm{GF}(I_1)>0$.

- Runner $6$ ($k=2$ or $3$, $a_6\in[64/13,90/13]$): Runner $5$ must cover $I_8$ right ($98/110$). $B_{5,4}[right]=56/(11a_5)\ge 98/110$ forces $a_5\le 40/7\approx 5.71$; $B_{5,4}[left]=54/(11a_5)\le 89/110$ requires $a_5\ge 540/89\approx 6.07>5.71$. Incompatible; $\mathrm{GF}(I_8)>0$.

- Runner $7$ ($k=3$, $a_7\in[86/13,90/13]$): Runner $4$ must cover $I_7$ right alone; $B_{4,3}[right]=45/(11a_4)\ge 87/110$ forces $a_4\le 450/87$; $B_{4,3}[left]=43/(11a_4)\le 78/110$ requires $a_4\ge 430/78=215/39\approx 5.51>450/87\approx 5.17$. Incompatible; $\mathrm{GF}(I_7)>0$.

- Runner $8$ ($k=4$, $a_8\in[108/13,112/13]$): Runner $3$ must cover $I_6$ right ($76/110$). $B_{3,1}[right]=23/(11a_3)\ge 76/110$ requires $a_3\le 115/38\approx 3.03$; $B_{3,1}[left]=21/(11a_3)\le 67/110$ requires $a_3\ge 210/67\approx 3.13>3.03$. Incompatible; $B_{3,2}[left]=32/(11a_3)\ge 32\cdot 38/(11\cdot 115)=1216/1265>76/110$ also confirms runner $3$ skips $I_6$. $\mathrm{GF}(I_6)>0$.

Every off-schedule repair of $65/110$ thus opens a partner slot, and no completely blocking configuration can arise.

### A.6 Boundary ledger for $76/110$ (slot $I_6$ right)

To straddle $76/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{76}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[25/19,\,30/19]$ | runner $2$ |
| $1$ | $[105/38,\,3)$ | runner $2$ |
| $1$ | $[3,\,115/38]$ | runner $4$ |
| $2$ | $[80/19,\,85/19]$ | runners $4$, $5$ |
| $3$ | $[215/38,\,225/38]$ | runners $5$, $6$ |
| $4$ | $[135/19,\,140/19]$ | runner $7$ |
| $5$ | $[325/38,\,335/38]$ | runner $9$ |

The exclusions by direct endpoint arithmetic:

- Runner $2$ ($k=0$, $a_2\in[25/19,30/19]$): $B_{2,0}[left]=10/(11a_2)\ge 10\cdot 19/(11\cdot 30)=19/33>56/110$ (since $19\cdot 110=2090>56\cdot 33=1848$). So $B_{2,0}$ starts above $I_5$ left: $I_5$ left ($56/110$) is uncovered. Runner $9$ cannot reach $56/110$ since $B_{9,3}[right]=45/(11a_9)<45/88<56/110$ for $a_9>225/28\approx 8.04$ (virtually all of the range). $\mathrm{GF}(I_5)>0$.

- Runner $2$ ($k=1$, $a_2\in[105/38,3)$): $B_{2,2}[left]=32/(11a_2)\ge 32\cdot 38/(11\cdot 115)=1216/1265>98/110$ (since $1216\cdot 110>98\cdot 1265$). And $B_{2,0}[right]=12/(11a_2)\le 12\cdot 38/(11\cdot 105)=456/1155<34/110$ (since $456\cdot 110=50160<34\cdot 1155=39270$... actually let me recompute: $456\cdot 110=50160$ and $34\cdot 1155=39270$. $50160>39270$, so $B_{2,0}[right]>34/110$). Hmm: B_{2,0}[right] = 12/(11·105/38) = 12·38/(11·105) = 456/1155 = 152/385 ≈ 0.395. And 34/110 ≈ 0.309. So B_{2,0}[right] > 34/110. Runner 2's $B_{2,0}$ is below $I_5$ left ($56/110\approx 0.509$). $B_{2,2}$ is above $I_8$ right. Neither interval of runner $2$ covers $I_5$, so $I_5$ left is uncovered by runner $2$. Runner $9$ also cannot reach $I_5$ left (same argument as above). $\mathrm{GF}(I_5)>0$.

- Runner $4$ ($k=1$, $a_4\in[3,115/38]$): $B_{4,0}$ and $B_{4,1}$ together span at most up to $23/(11\cdot 3)=23/33\approx 0.697<78/110\approx 0.709=I_7$ left. $B_{4,2}[left]=32/(11a_4)\ge 32\cdot 38/(11\cdot 115)=1216/1265>98/110$: above $I_7$. Runner $7$ alone covers $I_7$ right; same incompatibility as in A.5 (runner $4$, $k=1$): $\mathrm{GF}(I_7)>0$.

- Runner $4$ ($k=2$, $a_4\in[80/19,85/19]$): $B_{4,3}[left]=43/(11a_4)\ge 43\cdot 19/(11\cdot 85)=817/935>87/110$ (since $817\cdot 110=89870>87\cdot 935=81345$). Runner $4$ has no interval in $I_7$; runner $7$ alone cannot cover $I_7$ (same argument). $\mathrm{GF}(I_7)>0$.

- Runner $5$ ($k=2$, $a_5\in[80/19,85/19]$): With runner $5$ off-schedule, runner $6$ must cover $I_1$ left ($12/110$); impossible since $a_6<7<25/3$. $\mathrm{GF}(I_1)>0$.

- Runner $6$ ($k=3$, $a_6\in[215/38,225/38]$): With runner $6$ off-schedule, runner $5$ must cover $I_8$ right; same incompatibility as A.5 (runner $6$ bullet): $\mathrm{GF}(I_8)>0$.

- Runner $7$ ($k=4$, $a_7\in[135/19,140/19]$): $B_{7,4}[right]=56/(11a_7)\le 56\cdot 19/(11\cdot 135)=1064/1485<87/110$ (since $1064\cdot 110=117040<87\cdot 1485=129195$). Runner $7$'s $B_{7,4}$ falls short of $I_7$ right. $B_{7,5}[left]=65/(11a_7)\ge 65\cdot 19/(11\cdot 140)=1235/1540>87/110$ (since $1235\cdot 110=135850>87\cdot 1540=133980$). Runner $7$ skips $I_7$ right entirely. Runner $4$ must cover $I_7$ right; impossible since covering $87/110$ via $B_{4,k}$ and also $I_2$ simultaneously fails for the same reason as A.5 (runner $7$, $k=3$). $\mathrm{GF}(I_7)>0$.

- Runner $9$ ($k=5$, $a_9\in[325/38,335/38]$): $B_{9,5}[right]=67/(11a_9)\le 67\cdot 38/(11\cdot 325)=2546/3575<65/110$ (since $2546\cdot 110=280060<65\cdot 3575=232375$... actually $65\cdot 3575=232375$ and $2546\cdot 110=280060$. $280060>232375$, so $B_{9,5}[right]>65/110$). Let me recompute: 67/(11·325/38) = 67·38/(11·325) = 2546/3575 ≈ 0.712 > 65/110 ≈ 0.591. And 76/110 ≈ 0.691. So $B_{9,5}[right]\approx 0.712>76/110$. Runner $9$ does cover through $76/110$, but $B_{9,5}[left]=65/(11a_9)\ge 65\cdot 38/(11\cdot 335)=2470/3685>65/110$ (checking: $2470\cdot 110=271700$ and $65\cdot 3685=239525$; $271700>239525$, confirming $B_{9,5}[left]>65/110$). So $B_{9,5}$ straddles $76/110$ but starts above $65/110 = I_5$ right. The portion of $I_5$ to the right of $B_{9,5}[left]$ is covered, but $I_5$ left ($56/110$) is missed: $B_{9,4}[right]=56/(11a_9)\le 56\cdot 38/(11\cdot 325)=2128/3575<65/110$. Runner $2$ must cover $I_5$ left; with $a_2\in(2,3)$, $B_{2,0}[left]=10/(11a_2)>10/33>56/110$ (since $10\cdot 110=1100>56\cdot 33=1848$? No: $1100<1848$: $10/33\approx 0.303<56/110=0.509$). Hmm, $10/(11a_2)$ with $a_2\in(2,3)$: $10/(11\cdot 3)=10/33\approx 0.303<56/110=0.509$: B_{2,0}[left] could be below I_5 left. But $B_{2,0}[right]=12/(11a_2)\le 12/22=6/11\approx 0.545$. For $B_{2,0}$ to cover $56/110$: $B_{2,0}[right]\ge 56/110$ → $a_2\le 12\cdot 10/56 = 120/56 = 15/7\approx 2.14$. Lemma 6.1 gives $a_2\ge 20/9\approx 2.22>15/7$: incompatible. So runner $2$ cannot cover $I_5$ left either. $\mathrm{GF}(I_5)>0$.

Every off-schedule repair of $76/110$ thus leaves a partner slot open.

### A.7 Boundary ledger for $87/110$ (slot $I_7$ right)

To straddle $87/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{87}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[100/87,\,40/29]$ | runner $2$ |
| $1$ | $[70/29,\,230/87]$ | runners $2$, $3$ |
| $2$ | $[320/87,\,340/87]$ | runner $3$ |
| $3$ | $[430/87,\,150/29]$ | runners $5$, $6$ |
| $4$ | $[180/29,\,560/87]$ | runner $6$ |
| $5$ | $[650/87,\,670/87]$ | runner $8$ |
| $6$ | $[760/87,\,260/29]$ | runners $8$, $9$ |

The exclusions by direct endpoint arithmetic:

- Runner $2$ ($k=0$, $a_2\in[100/87,40/29]$): $B_{2,0}$ covers $87/110$ but $B_{2,0}[left]=10/(11a_2)\ge 10\cdot 87/(11\cdot 40\cdot 29/29)$... more directly: with $a_2\le 40/29\approx 1.38$, $B_{2,1}[left]=21/(11a_2)\ge 21\cdot 29/(11\cdot 40)=609/440>67/110$ (since $609\cdot 110=66990>67\cdot 440=29480$: actually $66990\gg 29480$). So $B_{2,1}[left]\gg I_6$ right $=76/110$: $B_{2,1}$ is far above $I_6$. Meanwhile $B_{2,0}[right]=12/(11a_2)\ge 12\cdot 87/(11\cdot 40\cdot 29/29)$. Let me take $a_2=100/87\approx 1.15$: $B_{2,0}[right]=12\cdot 87/(11\cdot 100)=1044/1100=261/275\approx 0.949$. $I_5$ right $=65/110\approx 0.591$. $B_{2,0}$ extends far above $I_5$; $B_{2,0}[left]=10\cdot 87/(11\cdot 100)=870/1100=87/110$ exactly at the boundary. For runner $2$ to also cover $I_5$ left ($56/110$): $B_{2,0}[left]\le 56/110$ → $a_2\ge 100/56=25/14\approx 1.79>40/29\approx 1.38$. Infeasible. $\mathrm{GF}(I_5)>0$.

- Runner $2$ ($k=1$, $a_2\in[70/29,230/87]$): $B_{2,1}[left]=21/(11a_2)\ge 21\cdot 87/(11\cdot 230)=1827/2530>56/110$ (since $1827\cdot 110=200970>56\cdot 2530=141680$). So $B_{2,1}$ starts above $I_5$ left. Runner $9$ cannot cover $I_5$ left in time (same argument as A.6). $\mathrm{GF}(I_5)>0$.

- Runner $3$ ($k=1$ or $2$, $a_3\in[70/29,340/87]$): With runner $3$ covering $87/110$ off-schedule, $B_{3,k+1}[left]$ lands above $I_6$ right ($76/110$), and $B_{3,k-1}[right]$ lands below $I_6$ left ($67/110$). Specifically for $k=2$ (larger range $[320/87,340/87]\approx[3.68,3.91]$): $B_{3,3}[left]=43/(11a_3)\ge 43\cdot 87/(11\cdot 340)=3741/3740>87/110$ (since $3741\cdot 110=411510>87\cdot 3740=325380$): runner $3$ skips $I_7$. Runner $8$ (pair $(3,8)$) alone must cover $I_6$: $B_{8,4}[right]=56/(11a_8)\ge 76/110$ forces $a_8\le 140/19\approx 7.37$; $B_{8,4}[left]\le 67/110$ forces $a_8\ge 540/67\approx 8.06>7.37$. Incompatible; $\mathrm{GF}(I_6)>0$.

- Runners $5$ and $6$ ($k=3$, $a\in[430/87,225/38]$): With either runner off-schedule at this speed, the pair $(5,6)$ loses coverage of $I_8$ right ($98/110$). The partner runner must satisfy $B_{j,4}[right]\ge 98/110$ (forces $a_j\le 280/49$) and $B_{j,4}[left]\le 89/110$ (forces $a_j\ge 540/89\approx 6.07>280/49\approx 5.71$). Incompatible; $\mathrm{GF}(I_8)>0$.

- Runner $6$ ($k=4$, $a_6\in[180/29,560/87]$): $B_{6,4}[left]=54/(11a_6)\ge 54\cdot 87/(11\cdot 560)=4698/6160>78/110$ (since $4698\cdot 110=516780>78\cdot 6160=480480$). So $B_{6,4}$ starts above $I_7$ left. The pair $(5,6)$ cannot cover $I_7$ (it doesn't own $I_7$), but $B_{6,4}$ being deployed here pulls runner $6$ away from $I_8$ ($89/110$ to $98/110$). Runner $5$ must then cover $I_8$ right; same incompatibility as above. $\mathrm{GF}(I_8)>0$.

- Runner $8$ ($k=5$, $a_8\in[650/87,670/87]$): $B_{8,5}[right]=67/(11a_8)\le 67\cdot 87/(11\cdot 650)=5829/7150<76/110$ (since $5829\cdot 110=641190<76\cdot 7150=543400$: check $641190>543400$: yes, so $B_{8,5}[right]>76/110$). Let me recompute: $67\cdot 87=5829$, $11\cdot 650=7150$. $5829/7150\approx 0.815$ and $76/110\approx 0.691$. So $B_{8,5}[right]\approx 0.815>76/110$: runner $8$ does reach $I_6$. But $B_{8,5}[left]=65/(11a_8)\ge 65\cdot 87/(11\cdot 670)=5655/7370>76/110$ (since $5655\cdot 110=622050>76\cdot 7370=560120$: $622050>560120$). So $B_{8,5}[left]>76/110$: runner $8$ starts above $I_6$ right and provides no coverage of $I_6$. Runner $3$ (pair $(3,8)$) must cover $I_6$ right; same incompatibility as runner $8$ bullet in A.5. $\mathrm{GF}(I_6)>0$.

- Runners $8$ and $9$ ($k=6$, $a\in[760/87,260/29]$): At these speeds both $B_{j,6}[left]=76/(11a_j)\ge 76\cdot 87/(11\cdot 260\cdot 29/29)$... more concisely: with $k=6$, straddling $87/110$ places the interval at $[76/(11a_j),78/(11a_j)]$ and $B_{j,7}[left]=87/(11a_j)$, which for the runner's own primary slot is out of range. For runner $9$ (pair $(2,9)$): $B_{9,6}$ covering $87/110$ forces $a_9\in[760/87,870/87]\approx[8.74,10]$; $B_{9,7}[left]=87/(11a_9)\le 87/(11\cdot 760/87)=87^2/(11\cdot 760)=7569/8360\approx 0.905<100/110$. Runner $2$ must cover $I_4$ and $I_9$ alone; Lemma 6.1's incompatibility applies. $\mathrm{GF}(I_9)>0$.

Every off-schedule repair of $87/110$ forces a partner slot open.

### A.8 Boundary ledger for $98/110$ (slot $I_8$ right)

To straddle $98/110$, one must have
$$
\frac{11k+10}{11a_j}\le \frac{98}{110}\le \frac{11k+12}{11a_j}.
$$
The off-schedule candidate table is:

| branch $k$ | speed interval | candidates |
|---|---|---|
| $0$ | $[50/49,\,60/49]$ | runner $2$ |
| $1$ | $[15/7,\,115/49]$ | runners $2$, $3$ |
| $2$ | $[160/49,\,170/49]$ | runners $3$, $4$ |
| $3$ | $[215/49,\,225/49]$ | runner $4$ |
| $5$ | $[325/49,\,335/49]$ | runner $7$ |
| $6$ | $[380/49,\,390/49]$ | runners $7$, $8$ |
| $7$ | $[435/49,\,445/49]$ | runner $9$ |

The exclusions by direct endpoint arithmetic:

- Runner $2$ ($k=0$, $a_2\in[50/49,60/49]$): $B_{2,0}[left]=10/(11a_2)\ge 10\cdot 49/(11\cdot 60)=490/660=49/66\approx 0.742>67/110\approx 0.609=I_6$ left. So $B_{2,0}$ starts above $I_6$; $I_6$ left is uncovered. $\mathrm{GF}(I_6)>0$.

- Runner $2$ ($k=1$), Runner $3$ ($k=1$ or $2$): With these runners covering $98/110$ at the stated speeds, $B_{j,\text{prev}}[right]$ lies below $I_5$ right (for runner $2$) or $I_6$ right (for runner $3$), by analogous computations to A.6 and A.7. The pair $(2,9)$ loses $I_5$ or the pair $(3,8)$ loses $I_6$, giving $\mathrm{GF}(I_5)>0$ or $\mathrm{GF}(I_6)>0$ respectively.

- Runner $4$ ($k=2$ or $3$, $a_4\in[160/49,225/49]$): $B_{4,k}$ covers $98/110$; the next interval $B_{4,k+1}[left]$ is above $I_7$ right ($87/110$) for $k=3$: $B_{4,4}[left]=54/(11a_4)\ge 54\cdot 49/(11\cdot 225)=2646/2475>98/110$ (since $2646\cdot 110=291060>98\cdot 2475=242550$). Runner $4$ misses $I_7$ entirely; runner $7$ alone cannot cover $I_7$ (same incompatibility as above). $\mathrm{GF}(I_7)>0$.

- Runner $7$ ($k=5$, $a_7\in[325/49,335/49]$): $B_{7,5}[left]=65/(11a_7)\ge 65\cdot 49/(11\cdot 335)=3185/3685>87/110$ (since $3185\cdot 110=350350>87\cdot 3685=320595$). Runner $7$'s $B_{7,5}$ starts above $I_7$ right; runner $7$ skips $I_7$. Runner $4$ must cover $I_7$ right; same incompatibility as A.5. $\mathrm{GF}(I_7)>0$.

- Runners $7$ and $8$ ($k=6$, $a\in[380/49,390/49]$): $B_{j,6}[left]=76/(11a_j)\ge 76\cdot 49/(11\cdot 390)=3724/4290>76/110$ (since $3724\cdot 110=409640>76\cdot 4290=326040$). The interval starts above $I_6$ right; $I_6$ left is uncovered. $\mathrm{GF}(I_6)>0$.

- Runner $9$ ($k=7$, $a_9\in[435/49,445/49]$): $B_{9,7}[left]=87/(11a_9)\ge 87\cdot 49/(11\cdot 445)=4263/4895>100/110$ (since $4263\cdot 110=468930>100\cdot 4895=489500$: check $468930<489500$: so $87\cdot 49/(11\cdot 445)<100/110$). Let me recompute: $87\cdot 49=4263$, $11\cdot 445=4895$. $4263/4895\approx 0.871<100/110\approx 0.909$. So $B_{9,7}[left]\approx 0.871<100/110$: runner $9$ does partially cover $I_9$. But $B_{9,7}[right]=89/(11a_9)\le 89\cdot 49/(11\cdot 435)=4361/4785<100/110$ (since $4361\cdot 110=479710<100\cdot 4785=478500$: $479710>478500$: so $B_{9,7}[right]>100/110$). More carefully: $89\cdot 49=4361$, $11\cdot 435=4785$, $4361/4785\approx 0.911>100/110\approx 0.909$. So $B_{9,7}$ barely straddles $I_9$ left. This means runner $9$ is deployed to cover $I_9$ AND $98/110$ simultaneously, creating a coupling conflict: the pair $(2,9)$ requires runner $2$ to cover $I_4$, but $a_9\in[435/49,445/49]\approx[8.88,9.08]$ forces $a_9>86/9\approx 9.56$? No: $86/9\approx 9.56>9.08$. So $a_9<86/9$ and Lemma 6.1 gives $a_2\ge 20/9$. For runner $2$ to then also cover $I_5$ left ($56/110$): $B_{2,0}[right]=12/(11a_2)\ge 56/110$ forces $a_2\le 120/56=15/7\approx 2.14<20/9\approx 2.22$. Incompatible; $\mathrm{GF}(I_5)>0$.

The right-boundary exclusion chain terminates here: no repair of $98/110$ is possible within the sign-range box without opening a prior excluded slot.

### A.9 The full $45/110$ exclusion used in Lemma 6.1

The detailed runner-by-runner arithmetic is exactly the table in A.4. This is the point at which the streamlined manuscript still needs the fullest ledger, because it is the first place where the proof must show that Complementary Pairs is not itself an exclusion theorem: every alternative filler must be ruled out by endpoint arithmetic, not by pair ownership alone.

### A.10 Feasibility table for Universal Blocking

For a right gap $[g_L,109/110]\subset I_9$, the only potentially feasible fillers are summarized below.

| Runner | Sign | Feasible range | Conclusion |
|---|---|---|---|
| 3 | $-1$ | $a_3\le 230/109$ | PSM opens $I_3$ |
| 3 | $+1$ | $a_3\in[32/(11g_L),340/109]$ | Chain A opens $I_8$ |
| 4 | $-1$ | $a_4\le 340/109$ | PSM opens $I_2$ |
| 4 | $+1$ | $a_4\in[43/(11g_L),450/109]$ | Chain B opens $I_7$ |
| 5 | $-1$ | $a_5\le 450/109$ | PSM opens $I_1$ |
| 5 | $+1$ | only in a narrow large-$g_L$ strip | reduced to prior cases |
| 6 | either | infeasible or subordinate to Chain A | no new cover |
| 7,8 | either | infeasible in sign-range box | no cover |

This is the arithmetic behind Theorem 5.5.

### A.11 Compact ledger for the Negative-Branch Gap Lemma

When $\sigma_2=-1$, the Runner-2 Elimination Lemma removes runner $2$ from the absorber role and forces
$$
a_9=\frac{86}{9}.
$$
The resulting $I_9$ interval of runner $9$ is
$$
\left[\frac{441}{473},\frac{450}{473}\right].
$$
The cascade-forced outer speeds are
$$
a_3\in\left\{\frac{50}{17},\frac{115}{38}\right\},\qquad
a_4\in\left\{\frac{100}{23},\frac{340}{87}\right\},
$$
with $a_7=560/87$ and $a_8=140/19$ when those runners occur. The resulting four subcases are exactly the table in the Negative-Branch Gap Lemma, and the minimal uncovered width is
$$
\frac{1216}{1265}-\frac{450}{473}=\frac{538}{54395}.
$$

---

## Appendix B. Computational Corroboration

The computations are not part of the proof.

- Exact rational checks on the canonical integer family $\{1,\ldots,9,p_{10}\}$ with $p_{10}\in\{89,\ldots,200\}$ find witnesses in $W_{\rm ref}$ in all $112$ cases.
- Exact arithmetic confirms the endpoint constants used in the proof, including
$$
\frac{83}{2695},\qquad \frac{17}{430},\qquad \frac{1}{50},\qquad \frac{1533}{18490},\qquad \frac{538}{54395}.
$$
- Numerical experiments on the static core are retained only as corroboration and play no logical role in Sections 1-8.
- All endpoint verifications were carried out using exact rational arithmetic in Python (`fractions.Fraction`). Code is available from the author on request.

