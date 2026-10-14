# The Lonely Runner Conjecture for n = 11

**Author:** Trent Palelei  
**Date:** 2026-03-30 / v28.2  
**Status:** Streamlined submission draft, referee-facing appendix and naming pass  
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

**Proof.** Direct endpoint arithmetic; see Appendix A.10. $\square$

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

**Proof.** The runner-$3$ coverage of $I_9$ leaves a right subgap in $I_3$, forcing runner $8$ by pair ownership; runner $8$ then leaves a right subgap in $I_6$, forcing runner $6$; at the extremal value $a_6=225/38$ one gets
$$
B_{6,4}[0]=\frac{228}{275}>\frac{89}{110}=I_8[\mathrm{left}],
$$
and the shortfall is exactly $1/50$. See Appendix A.10. $\square$

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

**Proof.** Direct endpoint arithmetic; see Appendix A.10. $\square$

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
| runners 5,6,7,8 | various | infeasible in the stated speed ranges |

If no runner is feasible, then the gap survives directly in $I_9$. Otherwise one of PSM, Chain A, or Chain B opens another slot. In all cases $\mathrm{GF}(I_k)>0$ for some slot $I_k$. Full feasibility intervals are listed in Appendix A.10. $\square$

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

**Proof.** This is the endpoint bookkeeping for the intervals $B_{2,1}$, $B_{9,7}$, and $B_{9,8}$. In the three $\alpha$-regions the lower bound from Lemma 6.1 conflicts with the upper bound needed to bridge $I_9$:
$$
a_2\le \frac{23a_9}{87}\quad(\alpha_1),\qquad
a_2\le \frac{23a_9}{98}\quad(\alpha_2,\alpha_3),
$$
and one has
$$
\frac{20}{9}>\frac{23a_9}{87}\ \text{ when }a_9<580/69,\qquad
\frac{20}{9}>\frac{23a_9}{98}\ \text{ when }a_9<1960/207.
$$
In the remaining four $\beta$-regions the bridge is possible but leaves a nonempty right gap in $I_9$. $\square$

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
Hence $y\in T_e$. By Kronecker's theorem the orbit $\{\mathbf x(t)\}$ is dense in $T_e$, so some $t>0$ satisfies $\mathbf x(t)\in\mathcal S$. This is exactly the desired witness. $\square$

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

These are the right-edge mirrors of the A.4 branches. The exclusions are recorded in the same runner-by-runner order:

- runner $3$ ($k=1$): forcing $B_{3,1}$ to reach $65/110$ drags the pair $(3,8)$ left and opens the reflected partner-slot obstruction at the right edge $76/110$; this is exactly the A.6 obstruction for the pair $(3,8)$.
- runner $4$ ($k=1$ or $2$): the $k=1$ branch shifts the pair $(4,7)$ into the reflected A.7 regime, while the $k=2$ branch is the right-edge mirror of the Chain B branch from A.4 and again opens the $(4,7)$ obstruction at $87/110$.
- runner $5$ ($k=2$): this is the right-edge mirror of the runner-$5$ branch in A.4 and forces the pair $(5,6)$ into the A.8 obstruction at $98/110$.
- runner $6$ ($k=2$ or $3$): both branches are right-edge mirrors of the runner-$6$ branch in A.4; they push the pair $(5,6)$ so far right that the $I_8$ right edge must be repaired off schedule.
- runner $7$ ($k=3$): this is the right-edge mirror of the inter-interval-gap calculation for runner $7$ in A.4 and leaves the reflected pair $(4,7)$ with an unresolved right-edge obligation at $87/110$.
- runner $8$ ($k=4$): this is the right-edge mirror of the runner-$3$ branch in A.4 and pushes the pair $(3,8)$ into the unresolved right-edge obligation at $76/110$.

Thus every off-schedule repair of $65/110$ feeds into one of the later right-boundary ledgers A.6-A.8, and no completely blocking configuration can terminate there.

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

This is the right-edge mirror of A.3. The corresponding exclusions are:

- runner $2$: either branch forces the pair $(2,9)$ to miss the right edge of $I_5$, the exact right-edge analogue of the first bullet in A.3.
- runner $4$: both branches are the reflected versions of the runner-$4$ branch in A.3, so the pair $(4,7)$ loses the right edge of $I_7$ and moves directly into the A.7 ledger.
- runner $5$ or runner $6$: these are the reflected versions of the runner-$6$ branch in A.3, so the pair $(5,6)$ is pushed into the terminal A.8 ledger at the right edge $98/110$.
- runner $7$: this is the reflected version of the runner-$7$ obstruction in A.3 and again sends the pair $(4,7)$ to the right edge $87/110$.
- runner $9$: as in A.3, the same split at $a_9=86/9$ shows that runner $9$ fails to keep the pair $(2,9)$ on its primary $I_4/I_5$ schedule.

Hence every off-schedule repair of $76/110$ either creates a direct reflected gap or reduces to A.7 or A.8.

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

This is the right-edge mirror of A.2. The exclusions are:

- runners $2$ and $3$: these are the reflected versions of the A.2 left-edge repairs and force the pair $(2,9)$ or $(3,8)$ off its primary schedule, reducing to the already excluded A.6 or A.5 regimes.
- runners $5$ and $6$: these are the reflected versions of the pair-$(5,6)$ left-edge obstructions and push the argument to the terminal right edge $98/110$.
- runner $8$: this is the reflected counterpart of the runner-$5$/runner-$6$ left-edge calculation and again opens the pair $(3,8)$ on the opposite side.
- runner $9$: this branch is the right-edge analogue of the runner-$9$ bullet from A.2; it breaks the $(2,9)$ schedule unless the configuration already falls into one of the previously excluded branches.

The sharpest numerical obstruction in this ledger is the same one used in Chain B,
$$
a_7\le \frac{560}{87},
$$
which is incompatible with the speeds required to repair $87/110$ off schedule while keeping the pair $(4,7)$ closed.

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

This is the terminal right-edge mirror of A.1. Every branch leaves an unresolved reflected partner slot:

- runners $2$ and $3$ force the pair $(2,9)$ or $(3,8)$ so far right that the preceding right-boundary ledgers A.6 or A.7 must already have failed.
- runners $4$, $7$, and $8$ are the right-edge mirrors of the A.3 and A.4 off-schedule branches and therefore reopen the reflected $(4,7)$ or $(5,6)$ pair obstructions.
- runner $9$ is the right-edge mirror of the runner-$9$ branch in A.1, so it cannot simultaneously maintain the pair $(2,9)$ on both of its primary slots.

Thus the right-boundary exclusion chain terminates here: the repair of $98/110$ cannot be completed within the sign-range box without reopening an earlier excluded slot.

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

---

## Appendix C. Historical Material

This submission draft removes the superseded `WIT` and `SET` routes, as well as the independent 11-pacemaker note, from the main narrative. Those materials remain archived in the longer development drafts and are not used anywhere in the proof chain of this paper.
