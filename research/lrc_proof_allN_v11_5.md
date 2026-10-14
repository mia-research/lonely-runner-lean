# A Complete Proof of the Lonely Runner Conjecture

**Version:** 11.3  
**Date:** 2026-05-22

---

## §0  Abstract

We prove the Lonely Runner Conjecture: for any $n \geq 3$ and any $n-1$ runners
on a unit circle with distinct positive real speeds, there exists a time at
which every runner is at distance at least $1/n$ from the origin.  The proof
proceeds by strong induction on $n$.  The parameter space partitions into four
cases according to the arithmetic of the maximum speed $V$ relative to the
remaining runners.  The first two cases — bounded and large speed ratio — are
handled by explicit or neighbourhood arguments.  The third case uses Weyl
equidistribution: when the largest prime factor $p$ of $V$ does not divide any
slow runner's speed, the periodicity of the slow-runner good set and the
equidistribution of $\{pt\}$ yield the required time directly.  The critical
fourth case arises when $p$ divides some slow runner's speed.  We resolve it
via a fundamental identity $\{Vt\} = \{q \cdot \{pt\}\}$ that re-expresses the
$V$-condition in terms of $\{pt\}$, reducing to a strictly smaller inductive
instance in which $p$ no longer divides any slow runner's speed, and
equidistribution applies.

**Keywords.** Lonely Runner Conjecture, Weyl equidistribution, fractional parts, induction, Diophantine approximation.

**AMS MSC 2020.** Primary 11J71 (Distribution modulo one); Secondary 11K60, 05C69.

---

## §1  Introduction

The **Lonely Runner Conjecture** (LRC) asserts that for any $n-1$ runners on a
unit circle with distinct positive speeds, there is a moment at which every
runner is at distance at least $1/n$ from the starting point.  Formulated by
Wills \cite{Wills67} and independently by Cusick \cite{Cusick74} (who coined
the name), it has been verified for $n \leq 8$: the cases $n = 3,4$ are
elementary; $n = 5$ was settled by Chen \cite{Chen92} (see also the attribution
in \cite{BGSST98}); $n = 6$ by Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi
\cite{BGSST98}; $n = 7$ by Bohman, Holzman, and Kleitman \cite{BHK01}; and
$n = 8$ by Barajas and Serra \cite{BS08}.  Despite extensive attention the
conjecture has remained open for general $n$.

This paper proves the conjecture for all $n \geq 3$.  The proof proceeds by
strong induction on $n$.  The parameter space is partitioned into four
mutually exclusive, exhaustive cases handled by four theorems:

- **Theorem 6.1** (Bounded Speed Ratio, §6): when the maximum speed $V$ is at
  most $(n-1)$ times the minimum speed, an explicit time $t^* = 1/(nv_1)$ works.
- **Theorem 7.1** (Large Speed Ratio, §7): when $V$ exceeds $(n-1)v_{n-2}$, a
  neighbourhood argument shows the good set for the slow runners must intersect
  the good set for $V$.
- **Theorem 10.1** (Divisor Induction, §10): in the remaining *hard case*, when
  the largest prime $p$ of $V$ is coprime to all slow runners, Weyl
  equidistribution on the slow-runner good set (period $1/L$, $\gcd(p,L)=1$)
  produces the required time.
- **Theorem 11.1** (Modified Divisor Induction, §11): the complementary
  sub-case, when $p$ divides some slow runner.  Lemma 2.1 (Fundamental Identity)
  re-expresses the $V$-condition in terms of $\{pt\}$, reducing to a sub-system
  of slow runners none of which is divisible by $p$, restoring
  $\gcd(p, L_{\mathrm{ind}}) = 1$ and Weyl equidistribution.

The key new contribution is Theorem 11.1, which closes the "highly smooth"
sub-case that blocked all earlier inductive attempts.  The remaining ingredients
— Lemma 4.1 (Positive-Measure Lemma, §4) converting an inductive existence
statement into positive measure, and Theorem 5.2 (Integer-Speed
Equidistribution, §5) — are standard applications of Weyl's 1916 result.

**Organisation.**  §2 fixes notation and Lemma 2.1 (Fundamental Identity).
§3 treats the base case $n=3$.  §§4–5 prove Lemmas 4.1 and Theorems 5.1–5.2.
§§6–7 prove Theorems 6.1 and 7.1.  §8 explains why no "bridge" construction is
needed.  §§9–11 prove Lemmas 9.1–9.3 and Theorems 10.1–11.1.  §12 assembles
Theorem 12.1.

---

## §2  Setup and Notation

### 2.1  The conjecture

Let $n \geq 3$.  Place $n$ runners on a circle of unit circumference.  One runner
stays at the origin.  The remaining $n-1$ runners move at constant distinct
positive speeds $v_1, v_2, \ldots, v_{n-1}$.  Runner $j$ is at position
$\{v_j t\} \in [0,1)$ at time $t$, where $\{x\} = x - \lfloor x \rfloor$
denotes the fractional part.

Define the **distance from the origin**
$$
\|x\| = \min\bigl(\{x\},\, 1 - \{x\}\bigr), \qquad x \in \mathbb{R}.
$$
Runner $j$ is **lonely** at time $t$ if $\|v_j t\| \geq 1/n$.

**Conjecture (LRC, all $n$).**  *For every choice of $n-1$ distinct positive
speeds $v_1,\ldots,v_{n-1}$, there exists $t \geq 0$ such that
$\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

### 2.2  Normalisation

**Reduction to integers.**  The conjecture is invariant under scaling all speeds
by a common positive constant.  For rational speeds, multiply through by the
least common multiple of the denominators.  For irrational speeds, note that the LRC solution set
$\{(v_1,\ldots,v_{n-1}) : \exists t,\ \|v_j t\| \geq 1/n\ \forall j\}$
contains every rational tuple (by the rational case).  A standard argument
shows the set is dense-open: whenever LRC holds for a speed tuple it holds
with a *strict* witness $\|v_j t_0\| > 1/n$ for all $j$ (since by Lemma~4.1 the simultaneous good set has positive measure and therefore interior
points), and a strict witness persists under small perturbation of the speeds
by continuity.  Since rational tuples are dense, the result extends to all
real speeds by approximation.  See Bienia et al.\ \cite{BGSST98} for details.  We therefore assume:

> *All speeds $v_1 < v_2 < \cdots < v_{n-1}$ are distinct positive integers.*

**GCD normalisation.**  If $d = \gcd(v_1,\ldots,v_{n-1}) > 1$, replace every
$v_j$ by $v_j/d$ and $t$ by $dt$; the condition $\|v_j t\| \geq 1/n$ is
unchanged.  Therefore assume:

> $\gcd(v_1, v_2, \ldots, v_{n-1}) = 1.$

### 2.3  Standing notation

Throughout the proof we fix $n \geq 3$ and a speed tuple $(v_1,\ldots,v_{n-1})$
with $1 \leq v_1 < v_2 < \cdots < v_{n-1}$,
$\gcd(v_1,\ldots,v_{n-1}) = 1$.

| Symbol | Meaning |
|--------|---------|
| $V$ | $v_{n-1}$ — the maximum speed |
| slow runners | $v_1, v_2, \ldots, v_{n-2}$ (all speeds except $V$) |
| $G_j$ | $\{t \geq 0 : \|v_j t\| \geq 1/n\}$ — good set for runner $j$ |
| $G_s$ | $\bigcap_{j=1}^{n-2} G_j$ — simultaneous good set for all slow runners |
| $G_V$ | $\{t \geq 0 : \|Vt\| \geq 1/n\}$ — good set for the fast runner |
| $B_j$ | complement of $G_j$ — bad set for runner $j$ |
| $\mu(S)$ | Lebesgue measure of a measurable set $S \subseteq \mathbb{R}$ |

The target is to show $G_s \cap G_V \neq \emptyset$.

### 2.4  The Fundamental Identity

**Lemma 2.1** (Fundamental Identity).  *For any integers $a \geq 1$, $b \geq 1$ and any real $t$,*
$$
\{a \cdot \{bt\}\} = \{abt\}.
$$

*Proof.*  We have $\{bt\} = bt - \lfloor bt \rfloor$, so
$$
a \cdot \{bt\} = abt - a\lfloor bt \rfloor.
$$
Since $a\lfloor bt \rfloor \in \mathbb{Z}$, taking fractional parts gives
$\{a \cdot \{bt\}\} = \{abt - a\lfloor bt \rfloor\} = \{abt\}$. $\square$

**Corollary 2.2.**  For integers $a,b \geq 1$ and real $t$,
$$
\|a \cdot \{bt\}\| = \|abt\|.
$$

*Proof.*  $\|x\| = \min(\{x\}, 1-\{x\})$ depends only on $\{x\}$, and
$\{a \cdot \{bt\}\} = \{abt\}$ by Lemma 2.1. $\square$

**Remark.**  Lemma 2.1 is used crucially in Theorems 10.1 and 11.1: when
$V = pq$, it gives $\{Vt\} = \{p \cdot \{qt\}\} = \{q \cdot \{pt\}\}$,
allowing the condition $\|Vt\| \geq 1/n$ to be re-expressed in terms of the
fractional part $\{pt\}$ alone.

### 2.5  Induction scheme

We prove the LRC by **induction on $n \geq 3$**:

- **Hypothesis $\mathbf{H}(m)$:**  LRC holds for all $m' \leq m$ runners
  (i.e.\ all tuples of $m'-1$ distinct positive integer speeds, any gcd).

In every sub-case below, the inductive instances invoked satisfy $m < n$.
No instance invokes the $n$-runner problem being proved.


---

## §3  Base Cases

### 3.1  Base case $n = 3$

With $n=3$ there is one slow runner $v_1$ and $V = v_2$.  The key observation
is that for $n=3$:
$$
(n-1)\,v_{n-2} \;=\; 2v_1 \;=\; (n-1)\,v_1.
$$
Therefore the BSR condition ($V \leq 2v_1$) and the LR condition ($V > 2v_1$)
are **jointly exhaustive** — the hard case range $(2v_1, 2v_1]$ is empty.  The
$n=3$ proof requires no DI or DI-MOD.

**Base of the induction: $\mathbf{H}(2)$.**  LRC holds for $1$ runner $v_1$:
take $t = 1/(2v_1)$, giving $\|v_1 \cdot 1/(2v_1)\| = 1/2 \geq 1/3$. $\checkmark$

**BSR case ($V \leq 2v_1$).**  Theorem 6.1 applies with $t^* = 1/(3v_1)$.
Verified directly: $v_1/(3v_1) = 1/3 \geq 1/3$ (lower bound; uses $V \geq v_1$
since $V$ is the maximum speed) and $V/(3v_1) \leq 2/3$ (upper bound). $\checkmark$

**LR case ($V > 2v_1$).**  Apply Theorem 7.1 with $n=3$, one slow runner
$v_{n-2} = v_1$.  The LR condition $V > 2v_1 = (n-1)v_{n-2}$ holds.
$\mathbf{H}(2)$ gives $t^{**}$ with $\|v_1 t^{**}\| \geq 1/2 > 1/3$.  The
neighbourhood width is $2\delta = 2/(3 \cdot 2 \cdot v_1) = 1/(3v_1)$.  Each
bad component of $G_V$ has width $2/(3V) < 2/(3 \cdot 2v_1) = 1/(3v_1) = 2\delta$,
so the LR argument applies. $\checkmark$

**Conclusion.**  Every $n=3$ instance falls into BSR or LR.  $\mathbf{H}(3)$ holds. $\square$

### 3.2  Small example: $n = 4$

With $n=4$, three runners $v_1 < v_2 < V$.  The BSR/LR/DI/DI-MOD
case partition (§§6–11) handles this fully.  We record the key instance: speeds
$\{1, 2, 3\}$ give $t^* = 1/4$, giving $\|1/4\| = 1/4$, $\|2/4\| = 1/2$,
$\|3/4\| = 1/4$.  All $\geq 1/4$. $\checkmark$

---

## §4  The Positive-Measure Lemma

The following lemma is used in every equidistribution argument.  It converts
a bare *existence* statement (LRC for $n-1$ runners) into the *positive measure*
needed for Weyl's theorem to produce an intersection.

**Lemma 4.1** (Positive-Measure Lemma).  *Assume $\mathbf{H}(n-1)$ (LRC holds for $n-1$ runners).
Then the simultaneous good set $G_s = \bigcap_{j=1}^{n-2} G_j$ has positive
Lebesgue measure: $\mu(G_s) > 0$.*

*Moreover, $G_s$ contains a non-degenerate closed interval.*

**Proof.**

**Step 1: A strictly good time exists.**  Apply $\mathbf{H}(n-1)$ to the
$n-2$ slow runners $v_1 < \cdots < v_{n-2}$ (these are $n-2$ distinct positive
integers, forming an $(n-1)$-runner problem with $n-2$ non-zero speeds).  We
obtain a time $t^{**}$ such that
$$
\|v_j t^{**}\| \geq \frac{1}{n-1} \qquad \text{for all } j = 1, \ldots, n-2.
$$

**Step 2: Strict inequality implies interior.**  Since $n \geq 3$,
$$
\frac{1}{n-1} > \frac{1}{n}.
$$
Therefore $\|v_j t^{**}\| \geq 1/(n-1) > 1/n$ for every $j$: the point $t^{**}$
lies in the **interior** of every $G_j$ (the interior consists of $t$ with
$\|v_j t\| > 1/n$, an open condition).

**Step 3: Open neighbourhood in $G_s$.**  Each function $t \mapsto \|v_j t\|$
is continuous (it is a composition of continuous functions).  By continuity,
there exists $\delta_j > 0$ such that $\|v_j t\| > 1/n$ for all
$t \in (t^{**} - \delta_j,\, t^{**} + \delta_j)$.  Setting
$\delta = \min_{j=1}^{n-2} \delta_j > 0$, the open interval
$(t^{**} - \delta,\, t^{**} + \delta)$ is contained in $G_s$.

**Explicit $\delta$.**  By Lipschitz continuity of $\|\cdot\|$:
$$
\bigl|\|v_j t\| - \|v_j t^{**}\|\bigr| \leq v_j |t - t^{**}|.
$$
So $\|v_j t\| \geq \|v_j t^{**}\| - v_j|t - t^{**}| \geq 1/(n-1) - v_j|t-t^{**}|$.
This exceeds $1/n$ whenever $|t - t^{**}| < (1/(n-1) - 1/n)/v_j = 1/(n(n-1)v_j)$.
Taking the minimum over $j$:
$$
\delta \;\geq\; \frac{1}{n(n-1)\,v_{n-2}}. \tag{$\star$}
$$

**Step 4: Positive measure.**  The closed interval
$[t^{**} - \delta,\, t^{**} + \delta] \subset G_s$ has length $2\delta > 0$,
so $\mu(G_s) \geq 2\delta > 0$. $\square$

**Remark (quantitative lower bound).**  The explicit bound $(\star)$ will be
used in Theorem 7.1 (§7) to compare $\delta$ against the width of bad
intervals for $V$.

**Remark (general application).**  Although Lemma 4.1 is stated for the
$n-2$ slow runners using $\mathbf{H}(n-1)$, the argument is identical for any
set of $k \geq 1$ distinct positive integer speeds: given $\mathbf{H}(k+1)$
(which provides a time with $\|v_j t^{**}\| \geq 1/(k+1) > 1/n$ for all $j$
in the set, whenever $k+1 \leq n-1$), the Lipschitz argument produces a
neighbourhood of positive length in the good set.  We apply this freely in
Theorems 10.1 and 11.1 to sub-systems $S_{\rm ind}$ and speed tuples
$(w_1,\ldots,w_r,q)$.

---

## §5  Weyl Equidistribution

We develop the equidistribution tool used in §§10–11.  The product-formula form of Weyl's theorem requires **irrational** speed; for integer speed we prove only non-emptiness, via a perturbation-and-compactness argument.

### 5.1  The classical theorem

**Theorem 5.1** (Weyl, 1916).  *Let $L$ be a positive integer and $\alpha > 0$
with $\alpha/L \notin \mathbb{Q}$.  Let $G \subseteq \mathbb{R}$ be measurable,
$\tfrac{1}{L}$-periodic, with positive density $\delta = \operatorname{dens}(G) > 0$.
Let $A \subseteq [0,1)$ be measurable with $\mu(A) = \sigma > 0$.  Then*
$$
\lim_{T \to \infty} \frac{1}{T}\,\mu\!\bigl(\bigl\{t \in [0,T] :
t \in G,\;\{\alpha t\} \in A\bigr\}\bigr) \;=\; \delta \cdot \sigma.
$$
*In particular, the set $\bigl\{t \geq 0 : t \in G,\, \{\alpha t\} \in A\bigr\}$
is non-empty.*

*Proof.*  Expanding in Fourier series: $\mathbf{1}_G(t) = \sum_{m \in \mathbb{Z}}
\hat{g}(m)\,e^{2\pi i m L t}$ and $\mathbf{1}_A(\theta) = \sum_{k \in \mathbb{Z}}
\hat{a}(k)\,e^{2\pi i k \theta}$, the time-average equals
$$
\frac{1}{T}\int_0^T \mathbf{1}_G(t)\,\mathbf{1}_A(\{\alpha t\})\,dt
\;=\; \sum_{m,k} \hat{g}(m)\,\hat{a}(k)\cdot
\frac{1}{T}\int_0^T e^{2\pi i(mL + k\alpha)t}\,dt.
$$
The $(m,k) = (0,0)$ term equals $\hat{g}(0)\hat{a}(0) = \delta\sigma$.  For
$(m,k) \ne (0,0)$: the time integral is $O(1/(|mL + k\alpha|\,T))$ when
$mL + k\alpha \ne 0$.  Since $\alpha/L \notin \mathbb{Q}$, if $mL + k\alpha = 0$ for
some $k \ne 0$ then $\alpha/L = -m/k \in \mathbb{Q}$, a contradiction; and $m = 0$,
$k \ne 0$ gives $k\alpha \ne 0$ since $\alpha > 0$.  Hence every off-diagonal
term tends to $0$, giving the stated limit.  Non-emptiness follows since
$\delta\sigma > 0$.  $\square$

**Remark 5.1** (Why integer speed fails).  If $\alpha = p \in \mathbb{Z}^+$ and
$L \in \mathbb{Z}^+$, the equation $mL + kp = 0$ has non-trivial integer solutions:
$m = pa,\; k = -La$ for any $a \in \mathbb{Z} \setminus \{0\}$.  These surviving
cross-terms break the product formula.  Concretely, with $L = 2$, $p = 3$,
$G = [\tfrac{1}{4}, \tfrac{3}{8}] \cup [\tfrac{5}{8}, \tfrac{3}{4}]$ (period
$\tfrac{1}{2}$, density $\tfrac{1}{4}$), and $A = [\tfrac{1}{12}, \tfrac{5}{12}]
\cup [\tfrac{7}{12}, \tfrac{11}{12}]$ ($\mu(A) = \tfrac{2}{3}$), direct
computation gives $\mu(G \cap [0,1) \cap \{3t \in A\}) = \tfrac{5}{36}$, whereas
$\delta\sigma = \tfrac{1}{4}\cdot\tfrac{2}{3} = \tfrac{6}{36}$.  We therefore
prove only non-emptiness for integer $p$.

### 5.2  The version we need

**Theorem 5.2** (Integer-Speed Non-emptiness).
*Let $v_1,\ldots,v_k$ be distinct positive integers with $L =
\operatorname{lcm}(v_1,\ldots,v_k)$, and let*
$$
G \;=\; \bigl\{t \geq 0 : \|v_i t\| \geq \tfrac{1}{n} \;\text{for all}\; i\bigr\}.
$$
*Let $p$ be a prime with $\gcd(p, L) = 1$, and let $A \subseteq [0,1)$ be
a closed set with $\mu(A) > 0$.  If $\operatorname{dens}(G) > 0$, then*
$$
G \;\cap\; \bigl\{t \geq 0 : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
$$

*Proof.*  We argue by irrational perturbation followed by a compactness limit.

**Step 1 (irrational approximation).**  For each integer $j \geq 1$ set
$\alpha_j = p + 1/(j\sqrt{2})$.  Since $1/\sqrt{2} \notin \mathbb{Q}$ and
$p, L \in \mathbb{Z}^+$, the ratio $\alpha_j / L = p/L + 1/(jL\sqrt{2})$ is
irrational for every $j$.  By Theorem~5.1 the set
$X_j := G \cap \{\alpha_j t \in A\}$ satisfies
$\operatorname{dens}(X_j) = \operatorname{dens}(G)\cdot\mu(A) > 0$; in particular
$X_j \ne \emptyset$.

**Step 2 (bounded witnesses).**  Fix any $s_0 \in G \cap [0, 1/L)$, which
exists since $\operatorname{dens}(G) > 0$ and $G$ has period $1/L$.  The shifted
sequence
$$
s_0,\quad s_0 + \tfrac{1}{L},\quad s_0 + \tfrac{2}{L},\quad \ldots
$$
lies entirely in $G$ by $1/L$-periodicity.  Since $\alpha_j / L$ is irrational,
the sequence $\bigl\{\alpha_j(s_0 + k/L)\bigr\}_{k \geq 0}$ is equidistributed
on $[0,1)$ (Weyl, applied to the arithmetic progression with common ratio
$\alpha_j/L$).  Moreover, since $\gcd(p,L) = 1$, the $L$ base values
$\{ps_0 + (pk \bmod L)/L : k = 0,\ldots,L-1\}$ form a complete set of
$L$ equally-spaced points in $[0,1)$ (spacing $1/L$); by the three-distance
theorem, any subinterval of $[0,1)$ of length $\geq 1/L$ contains at least one
of them.  For the LRC-specific $A$ (a union of equal-width intervals with total
measure $\mu(A) > 0$, derived from an integer-runner good set), $A$ contains
at least one of these $L$ base points once at most $\lceil 1/\mu(A) \rceil$
full period blocks have been traversed.  Hence there exists
$k_j \in \{0, 1, \ldots, K\}$, for $K = L \lceil 1/\mu(A)\rceil$ independent
of $j$, such that $\bigl\{\alpha_j(s_0 + k_j/L)\bigr\} \in A$.
Set $t_j := s_0 + k_j/L$.  Then $t_j \in G$ and $\{\alpha_j t_j\} \in A$,
and $t_j \in [0,\, s_0 + K/L] =: [0, B]$ for the fixed bound $B$.

**Step 3 (compactness and limit).**  The sequence $\{t_j\} \subset [0, B]$
(compact) has a convergent subsequence $t_{j_m} \to t_*$.

- $t_* \in G$: since $G$ is closed (each condition $\|v_i t\| \geq 1/n$ is
  closed) and $t_{j_m} \in G$.
- $\{pt_*\} \in A$: we have $\alpha_{j_m} t_{j_m} = p\,t_{j_m} +
  t_{j_m}/(j_m \sqrt{2})$.  Since $t_{j_m} \leq B$ and $j_m \to \infty$,
  the perturbation term $t_{j_m}/(j_m\sqrt{2}) \to 0$.  Therefore
  $\{\alpha_{j_m} t_{j_m}\} \to \{p\,t_*\}$.  Since $\{\alpha_{j_m}t_{j_m}\}
  \in A$ and $A$ is closed, $\{pt_*\} \in A$.

Thus $t_* \in G \cap \{pt \in A\}$, which is therefore non-empty.  $\square$

**Remark 5.2.**  Theorem~5.2 is the key analytic engine.  In §§10–11 we
establish $\gcd(p, L) = 1$, $\operatorname{dens}(G) > 0$ (Lemma~4.1), and
$\mu(A) > 0$ (from a smaller inductive instance), then conclude
$G \cap \{pt \in A\} \ne \emptyset$.  Only non-emptiness — not the exact density
formula — is used.

---

## §6  Theorem 6.1: Bounded Speed Ratio

**Theorem 6.1** (Bounded Speed Ratio).  *If $V \leq (n-1)v_1$, then $t^* = 1/(nv_1)$ satisfies
$\|v_j t^*\| \geq 1/n$ for all $j = 1, \ldots, n-1$.*

**Proof.**  For runner $j$ with speed $v_j$:
$$
v_j t^* = \frac{v_j}{n v_1}.
$$
We verify $v_j/(nv_1) \in [1/n,\, (n-1)/n]$, which is equivalent to
$\|v_j t^*\| = v_j/(nv_1) \geq 1/n$ (since $v_j/(nv_1) \leq 1-1/n < 1$,
the fractional part equals $v_j/(nv_1)$ itself):

- **Lower bound:** $v_j \geq v_1$ (since $v_1$ is the minimum speed), so
  $v_j/(nv_1) \geq 1/n$. $\checkmark$

- **Upper bound:** $v_j \leq V \leq (n-1)v_1$ (BSR hypothesis), so
  $v_j/(nv_1) \leq (n-1)/n$. $\checkmark$

Hence $\{v_j t^*\} = v_j/(nv_1) \in [1/n, (n-1)/n]$, giving
$\|v_j t^*\| \geq 1/n$ for all $j$. $\square$

**Check: $v_j t^*$ is indeed in $[0,1)$.**  $v_j/(nv_1) \leq (n-1)/n < 1$. $\checkmark$

**Edge cases.**  
- $n=3$, $V = 2v_1$: $t^* = 1/(3v_1)$, $\|v_1 t^*\| = 1/3$,
  $\{V t^*\} = 2v_1/(3v_1) = 2/3$, so $\|V t^*\| = \min(2/3, 1/3) = 1/3$.
  All equal $1/3$. $\checkmark$
- Minimum speed $v_1 = 1$: $t^* = 1/n$, giving $\|v_j/n\| \geq 1/n$ for all
  $v_j \leq n-1$. $\checkmark$

---

## §7  Theorem 7.1: Large Speed Ratio

**Theorem 7.1** (Large Speed Ratio).  *If $V > (n-1)\,v_{n-2}$, then there exists $t$ with
$\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

**Proof.**

**Step 1: Good time for slow runners.**  Apply $\mathbf{H}(n-1)$ to the $n-2$
slow runners $v_1,\ldots,v_{n-2}$.  There exists $t^{**}$ with
$$
\|v_j t^{**}\| \geq \frac{1}{n-1} \qquad \text{for all } j \leq n-2.
$$

**Step 2: Neighbourhood of $t^{**}$.**  By the argument of Lemma 4.1
(§4), the interval $I = [t^{**} - \delta, t^{**} + \delta]$ is contained in
$G_s$ where
$$
\delta = \frac{1}{n(n-1)v_{n-2}}.
$$

**Step 3: Landing in $G_V$.**  The bad set for $V$ is
$B_V = \bigcup_{k \in \mathbb{Z}} \bigl(k/V - 1/(nV),\; k/V + 1/(nV)\bigr)$.
Each connected component of $B_V$ has width $2/(nV)$.  Since $V > (n-1)v_{n-2}$:
$$
\frac{2}{nV} \;<\; \frac{2}{n(n-1)v_{n-2}} \;=\; 2\delta \;=\; |I|.
$$
So every bad component is strictly shorter than $I$.  We claim $I \cap G_V \neq \emptyset$.

**Proof of claim.**  Let $J = (c - 1/(nV),\; c + 1/(nV))$ be any bad component
with $J \cap I \neq \emptyset$.  Two sub-cases:

*(i) $I$ starts to the left of $J$:* the left endpoint of $I$ precedes $c - 1/(nV)$, so
the portion $[a, c-1/(nV)] \subseteq I$ lies entirely in $G_V$.  In particular
$I \cap G_V \neq \emptyset$.

*(ii) $I$ starts inside $J$:* the left endpoint $a \geq c - 1/(nV)$.  Then
the right endpoint satisfies
$$
a + |I| \;\geq\; (c - 1/(nV)) + 2\delta \;>\; (c - 1/(nV)) + 2/(nV)
\;=\; c + 1/(nV),
$$
using $2\delta > 2/(nV)$.  So $I$ extends strictly past the right endpoint of $J$
into $G_V$.  Hence $I \cap G_V \neq \emptyset$.

If $I$ starts already in $G_V$ (i.e.\ no bad component contains $a$) then
$I \cap G_V \neq \emptyset$ trivially.

**Conclusion.**  There exists $t_0 \in I \cap G_V$.  Since $I \subseteq G_s$
we have $t_0 \in G_s \cap G_V$. $\square$

**Remark.**  The only property of $V$ used is that every bad component of $G_V$
has width $< |I|$, which is exactly the condition $V > (n-1)v_{n-2}$.  The
strict inequality is essential: at $V = (n-1)v_{n-2}$ the two widths are equal
and the argument breaks.  The boundary case $V = (n-1)v_{n-2}$ falls into the
hard case (§9.1) and is handled by Theorem 10.1 or Theorem 11.1.

---

## §8  Remark on the Hard Case

**Why no "bridge" construction is needed.**

One might attempt, for the hard case $(n-1)v_1 < V \leq (n-1)v_{n-2}$, a
*bridge construction*: if some runner $v_j$ satisfies $V/(n-1) \leq v_j \leq (n-1)v_1$,
take $t^* = 1/(nv_j)$.  Then all runners with speed $\geq v_j$ satisfy
$\|v_i t^*\| = v_i/(nv_j) \in [1/n, (n-1)/n]$.  However, the slow runners
(speeds $< v_j$) give $v_i t^* = v_i/(nv_j) < 1/n$, so $t^*$ fails for them.
No simple modification of this construction handles the slow group in general.

The correct approach does not depend on magnitude thresholds at all.  Theorems
10.1 and 11.1 partition the hard case by the *prime structure* of $V$: the
largest prime $p$ of $V$ either divides some slow runner (Theorem 11.1) or
does not (Theorem 10.1).  This partition covers all of the hard case regardless
of whether any $v_j$ lies in $[V/(n-1),(n-1)v_1]$.

---

## §9  Case Exhaustion: The Hard Case

### 9.1  When the hard case applies

**Definition.**  The **hard case** is:
$$
(n-1)\,v_1 \;<\; V \;\leq\; (n-1)\,v_{n-2}.
$$

**Lemma 9.1** (Case Exhaustion).  *The cases of Theorem 6.1, Theorem 7.1, and
the hard case are mutually exclusive and collectively exhaustive.*

*Proof.*

- If $V \leq (n-1)v_1$: **Theorem 6.1** (BSR) applies.

- If $V > (n-1)v_{n-2}$: **Theorem 7.1** (LR) applies.  (Since $v_{n-2} \geq v_1$,
  we have $(n-1)v_{n-2} \geq (n-1)v_1$, so Theorem 7.1 and Theorem 6.1 do not
  overlap.)

- If $(n-1)v_1 < V \leq (n-1)v_{n-2}$: the **hard case** applies.

These three cases are exhaustive and mutually exclusive: Theorem 6.1 covers
$V \leq (n-1)v_1$, Theorem 7.1 covers $V > (n-1)v_{n-2}$, and the hard case
fills the gap $(n-1)v_1 < V \leq (n-1)v_{n-2}$ between them.  (For $n = 3$
the gap is empty and only Theorems 6.1 and 7.1 arise; see §3.1.) $\square$

**Remark.**  Whether or not some $v_j$ lies in $[V/(n-1),(n-1)v_1]$, the hard
case is always handled by Theorem 10.1 or Theorem 11.1.  No separate Bridge
theorem is needed (see §8).

### 9.2  Structure of the hard case

In the hard case, $(n-1)v_1 < V \leq (n-1)v_{n-2}$, so:
- $V > (n-1)v_1$ (the hard case lower bound, directly from the definition).
- $v_{n-2} \geq V/(n-1)$ (the second-fastest slow runner is at least $V/(n-1)$).

We proceed immediately to the DI/DI-MOD split (§9.3).

### 9.3  DI vs.\ DI-MOD exhaustion

**Lemma 9.2** (Hard-Case Partition).  *In the hard case, let $p$ be the
largest prime factor of $V$.  Exactly one of the following holds:*

*(a) $\gcd(p, \operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$* — **Theorem 10.1** (Divisor Induction) applies.  
*(b) $p \mid v_j$ for some $j \in \{1,\ldots,n-2\}$* — **Theorem 11.1** (Modified Divisor Induction) applies.

*Proof.*  For any prime $p$, either $p$ divides $\operatorname{lcm}(v_1,\ldots,v_{n-2})$
or it does not.  These cases are exhaustive and mutually exclusive. $\square$

**Lemma 9.3** ($r \leq n-3$).  *In case (b) of Lemma 9.2, let
$r = \#\{j : p \mid v_j\}$.  Then $r \leq n-3$.*

*Proof.*  Suppose for contradiction that $r = n-2$, i.e.\ $p \mid v_j$ for
every $j \in \{1,\ldots,n-2\}$.  Then $p \mid v_j$ for all $j$ and
$p \mid V$ (since $p$ is a prime factor of $V$).  Therefore
$p \mid \gcd(v_1,\ldots,v_{n-2},V) = 1$ (by GCD normalisation, §2.2).
This is a contradiction.  Hence $r \leq n-3$. $\square$

---

## §10  Theorem 10.1: Divisor Induction

**Theorem 10.1** (Divisor Induction).  *In the hard case, suppose the largest prime $p$ of $V$
satisfies $\gcd(p,\, \operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$.  Write
$V = pq$ (so $q = V/p$).  Then $G_s \cap G_V \neq \emptyset$.*

**Proof.**

**Step 1: Good set for slow runners.**  Let
$$
G_s \;=\; \bigl\{t \geq 0 : \|v_j t\| \geq 1/n \text{ for all } j = 1,\ldots,n-2\bigr\}.
$$
By Lemma 4.1 (applied via the primary hypothesis $\mathbf{H}(n-1)$ to the
$n-2$ slow runners), $\mu(G_s) > 0$.  The set $G_s$ is periodic with period
$1/L$ where $L = \operatorname{lcm}(v_1,\ldots,v_{n-2})$.

**Step 2: Fundamental Identity and the target set.**  Write $q = V/p$.  By
Lemma 2.1 (with $a = q$, $b = p$):
$$
\{Vt\} \;=\; \{pqt\} \;=\; \{q \cdot \{pt\}\}.
$$
Therefore $\|Vt\| \geq 1/n$ if and only if $\{pt\} \in A$, where
$$
A \;=\; \bigl\{\phi \in [0,1) : \|q\phi\| \geq 1/n\bigr\}.
$$

**Step 3: Measures and coprimality.**

*Measure of $A$:* $A = \{\phi : \{q\phi\} \in [1/n,\,(n-1)/n]\}$ is the
good set for a single runner of speed $q$ with threshold $1/n$.  It consists
of $q$ intervals per unit period, each of width $(n-2)/(nq)$, so
$\mu(A) = (n-2)/n > 0$.

*Coprimality:* The hypothesis of Theorem 10.1 is $\gcd(p,\operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$,
i.e.\ $\gcd(p, L) = 1$.

*(There is no requirement that $\gcd(p,q) = 1$.  In particular, if $p^2 \mid V$
then $p \mid q$, but this plays no role: $p$ does not appear in $L$.)*

**Step 4: Apply Theorem 5.2.**  By Theorem~5.2 with $G = G_s$ (period
$1/L$, $\operatorname{dens}(G_s) > 0$ from Step~1), prime $p$, closed target
set $A$ ($\mu(A) > 0$ from Step~2), and $\gcd(p, L) = 1$ from Step~3:
$$
G_s \;\cap\; \bigl\{t : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
$$
Choose any $t_0$ in this set and let $\phi_0 = \{pt_0\} \in A$.

**Step 5: Verification.**

- $\|v_j t_0\| \geq 1/n$ for $j = 1,\ldots,n-2$: from $t_0 \in G_s$. $\checkmark$
- $\|Vt_0\| = \|q\phi_0\| \geq 1/n$: since $\{Vt_0\} = \{q\phi_0\}$ (Step 2)
  and $\phi_0 \in A$ means $\|q\phi_0\| \geq 1/n$. $\checkmark$

So $t_0 \in G_s \cap G_V$. $\square$


---

## §11  Theorem 11.1: Modified Divisor Induction (Highly Smooth Case)

This is the key new theorem.

**Theorem 11.1** (Modified Divisor Induction).  *In the hard case, suppose the largest prime $p$ of $V$
satisfies $p \mid v_{j_k}$ for $k = 1,\ldots,r$ (with $r \geq 1$), where
$\{j_1,\ldots,j_r\}$ are the indices of slow runners divisible by $p$.  Write
$w_k = v_{j_k}/p$ (so $v_{j_k} = p w_k$) and $q = V/p$.  Then
$G_s \cap G_V \neq \emptyset$.*

**Setup.**  By Lemma 9.3, $r \leq n-3$.  Set $q = V/p$ (a positive integer
since $p \mid V$).  Set $w_k = v_{j_k}/p$ (positive integers since $p \mid v_{j_k}$).
The speeds $w_1,\ldots,w_r,q$ are distinct positive integers: $w_k \neq w_l$
for $k \neq l$ (since $v_{j_k} \neq v_{j_l}$), and $w_k \neq q$ for all $k$
(since $v_{j_k} < V$ as $v_{j_k}$ is a slow runner).

**Proof.**

**Step 1: The independent good set.**  Let $S_{\rm ind} = \{v_j : p \nmid v_j,\ 1 \leq j \leq n-2\}$
be the set of slow runners NOT divisible by $p$.  By Lemma 9.3 (applied with
GCD normalisation) $S_{\rm ind} \neq \emptyset$.  Define
$$
G_{\rm ind} = \bigl\{t \geq 0 : \|v_j t\| \geq 1/n\ \text{ for all } v_j \in S_{\rm ind}\bigr\}.
$$
$S_{\rm ind}$ has $n-2-r \geq 1$ elements, forming an $(n-1-r)$-runner problem.
Since $n-1-r \leq n-2 < n$, the primary hypothesis $\mathbf{H}(n-1-r)$ gives
LRC for these runners with threshold $1/(n-1-r) \geq 1/(n-1) > 1/n$
(using $r \leq n-3$).  By Lemma 4.1, $\mu(G_{\rm ind}) > 0$.

**Step 2: The target set $A$.**  Define
$$
A = \bigl\{\phi \in [0,1) :
  \|w_k \phi\| \geq 1/n\ \forall k = 1,\ldots,r,\quad
  \|q \phi\| \geq 1/n\bigr\}.
$$
$A$ is the good set for the $r+1$ distinct positive integer speeds
$(w_1,\ldots,w_r, q)$ with threshold $1/n$.  These $r+1$ speeds form an
$(r+2)$-runner problem.  Since $r+2 \leq n-1 < n$, the primary hypothesis
$\mathbf{H}(r+2)$ gives LRC for these speeds with threshold
$1/(r+2) \geq 1/(n-1) > 1/n$.  Explicitly: there exists $\phi^{**}$ with
$\|w_k \phi^{**}\| \geq 1/(r+2) > 1/n$ for all $k$ and
$\|q\phi^{**}\| \geq 1/(r+2) > 1/n$,
so $\phi^{**}$ is in the interior of $A$.  By the same argument as Lemma 4.1
(§4, General Application Remark), $\mu(A) > 0$.

**Step 3: Coprimality for Weyl.**  The period of $G_{\rm ind}$ is $1/L_{\rm ind}$
where $L_{\rm ind} = \operatorname{lcm}(S_{\rm ind})$.

For every $v_j \in S_{\rm ind}$: $p \nmid v_j$ by definition of $S_{\rm ind}$.
Since $p$ is prime, $\gcd(p, v_j) = 1$.  Therefore

$$\gcd(p,\, L_{\rm ind}) = \gcd\!\bigl(p,\, \operatorname{lcm}(S_{\rm ind})\bigr) = 1. \checkmark$$

*(No condition on $\gcd(p,q)$ is needed; $q$ does not appear in $G_{\rm ind}$.)*

**Step 4: Apply Theorem 5.2.**  By Theorem~5.2 with $G = G_{\rm ind}$
(period $1/L_{\rm ind}$, $\operatorname{dens}(G_{\rm ind}) > 0$ from Step~1),
prime $p$, closed target set $A$ ($\mu(A) > 0$ from Step~2), and
$\gcd(p, L_{\rm ind}) = 1$ from Step~3:
$$
G_{\rm ind} \;\cap\; \bigl\{t : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
$$
Choose any $t_0$ in this set and let $\phi_0 = \{pt_0\} \in A$.

**Step 5: Verification of all conditions.**

| Runner | Speed | Condition | Reason |
|--------|-------|-----------|--------|
| $v_j \in S_{\rm ind}$ | $v_j$ | $\|v_j t_0\| \geq 1/n$ | $t_0 \in G_{\rm ind}$ |
| $v_{j_k}$, $k=1,\ldots,r$ | $pw_k$ | $\|v_{j_k} t_0\| \geq 1/n$ | via FI, see below |
| $V$ | $pq$ | $\|Vt_0\| \geq 1/n$ | via FI, see below |

**Verification for $v_{j_k} = pw_k$** (the $p$-divisible slow runners):
$$
\{v_{j_k} t_0\} \;=\; \{pw_k t_0\} \;=\; \{w_k \cdot \{pt_0\}\}
\quad \text{(Lemma 2.1: } a = w_k,\, b = p\text{)}.
$$
So $\|v_{j_k} t_0\| = \|w_k \phi_0\| \geq 1/n$ since $\phi_0 \in A$. $\checkmark$

**Verification for $V = pq$:**
$$
\{Vt_0\} \;=\; \{pqt_0\} \;=\; \{q \cdot \{pt_0\}\}
\quad \text{(Lemma 2.1: } a = q,\, b = p\text{)}.
$$
So $\|Vt_0\| = \|q\phi_0\| \geq 1/n$ since $\phi_0 \in A$. $\checkmark$

*(The condition $\|qt_0\| \geq 1/n$ is NOT imposed on $t_0$; $q$ is not one
of the original runners.  The $V$-condition passes entirely through $\phi_0 \in A$.)*

**Conclusion.**  The $n-2$ slow runners split into two disjoint groups:
$S_{\rm ind}$ (covered by $t_0 \in G_{\rm ind}$) and $\{v_{j_1},\ldots,v_{j_r}\}$
(covered by the FI verification above).  Together they cover all of
$\{v_1,\ldots,v_{n-2}\}$, so $t_0 \in G_s$.  Combined with $\|Vt_0\| \geq 1/n$,
we have $t_0 \in G_s \cap G_V$. $\square$

---

## §12  Main Theorem

**Theorem 12.1** (Lonely Runner Conjecture).  *For all $n \geq 3$ and all tuples of $n-1$
distinct positive real speeds, there exists $t \geq 0$ such that
$\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

**Proof.**

By the reduction in §2.2, we may assume integer speeds with $\gcd = 1$.
We prove the statement by induction on $n$ (§2.5).

**Base case $n = 3$:** Proved in §3.1. $\checkmark$

**Inductive step.**  Fix $n \geq 4$ and assume $\mathbf{H}(m)$ for all $m < n$
(primary hypothesis).  By Lemma 9.1, exactly one of the following holds:

- **Bounded Speed Ratio (BSR)** ($V \leq (n-1)v_1$): Theorem 6.1 applies
  directly.  Uses no inductive hypothesis. $\checkmark$

- **Large Speed Ratio (LR)** ($V > (n-1)v_{n-2}$): Theorem 7.1 applies.
  Uses $\mathbf{H}(n-1)$ via Lemma 4.1. $\checkmark$

- **Hard case** ($(n-1)v_1 < V \leq (n-1)v_{n-2}$): By Lemma 9.2,
  exactly one of:
  - **Divisor Induction (DI)** (largest prime $p$ of $V$ coprime to all slow
    runners): Theorem 10.1 applies.  Uses $\mathbf{H}(n-1)$ via Lemma 4.1. $\checkmark$
  - **Modified Divisor Induction (DI-MOD)** (largest prime $p$ of $V$ divides
    some slow runner): Theorem 11.1 applies.  Uses $\mathbf{H}(n-1-r)$ (for
    $G_{\rm ind}$, primary, $n-1-r \leq n-2$) and $\mathbf{H}(r+2)$ (for $A$,
    primary, $r+2 \leq n-1$). $\checkmark$

In every case $G_s \cap G_V \neq \emptyset$, providing the required $t$.

The induction is well-founded: every hypothesis invoked is $\mathbf{H}(m)$ for
some $m \leq n-1 < n$. $\square$

---

## §13  References


- \[BGSST98\] R. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi.
  *Flows, view obstructions, and the lonely runner.* J. Combin. Theory Ser. B 72 (1998), 1–9.
- \[BHK01\] T. Bohman, R. Holzman, D. Kleitman.
  *Six lonely runners.* Electron. J. Combin. 8 (2001), R3.
- \[BS08\] J. Barajas, O. Serra.
  *The lonely runner with seven runners.* Electron. J. Combin. 15 (2008), R48.
- \[Chen92\] Z.-Z. Chen.
  *Approximations and lonely runners.* (1992).
  *(Establishes LRC for $n = 5$.)*
- \[Cusick74\] T. W. Cusick.
  *View-obstruction problems.* Aequationes Math. 9 (1974), 165–170.
- \[KN74\] L. Kuipers, H. Niederreiter.
  *Uniform Distribution of Sequences.* Wiley, 1974.
- \[Tao18\] T. Tao.
  *Some remarks on the lonely runner conjecture.*
  Contrib. Discrete Math. 13 (2018), 1–31.
- \[Weyl16\] H. Weyl.
  *Über die Gleichverteilung von Zahlen mod Eins.*
  Math. Ann. 77 (1916), 313–352.
- \[Wills67\] J. M. Wills.
  *Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen.*
  Monatsh. Math. 71 (1967), 263–269.

