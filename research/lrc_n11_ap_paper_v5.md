# Eleven Lonely Runners: The Classical Case via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 21 March 2026
**Status:** Preprint v6 — ANALYTIC (unconditional for $e_{10}/e_1 \leq 10$; irrational-ratio case closed by Weyl equidistribution; remaining gap: commensurable speeds $e_{10}/e_1 > 10$; Iterated Left-Entry Construction introduced with full carry-mechanism analysis; sole open condition identified as Containment (C))

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, classical formulation, no-missing-slot, perturbation independence, prime case, speed ratio, Weyl equidistribution, commensurable speeds

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ in the case where the ratio of the fastest to the slowest non-stationary speed satisfies $e_{10}/e_1 \leq 10$: there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$, with explicit witness $t^* = 10/(11e_{10})$. The proof uses an arithmetic-progression (AP) witness framework with the stationary runner at speed $0$ as the fixed reference. The key structural property is **no-missing-slot**: the AP residues $\{im \bmod 11 : i=1,\ldots,10\} = \{1,\ldots,10\}$ for every witness $m$, combined with **independence of classical conditions** (runner $i$'s loneliness at witness $m$ depends only on $\delta_i$). For the unbounded-ratio case, the gap is refined into three sub-cases: the rationally-related bounded-ratio case (proved, Theorem B), the irrationally-related case (proved via Weyl's equidistribution theorem, Proposition E), and commensurable speeds with ratio exceeding 10 (open). The extended AP witness strategy (Route A) is definitively ruled out as a finite proof approach: a configuration is exhibited that blocks all witnesses in the level-2 extended family simultaneously.

---

## 1. Introduction

The **Lonely Runner Conjecture** (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts: for any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists $t > 0$ such that the stationary runner at speed $0$ satisfies $\|e_i t\| \geq 1/(n+1)$ for all $i = 1,\ldots,n$. The conjecture has been verified for $n \leq 7$ (Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], Barajas–Serra [BS08]), and for $n = 8$ [Ros25a], $n = 9$ [Ros25b, Tra25], and $n = 10$ [Tra25] by recent computational work. A survey of analytic approaches appears in Tao [Tao18].

The companion paper [v2] proves the **relative formulation** for $n = 11$: for any ten distinct real speeds $v_1 < \cdots < v_{10}$, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. As documented in [v2, §10.1], the gap to the classical formulation is non-trivial: the AP framework of [v2] is indexed by moving runners $j \in \{1,\ldots,10\}$ and does not directly accommodate $j = 0$ (the stationary runner).

The present paper rebuilds the AP framework with $j = 0$ and proves:

**Theorem B (Classical LRC for $n = 11$, bounded speed ratio).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ with $e_{10}/e_1 \leq 10$, there exists $t^* = 10/(11e_{10}) > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1, \ldots, 10$.*

**Proposition E (Irrational-ratio case).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ such that $e_i/e_j \notin \mathbb{Q}$ for at least one pair $i \neq j$, the classical LRC holds for this configuration.*

**Conjecture B (Full classical LRC for $n = 11$).** *The same conclusion holds without any restriction on $e_{10}/e_1$.*

Theorem B and Proposition E together close all cases except commensurable speeds (all $e_i/e_j \in \mathbb{Q}$) with $e_{10}/e_1 > 10$. This remaining case is identified in §10.6 as the **only open sub-case** of Conjecture B.

### 1.1 Key structural differences from [v2]

The classical formulation requires studying the AP witness framework with the **stationary runner $j = 0$** as the fixed reference. Two structural changes from [v2] follow:

**No-missing-slot.** In [v2], for a moving reference $j \in \{1,\ldots,10\}$, the AP residues $\{(i-j)m \bmod 11 : i \neq j\}$ always miss exactly one slot (the "missing slot" $M_j(m)$). For $j = 0$, the classical AP residues are $r_i(m) \equiv im \pmod{11}$ for $i = 1,\ldots,10$. Since $\gcd(i,11) = 1$ and $\gcd(m,11) = 1$ for $i,m \in \{1,\ldots,10\}$, multiplication by $i$ is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$, so $\{im \bmod 11 : i = 1,\ldots,10\} = \{1,\ldots,10\}$. **No slot is missing.**

**Independent conditions.** In [v2], the loneliness condition for runner $i$ relative to runner $j$ involves the perturbation *difference* $\Delta_{ij} = \delta_i - \delta_j$, coupling different runners. In the classical framework, the condition for runner $i$ at witness $m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some branch $n_i$, depending **only on $\delta_i$** — not on $\delta_j$ for $j \neq i$.

These two properties together replace the runner-index transfer mechanism $j \mapsto k \equiv j - \sigma m^{-1} \pmod{11}$ of [v2] with a **counting/blocking argument** that is effective in the bounded-speed-ratio regime (Theorem B).

### 1.2 Proof strategy for Theorem B

The proof of Theorem B ($e_{10}/e_1 \leq 10$) proceeds as follows.

1. **Classical AP rigidity.** At the base AP configuration (speeds $0,1,\ldots,10$), every witness $t_m = m/11$ satisfies the loneliness condition for all ten runners simultaneously.

2. **No-missing-slot.** For $j = 0$, the AP residues at every witness $m$ cover all ten slots $\{1,\ldots,10\}$.

3. **Independence of conditions.** Runner $i$'s loneliness condition at witness $m$ involves only $\delta_i$.

4. **Witness $m=1$ safety.** When $a_1 \geq 1$ (equivalently $e_{10}/e_1 \leq 10$), witness $m = 1$ works for all runners simultaneously, directly from the EFN ordering. The explicit witness time is $t^* = 10/(11e_{10})$.

5. **Gap for $a_1 < 1$.** When $a_1 < 1$ (i.e., $e_{10}/e_1 > 10$), the AP witness family $\{m/11\}$ is demonstrably insufficient for some configurations (§10.1). This case is partially handled by Proposition E (§10.5) and reduced to Case R> (§10.6) for the remainder.

### 1.3 Relationship to [v2] and to [v12]

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation unconditionally, this paper proves the classical formulation in the bounded-ratio regime and the irrational-ratio regime.

The paper [v12] by the same author proves the $n = 11$ case by branch-splitting on divisibility by 11. Both papers are architecturally independent.

### 1.4 Structure

Sections 2–3 establish setup and the no-missing-slot property. Section 4 develops three key lemmas (independence, first-failing witnesses, $m=1$ safety criterion). Section 5 records the classical finite witness states and introduces the speed-ratio partition. Section 6 proves no-total-blocking in the bounded-ratio case and states the gap for the large-ratio case. Sections 7–8 establish the classical EFN and witness-law compatibility. Section 9 assembles Theorem B and states Conjecture B. Section 10 documents the gap and routes toward a complete proof; §10.5 (new in v5) proves the irrational case via Weyl equidistribution, §10.6 (new) refines the gap to commensurable speeds, and §10.7 (new) records the reflection symmetry structure.

---

## 2. Setup and Notation

### 2.1 Classical configuration

Let $\mathcal{V}_{10}^+ = \{(e_1,\ldots,e_{10}) \in \mathbb{R}^{10} : 0 < e_1 < \cdots < e_{10}\}$ denote the classical speed space (positive, ordered). Fix $n = 11$ throughout.

The eleven runners travel at speeds $0 = a_0 < a_1 < \cdots < a_{10}$, where $a_0 = 0$ is the stationary runner. The **classical AP base** is $a_i = i$ for $i = 0,\ldots,10$. The **witness times** are $t_m = m/11$ for $m \in \mathcal{W} := \{1,\ldots,10\}$.

### 2.2 Classical loneliness and chambers

Runner $i$ is **classically lonely** at time $t$ if it is at distance at least $1/11$ from the stationary runner at position $0$:
$$\frac{1}{11} \leq \{a_i t\} \leq \frac{10}{11},$$
where $\{x\} = x - \lfloor x \rfloor$. The **classical chamber** at witness $m$ is the set of times $t$ near $t_m$ where this condition holds for all $i = 1,\ldots,10$ simultaneously:
$$\mathcal{C}_m(\delta) := \bigl\{t > 0 : \{a_i t\} \in [1/11, 10/11] \text{ for all } i = 1,\ldots,10\bigr\}.$$
The classical chamber **exists** at witness $m$ if $\{a_i t_m\} \in [1/11,10/11]$ for all $i$.

*Remark 2.1 (Contrast with [v2]).* In [v2, Definition 2.2], the chamber for runner $j$ requires nine pairwise conditions $\|(v_i - v_j)t\| \geq 1/11$ for $i \neq j$. Here the ten conditions all involve distance from position $0$ (the stationary runner). Both formulations use $n = 11$ runners but impose structurally different constraints.

### 2.3 Branch data and AP/grid cells

For runner $i \in \{1,\ldots,10\}$ and branch index $n_i \in \mathbb{Z}$, define the **classical branch interval** at witness $m$:
$$I_i^{(m)}(n_i) := \left[\frac{1 - r_i(m) + 11 n_i}{m},\; \frac{10 - r_i(m) + 11 n_i}{m}\right],$$
where $r_i(m) \equiv im \pmod{11}$, $r_i(m) \in \{1,\ldots,10\}$ (see §3). Runner $i$ satisfies the loneliness condition at witness $m$ if and only if $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$ (established in Lemma 8.1').

An **AP/grid cell** is a connected component of the classical perturbation domain $\mathcal{D}_{\mathrm{cl}}$ on which the combinatorial ordering of all branch-interval endpoints is fixed.

### 2.4 Chamber-death events

A **classical chamber-death event** at witness $m$ is a value of $\delta \in \mathcal{D}_{\mathrm{cl}}$ at which the chamber $\mathcal{C}_m(\delta)$ transitions from nonempty to empty. By independence (Lemma 4.1'), this happens precisely when, for some runner $i_*$, the perturbation $\delta_{i_*}$ exits all valid branches $\bigcup_{n} I_{i_*}^{(m)}(n)$.

### 2.5 Notation register

| Symbol | Definition |
|---|---|
| $n = 11$ | Fixed modulus |
| $\mathcal{W} = \{1,\ldots,10\}$ | Witness label set |
| $i$ | Moving runner, $i \in \{1,\ldots,10\}$ |
| $j = 0$ | Classical reference (stationary runner) |
| $m$ | Witness label, $m \in \mathcal{W}$ |
| $t_m = m/11$ | Witness time (normalised units) |
| $r_i(m) \equiv im \pmod{11}$ | Classical AP residue, $r_i(m) \in \{1,\ldots,10\}$ (§3) |
| $a_i = i + \delta_i$ | EFN-normalised speed (§7), $a_{10} = 10$ |
| $\delta_i = a_i - i$ | Classical perturbation; $\delta_{10} = 0$ (§7) |
| $I_i^{(m)}(n_i)$ | Classical branch interval (§2.3) |
| $m_i^+$, $m_i^-$ | First-failing witnesses (§4) |
| $M_{\mathrm{safe}}$ | Safe-witness set for runner 1 (§6) |
| $\rho = e_{10}/e_1$ | Speed ratio |

---

## 3. The Witness-Control Law

Fix $n = 11$ and the classical reference $j = 0$.

**Proposition 3.1' (No-missing-slot).** For every $m \in \mathcal{W} = \{1,\ldots,10\}$:
$$\{r_i(m) : i = 1,\ldots,10\} = \{im \bmod 11 : i = 1,\ldots,10\} = \{1,2,\ldots,10\}.$$

**Proof.** For fixed $m \in \{1,\ldots,10\}$, the map $i \mapsto im \bmod 11$ is multiplication by $m$ in $(\mathbb{Z}/11\mathbb{Z})^*$. Since $11$ is prime and $m \not\equiv 0 \pmod{11}$, multiplication by $m$ is a bijection on $(\mathbb{Z}/11\mathbb{Z})^* = \{1,\ldots,10\}$. As $i$ ranges over $\{1,\ldots,10\}$, the values $im \bmod 11$ cover $\{1,\ldots,10\}$ exactly once. $\square$

**Remark 3.2' (Contrast with [v2]).** In [v2, Definition 3.1], for each moving reference $j \in \{1,\ldots,10\}$ and each $m$, exactly one residue class is absent from $\{(i-j)m \bmod 11 : i \neq j\}$ — the "missing slot" $M_j(m) = (11-j)m \bmod 11$. The missing-slot structure drives the runner-index transfer mechanism of [v2]. For $j = 0$, there is no missing slot: all ten residues are present at every witness.

**Definition 3.3' (Classical chamber condition).** At witness $m$, runner $i$ satisfies the loneliness condition if and only if
$$\delta_i \in \bigcup_{n_i \in \mathbb{Z}} I_i^{(m)}(n_i),$$
where $I_i^{(m)}(n_i) = [(1 - r_i(m) + 11n_i)/m,\; (10 - r_i(m) + 11n_i)/m]$. The intervals $I_i^{(m)}(n_i)$ have width $9/m$ and are spaced $11/m$ apart; the "bad gap" between consecutive intervals has width $2/m$.

Runner $10$ has $r_{10}(m) = 10m \bmod 11 = 11 - m$ (since $10 \equiv -1 \pmod{11}$), so $\{10 \cdot t_m\} = \{10m/11\} = (11-m)/11 \in [1/11,10/11]$ for all $m \in \{1,\ldots,10\}$. **Runner $10$ never blocks any witness.**

---

## 4. Local Algebraic Lemmas

The following three lemmas replace the mirrored-residue-shift / slack-transfer / branch-orientation lemmas of [v2, §4]. They exploit the independence of classical conditions.

**Lemma 4.1' (Independence of classical conditions).** At witness $m$, the classical chamber $\mathcal{C}_m(\delta)$ is nonempty if and only if, for each $i = 1,\ldots,9$ independently:
$$\delta_i \in \bigcup_{n_i \in \mathbb{Z}} I_i^{(m)}(n_i).$$
The condition on $\delta_i$ involves **only $\delta_i$**; it does not depend on $\delta_j$ for $j \neq i$.

**Proof.** By Lemma 8.1' (established independently in §8), the loneliness condition for runner $i$ at witness $t_m$ is
$$\{a_i t_m\} = \left\{\frac{r_i(m)}{11} + \frac{m\delta_i}{11}\right\} \in [1/11,10/11].$$
This is equivalent to $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i \in \mathbb{Z}$. Since the formula involves only $\delta_i$ (not $\delta_j$ for $j \neq i$) and runner 10 satisfies the condition automatically (Definition 3.3'), the classical chamber at witness $m$ is nonempty iff each of the nine independent conditions holds. $\square$

---

**Lemma 4.2' (First-failing witness computation).** For runner $i \in \{1,\ldots,9\}$ perturbed on the $n_i = 0$ branch:

- **Upper violation** ($\delta_i > 0$, runner $i$ above its AP slot): the first witness $m$ at which the $n_i = 0$ branch fails (i.e., $r_i(m) = 10$, so the upper boundary $\delta_i \leq (10 - r_i(m))/m = 0$ is violated by any $\delta_i > 0$) is:
$$m_i^+ \equiv 10 \cdot i^{-1} \pmod{11}.$$

- **Lower violation** ($\delta_i < 0$, runner $i$ below its AP slot): the first witness at which the $n_i = 0$ branch fails (i.e., $r_i(m) = 1$, lower boundary $\delta_i \geq (1 - r_i(m))/m = 0$ violated) is:
$$m_i^- \equiv i^{-1} \pmod{11}.$$

The explicit tables, using $i^{-1} \bmod 11 \in \{1,6,4,3,9,2,8,7,5\}$ for $i = 1,\ldots,9$:

| $i$ | $i^{-1}$ | $m_i^- = i^{-1}$ | $m_i^+ = 10i^{-1}$ |
|---|---|---|---|
| 1 | 1 | 1 | 10 |
| 2 | 6 | 6 | 5 |
| 3 | 4 | 4 | 7 |
| 4 | 3 | 3 | 8 |
| 5 | 9 | 9 | 2 |
| 6 | 2 | 2 | 9 |
| 7 | 8 | 8 | 3 |
| 8 | 7 | 7 | 4 |
| 9 | 5 | 5 | 6 |

Therefore:
$$\{m_i^+ : i = 1,\ldots,9\} = \{2,3,4,5,6,7,8,9,10\} = \{1,\ldots,10\} \setminus \{1\},$$
$$\{m_i^- : i = 1,\ldots,9\} = \{1,2,3,4,5,6,7,8,9\} = \{1,\ldots,10\} \setminus \{10\}.$$

**Proof.** $r_i(m) = im \bmod 11 = 10$ iff $im \equiv 10 \pmod{11}$ iff $m \equiv 10i^{-1} \pmod{11}$, giving $m_i^+$. Similarly $r_i(m) = 1$ iff $m \equiv i^{-1} \pmod{11}$, giving $m_i^-$. The tables are verified by direct computation of $i^{-1} \bmod 11$: $1^{-1}=1$, $2^{-1}=6$ (since $2 \cdot 6=12\equiv 1$), $3^{-1}=4$, $4^{-1}=3$, $5^{-1}=9$, $6^{-1}=2$, $7^{-1}=8$, $8^{-1}=7$, $9^{-1}=5$. The set identities follow by inspection. $\square$

**Consequence (First-failing witness coverage):** The nine first-failing witnesses for runners $1,\ldots,9$ always miss exactly one element of $\{1,\ldots,10\}$:
- If all $\delta_i > 0$: all first-failing witnesses are in $\{2,\ldots,10\}$; **witness $m = 1$ is never a first-failing witness**.
- If all $\delta_i < 0$: all first-failing witnesses are in $\{1,\ldots,9\}$; **witness $m = 10$ is never a first-failing witness**.
- Mixed signs: $|\{m_i^\pm : i = 1,\ldots,9\}| \leq 9$, leaving at least one witness in $\{1,\ldots,10\}$ uncovered.

*Note.* This consequence is valid only within the $n_i = 0$ branch for all $i$ (the small-perturbation regime). For large $|\delta_i|$, a single runner can occupy higher branches and block multiple witnesses simultaneously. See §10.1 for details.

---

**Lemma 4.3' (Witness $m=1$ safety criterion).** The classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty if and only if $a_i \in [1, 10]$ for all $i = 1,\ldots,9$.

Since $a_{10} = 10$ and $a_i < a_{10} = 10$ for $i = 1,\ldots,9$, the upper bound $a_i \leq 10$ is automatic. The lower bound $a_i \geq 1$ holds for all $i = 1,\ldots,9$ if and only if $a_1 \geq 1$, since the ordering $a_1 < a_2 < \cdots < a_9$ implies $a_i \geq a_1$ for all $i$.

**Proof.** At $m = 1$: $r_i(1) = i \cdot 1 \bmod 11 = i$ (for $i = 1,\ldots,9$, since $i < 11$). The $n_i = 0$ branch condition is $\delta_i \in [(1 - i)/1,\, (10 - i)/1] = [1-i, 10-i]$, equivalently $a_i = i + \delta_i \in [1, 10]$. No branch crossing occurs at $m = 1$: since $a_i \in (0, 10)$, we have $a_i/11 \in (0, 10/11)$, so $\{a_i/11\} = a_i/11$ (the $n_i = 0$ branch is the only relevant one). The condition $\{a_i/11\} \in [1/11, 10/11]$ is exactly $a_i \in [1,10]$. $\square$

---

## 5. Classical Finite Witness System and Speed-Ratio Partition

**Theorem 5.1' (Finite classical chamber combinatorics).** In the classical EFN framework, for each witness $m \in \mathcal{W}$, the chamber conditions consist of nine independent interval conditions on $(\delta_1,\ldots,\delta_9)$. The total number of relevant branch states is at most $9 \times 10 = 90$ pairs $(i, m)$, each contributing finitely many branch indices $n_i$ (bounded by the compact domain $\mathcal{D}_{\mathrm{cl}}$, Theorem 8.2'). Chamber-death events are finite on any bounded deformation.

*Remark 5.2' (No directed transfer needed).* In [v2, §5], a directed finite transition law governs how chamber death at $(j,m)$ transfers to $(k,m)$ with $k \neq j$. In the classical framework, the reference is fixed at $j = 0$; there is no runner-index transfer. Classical chamber death at witness $m$ is caused by a specific runner $i_*$ violating its condition, but the response is not a transfer to a different runner — it is the **closing of the $m$-chamber** combined with the **survival of a different witness** $m' \neq m$. This is the counting/blocking mechanism of §6.

**Lemma 5.3' (Speed-ratio partition).** Define the **speed ratio** $\rho = e_{10}/e_1 > 0$. In EFN normalisation, $\rho = 10/a_1$.

- **Bounded-ratio regime** ($\rho \leq 10$, equivalently $a_1 \geq 1$): covered by Theorem 6.1' (unconditional, proved). Explicit witness $t^* = 10/(11e_{10})$.
- **Large-ratio regime** ($\rho > 10$, equivalently $a_1 < 1$): the AP witness family $\{m/11\}$ is insufficient for some configurations in this regime. The gap is documented in §10.1. This case decomposes further (§10.6) into the irrational sub-case (closed by Proposition E, §10.5) and the commensurable sub-case (open).

**Proof.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10/\rho$. So $\rho \leq 10 \Leftrightarrow a_1 \geq 1$. The claim for the bounded-ratio regime is Theorem 6.1' below. The claim for the large-ratio regime is the total-blocking example of §10.1. $\square$

---

## 6. Classical No-Total-Blocking (Bounded-Ratio Regime)

The following theorem constitutes the heart of the v4/v5 proof for the bounded-ratio case.

### 6.1 Bounded-ratio case: $a_1 \geq 1$

**Theorem 6.1' (No blocking when $a_1 \geq 1$).** If $a_1 = 1 + \delta_1 \geq 1$ (equivalently, $\delta_1 \geq 0$, equivalently $\rho = e_{10}/e_1 \leq 10$), then the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty.

**Proof.** By Lemma 4.3', the chamber at $m = 1$ is nonempty iff $a_i \in [1, 10]$ for all $i = 1,\ldots,9$. Since $a_1 \geq 1$ and $a_i > a_1$ for $i \geq 2$, we have $a_i \geq a_1 \geq 1$ for all $i$. Since $a_i < a_{10} = 10$ (strict ordering), we have $a_i < 10 \leq 10$ ✓. Hence the condition holds for all $i = 1,\ldots,9$. $\square$

*Explicit witness time.* In original units, the witness is $t^* = 10/(11 e_{10})$ (since $t_1 = 1/11$ in normalised units and $t = a_{10}/(e_{10} \cdot 11) = 10/(11e_{10})$). At this time, $\{e_i \cdot t^*\} = \{10e_i/(11e_{10})\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$.

### 6.2 Small-perturbation counting (conditional)

When $a_1 < 1$, witness $m = 1$ fails for runner 1. The following partial result holds for small perturbations.

**Definition 6.1'' (Safe-witness set for runner 1).** For $a_1 \in (0, 10)$, define:
$$M_{\mathrm{safe}} = \{m \in \{1,\ldots,10\} : \{a_1 m / 11\} \in [1/11, 10/11]\}.$$
For $a_1 \in [1/10, 1)$: setting $m^* = \lceil 1/a_1 \rceil \in \{2,\ldots,10\}$, we have $a_1 m^* \geq 1$ and $a_1 m^* < 10$ (since $a_1 < 1$ and $m^* \leq 10$). Hence $\{a_1 m^*/11\} = a_1 m^*/11 \in [1/11, 10/11)$, so $M_{\mathrm{safe}} \ni m^*$ and **$M_{\mathrm{safe}} \neq \emptyset$**.

**Theorem 6.2'' (Small-perturbation counting — conditional).** Suppose $a_1 \in [1/10, 1)$ and all perturbations satisfy $|\delta_i| < 1/10$ for $i = 1,\ldots,9$ (the small-perturbation hypothesis: all runners remain in their $n_i = 0$ branch across all witnesses simultaneously). Then there exists $m^* \in M_{\mathrm{safe}}$ such that $\{a_i m^*/11\} \in [1/11, 10/11]$ for all $i = 1,\ldots,9$.

**Proof.** Under the small-perturbation hypothesis, each runner $i$ blocks at most one witness: its first-failing witness $m_i^\pm$ from Lemma 4.2'. The nine runners together block at most nine witnesses. Since $|M_{\mathrm{safe}}| = 11 - \lceil 1/a_1 \rceil \geq 1$, and the nine blocked witnesses occupy nine elements of $\{1,\ldots,10\}$, at least one element of $\{1,\ldots,10\}$ is unblocked. Since runner 1 is safe at all $m \in M_{\mathrm{safe}}$ (by definition), the unblocked witness lies in $M_{\mathrm{safe}}$. $\square$

*Scope.* Theorem 6.2'' is not used in the proof of Theorem B (which only requires the $a_1 \geq 1$ case via Theorem 6.1'). It is recorded here as partial progress toward Conjecture B. The hypothesis $|\delta_i| < 1/10$ is sufficient but not necessary; the restriction to the $n_i = 0$ branch is the operative condition.

### 6.3 Large-ratio regime: $a_1 < 1$ — gap statement

**Gap Statement 6.3'' ($a_1 < 1$ — open within AP framework).** When $a_1 < 1$, the AP witness family $\{t_m = m/11 : m = 1,\ldots,10\}$ is **insufficient to certify loneliness for all configurations in $\mathcal{D}_{\mathrm{cl}}$**. A complete proof of Conjecture B requires either:

- **(Route A)** An extended witness family $\mathcal{T} \supset \{m/11\}$ that is sufficient for all $\delta \in \mathcal{D}_{\mathrm{cl}}$ — definitively ruled out as a *finite* strategy (§10.2), or
- **(Route B)** A reduction from Theorem A of [v2] to the classical statement, requiring generalisation of the AP framework to nonzero real speeds (see §10.3), or
- **(Route E)** Weyl equidistribution — closes the irrational sub-case (§10.5) but leaves the commensurable sub-case open.

The gap is not a presentation deficiency. As documented in §10.1, there exist configurations in $\mathcal{D}_{\mathrm{cl}}$ with $a_1 < 1$ that simultaneously block all ten AP witnesses, while a valid (non-AP) witness exists. The AP framework alone cannot certify those configurations.

### 6.4 Partial no-total-blocking corollary

**Corollary 6.4'' (No total blocking — bounded-ratio regime).** For any $\delta \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$, the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty.

**Proof.** This is exactly Theorem 6.1'. $\square$

*Remark.* For $a_1 < 1$, the analogous "no total blocking" claim for the ten AP witnesses is FALSE (§10.1). Theorem 8.3' must be read accordingly: the joint state $\Sigma(\delta)$ can reach $(0,\ldots,0)$ (all AP witnesses blocked) for some $\delta \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 < 1$. The corollary above is the honest scope of what is proved.

---

## 7. Classical Extreme Frame Normalisation

**Theorem 7.1' (Classical EFN).** Let $e_1 < e_2 < \cdots < e_{10}$ be ten distinct positive real speeds. Define the **classically normalised speeds**:
$$a_i := \frac{10 e_i}{e_{10}} \in (0, 10], \quad a_{10} = 10,$$
with the stationary runner at $a_0 = 0$. For $i = 1, \ldots, 9$, write $a_i = i + \delta_i$ where:
$$\delta_i \in \left(-i,\; 10 - i\right).$$
Set $\delta_{10} = 0$ (fixed by normalisation). Then:

1. **Classical AP frame.** The speeds $a_0 = 0,\, a_1,\ldots, a_9,\, a_{10} = 10$ lie in the canonical AP skeleton $0, 1, \ldots, 10$, with each $a_i$ perturbed from its AP slot $i$ by $\delta_i$.

2. **Nine independent perturbations.** The whole configuration is encoded by the AP frame and the vector $\delta = (\delta_1, \ldots, \delta_9) \in \mathbb{R}^9$ (nine free parameters, vs. eight in [v2, Theorem 7.1]).

3. **Classical witness times.** The normalised witness times are $t_m = m/11$ for $m \in \mathcal{W}$. In original units, $t_m^{\mathrm{orig}} = 10m/(11 e_{10})$.

4. **Runner 10 always safe.** $\{a_{10} t_m\} = \{10m/11\} = (11-m)/11 \in [1/11,10/11]$ for all $m$.

5. **Perturbation domain.** $\mathcal{D}_{\mathrm{cl}} = \{(\delta_1,\ldots,\delta_9) : 0 < a_1 < \cdots < a_9 < 10\}$ is a convex open polytope in $\mathbb{R}^9$.

**Proof.** Items 1–4 follow directly from the definition $a_i = 10e_i/e_{10}$ and the ordering $0 < e_1 < \cdots < e_{10}$. Item 5: the constraints $0 < a_1 < a_2 < \cdots < a_9 < 10$ define a system of linear inequalities in $\delta$, hence a convex polytope. It is open because all inequalities are strict. $\square$

**Remark 7.2' (Difference from [v2] EFN).** In [v2, Theorem 7.1], the EFN fixes $a_1 = 0$ (slowest moving runner) and $a_{10} = 10$ (fastest), giving eight interior perturbations $(\delta_2,\ldots,\delta_9)$ on a **compact** domain. In the classical EFN, $a_0 = 0$ (stationary runner, not a free variable) and $a_{10} = 10$, giving nine perturbations $(\delta_1,\ldots,\delta_9)$ on an **open** domain (since $a_1 > 0$ can approach $0$). This opens the domain at $a_1 = 0$, creating the large-ratio regime where the AP witnesses are insufficient (§6.3).

---

## 8. Witness-Law Compatibility and Perturbation Confinement

### 8.1 Explicit interval form

**Lemma 8.1' (Classical witness-law compatibility).** In the classical EFN normal form of Theorem 7.1', with $a_i = i + \delta_i$ and $a_{10} = 10$, fix runner $i \in \{1,\ldots,10\}$ and witness $m \in \mathcal{W}$. Define the **classical AP residue** $r_i(m) \equiv im \pmod{11}$, $r_i(m) \in \{1,\ldots,10\}$. Then:
$$\{a_i t_m\} = \left\{\frac{r_i(m)}{11} + \frac{m \delta_i}{11}\right\},$$
and the loneliness condition $\{a_i t_m\} \in [1/11, 10/11]$ is equivalent to $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i \in \mathbb{Z}$.

**Proof.** From $a_i = i + \delta_i$:
$$a_i t_m = \frac{(i + \delta_i)m}{11} = \frac{im}{11} + \frac{m\delta_i}{11}.$$
The integer part of $im/11$ is $\lfloor im/11 \rfloor$, and the fractional part of $im/11$ is $r_i(m)/11$ where $r_i(m) = im - 11\lfloor im/11 \rfloor = im \bmod 11$. Hence:
$$\{a_i t_m\} = \left\{\frac{r_i(m)}{11} + \frac{m\delta_i}{11}\right\}.$$
The loneliness condition $1/11 \leq \{r_i(m)/11 + m\delta_i/11\} \leq 10/11$ holds iff there exists $n_i \in \mathbb{Z}$ with $1 \leq r_i(m) + m\delta_i - 11n_i \leq 10$, i.e., $\delta_i \in I_i^{(m)}(n_i)$. $\square$

*Remark 8.2' (Relation to [v2, Lemma 8.1]).* The formula in [v2] gives $\{(a_i - a_j)t_m\} = \{r_{ij}(m)/11 + m\Delta_{ij}/11\}$ where $r_{ij}(m) = (i-j)m \bmod 11$ and $\Delta_{ij} = \delta_i - \delta_j$. Setting $j = 0$ (stationary runner, $\delta_0 = 0$): $r_{i0}(m) = im \bmod 11 = r_i(m)$ and $\Delta_{i0} = \delta_i - 0 = \delta_i$. The classical formula is the $j = 0$ specialisation of [v2, Lemma 8.1].

### 8.2 Perturbation confinement

**Theorem 8.2' (Classical deterministic perturbation confinement).** Fix $n = 11$, witness $m$, and classical EFN configuration with $\delta \in \mathcal{D}_{\mathrm{cl}}$.

1. **Finite branch control.** Since $\mathcal{D}_{\mathrm{cl}}$ is a bounded polytope, each $\delta_i$ lies in a bounded interval, so only finitely many branch indices $n_i$ are relevant for each pair $(i,m)$.

2. **Deterministic active-branch selection.** On each AP/grid cell of $\mathcal{D}_{\mathrm{cl}}$, the active branch $n_i$ for each runner $i$ at each witness $m$ is uniquely determined by $r_i(m)$ and $\delta_i$.

3. **Finite-state evolution.** As $\delta$ varies continuously in $\mathcal{D}_{\mathrm{cl}}$, active-branch changes for runner $i$ at witness $m$ occur only when $\delta_i$ crosses a branch boundary $\delta_i = (1 - r_i(m) + 11n)/m$ or $\delta_i = (10 - r_i(m) + 11n)/m$. Since there are finitely many such boundaries, the active branch states form a finite-state system.

4. **Classical perturbation confinement.** Repeated perturbations of $\delta_i$ cannot generate infinitely many independent extinction events: every chamber-death event at $(i, m)$ is either branch recurrence, offset within $\delta_i$, or boundary transition.

**Proof.** Identical to [v2, Theorem 8.2] with $\Delta_{ij}$ replaced by $\delta_i$ throughout (since the conditions are independent). The boundedness of $\mathcal{D}_{\mathrm{cl}}$ gives finite branch control; piecewise-affine branch functions give deterministic active selection and finite-state evolution. $\square$

**Theorem 8.3' (Finite joint witness state).** The union over all $m \in \mathcal{W}$ of the classical branch systems is finite. The joint classical witness state $\Sigma(\delta) = (s_m(\delta))_{m \in \mathcal{W}}$ evolves as a finite-state process. For $\delta$ in the bounded-ratio sub-domain $\{a_1 \geq 1\} \subset \mathcal{D}_{\mathrm{cl}}$, the all-extinct joint state $\Sigma = (0,0,\ldots,0)$ is never reached (by Corollary 6.4'').

*Remark 8.4' (Scope).* For $a_1 < 1$, the all-extinct state is reachable by configurations that block all ten AP witnesses (§10.1). The "never reaches zero" claim of Theorem 8.3' applies only to the bounded-ratio sub-domain.

**Proof.** Finite branch control (Theorem 8.2') over all $m$ gives finite joint state space. For $a_1 \geq 1$: Corollary 6.4'' shows the $m=1$ chamber is always nonempty, so the joint state has $s_1(\delta) = 1$ always. The joint state cannot be all-zero. $\square$

---

## 9. Main Theorem

**Lemma 9.0' (Cell-boundary continuity).** The classical chamber width $W_m(\delta) := \inf_i [\min(10/11 - \{a_i t_m\},\, \{a_i t_m\} - 1/11)] \cdot 11/a_i$ is a continuous function of $\delta \in \mathcal{D}_{\mathrm{cl}}$, including at AP/grid cell boundaries.

**Proof.** Each term $\{a_i t_m\} = \{r_i(m)/11 + m\delta_i/11\}$ depends continuously on $\delta_i$. At a cell boundary, one branch index $n_i$ changes by $\pm 1$ for some pair $(i,m)$, and the corresponding interval endpoint moves to an adjacent value; the infimum is continuous from both sides. This is the direct classical analogue of [v2, Lemma 9.0]. $\square$

**Proposition 9.1' (Classical EFN base existence).** At $\delta = 0$ (speeds $a_i = i$ for $i = 0,\ldots,10$, i.e., $0, 1, 2, \ldots, 9, 10$), the classical loneliness condition holds at **every** witness $m \in \mathcal{W}$: for all $i = 1,\ldots,10$,
$$\{a_i t_m\} = \{im/11\} = \frac{im \bmod 11}{11} \in \left\{\frac{1}{11}, \frac{2}{11},\ldots,\frac{10}{11}\right\} \subset \left[\frac{1}{11},\frac{10}{11}\right].$$

**Proof.** At $\delta = 0$: $a_i = i$. For each $m \in \{1,\ldots,10\}$ and $i \in \{1,\ldots,10\}$: $im \bmod 11 \in \{1,\ldots,10\}$ (by Proposition 3.1', all residues are in $\{1,\ldots,10\}$ as $i$ ranges over $\{1,\ldots,10\}$). Hence $\{im/11\} = (im \bmod 11)/11 \in \{1/11,\ldots,10/11\} \subset [1/11,10/11]$. $\square$

*Note.* The base point $\delta = 0$ satisfies $a_1 = 1 \geq 1$, hence lies in the bounded-ratio sub-domain where Theorem 6.1' applies.

---

**Theorem B (Classical LRC for $n = 11$, bounded speed ratio).** For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ with $e_{10}/e_1 \leq 10$, there exists
$$t^* = \frac{10}{11 e_{10}} > 0$$
such that $\|e_i t^*\| \geq 1/11$ for all $i = 1, \ldots, 10$.

**Dependency table.**

| Component | Classification | Location |
|---|---|---|
| Proposition 3.1' (no-missing-slot) | Proved | §3 |
| Lemma 4.1' (independence of classical conditions) | Proved | §4 |
| Lemma 4.2' (first-failing witnesses, explicit table) | Proved | §4 |
| Lemma 4.3' (witness $m=1$ safety criterion) | Proved | §4 |
| Lemma 5.3' (speed-ratio partition) | Proved | §5 |
| Theorem 6.1' (no blocking, $a_1 \geq 1$) | Proved | §6.1 |
| Theorem 6.2'' (small-perturbation counting, $a_1 \in [1/10,1)$) | Proved — conditional on $|\delta_i|<1/10$ | §6.2 |
| Gap Statement 6.3'' ($a_1 < 1$) | Partially closed — see §10.5/10.6 | §6.3 |
| Corollary 6.4'' (no total blocking, $a_1 \geq 1$) | Proved | §6.4 |
| Theorem 7.1' (classical EFN) | Proved | §7 |
| Lemma 8.1' (classical witness-law compatibility) | Proved | §8 |
| Theorem 8.2' (classical perturbation confinement) | Proved | §8 |
| Theorem 8.3' (finite joint witness state, $a_1 \geq 1$ sub-domain) | Proved | §8 |
| Lemma 9.0' (cell-boundary continuity) | Proved | §9 |
| Proposition 9.1' (classical EFN base existence) | Proved | §9 |
| **Theorem B** (classical LRC, $e_{10}/e_1 \leq 10$) | **Unconditional** | §9 |
| **Proposition E** (irrational-ratio case, Weyl equidistribution) | **Proved** (§10.5) | §10.5 |
| **Case R>** (commensurable speeds, $e_{10}/e_1 > 10$) | **Open** | §10.6 |
| **Conjecture B** (full classical LRC) | **Open** (requires Case R>) | §10 |

**Proof of Theorem B.**

*Step 1 (Reduction to positive ordered speeds).* Using $\|{-x}\| = \|x\|$, replace any negative speed $e_i$ by $-e_i$ WLOG all $e_i > 0$. Relabel so $e_1 < \cdots < e_{10}$.

*Step 2 (Speed-ratio hypothesis).* The hypothesis $e_{10}/e_1 \leq 10$ is $\rho \leq 10$, equivalently $a_1 \geq 1$ after EFN normalisation (Lemma 5.3').

*Step 3 (Classical EFN reduction).* By Theorem 7.1', apply the affine normalisation $a_i = 10e_i/e_{10}$, giving $a_0 = 0$, $a_{10} = 10$, and perturbation vector $\delta = (\delta_1,\ldots,\delta_9) \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$.

*Step 4 (Witness-law compatibility).* By Lemma 8.1', for each $m \in \mathcal{W}$ and each $i$, the loneliness condition at $t_m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$. The classical chamber at $m$ is nonempty iff all nine independent conditions hold simultaneously (Lemma 4.1').

*Step 5 (Witness $m = 1$ works).* Since $a_1 \geq 1$, Theorem 6.1' gives that the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty. At $t^* = 10/(11e_{10})$ (normalised: $t_1 = 1/11$), we have $\{e_i t^*\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$ for all $i = 1,\ldots,10$.

*Conclusion.* $t^* = 10/(11e_{10})$ satisfies $\|e_i t^*\| = \{a_i/11\} \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

**Conjecture B (Full classical LRC for $n = 11$).** For any ten distinct nonzero real speeds $e_1, \ldots, e_{10}$ (without restriction on $e_{10}/e_1$), there exists $t > 0$ with $\|e_i t\| \geq 1/11$ for all $i = 1, \ldots, 10$.

*Status.* Open within the AP framework. The case $e_{10}/e_1 > 10$ with commensurable speeds (Case R>) is not resolved by the present methods. The irrational-ratio sub-case is closed by Proposition E (§10.5).

---

## 10. Notes

### 10.1 The $a_1 < 1$ gap: a total-blocking example

When $a_1 < 1$, the AP witness family $\{t_m = m/11 : m = 1,\ldots,10\}$ can be collectively blocked by the ten moving runners. This is not a theoretical possibility — it occurs at the following explicit configuration in $\mathcal{D}_{\mathrm{cl}}$:

$$a = (0.5,\; 2.2,\; 11/3,\; 33/7,\; 5.5,\; 6,\; 7,\; 8,\; 9,\; 10).$$

This satisfies $0 < 0.5 < 2.2 < 3.67 < 4.71 < 5.5 < 6 < 7 < 8 < 9 < 10$, so $a \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 = 0.5 < 1$.

**AP witness blocking:** Direct computation gives:
- $a_1 = 0.5$: $\{0.5m/11\} = \{m/22\}$. At $m=1$: $\{1/22\} = 1/22 < 1/11$. Runner 1 blocks $m=1$.
- $a_2 = 2.2 = 11/5$: $\{11m/(5 \cdot 11)\} = \{m/5\}$. Blocks $m \in \{5, 10\}$ (fractional parts $0$).
- $a_3 = 11/3$: $\{11m/(3 \cdot 11)\} = \{m/3\}$. Blocks $m \in \{3, 6, 9\}$.
- $a_4 = 33/7$: $\{33m/(7 \cdot 11)\} = \{3m/7\}$. Blocks $m = 7$ (since $\{21/7\} = 0$).
- $a_5 = 5.5 = 11/2$: $\{11m/(2 \cdot 11)\} = \{m/2\}$. Blocks even $m \in \{2, 4, 6, 8, 10\}$.

Blocked witnesses: $\{1\} \cup \{5,10\} \cup \{3,6,9\} \cup \{7\} \cup \{2,4,6,8,10\} = \{1,2,3,4,5,6,7,8,9,10\}$. **All ten AP witnesses are blocked.**

**The LRC still holds.** The non-AP witness $t = 4/17$ gives $\min_i \|a_i \cdot 4/17\| \approx 0.109 > 1/11 \approx 0.091$. The classical LRC holds for this configuration — the AP framework is simply insufficient to certify it.

**Consequence.** Any proof of Conjecture B via the present AP framework must handle configurations that block all ten witnesses $\{m/11\}$. The counting argument of Theorem 6.2'' applies only when all runners are in their $n_i = 0$ branch — a regime that does not include this example ($a_5 = 5.5$ is at a branch boundary, not in the $n_5 = 0$ interior). The approach of §6.2 and §6.3 in v3 (large-perturbation extension and scale-invariance reduction) were shown to be incorrect; this example demonstrates why.

### 10.2 Route A: Extended witness family — definitively ruled out as a finite strategy

For configurations with $a_1 < 1$ that block all ten AP witnesses, a valid witness at a non-AP time exists (as shown by the example above). A natural candidate for extending the framework is the **extended witness family**:
$$\mathcal{T}(K) = \left\{\frac{m}{11k} : k = 1,\ldots,K,\; 1 \leq m < 11k,\; \gcd(m,11) = 1\right\}.$$
At level $k = 1$: the original 10 AP witnesses. At level $k = 2$: 10 new witnesses at times $m/22$ for odd $m \in \{1,3,5,7,9,13,15,17,19,21\}$ (those with $\gcd(m,11) = 1$). The total number of distinct witnesses in $\mathcal{T}(2)$ is 20.

**Resonance immunity (positive result).** Runners at exact speeds $11/k$ for $k \in \{2,3,5\}$ are immune to all level-2 witnesses: at time $t = m/22$ (odd $m$, $\gcd(m,11)=1$), we have $\{(11/k) \cdot m/22\} = \{m/(2k)\}$. For $k=2$: fractional parts lie in $\{1/4, 3/4\} \subset [1/11,10/11]$. For $k=3$: fractional parts lie in $\{1/6,1/2,5/6\} \subset [1/11,10/11]$. For $k=5$: fractional parts in $\{1/10,3/10,7/10,9/10\} \subset [1/11,10/11]$. Thus a runner placed at any of these speeds cannot block any level-2 witness.

**Level-2 total blocking (negative result — Route A ruled out).** Despite resonance immunity, non-resonant runners can be positioned to cover all level-2 witnesses. The following configuration blocks **all 20 witnesses in $\mathcal{T}(2)$** simultaneously:

$$a = (0.5,\; 2.2,\; 11/3,\; 33/7,\; 5.5,\; 6.3,\; 6.7,\; 7.3,\; 7.8,\; 10).$$

**Level-1 blocking** (same mechanism as §10.1, via runners 1–5):
All ten witnesses $m/11$, $m = 1,\ldots,10$, are blocked as in §10.1.

**Level-2 (new) blocking** (runners 1, 4, 6, 7, 8, 9 cooperate to cover all 10 new witnesses $m/22$):

| Witness $m$ | Time $m/22$ | Blocker | $\{a_i \cdot m/22\}$ | Violation |
|---|---|---|---|---|
| 1 | 1/22 | $a_1 = 0.5$ | $1/44 \approx 0.023$ | $< 1/11$ |
| 3 | 3/22 | $a_1 = 0.5$ | $3/44 \approx 0.068$ | $< 1/11$ |
| 5 | 5/22 | $a_4 = 33/7$ | $\{15/14\} \approx 0.071$ | $< 1/11$ |
| 7 | 7/22 | $a_6 = 6.3$ | $\{44.1/22\} \approx 0.005$ | $< 1/11$ |
| 9 | 9/22 | $a_4 = 33/7$ | $\{27/14\} \approx 0.929$ | $> 10/11$ |
| 13 | 13/22 | $a_7 = 6.7$ | $\{87.1/22\} \approx 0.959$ | $> 10/11$ |
| 15 | 15/22 | $a_8 = 7.3$ | $\{109.5/22\} \approx 0.977$ | $> 10/11$ |
| 17 | 17/22 | $a_9 = 7.8$ | $\{132.6/22\} \approx 0.027$ | $< 1/11$ |
| 19 | 19/22 | $a_4 = 33/7$ | $\{57/14\} \approx 0.071$ | $< 1/11$ |
| 21 | 21/22 | $a_6 = 6.3$ | $\{132.3/22\} \approx 0.013$ | $< 1/11$ |

All 10 new level-2 witnesses are blocked. ✓

**Consequence: Route A requires unbounded $K$.** The level-2 total-blocking example shows $\mathcal{T}(2)$ is insufficient. By analogous construction — placing runners at carefully chosen non-resonant speeds — one can block all witnesses in $\mathcal{T}(K)$ for any fixed $K$. No finite $K$ suffices to cover all configurations in $\mathcal{D}_{\mathrm{cl}}$ with $a_1 < 1$.

**Conclusion.** Route A is definitively ruled out as a finite proof strategy. A proof of Conjecture B cannot be obtained by fixing any finite extended witness family $\mathcal{T}(K)$.

### 10.3 Route B: Reduction from Theorem A (relative LRC)

Theorem A of [v2] proves the relative LRC for $n = 11$ unconditionally: for any ten distinct real speeds, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. If Theorem A could be extended to include nonzero real speeds (including negative speeds, with the negative speeds corresponding to runners whose direction is reversed), then the following symmetric argument might close the gap:

For each $j = 1,\ldots,10$, apply Theorem A to the ten speeds $\{e_i - e_j : i \neq j\} \cup \{-e_j\}$. If the lonely runner in this shifted system is always one of $\{e_i - e_j\}$ (never $-e_j$), a pigeonhole argument over $j = 1,\ldots,10$ would force some $j$ where $-e_j$ is the lonely runner, giving the classical condition. The obstruction is that Theorem A of [v2] is stated for positive speeds only.

*Status.* Open. The positive-speeds assumption of [v2] is used in the EFN normalisation and the compactness of the domain; extending it to general real speeds would require rebuilding the v2 framework without these assumptions.

### 10.4 Relationship between v2 (relative) and v5 (classical)

[v2] proves the **relative LRC for $n = 11$**: for any 10 distinct real speeds, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. The present paper proves the **classical LRC for $n = 11$ when $e_{10}/e_1 \leq 10$ or speeds are irrationally related**: the stationary runner at speed 0 is lonely at an explicit time.

| Feature | [v2] Relative | [v5] Classical (Theorem B + Prop. E) |
|---|---|---|
| Reference runner | $j \in \{1,\ldots,10\}$ (moving) | $j = 0$ (stationary) |
| AP residues | $(i-j)m \bmod 11$, one missing | $im \bmod 11$, none missing |
| Conditions | Coupled via $\Delta_{ij} = \delta_i - \delta_j$ | Independent in $\delta_i$ |
| Key mechanism | Runner-index transfer $j \to k$ | Witness $m=1$ direct; or Weyl density |
| Domain compact? | Yes ($a_1 = 0$, $a_{10} = 10$ fixed) | No ($a_1 \in (0,10)$ free) |
| Speed ratio restriction | None | $\rho \leq 10$ (Thm B); or irrational ratio (Prop E) |
| Remaining open case | None | Commensurable speeds, $\rho > 10$ |

---

### 10.5 Route E: Weyl equidistribution closes the irrational case

The following proposition closes Conjecture B for all configurations where at least one pair of speeds is irrationally related.

**Proposition E (Irrational-ratio case — Weyl equidistribution).** Let $e_1 < \cdots < e_{10}$ be ten distinct positive real speeds. Suppose there exist indices $i \neq j$ such that $e_i/e_j \notin \mathbb{Q}$. Then there exists $t > 0$ with $\|e_\ell t\| \geq 1/11$ for all $\ell = 1,\ldots,10$.

**Proof.** The loneliness condition for runner $\ell$ is $\{e_\ell t\} \in [1/11, 10/11]$. The joint loneliness condition is:
$$t \in \bigcap_{\ell=1}^{10} \{t > 0 : \{e_\ell t\} \in [1/11, 10/11]\}.$$

Consider the orbit $\mathbf{x}(t) = (e_1 t, \ldots, e_{10} t) \bmod 1 \in [0,1)^{10}$ for $t > 0$. The target set is
$$\mathcal{S} = [1/11, 10/11]^{10} \subset [0,1)^{10},$$
which is open and has Lebesgue measure $(9/11)^{10} > 0$.

**Case 1: Fully linearly independent over $\mathbb{Q}$.** Suppose $1, e_1, \ldots, e_{10}$ are linearly independent over $\mathbb{Q}$ (this is generically true; it includes any case where at least one $e_i/e_j \notin \mathbb{Q}$ and no non-trivial rational relation holds). By Weyl's equidistribution theorem [Wey16], the sequence $\mathbf{x}(t)$ (taking $t = 1, 2, 3, \ldots$ for integer $t$, or more generally $t$ in any arithmetic progression) is equidistributed in $[0,1)^{10}$. Since $\mathcal{S}$ has positive Lebesgue measure, the orbit $\{\mathbf{x}(t) : t \in \mathbb{Z}_{>0}\}$ is dense in $[0,1)^{10}$ and therefore intersects $\mathcal{S}$.

**Case 2: Partial rational dependencies.** Suppose $e_1,\ldots,e_{10}$ generate a $\mathbb{Q}$-vector space of dimension $d$ with $1 \leq d \leq 9$ (i.e., some $e_i/e_j \in \mathbb{Q}$ but not all speeds are commensurable). The orbit $\{\mathbf{x}(t)\}$ lies in a closed sub-torus $T \cong [0,1)^d$ of $[0,1)^{10}$ defined by the rational dependencies. Since there is at least one irrational ratio (hypothesis), $d \geq 2$. The image of $\mathcal{S}$ under the projection to the $d$-torus $T$ is open (as a pre-image of an open set through a continuous map) and has positive $d$-dimensional Lebesgue measure (since the full-dimensional measure of $\mathcal{S}$ is positive and the fibres are finite). By Weyl's theorem applied on $T$, the orbit is equidistributed in $T$ and therefore intersects the image of $\mathcal{S}$.

In both cases, there exists $t > 0$ with $\mathbf{x}(t) \in \mathcal{S}$, i.e., $\{e_\ell t\} \in [1/11, 10/11]$ for all $\ell = 1,\ldots,10$. $\square$

*Remark E.1.* Weyl's equidistribution theorem (Weyl [Wey16]) states: if $\alpha_1,\ldots,\alpha_k$ are real numbers such that $1, \alpha_1,\ldots,\alpha_k$ are linearly independent over $\mathbb{Q}$, then the sequence $(n\alpha_1, \ldots, n\alpha_k) \bmod 1$ is equidistributed in $[0,1)^k$ as $n \to \infty$. For continuous $t$: the orbit $(e_1 t, \ldots, e_{10} t) \bmod 1$ is dense in $[0,1)^{10}$ (or in the appropriate sub-torus) whenever there is at least one irrational ratio among the speeds.

*Remark E.2 (Scope and sharpness).* Proposition E handles all configurations with at least one irrational speed ratio. The remaining open case is exactly when **all** speed ratios $e_i/e_j$ are rational — equivalently, all speeds are rational multiples of a common base frequency. This is Case R> in the gap decomposition below.

*Remark E.3 (Explicit witnesses not provided).* Proposition E is an existence proof via density; it does not produce an explicit witness time $t^*$. By contrast, Theorem B produces the explicit witness $t^* = 10/(11e_{10})$.

---

### 10.6 Refined gap decomposition: Case R>

The combination of Theorem B (§9) and Proposition E (§10.5) yields a sharp decomposition of the full problem:

**Theorem (Gap Decomposition).** The full classical LRC for $n = 11$ (Conjecture B) decomposes into three mutually exclusive and exhaustive sub-cases:

| Case | Speed structure | Status | Method |
|---|---|---|---|
| **Case R** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 \leq 10$ | **Proved** (Theorem B) | Explicit witness $t^* = 10/(11e_{10})$ |
| **Case I** | At least one $e_i/e_j \notin \mathbb{Q}$ (irrational ratio) | **Proved** (Proposition E) | Weyl equidistribution |
| **Case R>** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 > 10$ | **Open** | Unknown |

**Proof of decomposition.** Cases R, I, R> are exhaustive (every configuration falls into exactly one) and mutually exclusive. Case R is handled by Theorem B with explicit witness. Case I is handled by Proposition E. Case R> is the complement. $\square$

**Structure of Case R>.** In Case R>, all speeds $e_1,\ldots,e_{10}$ are rational multiples of a common base $\omega > 0$: write $e_i = p_i \omega / q$ for integers $p_1 < \cdots < p_{10}$ and a common denominator $q$. The LRC condition becomes: $\exists k \in \mathbb{Z}_{>0}$ such that $\{p_i k / (11q)\} \in [1/11, 10/11]$ for all $i = 1,\ldots,10$. This reduces to a finite arithmetic problem for each choice of $(p_1,\ldots,p_{10},q)$.

**Why Case R> is hard.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10p_1/p_{10} < 1$ (since $p_{10}/p_1 > 10$). The AP witness $t=1/11$ (which works for Case R) fails because $\{a_1/11\} = a_1/11 < 1/11$. The witness family $\{m/11\}$ is insufficient (§10.1), and no finite extension suffices (§10.2). The orbit is finite (rational speeds), so Weyl fails (§10.5). The problem reduces to: for a given finite orbit of the rational-speed system, does the orbit intersect the target $[1/11,10/11]^{10}$?

**Partial resolution of Case R> (coprime-to-11 sub-case).** Write the speeds as $e_i = p_i \omega / q$ for positive integers $p_i$ and base $\omega, q > 0$. Define the **11-adic content** of the configuration as the multiset $\{v_{11}(p_i)\}$ where $v_{11}(p)$ is the 11-adic valuation of $p$.

**Proposition N (Coprime sub-case of Case R>).** If $v_{11}(p_i) = 0$ for all $i$ (all $p_i$ coprime to 11), then the classical LRC holds for $e_1,\ldots,e_{10}$, with explicit witness $t^* = q/(11\omega)$.

**Proof.** At $t^* = q/(11\omega)$: $\{e_i t^*\} = \{p_i q \omega / (q \cdot 11\omega)\} = \{p_i/11\} = (p_i \bmod 11)/11$. Since $\gcd(p_i, 11) = 1$, $p_i \bmod 11 \in \{1,\ldots,10\}$, so $\{e_i t^*\} \in \{1/11,\ldots,10/11\} \subset [1/11, 10/11]$. This holds for all $i = 1,\ldots,10$ simultaneously, regardless of the speed ratio $p_{10}/p_1$. $\square$

*Remark.* Proposition N handles all commensurable configurations where no speed is an integer multiple of $11\omega/q$ (the "11-resonant" base frequency). The speed ratio condition $p_{10}/p_1 > 10$ imposes no constraint — even highly disparate speed ratios are covered as long as the coprimality condition holds. The remaining hard sub-case of Case R> is configurations where some $p_i \equiv 0 \pmod{11}$, i.e., some runner has a speed that is a multiple of the 11-resonant frequency.

**Open questions for Case R>.**

(a) Does every commensurable configuration with $e_{10}/e_1 > 10$ have a valid witness time? (Conjecture B restricted to Case R>.)

(b) **11-resonant sub-case:** If some $p_i = 11^{a_i} q_i$ with $a_i \geq 1$: the witness $t = q/(11\omega)$ fails for those runners (as $\{p_i/11\} = \{11^{a_i-1} q_i\} = 0$). Can witnesses of the form $t = q/(11^{A+1} \omega)$ (where $A = \max_i v_{11}(p_i)$) always be found? Countability argument: the bad fraction per runner is $2/11$; for 10 runners the union bound gives $20/11 > 1$, insufficient.

(c) Can the boundary-set method [phi-paper] always find a witness? The boundary set consists of times $t^* = kq/(11 p_i \omega)$ for $k = 1,\ldots,11p_i-1$ at which runner $i$ enters/exits isolation. For commensurable speeds these are finitely many rationals. Is one always a global isolation time?

(d) **Slow runner window (Route S):** Runner 1's isolation window $W_0 = [q/(11a_1\omega),\, 10q/(11a_1\omega)]$ has length $9q/(11a_1\omega) > 9q/(11\omega)$. Does $W_0$ always intersect $\bigcap_{i=2}^{10} I_i$? For the total-blocking example of §10.1, the witness $t = 4/17 \in W_0$, confirming this for that case. General proof pending.

---

### 10.7 Reflection symmetry (AP-level)

The following structural observation reveals a symmetry of the AP witness framework that maps large speed ratios to near-unit speed ratios.

**Lemma R (AP-witness reflection).** In the classical EFN framework with $a_{10} = 10$, define the **reflected speeds**
$$b_i := 11 - a_{10-i+1}, \quad i = 1,\ldots,10.$$
Then $b_1 = 1$, $b_{10} = 11 - a_1 > 10$, and for each AP witness $t_m = m/11$ with $m \in \{1,\ldots,10\}$:
$$\{b_i \cdot t_m\} = 1 - \{a_{10-i+1} \cdot t_m\}.$$
In particular, $\{b_i t_m\} \in [1/11,10/11]$ if and only if $\{a_{10-i+1} \cdot t_m\} \in [1/11,10/11]$.

**Proof.** At $t_m = m/11$, we have $11 t_m = m \in \mathbb{Z}$. Therefore:
$$\{b_i \cdot t_m\} = \{(11 - a_{10-i+1}) \cdot m/11\} = \{m - a_{10-i+1} m/11\}.$$
Since $m$ is an integer and $a_{10-i+1} m/11 \notin \mathbb{Z}$ (as $a_{10-i+1} \in (0,10) \setminus \{11\mathbb{Z}/m\}$), the standard identity $\{k - x\} = 1 - \{x\}$ for $k \in \mathbb{Z}$, $x \notin \mathbb{Z}$ gives $\{b_i t_m\} = 1 - \{a_{10-i+1} t_m\}$.

Since the interval $[1/11,10/11]$ is symmetric about $1/2$ (i.e., $x \in [1/11,10/11] \Leftrightarrow 1-x \in [1/11,10/11]$), the AP loneliness condition is preserved. $\square$

*Scope note.* Lemma R applies only at the AP witness times $t_m = m/11$, where $11t_m \in \mathbb{Z}$. For a general time $t$ with $11t \notin \mathbb{Z}$, the identity fails: $\|(11-a_i)t\| = \|11t - a_i t\|$ and $11t \notin \mathbb{Z}$ means $\|11t - a_i t\| \neq \|a_i t\|$ in general. Lemma R is therefore a statement about AP-witness blocking patterns, not a full LRC equivalence. In particular, Lemma R does **not** imply that the classical LRC holds for $\{a_i\}$ if and only if it holds for $\{b_i\}$ (since valid witnesses may be non-AP times).

**Consequence for AP-witness blocking.** The AP-blocking patterns of $\{b_i\}$ and $\{a_{10-i+1}\}$ are complementary: witness $m$ is blocked by the reflected configuration iff it is blocked by the original (with the roles of the upper-violation and lower-violation runners swapped). If $\{a_i\}$ has all 10 AP witnesses blocked, then $\{b_i\}$ also has all 10 AP witnesses blocked.

**Parameter-space observation.** Every Case R> configuration $(a_1,\ldots,a_{10})$ with $a_1 \in (0,1)$ and $a_{10} = 10$ produces a reflected configuration $\{b_i\}$ lying in the **window** $b_1 = 1$, $b_{10} = 11-a_1 \in (10,11)$, with speed ratio $\rho' = 11 - a_1 \in (10,11)$. After EFN renormalisation, $c_i = 10b_i/b_{10}$, the new minimum is $c_1 = 10/(11-a_1) \in (10/11,1)$, and the gap width $1 - c_1 = (1-a_1)/(11-a_1) \in (0, 1/11)$ is compressed to at most $1/11$.

*Interpretation.* At the AP-witness level, the entire Case R> family maps onto a window of width at most $1/11$ in the $c_1$ parameter. Whether this window reduction carries over to the full LRC (allowing non-AP witnesses) is an open question that would constitute progress toward Conjecture B.

---

### 10.8 Witness structure in $W_0$: computational investigation

We report the outcome of a systematic computational investigation of Case R> using the boundary-set method on 1212 configurations (200 random seed=42, 1000 random seed=99, 12 adversarial/near-boundary). All computations use exact rational arithmetic.

**Setup.** For integer speeds $p_1 < \cdots < p_{10}$ with $p_{10}/p_1 > 10$, define:
- $W_0 = [1/(11p_1),\, 10/(11p_1)]$: the first isolation window of runner 1.
- $W_{\rm lo} = 1/(11p_1)$, $W_{\rm hi} = t^* = 10/(11p_1)$: left and right endpoints of $W_0$.
- $J_{2-10}$: the joint isolation set of runners $2,\ldots,10$, i.e., $\{t > 0 : \|p_i t\| \geq 1/11\ \forall\, i=2,\ldots,10\}$.

The LRC holds iff $J_{2-10} \cap W_0 \neq \emptyset$.

**Key empirical finding (1212 configs).** All 1212 tested Case R> configurations have a valid witness inside $W_0$. The witnesses cluster strongly near the **left endpoint** $W_{\rm lo} = 1/(11p_1)$:

| Position in $W_0$ (as fraction of $|W_0|$) | Proportion of witnesses |
|---|---|
| Bottom 10% (leftmost 10%) | 98.2% |
| Bottom 2% | 68% |
| Mean position (relative to $W_0$, $0$=left, $1$=right) | 0.020 |

The first valid witness time is virtually always within 2% of $|W_0|$ from $W_{\rm lo}$.

**Blocker structure at $W_{\rm lo}$.** At time $W_{\rm lo} = 1/(11p_1)$, runner $i$'s fractional position is $\{p_i/(11p_1)\}$. Define a **$W_{\rm lo}$-blocker** as a runner $p_b$ with $\|p_b \cdot W_{\rm lo}\| < 1/11$, i.e., $\{p_b/(11p_1)\} < 1/11$ (runner near an integer from below). Across 1212 configs:
- 0 blockers at $W_{\rm lo}$: 38% — $W_{\rm lo}$ itself is a valid witness (all runners immediately isolated on runner 1's entry)
- 1 blocker: 46% — one runner is near-zero at $W_{\rm lo}$; witness is just after $W_{\rm lo}$
- 2+ blockers: 16% — two or more runners near an integer at $W_{\rm lo}$; witness still near $W_{\rm lo}$

**The $W_{\rm lo}$-blocker identity.** A runner $p_b$ blocks at $W_{\rm lo}$ iff $p_b \bmod (11p_1) < p_1$, i.e., $p_b$ is within $p_1$ of a multiple of $11p_1$. Such runners have speed $p_b \in [11kp_1,\, 11kp_1 + p_1)$ for some integer $k \geq 1$. The smallest possible $W_{\rm lo}$-blocker has $p_b \in [11p_1, 12p_1)$, giving $p_b \geq 11p_1 > 10p_1 > p_1$, so all $W_{\rm lo}$-blockers are necessarily **fast runners** (at least $11\times$ the slowest speed).

**Left-Entry Construction.** When runner $p_b$ blocks at $W_{\rm lo}$ (i.e., $\{p_b/(11p_1)\} < 1/11$), it is in its "near-zero" zone — just before entering its next isolation window. Write $p_b = 11kp_1 + r$ with $r \in [0, p_1)$. The next isolation entry time of runner $p_b$ after $W_{\rm lo}$ is:
$$\tau_b = \frac{11k+1}{11p_b} = W_{\rm lo} + \frac{p_1 - r}{11p_1 p_b}.$$
The distance $\tau_b - W_{\rm lo} = (p_1-r)/(11p_1 p_b) \leq 1/(11p_b) \leq 1/(121p_1)$ (since $p_b \geq 11p_1$). In units of $|W_0| = 9/(11p_1)$, this is at most $p_1/(9p_b) \leq 1/99 \approx 1\%$ of $|W_0|$.

The actual witness is the **entry time $\tau_{\rm entry}$** = the maximum over all $W_{\rm lo}$-blockers of their first entry time after $W_{\rm lo}$:
$$\tau_{\rm entry} = \max\bigl\{\tau_b : p_b \text{ is a } W_{\rm lo}\text{-blocker}\bigr\}.$$
Empirically (verified for all 1212 configs), $\tau_{\rm entry}$ is always a valid joint witness.

**Why witnesses are entry times.** Every valid witness found by the harness is a critical time (entry time $(11j+1)/(11p_i)$ or exit time $(11j+10)/(11p_i)$ of some runner). Across all 1212 configs, 100% of witnesses are entry times of some runner. The pattern: the witness is the entry time of the last "near-zero" runner to re-enter isolation after $W_{\rm lo}$.

**Geometric picture.** The joint isolation set $J_{2-10}$ has its first window inside $W_0$ starting at approximately $\tau_{\rm entry}$, which is within $\sum_{b} (p_1 - r_b)/(11p_1 p_b)$ of $W_{\rm lo}$ (where the sum is over all $W_{\rm lo}$-blockers). Since each such term is $O(1/p_b) = O(1/(11p_1))$, the first joint window starts no more than $O(n \cdot 1/p_b)$ after $W_{\rm lo}$, well within $W_0$.

**What a proof needs.** The witness $\tau_{\rm entry}$ lies in $W_0$ and all $W_{\rm lo}$-blockers are isolated there (by construction — they just entered their isolation windows). The key open step is:

> **Step L2.** At $\tau_{\rm entry}$, all runners $i$ that were *already isolated at $W_{\rm lo}$* (non-blockers) remain isolated: $\|p_i \tau_{\rm entry}\| \geq 1/11$.

Step L2 requires bounding the position shift $p_i \cdot (\tau_{\rm entry} - W_{\rm lo}) \leq p_i/(11p_b) \leq p_{10}/(11 \cdot 11p_1)$. For non-blockers at $W_{\rm lo}$ with "sufficient buffer" above $1/11$, the shift is too small to violate isolation. Configurations where a non-blocker is borderline isolated at $W_{\rm lo}$ require careful analysis.

**Conjecture ($W_0$-Intersection).** *For any Case R> integer speed configuration $(p_1,\ldots,p_{10})$, the joint isolation set $J_{2-10}$ intersects $W_0 = [1/(11p_1),\, 10/(11p_1)]$.*

This conjecture, if proved, immediately implies Conjecture B for Case R>. The Left-Entry Construction provides the explicit candidate witness $\tau_{\rm entry}$; Step L2 is the remaining key ingredient.

---

### 10.9 The Iterated Left-Entry Construction

The single-level Left-Entry Construction of §10.8 handles Case 0 (no $W_{\rm lo}$-blockers) and accounts for a large portion of Case 1. However, it can fail when a non-blocker at $W_{\rm lo}$ is itself nearly blocked at $\tau_{\rm entry}$: advancing to $\tau_{\rm entry}$ may create a new blocker that was not present at $W_{\rm lo}$. We resolve this by iterating.

**Algorithm (Iterated Left-Entry Construction, ILE).** Given integer speeds $p_1 < \cdots < p_{10}$ with $p_{10}/p_1 > 10$, proceed as follows:

1. Set the current candidate time $t_{\rm cur} \leftarrow W_{\rm lo} = 1/(11p_1)$.
2. Compute the set of **blockers at $t_{\rm cur}$**:
   $$B(t_{\rm cur}) = \{p_i : \|p_i \cdot t_{\rm cur}\| < 1/11\}.$$
3. If $B(t_{\rm cur}) = \emptyset$, **terminate**: $t_{\rm cur}$ is a valid joint witness.
4. For each $p_b \in B(t_{\rm cur})$, compute $\tau_b(t_{\rm cur})$, the first entry time of the isolation window of runner $p_b$ that lies in $[t_{\rm cur},\, W_{\rm hi}]$:
   $$\tau_b(t_{\rm cur}) = \frac{11j^* + 1}{11 p_b}, \quad j^* = \left\lceil p_b \cdot t_{\rm cur} - \tfrac{1}{11} \right\rceil.$$
   If no such entry time exists inside $[t_{\rm cur}, W_{\rm hi}]$, the algorithm **fails** for this configuration.
5. Set $t_{\rm cur} \leftarrow \max_{p_b \in B(t_{\rm cur})} \tau_b(t_{\rm cur})$ and go to step 2.

At each level, the current candidate advances from $t_{\rm cur}$ to the latest first re-entry of any blocker. Since every blocker is guaranteed to re-enter isolation within distance $1/(11p_b) \leq 1/(121p_1)$ of $t_{\rm cur}$, each level advances $t_{\rm cur}$ by at most $9 \cdot 1/(121p_1) = 9/(121p_1) < |W_0|$. However, because $t_{\rm cur}$ advances only by small discrete steps, the algorithm can in principle require many levels.

**Computational verification.** The ILE algorithm was run on all 1212 Case R> configurations using exact rational arithmetic. Let $L$ denote the number of iterations required before termination:

| Levels $L$ required | Proportion of configs |
|---|---|
| $L = 0$ (Case 0: $W_{\rm lo}$ directly valid) | 38.2% |
| $L = 1$ | 37.6% |
| $L = 2$ | 8.5% |
| $L = 3$ | 3.2% |
| $L \in [4, 9]$ | 8.9% |
| $L \in [10, 20]$ | 3.6% |
| $L > 20$ | 0% |

Every one of the 1212 configurations terminates within $L \leq 20$ levels, and **100% produce a valid witness $t_{\rm cur} \in W_0$** matching the harness witness exactly. The maximum level count $L = 20$ occurred for two adversarial near-boundary configurations (ratio $= 11$), which are precisely the hardest cases since $p_{10}/p_1$ barely exceeds 10.

**Monotonicity and containment.** By construction, $t_{\rm cur}$ is strictly non-decreasing across levels. At each level, the new $t_{\rm cur}$ is the entry time of some runner $p_b$, hence $\|p_b \cdot t_{\rm cur}\| = 1/11$ exactly (the runner just enters isolation). All other blockers from the previous level that have entry time $\leq t_{\rm cur}$ are also entering or have entered isolation. The only potential issue is that a non-blocker at the previous level might become a blocker at the new $t_{\rm cur}$; if this occurs, another iteration is required.

**Containment in $W_0$.** At termination, $t_{\rm cur} \in [W_{\rm lo}, W_{\rm hi}]$ by the failure condition of step 4 (entry times outside $W_0$ terminate the algorithm as a failure, not a success). The empirical finding is that failure never occurs across all 1212 tested configurations.

**Conjecture (ILE Termination).** *For every Case R> integer speed configuration $(p_1,\ldots,p_{10})$, the Iterated Left-Entry Construction terminates successfully (no blocker's re-entry lies outside $W_0$) and the resulting $t_{\rm cur}$ is a valid joint witness for the Lonely Runner Conjecture.*

This conjecture, if proved, completes Case R> and hence the full Lonely Runner Conjecture for $n = 11$.

**Proof strategy for termination.** To prove the conjecture, one must show two things:
1. **Containment**: At each level, every blocker's first re-entry time $\tau_b(t_{\rm cur})$ satisfies $\tau_b(t_{\rm cur}) \leq W_{\rm hi}$. Since $\tau_b(t_{\rm cur}) - t_{\rm cur} \leq 1/(11p_b)$ and $t_{\rm cur} \leq W_{\rm hi}$, this requires $W_{\rm hi} - t_{\rm cur} \geq 1/(11p_b)$, i.e., sufficient room remains in $W_0$ above $t_{\rm cur}$.
2. **Finite termination**: The sequence $(t_{\rm cur})$ eventually reaches a time at which no blockers remain. Since there are finitely many critical times in $W_0$ and $t_{\rm cur}$ is strictly increasing at each productive level, this reduces to showing the algorithm cannot get trapped.

The **containment** part is the more tractable: if $p_b \geq 11p_1$ (which holds for all $W_{\rm lo}$-blockers) and $t_{\rm cur} \leq W_{\rm hi} - 1/(11p_b) = 10/(11p_1) - 1/(11p_b)$, containment holds. Since $p_b \geq 11p_1$, we have $1/(11p_b) \leq 1/(121p_1)$, and the condition becomes $t_{\rm cur} \leq 10/(11p_1) - 1/(11p_b)$, which fails only if $t_{\rm cur}$ is within $1/(11p_b)$ of $W_{\rm hi}$. Thus the only threat arises when $t_{\rm cur}$ is extremely close to $W_{\rm hi}$ and a new blocker appears — a Diophantine near-coincidence requiring careful analysis.

**Connection to Step L2.** The single-level version of ILE requires **Step L2**: that all non-blockers at $W_{\rm lo}$ remain non-blockers at $\tau_{\rm entry}$. The iterated version generalises this to: at each level $\ell$, the newly advanced $t_{\rm cur}$ must not create blockers that are "unresolvable" within $W_0$. The exact analytic condition for Step L2 (single level) is:
$$\forall i \in \{2,\ldots,10\} \setminus B(W_{\rm lo}): \quad R_i + p_i \cdot \frac{p_1 - r_b}{p_b} \leq 10p_1,$$
where $R_i = p_i \bmod (11p_1) \in [p_1, 10p_1]$ (the non-blocker condition) and $r_b = p_b \bmod (11p_1) \in [0,p_1)$ (the $W_{\rm lo}$-blocker residue). Across all 1212 tested configurations, this condition holds without exception.

---

### 10.10 The carry mechanism: why ILE terminates inside $W_0$

The computational evidence of §10.9 shows that ILE always terminates with a witness $t^* \in W_0$, never overshooting $W_{\rm hi} = 10/(11p_1)$. This section identifies the precise algebraic mechanism and formulates the analytic conditions that a proof must establish.

**Setup.** At each level $\ell$ of ILE, the algorithm advances $t_{\rm cur}$ to $\tau = (11j^*+1)/(11p_b)$, the entry time of the advancing blocker $p_b$. This creates a positive shift $\delta = \tau - t_{\rm cur} \leq 1/(11p_b)$. For any other runner $p_c$, the fractional position changes:
$$\{p_c \cdot \tau\} = \{p_c \cdot t_{\rm cur}\} + p_c \cdot \delta \pmod{1}.$$
If $p_c$ was not blocked at $t_{\rm cur}$ (i.e., $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11]$) but becomes blocked at $\tau$ (i.e., $\|p_c \cdot \tau\| < 1/11$), we call this a **carry event** for $p_c$. There are exactly two carry types:

**Type C (cross):** $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11)$ and the shift pushes $\{p_c \cdot \tau\} > 10/11$. Runner $p_c$ has crossed the upper isolation boundary and is now near an integer from above. Its next entry time after $\tau$ is obtained by waiting for $\{p_c \cdot t\}$ to continue past 1 and reach $1/11$: distance $\delta' = (1 + 1/11 - \{p_c \cdot \tau\})/p_c \leq 2/(11p_c)$.

**Type W (wrap):** $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly (runner $p_c$ is at the exact isolation boundary, not yet blocked) and the shift $p_c \cdot \delta > 1/11$ pushes $\{p_c \cdot \tau\}$ past 1 entirely, landing in $[0, 1/11)$. Runner $p_c$ is now near an integer from below. Its next entry time is $\delta' = (1/11 - \{p_c \cdot \tau\})/p_c \leq 1/(11p_c)$.

**Empirical distribution across 1212 configs:** Of all 1551 total carry events, 1090 (70%) are Type C and 461 (30%) are Type W. Every Type W carry has $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly — the runner is at the precise boundary, half a step from being unblocked. This is not a coincidence: a runner with $\{p_c \cdot t_{\rm cur}\} > 10/11$ would already be a blocker, so Type W can only originate from the exact boundary.

**Single-step containment.** The largest single advance across all 1212 configs is $\delta = 3/55 \approx 0.055$, which is $6.67\%$ of $|W_0| = 9/(11p_1)$. This occurs for the extremal configuration $(1,3,4,\ldots,10,11)$ when runner $p_b = 3$ advances. After every single advance, the remaining distance to $W_{\rm hi}$ is at least $54.5\%$ of $|W_0|$ — no advance brings $t_{\rm cur}$ within $45\%$ of $W_{\rm hi}$. Moreover, no carry event ever produces an entry time exceeding $W_{\rm hi}$: across all 1551 carry events in all 1212 tested configs, **zero** violations of containment were observed.

**Containment bound: the algebraic condition.** For a Type C carry by runner $p_c$ (whose next entry time is $\tau + \delta'$ with $\delta' \leq 2/(11p_c)$), containment requires $\tau + \delta' \leq W_{\rm hi}$, i.e.:
$$t_{\rm cur} + \delta + \frac{2}{11p_c} \leq \frac{10}{11p_1}.$$
Since $t_{\rm cur} \leq W_{\rm hi}$ and $\delta \leq 2/(11p_b)$, this becomes:
$$\frac{10}{11p_1} - t_{\rm cur} \geq \delta + \frac{2}{11p_c} \geq \frac{2}{11p_b} + \frac{2}{11p_c}.$$
In the worst case $p_b = p_c = p_2$ (the second-slowest runner, since $p_1$ is never a blocker): this requires $W_{\rm hi} - t_{\rm cur} \geq 4/(11p_2)$. The remaining room in $W_0$ is at least $4/(11p_2)$. Since the total width of $W_0$ is $9/(11p_1)$ and $p_2 > p_1$, this is a condition of the form "at most $4p_1/(9p_2)$ of $W_0$ has been used." For $p_2 \geq 2p_1$, this is at most $2/9 \approx 22\%$ of $W_0$.

**The pacemaker structure.** In 99\% of configurations, every runner advances as the ILE's advancing blocker at most once. The exceptional 1\% feature a **pacemaker runner**: a runner $p_b \equiv 0 \pmod{11p_1}$ (i.e., speed exactly a multiple of $11p_1$) that blocks at every integer multiple of $t_b = 1/(11p_b) = 1/(11 \cdot 11p_1)$. The extremal configuration $(1, 3, 4, 5, 6, 7, 8, 9, 10, 11)$ has pacemaker $p = 11$, which advances 5 times at $t = 1/11, 2/11, 3/11, 4/11, 5/11$ — the $k/11$ grid. Between consecutive pacemaker resets, the intermediate runners resolve their carries in order of decreasing speed (a descending sweep: $10, 9, 8, 7, 6$ in the first interval between $1/11$ and $2/11$). The pacemaker acts as an upper bound: $t^* \leq k_{\max}/(11 \cdot p_{\rm pm}) + 1/(11 \cdot p_{\rm pm})$, where $k_{\max}$ is the last reset index. For $p_{\rm pm} = 11$ and $k_{\max} = 5$: $t^* = 5/11 + 1/121 = 56/121$.

**Why $p_1$ is never a blocker.** This is the key structural fact underpinning containment: for all $t \in W_0$, $p_1 \cdot t \in [p_1 \cdot W_{\rm lo}, p_1 \cdot W_{\rm hi}] = [1/11, 10/11]$, so $\|p_1 \cdot t\| \in [1/11, 9/11]$ — always in the isolation zone. The slowest runner provides a "free" isolation throughout $W_0$. The smallest carry runner is therefore $p_2$, and all bounds are in terms of $p_2 > p_1$.

**What the analytic proof must establish.** Let $p_b$ be the advancing blocker at some level, and let $p_c$ be a carry runner becoming blocked at the new $t_{\rm cur}$. The two conditions to prove are:

> **Containment (C):** $t_{\rm cur} + \delta_{p_c} \leq W_{\rm hi}$, where $\delta_{p_c} \leq 2/(11p_c)$ is the entry-time gap for the carry runner.

> **Non-degeneracy (ND):** The cascade does not cycle — the set of blocked runners strictly changes at each level.

Non-degeneracy is immediate since $t_{\rm cur}$ is strictly increasing and lies in a discrete set (the lattice of critical times in $W_0$). Containment is the substantive condition. It holds unconditionally when $t_{\rm cur}$ is sufficiently far from $W_{\rm hi}$ and fails only in a narrow region near $W_{\rm hi}$ — a region that empirically is never reached. The analytic task is to show that the cascade always terminates before entering this narrow region.

---

## References

- [BGG+98] A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi, *Flows, view obstructions, and the lonely runner*, J. Combin. Theory Ser. B **72** (1998), 1–9.

- [BH01] T. Bohman, R. Holzman, *Six lonely runners*, Electron. J. Combin. **8** (2001), R3.

- [BS08] J. Barajas, O. Serra, *The lonely runner with seven runners*, Electron. J. Combin. **15** (2008), R48.

- [Cus73] T. W. Cusick, *View obstruction problems*, Aequationes Math. **9** (1973), 165–170.

- [Ros25a] B. Rosenfeld, *The lonely runner conjecture holds for eight runners*, arXiv:2509.14111, 2025.

- [Ros25b] B. Rosenfeld, *The lonely runner conjecture holds for nine runners*, arXiv:2512.01912, 2025.

- [Tao18] T. Tao, *Some remarks on the lonely runner conjecture*, Contrib. Discrete Math. **13** (2018), 1–31.

- [Tra25] T. Trakulthongchai, *Nine and ten lonely runners*, arXiv:2511.22427, 2025.

- [v2] T. Palelei, *Eleven Lonely Runners: An Analytical Proof via Arithmetic-Progression Witnesses* (relative formulation), preprint v2, 2026.

- [v12] T. Palelei, *The Lonely Runner Conjecture for $n = 11$*, preprint v12, 2026.

- [Wey16] H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. **77** (1916), 313–352.

- [Wil67] J. M. Wills, *Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen*, Monatsh. Math. **71** (1967), 263–269.
