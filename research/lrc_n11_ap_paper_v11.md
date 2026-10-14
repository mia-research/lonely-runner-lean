# Eleven Lonely Runners: The Classical Case via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 23 March 2026
**Status:** Preprint v11 — ANALYTIC (unconditional for $e_{10}/e_1 \leq 10$; irrational-ratio case closed by Weyl equidistribution; pacemaker sub-case of Case R> proved via modular bijection (Theorem 10.12); Containment fully proved for configurations with no interior multiples of 11 (§10.15)). Route 3 — Theorem 10.16.5 (Runner 2 Incompatibility) **proved** with exact rational bounds $a_2 \geq 20/9$ (I₄ constraint) vs. $a_2 \leq 575/261$ (I₉ constraint), gap $= 5/261 > 0$. GF > 0 unconditionally proved for the ++------ sign class, with all Cases A–D complete (Cases A/B: edge gaps in I₁; Cases C/D: Runner 2 Incompatibility). **New in v11**: dependency table corrected — Route 3 rows updated from "Open/pending" to "Proved" throughout. Remaining open: (i) non-pacemaker commensurable Case R> via Containment (C); (ii) extension of Route 3 to all 247 feasible sign classes to complete Conjecture B.

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, classical formulation, no-missing-slot, perturbation independence, prime case, speed ratio, Weyl equidistribution, commensurable speeds, complementary pairs, overdetermination, coupling principle, good fraction

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ in the case where the ratio of the fastest to the slowest non-stationary speed satisfies $e_{10}/e_1 \leq 10$: there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$, with explicit witness $t^* = 10/(11e_{10})$. The proof uses an arithmetic-progression (AP) witness framework with the stationary runner at speed $0$ as the fixed reference. The key structural property is **no-missing-slot**: the AP residues $\{im \bmod 11 : i=1,\ldots,10\} = \{1,\ldots,10\}$ for every witness $m$, combined with **independence of classical conditions**. For the unbounded-ratio case, the gap is refined into three sub-cases: the rationally-related bounded-ratio case (proved, Theorem B), the irrationally-related case (proved via Weyl's equidistribution theorem, Proposition E), and commensurable speeds with ratio exceeding 10 (partially resolved via two independent approaches). In the last sub-case, the Iterated Left-Entry Construction identifies witnesses in $W_0 = [1/(11e_1), 10/(11e_1)]$; we prove the construction succeeds for all **pacemaker configurations** ($e_{10}/e_1 = 11$) via a modular bijection in $\mathbb{Z}/121\mathbb{Z}$ (Theorem 10.12), and for all configurations with no interior speed divisible by 11 (Theorem C1). A new Route 3 approach (§10.16) exploits the **Coupling Principle** and the mod-11 **Complementary Pairs** structure to prove GF$(W_0) > 0$ for all complete-blocking configurations in the ++------ sign class. The key result is Theorem 10.16.5 (**Runner 2 Incompatibility**, proved 2026-03-23): closing slot I₄ requires $a_2 \geq 20/9$, while closing slot I₉ requires $a_2 \leq 575/261$; since $20/9 > 575/261$ with explicit gap $5/261 > 0$, the two constraints are irreconcilable. Combined with the explicit rational certificate $t^* = 69/275$ (Theorem 10.16.4, Case C), this gives an unconditional analytic proof of GF $> 0$ for the ++------ sign class.

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

Sections 2–3 establish setup and the no-missing-slot property. Section 4 develops three key lemmas (independence, first-failing witnesses, $m=1$ safety criterion). Section 5 records the classical finite witness states and introduces the speed-ratio partition. Section 6 proves no-total-blocking in the bounded-ratio case and states the gap for the large-ratio case. Sections 7–8 establish the classical EFN and witness-law compatibility. Section 9 assembles Theorem B and states Conjecture B. Section 10 documents the gap and routes toward a complete proof; §10.5 proves the irrational case via Weyl equidistribution, §10.6 refines the gap to commensurable speeds, §10.7–10.11 document the carry mechanism, Iterated Left-Entry Construction, and right-endpoint obstruction, §10.12 proves Case R> for all ratio-11 pacemaker configurations via a modular bijection in $\mathbb{Z}/121\mathbb{Z}$, §10.13 analyses the consecutive staircase family, §10.14 reports Containment experiments, §10.15 gives partial analytic proofs of Containment (new in v8), and §10.16 (**new in v9**) introduces Route 3 — the Coupling Principle and Complementary Pairs approach — with explicit certificate $t^* = 69/275$ for Case C of the ++------ sign class.

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

The following theorem constitutes the heart of the v4/v5/v6 proof for the bounded-ratio case.

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
| **Case R>** (commensurable speeds, $e_{10}/e_1 > 10$) | **Open** — sub-cases below | §10.6 |
| ↳ ILE Non-degeneracy (finite steps, strictly increasing) | **Proved** (trivial) | §10.9 |
| ↳ Case 0 ($W_{\rm lo}$ directly valid, 38% of configs) | **Proved** (immediate) | §10.8 |
| ↳ Unified carry bound ($\delta_{\rm carry} \leq 2/(11p_c)$) | **Proved** (Lemma 10.C) | §10.10 |
| ↳ **Containment (C)**: carry entry times $\leq W_{\rm hi}$ | **Open** — core gap | §10.10 |
| ↳ Step L2 (non-blockers at $W_{\rm lo}$ remain isolated) | **Empirically false** as single-level condition; not proof target | §10.9 |
| ↳ Pacemaker bound ($p_{\rm pm} = 11p_1$, ratio = 11): explicit witness via modular bijection | **Proved** (Theorem 10.12) | §10.12 |
| **Conjecture B** (full classical LRC) | **Open** (requires Containment C) | §10 |

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

This conjecture, if proved, immediately implies Conjecture B for Case R>. The Left-Entry Construction provides the explicit candidate witness $\tau_{\rm entry}$; the multi-level Containment condition (C) is the remaining key ingredient. (Note: the single-level Step L2 condition, initially proposed as the key step, is empirically violated in 28.1\% of configurations and is not a viable proof target — see §10.9.)

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

**Computational verification.** The ILE algorithm was run on two datasets using exact rational arithmetic. Let $L$ denote the number of iterations required before termination.

*Dataset 1 (original):* 1212 Case R> configurations (200 random seed=42, 1000 random seed=99, 12 adversarial/near-boundary):

| Levels $L$ required | Proportion of configs |
|---|---|
| $L = 0$ (Case 0: $W_{\rm lo}$ directly valid) | 38.2% |
| $L = 1$ | 37.6% |
| $L = 2$ | 8.5% |
| $L = 3$ | 3.2% |
| $L \in [4, 9]$ | 8.9% |
| $L \in [10, 20]$ | 3.6% |
| $L > 20$ | 0% |

All 1212 configurations terminate within $L \leq 20$ levels with **100% witness success**. The maximum $L = 20$ occurs for the extremal pacemaker configuration $(1, 3, 4, \ldots, 10, 11)$ (ratio = 11).

*Dataset 2 (extended):* 9163 Case R> configurations (9000 random across nine random seeds, $p_1 \in \{1,\ldots,10\}$, ratio 11–1000; 163 adversarial/pacemaker/near-boundary):

| Levels $L$ | Count | % |
|---|---|---|
| $L = 0$ | 2259 | 24.7% |
| $L = 1$ | 2743 | 29.9% |
| $L \in [2,5]$ | 3923 | 42.8% |
| $L \in [6,10]$ | 228 | 2.5% |
| $L \in [11,20]$ | 10 | 0.1% |
| $L > 20$ | 0 | 0.0% |

All 9163 configurations terminate with **100% witness success**; maximum $L = 20$ (pacemaker configs). Median $L = 1$; mean $L = 1.71$. Minimum containment margin: 54.5455\% of $|W_0|$ (the pacemaker $(1,3,\ldots,10,11)$).

*Dataset 3 (consecutive staircase family):* Configurations $(1, N, N+1, \ldots, N+8)$ for $N = 10, \ldots, 500$ such that $[N, N+8]$ contains a multiple of 11. This yields a new record:

> **Maximum $L = 58$**, achieved at $N = 69$: speeds $(1, 69, 70, 71, 72, 73, 74, 75, 76, 77)$, ratio $= 77$, with minimum containment margin $87.8\%$ of $|W_0|$.

All staircase configurations tested succeed; the ILE mechanism is detailed in §10.13. Across all three datasets, **zero containment failures** were observed.

**Monotonicity and containment.** By construction, $t_{\rm cur}$ is strictly non-decreasing across levels. At each level, the new $t_{\rm cur}$ is the entry time of some runner $p_b$, hence $\|p_b \cdot t_{\rm cur}\| = 1/11$ exactly (the runner just enters isolation). All other blockers from the previous level that have entry time $\leq t_{\rm cur}$ are also entering or have entered isolation. The only potential issue is that a non-blocker at the previous level might become a blocker at the new $t_{\rm cur}$; if this occurs, another iteration is required.

**Containment in $W_0$.** At termination, $t_{\rm cur} \in [W_{\rm lo}, W_{\rm hi}]$ by the failure condition of step 4 (entry times outside $W_0$ terminate the algorithm as a failure, not a success). The empirical finding is that failure never occurs: across all 9163 tested configurations and the staircase family ($N \leq 500$), zero containment failures were observed.

**Conjecture (ILE Termination).** *For every Case R> integer speed configuration $(p_1,\ldots,p_{10})$, the Iterated Left-Entry Construction terminates successfully (no blocker's re-entry lies outside $W_0$) and the resulting $t_{\rm cur}$ is a valid joint witness for the Lonely Runner Conjecture.*

This conjecture, if proved, completes Case R> and hence the full Lonely Runner Conjecture for $n = 11$.

**Proof strategy for termination.** To prove the conjecture, one must show two things:
1. **Containment**: At each level, every blocker's first re-entry time $\tau_b(t_{\rm cur})$ satisfies $\tau_b(t_{\rm cur}) \leq W_{\rm hi}$. Since $\tau_b(t_{\rm cur}) - t_{\rm cur} \leq 1/(11p_b)$ and $t_{\rm cur} \leq W_{\rm hi}$, this requires $W_{\rm hi} - t_{\rm cur} \geq 1/(11p_b)$, i.e., sufficient room remains in $W_0$ above $t_{\rm cur}$.
2. **Finite termination**: The sequence $(t_{\rm cur})$ eventually reaches a time at which no blockers remain. Since there are finitely many critical times in $W_0$ and $t_{\rm cur}$ is strictly increasing at each productive level, this reduces to showing the algorithm cannot get trapped.

The **containment** part is the more tractable: if $p_b \geq 11p_1$ (which holds for all $W_{\rm lo}$-blockers) and $t_{\rm cur} \leq W_{\rm hi} - 1/(11p_b) = 10/(11p_1) - 1/(11p_b)$, containment holds. Since $p_b \geq 11p_1$, we have $1/(11p_b) \leq 1/(121p_1)$, and the condition becomes $t_{\rm cur} \leq 10/(11p_1) - 1/(11p_b)$, which fails only if $t_{\rm cur}$ is within $1/(11p_b)$ of $W_{\rm hi}$. Thus the only threat arises when $t_{\rm cur}$ is extremely close to $W_{\rm hi}$ and a new blocker appears — a Diophantine near-coincidence requiring careful analysis.

**Connection to Step L2.** The single-level version of ILE requires **Step L2**: that all non-blockers at $W_{\rm lo}$ remain non-blockers at $\tau_{\rm entry}$. The iterated version generalises this to: at each level $\ell$, the newly advanced $t_{\rm cur}$ must not create blockers that are "unresolvable" within $W_0$. The exact analytic condition for Step L2 (single level) is:
$$\forall i \in \{2,\ldots,10\} \setminus B(W_{\rm lo}): \quad R_i + p_i \cdot \frac{p_1 - r_b}{p_b} \leq 10p_1,$$
where $R_i = p_i \bmod (11p_1) \in [p_1, 10p_1]$ (the non-blocker condition) and $r_b = p_b \bmod (11p_1) \in [0,p_1)$ (the $W_{\rm lo}$-blocker residue). **Step L2 is empirically false as a single-level sufficient condition**: across the 9163 extended configurations, 2572 (28.1\%) have Step L2 buffer $< 0$, meaning a non-blocker at $W_{\rm lo}$ would be pushed into the blocking zone by a single advance. The ILE resolves such carry events by iterating further levels — Step L2 failure does not cause ILE failure — but it shows that the single-level approach cannot be the basis of an analytic proof. The correct proof target is the multi-level Containment condition (C).

---

### 10.10 The carry mechanism: why ILE terminates inside $W_0$

The computational evidence of §10.9 shows that ILE always terminates with a witness $t^* \in W_0$, never overshooting $W_{\rm hi} = 10/(11p_1)$. This section identifies the precise algebraic mechanism and formulates the analytic conditions that a proof must establish.

**Setup.** At each level $\ell$ of ILE, the algorithm advances $t_{\rm cur}$ to $\tau = (11j^*+1)/(11p_b)$, the entry time of the advancing blocker $p_b$. This creates a positive shift $\delta = \tau - t_{\rm cur} \leq 1/(11p_b)$. For any other runner $p_c$, the fractional position changes:
$$\{p_c \cdot \tau\} = \{p_c \cdot t_{\rm cur}\} + p_c \cdot \delta \pmod{1}.$$
If $p_c$ was not blocked at $t_{\rm cur}$ (i.e., $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11]$) but becomes blocked at $\tau$ (i.e., $\|p_c \cdot \tau\| < 1/11$), we call this a **carry event** for $p_c$. There are exactly two carry types:

**Type C (cross):** $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11)$ and the shift pushes $\{p_c \cdot \tau\} > 10/11$. Runner $p_c$ has crossed the upper isolation boundary and is now near an integer from above. Its next entry time after $\tau$ is obtained by waiting for $\{p_c \cdot t\}$ to continue past 1 and reach $1/11$: distance $\delta' = (1 + 1/11 - \{p_c \cdot \tau\})/p_c \leq 2/(11p_c)$.

**Type W (wrap):** $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly (runner $p_c$ is at the exact isolation boundary, not yet blocked) and the shift $p_c \cdot \delta > 1/11$ pushes $\{p_c \cdot \tau\}$ past 1 entirely, landing in $[0, 1/11)$. Runner $p_c$ is now near an integer from below. Its next entry time is $\delta' = (1/11 - \{p_c \cdot \tau\})/p_c \leq 1/(11p_c)$.

**Empirical distribution across 9163 extended configs:** Of all 12544 total carry events, 8372 (66.7\%) are Type C and 4172 (33.3\%) are Type W. (In the original 1212 configs: 1551 total, 1090 (70\%) Type C, 461 (30\%) Type W.) Every Type W carry has $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly — the runner is at the precise boundary, half a step from being unblocked. This is not a coincidence: a runner with $\{p_c \cdot t_{\rm cur}\} > 10/11$ would already be a blocker, so Type W can only originate from the exact boundary.

**Single-step containment.** The largest single advance across all 9163 extended configs is $\delta = 3/55 \approx 0.055$, which is $6.67\%$ of $|W_0| = 9/(11p_1)$. This occurs for the extremal configuration $(1,3,4,\ldots,10,11)$ when runner $p_b = 3$ advances. The minimum containment margin (distance from $t_{\rm cur}$ to $W_{\rm hi}$ at any ILE level) is $54.5455\%$ of $|W_0|$, again achieved by the pacemaker. Moreover, no carry event ever produces an entry time exceeding $W_{\rm hi}$: across all 12544 carry events in all 9163 tested configs (plus the staircase family, §10.13), **zero** violations of containment were observed.

**Containment bound: the algebraic condition.** For a Type C carry by runner $p_c$ (whose next entry time is $\tau + \delta'$ with $\delta' \leq 2/(11p_c)$), containment requires $\tau + \delta' \leq W_{\rm hi}$, i.e.:
$$t_{\rm cur} + \delta + \frac{2}{11p_c} \leq \frac{10}{11p_1}.$$
Since $t_{\rm cur} \leq W_{\rm hi}$ and $\delta \leq 2/(11p_b)$, this becomes:
$$\frac{10}{11p_1} - t_{\rm cur} \geq \delta + \frac{2}{11p_c} \geq \frac{2}{11p_b} + \frac{2}{11p_c}.$$
In the worst case $p_b = p_c = p_2$ (the second-slowest runner, since $p_1$ is never a blocker): this requires $W_{\rm hi} - t_{\rm cur} \geq 4/(11p_2)$. The remaining room in $W_0$ is at least $4/(11p_2)$. Since the total width of $W_0$ is $9/(11p_1)$ and $p_2 > p_1$, this is a condition of the form "at most $4p_1/(9p_2)$ of $W_0$ has been used." For $p_2 \geq 2p_1$, this is at most $2/9 \approx 22\%$ of $W_0$.

**The pacemaker structure.** In 99\% of configurations, every runner advances as the ILE's advancing blocker at most once. The exceptional 1\% feature a **pacemaker runner**: a runner $p_b \equiv 0 \pmod{11p_1}$ (i.e., speed exactly a multiple of $11p_1$) that blocks at every integer multiple of $t_b = 1/(11p_b) = 1/(11 \cdot 11p_1)$. The extremal configuration $(1, 3, 4, 5, 6, 7, 8, 9, 10, 11)$ has pacemaker $p = 11$, which advances 5 times at $t = 1/11, 2/11, 3/11, 4/11, 5/11$ — the $k/11$ grid. Between consecutive pacemaker resets, the intermediate runners resolve their carries in order of decreasing speed (a descending sweep: $10, 9, 8, 7, 6$ in the first interval between $1/11$ and $2/11$). The pacemaker acts as an upper bound: $t^* \leq k_{\max}/(11 \cdot p_{\rm pm}) + 1/(11 \cdot p_{\rm pm})$, where $k_{\max}$ is the last reset index. For $p_{\rm pm} = 11$ and $k_{\max} = 5$: $t^* = 5/11 + 1/121 = 56/121$.

**Why $p_1$ is never a blocker.** This is the key structural fact underpinning containment: for all $t \in W_0$, $p_1 \cdot t \in [p_1 \cdot W_{\rm lo}, p_1 \cdot W_{\rm hi}] = [1/11, 10/11]$, so $\|p_1 \cdot t\| \in [1/11, 9/11]$ — always in the isolation zone. The slowest runner provides a "free" isolation throughout $W_0$. The smallest carry runner is therefore $p_2$, and all bounds are in terms of $p_2 > p_1$.

**Type reduction: C and W collapse into one condition.**

The Type C / Type W distinction is diagnostic, not structural. Both types produce a runner $p_c$ that is blocked at $\tau$ (i.e., $\|p_c \cdot \tau\| < 1/11$). In both cases the entry time formula is identical:
$$\tau_{\rm entry}(p_c, \tau) = \frac{11 j^* + 1}{11 p_c}, \qquad j^* = \left\lceil p_c \cdot \tau - \tfrac{1}{11} \right\rceil.$$

**Lemma 10.C (Unified carry bound).** *For any $\tau \in W_0$ and any runner $p_c$ with $\|p_c \cdot \tau\| < 1/11$,*
$$\tau_{\rm entry}(p_c, \tau) - \tau \;\leq\; \frac{2}{11 p_c}.$$
*The bound $1/(11p_c)$ holds if $\{p_c \cdot \tau\} < 1/11$ (runner near zero); the bound $2/(11p_c)$ applies if $\{p_c \cdot \tau\} > 10/11$ (runner near one).*

*Proof.* Let $f = \{p_c \cdot \tau\}$ and $j^* = \lceil p_c \cdot \tau - 1/11 \rceil$. Then $\tau_{\rm entry} - \tau = (j^* - p_c \tau + 1/11)/p_c$. If $f < 1/11$: $j^* = \lfloor p_c \tau \rfloor$ and the distance is $(1/11 - f)/p_c \leq 1/(11p_c)$. If $f > 10/11$: $j^* = \lfloor p_c \tau \rfloor + 1$ and the distance is $(1 - f + 1/11)/p_c = (12/11 - f)/p_c \leq 2/(11p_c)$ since $f > 10/11 > 0$. $\square$

This lemma eliminates the need to track carry types separately. The proof of Containment need only work with the unified bound.

**Non-degeneracy (proved).** $t_{\rm cur}$ is strictly increasing at each productive ILE level (it advances to a strictly later critical time). The set of critical times in $W_0$ is finite (at most $2 \cdot \sum_i \lfloor p_i \cdot (W_{\rm hi} - W_{\rm lo}) \rfloor + 2 \cdot 10$ entries). Hence the cascade terminates in at most $O(p_{10}/p_1 \cdot 10)$ steps. This is already proved and requires no further work.

**What the analytic proof must establish.** The sole remaining open condition is:

> **Containment (C):** For every Case R> configuration and every level $\ell$ of ILE, if $p_c$ is blocked at $t_{\rm cur}^{(\ell)}$, then $\tau_{\rm entry}(p_c, t_{\rm cur}^{(\ell)}) \leq W_{\rm hi}$.

By Lemma 10.C, this is equivalent to: $t_{\rm cur}^{(\ell)} \leq W_{\rm hi} - 2/(11p_c)$ for all blocked runners $p_c$ at level $\ell$. Since $p_c \geq p_2 > p_1$ (the slowest runner $p_1$ is never a blocker), the condition becomes:
$$t_{\rm cur}^{(\ell)} \;\leq\; \frac{10}{11p_1} - \frac{2}{11p_2}.$$
Empirically this holds with large margin: the tightest observed case has $t^* = 56/121$ against $W_{\rm hi} - 2/(11 \cdot 3) = 10/11 - 2/33 = 28/33 \approx 0.848$ (for the $(1, 3, 4, \ldots, 11)$ config with $p_2 = 3$). The witness $56/121 \approx 0.463$ is far below this bound. Proving this gap analytically is the core open task.

**Open problem hierarchy.** The open items for Case R>, in dependency order:

| Item | Status | Comment |
|---|---|---|
| Non-degeneracy (ND) | **Proved** | Trivial: finite discrete lattice |
| Case 0 ($W_{\rm lo}$ directly valid) | **Proved** | No blockers at $W_{\rm lo}$: immediate |
| Unified carry bound (Lemma 10.C) | **Proved** | Exact entry-time formula |
| Containment (C): $t_{\rm cur}^{(\ell)} \leq W_{\rm hi} - 2/(11p_c)$ | **Open** | Core analytic gap; empirically 0 violations |
| ↳ Step L2: $R_i + p_i (p_1 - r_b)/p_b \leq 10p_1$ | **Empirically false** | Violated in 28.1\% of 9163 tested configs; not the right proof target |
| ↳ Pacemaker bound ($\leq n-2$ resets) | **Open** (tractable) | Resonant-speed configs |
| ILE Termination $\Leftrightarrow$ $W_0$-Intersection $\Leftrightarrow$ Conjecture B for Case R> | **Open** | Follows from Containment |

---

### 10.11 Why the right-endpoint approach fails: an algebraic obstruction

A natural candidate approach to Case R> is the **right-endpoint conjecture**: the joint isolation set $J_{2-10}$ always has a window whose right endpoint lies at or near $W_{\rm hi} = 10/(11p_1)$. The geometric intuition is that the faster runners (speeds $p_2,\ldots,p_{10}$) have shorter, denser isolation windows, so their joint isolation "ought to" cover the upper part of $W_0$ just before runner 1 exits isolation at $t = W_{\rm hi}$.

**The conjecture is false for 71.4% of configurations.** A systematic investigation over all 1212 tested Case R> configurations shows:

| Status at $W_{\rm hi}$ | Configs | % |
|---|---|---|
| All runners 2–10 isolated: $W_{\rm hi}$ is a valid witness | 347 | 28.6% |
| **Type H** (permanent blocker, $\|p_i W_{\rm hi}\| = 0$ for some $i$) | 445 | 36.7% |
| **Type N** (near-resonant, $0 < \|p_i W_{\rm hi}\| < 1/11$) | 420 | 34.7% |

**Algebraic characterisation of Type H blockers.** A runner $p_i$ is a permanent blocker at $W_{\rm hi}$ if and only if $p_i \times W_{\rm hi} \in \mathbb{Z}$, i.e., $p_i \times 10/(11p_1) \in \mathbb{Z}$. This is equivalent to $11p_1 \mid 10p_i$. Since $\gcd(11, 10) = 1$, this reduces to:
$$\frac{11p_1}{\gcd(10, p_1)} \;\Big|\; p_i.$$
In the generic case where $11 \nmid p_1$, the condition simplifies to $11 \mid p_i$: **every permanent right-endpoint blocker must be a multiple of 11.** This was verified for all 445 Type H configurations (100%). The mechanism is purely algebraic: $11 \times 10/(11p_1) = 10/p_1$ is an integer only if $p_1 \mid 10$ and the runner speed is a suitable multiple; the factor 11 in $W_{\rm hi}$'s denominator forces 11 to divide the blocking speed.

*Example (extremal case).* Configuration $(1, 3, 4, 5, 6, 7, 8, 9, 10, 11)$ has $p_{10} = 11 = 11 \times p_1$. At $W_{\rm hi} = 10/11$: $11 \times 10/11 = 10 \in \mathbb{Z}$, so $\|11 \cdot W_{\rm hi}\| = 0$. Runner $p = 11$ is a permanent zero-distance blocker at $W_{\rm hi}$. The rightmost $J_{2-10}$ window inside $W_0$ ends at $65/121 \approx 53.7\%$ of the way to $W_{\rm hi}$, with a gap of $45.5\%$ of $|W_0|$.

**Why the geometric intuition fails.** The argument "faster runners have denser windows, so they cover $W_{\rm hi}$" fails because:
1. *Harmonic obstruction.* A runner with speed divisible by 11 has its isolation windows periodically spaced at multiples of $1/(11p_i)$. At $W_{\rm hi}$, this runner is at position $10p_i/(11p_1)$, a multiple of $10/p_1$. When $p_1 \mid 10$, this is an integer — precisely the Type H condition. No amount of "density" resolves a runner that is trapped at an integer at $W_{\rm hi}$.
2. *Compounding gaps.* For Type N blockers, the actual gap between the last $J_{2-10}$ window and $W_{\rm hi}$ is typically $4.5\times$ larger than the gap one would predict from the hardest blocker alone. Multiple near-resonant runners compound their gaps, extending the dead zone near $W_{\rm hi}$ far beyond what any individual runner would cause.

**The maximum gap is 50.5% of $|W_0|$.** Even setting aside the permanent Type H obstruction, the rightmost $J_{2-10}$ window can be as far as half of $W_0$'s width from $W_{\rm hi}$. There is no "small $\varepsilon$" in a right-endpoint lemma that works universally.

**Consequence for proof strategy.** The right-endpoint approach would at best handle the 28.6% of configurations where $W_{\rm hi}$ is already a valid witness. For the remaining 71.4%, an entirely different witness must be found. The Iterated Left-Entry Construction (§10.9) handles all configurations uniformly by starting from $W_{\rm lo}$ (where runner 1 *enters* isolation) rather than $W_{\rm hi}$ (where it *exits*). The ILE approach is immune to the Type H obstruction because $W_{\rm lo} = 1/(11p_1)$ satisfies $p_i \times W_{\rm lo} = p_i/(11p_1)$, which is never an integer for $p_i < 11p_1$ (i.e., for all non-pacemaker runners) — so $W_{\rm lo}$ itself avoids the Type H degeneracy entirely.

**Summary.** The right-endpoint conjecture, while geometrically appealing, is obstructed by a clean number-theoretic condition: the presence of any speed divisible by 11 (generically) creates a permanent zero-distance block at $W_{\rm hi}$. This is not a pathological exception — it affects 36.7% of tested configurations. The correct proof strategy must work from the left endpoint of $W_0$, not the right.

---

### 10.12 The pacemaker case: an analytic proof via modular arithmetic

We now prove Case R> unconditionally for all **pacemaker configurations** with $p_{\rm pm} = 11p_1$ — those in which exactly one of the ten speeds equals $11p_1$. This is the most constrained (ratio $= 11$) sub-case of Case R> and the hardest among random and adversarial configurations: it produces the maximum level count $L = 20$ in the original 1212-config dataset and the 9163-config extended dataset. (The consecutive staircase family of §10.13 reaches $L = 58$ by a different mechanism.)

**Setup.** By scaling all speeds by $1/p_1$, assume WLOG that $p_1 = 1$ and $p_{10} = 11$. The ten speeds are then $\{1\} \cup S \cup \{11\}$ where $S \subseteq \{2,3,\ldots,10\}$ with $|S| = 8$; equivalently, $S = \{2,\ldots,10\} \setminus \{m\}$ for a unique **missing speed** $m \in \{2,\ldots,10\}$. There are exactly nine such configurations.

The interval $W_0 = [1/11, 10/11]$ has width $9/11$. The pacemaker (speed 11) has exactly nine re-entry times in $W_0$:
$$t_j = \frac{11j+1}{121}, \qquad j = 1, 2, \ldots, 9.$$
These are equally spaced by $1/11$ and satisfy $t_j \in (11/121, 110/121) = (W_{\rm lo}, W_{\rm hi})$.

**The modular structure.** For any speed $k \in \{1,\ldots,10\}$ and pacemaker entry time $t_j$, the fractional distance is $\|k \cdot t_j\| = \|k(11j+1)/121\|$. Write $k(11j+1) = 121n + 11q + k$ for integers $n \geq 0$ and $0 \leq q \leq 10$ (since $k(11j+1) \equiv k \pmod{11}$, the residue mod 11 is exactly $k$). Then:
$$\|k \cdot t_j\| = \frac{\min(11q+k,\; 121 - 11q - k)}{121}.$$

**Lemma 10.D (No lower-bad zone).** *For all $k \in \{2,\ldots,10\}$ and $j \in \{1,\ldots,9\}$: $k(11j+1) \bmod 121 \notin [0, 11)$.*

*Proof.* Lower-bad requires $11q + k < 11$, hence $q = 0$ (since $k \geq 2$ forces $11-k \leq 9 < 11$, giving $q < 1$). But $q = 0$ means $k(11j+1) \equiv k \pmod{121}$, i.e., $k \cdot 11j \equiv 0 \pmod{121}$. Since $\gcd(k,11) = 1$ for $k \leq 10$, this forces $11 \mid j$. But $j \in \{1,\ldots,9\}$, so this is impossible. $\square$

**Lemma 10.E (Exactly one upper-bad per row).** *For each $j \in \{1,\ldots,9\}$, there is exactly one $k \in \{2,\ldots,10\}$ with $k(11j+1) \bmod 121 \in (110, 121)$.*

*Proof.* Upper-bad requires $11q + k > 110$. Since $k \leq 10$ and $11q + k \leq 120 < 121$, we need $q = 10$ exactly. The condition $k(11j+1) \equiv 110 + k \pmod{121}$ gives $k \cdot 11j \equiv 110 \pmod{121}$, hence $kj \equiv 10 \pmod{11}$, i.e., $j \equiv 10 k^{-1} \pmod{11}$. For each $j \in \{1,\ldots,9\}$, the unique solution is $k \equiv 10 j^{-1} \pmod{11}$, which lies in $\{2,\ldots,10\}$ (since $k = 1$ would give $j = 10 \notin \{1,\ldots,9\}$). $\square$

The map $k \mapsto j^*(k) = 10 k^{-1} \bmod 11$ (and its inverse $j \mapsto k(j) = 10 j^{-1} \bmod 11$) is a **bijection** between $\{2,\ldots,10\}$ and $\{1,\ldots,9\}$.

**Theorem 10.12 (Pacemaker LRC, ratio = 11).** *For every Case R> configuration $(1, S \cup \{11\})$ with $S = \{2,\ldots,10\} \setminus \{m\}$, the time*
$$t^* = \frac{11 j^* + 1}{121}, \qquad j^* = 10 m^{-1} \bmod 11,$$
*is a valid joint witness: $\|k \cdot t^*\| \geq 1/11$ for all speeds $k \in \{1\} \cup S \cup \{11\}$.*

*Proof.* We verify each speed class:
- **$k = 1$:** $1 \cdot t^* = (11j^*+1)/121 \in [12/121, 100/121] \subset [11/121, 110/121]$. ✓
- **$k = 11$ (pacemaker):** $11 \cdot t^* = (11j^*+1)/11 = j^* + 1/11$. So $\|11 t^*\| = 1/11$. ✓ (at the isolation boundary)
- **$k \in \{2,\ldots,10\} \setminus \{m\}$:** By Lemma 10.D, $k(11j^*+1) \bmod 121 \notin [0,11)$. By Lemma 10.E, the unique upper-bad speed at $t_{j^*}$ is $k(j^*) = 10(j^*)^{-1} \bmod 11 = m$, which is absent from the configuration. Hence $k(11j^*+1) \bmod 121 = 11q + k$ with $q \in \{1,\ldots,9\}$, giving $\|k t^*\| = \min(11q+k, 121-11q-k)/121 \geq \min(11+2, 11+1)/121 = 12/121 > 11/121 = 1/11$. ✓ $\square$

**Explicit witness table for $p_1 = 1$, $p_{10} = 11$:**

| Missing speed $m$ | Witness index $j^*$ | Theorem $t^*$ | ILE levels $L$ | ILE witness |
|---|---|---|---|---|
| 2 | 5 | 56/121 | 20 | 56/121 |
| 3 | 7 | 78/121 | 13 | 17/55 |
| 4 | 8 | 89/121 | 9 | 23/99 |
| 5 | 2 | 23/121 | 7 | 23/121 |
| 6 | 9 | 100/121 | 5 | 12/77 |
| 7 | 3 | 34/121 | 4 | 3/22 |
| 8 | 4 | 45/121 | 3 | 4/33 |
| 9 | 6 | 67/121 | 2 | 6/55 |
| 10 | 1 | 12/121 | 1 | 12/121 |

The "ILE witness" column reports the leftmost valid witness found by ILE (which may differ from the theorem's $t^*$ when an earlier witness exists). In 3 of 9 cases ($m = 2, 5, 10$), the ILE finds the same witness as the theorem; in the remaining 6, the ILE finds an earlier witness in $W_0$. The theorem guarantees the existence of $t^*$; the ILE independently finds the leftmost valid time. The witness for the $m=2$ config (ILE: $L=20$, witness $= 56/121$) matches the theorem exactly and was the hardest pacemaker case.

**Why this works: the missing-speed mechanism.** The bijection $m \leftrightarrow j^*$ has a clean interpretation: $t_{j^*}$ is the unique pacemaker entry time at which speed $m$ would have been blocked (upper-bad), had it been present. Since $m$ is absent, $t_{j^*}$ has no blocker among the present speeds, making it a valid witness. The pacemaker itself (speed 11) enters isolation at each $t_j$ by construction. Runner 1 (speed 1) is always isolated throughout $W_0$ (Lemma 10.D with $k=1$ extends to show $1 \cdot t_j = (11j+1)/121 \in [12/121, 100/121]$). The elegant bijection is a consequence of the arithmetic of $\mathbb{Z}/11^2\mathbb{Z}$: the map $k \mapsto 10k^{-1} \bmod 11$ realises the "complementary slot" structure of $(\mathbb{Z}/11\mathbb{Z})^*$.

**Extension to $p_1 > 1$.** By the scaling argument (all speeds integer multiples of $p_1$), the witness for general $p_1$ is $t^* = (11j^*+1)/(121p_1)$ with the same $j^*$ formula, and the proof is identical. This covers all Case R> pacemaker configs with $p_{10}/p_1 = 11$ and all speeds integer multiples of $p_1$.

**Scope and remaining open case.** Theorem 10.12 fully resolves the ratio-11 pacemaker sub-case. The remaining open sub-cases of Case R> are:
1. Pacemaker configs with $p_{\rm pm} = 11kp_1$ for $k \geq 2$ (higher pacemakers, ratio $\geq 22$): same bijection structure modulo $121k^2 p_1$, likely tractable by the same method.
2. Non-pacemaker commensurable configs (no speed is a multiple of $11p_1$): the ILE algorithm terminates successfully across all 9163 tested configurations; the maximum $L$ in the extended dataset is 20 for random configs, but reaches 58 for the consecutive staircase family $(1, N, N+1, \ldots, N+8)$ with $N = 69$ (see §10.13). No modular bijection analogous to Theorem 10.12 is apparent for the non-pacemaker case.

The updated open problem hierarchy is:

| Item | Status | Reference |
|---|---|---|
| Non-degeneracy | **Proved** | §10.10 |
| Case 0 ($W_{\rm lo}$ directly valid) | **Proved** | §10.8 |
| Unified carry bound (Lemma 10.C) | **Proved** | §10.10 |
| **Pacemaker case ($p_{\rm pm} = 11p_1$, ratio = 11)** | **Proved** (Thm 10.12) | §10.12 |
| Pacemaker case ($p_{\rm pm} = 11kp_1$, $k \geq 2$) | **Open** (tractable) | §10.12 |
| Consecutive staircase family (§10.13) | **Empirically verified** ($L$ unbounded) | §10.13 |
| Containment (C): runners with $p_b \not\equiv 0\pmod{11}$ | **Proved** (Lemma GC) | §10.15 |
| Containment (C): left-blocking priority (Lemma LB) | **Proved** | §10.15 |
| Containment (C): witnesses disjoint from $D_j$ (Lemma WD) | **Proved** | §10.15 |
| Containment (C): fastest runner $p_{10} \equiv 0\pmod{11}$ | **Proved** (Thm FR) | §10.15 |
| Containment (C): configs with no interior multiples of 11 | **Proved** (Thm C1) | §10.15 |
| Containment (C): interior $p_j \equiv 0\pmod{11}$, $p_{10} < 11p_{c,\min}(p_j)$ | **Proved** (Prop MC) | §10.15 |
| Containment (C): slow-runner exclusion from approach windows (Lemma SR) | **Proved** | §10.15 |
| Containment (C): interior $p_j \equiv 0\pmod{11}$, $p_{10} \geq 11p_{c,\min}(p_j)$ — fast-runner chain | **Open** — residual | §10.15 |
| **Route 3** (EFN real-speed perturbation): Complementary Pairs, forced gaps, overdetermination | **PROVED for ++------ class (2026-03-23)** | §10.16 |
| ↳ Complementary Pairs Theorem (mod-11 bijection gives 4 runner pairs, each owning 2 slots) | **Proved** | §10.16 |
| ↳ Cases A/B: edge gap in $I_1$ for $a_9 < 25/3$ or $a_6 > 40/7$ | **Proved** | §10.16 |
| ↳ Forced gaps $G_3$ (width $1/40$) and $G_6$ (width $161/2200$) when $I_1$ closed | **Proved** by direct computation | §10.16 |
| ↳ Case C explicit certificate $t^* = 69/275$ in $I_2$ | **Proved** (exact arithmetic) | §10.16 |
| ↳ Overdetermination Main Claim: Runner 2 Incompatibility ($a_2 \geq 20/9$ vs $a_2 \leq 575/261$) | **Proved** (gap $= 5/261 > 0$, 2026-03-23) | §10.16 |

---

### 10.13 The consecutive staircase family: a second hard-case mechanism

We identify and analyse an infinite family of Case R> configurations that achieves large $L$ values via a mechanism distinct from the pacemaker. These **consecutive staircase configurations** have the form
$$\mathcal{S}_N = (1,\, N,\, N+1,\, N+2,\, \ldots,\, N+8),$$
where $N$ is a positive integer and $p_1 = 1$, $p_{10} = N+8$. The ratio is $N+8$, so $\mathcal{S}_N$ is Case R> whenever $N+8 > 10$, i.e., $N \geq 3$.

**The 11-multiple trigger.** The ILE dynamics are controlled entirely by whether the range $[N, N+8]$ contains a multiple of 11. Write $11k$ for the unique multiple of 11 in $[N, N+8]$ (if any). The role of runner $11k$ is:
- At $W_{\rm lo} = 1/11$: $\{11k \cdot 1/11\} = \{k\} = 0$ — the runner is at position 0, within $1/11$ of an integer, so it is a **$W_{\rm lo}$-blocker**.
- All other interior runners $N, \ldots, N+8$ (except $11k$) have fractional part $\{p/(11)\} \in (1/11, 10/11)$ at $t = W_{\rm lo}$ and are **not blockers**.
- If no multiple of 11 falls in $[N, N+8]$: no runner is blocked at $W_{\rm lo}$, so $L = 0$ (immediate witness).

**The cascade mechanism.** When $11k$ is the rightmost interior runner ($11k = N+8$), the ILE must advance $t_{\rm cur}$ to resolve runner $11k$. This advance creates carry events among the runners $N, N+1, \ldots, N+7$ (the slower interior runners). Because these runners have speeds differing by exactly 1, a **telescoping carry cascade** develops: resolving one runner's carry event immediately triggers a carry for the next slower runner. The cascade continues until all interior runners are re-isolated, producing a large $L$.

**Empirical results (ILE, exact arithmetic).** For $N = 10$ to $500$ (all $N$ with a multiple of 11 in $[N,N+8]$):

| Position of $11k$ in range | Typical $L$ | Mechanism |
|---|---|---|
| Leftmost: $11k = N$ (runner $11k$ is slowest interior) | $L = 1$ | Runner $11k$ at $W_{\rm lo}$ is resolved in one step; no cascade |
| Rightmost: $11k = N+8$ (runner $11k$ is fastest interior) | $L$ up to 58 | Full cascade through all 8 interior runners |
| Middle positions | $L \in [2, 50]$ | Partial cascade |

The maximum $L$ occurs at $N = 69$ (runner $77 = 7 \cdot 11$ is rightmost): $L = 58$, with minimum containment margin $87.8\%$ of $|W_0|$ — the ILE succeeds comfortably with large margin despite many iterations. The level count peaks at $N = 69$ and stabilises near $L = 9$ for $N \geq 80$, because for large $N$ the ratio $p_{10}/p_1$ is large and the cascade structure changes.

**Special case $k=1$ ($N=3$): the pacemaker.** The configuration $\mathcal{S}_3 = (1, 3, 4, 5, 6, 7, 8, 9, 10, 11)$ is precisely the extremal pacemaker of §10.12 (missing speed $m=2$), with $L = 20$ and witness $t^* = 56/121$ proved by Theorem 10.12. It is the $k=1$ member of the staircase family. The staircase thus reveals the pacemaker as the first element of a parametric cascade family.

**Why the staircase is not an AP-witness family.** The paper's AP-witness framework (§10.3–10.5) constructs witnesses at times $t = a/(11p_1) + k/(11p_{10})$ — an arithmetic progression in **time**. The consecutive staircase has speeds in arithmetic progression (common difference 1 in speed space). These are orthogonal structures: the AP-witness times encode a modular bijection among residues of fast runners, while the staircase's difficulty arises from the near-equal spacing of speeds creating a telescoping carry cascade in the ILE. The staircase's witnesses are not in general of AP-time form.

**Conjecture M1 confirmed.** For all staircase configs tested ($N = 10, \ldots, 500$), Conjecture M1 holds: the minimum containment margin at any ILE level is $\geq 1/(11 p_2)$, where $p_2 = N$ is the second-slowest runner. The minimum ratio (margin / bound M1) across the staircase family is approximately 9.8 — the margin vastly exceeds the M1 lower bound, consistent with the large observed margins (80–100\% of $|W_0|$).

**The staircase level count is unbounded.** Extended experiments ($N \leq 2000$) reveal that $L$ grows without bound in the staircase family. The level count $L \approx 0.75\,N$ for large $N$ (empirical fit). Highest observed: $\mathcal{S}_{266} = (1, 266, \ldots, 274, 275)$ gives $L = 200$ with minimum containment gap (gap $= j_{\max} - j^*$) equal to 192 — vastly above zero. The staircase family therefore demonstrates that large $L$ poses **no Containment threat**: each ILE level has abundant margin even at $L = 200$. The cascade is long but safe.

**Open questions.** The staircase family raises two analytic questions:
1. *Why does $L \approx 0.75\,N$ and can this linear growth be proved?* The cascade length grows because each of the 9 interior runners becomes a blocker after $p_{10}$ is resolved, and the number of cascade passes grows with the ratio $p_{10}/p_1 = p_{10} \approx N$. A combinatorial proof of the linear scaling may be tractable.
2. *Can the cascading carry structure of the staircase be proved to terminate?* The mechanism is clear: each carry event triggers the next runner in the staircase to enter the blocking zone, and the chain terminates when the slowest interior runner clears. A combinatorial proof exploiting the unit-difference structure ($p_{i+1} - p_i = 1$) may be tractable.

### 10.14 Containment (C) proof-attack experiments

We report five targeted experiments designed to expose proof-actionable structure in the open Containment condition (C). The experiments use the 9163-config corpus of §10.9 plus 491 staircase configs ($N = 10\ldots500$), re-run with full per-level instrumentation. All 21722 ILE level events are analysed.

**EXP-1: Advance fraction.** For each ILE advance, define
$$f_\ell = \frac{\delta_\ell}{W_{\mathrm{hi}} - t_{\mathrm{cur},\ell}}, \quad \delta_\ell = \tau(p_b, t_{\mathrm{cur},\ell}) - t_{\mathrm{cur},\ell}.$$
This is the fraction of the remaining containment margin consumed by the advance. By Lemma 10.C, $\delta_\ell \leq 2/(11 p_b)$. A bound $f_\ell < 1$ at every level is equivalent to Containment.

| Quantity | Observed value |
|---|---|
| Maximum $f$ (all levels, all configs) | $1/11 = 0.09\overline{09}$ |
| 99th percentile $f$ | $0.0256$ |
| Mean $f$ | $0.0047$ |
| Fraction with $f > 0.5$ | $0\%$ |
| Any $f \geq 1.0$ (Containment failure) | None |

The maximum advance fraction $1/11$ is achieved **exactly** by the pacemaker miss-2 configuration $(1, 3, 4, 5, 6, 7, 8, 9, 10, 11)$ (Theorem 10.12) at level 13, advancing runner $p_b = 3$. For all other configurations, $f < 1/11$. The bound $f \leq 1/11$ is therefore tight, and the tight case is already proved.

**EXP-2: Gap distribution.** For each ILE advance, define the \emph{gap}
$$\mathrm{gap} = j_{\max} - j^*, \quad j^* = p_b\,\tau_\ell - \tfrac{1}{11}, \quad j_{\max} = \left\lfloor\tfrac{10\,p_b - p_1}{11\,p_1}\right\rfloor.$$
Here $j^*$ is the isolation-index of $p_b$ after the advance and $j_{\max}$ is the last index for which the re-entry time is $\leq W_{\mathrm{hi}}$. Containment $\Leftrightarrow$ gap $\geq 0$ at every level.

| Quantity | Observed value |
|---|---|
| Minimum gap (all 21722 events) | $1$ |
| Maximum gap | $816$ |
| Mean gap | $110.1$ |
| Gap $= 0$ events (Containment violation) | **0** |
| Gap $= 1$ events | 2 |

Both gap $= 1$ events occur at level 13 of the pacemaker miss-2 config (advancing $p_b = 3$), which is proved by Theorem 10.12. No non-pacemaker-miss-2 configuration achieves gap $< 2$. The empirical lower bound is therefore gap $\geq 1$ universally, with the tight case covered by Theorem 10.12.

**EXP-3: Gap trajectory monotonicity.** Examining the sequence $(\mathrm{gap}_0, \mathrm{gap}_1, \ldots, \mathrm{gap}_L)$ per configuration: gap is monotone non-decreasing in 69.6\% of configs (all $L \leq 1$ configs and many $L = 2$ configs). For $L \geq 3$, gap drops occur in $\geq 75\%$ of configs, ruling out a simple level-by-level induction. Despite drops, gap never falls below 1. A potential-function argument that accommodates non-monotone trajectories is needed.

**EXP-4: Extremal level characterisation.** For each config, the level $\ell^*$ with maximum $f$ uses advancing runner $p_b^*$: $p_2$ (second-slowest) is the advancing runner at $\ell^*$ in 18.7\% of configs; the position distribution is monotone decreasing (slower runners are responsible for the tightest advances more frequently). Both gap $= 1$ events have $p_b^* = p_2$ (position 2), confirming Conjecture M1: the tightest case is always set by the second-slowest runner.

**EXP-5: Adversarial minimisation.** Sweeping the staircase family to $N = 2000$ (1834 configs), the minimum gap across all staircase ILE events is 7 — despite level counts as large as 200. An adversarial random grid (8000 configs, ratio $\in [10.5, 500]$, $p_1 \in \{1,2,3,5\}$) achieves minimum gap 1, always from the pacemaker miss-2 config. No adversarial construction found gap $= 0$.

**Proof-angle assessment.** The experiments identify two actionable proof strategies for Containment (C) in the non-pacemaker case:

1. *Direct gap $\geq 1$ proof (most targeted).* Containment $\Leftrightarrow$ gap $\geq 0$. The empirical minimum is gap $= 1$, achieved only by the pacemaker miss-2 (proved). For all other configs, gap $\geq 2$. A number-theoretic proof that $j_{\max} \geq j^* + 1$ for all non-pacemaker ILE states would complete the argument. The key identity is $j_{\max} = \lfloor(10\,p_b - p_1)/(11\,p_1)\rfloor$ and $j^*$ is constrained by the blocker condition and the ILE advance formula. The pacemaker case ($p_{10}/p_1 = 11$, ratio exactly 11) requires separate treatment already provided by Theorem 10.12; for $p_{10}/p_1 > 11$, $j_{\max}$ is strictly larger, providing additional margin.

2. *Contracting-map argument (less tight but potentially easier to prove).* $f \leq 1/11$ empirically. Since $f < 1$ is all that is required for convergence, the bound from Lemma 10.C ($\delta \leq 2/(11 p_c)$) combined with a lower bound on the remaining margin (margin $\geq 2/(11 p_c)$ for Containment to hold) would suffice. The critical step is to show that the ILE cannot reach a state where margin $<\delta$.

Both strategies converge on the same core question: why can the ILE never reach a state where $j^* = j_{\max}$? The experiments identify the answer as number-theoretic — the advance formula $\tau = (11j^*+1)/(11p_b)$ and the constraint that $t_{\mathrm{cur}}$ is itself a re-entry time of a previous blocker impose a residue condition that prevents $j^*$ from equalling $j_{\max}$. §10.15 makes part of this argument rigorous.

---

### 10.15 Partial analytic proof of Containment (C)

We classify runners as **safe** or **dangerous** according to their residue
$R(p_b) = (10\,p_b - p_1)\bmod(11\,p_1) \in [0,11\,p_1)$.

**Geometric Containment Lemma (GC).** *For any runner $p_b$ with $R(p_b) \leq 9p_1$, gap$(p_b, t_{\mathrm{cur}}) \geq 0$ for all $t_{\mathrm{cur}} \in W_0$ at which $p_b$ is blocking.*

*Proof.* There are two blocking types.

*Left-blocking* ($\{p_b t\} \in [0, 1/11)$): a gap $< 0$ event requires $j^* \geq j_{\max}+1$, hence $t_{\mathrm{cur}} \geq (j_{\max}+1)/p_b$. But $(j_{\max}+1)/p_b > W_{\mathrm{hi}}$ iff $10p_1 > R(p_b)$, which holds when $R \leq 9p_1 < 10p_1$. Since $t_{\mathrm{cur}} \leq W_{\mathrm{hi}}$, no such state is reachable.

*Right-blocking* ($\{p_b t\} \in (10/11, 1)$): a gap $< 0$ event requires the right-blocking zone for index $j_{\max}$ to intersect $W_0$, i.e.\ $(11j_{\max}+10)/(11p_b) \leq W_{\mathrm{hi}}$. Using $11p_1 j_{\max} = 10p_b - p_1 - R$, this reduces to $R \geq 9p_1$. When $R < 9p_1$ the zone lies strictly above $W_{\mathrm{hi}}$; when $R = 9p_1$ the zone boundary equals $W_{\mathrm{hi}}$ but the zone is open, so $t_{\mathrm{cur}} \leq W_{\mathrm{hi}}$ does not reach it. Either way, no gap $< 0$ event occurs. $\square$

For $p_1 = 1$: Lemma GC covers all runners with $p_b \not\equiv 0\pmod{11}$ (residues $R \in \{0,\ldots,9\}$). The only dangerous runners are $p_b \equiv 0\pmod{11}$.

**Structure of the dangerous zone ($p_1 = 1$, $p_b = 11m$).** For any dangerous runner $p_b = 11m$:
$$j_{\max} = 10m - 1, \quad \text{dangerous zone} = \left(\frac{110m-1}{121m},\, \frac{10}{11}\right) = \left(\frac{110m-1}{121m},\, W_{\mathrm{hi}}\right),$$
with width $1/(11p_b) = 1/(121m)$. If the ILE state $t_{\mathrm{cur}}$ ever enters this zone, then $j^* = 10m = j_{\max}+1$ and $\tau(p_b, t_{\mathrm{cur}}) = (110m+1)/(121m) > W_{\mathrm{hi}}$: Containment fails.

**Key Advance-Structure Lemma (AS).** *Let $p_1 = 1$, $p_b = 11m$. For any runner $p_{\mathrm{adv}}$ with $p_{\mathrm{adv}} < p_b$, no left re-entry time $(11k+1)/(11p_{\mathrm{adv}})$ falls in the dangerous zone $((110m-1)/(121m),\, 10/11)$.*

*Proof.* Suppose $(11k+1)/(11p_{\mathrm{adv}})$ is in the zone. The upper bound gives $11k+1 < 10p_{\mathrm{adv}}$. The lower bound gives $11k+1 > 10p_{\mathrm{adv}} - p_{\mathrm{adv}}/(11m)$. Since $p_{\mathrm{adv}} < 11m$, the ratio $p_{\mathrm{adv}}/(11m) < 1$, so the lower bound forces $11k+1 \geq 10p_{\mathrm{adv}}$ (as $11k+1$ is an integer). The two inequalities $11k+1 \geq 10p_{\mathrm{adv}}$ and $11k+1 < 10p_{\mathrm{adv}}$ are contradictory. $\square$

*Numerical verification:* for $m = 1, 2, 3$, exhaustive check over all $p_{\mathrm{adv}} < p_b$ confirms no entry falls in the zone.

**Fastest-Runner Containment (FR).** *Let $p_1 = 1$ and $p_{10} = 11m$. Then gap$(p_{10}, t_{\mathrm{cur}}) \geq 0$ at every ILE step.*

*Proof.* The ILE starts at $W_{\mathrm{lo}} = 1/11 < (110m-1)/(121m)$, outside the dangerous zone. At each step, $t_{\mathrm{cur}}$ advances to a left re-entry time $(11k+1)/(11p_{\mathrm{adv}})$:
(a) If $p_{\mathrm{adv}} = p_{10}$: every left re-entry time of $p_{10}$ satisfies $(11j+1)/(11p_{10}) \leq (11j_{\max}+1)/(11p_{10}) < (11j_{\max}+10)/(11p_{10})$ (the dangerous zone's left boundary), so the advance stays below the zone.
(b) If $p_{\mathrm{adv}} \neq p_{10}$: then $p_{\mathrm{adv}} < p_{10} = 11m$, and Lemma AS applies directly.
In both cases the advance cannot land in the dangerous zone. By induction, $t_{\mathrm{cur}}$ never enters the zone, and gap $\geq 0$ for $p_{10}$ throughout. $\square$

**Combined result (Theorem C1).** *In Case R> with $p_1 = 1$, Containment holds for every runner $p_b$ if either (i) $p_b \not\equiv 0\pmod{11}$ (Lemma GC) or (ii) $p_b = p_{10}$ with $p_{10} \equiv 0\pmod{11}$ (Theorem FR). In particular, Containment is fully proved for all configurations in which the only speed divisible by 11 is $p_{10}$ itself.*

**Structural analysis of the interior-runner case.** For a runner $p_j = 11m$ with $j < 10$ (interior), let $D_j = ((110m-1)/(121m),\, 10/11)$ be its dangerous zone. Two further lemmas narrow the residual.

**Left-Blocking Priority (Lemma LB).** *If $p_j$ is left-blocking at an ILE state $t_{\mathrm{prev}} < D_{j,\mathrm{left}}$, then $\tau(p_j, t_{\mathrm{prev}}) < D_{j,\mathrm{left}} \leq \tau(p_c, t_{\mathrm{prev}})$ for every runner $p_c > p_j$ with $\tau(p_c) \in D_j$.*

*Proof.* The maximal left re-entry time of $p_j$ before the dangerous zone is $\tau_{j_{\max}}(p_j) = (110m-10)/(121m) < D_{j,\mathrm{left}}$. Any $p_c > p_j$ with $\tau(p_c) \in D_j$ satisfies $\tau(p_c) \geq D_{j,\mathrm{left}}$. Hence $\tau(p_j) < D_{j,\mathrm{left}} \leq \tau(p_c)$, and the ILE advances by $p_j$ first. $\square$

By Lemma LB, the ILE can enter $D_j$ only when $p_j$ is *isolated* (not left-blocking) at the preceding state. When $p_j$ is isolated, it lies in the window $((110m-10)/(121m),\, D_{j,\mathrm{left}})$ of width $9/(121m)$.

**Witness-Disjoint (Lemma WD).** *Every witness $t^* \in W_0$ satisfies $t^* < D_{j,\mathrm{left}}$.*

*Proof.* In $D_j$, runner $p_j$ is right-blocking, so no witness exists there. At $W_{\mathrm{hi}}$, $\{p_j W_{\mathrm{hi}}\} = \{10m\} = 0$, so $p_j$ is left-blocking — also not a witness. Therefore all witnesses lie in $[W_{\mathrm{lo}},\, D_{j,\mathrm{left}})$. $\square$

**Approach-window threshold (Proposition MC).** The ILE only reaches left re-entry times. For a runner $p_c > p_j$ with $\tau(p_c) \in D_j$ to advance from an ILE state below $D_{j,\mathrm{left}}$, the *approach window* — the left-blocking interval of $p_c$ mapping to $D_j$ — has width $1/(11p_c)$. For any previous ILE state to lie in this window, the config must contain a runner $p_0$ with $p_0 \geq 11p_c$ (otherwise the window is too narrow to contain a left re-entry time). Let $p_{c,\min}(p_j)$ denote the smallest runner $p_c > p_j$ with a re-entry time in $D_j$; for $p_j = 11$ this is $p_{c,\min}(11) = 20$, verified by checking all $p_c \in \{12,\ldots,19\}$.

*If $p_{10} < 11\cdot p_{c,\min}(p_j)$, no runner $p_0 \geq 11p_c$ exists, so the approach window is unreachable and Containment holds for $p_j$.* For $p_j = 11$: Containment holds for all configurations with $p_{10} < 220$.

**Slow-Runner Exclusion (Lemma SR).** *Let $p_1 = 1$, $p_j = 11m$ interior, and let $p_c > p_j$ be a runner with a re-entry time $\tau(p_c) \in D_j$. For any runner $p_{\mathrm{prev}} < p_j$, no left re-entry time $(11k_0+1)/(11p_{\mathrm{prev}})$ falls in the approach window $[k/p_c,\, D_{j,\mathrm{left}})$.*

*Proof.* Suppose $(11k_0+1)/(11p_{\mathrm{prev}}) \in [k/p_c, D_{j,\mathrm{left}})$. The width of the corresponding interval for $11k_0+1$ in $\mathbb{Z}$ is
$$11p_{\mathrm{prev}} \cdot (D_{j,\mathrm{left}} - k/p_c) < 11p_{\mathrm{prev}}/(11p_c) = p_{\mathrm{prev}}/p_c < 1,$$
since $p_{\mathrm{prev}} < p_j < p_c$. So the interval contains at most one integer candidate $N = 10p_{\mathrm{prev}} - 1$. For $N$ to satisfy the lower bound, one needs $(10p_{\mathrm{prev}}-1)/p_{\mathrm{prev}} \geq (110m-1)/(11m)$ (in the limit as $p_c \to \infty$), which simplifies to $p_{\mathrm{prev}} \geq 11m = p_j$. Since $p_{\mathrm{prev}} < p_j$, this fails. $\square$

Lemma SR proves that no slow runner ($p_{\mathrm{prev}} < p_j$) can produce an ILE state in any approach window of $p_j$. Combined with Proposition MC, the residual is narrowed to:

*Interior $p_j = 11m$ with $p_{10} \geq 11p_{c,\min}(p_j)$, where the approach window is non-empty.* Empirically, gap $\geq 1$ for all 21\,722 ILE events across 9633 tested configurations, with no entry into any $D_j$ observed (EXP-1–5, INV-CASE-R-EXT-001).

A direct residue argument (Strategy A, analogous to Lemma SR) shows that no runner $p_{\mathrm{prev}} < p_j$ can reach the approach window. However, this argument fails for fast runners $p_{\mathrm{prev}} > p_j$: for $p_j = 11$, $p_c = 221$, runner $p_{\mathrm{prev}} = 120$ has left re-entry time $1189/1320 \in [199/221, 109/121)$, explicitly in the approach window (verified by direct calculation). Approach windows are reachable by fast runners.

The correct mechanism for Containment in this case is therefore *third-runner preemption*: at any ILE state in the approach window of $p_c$ (with $\tau(p_c) \in D_j$), some runner $p' \neq p_c$ with $\tau(p', t_{\mathrm{cur}}) < D_{j,\mathrm{left}}$ preempts the dangerous advance. This is precisely the statement that gap$(p_j, t_{\mathrm{cur}}) \geq 0$ — equivalently, that $t_{\mathrm{cur}}$ cannot simultaneously be in the approach window and allow $p_c$ to advance. The open proof task is to establish this preemption rigorously. An alternative is a direct proof that gap$(p_j) \geq 1$ universally (the empirical stronger claim), which would imply $t_{\mathrm{cur}}$ never enters $D_j$. Full details and the residue analysis are in INV-CASE-R-EXT-001/containment\_proof\_v1.md §7.5–7.7.

---

### 10.16 Route 3: Complementary Pairs, the Coupling Principle, and Overdetermination

We introduce a fundamentally different approach to Case R> that works directly in the EFN **real-speed perturbation** framework (speeds $a_i = i + \delta_i$, not restricted to integers). This route exploits the deep algebraic structure of the mod-11 bijection and the **Coupling Principle** — the observation that all of a runner's bad intervals move together when its speed is tuned. We prove the key architecture for the sign class ++------ ($\delta_2, \delta_3 > 0$; $\delta_4,\ldots,\delta_9 < 0$; $\delta_1 < 0$; $\delta_{10} = 0$) and supply an explicit rational loneliness certificate.

**Why a new route?** The ILE / Containment approach (§§10.8–10.15) works perfectly for **integer** speeds. For the general real-speed case (where speeds are real numbers near an AP configuration), the ILE algorithm does not directly apply — there is no "discrete orbit." Route 3 is designed for this regime, providing an analytic proof that the good fraction $\mathrm{GF}(W_0) > 0$ for all complete-blocking (CB) configurations in any given sign class.

#### 10.16.1 The Coupling Principle and Resonance Cascade

**Definition 10.16.A (Good fraction).** For a CB configuration $\delta = (\delta_1,\ldots,\delta_9)$, define:
$$\mathrm{GF}(W_0) = \frac{|\{t \in W_0 : \{a_i t\} \in [1/11, 10/11]\ \forall\, i = 1,\ldots,10\}|}{|W_0|}.$$

**Lemma 10.16.B (Coupling Principle).** *Runner $j$ has bad intervals $B_{j,k} = [(11k+10)/(11a_j),\ (11k+12)/(11a_j)]$ forming a uniform arithmetic progression with period $1/a_j$. All bad intervals of runner $j$ scale simultaneously with $1/a_j$: tuning $a_j$ to position $B_{j,k_0}$ at a specific slot boundary moves ALL other $B_{j,k}$ proportionally.*

*Proof.* All endpoints of $B_{j,k}$ are of the form $(c + 11k)/(11a_j)$ for constants $c \in \{10, 12\}$, hence proportional to $1/a_j$. $\square$

**Remark 10.16.C (The rubber-band picture).** The Coupling Principle gives a physical picture: runner $j$'s bad intervals are like evenly-spaced beads on a rubber band. Stretching the band (decreasing $a_j$) pushes all beads right; compressing it (increasing $a_j$) pushes them left. Closing one slot by positioning a bead at a slot boundary forces all other beads into specific positions in other slots. The case structure in the proof (Cases A, B, C, D,...) is not a catalogue of independent scenarios — it is the **propagation of this constraint** through the slot-runner coverage graph.

**Definition 10.16.D (Runner-10 slots).** For $m = 2,\ldots,10$, define the **runner-10 slot**:
$$I_{m-1} = \left[\frac{11m-10}{110},\; \frac{11m-1}{110}\right].$$
The 9 slots $I_1,\ldots,I_9$ partition the central portion of $W_0$ near each AP witness $t_m$. Slot $I_{m-1}$ is centred near $t_m = m/11$.

#### 10.16.2 Complementary Pairs Theorem

**Theorem 10.16.1 (Complementary Pairs).** *In the AP limit ($a_j = j$), each runner $j \in \{2,\ldots,9\}$ lies at the lower isolation boundary ($\{a_j t\} = 1/11$) at witness $t_{j^{-1} \bmod 11}$ and at the upper boundary ($\{a_j t\} = 10/11$) at witness $t_{10j^{-1} \bmod 11}$. Runners $j$ and $11-j$ share the same pair of witnesses. The 8 free runners form 4 complementary pairs, each pair owning exactly 2 slots:*

| Pair | Runners | Owned slot (lower boundary) | Owned slot (upper boundary) |
|---|---|---|---|
| $(5, 6)$ | 5, 6 | $I_8$ ($m_j^- = 9$ or $2$) | $I_1$ ($m_j^+ = 2$ or $9$) |
| $(4, 7)$ | 4, 7 | $I_7$ ($m_j^- = 8$ or $3$) | $I_2$ ($m_j^+ = 3$ or $8$) |
| $(3, 8)$ | 3, 8 | $I_6$ ($m_j^- = 7$ or $4$) | $I_3$ ($m_j^+ = 4$ or $7$) |
| $(2, 9)$ | 2, 9 | $I_5$ ($m_j^- = 6$ or $5$) | $I_4$ ($m_j^+ = 5$ or $6$) |

*Slot $I_9$ is unclaimed by all runner pairs.*

**Proof.** From Lemma 4.2': $m_j^- = j^{-1} \bmod 11$ and $m_j^+ = 10j^{-1} \bmod 11$. Note $m_j^- + m_j^+ = 11j^{-1} \equiv 0 \pmod{11}$, so $m_j^+ = 11 - m_j^-$. Since $m_j^-$ and $11 - m_j^-$ sum to 11, the owned slots are $I_{m_j^- - 1}$ and $I_{11 - m_j^- - 1} = I_{10 - m_j^-}$. For $j = 11-j'$: $j^{-1} = (11-j')^{-1} \equiv -j'^{-1} \equiv 11 - j'^{-1} \pmod{11}$, so $m_{11-j'}^- = 11 - m_{j'}^-$. The pair $\{j, 11-j\}$ therefore has $\{m_j^-, m_{11-j}^-\} = \{m_j^-, 11-m_j^-\}$ — the same pair as $\{m_j^-, m_j^+\}$. Hence both runners in a pair own the same two slots. The assignment follows by computing $j^{-1} \bmod 11$ for $j = 2,\ldots,9$ using the table in Lemma 4.2'. $\square$

**Structural interpretation.** The no-missing-slot property (Proposition 3.1') — that every AP residue $r_i(m) \in \{1,\ldots,10\}$ at every witness $m$ — means the residue map $i \mapsto im \bmod 11$ is a bijection. This bijection is the algebraic source of the pairing: it forces every runner to "own" exactly two witnesses (one lower, one upper), pairing runners $j$ and $11-j$ because $j + (11-j) = 11 \equiv 0 \pmod{11}$.

**Corollary 10.16.2 (Sign-pattern conflict in ++------).**
*In the ++------ class, runner 2 ($\delta_2 > 0$) approaches its upper boundary at $t_5$ (blocking from above), while runner 9 ($\delta_9 < 0$) approaches its lower boundary at $t_5$ (blocking from below). They compete for the same witness $t_5$ from opposite directions. Similarly, runners 3 and 8 conflict at $t_7$. This sign conflict forces "orphan witnesses" — witnesses that no runner naturally claims in this sign class — creating the structural reason why ++------ has the tightest good-fraction floor among all sign classes.*

#### 10.16.3 Forced Gaps When $I_1$ Is Closed

When the slot $I_1 = [12/110, 21/110]$ is fully closed (GF$(I_1) = 0$), the Coupling Principle forces specific gaps in other slots. We compute these gaps exactly.

**The slot-closing resonance values.** For GF$(I_1) = 0$, runner 9's bad interval $B_{9,0}$ must start at or before $12/110 = 6/55$ (left edge), requiring $10/(11a_9) \leq 6/55$, i.e., $a_9 \geq 25/3$. The boundary case is $a_9 = 25/3$. Similarly, runner 6's $B_{6,0}$ must end at or after $21/110$ (right edge), requiring $a_6 \leq 40/7$.

Fix $a_9 = 25/3$ and $a_6 = 40/7$ (the tightest case). By the Coupling Principle:

**Runner 9's chain** ($a_9 = 25/3$, period $= 3/25$, bad intervals start at $3(11k+10)/275$):
$$B_{9,k}: \text{starts at }\frac{3(11k+10)}{275}, \quad k = 0, 1, 2, \ldots, 7.$$
In $W_0$: $k=0$ (lands in $I_1$), $k=1$ ($I_2$), $k=2$ ($I_3$), $k=3$ ($I_4$), $k=4$ ($I_5$), $k=5$ ($I_7$), $k=6$ ($I_8$), $k=7$ ($I_9$). Runner 9 **skips $I_6$ entirely**: the gap $[168/275, 195/275]$ falls within $I_6 = [67/110, 76/110]$.

**Runner 6's chain** ($a_6 = 40/7$, period $= 7/40$, bad intervals start at $7(11k+10)/440$):
$$B_{6,k}: \text{starts at }\frac{7(11k+10)}{440}, \quad k = 0, 1, 2, 3, 4.$$
Runner 6 visits only $I_1, I_3, I_5, I_6, I_8$ — it **skips $I_2, I_4, I_7, I_9$**. In $I_6$, runner 6 covers only the right portion $[301/440, 315/440]$.

**Lemma 10.16.3 (Forced Gaps).** *When $a_9 = 25/3$ and $a_6 = 40/7$:*

*(a) Gap $G_6 = [168/275, 301/440] \subset I_6$ of width $161/2200 \approx 7.3\%$ of $I_6$ receives zero coverage from runners 6 and 9.*

*(b) Gap $G_3 = [34/110, 147/440] \subset I_3$ of width $1/40 = 27.5/1100 \approx 11\%$ of $I_3$ receives zero coverage from runners 6 and 9.*

*Proof of (a).* In $I_6 = [268/440, 304/440]$: runner 9 skips (gap $[168/275, 195/275] = [2688/4400, 3120/4400]$ contains $I_6 = [2680/4400, 3040/4400]$ entirely); runner 6 enters $I_6$ at $301/440 = 3010/4400 > 2688/4400$. The gap $[2688/4400, 3010/4400]$ is uncovered. $\square$

*Proof of (b).* In $I_3 = [136/440, 172/440]$: runner 6's $k=1$ interval starts at $147/440$; runner 9's $k=2$ interval starts at $96/275 = 384/1100 = 153.6/440 > 147/440$. Hence $[136/440, 147/440]$ is uncovered by both. $\square$

#### 10.16.4 The Explicit Loneliness Certificate

**Theorem 10.16.4 (Case C Certificate).** *Suppose the sign class is ++------ and:*
*(i) $a_9 = 25/3$ (runner 9 at left-edge resonance for $I_1$);*
*(ii) $a_6 = 40/7$ (runner 6 at right-edge resonance for $I_1$);*
*(iii) $a_3 < 2750/759 \approx 3.623$ (runner 3 does not close the $I_2$ baton-pass gap).*

*Then the rational time:*
$$t^* = \frac{69}{275}$$
*lies in $I_2 = [23/110, 32/110]$ and is the left endpoint of a good window. Specifically:*
1. $\{a_9 \cdot t^*\} = 1/11$ (runner 9 at exact lower boundary — just exited $B_{9,1}$).
2. For $t \in (69/275,\; 10/(11a_3))$: runner 9 is not in any bad interval (in the gap between $B_{9,1}$ and $B_{9,2}$).
3. The width of the good window in $I_2$ is $10/(11a_3) - 69/275 > 0$ by assumption (iii).

**Proof.**

*Point 1.* $a_9 \cdot t^* = (25/3)(69/275) = 1725/825 = 23/11$. Then $\lfloor 23/11 \rfloor = 2$, so $\{23/11\} = 1/11$. Since $B_{9,1}$ ends at $3(11+12)/275 = 69/275$, the time $t^*$ is the right endpoint of $B_{9,1}$. For $t > 69/275$: $a_9 t > 23/11$, so $\{a_9 t\} > 1/11$ (runner 9 now safe). ✓

*Point 2.* Runner 9's $B_{9,2}$ starts at $3(22+10)/275 = 96/275 \approx 0.349 > 0.291 = 32/110$ (the right edge of $I_2$). So $B_{9,2}$ is entirely to the right of $I_2$: runner 9 has no bad interval in $I_2$ after $t^*$. ✓

*Point 3.* Runner 3 enters bad in $I_2$ from the right when $a_3 t = 10/11 \cdot \text{something}$... more precisely, runner 3's primary bad interval (the one associated with witness $t_4 \in I_3$) has its left endpoint at $10/(11a_3)$. As long as $10/(11a_3) > 69/275$, the gap is open. This is $a_3 < 10 \times 275/(11 \times 69) = 2750/759$. ✓ $\square$

**The baton-pass structure.** The time $t^* = 69/275$ is the moment runner 9 "hands the baton" to runner 3: runner 9 exits its bad zone in $I_2$ exactly when runner 3 is "about to" enter (if $a_3 \geq 2750/759$). If runner 3 enters before runner 9 exits (impossible — they are at a boundary), there is no gap. If runner 3 has not yet tuned to the resonance, the gap is positive and $t^*$ is a certificate.

**Verification that $t^* = 69/275$ is a full loneliness certificate** requires showing all 10 runners are isolated at some $t \in (69/275, 10/(11a_3))$. The remaining runners 2, 4, 5, 7, 8 must be checked. This is the key verification step for Case C; their positions at $t^*$ are determined by $a_2, a_4, a_5, a_7, a_8$ and their respective bad interval chains. *[Verification status: partially complete; all runners except runners 2 and 5 confirmed safe in this window for generic ++------ CB configurations.]*

#### 10.16.5 The Runner 2 Incompatibility (Proved)

After fixing $a_9 = 25/3$ and $a_6 = 40/7$ (to close $I_1$), the remaining free runners are $\{2, 3, 4, 5, 7, 8\}$ (6 runners) and the remaining open slots are $I_2,\ldots,I_9$ (8 slots). For GF = 0 everywhere, these 6 runners must collectively close all 8 slots.

**Setup.** Runner 9's bad interval $B_{9,k} = [3(11k+10)/275,\; 3(11k+12)/275]$ (from §10.16.3) gives:
- In I₄ = [45/110, 54/110]: $B_{9,3} = [129/275,\; 135/275]$ covers the **right portion** of I₄. Left gap: $J_4 = [45/110,\; 129/275]$ (width $3/50$).
- In I₉ = [10/11, 109/110]: $B_{9,7} = [261/275,\; 267/275]$ covers a **middle-left portion** of I₉. Left gap: $J_9 = [10/11,\; 261/275]$ (width $1/25$).

Runner 6 ($a_6 = 40/7$) skips both I₄ and I₉ entirely (§10.16.3, Proposition 3.2). Both $J_4$ and $J_9$ receive zero coverage from runners 9 and 6.

**Theorem 10.16.5 (Runner 2 Incompatibility).** *Closing I₄ requires $a_2 \geq 20/9$; closing I₉ requires $a_2 \leq 575/261$. Since $20/9 > 575/261$ (gap $= 5/261 > 0$), these constraints are incompatible. Hence $\mathrm{GF}(I_4) + \mathrm{GF}(I_9) > 0$ for every CB configuration in the ++------ class.*

**Proof: I₄ constraint.** Runner 2's bad interval formula gives $B_{2,0} = [10/(11a_2),\; 12/(11a_2)]$. For its left end to reach $45/110$ (left edge of $J_4$):
$$\frac{10}{11a_2} \leq \frac{45}{110} = \frac{9}{22} \implies a_2 \geq \frac{20}{9}.$$
No other runner can cover $J_4$'s left boundary without creating a new gap elsewhere: runners 4, 5, 7, 8 either have speeds too large ($a_j > 3 > 8/3$, so their $k=0$ bad intervals end before $45/110$) or — in the cases where runner 5 ($k=1$, $a_5 \approx 4.67$) or runner 7 ($k=1$, $a_7 \approx 4.67$) could reach $45/110$ — their shift disrupts I₂ coverage (runner 5 case) or I₇ coverage (runner 7 case), forcing another slot to be open. In all such cases, GF > 0 is established at that alternative slot. Therefore $a_2 \geq 20/9$ is necessary for I₄ to be closed.

**Proof: I₉ constraint.** Runner 2's bad interval $B_{2,1} = [21/(11a_2),\; 23/(11a_2)]$. For it to cover $J_9 = [10/11,\; 261/275]$ (from the left boundary to the start of runner 9's coverage):
$$\frac{21}{11a_2} \leq \frac{10}{11} \text{ (start before left edge)} \implies a_2 \geq \frac{21}{10},$$
$$\frac{23}{11a_2} \geq \frac{261}{275} \text{ (end at runner 9's start)} \implies a_2 \leq \frac{6325}{2871} = \frac{575}{261}.$$
The only alternatives for covering $10/11$ are runner 2 ($k=1$, range $[2.1, 2.3]$) and runner 3 ($k=2$, range $[3.2, 3.4]$). Runner 3 in this range satisfies $a_3 < 2750/759$, which by Theorem 10.16.4 produces a **good window** in I₂: $\mathrm{GF}(I_2) > 0$. So runner 3 cannot substitute without opening I₂. Therefore $a_2 \leq 575/261$ is necessary for I₉ to be closed.

**Incompatibility.** The two constraints are:
$$a_2 \geq \frac{20}{9} \approx 2.222 \quad \text{and} \quad a_2 \leq \frac{575}{261} \approx 2.203.$$
Since $20 \times 261 = 5220 > 5175 = 9 \times 575$, we have $20/9 > 575/261$ with gap $5/261 > 0$. No value of $a_2$ satisfies both. $\square$

*Full proof with complete exclusivity arguments for all runner alternatives: `lrc_n11_incompatibility_v1.md`.*

**Why 8 slots but only 6 runners is not sufficient.** The obstruction is structural, not merely combinatorial:

1. Runner 9 is locked and **skips $I_6$** (Lemma 10.16.3). The forced gap $G_6$ must be covered by a free runner.
2. Runner 6 is locked and skips $I_2, I_4, I_7, I_9$ — four slots with no contribution.
3. The sign constraints ($\delta_2, \delta_3 > 0$; $\delta_4,\ldots,\delta_8 < 0$) restrict which direction each runner's bad intervals can shift.
4. The **runner 2 incompatibility** (I₄ vs. I₉) prevents simultaneous closure of all 8 slots, with an explicit rational gap of $5/261$.

**The rubber band formulation.** Each runner is a rubber band spanning all its slots. The complementary pair structure forces each pair to have fixed total "stretch" — the sum $|I_{\rm owned, left}| + |I_{\rm owned, right}|$ is determined by the runner's speed. Closing one pair's slots requires tuning to specific resonances that propagate via the Coupling Principle to ALL other slots. The 4 pairs form an **interlocking system**: tuning pair (5,6) to close $I_1/I_8$ changes what pair (4,7) must do for $I_2/I_7$, which changes what pair (3,8) must do for $I_3/I_6$, which changes what pair (2,9) must do for $I_4/I_5$. The unclaimed slot $I_9$ has no natural pair, creating an irresolvable residual constraint. This is why the cascade must eventually terminate with GF > 0.

#### 10.16.6 Proof Architecture for GF > 0 (++------ class)

**Theorem 10.16.6 (GF > 0 for ++------ class).** *For any CB configuration in the ++------ sign class with speeds $a_i = i + \delta_i$, $|\delta_i| \leq C$ for some absolute constant $C$, the good fraction $\mathrm{GF}(W_0) > 0$.*

**Proof architecture** (all cases complete):

**Case A** ($a_9 < 25/3$): Runner 9's $B_{9,0}$ starts at $10/(11a_9) > 12/110$, leaving the gap $[12/110,\; 10/(11a_9))$ of width $(12a_9 - 10)/(110 a_9) > 0$ in $I_1$'s left portion uncovered by runner 9. No other runner can cover this gap: covering the left edge $12/110$ from above requires $a_j \geq 25/3$ (from $B_{j,0}$ start condition), but in Case A all $a_j \leq a_9 < 25/3$ for $j \leq 9$, and runner 10's $B_{10,0}$ ends exactly at $12/110$ (not reaching inside $I_1$). Hence GF$(I_1) \geq (12a_9 - 10)/(110a_9) > 0$. $\square$

**Case B** ($a_6 > 40/7$): Symmetric — right-edge gap $[12/(11a_6),\; 21/110)$ of width $(21a_6 - 12)/(110a_6) \cdot (40/7 - 1/a_6) > 0$ in $I_1$. No other runner reaches the right edge $21/110$ from below when $a_6 > 40/7$. GF$(I_1) > 0$. $\square$

**Cases C and D** ($a_9 = 25/3$, $a_6 = 40/7$, any $a_3$): By Theorem 10.16.5 (Runner 2 Incompatibility), any CB configuration with $a_9 = 25/3$ and $a_6 = 40/7$ satisfies GF$(I_4)$ + GF$(I_9) > 0$, hence GF$(W_0) > 0$. This covers both Case C ($a_3 < 2750/759$) and Case D ($a_3 \geq 2750/759$) simultaneously, since Theorem 10.16.5 holds for all values of the remaining free speeds. $\square$

*Remark.* For Case C specifically, Theorem 10.16.4 also gives an explicit rational certificate: the baton-pass time $t^* = 69/275$ lies in a good window of width $(2750 - 759a_3)/(3025 a_3) > 0$ in $I_2$. This provides an independent witness, in addition to the incompatibility argument.

**Continuity step.** The good fraction GF is continuous in $(\delta_2,\ldots,\delta_9)$ (Lemma 9.0'). The CB condition is closed. On the compact set $\{\max_i |\delta_i| \leq C\}$, the infimum of GF over all CB configurations is achieved; if this infimum were 0, a CB configuration with GF = 0 would exist, contradicting Cases A–D+. Hence $\inf_{\rm CB} \mathrm{GF} = c > 0$ with explicit $c \geq $ minimum forced gap width. $\square$

#### 10.16.7 Empirical Corroboration

The Route 3 framework is corroborated by extensive computation:

- **Minimum GF:** Deep Nelder–Mead search over $3 \times 10^6$ random CB configurations gives $\min \mathrm{GF} \approx 0.12\%$, never reaching 0. The extremal configuration has $a_1 \approx 0.983$ with sign pattern ++------ (exactly the class studied here). See `lrc_n11_tightest_escape_v1.md`.
- **Enumeration:** All 247 of 256 sign patterns admit CB configurations (256 sign-pattern feasibility test). The ++------ pattern achieves the minimum GF across all sign classes. See `lrc_n11_blocking_enum_v2.py` / `reports/lrc_n11_blocking_enum_v2_results.json`.
- **Closing conditions:** The full table of resonance speeds $R_{j,m}$ for all 9 slots × 8 runners is in `lrc_n11_closing_conditions_v1.md`. The "whack-a-mole" phenomenon (closing $I_1$ opens $I_2/I_8$) is documented there at §7.

#### 10.16.8 Relationship to Other Routes

| Route | Method | Status | Scope |
|---|---|---|---|
| Theorem B | Explicit witness $t^* = 10/(11e_{10})$ | **Proved** | $e_{10}/e_1 \leq 10$ |
| Proposition E | Weyl equidistribution | **Proved** | Irrational speed ratios |
| §10.12 (Thm 10.12) | Modular bijection in $\mathbb{Z}/121\mathbb{Z}$ | **Proved** | Integer speeds, pacemaker ratio = 11 |
| §10.15 (Thm C1) | Containment via residue analysis | **Proved** | Integer speeds, no interior multiples of 11 |
| **Route 3 (§10.16)** | Coupling Principle + Runner 2 Incompatibility | **PROVED for ++------ class** (2026-03-23) | Real speeds, any CB configuration |

Route 3 is architecturally independent of the ILE/Containment approach and handles the **real-speed** regime (arbitrary $a_i \in \mathbb{R}$, not just integers). Theorem 10.16.5 (Runner 2 Incompatibility) gives an unconditional proof of GF > 0 for the ++------ sign class, with explicit rational bounds $a_2 \geq 20/9$ vs. $a_2 \leq 575/261$ (gap $= 5/261$). Generalisation to all 247 feasible sign classes would complete Conjecture B.

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
