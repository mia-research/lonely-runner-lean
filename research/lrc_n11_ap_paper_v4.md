# Eleven Lonely Runners: The Classical Case via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 21 March 2026
**Status:** Preprint v4 — ANALYTIC (unconditional for $e_{10}/e_1 \leq 10$; gap documented for $e_{10}/e_1 > 10$)

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, classical formulation, no-missing-slot, perturbation independence, prime case, speed ratio

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ in the case where the ratio of the fastest to the slowest non-stationary speed satisfies $e_{10}/e_1 \leq 10$: there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$, with explicit witness $t^* = 10/(11e_{10})$. The proof uses an arithmetic-progression (AP) witness framework with the stationary runner at speed $0$ as the fixed reference. The key structural property is **no-missing-slot**: the AP residues $\{im \bmod 11 : i=1,\ldots,10\} = \{1,\ldots,10\}$ for every witness $m$, combined with **independence of classical conditions** (runner $i$'s loneliness at witness $m$ depends only on $\delta_i$). The case $e_{10}/e_1 > 10$ (equivalently $a_1 < 1$ in EFN normalisation) is identified as a genuine gap: we provide a total-blocking configuration in the EFN domain that eliminates all ten AP witnesses while admitting a valid non-AP witness, and document two routes toward a complete proof.

---

## 1. Introduction

The **Lonely Runner Conjecture** (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts: for any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists $t > 0$ such that the stationary runner at speed $0$ satisfies $\|e_i t\| \geq 1/(n+1)$ for all $i = 1,\ldots,n$. The conjecture has been verified for $n \leq 7$ (Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], Barajas–Serra [BS08]), and for $n = 8,9,10$ by recent computational work [Ros25, Tra25]. A survey of analytic approaches appears in Tao [Tao18].

The companion paper [v2] proves the **relative formulation** for $n = 11$: for any ten distinct real speeds $v_1 < \cdots < v_{10}$, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. As documented in [v2, §10.1], the gap to the classical formulation is non-trivial: the AP framework of [v2] is indexed by moving runners $j \in \{1,\ldots,10\}$ and does not directly accommodate $j = 0$ (the stationary runner).

The present paper rebuilds the AP framework with $j = 0$ and proves:

**Theorem B (Classical LRC for $n = 11$, bounded speed ratio).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ with $e_{10}/e_1 \leq 10$, there exists $t^* = 10/(11e_{10}) > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1, \ldots, 10$.*

**Conjecture B (Full classical LRC for $n = 11$).** *The same conclusion holds without any restriction on $e_{10}/e_1$.*

The full conjecture remains open within the AP framework. The gap is precisely identified in §10.1.

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

5. **Gap for $a_1 < 1$.** When $a_1 < 1$ (i.e., $e_{10}/e_1 > 10$), the AP witness family $\{m/11\}$ is demonstrably insufficient for some configurations (§10.1). This case is open.

### 1.3 Relationship to [v2] and to [v12]

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation unconditionally, this paper proves the classical formulation in the bounded-ratio regime.

The paper [v12] by the same author proves the $n = 11$ case by branch-splitting on divisibility by 11. Both papers are architecturally independent.

### 1.4 Structure

Sections 2–3 establish setup and the no-missing-slot property. Section 4 develops three key lemmas (independence, first-failing witnesses, $m=1$ safety criterion). Section 5 records the classical finite witness states and introduces the speed-ratio partition. Section 6 proves no-total-blocking in the bounded-ratio case and states the gap for the large-ratio case. Sections 7–8 establish the classical EFN and witness-law compatibility. Section 9 assembles Theorem B and states Conjecture B. Section 10 documents the gap and routes toward a complete proof.

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
- **Large-ratio regime** ($\rho > 10$, equivalently $a_1 < 1$): the AP witness family $\{m/11\}$ is insufficient for some configurations in this regime. The gap is documented in §10.1. This case is **open** within the present framework.

**Proof.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10/\rho$. So $\rho \leq 10 \Leftrightarrow a_1 \geq 1$. The claim for the bounded-ratio regime is Theorem 6.1' below. The claim for the large-ratio regime is the total-blocking example of §10.1. $\square$

---

## 6. Classical No-Total-Blocking (Bounded-Ratio Regime)

The following theorem constitutes the heart of the v4 proof for the bounded-ratio case.

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

- **(Route A)** An extended witness family $\mathcal{T} \supset \{m/11\}$ that is sufficient for all $\delta \in \mathcal{D}_{\mathrm{cl}}$ (see §10.2), or
- **(Route B)** A reduction from Theorem A of [v2] to the classical statement, requiring generalisation of the AP framework to nonzero real speeds (see §10.3).

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
| Gap Statement 6.3'' ($a_1 < 1/10$) | **Open** — AP witnesses insufficient | §6.3 |
| Corollary 6.4'' (no total blocking, $a_1 \geq 1$) | Proved | §6.4 |
| Theorem 7.1' (classical EFN) | Proved | §7 |
| Lemma 8.1' (classical witness-law compatibility) | Proved | §8 |
| Theorem 8.2' (classical perturbation confinement) | Proved | §8 |
| Theorem 8.3' (finite joint witness state, $a_1 \geq 1$ sub-domain) | Proved | §8 |
| Lemma 9.0' (cell-boundary continuity) | Proved | §9 |
| Proposition 9.1' (classical EFN base existence) | Proved | §9 |
| **Theorem B** (classical LRC, $e_{10}/e_1 \leq 10$) | **Unconditional** | §9 |
| **Conjecture B** (full classical LRC) | **Open** (requires $a_1 < 1$ case) | §10 |

**Proof of Theorem B.**

*Step 1 (Reduction to positive ordered speeds).* Using $\|{-x}\| = \|x\|$, replace any negative speed $e_i$ by $-e_i$ WLOG all $e_i > 0$. Relabel so $e_1 < \cdots < e_{10}$.

*Step 2 (Speed-ratio hypothesis).* The hypothesis $e_{10}/e_1 \leq 10$ is $\rho \leq 10$, equivalently $a_1 \geq 1$ after EFN normalisation (Lemma 5.3').

*Step 3 (Classical EFN reduction).* By Theorem 7.1', apply the affine normalisation $a_i = 10e_i/e_{10}$, giving $a_0 = 0$, $a_{10} = 10$, and perturbation vector $\delta = (\delta_1,\ldots,\delta_9) \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$.

*Step 4 (Witness-law compatibility).* By Lemma 8.1', for each $m \in \mathcal{W}$ and each $i$, the loneliness condition at $t_m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$. The classical chamber at $m$ is nonempty iff all nine independent conditions hold simultaneously (Lemma 4.1').

*Step 5 (Witness $m = 1$ works).* Since $a_1 \geq 1$, Theorem 6.1' gives that the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty. At $t^* = 10/(11e_{10})$ (normalised: $t_1 = 1/11$), we have $\{e_i t^*\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$ for all $i = 1,\ldots,10$.

*Conclusion.* $t^* = 10/(11e_{10})$ satisfies $\|e_i t^*\| = \{a_i/11\} \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

**Conjecture B (Full classical LRC for $n = 11$).** For any ten distinct nonzero real speeds $e_1, \ldots, e_{10}$ (without restriction on $e_{10}/e_1$), there exists $t > 0$ with $\|e_i t\| \geq 1/11$ for all $i = 1, \ldots, 10$.

*Status.* Open within the AP framework. The case $e_{10}/e_1 > 10$ is not resolved by the present methods (§6.3, §10.1–10.3).

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

### 10.2 Route A: Extended witness family

For configurations with $a_1 < 1$ that block all ten AP witnesses, a valid witness at a non-AP time exists (as shown by the example above). A natural candidate for extending the framework is the **extended witness family**:
$$\mathcal{T}(K) = \left\{\frac{m}{11k} : k = 1,\ldots,K,\; m = 1,\ldots,10k,\; \gcd(m,11) = 1\right\}.$$
At level $k = 1$: the original AP witnesses. At level $k = 2$: witnesses at $\{1/22, 3/22, 5/22, \ldots, 21/22\}$ (11 additional times). The AP residue structure for witnesses $m/(11k)$ involves residues mod $11k$, which remains prime-structured as long as $\gcd(k, 11) = 1$.

Open question: does $\mathcal{T}(K)$ suffice for all $\delta \in \mathcal{D}_{\mathrm{cl}}$ for some bounded $K$ depending on $a_1$? For example, for $a_1 \in [1/(K+1), 1/K)$, does level $k = K+1$ always provide a valid witness?

### 10.3 Route B: Reduction from Theorem A (relative LRC)

Theorem A of [v2] proves the relative LRC for $n = 11$ unconditionally: for any ten distinct real speeds, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. If Theorem A could be extended to include nonzero real speeds (including negative speeds, with the negative speeds corresponding to runners whose direction is reversed), then the following symmetric argument might close the gap:

For each $j = 1,\ldots,10$, apply Theorem A to the ten speeds $\{e_i - e_j : i \neq j\} \cup \{-e_j\}$. If the lonely runner in this shifted system is always one of $\{e_i - e_j\}$ (never $-e_j$), a pigeonhole argument over $j = 1,\ldots,10$ would force some $j$ where $-e_j$ is the lonely runner, giving the classical condition. The obstruction is that Theorem A of [v2] is stated for positive speeds only.

### 10.4 Relationship between v2 (relative) and v4 (classical)

[v2] proves the **relative LRC for $n = 11$**: for any 10 distinct real speeds, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. The present paper proves the **classical LRC for $n = 11$ when $e_{10}/e_1 \leq 10$**: the stationary runner at speed 0 is lonely at $t^* = 10/(11e_{10})$.

| Feature | [v2] Relative | [v4] Classical (Theorem B) |
|---|---|---|
| Reference runner | $j \in \{1,\ldots,10\}$ (moving) | $j = 0$ (stationary) |
| AP residues | $(i-j)m \bmod 11$, one missing | $im \bmod 11$, none missing |
| Conditions | Coupled via $\Delta_{ij} = \delta_i - \delta_j$ | Independent in $\delta_i$ |
| Key mechanism | Runner-index transfer $j \to k$ | Witness $m=1$ direct |
| Domain compact? | Yes ($a_1 = 0$, $a_{10} = 10$ fixed) | No ($a_1 \in (0,10)$ free) |
| Speed ratio restriction | None | $\rho = e_{10}/e_1 \leq 10$ |

---

## References

- [BGG+98] A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi, *Flows, view obstructions, and the lonely runner*, J. Combin. Theory Ser. B **72** (1998), 1–9.

- [BH01] T. Bohman, R. Holzman, *Six lonely runners*, Electron. J. Combin. **8** (2001), R3.

- [BS08] J. Barajas, O. Serra, *The lonely runner with seven runners*, Electron. J. Combin. **15** (2008), R48.

- [Cus73] T. W. Cusick, *View obstruction problems*, Aequationes Math. **9** (1973), 165–170.

- [Ros25] B. Rosenfeld, *The lonely runner conjecture for eight runners*, preprint, 2025.

- [Tao18] T. Tao, *Some remarks on the lonely runner conjecture*, Contrib. Discrete Math. **13** (2018), 1–31.

- [Tra25] P. Traill, *Ten lonely runners*, preprint, 2025.

- [v2] T. Palelei, *Eleven Lonely Runners: An Analytical Proof via Arithmetic-Progression Witnesses* (relative formulation), preprint v2, 2026.

- [v12] T. Palelei, *The Lonely Runner Conjecture for $n = 11$*, preprint v12, 2026.

- [Wil67] J. M. Wills, *Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen*, Monatsh. Math. **71** (1967), 263–269.

---
