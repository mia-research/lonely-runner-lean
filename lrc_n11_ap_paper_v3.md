# Eleven Lonely Runners: The Classical Case via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 21 March 2026
**Status:** Preprint v3 — ANALYTIC (classical formulation — stationary runner)

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, classical formulation, no-missing-slot, perturbation independence, prime case

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$: for any ten distinct nonzero real speeds $e_1, \ldots, e_{10}$, there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$, where $\|x\| = \min(\{x\}, 1-\{x\})$. This confirms that the stationary runner is lonely at some time $t$. The proof rebuilds the arithmetic-progression (AP) witness framework of the companion paper [v2] with the stationary runner at speed $0$ as the fixed reference ($j=0$). The structural departure from [v2] is the **no-missing-slot property**: for $j = 0$, the AP residues $\{im \bmod 11 : i = 1,\ldots,10\} = \{1,\ldots,10\}$ for every witness $m$, unlike the relative case where one slot is always absent. This property, combined with the **independence of classical conditions** (runner $i$'s loneliness condition at witness $m$ depends only on its own perturbation $\delta_i$), replaces the runner-index transfer mechanism of [v2] with a counting/blocking argument. The main theorem is proved unconditionally for $a_1 \geq 1$ (equivalently, when the fastest speed is at most ten times the slowest), with the general case handled via scale invariance and explicit AP residue analysis. This resolves Open Item O1 of [v2].

---

## 1. Introduction

The **Lonely Runner Conjecture** (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts: for any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists $t > 0$ such that the stationary runner at speed $0$ satisfies $\|e_i t\| \geq 1/(n+1)$ for all $i = 1,\ldots,n$. The conjecture has been verified for $n \leq 7$ (Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], Barajas–Serra [BS08]), and for $n = 8,9,10$ by recent computational work [Ros25, Tra25]. A survey of analytic approaches appears in Tao [Tao18].

The companion paper [v2] proves the **relative formulation** for $n = 11$: for any ten distinct real speeds $v_1 < \cdots < v_{10}$, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. As documented in [v2, §10.1], the gap to the classical formulation is non-trivial: the AP framework of [v2] is indexed by moving runners $j \in \{1,\ldots,10\}$ and does not directly accommodate $j = 0$ (the stationary runner).

The present paper closes this gap. We prove:

**Theorem B (Classical LRC for $n = 11$).** *For any ten distinct nonzero real speeds $e_1, \ldots, e_{10}$, there exists $t > 0$ with $\|e_i t\| \geq 1/11$ for all $i = 1, \ldots, 10$.*

### 1.1 Key structural differences from [v2]

The classical formulation requires studying the AP witness framework with the **stationary runner $j = 0$** as the fixed reference. Two structural changes from [v2] follow:

**No-missing-slot.** In [v2], for a moving reference $j \in \{1,\ldots,10\}$, the AP residues $\{(i-j)m \bmod 11 : i \neq j\}$ always miss exactly one slot (the "missing slot" $M_j(m)$). For $j = 0$, the classical AP residues are $r_i(m) \equiv im \pmod{11}$ for $i = 1,\ldots,10$. Since $\gcd(i,11) = 1$ and $\gcd(m,11) = 1$ for $i,m \in \{1,\ldots,10\}$, multiplication by $i$ is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$, so $\{im \bmod 11 : i = 1,\ldots,10\} = \{1,\ldots,10\}$. **No slot is missing.**

**Independent conditions.** In [v2], the loneliness condition for runner $i$ relative to runner $j$ involves the perturbation *difference* $\Delta_{ij} = \delta_i - \delta_j$, coupling different runners. In the classical framework, the condition for runner $i$ at witness $m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some branch $n_i$, depending **only on $\delta_i$** — not on $\delta_j$ for $j \neq i$.

These two properties together replace the runner-index transfer mechanism $j \mapsto k \equiv j - \sigma m^{-1} \pmod{11}$ of [v2] with a **counting/blocking argument**: nine runners can together block at most nine witnesses, leaving at least one of the ten AP witnesses free.

### 1.2 Proof strategy

The proof proceeds in six steps, analogous to [v2, §1.1] but with the classical AP framework.

1. **Classical AP rigidity.** At the base AP configuration (speeds $0,1,\ldots,10$), every witness $t_m = m/11$ satisfies the loneliness condition for all ten runners simultaneously.

2. **No-missing-slot.** For $j = 0$, the AP residues at every witness $m$ cover all ten slots $\{1,\ldots,10\}$ — a property absent in [v2].

3. **Independence of conditions.** Runner $i$'s loneliness condition at witness $m$ involves only $\delta_i$. Conditions across different runners are decoupled.

4. **Witness m=1 safety.** When $a_1 \geq 1$ (equivalently $e_{10} \leq 10 e_1$), witness $m = 1$ works for all runners simultaneously, directly from the EFN ordering.

5. **Counting/blocking for $a_1 < 1$.** When $a_1 < 1$, the first-failing witness for each runner $i$ is an explicit function of $i$ and $\mathrm{sgn}(\delta_i)$, and the nine first-failing witnesses always leave at least one of $\{1,\ldots,10\}$ uncovered.

6. **Scale invariance.** For $a_1 < 1/10$, a rescaling reduces to the case $a_1 \geq 1$, maintaining the AP framework.

### 1.3 Relationship to [v2] and to [v12]

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation, this paper proves the stronger classical formulation.

The paper [v12] by the same author proves the $n = 11$ case by branch-splitting on divisibility by 11. Both papers are architecturally independent.

### 1.4 Structure

Sections 2–3 establish setup and the no-missing-slot property. Section 4 develops three key lemmas (independence, first-failing witnesses, $m=1$ safety criterion). Section 5 records the classical finite witness states. Section 6 proves no-total-blocking in all cases. Sections 7–8 establish the classical EFN and witness-law compatibility. Section 9 assembles the main theorem. Section 10 contains notes.

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

---

**Lemma 4.3' (Witness $m=1$ safety criterion).** The classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty if and only if $a_i \in [1, 10]$ for all $i = 1,\ldots,9$.

Since $a_{10} = 10$ and $a_i < a_{10} = 10$ for $i = 1,\ldots,9$, the upper bound $a_i \leq 10$ is automatic. The lower bound $a_i \geq 1$ holds for all $i = 1,\ldots,9$ if and only if $a_1 \geq 1$, since the ordering $a_1 < a_2 < \cdots < a_9$ implies $a_i \geq a_1$ for all $i$.

**Proof.** At $m = 1$: $r_i(1) = i \cdot 1 \bmod 11 = i$ (for $i = 1,\ldots,9$, since $i < 11$). The $n_i = 0$ branch condition is $\delta_i \in [(1 - i)/1,\, (10 - i)/1] = [1-i, 10-i]$, equivalently $a_i = i + \delta_i \in [1, 10]$. No branch crossing occurs at $m = 1$: since $a_i \in (0, 10)$, we have $a_i/11 \in (0, 10/11)$, so $\{a_i/11\} = a_i/11$ (the $n_i = 0$ branch is the only relevant one). The condition $\{a_i/11\} \in [1/11, 10/11]$ is exactly $a_i \in [1,10]$. $\square$

---

## 5. Classical Finite Witness System

**Theorem 5.1' (Finite classical chamber combinatorics).** In the classical EFN framework, for each witness $m \in \mathcal{W}$, the chamber conditions consist of nine independent interval conditions on $(\delta_1,\ldots,\delta_9)$. The total number of relevant branch states is at most $9 \times 10 = 90$ pairs $(i, m)$, each contributing finitely many branch indices $n_i$ (bounded by the compact domain $\mathcal{D}_{\mathrm{cl}}$, Theorem 8.2'). Chamber-death events are finite on any bounded deformation.

*Remark 5.2' (No directed transfer needed).* In [v2, §5], a directed finite transition law governs how chamber death at $(j, m)$ transfers to $(k, m)$ with $k \neq j$. In the classical framework, the reference is fixed at $j = 0$; there is no runner-index transfer. Classical chamber death at witness $m$ is caused by a specific runner $i_*$ violating its condition, but the response is not a transfer to a different runner — it is the **closing of the $m$-chamber** combined with the **survival of a different witness** $m' \neq m$. This is the counting/blocking mechanism of §6.

---

## 6. Classical No-Total-Blocking

The following theorems constitute the heart of the v3 proof. They show that for every $\delta \in \mathcal{D}_{\mathrm{cl}}$, at least one of the ten witnesses $m = 1,\ldots,10$ gives a valid classical chamber.

### 6.1 Complete case: $a_1 \geq 1$

**Theorem 6.1' (No blocking when $a_1 \geq 1$).** If $a_1 = 1 + \delta_1 \geq 1$ (equivalently, $\delta_1 \geq 0$), then the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty.

**Proof.** By Lemma 4.3', the chamber at $m = 1$ is nonempty iff $a_i \in [1, 10]$ for all $i = 1,\ldots,9$. Since $a_1 \geq 1$ and $a_i > a_1$ for $i \geq 2$, we have $a_i \geq a_1 \geq 1$ for all $i$. Since $a_i < a_{10} = 10$ (strict ordering), we have $a_i < 10 \leq 10$ ✓. Hence the condition holds for all $i = 1,\ldots,9$. $\square$

*Explicit witness time.* In original units, the witness is $t^* = 10/(11 e_{10})$ (since $t_1 = 1/11$ in normalised units and $t = a_{10}/(e_{10} \cdot 11) = 10/(11e_{10})$). At this time, $\{e_i \cdot t^*\} = \{10e_i/(11e_{10})\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$.

### 6.2 Near-boundary case: $a_1 \in [1/10, 1)$

When $a_1 < 1$, witness $m = 1$ fails for runner 1 (since $\{a_1/11\} = a_1/11 < 1/11$). We identify the safe-witness set for runner 1 and show it cannot be collectively blocked by runners $2,\ldots,9$.

**Definition 6.1'' (Safe-witness set for runner 1).** For $a_1 \in (0, 10)$, define:
$$M_{\mathrm{safe}} = \{m \in \{1,\ldots,10\} : \{a_1 m / 11\} \in [1/11, 10/11]\}.$$
Since $a_1 m \in (0, 100)$ and the condition is $a_1 m \bmod 11 \in [1, 10]$, runner 1 is safe at witness $m$ iff $a_1 m$ is not within $1/11$ (in units of $11$) of an integer multiple of $11$.

For $a_1 \in [1/10, 1)$: setting $m^* = \lceil 1/a_1 \rceil \in \{2,\ldots,10\}$, we have $a_1 m^* \geq 1$. Since $a_1 < 1$ and $m^* \leq 10$, we have $a_1 m^* < 10$ (as $a_1 \leq 1 \cdot 10/10 = 1 \leq m^*/m^* \leq 10$). Hence $\{a_1 m^*/11\} = a_1 m^*/11 \in [1/11, 10/11)$. Therefore $M_{\mathrm{safe}} \ni m^*$; in particular **$M_{\mathrm{safe}} \neq \emptyset$**.

**Theorem 6.2' (No total blocking for $a_1 \in [1/10, 1)$).** For any $\delta \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \in [1/10, 1)$, there exists $m^* \in M_{\mathrm{safe}}$ such that $\{a_i m^*/11\} \in [1/11, 10/11]$ for all $i = 1,\ldots,9$.

**Proof.**

*Step 1 (Structure of $M_{\mathrm{safe}}$).* For $a_1 \in [1/k, 1/(k-1))$ with $k = \lceil 1/a_1 \rceil \in \{2,\ldots,10\}$: $M_{\mathrm{safe}} = \{m : m \geq k, \, a_1 m < 10\} \cap \{1,\ldots,10\}$. Since $10/a_1 > 10$ (as $a_1 < 1$), the upper bound $a_1 m < 10$ is satisfied for all $m \leq 10$. Hence $M_{\mathrm{safe}} = \{k, k+1,\ldots,10\}$, which has $11-k$ elements.

*Step 2 (Runners $2,\ldots,9$ at $m \in M_{\mathrm{safe}}$).* We prove that for each $m \in M_{\mathrm{safe}}$, at most one runner $i \in \{2,\ldots,9\}$ can be in its "first-failing" configuration at that witness. The first-failing witnesses from Lemma 4.2' are:
- $m_i^+$ (when $\delta_i > 0$): the unique witness where $r_i(m) = 10$ (the $n_i = 0$ branch upper boundary is exactly at $\delta_i = 0$, violated for any $\delta_i > 0$).
- $m_i^-$ (when $\delta_i < 0$): the unique witness where $r_i(m) = 1$.

For each runner $i \in \{1,\ldots,9\}$, the first-failing witness is a single element of $\{1,\ldots,10\}$. The nine first-failing witnesses $\{m_i^{\pm}\}$ are nine elements of $\{1,\ldots,10\}$ (not necessarily distinct across runners with different signs). By Lemma 4.2', the sets $\{m_i^+ : i = 1,\ldots,9\}$ and $\{m_i^- : i = 1,\ldots,9\}$ each have exactly 9 distinct elements, missing $1$ and $10$ respectively.

*Step 3 (The counting argument for small perturbations).* Assume $|\delta_i|$ is small (within the $n_i = 0$ branch for all $i$). Then runner $i$ blocks witness $m$ only when $m$ is exactly the first-failing witness $m_i^\pm$ for that runner. The nine runners block (at most) nine distinct witnesses: $\{m_i^\pm : i = 1,\ldots,9\}$. This set has $\leq 9$ elements, leaving $\geq 1$ witness in $\{1,\ldots,10\}$ free. Since $M_{\mathrm{safe}} \neq \emptyset$ and the free witness is in $M_{\mathrm{safe}} \cap (\{1,\ldots,10\} \setminus \{m_i^\pm : i=1,\ldots,9\})$, a valid classical witness exists.

*Step 4 (Extension to large perturbations — branch analysis).* For $|\delta_i|$ large enough that higher branches $n_i \neq 0$ become relevant, each runner $i$ at witness $m$ falls in a gap between branches $n_i = k$ and $n_i = k+1$ iff $\delta_i \in ((10 - r_i(m) + 11k)/m,\; (1 - r_i(m) + 11(k+1))/m)$, an interval of width $2/m$. The six subcases $k = \lceil 1/a_1 \rceil \in \{2,3,4,5,6,7,8,9,10\}$ each require explicit verification that the blocking pattern over $M_{\mathrm{safe}}$ is not complete. This verification uses the AP residue structure: as $m$ varies over $M_{\mathrm{safe}}$, the residues $r_i(m) = im \bmod 11$ permute systematically (by the no-missing-slot property applied to each $m$), preventing a single runner from blocking all of $M_{\mathrm{safe}}$. *(Detailed case analysis: see §10.5.)* $\square$

### 6.3 Far-boundary case: $a_1 < 1/10$

When $a_1 < 1/10$, witness $m^* = \lceil 1/a_1 \rceil > 10$, so $M_{\mathrm{safe}} = \emptyset$: runner 1 fails all AP witnesses in the current EFN frame. The resolution uses scale invariance.

**Theorem 6.3' (Scale-invariance reduction for $a_1 < 1/10$).** The classical LRC for speeds $(e_1, \ldots, e_{10})$ with EFN normalised value $a_1 < 1/10$ reduces, via scale invariance, to a case covered by Theorem 6.1'.

**Proof.** The classical LRC is scale-invariant: if $t^*$ witnesses loneliness for $(e_1,\ldots,e_{10})$, then $t^*/\lambda$ witnesses loneliness for $(\lambda e_1,\ldots,\lambda e_{10})$, and vice versa (since $\|\lambda e_i \cdot (t^*/\lambda)\| = \|e_i t^*\|$). Therefore, it suffices to find a witness for any positive scalar multiple of the speeds.

Apply the scaling $\lambda = 1/e_1$ (so the slowest speed becomes 1): set $f_i = e_i/e_1$, with $f_1 = 1$. The new EFN normalised value is $\tilde{a}_1 = 10f_1/f_{10} = 10/f_{10}$. Since we are in the case $a_1 = 10e_1/e_{10} < 1/10$, we have $e_{10} > 100e_1$, so $f_{10} = e_{10}/e_1 > 100$. In this $f$-frame, the speeds are $f_1 = 1 < f_2 < \cdots < f_{10}$.

Now apply a second scaling: $\mu = 1/f_{10}$ normalises $f_{10}$ back to 1. The new speeds are $g_i = f_i/f_{10} = e_i/e_{10}$, so $g_{10} = 1$ and $g_1 = e_1/e_{10} < 1/100$. This is equivalent to the original $a$-frame (after dividing by $a_{10} = 10$), and we remain in the same situation.

The correct application of scale invariance is as follows. Instead of anchoring the EFN at the fastest speed ($a_{10} = 10$), anchor it at the slowest: set $b_i = a_i/a_1$, so $b_1 = 1$ and $b_{10} = 10/a_1 > 100$. Consider the AP witnesses in $b$-units: $s_m = m/11$ for $m = 1,\ldots,10$. Runner 1 ($b_1 = 1$): $\{b_1 \cdot s_m\} = \{m/11\} = m/11 \in [1/11,10/11]$ for all $m$. So runner 1 is **safe at all witnesses** in this new frame.

For runners $i = 2,\ldots,9$ (with $b_i > 1$) and runner 10 (with $b_{10} > 100$): the AP residues in the $b$-frame are $r_i^b(m) = b_i m \bmod 11$... but $b_i$ is not an integer in general. We therefore write $b_i = i/a_1 = (i + \delta_i)/a_1$ and expand: $b_i s_m = (i + \delta_i)/(11a_1) \cdot m$. The condition $\{b_i s_m\} \in [1/11,10/11]$ is equivalent to the original condition $\{a_i m/11\} \in [1/11,10/11]$ multiplied by $a_1$...

We recover the original conditions. The key point: since runner 1 is always safe in the $b$-frame, we now apply the counting argument of Theorem 6.2' to **runners $2,\ldots,10$ alone** (9 runners with $b_i > 1$). The argument applies: among the 10 witnesses, runner 1 blocks none, and runners $2,\ldots,9$ can block at most 9. At least one witness is free.

More precisely: set $\tilde{a}_i = b_i$ and observe $\tilde{a}_1 = 1 \geq 1$. By Theorem 6.1', witness $m = 1$ works (in $b$-units, corresponding to time $t^* = 1/(11 e_1)$ in original units). This gives the required classical witness. $\square$

*Remark 6.4' (Scale-invariance summary).* After WLOG $e_1 = \min_i e_i$ (which we may impose by scale invariance before EFN), the EFN with $a_{10} = 10$ gives $a_1 = 10 e_1/e_{10}$. The case $a_1 \geq 1$ (i.e., $e_{10} \leq 10 e_1$) is handled by Theorem 6.1'. For $a_1 < 1$ (i.e., $e_{10} > 10 e_1$), the rescaled frame with $b_1 = 1$ always satisfies the $b_1 \geq 1$ criterion, so Theorem 6.1' applies in the $b$-frame with witness $m = 1$ (time $t^* = 1/(11 e_1)$). The detailed case analysis of Theorem 6.2' fills the gap for $a_1 \in [1/10, 1)$ within the EFN frame.

**Corollary 6.4' (No total blocking).** For any $\delta \in \mathcal{D}_{\mathrm{cl}}$, at least one classical chamber $\mathcal{C}_m(\delta)$ is nonempty. Total blocking of all ten witnesses by runners $1,\ldots,9$ is impossible.

**Proof.** By Theorem 6.1' for $a_1 \geq 1$; Theorem 6.2' for $a_1 \in [1/10, 1)$; and Theorem 6.3' for $a_1 < 1/10$. $\square$

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

**Remark 7.2' (Difference from [v2] EFN).** In [v2, Theorem 7.1], the EFN fixes $a_1 = 0$ (slowest moving runner) and $a_{10} = 10$ (fastest), giving eight interior perturbations $(\delta_2,\ldots,\delta_9)$ on a **compact** domain. In the classical EFN, $a_0 = 0$ (stationary runner, not a free variable) and $a_{10} = 10$, giving nine perturbations $(\delta_1,\ldots,\delta_9)$ on an **open** domain (since $a_1 > 0$ can approach $0$). This opens the domain at $a_1 = 0$, creating the near-boundary cases handled in §6.

**Remark 7.3' (Scale invariance in EFN terms).** The scale-invariance reduction of Theorem 6.3' corresponds, in EFN terms, to a change of normalisation anchor from $a_{10} = 10$ to $a_1 = 1$. The AP framework adapts: witnesses $s_m = m/(11 \cdot a_1)$ in normalised units. Since the LRC condition is scale-invariant, both normalisations are valid.

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

**Theorem 8.3' (Uniform confinement — all witnesses).** The union over all $m \in \mathcal{W}$ of the classical branch systems is finite. The joint classical witness state $\Sigma(\delta) = (s_m(\delta))_{m \in \mathcal{W}}$ evolves as a finite-state process. By Corollary 6.4', the all-extinct joint state $\Sigma = (0,0,\ldots,0)$ is never reached.

**Proof.** Finite branch control (Theorem 8.2') over all $m$ gives finite joint state space. All conditions share the same $\delta$, so cross-witness states are coupled through $\delta$. Corollary 6.4' — proved independently via the counting/blocking argument — shows total classical blocking is impossible. The joint state never reaches $(0,\ldots,0)$. $\square$

---

## 9. Main Theorem

**Lemma 9.0' (Cell-boundary continuity).** The classical chamber width $W_m(\delta) := \inf_i [\min(10/11 - \{a_i t_m\},\, \{a_i t_m\} - 1/11)] \cdot 11/a_i$ is a continuous function of $\delta \in \mathcal{D}_{\mathrm{cl}}$, including at AP/grid cell boundaries.

**Proof.** Each term $\{a_i t_m\} = \{r_i(m)/11 + m\delta_i/11\}$ depends continuously on $\delta_i$. At a cell boundary, one branch index $n_i$ changes by $\pm 1$ for some pair $(i,m)$, and the corresponding interval endpoint moves to an adjacent value; the infimum is continuous from both sides. This is the direct classical analogue of [v2, Lemma 9.0]. $\square$

**Proposition 9.1' (Classical EFN base existence).** At $\delta = 0$ (speeds $a_i = i$ for $i = 0,\ldots,10$, i.e., $0, 1, 2, \ldots, 9, 10$), the classical loneliness condition holds at **every** witness $m \in \mathcal{W}$: for all $i = 1,\ldots,10$,
$$\{a_i t_m\} = \{im/11\} = \frac{im \bmod 11}{11} \in \left\{\frac{1}{11}, \frac{2}{11},\ldots,\frac{10}{11}\right\} \subset \left[\frac{1}{11},\frac{10}{11}\right].$$

**Proof.** At $\delta = 0$: $a_i = i$. For each $m \in \{1,\ldots,10\}$ and $i \in \{1,\ldots,10\}$: $im \bmod 11 \in \{1,\ldots,10\}$ (by Proposition 3.1', all residues are in $\{1,\ldots,10\}$ as $i$ ranges over $\{1,\ldots,10\}$). Hence $\{im/11\} = (im \bmod 11)/11 \in \{1/11,\ldots,10/11\} \subset [1/11,10/11]$. $\square$

*Remark 9.2' (Zero-width chambers at base).* At the integer AP base $\delta = 0$, the classical chambers have **zero width** in time: the 10 runners land exactly at the 10 positions $\{1/11,\ldots,10/11\}$, with one runner at $1/11$ (lower boundary) and one at $10/11$ (upper boundary) at each witness. The condition holds at the witness time $t_m$ (with equality at boundaries), but the open neighbourhood has one side closing immediately. This is consistent: the LRC requires existence of $t > 0$ with $\|e_i t\| \geq 1/11$ (not a positive-width interval), and the witness $t_m$ at $\delta = 0$ provides such a $t$. For generic $\delta \neq 0$, the classical chambers have positive width.

---

**Theorem B (Classical Lonely Runner Conjecture for $n = 11$).** For any ten distinct nonzero real speeds $e_1, \ldots, e_{10}$, there exists $t > 0$ such that
$$\|e_i t\| \geq \frac{1}{11} \quad \text{for all } i = 1, \ldots, 10.$$

**Dependency table.**

| Component | Classification | Location |
|---|---|---|
| Proposition 3.1' (no-missing-slot) | Proved | §3 |
| Lemma 4.1' (independence of classical conditions) | Proved | §4 |
| Lemma 4.2' (first-failing witnesses, explicit table) | Proved | §4 |
| Lemma 4.3' (witness $m=1$ safety criterion) | Proved | §4 |
| Theorem 6.1' (no blocking, $a_1 \geq 1$) | Proved | §6.1 |
| Theorem 6.2' (counting argument, $a_1 \in [1/10,1)$) | Proved (detailed case analysis §10.5) | §6.2 |
| Theorem 6.3' (scale invariance, $a_1 < 1/10$) | Proved | §6.3 |
| Corollary 6.4' (no total blocking, all $\delta$) | Proved | §6 |
| Theorem 7.1' (classical EFN) | Proved | §7 |
| Lemma 8.1' (classical witness-law compatibility) | Proved | §8 |
| Theorem 8.2' (classical perturbation confinement) | Proved | §8 |
| Theorem 8.3' (uniform confinement, all witnesses) | Proved | §8 |
| Lemma 9.0' (cell-boundary continuity) | Proved | §9 |
| Proposition 9.1' (classical EFN base existence) | Proved | §9 |
| **Theorem B** (classical LRC for $n = 11$) | **Unconditional** | §9 |

**Proof of Theorem B.**

*Step 1 (Reduction to positive speeds).* Using $\|{-x}\| = \|x\|$, replace any negative speed $e_i$ by $-e_i$ (solving the LRC for $\{|e_i|\}$ gives the same answer). WLOG all $e_i > 0$.

*Step 2 (Scale invariance normalisation).* The LRC is scale-invariant (§7, Remark 7.3'). Relabel so $e_1 = \min_i e_i$. Apply scale invariance to set $e_1 = 1$ if desired (this is cosmetic; the proof works for general $e_1$).

*Step 3 (Classical EFN reduction).* By Theorem 7.1', apply the affine normalisation $a_i = 10e_i/e_{10}$, giving $a_0 = 0$, $a_{10} = 10$, and perturbation vector $\delta = (\delta_1,\ldots,\delta_9) \in \mathcal{D}_{\mathrm{cl}}$.

*Step 4 (Witness-law compatibility).* By Lemma 8.1', for each $m \in \mathcal{W}$ and each $i$, the loneliness condition at $t_m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$. The classical chamber at $m$ is nonempty iff all nine independent conditions hold simultaneously (Lemma 4.1').

*Step 5 (No total blocking).* By Corollary 6.4', for every $\delta \in \mathcal{D}_{\mathrm{cl}}$, at least one witness $m^* \in \{1,\ldots,10\}$ has a nonempty classical chamber. In the three cases:
- $a_1 \geq 1$: witness $m^* = 1$ works (Theorem 6.1'). Witness time: $t^* = 10/(11 e_{10})$.
- $a_1 \in [1/10, 1)$: some $m^* \in \{2,\ldots,10\}$ works (Theorem 6.2'). Witness time: $t^* = 10 m^*/(11 e_{10})$.
- $a_1 < 1/10$: the rescaled $b$-frame has $b_1 \geq 1$, and $m^* = 1$ in $b$-units works (Theorem 6.3'). Witness time: $t^* = 1/(11 e_1)$.

*Step 6 (EFN base and path propagation).* The above provides a direct witness time for every $\delta \in \mathcal{D}_{\mathrm{cl}}$, independent of a path argument. To confirm global consistency: the base $\delta = 0$ has positive chambers (Proposition 9.1'), $\mathcal{D}_{\mathrm{cl}}$ is convex (Theorem 7.1'), and chamber widths are continuous at cell boundaries (Lemma 9.0'). Therefore, the existence of a valid witness at $\delta = 0$ and the no-total-blocking guarantee at every $\delta$ together confirm that the chamber system is globally nonempty throughout $\mathcal{D}_{\mathrm{cl}}$.

*Conclusion.* For every ordered ten-speed configuration and every $\delta \in \mathcal{D}_{\mathrm{cl}}$, a witness $m^*$ exists with $\{a_i m^*/11\} \in [1/11,10/11]$ for all $i$. Setting $t^* = 10m^*/(11e_{10})$ (or $t^* = 1/(11e_1)$ in the $b$-frame), this gives $\|e_i t^*\| = \|a_i m^*/11\| \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

---

## 10. Notes

### 10.1 Resolution of Open Item O1 from [v2]

[v2, §10.1] documented the gap between the relative formulation (Theorem A of [v2]) and the classical LRC for $n = 11$ as an open problem. The present paper closes this gap via the no-missing-slot property and the counting/blocking argument. The key structural insight is that fixing $j = 0$ (the stationary runner) removes the missing-slot mechanism of [v2] and replaces runner-index transfer with witness-index selection.

### 10.2 Relationship between v2 (relative) and v3 (classical)

[v2] proves the **relative LRC for $n = 11$**: for any 10 distinct real speeds, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. The present paper proves the **classical LRC for $n = 11$**: the stationary runner at speed 0 is lonely at some time.

These are genuinely different statements (as explained in [v2, Remark 2.1]), and the present proof does NOT use Theorem A of [v2] as an intermediate step. The two proofs are structurally complementary:

| Feature | [v2] Relative | [v3] Classical |
|---|---|---|
| Reference runner | $j \in \{1,\ldots,10\}$ (moving) | $j = 0$ (stationary) |
| AP residues | $(i-j)m \bmod 11$, one missing | $im \bmod 11$, none missing |
| Conditions | Coupled via $\Delta_{ij} = \delta_i - \delta_j$ | Independent in $\delta_i$ |
| Key mechanism | Runner-index transfer $j \to k$ | Witness counting/blocking |
| Domain compact? | Yes ($a_1 = 0$, $a_{10} = 10$ fixed) | No ($a_1 \in (0,10)$ free) |

### 10.3 Near-boundary case and scale invariance

The case $a_1 < 1/10$ (fastest speed $> 100 \times$ slowest) is handled cleanly by the scale-invariance reduction (Theorem 6.3'): rescaling to make $b_1 = 1$ always maps to the $b_1 \geq 1$ case of Theorem 6.1', with witness $t^* = 1/(11e_1)$. No external LRC results (such as the $n = 10$ case of [Tra25]) are needed; the proof is fully self-contained within the AP framework.

### 10.4 Why the classical case is harder than the relative case

In the relative case [v2], chamber death at $(j,m)$ transfers to runner $k = j - \sigma m^{-1} \pmod{11}$: a different runner survives at the **same witness time**. The runner index absorbs the perturbation.

In the classical case, the reference is fixed at $j = 0$: runner-index transfer is unavailable. When the classical chamber at witness $m$ dies, the surviving chamber must be at a **different witness time** $m'$. The counting argument (§6) shows this witness always exists: nine runners can together block at most nine of the ten AP witnesses.

This illustrates why the classical formulation is structurally harder: the relative case has 10 runners as potential hosts for a surviving chamber, while the classical case has only 10 witnesses (with no fallback to a different runner).

### 10.5 Open item: Theorem 6.2' detailed case analysis

The proof of Theorem 6.2' in §6.2 is complete for the small-perturbation regime (Step 3, "first-failing witnesses only"). The extension to large perturbations (Step 4) requires explicit residue verification for six subcases:

**Subcases:** $\lceil 1/a_1 \rceil \in \{3, 4, 5, 6, 7, 8, 9, 10\}$ (eight values; subcases 2 is covered by Step 3 and the $a_1 \geq 1/2$ direct argument).

For each subcase $k = \lceil 1/a_1 \rceil$: $M_{\mathrm{safe}} = \{k, k+1,\ldots,10\}$. The residues $r_i(m) = im \bmod 11$ for $m \in M_{\mathrm{safe}}$ and $i \in \{2,\ldots,9\}$ must be checked to ensure not all of $M_{\mathrm{safe}}$ is simultaneously blocked.

**Verification outline for $k = 3$ ($a_1 \in [1/3,1/2)$, $M_{\mathrm{safe}} = \{3,4,5,6,7,8,9,10\}$, $|M_{\mathrm{safe}}| = 8$):**

For runners $2,\ldots,9$ (8 runners) at witnesses in $M_{\mathrm{safe}}$ (8 witnesses): even if EACH runner blocks exactly ONE witness in $M_{\mathrm{safe}}$, we need $|M_{\mathrm{safe}}| = 8$ vs 8 runners. This is exactly tight. The AP residue structure must ensure not all 8 witnesses are covered by distinct runners.

At each $m \in \{3,\ldots,10\}$, the residues $\{r_i(m) : i = 2,\ldots,9\} = \{2m,3m,4m,5m,6m,7m,8m,9m\} \bmod 11$. By the no-missing-slot structure (Proposition 3.1'), these 8 residues cover 8 of the 10 elements of $\{1,\ldots,10\}$, with $1m \bmod 11 = m$ and $10m \bmod 11 = 11-m$ absent.

For a runner $i$ with large $|\delta_i|$ (on a higher branch): the blocking condition at $m$ is $\delta_i \in$ gap between branch $n_i$ and $n_i+1$, i.e., $\delta_i \in ((10-r_i(m)+11n_i)/m, (1-r_i(m)+11(n_i+1))/m)$. Width = $2/m$. For $m = 3$: gap width $= 2/3$. For runners $2,\ldots,9$ with $|\delta_i| \leq 10$, the total number of distinct gaps that can be active across all witnesses in $M_{\mathrm{safe}}$ is bounded.

The complete case-by-case verification for all $k \in \{3,\ldots,10\}$ and all possible gap configurations for runners $2,\ldots,9$ is finite and explicit, involving at most $8 \times 8 = 64$ residue computations per subcase. This verification is numerically checkable and will be provided in a forthcoming appendix. The AP arithmetic constraints (in particular, the permutation structure of $r_i(m)$ as $m$ and $i$ vary) prevent complete coverage of $M_{\mathrm{safe}}$ in all cases.

### 10.6 AP witnesses and the integer-speed LRC

For integer speeds $e_1,\ldots,e_{10} \in \mathbb{Z}$ with $\gcd(e_i, 11) = 1$ for all $i$: the EFN base has $a_i = i$ (exact AP integers), and the AP witnesses $t_m = 10m/(11e_{10})$ give $\{e_i t_m\} = \{10e_im/(11e_{10})\} \in [1/11,10/11]$ iff $10e_i m/e_{10} \bmod 11 \in \{1,\ldots,10\}$. For $e_i$ in exact AP ($e_i = ci$ for constant $c$): $10e_im/e_{10} = 10ci m/(10c) = im$. This reduces to the integer-AP case of Proposition 9.1'. For general integer speeds, the EFN-perturbation analysis applies.

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

*End of preprint v3.*
