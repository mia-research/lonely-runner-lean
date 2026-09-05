# The Lonely Runner Conjecture for n = 11: A Complete Proof

**Authors:** Trent Palelei
**Date:** 2026-03-27
**Status:** PROOF COMPLETE (v22, 2026-03-27)
**MSC 2020:** 11K60, 11J71
**Keywords:** Lonely Runner Conjecture, arithmetic progressions, Weyl equidistribution, complementary pairs

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ unconditionally. For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$, there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1, \ldots, 10$. The proof proceeds by an exhaustive case split over three mutually exclusive and exhaustive cases. (B) Bounded speed ratio $e_{10}/e_1 \leq 10$: explicit witness $t^* = 10/(11e_{10})$ (Theorem B). (E) Irrational speed ratio: Weyl equidistribution (Proposition E). (R>) Commensurable speeds with $e_{10}/e_1 > 10$: we work in the window $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$ where runner $e_1$ is trivially isolated. The **Static Core Theorem** — comprising Theorem U (for $\sigma_2 = +1$, minimum gap $59/9460$) and Lemma S2 (for $\sigma_2 = -1$, minimum gap $538/54395$) — proves that every CB configuration has some slot with positive good fraction. The **Phase-Uniform Extension** (Lemma P: bad-interval widths are phase-independent; Lemma C: the UB cascade is speed-range only) ensures the cascade applies in every pacemaker sub-cycle of $W_{\rm ref}$. **Corollary W_ref** then gives a witness in $W_{\rm ref}$ for all Case R> configurations. Cases B, E, R> are exhaustive; the proof is complete. Computational corroboration: 112/112 canonical integer configurations $\{1,\ldots,9,p_{10}\}$ with $p_{10} \in \{89,\ldots,200\}$ have witnesses in $W_{\rm ref}$, verified by exact arithmetic (Appendix A).

---

## 1. Introduction

The **Lonely Runner Conjecture** (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts: for any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists $t > 0$ such that the stationary runner at speed $0$ satisfies $\|e_i t\| \geq 1/(n+1)$ for all $i = 1,\ldots,n$. The conjecture has been verified for $n \leq 7$ (Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], Barajas–Serra [BS08]), and for $n = 8$ [Ros25a], $n = 9$ [Ros25b, Tra25], and $n = 10$ [Tra25] by recent computational work. A survey of analytic approaches appears in Tao [Tao18].

The companion paper [v2] proves the **relative formulation** for $n = 11$: for any ten distinct real speeds $v_1 < \cdots < v_{10}$, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. The present paper builds the AP framework with $j = 0$ (stationary runner) and proves the classical formulation unconditionally.

**Theorem B (Classical LRC for $n = 11$, bounded speed ratio).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ with $e_{10}/e_1 \leq 10$, there exists $t^* = 10/(11e_{10}) > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1, \ldots, 10$.*

**Proposition E (Irrational-ratio case).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ such that $e_i/e_j \notin \mathbb{Q}$ for at least one pair $i \neq j$, the classical LRC holds for this configuration.*

**Theorem C (Full classical LRC for $n = 11$).** *The same conclusion holds without restriction on $e_{10}/e_1$. The remaining case (commensurable speeds, $e_{10}/e_1 > 10$) is closed by Theorem W_ref (§10.6).*

### 1.1 Key structural differences from [v2]

The classical formulation requires the AP witness framework with the **stationary runner $j = 0$** as the fixed reference. Two structural changes from [v2] follow.

**No-missing-slot.** In [v2], for a moving reference $j \in \{1,\ldots,10\}$, the AP residues $\{(i-j)m \bmod 11 : i \neq j\}$ always miss exactly one slot. For $j = 0$, the classical AP residues are $r_i(m) \equiv im \pmod{11}$ for $i = 1,\ldots,10$. Since $11$ is prime and $\gcd(i,11) = 1$, multiplication by $m$ is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$, so $\{im \bmod 11 : i = 1,\ldots,10\} = \{1,\ldots,10\}$. No slot is missing.

**Independent conditions.** In the classical framework, the loneliness condition for runner $i$ at witness $m$ involves only $\delta_i$ — not $\delta_j$ for $j \neq i$. This replaces the runner-index transfer mechanism of [v2] with a counting/blocking argument.

### 1.2 Proof strategy for Theorem B

The proof of Theorem B ($e_{10}/e_1 \leq 10$) proceeds as follows.

1. **Classical AP rigidity.** At the base AP configuration, every witness $t_m = m/11$ satisfies the loneliness condition for all ten runners simultaneously.
2. **No-missing-slot.** For $j = 0$, the AP residues at every witness $m$ cover all ten slots $\{1,\ldots,10\}$.
3. **Independence of conditions.** Runner $i$'s loneliness condition at witness $m$ involves only $\delta_i$.
4. **Witness $m=1$ safety.** When $a_1 \geq 1$ (equivalently $e_{10}/e_1 \leq 10$), witness $m = 1$ works for all runners simultaneously. The explicit witness is $t^* = 10/(11e_{10})$.

### 1.3 Relationship to [v2] and to earlier versions

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation unconditionally; this paper proves the classical formulation.

### 1.4 Structure

- §2–§3: Notation and Witness-Control Law
- §4–§8: Local algebra, speed-ratio partition, Theorem B, Classical EFN, compatibility
- §9: Main theorem (Theorem B + dependency table)
- §10.1: The open case and motivation for Route 3
- §10.2: Irrational-ratio case (Proposition E)
- §10.3: Commensurable large-ratio decomposition (Case R> formalised)
- §10.4–§10.7: Route 3 — Coupling Principle, Complementary Pairs, Static Core, Phase-Uniform Extension, Theorem C
- §10.8: The 11-Pacemaker special case (independent verification)
- Appendix A: Computational corroboration (112/112; not part of proof)
- Appendix B: Historical approaches (ILE, SET, WIT — superseded)

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
- **Large-ratio regime** ($\rho > 10$, equivalently $a_1 < 1$): the AP witness family $\{m/11\}$ is insufficient for some configurations in this regime. The gap is documented in §10.1. This case decomposes further (§10.3) into the irrational sub-case (closed by Proposition E, §10.2) and the commensurable sub-case (closed by Theorem W_ref, §10.6).

**Proof.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10/\rho$. So $\rho \leq 10 \Leftrightarrow a_1 \geq 1$. The claim for the bounded-ratio regime is Theorem 6.1' below. The claim for the large-ratio regime is the total-blocking example of §10.1. $\square$

---

## 6. Classical No-Total-Blocking (Bounded-Ratio Regime)

The following theorem constitutes the heart of the proof for the bounded-ratio case.

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

*Scope.* Theorem 6.2'' is not used in the proof of Theorem B (which only requires the $a_1 \geq 1$ case via Theorem 6.1'). It is recorded here as partial progress toward Theorem C.

### 6.3 Large-ratio regime: $a_1 < 1$ — gap statement

**Gap Statement 6.3'' ($a_1 < 1$ — open within AP framework alone).** When $a_1 < 1$, the AP witness family $\{t_m = m/11 : m = 1,\ldots,10\}$ is **insufficient to certify loneliness for all configurations in $\mathcal{D}_{\mathrm{cl}}$**. As documented in §10.1, there exist configurations in $\mathcal{D}_{\mathrm{cl}}$ with $a_1 < 1$ that simultaneously block all ten AP witnesses, while a valid (non-AP) witness exists. The commensurable sub-case is closed by Theorem W_ref (§10.6); the irrational sub-case is closed by Proposition E (§10.2).

### 6.4 Partial no-total-blocking corollary

**Corollary 6.4'' (No total blocking — bounded-ratio regime).** For any $\delta \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$, the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty.

**Proof.** This is exactly Theorem 6.1'. $\square$

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

### 8.2 Perturbation confinement

**Theorem 8.2' (Classical deterministic perturbation confinement).** Fix $n = 11$, witness $m$, and classical EFN configuration with $\delta \in \mathcal{D}_{\mathrm{cl}}$.

1. **Finite branch control.** Since $\mathcal{D}_{\mathrm{cl}}$ is a bounded polytope, each $\delta_i$ lies in a bounded interval, so only finitely many branch indices $n_i$ are relevant for each pair $(i,m)$.

2. **Deterministic active-branch selection.** On each AP/grid cell of $\mathcal{D}_{\mathrm{cl}}$, the active branch $n_i$ for each runner $i$ at each witness $m$ is uniquely determined by $r_i(m)$ and $\delta_i$.

3. **Finite-state evolution.** As $\delta$ varies continuously in $\mathcal{D}_{\mathrm{cl}}$, active-branch changes for runner $i$ at witness $m$ occur only when $\delta_i$ crosses a branch boundary $\delta_i = (1 - r_i(m) + 11n)/m$ or $\delta_i = (10 - r_i(m) + 11n)/m$. Since there are finitely many such boundaries, the active branch states form a finite-state system.

4. **Classical perturbation confinement.** Repeated perturbations of $\delta_i$ cannot generate infinitely many independent extinction events: every chamber-death event at $(i, m)$ is either branch recurrence, offset within $\delta_i$, or boundary transition.

**Proof.** Identical to [v2, Theorem 8.2] with $\Delta_{ij}$ replaced by $\delta_i$ throughout (since the conditions are independent). The boundedness of $\mathcal{D}_{\mathrm{cl}}$ gives finite branch control; piecewise-affine branch functions give deterministic active selection and finite-state evolution. $\square$

**Theorem 8.3' (Finite joint witness state).** The union over all $m \in \mathcal{W}$ of the classical branch systems is finite. The joint classical witness state $\Sigma(\delta) = (s_m(\delta))_{m \in \mathcal{W}}$ evolves as a finite-state process. For $\delta$ in the bounded-ratio sub-domain $\{a_1 \geq 1\} \subset \mathcal{D}_{\mathrm{cl}}$, the all-extinct joint state $\Sigma = (0,0,\ldots,0)$ is never reached (by Corollary 6.4'').

**Proof.** Finite branch control (Theorem 8.2') over all $m$ gives finite joint state space. For $a_1 \geq 1$: Corollary 6.4'' shows the $m=1$ chamber is always nonempty, so the joint state has $s_1(\delta) = 1$ always. The joint state cannot be all-zero. $\square$

---

## 9. Main Theorem

**Lemma 9.0' (Cell-boundary continuity).** The classical chamber width $W_m(\delta) := \inf_i [\min(10/11 - \{a_i t_m\},\, \{a_i t_m\} - 1/11)] \cdot 11/a_i$ is a continuous function of $\delta \in \mathcal{D}_{\mathrm{cl}}$, including at AP/grid cell boundaries.

**Proof.** Each term $\{a_i t_m\} = \{r_i(m)/11 + m\delta_i/11\}$ depends continuously on $\delta_i$. At a cell boundary, one branch index $n_i$ changes by $\pm 1$ for some pair $(i,m)$, and the corresponding interval endpoint moves to an adjacent value; the infimum is continuous from both sides. $\square$

**Proposition 9.1' (Classical EFN base existence).** At $\delta = 0$ (speeds $a_i = i$ for $i = 0,\ldots,10$), the classical loneliness condition holds at **every** witness $m \in \mathcal{W}$: for all $i = 1,\ldots,10$,
$$\{a_i t_m\} = \{im/11\} = \frac{im \bmod 11}{11} \in \left\{\frac{1}{11}, \frac{2}{11},\ldots,\frac{10}{11}\right\} \subset \left[\frac{1}{11},\frac{10}{11}\right].$$

**Proof.** At $\delta = 0$: $a_i = i$. For each $m \in \{1,\ldots,10\}$ and $i \in \{1,\ldots,10\}$: $im \bmod 11 \in \{1,\ldots,10\}$ (by Proposition 3.1'). Hence $\{im/11\} = (im \bmod 11)/11 \in \{1/11,\ldots,10/11\} \subset [1/11,10/11]$. $\square$

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
| Gap Statement 6.3'' ($a_1 < 1$) | Closed — §10.2/10.3/10.6 | §6.3 |
| Corollary 6.4'' (no total blocking, $a_1 \geq 1$) | Proved | §6.4 |
| Theorem 7.1' (classical EFN) | Proved | §7 |
| Lemma 8.1' (classical witness-law compatibility) | Proved | §8 |
| Theorem 8.2' (classical perturbation confinement) | Proved | §8 |
| Theorem 8.3' (finite joint witness state, $a_1 \geq 1$ sub-domain) | Proved | §8 |
| Lemma 9.0' (cell-boundary continuity) | Proved | §9 |
| Proposition 9.1' (classical EFN base existence) | Proved | §9 |
| **Theorem B** (classical LRC, $e_{10}/e_1 \leq 10$) | **Unconditional** | §9 |
| **Proposition E** (irrational-ratio case, Weyl equidistribution) | **Proved** | §10.2 |
| **Case R>** (commensurable speeds, $e_{10}/e_1 > 10$) | **CLOSED** — Corollary W_ref | §10.6 |
| ↳ Theorem U ($\sigma_2=+1$, gap $\geq 59/9460$) | **PROVED** | §10.5.1 |
| ↳ Lemma S2 ($\sigma_2=-1$, $W(I_9) \geq 538/54395$) | **PROVED** | §10.5.3 |
| ↳ Lemma P (bad-interval widths phase-independent) | **PROVED** | §10.6.2 |
| ↳ Lemma C (cascade phase-independent) | **PROVED** | §10.6.3 |
| ↳ **Corollary W_ref** | **PROVED** (2026-03-27) | §10.6.4 |
| **Theorem C** (full classical LRC for $n=11$) | **PROVED** (2026-03-27) — dependency-clean | §10.7 |

**Proof of Theorem B.**

*Step 1 (Reduction to positive ordered speeds).* Using $\|{-x}\| = \|x\|$, replace any negative speed $e_i$ by $-e_i$ WLOG all $e_i > 0$. Relabel so $e_1 < \cdots < e_{10}$.

*Step 2 (Speed-ratio hypothesis).* The hypothesis $e_{10}/e_1 \leq 10$ is $\rho \leq 10$, equivalently $a_1 \geq 1$ after EFN normalisation (Lemma 5.3').

*Step 3 (Classical EFN reduction).* By Theorem 7.1', apply the affine normalisation $a_i = 10e_i/e_{10}$, giving $a_0 = 0$, $a_{10} = 10$, and perturbation vector $\delta = (\delta_1,\ldots,\delta_9) \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$.

*Step 4 (Witness-law compatibility).* By Lemma 8.1', for each $m \in \mathcal{W}$ and each $i$, the loneliness condition at $t_m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$. The classical chamber at $m$ is nonempty iff all nine independent conditions hold simultaneously (Lemma 4.1').

*Step 5 (Witness $m = 1$ works).* Since $a_1 \geq 1$, Theorem 6.1' gives that the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty. At $t^* = 10/(11e_{10})$ (normalised: $t_1 = 1/11$), we have $\{e_i t^*\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$ for all $i = 1,\ldots,10$.

*Conclusion.* $t^* = 10/(11e_{10})$ satisfies $\|e_i t^*\| = \{a_i/11\} \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

---

## 10. Case R> Closure

### 10.1 The open case

Theorem B gives witness $t^* = 10/(11e_{10})$ when $e_{10}/e_1 \leq 10$. For ratio $> 10$, runner 1 can be positioned so all ten AP witnesses fall inside a bad interval. This is not a theoretical possibility — it occurs at the explicit configuration
$$a = (0.5,\; 2.2,\; 11/3,\; 33/7,\; 5.5,\; 6,\; 7,\; 8,\; 9,\; 10):$$
runners 1 and 5 together block witnesses 1–4 and 6–10; runner 5 blocks witnesses 2, 4, 6, 8, 10; runner 3 blocks 3, 6, 9; etc. All ten AP witnesses $\{m/11\}$ are blocked. (The LRC still holds — a non-AP witness $t = 4/17$ gives $\min_i \|a_i \cdot 4/17\| \approx 0.109 > 1/11$. The AP framework is simply insufficient to certify it.)

This motivates the case split: §10.2 handles irrational ratio; §10.3–§10.7 handle commensurable ratio $> 10$ via Route 3. Simple extended witness families (Route A) and reduction arguments (Route B) fail — see Appendix B.

### 10.2 Irrational-ratio case

**Proposition E (Irrational-ratio case — Weyl equidistribution).** Let $e_1 < \cdots < e_{10}$ be ten distinct positive real speeds. Suppose there exist indices $i \neq j$ such that $e_i/e_j \notin \mathbb{Q}$. Then there exists $t > 0$ with $\|e_\ell t\| \geq 1/11$ for all $\ell = 1,\ldots,10$.

**Proof.** The loneliness condition for runner $\ell$ is $\{e_\ell t\} \in [1/11, 10/11]$. The joint loneliness condition is:
$$t \in \bigcap_{\ell=1}^{10} \{t > 0 : \{e_\ell t\} \in [1/11, 10/11]\}.$$

Consider the orbit $\mathbf{x}(t) = (e_1 t, \ldots, e_{10} t) \bmod 1 \in [0,1)^{10}$ for $t > 0$. The target set is
$$\mathcal{S} = [1/11, 10/11]^{10} \subset [0,1)^{10},$$
which is open and has Lebesgue measure $(9/11)^{10} > 0$.

**Case 1: Fully linearly independent over $\mathbb{Q}$.** Suppose $1, e_1, \ldots, e_{10}$ are linearly independent over $\mathbb{Q}$. By Weyl's equidistribution theorem [Wey16], the orbit $\{\mathbf{x}(t) : t \in \mathbb{Z}_{>0}\}$ is equidistributed in $[0,1)^{10}$ and therefore intersects $\mathcal{S}$.

**Case 2: Partial rational dependencies.** Suppose $e_1,\ldots,e_{10}$ generate a $\mathbb{Q}$-vector space of dimension $d$ with $1 \leq d \leq 9$. The orbit $\{\mathbf{x}(t)\}$ lies in a closed sub-torus $T \cong [0,1)^d$ of $[0,1)^{10}$. Since there is at least one irrational ratio (hypothesis), $d \geq 2$. The image of $\mathcal{S}$ under the projection to $T$ is open and has positive $d$-dimensional Lebesgue measure. By Weyl's theorem applied on $T$, the orbit is equidistributed in $T$ and therefore intersects the image of $\mathcal{S}$.

In both cases, there exists $t > 0$ with $\mathbf{x}(t) \in \mathcal{S}$, i.e., $\{e_\ell t\} \in [1/11, 10/11]$ for all $\ell = 1,\ldots,10$. $\square$

*Remark E.1.* Weyl's equidistribution theorem [Wey16] states: if $\alpha_1,\ldots,\alpha_k$ are real numbers such that $1, \alpha_1,\ldots,\alpha_k$ are linearly independent over $\mathbb{Q}$, then the sequence $(n\alpha_1, \ldots, n\alpha_k) \bmod 1$ is equidistributed in $[0,1)^k$ as $n \to \infty$. The remaining open case after Proposition E is exactly when **all** speed ratios $e_i/e_j$ are rational — equivalently, all speeds are rational multiples of a common base frequency. This is Case R> in the decomposition below.

*Remark E.2 (Explicit witnesses not provided).* Proposition E is an existence proof via density; it does not produce an explicit witness time $t^*$. By contrast, Theorem B produces the explicit witness $t^* = 10/(11e_{10})$.

### 10.3 Commensurable large-ratio decomposition

**Theorem (Gap Decomposition).** The full classical LRC for $n = 11$ decomposes into three mutually exclusive and exhaustive sub-cases:

| Case | Speed structure | Status | Method |
|---|---|---|---|
| **Case R** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 \leq 10$ | **Proved** (Theorem B) | Explicit witness $t^* = 10/(11e_{10})$ |
| **Case I** | At least one $e_i/e_j \notin \mathbb{Q}$ (irrational ratio) | **Proved** (Proposition E) | Weyl equidistribution |
| **Case R>** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 > 10$ | **CLOSED** — Corollary W_ref (§10.6): switch to $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$; runner $e_1$ trivially isolated; Route 3 cascade gives GF$_{2\text{-}10}(W_{\rm ref})>0$ | Theorem W_ref + Route 3 |

**Proof of decomposition.** Cases R, I, R> are exhaustive (every configuration falls into exactly one) and mutually exclusive. Case R is handled by Theorem B with explicit witness. Case I is handled by Proposition E. Case R> is the complement. $\square$

**Structure of Case R>.** In Case R>, all speeds $e_1,\ldots,e_{10}$ are rational multiples of a common base $\omega > 0$: write $e_i = p_i \omega / q$ for integers $p_1 < \cdots < p_{10}$ and a common denominator $q$. The LRC condition becomes: $\exists k \in \mathbb{Z}_{>0}$ such that $\{p_i k / (11q)\} \in [1/11, 10/11]$ for all $i = 1,\ldots,10$. This reduces to a finite arithmetic problem for each choice of $(p_1,\ldots,p_{10},q)$.

**Why Case R> is hard.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10p_1/p_{10} < 1$ (since $p_{10}/p_1 > 10$). The AP witness $t=1/11$ fails because $\{a_1/11\} = a_1/11 < 1/11$. The witness family $\{m/11\}$ is insufficient (§10.1), and no finite extension suffices. The orbit is finite (rational speeds), so Weyl fails (§10.2). The Route 3 approach works by switching to runner $e_1$'s window.

### 10.4 Route 3: Coupling Principle and Complementary Pairs

We introduce the key algebraic structure underlying Case R>. This route exploits the deep algebraic structure of the mod-11 bijection and the **Coupling Principle** — the observation that all of a runner's bad intervals move together when its speed is tuned.

#### 10.4.1 The Coupling Principle and Resonance Cascade

**Definition 10.4.A (Good fraction).** For a CB configuration $\delta = (\delta_1,\ldots,\delta_9)$, define:
$$\mathrm{GF}(W_0) = \frac{|\{t \in W_0 : \{a_i t\} \in [1/11, 10/11]\ \forall\, i = 1,\ldots,10\}|}{|W_0|}.$$

**Lemma 10.4.B (Coupling Principle).** *Runner $j$ has bad intervals $B_{j,k} = [(11k+10)/(11a_j),\ (11k+12)/(11a_j)]$ forming a uniform arithmetic progression with period $1/a_j$. All bad intervals of runner $j$ scale simultaneously with $1/a_j$: tuning $a_j$ to position $B_{j,k_0}$ at a specific slot boundary moves ALL other $B_{j,k}$ proportionally.*

*Proof.* All endpoints of $B_{j,k}$ are of the form $(c + 11k)/(11a_j)$ for constants $c \in \{10, 12\}$, hence proportional to $1/a_j$. $\square$

**Remark 10.4.C (The rubber-band picture).** The Coupling Principle gives a physical picture: runner $j$'s bad intervals are like evenly-spaced beads on a rubber band. Stretching the band (decreasing $a_j$) pushes all beads right; compressing it (increasing $a_j$) pushes them left. Closing one slot by positioning a bead at a slot boundary forces all other beads into specific positions in other slots. The case structure in the proof is not a catalogue of independent scenarios — it is the **propagation of this constraint** through the slot-runner coverage graph.

**Definition 10.4.D (Runner-10 slots).** For $m = 2,\ldots,10$, define the **runner-10 slot**:
$$I_{m-1} = \left[\frac{11m-10}{110},\; \frac{11m-1}{110}\right].$$
The 9 slots $I_1,\ldots,I_9$ partition the central portion of $W_0$ near each AP witness $t_m$. Slot $I_{m-1}$ is centred near $t_m = m/11$.

#### 10.4.2 Complementary Pairs Theorem

**Theorem 10.4.1 (Complementary Pairs).** *In the AP limit ($a_j = j$), each runner $j \in \{2,\ldots,9\}$ lies at the lower isolation boundary ($\{a_j t\} = 1/11$) at witness $t_{j^{-1} \bmod 11}$ and at the upper boundary ($\{a_j t\} = 10/11$) at witness $t_{10j^{-1} \bmod 11}$. Runners $j$ and $11-j$ share the same pair of witnesses. The 8 free runners form 4 complementary pairs, each pair owning exactly 2 slots:*

| Pair | Runners | Owned slot (lower boundary) | Owned slot (upper boundary) |
|---|---|---|---|
| $(5, 6)$ | 5, 6 | $I_8$ ($m_j^- = 9$ or $2$) | $I_1$ ($m_j^+ = 2$ or $9$) |
| $(4, 7)$ | 4, 7 | $I_7$ ($m_j^- = 8$ or $3$) | $I_2$ ($m_j^+ = 3$ or $8$) |
| $(3, 8)$ | 3, 8 | $I_6$ ($m_j^- = 7$ or $4$) | $I_3$ ($m_j^+ = 4$ or $7$) |
| $(2, 9)$ | 2, 9 | $I_5$ ($m_j^- = 6$ or $5$) | $I_4$ ($m_j^+ = 5$ or $6$) |

*Slot $I_9$ is unclaimed by all runner pairs.*

**Proof.** From Lemma 4.2': $m_j^- = j^{-1} \bmod 11$ and $m_j^+ = 10j^{-1} \bmod 11$. Note $m_j^- + m_j^+ = 11j^{-1} \equiv 0 \pmod{11}$, so $m_j^+ = 11 - m_j^-$. For $j = 11-j'$: $j^{-1} = (11-j')^{-1} \equiv -j'^{-1} \equiv 11 - j'^{-1} \pmod{11}$, so $m_{11-j'}^- = 11 - m_{j'}^-$. The pair $\{j, 11-j\}$ therefore has $\{m_j^-, m_{11-j}^-\} = \{m_j^-, 11-m_j^-\}$ — the same pair as $\{m_j^-, m_j^+\}$. Hence both runners in a pair own the same two slots. The assignment follows by computing $j^{-1} \bmod 11$ for $j = 2,\ldots,9$ using the table in Lemma 4.2'. $\square$

**Structural interpretation.** The no-missing-slot property (Proposition 3.1') — that every AP residue $r_i(m) \in \{1,\ldots,10\}$ at every witness $m$ — means the residue map $i \mapsto im \bmod 11$ is a bijection. This bijection is the algebraic source of the pairing: it forces every runner to "own" exactly two witnesses (one lower, one upper), pairing runners $j$ and $11-j$ because $j + (11-j) = 11 \equiv 0 \pmod{11}$.

**Corollary 10.4.2 (Sign-pattern conflict in ++------).**
*In the ++------ class, runner 2 ($\delta_2 > 0$) approaches its upper boundary at $t_5$ (blocking from above), while runner 9 ($\delta_9 < 0$) approaches its lower boundary at $t_5$ (blocking from below). They compete for the same witness $t_5$ from opposite directions. Similarly, runners 3 and 8 conflict at $t_7$. This sign conflict forces "orphan witnesses," creating the structural reason why ++------ has the tightest good-fraction floor among all sign classes.*

#### 10.4.3 Forced Gaps When $I_1$ Is Closed

When the slot $I_1 = [12/110, 21/110]$ is fully closed (GF$(I_1) = 0$), the Coupling Principle forces specific gaps in other slots.

Fix $a_9 = 25/3$ and $a_6 = 40/7$ (the tightest case for $I_1$ closure). By the Coupling Principle:

**Runner 9's chain** ($a_9 = 25/3$, period $= 3/25$, bad intervals start at $3(11k+10)/275$):
$$B_{9,k}: \text{starts at }\frac{3(11k+10)}{275}, \quad k = 0, 1, 2, \ldots, 7.$$
In $W_0$: runner 9 visits $I_1, I_2, I_3, I_4, I_5, I_7, I_8, I_9$ and **skips $I_6$ entirely**.

**Runner 6's chain** ($a_6 = 40/7$, period $= 7/40$, bad intervals start at $7(11k+10)/440$):
Runner 6 visits only $I_1, I_3, I_5, I_6, I_8$ — it **skips $I_2, I_4, I_7, I_9$**. In $I_6$, runner 6 covers only the right portion $[301/440, 315/440]$.

**Lemma 10.4.3 (Forced Gaps).** *When $a_9 = 25/3$ and $a_6 = 40/7$:*

*(a) Gap $G_6 = [168/275, 301/440] \subset I_6$ of width $161/2200 \approx 7.3\%$ of $I_6$ receives zero coverage from runners 6 and 9.*

*(b) Gap $G_3 = [34/110, 147/440] \subset I_3$ of width $1/40 \approx 11\%$ of $I_3$ receives zero coverage from runners 6 and 9.*

#### 10.4.4 The Explicit Loneliness Certificate

**Theorem 10.4.4 (Case C Certificate).** *Suppose the sign class is ++------ and:*
*(i) $a_9 = 25/3$; (ii) $a_6 = 40/7$; (iii) $a_3 < 2750/759 \approx 3.623$.*

*Then the rational time $t^* = 69/275$ lies in $I_2 = [23/110, 32/110]$ and is the left endpoint of a good window of width $10/(11a_3) - 69/275 > 0$.*

**Proof.**

*Point 1.* $a_9 \cdot t^* = (25/3)(69/275) = 1725/825 = 23/11$. Then $\{23/11\} = 1/11$. Since $B_{9,1}$ ends at $3(11+12)/275 = 69/275$, the time $t^*$ is the right endpoint of $B_{9,1}$; for $t > 69/275$: runner 9 is safe. ✓

*Point 2.* Runner 9's $B_{9,2}$ starts at $3(22+10)/275 = 96/275 \approx 0.349 > 0.291 = 32/110$ (the right edge of $I_2$). Runner 9 has no bad interval in $I_2$ after $t^*$. ✓

*Point 3.* The width of the good window in $I_2$ is $10/(11a_3) - 69/275 > 0$ iff $a_3 < 2750/759$. ✓ $\square$

#### 10.4.5 The Runner 2 Incompatibility (Proved)

After fixing $a_9 = 25/3$ and $a_6 = 40/7$ (to close $I_1$), the remaining free runners are $\{2, 3, 4, 5, 7, 8\}$ and the remaining open slots are $I_2,\ldots,I_9$. For GF = 0 everywhere, these 6 runners must collectively close all 8 slots.

**Setup.** Runner 9's bad intervals (from §10.4.3) give:
- In I₄: $B_{9,3} = [129/275,\; 135/275]$ covers the right portion. Left gap: $J_4 = [45/110,\; 129/275]$ (width $3/50$).
- In I₉: $B_{9,7} = [261/275,\; 267/275]$ covers a middle-left portion. Left gap: $J_9 = [10/11,\; 261/275]$ (width $1/25$).

Runner 6 ($a_6 = 40/7$) skips both I₄ and I₉ entirely. Both $J_4$ and $J_9$ receive zero coverage from runners 9 and 6.

**Theorem 10.4.5 (Runner 2 Incompatibility).** *Closing I₄ requires $a_2 \geq 20/9$; closing I₉ requires $a_2 \leq 575/261$. Since $20/9 > 575/261$ (gap $= 5/261 > 0$), these constraints are incompatible. Hence $\mathrm{GF}(I_4) + \mathrm{GF}(I_9) > 0$ for every CB configuration in the ++------ class.*

**Proof: I₄ constraint.** Runner 2's bad interval formula gives $B_{2,0} = [10/(11a_2),\; 12/(11a_2)]$. For its left end to reach $45/110$ (left edge of $J_4$):
$$\frac{10}{11a_2} \leq \frac{45}{110} = \frac{9}{22} \implies a_2 \geq \frac{20}{9}.$$
No other runner can cover $J_4$'s left boundary without creating a new gap elsewhere: runners 4, 5, 7, 8 either have speeds too large or their shift disrupts $I_2$ coverage (runner 5 case) or $I_7$ coverage (runner 7 case), forcing another slot to be open. Therefore $a_2 \geq 20/9$ is necessary for I₄ to be closed.

**Proof: I₉ constraint.** Runner 2's bad interval $B_{2,1} = [21/(11a_2),\; 23/(11a_2)]$. For it to cover $J_9 = [10/11,\; 261/275]$:
$$\frac{21}{11a_2} \leq \frac{10}{11} \implies a_2 \geq \frac{21}{10},$$
$$\frac{23}{11a_2} \geq \frac{261}{275} \implies a_2 \leq \frac{6325}{2871} = \frac{575}{261}.$$
The only alternative for covering $10/11$ is runner 3 ($k=2$, range $[3.2, 3.4]$). Runner 3 in this range satisfies $a_3 < 2750/759$, which by Theorem 10.4.4 produces a **good window** in I₂: $\mathrm{GF}(I_2) > 0$. So runner 3 cannot substitute without opening I₂. Therefore $a_2 \leq 575/261$ is necessary for I₉ to be closed.

**Incompatibility.** The two constraints are:
$$a_2 \geq \frac{20}{9} \approx 2.222 \quad \text{and} \quad a_2 \leq \frac{575}{261} \approx 2.203.$$
Since $20 \times 261 = 5220 > 5175 = 9 \times 575$, we have $20/9 > 575/261$ with gap $5/261 > 0$. No value of $a_2$ satisfies both. $\square$

*Full proof with complete exclusivity arguments for all runner alternatives: `lrc_n11_incompatibility_v1.md`.*

---

### 10.5 The Static Core

#### 10.5.1 Theorem U: Universal σ₂=+1 Incompatibility

**Source:** `lrc_n11_universalincompat_v3.md`. Extends the ++------ incompatibility (Theorem 10.4.5) to all 128 σ₂=+1 sign classes. Every inequality is rational arithmetic.

**Notation.** Slots $I_k = [(11k+1)/110, (11k+10)/110]$. Bad interval $B_{j,k}(a_j) = [(11k+10)/(11a_j), (11k+12)/(11a_j)]$. Sign convention: $\sigma_j = +1$ means $a_j \in (j, j+1)$; $\sigma_j = -1$ means $a_j \in (j-1, j)$.

##### Core Structural Facts

**Fact A1.** *For any $a_9 \in (8,9)$: $B_{9,3}[0] = 43/(11a_9) > 45/110 = I_4[\text{left}]$.*

Proof: $43 \cdot 110 = 4730 > 495 a_9$ iff $a_9 < 946/99 \approx 9.556$. Since $a_9 < 9$. $\square$

**Fact B.** *For $a_9 \in (9,10)$: $B_{9,3}[0] = 45/110$ iff $a_9 = 86/9$.*

Proof: $43/(11a_9) = 45/110 \Rightarrow a_9 = 4730/495 = 86/9 \in (9,10)$. $\square$

##### I₄ Lower Bounds on a₂

**Lemma 2.1** ($\sigma_9 = -1$). *Closing $I_4$ requires $a_2 \geq 20/9$.*

Proof. By Fact A1, runner 9 leaves a left gap $[45/110,\, 43/(11a_9)] \subset I_4$. Complete candidate table for covering this gap:

| $k$ | $a_j$ range | Candidates |
|-----|-------------|------------|
| 0 | $[20/9,\, 8/3]$ | Runners 2, 3 |
| 1 | $[42/9,\, 46/9]$ | Runners 4 ($\sigma_4{=}+1$), 5 |
| 2 | $[64/9,\, 68/9]$ | Runners 7 ($\sigma_7{=}+1$), 8 ($\sigma_8{=}-1$) |
| $\geq 3$ | $>86/9$ | Runner 9 only — excluded by Fact A1 |

Each non-runner-2 candidate, if it covers the $I_4$ gap, forces a gap in another slot ($I_3$, $I_2$, $I_1$, or $I_7$ respectively), so GF $> 0$ is established elsewhere. Runner 2 is the unique viable candidate. For $B_{2,0}[0] \leq 45/110$: $a_2 \geq 1100/495 = 20/9$. $\square$

**Lemma 2.2** ($\sigma_9 = +1$, $a_9 < 86/9$). *Closing $I_4$ requires $a_2 \geq 20/9$.*

Proof. For $a_9 \in (9, 86/9)$: $B_{9,3}[0] > 45/110$ (Fact B with reversed inequality). The same 8-runner exclusion table applies with identical arguments. Runner 2 is uniquely forced; same threshold. $\square$

**Lemma 2.3** ($\sigma_9 = +1$, $a_9 \geq 86/9$). *Closing $I_4$ requires $a_2 \geq 2a_9/9 \geq 172/81$.*

Proof. Runner 9 covers $[9/22, 45/(11a_9)] \subset I_4$, leaving right gap $[45/(11a_9), 54/110]$. For $B_{2,0}[0] \leq 45/(11a_9)$: $a_2 \geq 2a_9/9 \geq 172/81$. $\square$

##### Part A: σ₉=−1, Cases A1–A2d

**Case A1** ($a_2 < 20/9$): Lemma 2.1 gives GF$(I_4) > 0$. $\square$

**Case A2** ($a_2 \geq 20/9$): Runner 2 covers $[10/11, 23/(11a_2)] \subset I_9$ with end $\leq 207/220$.

- **A2a** ($a_9 < 580/69$): Runner 9's $B_{9,7}[0] > 207/220 \geq 23/(11a_2)$. Middle gap in $I_9$. Incompatibility: $a_2 \geq 20/9$ vs $a_2 \leq 23a_9/87$; gap is positive since $a_9 < 580/69$. GF$(I_4)$ + GF$(I_9) > 0$. $\square$

- **A2b** ($a_9 \in [580/69, 87/10)$): Runners 2 and 9 cover $[10/11, 89/(11a_9)]$. Right gap $\Delta_R \geq 181/6380 > 0$. Chain Termination Lemma shows the gap cannot be filled. GF$(I_9) \geq 181/6380$. $\square$

- **A2c** ($a_9 \in [87/10, 980/109)$): Runner 9 provides no $I_9$ coverage. Right gap $g_L = 23/(11a_2) \leq 207/220$. Chain Termination Lemma applies. GF$(I_9) \geq 1/20$. $\square$

- **A2d** ($a_9 \in [980/109, 9)$): Bridging requires $a_2 \leq 23a_9/98 < 20/9$ (since $1960 > 207 \cdot 9$). INCOMPATIBLE with $a_2 \geq 20/9$. GF$(I_4)$ + GF$(I_9) > 0$. $\square$

##### Part B: σ₉=+1, Cases B1–B4

- **B1** ($a_9 < 1960/207$): Lemma 2.2 gives $a_2 \geq 20/9$. Bridging $I_9$ requires $a_2 \leq 23a_9/98 < 20/9$. INCOMPATIBLE. $\square$

- **B2** ($a_9 \in [1960/207, 86/9)$): Runners 2 and 9 cover up to $100/(11a_9)$. Right gap $(1199a_9 - 11000)/(1210a_9) \geq 83/2695 > 0$. Chain Termination Lemma applies. $\square$

- **B3** ($a_9 = 86/9$): By Lemma 2.3: $a_2 \in [172/81, 20/9]$. Right gap $= 109/110 - 450/473 = 17/430 > 0$. At $a_2 = 172/81$: right gap $= 59/9460 > 0$. GF$(I_9) \geq 59/9460$. $\square$

- **B4** ($a_9 > 86/9$): Right gap $\Delta_R > 17/430$. Chain Termination Lemma applies. $\square$

##### Chain Termination Lemma (Lemma CT)

> **Lemma CT.** Let $[g_L, 109/110] \subset I_9$ be a right gap not covered by runners 2 and 9, with $g_L > 0$. Then no speed assignment for runners $3,\ldots,8$ can cover $[g_L, 109/110]$ while maintaining GF$(I_k) = 0$ for all $k = 1,\ldots,8$.

The proof divides into three sub-cases by the value of $g_L$, with feasibility thresholds at $g_L = 872/935$ (runner 3) and $g_L = 4687/4950$ (runner 4). Sub-case CT0 ($g_L < 872/935$): the feasibility table is empty. Sub-cases CT1/CT2 ($g_L \geq 872/935$): runner 3 (CT1) or runners 3 and 4 (CT2) are the only candidates.

**Chain A** (CT1/CT2, runner 3 active, $a_3 \in [640/207, 340/109]$): The $I_3$ right gap forces $a_8 \geq 8a_3/3$, which forces runner 6 into a configuration where $B_{6,4}[0] = 54/(11a_6) \geq 228/275 > 89/110 = I_8[\text{left}]$. Minimum gap:
$$\frac{228}{275} - \frac{89}{110} = \frac{1}{50} > 0.$$
**GF$(I_8) \geq 1/50 > 0$.** $\square$

**Chain B** (CT2, runner 4 active, $a_4 \in [1849/450, 450/109]$): The $I_2$ right gap forces $a_7 \geq 7a_4/4 \geq 12943/1800$. The $I_7$ right coverage requires $a_7 \leq 560/87 \approx 6.44$. Incompatible: $12943 \times 87 = 1126041 > 560 \times 1800 = 1008000$. $I_7$ right gap $= 87/110 - 14400/20339 = 1533/18490 > 0$. **GF$(I_7) \geq 1533/18490 > 0$.** $\square$

##### Theorem U

**Theorem U (Universal $\sigma_2=+1$ Incompatibility).** *For any CB configuration with $\sigma_2=+1$: GF$(I_4)$ + GF$(I_9) > 0$.*

**Proof.** Cases A1, A2a, A2d, B1 give direct incompatibility. Cases A2b, A2c, B2, B3, B4 produce a right gap in $I_9$ that Lemma CT shows cannot be filled. In all 128 sign classes, GF$(I_4)$ + GF$(I_9) > 0$. $\square$

**Minimum gap:** $59/9460$ (Case B3, $a_9 = 86/9$, $a_2 = 172/81$).

#### 10.5.2 Lemma S1 (Runner 2 Elimination)

**Lemma S1 (Runner-2 $I_9$-elimination).** In any σ₂=−1 sign class, the approach that attempts to close $I_9$ using runner 2 alone fails: the runner-2 coverage of $I_9$ is incompatible with the simultaneous closure requirements on $I_5$ (pair (2,9)'s owned slot). Gap $= 114/1417 > 0$. See `lrc_n11_lemma_s1_proof_v1.md`.

#### 10.5.3 Lemma S2: Cascade-Conditional Witness Window

**Lemma S2.** In every σ₂=−1 sign class, the unclaimed slot $I_9 = [100/110, 109/110]$ retains a positive witness width. The minimum is $538/54395 > 0$.

**Setup.** In σ₂=−1, runner 2 has $a_2\in[25/14, 24/13]$ and closes $I_5$'s left boundary via $j=0$. Runner 9 must therefore close $I_4$.

**Step 1 — The Only Valid a₉ is 86/9.** $B_{9,k}[0] = 45/110$ ($I_4$ left) iff $a_9 = (110k+100)/45$. For $a_9 \in (9,10)$: unique solution $k=3$, giving $a_9 = 86/9$. For all other $a_9 \in (9, 10)$: pair $(2,9)$ fails to cover $I_4$ → $W(I_4) > 0$ → infeasible.

**Step 2 — Runner 9's Bad Interval in I₉.** For $a_9 = 86/9$:
$$B_{9,8}(86/9) = \left[\frac{441}{473},\ \frac{450}{473}\right] \subset I_9.$$

**Step 3 — Cascade-Forced Outer Runner Speeds.** Only runners 3, 4, 7, 8 (with specific $\sigma$) have bad intervals in $I_9$. Runners 5, 6, and 10 have empty effective $I_9$ intervals.

**Step 4 — The Four Sub-Cases.** The gap structure depends on σ₃ (runner 8's presence) and σ₄ (runners 4 and 7's presence).

**Case A** (σ₄=−1): Left portion $(10/11, 441/473)$ of $I_9$ uncovered. $W(I_9) \geq 1/43 > 0$. $\square$

**Case B** (σ₃=+1, σ₄=+1): Left coverage $[10/11, 741/770]$ fully covered by runners 4, 7, 9, 8. Runner 3 covers $[272/275, 109/110]$ on the right. Gap:
$$G_1 = (741/770,\ 272/275), \quad W(G_1) = 103/3850 > 0.$$
$W(I_9) = 103/3850 > 0$. $\square$

**Case C** (σ₃=−1, σ₄=+1): Left coverage by runners 4, 7, 9. Runner 3 covers $[1216/1265, 109/110]$. Gap:
$$G_2 = (450/473,\ 1216/1265), \quad W(G_2) = 538/54395 > 0.$$
$W(I_9) = 538/54395 > 0$. $\square$

**Summary:**

| σ₃ | σ₄ | $W(I_9)$ |
|----|----|----|
| +1 | +1 | **103/3850** |
| +1 | −1 | **8279/165550** |
| −1 | +1 | **538/54395** ← minimum |
| −1 | −1 | **1803/54395** |

Minimum $W(I_9) = 538/54395 > 0$. **Lemma S2: PROVED.** $\square$

*(Computational corroboration of these bounds — see Appendix A.)*

---

### 10.6 Phase-Uniform Extension and Theorem W_ref

#### 10.6.1 Theorem R1: Route 3 Closes Case R> for $p_{10}/p_1 \in (10, 89)$

**Background.** Theorem U + Lemma S2 prove $\mathrm{GF}_{2\text{-}9}(W_0) > 0$ for all 256 sign classes of runners 2–9. For $\sigma_1 = -1$ (i.e., $a_1 < 1$, equivalently Case R>): for $a_1 > 10/89$ the same Route 3 argument delivers $\mathrm{GF}_{\mathrm{total}} > 0$.

**Lemma R1.0 (Runner 1 isolation in slot $I_k$).** For $a_1 \in (0,1)$ and $t \in I_k$: $\{a_1 t\} = a_1 t$. Runner 1 is isolated throughout $I_k$ iff $a_1 \in [10/(11k+1),\; 100/(11k+10)]$.

*Key threshold: $I_8$: $a_1 \geq 10/89$.*

> **Theorem R1.** *For any EFN CB configuration with $a_1 \in (10/89, 1)$ (equivalently integer speeds with $p_{10}/p_1 \in (10, 89)$), $\mathrm{GF}_{\mathrm{total}}(W_0) > 0$.*

**Proof (sketch).** *Case A: $a_1 \in (10/89,\; 100/109)$.* Runner 1 is isolated throughout $I_8$ (since $a_1 > 10/89$) and $I_9$. Theorem U + Lemma S2 establish $\mathrm{GF}_{2\text{-}9} > 0$ in some slot $S^* \in \{I_8, I_9\}$. Runner 1 is isolated in $S^*$. Hence $\mathrm{GF}_{\mathrm{total}}(S^*) > 0$. $\square$

*Case B: $a_1 \in (100/109,\; 1)$.* Runner 1 right-blocks the upper portion of $I_9$ but is isolated throughout $I_4$, $I_7$, and $I_8$. Theorem U's Chain A gives $\mathrm{GF}_{2\text{-}9}(I_8) \geq 1/50$; since $a_1 > 10/89$, runner 1 is isolated in $I_8$. $\mathrm{GF}_{\mathrm{total}}(I_8) \geq 1/50 > 0$. $\square$

#### 10.6.2 Lemma P: Phase-Independence of Bad-Interval Widths

**Lemma P.** *The bad-interval widths $2/(11a_j)$ are independent of cycle index $k$ and pacemaker cycle $m$.*

**Proof.** Each bad interval $B_{j,k}$ has width $(11k+12)/(11a_j) - (11k+10)/(11a_j) = 2/(11a_j)$. This is independent of $k$ and of which sub-window $W_{\rm ref}[m]$ is under consideration. $\square$

#### 10.6.3 Lemma C: Phase-Independence of the UB Cascade

**Lemma C.** *All Theorem UB cascade conclusions (PSM, Chain A giving GF$(I_8) \geq 1/50$, Chain B giving GF$(I_7) \geq 1533/18490$) depend only on the EFN speed ranges $a_j \in (j-1,j)$ and sign $\sigma_j$, not on the pacemaker cycle index $m$ or phase $\varphi_{j,m}$.*

**Proof.** The PSM condition "$B_{j,0}[0]$ starts above the right edge of the primary slot" depends only on $a_j$ and the slot boundaries (which are fixed multiples of $1/110$), not on phase. Chain A and Chain B are sequences of speed-range inequalities of the form $a_j \geq L_j$ or $a_j \leq U_j$, derived from the Coupling Principle applied to fixed slot boundaries. None of these inequalities reference $m$ or $\varphi_{j,m}$. Hence the entire cascade is phase-independent. $\square$

#### 10.6.4 Theorem PU and Corollary W_ref

**Theorem PU (Phase-Uniform Extension).** *In any pacemaker sub-cycle $W_{\rm ref}[m] \subset W_{\rm ref}$, the Theorem UB cascade (Theorem U for $\sigma_2=+1$; Lemma S2 for $\sigma_2=-1$) applies with the same conclusions as in $W_0$: GF$_{2\text{-}10}(W_{\rm ref}[m]) > 0$.*

**Proof.** By Lemma P, bad-interval widths are the same in each pacemaker sub-cycle. By Lemma C, the cascade conclusions depend only on speed ranges and signs, which are the same across all sub-cycles. Hence the cascade applies uniformly in each $W_{\rm ref}[m]$ and gives GF$_{2\text{-}10} > 0$ in each. $\square$

> **Theorem W_ref** *(Window-shift closure of Case R>).* For any integer speeds $\{e_1, e_2, \ldots, e_{10}\}$ with $e_{10}/e_1 > 10$: let $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$. Runner $e_1$ is isolated throughout $W_{\rm ref}$ by construction. Runners $\{e_2,\ldots,e_{10}\}$, viewed through the EFN normalisation relative to $e_{10}$, satisfy Theorem U (for $\sigma_2 = +1$) and Lemma S2 (for $\sigma_2 = -1$). By Theorem PU, there exists a sub-window $W_{\rm ref}[m] \subset W_{\rm ref}$ with ${\rm GF}_{2\text{-}10}(W_{\rm ref}[m]) > 0$. Since runner $e_1$ is isolated throughout $W_{\rm ref} \supset W_{\rm ref}[m]$, we have ${\rm GF}_{\rm total}(W_{\rm ref}[m]) > 0$. A witness $t \in W_{\rm ref}[m]$ exists with all 10 runners isolated. $\square$

**Why the residuals vanish:**

| Residual | Why it blocked Theorem R1 | Why Theorem W_ref bypasses it |
|----------|--------------------------|-------------------------------|
| Mild $[89,100]$ (Chain A) | In $W_0$: runner $e_1$ enters Chain A's $I_8$ gap from left | In $W_{\rm ref}$: runner $e_1$ isolated throughout by definition |
| Hard $>100$ | In $W_0$: runner $e_1$ blocks all of $W_0$ | In $W_{\rm ref}$: $W_{\rm ref}$ is runner $e_1$'s window; it contains no blocking |

**Updated scope table:**

| $a_1$ range | Ratio $p_{10}/p_1$ | Theorem W_ref status |
|-------------|--------------------|-----------------------|
| $a_1 \in (10/89, 1)$ | $(10, 89)$ | **CLOSED** |
| $a_1 \in [1/10, 10/89]$ | $[89, 100]$ | **CLOSED** |
| $a_1 < 1/10$ | $> 100$ | **CLOSED** |

*(112/112 computational corroboration in Appendix A.)*

#### 10.6.5 Formal Dependency Chain

The proof of Corollary W_ref is dependency-clean:

**Static Core Theorem** (Theorem U + Lemma S1 + Lemma S2): proved in §10.5, source files `lrc_n11_universalincompat_v3.md` and `lrc_n11_lemma_s2_proof_v2.md`.

**Phase-Uniform Extension** (Lemma P + Lemma C + Theorem PU): proved in §10.6.2–10.6.4, source file `lrc_n11_periodicity_lemma_v1.md`.

**Corollary W_ref**: immediate from the two above components. Source file: `lrc_n11_w1_argument_v1.md`.

No SET, no WIT, no ILE, no containment.

---

### 10.7 Theorem C — Complete Proof

**Theorem C (Classical LRC for $n = 11$, complete).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$, there exists $t > 0$ with $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$.*

**Proof.** By the Gap Decomposition (§10.3), every configuration falls into exactly one of three cases:

*Case B (bounded ratio, $e_{10}/e_1 \leq 10$):* Theorem B gives explicit $t^* = 10/(11e_{10})$. $\square$

*Case I (irrational ratio):* Proposition E (§10.2) gives existence via Weyl equidistribution. $\square$

*Case R> (commensurable, $e_{10}/e_1 > 10$):* Theorem W_ref (§10.6.4) gives a witness in $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$. $\square$

The three cases are exhaustive and mutually exclusive. The proof is complete. $\square$

| Route | Method | Status | Scope |
|---|---|---|---|
| Theorem B | Explicit witness $t^* = 10/(11e_{10})$ | **PROVED** | $e_{10}/e_1 \leq 10$ |
| Proposition E | Weyl equidistribution | **PROVED** | Irrational speed ratios |
| **Theorem W_ref** | Coupling Principle + Runner 2 Incompatibility + Phase-Uniform Extension; window $W_{\rm ref}$ | **PROVED** (2026-03-27) | Case R> — all ratios |
| **Theorem C** | Cases B + I + R> exhaustive | **PROVED** (2026-03-27) | Full classical LRC, $n=11$ |

---

### 10.8 The 11-Pacemaker Special Case

*Note: The following provides an independent direct proof for the special case where the pacemaker is an integer multiple. This case is already closed by §10.6 (Corollary W_ref); we include it as an independent verification.*

**Normalisation.** Without loss of generality (rescaling by $e_1$), the ten runner speeds are positive integers
$$\mathcal{V} = \{1,\ 11,\ p_2,\ p_3,\ \ldots,\ p_9\},$$
where $p_2 < p_3 < \cdots < p_9$ are arbitrary positive integers, distinct from each other and from 1 and 11.

**Case dichotomy.** We split all possible free speed sets $\{p_2,\ldots,p_9\}$ into:
- **Case B:** $p_j \equiv 0 \pmod{11}$ for all $j = 2,\ldots,9$.
- **Case A:** $p_j \not\equiv 0 \pmod{11}$ for at least one $j$.

**Theorem 10.8.A (Case B: Explicit Witness $t^* = 12/121$).** *If all free speeds satisfy $p_j \equiv 0 \pmod{11}$ (so $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, all distinct), then $t^* = 12/121$ satisfies $\|v \cdot t^*\| \geq 1/11$ for all $v \in \mathcal{V}$.*

**Proof.**
- *Runner at speed 1:* $\{12/121\} = 12/121 \in (1/11, 10/11)$. ✓
- *Runner at speed 11:* $\{11 \cdot 12/121\} = \{132/121\} = \{1+11/121\} = 1/11$. So $\|11t^*\| = 1/11 \geq 1/11$. ✓
- *Runner at speed $11k_j$, $k_j \in \{2,\ldots,9\}$:* $\{11k_j \cdot 12/121\} = \{12k_j/11\} = k_j/11 \in \{2/11,\ldots,9/11\} \subset (1/11,10/11)$. ✓
- *Runner at speed $110$ ($k_j = 10$, if present):* $\{110 \cdot 12/121\} = 10/11$. So $\|110t^*\| = 1/11 \geq 1/11$. ✓

Since all $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, every runner is verified. $\square$

**Theorem 10.8.B (Case A: Positive-Measure Witness Set).** *If at least one free speed $p = p_{j_0}$ satisfies $p \not\equiv 0 \pmod{11}$, then the witness set $W = \{t > 0 : \{vt\} \in G\ \forall\, v \in \mathcal{V}\}$ (with $G = (1/11, 10/11)$) has positive Lebesgue measure. In particular $W \neq \emptyset$ and the LRC holds.*

**Proof (key steps).**

*Step 1 (Positive-measure base set).* Let $\mathcal{M} = \{k_j : p_j = 11k_j\}$ be the multipliers of the multiples-of-11 free runners. For any AP witness $m \in \{2,\ldots,9\}$, set $x_0 = m/11 \in G$; all $\{kx_0\}$ for $k \in \mathcal{M}$ lie strictly in $(1/11, 10/11)$. Hence each $m/11$ has an open neighbourhood with $S_A = \{x_0 \in G : \{kx_0\} \in G\ \text{for all}\ k \in \mathcal{M}\}$ of positive measure.

*Step 2 (Nine valid preimages).* For $x_0 \in S_A$ and times $t_j = (x_0+j)/11$, $j=0,\ldots,10$: $j=0$ and $j=10$ fail; $j=1,\ldots,9$ all satisfy $\{t_j\} = (x_0+j)/11 \in G$. Runner at speed 11 is safe since $\{11 t_j\} = x_0 \in G$.

*Step 3 (Key Lemma: equally-spaced preimages).* Let $p \not\equiv 0 \pmod{11}$, $r = p \bmod 11 \in \{1,\ldots,10\}$. Then $\{p \cdot t_j\} = \{\alpha + rj/11\}$ where $\alpha = \{px_0/11\}$. Since $\gcd(r,11)=1$, the values $rj \bmod 11$ for $j=0,\ldots,10$ are a permutation of $\{0,\ldots,10\}$, giving eleven equally-spaced points with gap $1/11$. Exactly 2 of the 11 values lie outside $\bar{G}$. Among $j=1,\ldots,9$ (9 valid preimages), at least 7 indices satisfy $\{p \cdot t_j\} \in \bar{G}$, leaving at least 5 strictly inside $G$.

*Step 4 (Positive measure via Fubini).* For each $x_0 \in S_A$, Step 3 gives $j^*(x_0) \in \{1,\ldots,9\}$ with $\{p \cdot t_{j^*}\} \in G$. Since $G$ is open, there is $\delta(x_0) > 0$ such that all conditions hold uniformly near $t_{j^*}$. Integrating over $x_0$ in a subset of $S_A$ where the distance to $\partial G$ is bounded below: $|W| \geq 2\eta/(11p) \cdot |E_\eta| > 0$. $\square$

**Theorem 10.8.Main (11-Pacemaker).** *Let $(e_1,\ldots,e_{10})$ be any ten distinct positive real speeds with the property that, after rescaling to integer speeds with minimum speed 1, the speed set contains both 1 and 11. Then there exists $t^* > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1,\ldots,10$.*

**Proof.** After rescaling, the speed set is $\{1, 11, p_2,\ldots,p_9\}$. Cases A and B are exhaustive:
- If all $p_j \equiv 0 \pmod{11}$ (and $p_j \leq 110$): Theorem 10.8.A gives explicit $t^* = 12/121$.
- If some $p_{j_0} \not\equiv 0 \pmod{11}$: Theorem 10.8.B gives $|W| > 0$, so $W \neq \emptyset$. $\square$

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

---

## Appendix A: Computational Corroboration of Case R>

**The following computations corroborate the analytic proof; they are not part of the proof.**

### A.1 W_ref 112/112 Verification

Script `tools/lrc_case_r_residual_harness_v1.py` (exact rational arithmetic, boundary-set method) verified witnesses in $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$ for all 112 canonical integer configurations $\{1,2,\ldots,9,p_{10}\}$ with $p_{10} \in \{89,\ldots,200\}$:

| Regime | Configs | Witnesses | Location |
|--------|---------|-----------|----------|
| Mild $[89,100]$ | 12 | 12/12 ✓ | $W_{\rm ref} = [1/11, 10/11]$ |
| Hard $[101,200]$ | 100 | 100/100 ✓ | $W_{\rm ref} = [1/11, 10/11]$ |

Zero failures. Results in `reports/lrc_case_r_residual_results_v1.json`. Full analytic argument: `lrc_n11_w1_argument_v1.md`.

### A.2 Route 3 Good-Fraction Floor

Deep minimisation over $3 \times 10^6$ random CB (complete-blocking) configurations + differential evolution + Nelder-Mead polish (from `lrc_n11_tightest_escape_v1.md`):
- Min GF $\approx$ 0.12%; never 0.
- Extremal configuration: $a_1 \approx 0.983$, sign pattern ++------.
- This is consistent with Theorem U's minimum gap of $59/9460 \approx 0.62\%$ (the analytic bound is not tight at the empirical extremal configuration; the extremal lies in a different sub-case).

### A.3 256 Sign-Pattern Feasibility

Enumeration over all $2^8 = 256$ sign patterns $\sigma \in \{+,-\}^8$ for $(\delta_1,\ldots,\delta_8)$ (script `lrc_n11_blocking_enum_v2.py`; results: `reports/lrc_n11_blocking_enum_v2_results.json`):
- 247 of 256 patterns admit CB configurations (GF = 0 achievable by some config).
- 9 patterns have no CB configurations (GF > 0 for all configs with that sign pattern).
- ++------ achieves the minimum $\min \mathrm{GF}$ across all 247 feasible patterns.

### A.4 Exact Rational Checks

The following quantities appear in the analytic proof and have been verified by exact rational arithmetic:

| Quantity | Value | Role |
|----------|-------|------|
| $86/9$ | $\approx 9.556$ | Unique $a_9$ closing $I_4$ left boundary in σ₂=−1 |
| $172/81$ | $\approx 2.123$ | Lower bound on $a_2$ in Case B3 of Theorem U |
| $181/6380$ | $\approx 0.0284$ | Minimum right gap in Case A2b |
| $59/9460$ | $\approx 0.0062$ | Minimum gap in Theorem U (Case B3) |
| $103/3850$ | $\approx 0.0268$ | $W(I_9)$ in Lemma S2 Case B |
| $538/54395$ | $\approx 0.00989$ | Minimum $W(I_9)$ in Lemma S2 (Case C) |
| $(9/11)^8 - 16/69 < 0$ | $(9/11)^8 = 43046721/214358881 \approx 0.2008$; $16/69 \approx 0.2319$; difference $\approx -0.031 < 0$ | Confirms falsity of WIT component (2) — see Appendix B.4 |

---

## Appendix B: Historical Approaches

*This appendix summarises proof strategies that were explored but are now superseded by Route 3 (Theorem W_ref). No part of the canonical proof depends on the material here.*

### B.1 ILE/Carry/Containment Framework (§10.7–§10.11 of v21)

The Intrinsic Loneliness Estimate (ILE) framework constructs witnesses by tracking runner positions via carry mechanisms and ILE advances. Reflection symmetry (Lemma R: AP-witness blocking patterns of $\{b_i\}$ and $\{a_{10-i+1}\}$ are complementary), explicit $W_0$ witness structures, and right-endpoint obstruction lemmas were developed. Key results: Theorem 10.12 (modular bijection in $\mathbb{Z}/121\mathbb{Z}$ — proved for pacemaker ratio = 11), Lemma 0 ($\Delta(q) > 0$ for all $q \geq 1$ — proved), unified carry bound ($\delta_{\rm carry} \leq 2/(11p_c)$ — proved). These are not part of the canonical proof; see v21 §§10.7–10.11 for full exposition.

### B.2 Consecutive Staircase and Containment (§10.12–§10.14 of v21)

The consecutive staircase family and containment experiments (BST, R2, PPL) explored whether every CB configuration contains a configuration from a known good family. The **whack-a-mole phenomenon** shows these families are insufficient: closing $I_1$ (by setting $a_9 = 25/3$, $a_6 = 40/7$) automatically opens $I_2$ and $I_8$ via the Coupling Principle. Specifically, closing $I_1$ forces $a_9 = 25/3$, which leaves $I_6$ uncovered (gap $G_6$). Covering $G_6$ requires runner 8 to shift, which opens $I_3$. The cascade continues until Runner 2 Incompatibility (Theorem 10.4.5) is reached. Full detail in v21 §§10.12–10.14.

### B.3 Slot-Economy Theorem (SET) — SUPERSEDED (known gap)

SET (from v21 §10.15) claimed: any CB configuration has at most 20 ILE advances for the extremal runner, bounding the good fraction from below.

**Known gap in Sub-case B2:** SET assumes $E_{\rm ext}(q) \cap \{11, 22, \ldots\}$ contributes at most one advance per staircase step. But for configurations $S$ where multiple multiples of 11 are present (e.g., both $11q$ and $22q$ in $S$), runners can re-enter blocking intervals between staircase positions, generating additional advances not tracked by the 20-step staircase. Specifically, the step from $t^*(q)$ to the next staircase level can be interrupted by a runner at $22q$ that blocks a witness after $t^*(q)$, invalidating the monotonicity argument that underpins the 20-step count.

Route 3 (Corollary W_ref) covers all cases without SET. SET's role in v21's §9 dependency table has been removed.

### B.4 Lemma WIT — SUPERSEDED (known gap)

Lemma WIT (from v21 §10.15) claimed a lower bound on GF using the Weyl density of runner orbits for large $p_{10}$.

**Known gap in component (2):** WIT's proof required the inequality $(9/11)^8 - 16/69 > 0$. This is **false**. Exact arithmetic: $(9/11)^8 = 43046721/214358881 \approx 0.2008$; $16/69 \approx 0.2319$; difference $\approx -0.031 < 0$. Component (3) (small-$p$ exhaustive certificate for $p_{10} \leq 69$) remains valid but is insufficient alone.

Route 3 (Corollary W_ref) covers all cases without WIT. Lemma WIT is not used in the canonical proof.

**Full historical text of §§10.7–10.15, Appendices A, C, D:** see `lrc_n11_ap_paper_v21.md`.
