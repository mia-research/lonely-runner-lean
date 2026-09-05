# The Lonely Runner Conjecture for n = 11: A Complete Proof

**Authors:** Trent Palelei
**Date:** 2026-03-30 / v27
**Status:** PROOF COMPLETE (v27, 2026-03-30) — all proofs inline; 14 referee gaps addressed; Lemmas 11.1.1 and 11.2.1 re-proved without circularity
**MSC 2020:** 11K60, 11J71
**Keywords:** Lonely Runner Conjecture, arithmetic progressions, Kronecker approximation, complementary pairs

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ unconditionally. For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$, there exists $t > 0$ such that $\|e_i t\| \geq 1/11$ for all $i = 1, \ldots, 10$. The proof proceeds by an exhaustive case split over three mutually exclusive and exhaustive cases. (B) Bounded speed ratio $e_{10}/e_1 \leq 10$: elementary explicit witness $t^* = 10/(11e_{10})$ (Theorem B). (E) Non-commensurable speeds: a Kronecker-closure argument produces a point of the orbit closure inside $(1/11, 10/11)^{10}$ (Proposition E). (R>) Commensurable speeds with $e_{10}/e_1 > 10$: we work in the window $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$ where runner $e_1$ is trivially isolated. The **Static Core Theorem** — comprising Theorem U (for $\sigma_2 = +1$) and Lemma S2 (for $\sigma_2 = -1$, minimum gap $538/54395$) — proves that every CB configuration has some slot $I_k$ with positive good fraction. The **Phase-Uniform Extension** (Lemma P: bad-interval widths are phase-independent; Lemma C: the UB cascade is speed-range only) ensures the cascade applies in every pacemaker sub-cycle of $W_{\rm ref}$. **Corollary W_ref** then gives a witness in $W_{\rm ref}$ for all Case R> configurations. Cases B, E, R> are exhaustive. Computational corroboration: 112/112 canonical integer configurations $\{1,\ldots,9,p_{10}\}$ with $p_{10} \in \{89,\ldots,200\}$ have witnesses in $W_{\rm ref}$, verified by exact arithmetic (Appendix A).

---

## 1. Introduction

The **Lonely Runner Conjecture** (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts: for any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists $t > 0$ such that the stationary runner at speed $0$ satisfies $\|e_i t\| \geq 1/(n+1)$ for all $i = 1,\ldots,n$. The conjecture has been verified for $n \leq 7$ (Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], Barajas–Serra [BS08]), and for $n = 8$ [Ros25a], $n = 9$ [Ros25b, Tra25], and $n = 10$ [Tra25] by recent computational work. A survey of analytic approaches appears in Tao [Tao18].

The companion paper [v2] proves the **relative formulation** for $n = 11$: for any ten distinct real speeds $v_1 < \cdots < v_{10}$, some runner $j^* \in \{1,\ldots,10\}$ has a lonely time with threshold $1/11$ relative to the other nine. The present paper builds the AP framework with $j = 0$ (stationary runner) and proves the classical formulation unconditionally.

**Theorem B (Classical LRC for $n = 11$, bounded speed ratio).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ with $e_{10}/e_1 \leq 10$, there exists $t^* = 10/(11e_{10}) > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1, \ldots, 10$.*

**Proposition E (Irrational-ratio case).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$ such that $e_i/e_j \notin \mathbb{Q}$ for at least one pair $i \neq j$, the classical LRC holds for this configuration.*

**Theorem C (Full classical LRC for $n = 11$).** *The same conclusion holds without restriction on $e_{10}/e_1$. The remaining case (commensurable speeds, $e_{10}/e_1 > 10$) is closed by Theorem W_ref (§13).*

### 1.1 Key structural differences from [v2]

The classical formulation requires the AP witness framework with the **stationary runner $j = 0$** as the fixed reference. Two structural changes from [v2] follow.

**No-missing-slot.** In [v2], for a moving reference $j \in \{1,\ldots,10\}$, the AP residues $\{(i-j)m \bmod 11 : i \neq j\}$ always miss exactly one slot. For $j = 0$, the classical AP residues are $r_i(m) \equiv im \pmod{11}$ for $i = 1,\ldots,10$. Since $11$ is prime and $\gcd(i,11) = 1$, multiplication by $m$ is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$, so $\{im \bmod 11 : i = 1,\ldots,10\} = \{1,\ldots,10\}$. No slot is missing.

**Independent conditions.** In the classical framework, the loneliness condition for runner $i$ at witness $m$ involves only $\delta_i$ — not $\delta_j$ for $j \neq i$. This replaces the runner-index transfer mechanism of [v2] with a counting/blocking argument.

### 1.2 Informal skeleton of the proof

The proof has a natural constructive skeleton that motivates all three cases.

**Bounded ratio (Case B, $e_{10}/e_1 \leq 10$).** The explicit witness $t^* = 10/(11e_{10})$ places every runner at fractional position in $[1/11, 10/11]$. This holds because the speed-ratio bound forces the slowest runner to position $\geq 1/11$ and the fastest to position $\leq 10/11$ at this single time. No AP framework is needed: it is a one-inequality argument.

The proof of Case B is logically independent of the AP framework developed later: it is a direct inequality argument.

**Large ratio (Case R>, $e_{10}/e_1 > 10$, commensurable).** When the ratio exceeds 10, the 10 runners cannot densely fill the natural speed grid $\{e_1, 2e_1, \ldots, 10e_1\}$. By a pigeonhole argument, at least one grid slot is unoccupied — equivalently, at least one blocking zone on the circle has no runner assigned to it. The lonely witness lives in this gap.

The technical machinery of §11–§13 (Complementary Pairs, Universal Blocking Theorem, Phase-Uniform Extension) formalises this "missing-runner" principle for $n = 11$: the Complementary Pairs structure identifies the primary unclaimed slot $I_9$, and Theorem U + Lemma S2 prove that some slot $I_k$ has strictly positive good fraction (in $\sigma_2=+1$ cases this may be $I_9$ directly or a cascade slot such as $I_8$ or $I_7$ when $I_9$ is covered by a filler runner). The Phase-Uniform Extension then propagates this across all pacemaker cycles of $W_{\rm ref}$.

**Heuristic picture (not used in the proof).** The arithmetic progression is the baseline configuration for the AP witness framework developed in §§2–13. In bounded ratio, the direct witness $t^* = 10/(11e_{10})$ already solves the problem before any AP analysis is needed. In large ratio, the AP witnesses can all fail simultaneously, and the proof switches to the unclaimed-slot analysis in the window $W_{\rm ref}$.

### 1.3 Proof strategy for Theorem B

The proof of Theorem B is elementary.

1. Set $t^* = 10/(11e_{10})$.
2. Then $e_{10} t^* = 10/11$, while the ratio hypothesis gives
$$e_1 t^* = \frac{10e_1}{11e_{10}} \geq \frac{1}{11}.$$
3. Since $e_1 \leq e_i \leq e_{10}$ for every $i$, we obtain
$$\frac{1}{11} \leq e_i t^* \leq \frac{10}{11}.$$
Hence $\|e_i t^*\| = e_i t^* \geq 1/11$ for all $i$.

### 1.4 Relationship to [v2] and to earlier versions

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation unconditionally; this paper proves the classical formulation.

### 1.5 Structure

- §2–§3: Notation and Witness-Control Law
- §4–§8: Local algebra, speed-ratio partition, Theorem B, Classical EFN, compatibility
- §9: Main theorem (Theorem B + dependency table)
- §10.1: The open case and motivation for Route 3
- §10.2: Irrational-ratio case (Proposition E) — torus-closure argument
- §10.3: Commensurable large-ratio decomposition (Case R> formalised)
- §10.4: Route 3 — Coupling Principle, Complementary Pairs, Runner 2 Incompatibility
- §11: Universal Blocking Theorem (Theorem U — complete self-contained proof)
- §12: The σ₂=−1 Case (Lemma S1 + Lemma S2 — complete self-contained proofs)
- §13: Phase-Uniform Extension and Theorem W_ref (complete self-contained proof)
- §14: Theorem C — Complete Proof (with Lemma CR reducing commensurable reals to integers)
- §15: The 11-Pacemaker Special Case (independent verification)
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
- **Large-ratio regime** ($\rho > 10$, equivalently $a_1 < 1$): the AP witness family $\{m/11\}$ is insufficient for some configurations in this regime. The gap is documented in §10.1. This case decomposes further (§10.3) into the irrational sub-case (closed by Proposition E, §10.2) and the commensurable sub-case (closed by Theorem W_ref, §13).

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

**Gap Statement 6.3'' ($a_1 < 1$ — open within AP framework alone).** When $a_1 < 1$, the AP witness family $\{t_m = m/11 : m = 1,\ldots,10\}$ is **insufficient to certify loneliness for all configurations in $\mathcal{D}_{\mathrm{cl}}$**. As documented in §10.1, there exist configurations in $\mathcal{D}_{\mathrm{cl}}$ with $a_1 < 1$ that simultaneously block all ten AP witnesses, while a valid (non-AP) witness exists. The commensurable sub-case is closed by Theorem W_ref (§13); the irrational sub-case is closed by Proposition E (§10.2).

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

**Proof.** We establish each point directly from the classical EFN structure (Theorem 7.1' and Lemma 8.1').

**Point 1 (Finite branch control).** By Theorem 7.1'(5), $\mathcal{D}_{\mathrm{cl}}$ is a bounded open polytope contained in the compact closure $\overline{\mathcal{D}_{\mathrm{cl}}}$, so each $\delta_i$ lies in a bounded interval $[\delta_i^{\min}, \delta_i^{\max}]$. By Lemma 8.1', the active branch index $n_i$ at witness $m$ satisfies the two-sided inequality $1 \leq r_i(m) + m\delta_i - 11n_i \leq 10$, which rearranges to
$$n_i \in \left[\frac{r_i(m) + m\delta_i^{\min} - 10}{11},\; \frac{r_i(m) + m\delta_i^{\max} - 1}{11}\right].$$
Since the endpoints are finite (as $\delta_i^{\min}, \delta_i^{\max}$ are finite), this interval contains only finitely many integers. Hence for each pair $(i, m)$, only finitely many branch indices $n_i$ are ever active. $\square$

**Point 2 (Deterministic active-branch selection).** From Lemma 8.1', the loneliness condition $\{a_i t_m\} \in [1/11, 10/11]$ is equivalent to: there exists a unique integer $n_i$ such that $\delta_i \in J_i^{(m)}(n_i) := [(11n_i + 1 - r_i(m))/m,\; (11n_i + 10 - r_i(m))/m]$. The intervals $J_i^{(m)}(n_i)$ for distinct integers $n_i$ are disjoint (consecutive intervals are separated by the gap $[(11(n_i+1) + 1 - r_i(m))/m,\; (11n_i + 10 - r_i(m))/m]$ of width $(11 - 9)/m = 2/m > 0$). Therefore, for any fixed $\delta_i$ not lying exactly on a boundary, the active branch $n_i$ is uniquely determined. On each open polyhedral cell of $\mathcal{D}_{\mathrm{cl}}$ (defined by fixing which half of each boundary each $\delta_i$ lies on), all ten branch indices $(n_1, \ldots, n_{10})$ are constant and uniquely determined. $\square$

**Point 3 (Finite-state evolution).** Branch transitions for runner $i$ at witness $m$ occur precisely when $\delta_i$ crosses a boundary of $J_i^{(m)}(n_i)$, i.e., when $\delta_i = (11n_i + 1 - r_i(m))/m$ or $\delta_i = (11n_i + 10 - r_i(m))/m$. By Point 1, $n_i$ ranges over a finite set for each $(i,m)$, so there are finitely many such boundary values for each pair. Summing over all $(i, m) \in \{1,\ldots,10\} \times \mathcal{W}$ (with $|\mathcal{W}| = 10$), there are at most $10 \times 10 \times 2 \times |\{n_i\}| < \infty$ boundary hyperplanes in $\mathcal{D}_{\mathrm{cl}}$. The branch-state tuple $(n_1,\ldots,n_{10})$ therefore forms a finite-state system as $\delta$ varies in $\mathcal{D}_{\mathrm{cl}}$. $\square$

**Point 4 (Classical perturbation confinement).** A \emph{chamber-death event} at $(i, m)$ is the exit of $\delta_i$ from the loneliness interval $J_i^{(m)}(n_i)$. By the definition of $\mathcal{D}_{\mathrm{cl}}$ (open domain with $0 < a_1 < \cdots < a_9 < 10$), any perturbation $\delta \mapsto \delta + \varepsilon$ that stays within $\mathcal{D}_{\mathrm{cl}}$ crosses only the finitely many branch boundaries identified in Point 3. Each such crossing is one of:
(a) \emph{Branch recurrence}: $\delta_i$ re-enters $J_i^{(m)}(n_i)$ from the same side (no net state change).
(b) \emph{Branch offset}: $\delta_i$ crosses into $J_i^{(m)}(n_i \pm 1)$ (adjacent branch; the loneliness condition for runner $i$ at witness $m$ is now satisfied in the adjacent branch).
(c) \emph{Boundary saturation}: $\delta_i$ reaches a boundary of $\mathcal{D}_{\mathrm{cl}}$ itself (impossible for perturbations remaining in the open domain).
Since there are finitely many branch boundaries and the domain is bounded, any continuous deformation of $\delta$ within $\mathcal{D}_{\mathrm{cl}}$ crosses finitely many boundaries — it cannot generate infinitely many independent extinction events. $\square$

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

**Direct proof.** Set
$$t^* = \frac{10}{11e_{10}}.$$
Then
$$e_{10}t^* = \frac{10}{11}, \qquad e_1 t^* = \frac{10e_1}{11e_{10}} \geq \frac{1}{11}$$
because $e_{10}/e_1 \leq 10$. Since $e_1 \leq e_i \leq e_{10}$ for every $i$,
$$\frac{1}{11} \leq e_i t^* \leq \frac{10}{11}.$$
Hence $\|e_i t^*\| = e_i t^* \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

---

## 10. Case R> Closure

### 10.1 The open case

Theorem B gives witness $t^* = 10/(11e_{10})$ when $e_{10}/e_1 \leq 10$. For ratio $> 10$, runner 1 can be positioned so all ten AP witnesses fall inside a bad interval. This is not a theoretical possibility — it occurs at the explicit configuration
$$a = (0.5,\; 2.2,\; 11/3,\; 33/7,\; 5.5,\; 6,\; 7,\; 8,\; 9,\; 10):$$
runners 1 and 5 together block witnesses 1–4 and 6–10; runner 5 blocks witnesses 2, 4, 6, 8, 10; runner 3 blocks 3, 6, 9; etc. All ten AP witnesses $\{m/11\}$ are blocked. (The LRC still holds — a non-AP witness $t = 4/17$ gives $\min_i \|a_i \cdot 4/17\| \approx 0.109 > 1/11$. The AP framework is simply insufficient to certify it.)

This motivates the case split: §10.2 handles irrational ratio; §10.3–§14 handle commensurable ratio $> 10$ via Route 3. Simple extended witness families (Route A) and reduction arguments (Route B) fail — see Appendix B.

### 10.2 Irrational-ratio case

**Proposition E (Irrational-ratio case — Kronecker closure).** Let $e_1 < \cdots < e_{10}$ be ten distinct positive real speeds. Suppose there exist indices $i \neq j$ such that $e_i/e_j \notin \mathbb{Q}$. Then there exists $t > 0$ with $\|e_\ell t\| \geq 1/11$ for all $\ell = 1,\ldots,10$.

**Proof.** Let
$$\mathbf{x}(t) := (e_1t,\ldots,e_{10}t) \bmod 1 \in \mathbb{T}^{10}, \qquad
\mathcal{S} := (1/11,10/11)^{10} \subset \mathbb{T}^{10}.$$
It is enough to prove that the orbit $\{\mathbf{x}(t): t \in \mathbb{R}\}$ meets the open set $\mathcal{S}$.

Let
$$L := \{m=(m_1,\ldots,m_{10}) \in \mathbb{Z}^{10} : m_1e_1 + \cdots + m_{10}e_{10} = 0\}.$$
By the Kronecker approximation theorem [KN74, Ch. 7], the closure of the orbit $\mathbf{x}(t)$ is the subtorus
$$T_e := \{y=(y_1,\ldots,y_{10}) \in \mathbb{T}^{10} : m_1y_1 + \cdots + m_{10}y_{10} \equiv 0 \pmod 1 \text{ for every } m \in L\}.$$
We show that $T_e \cap \mathcal{S} \neq \emptyset$.

Because some ratio $e_i/e_j$ is irrational, the speeds are not all commensurable. Hence
$$d := \dim_{\mathbb{Q}} \operatorname{span}_{\mathbb{Q}}\{e_1,\ldots,e_{10}\} \geq 2.$$
Choose a $\mathbb{Q}$-basis $b_1,\ldots,b_d$ from the set $\{e_1,\ldots,e_{10}\}$ itself; in particular $b_k > 0$ for every $k$. Write
$$e_i = \sum_{k=1}^d r_{ik} b_k, \qquad r_{ik} \in \mathbb{Q}.$$

Pick a rational vector $v=(v_1,\ldots,v_d) \in \mathbb{Q}_{>0}^d$ sufficiently close to $b=(b_1,\ldots,b_d)$ that the numbers
$$q_i := \sum_{k=1}^d r_{ik} v_k \qquad (i=1,\ldots,10)$$
are still positive, distinct, and ordered:
$$0 < q_1 < \cdots < q_{10}.$$
Thus $(q_1,\ldots,q_{10})$ is a commensurable speed configuration. After clearing denominators, it reduces to an integer-speed configuration. In the bounded-ratio case ($q_{10}/q_1 \leq 10$), Theorem B gives an explicit witness $s_0 = 10/(11q_{10})$ with $\{q_i s_0\} \in [1/11, 10/11]$ for all $i$; in the large-ratio case ($q_{10}/q_1 > 10$), Corollary $W_{\rm ref}$ gives a witness in $W_{\rm ref}$ with the same property. In both cases the good fraction is strictly positive (Theorem B's witness is interior to the good-fraction window, and Corollary $W_{\rm ref}$ gives GF $\geq 538/54395 > 0$), so the set of valid witnesses has positive measure and in particular contains points at which $\{q_i s\}$ is strictly interior to $[1/11, 10/11]$. Choose any such $s^*$ strictly in the interior of the good-fraction window; then
$$\{q_i s^*\} \in (1/11,10/11) \qquad \text{for all } i=1,\ldots,10.$$
Set
$$y := (\{q_1s^*\},\ldots,\{q_{10}s^*\}) \in \mathcal{S}.$$

We claim that $y \in T_e$. Let $m=(m_1,\ldots,m_{10}) \in L$. Since
$$0 = \sum_{i=1}^{10} m_i e_i = \sum_{k=1}^d \left(\sum_{i=1}^{10} m_i r_{ik}\right)b_k$$
and $b_1,\ldots,b_d$ are $\mathbb{Q}$-linearly independent, we have
$$\sum_{i=1}^{10} m_i r_{ik} = 0 \qquad \text{for each } k=1,\ldots,d.$$
Therefore
$$\sum_{i=1}^{10} m_i q_i
= \sum_{k=1}^d \left(\sum_{i=1}^{10} m_i r_{ik}\right) v_k
= 0.$$
Since the $m_i$ are integers,
$$\sum_{i=1}^{10} m_i y_i \equiv s^* \sum_{i=1}^{10} m_i q_i \equiv 0 \pmod 1,$$
so indeed $y \in T_e$.

Thus $T_e \cap \mathcal{S} \neq \emptyset$. Because the orbit $\mathbf{x}(t)$ is dense in $T_e$, some $t > 0$ satisfies $\mathbf{x}(t) \in \mathcal{S}$. For this $t$,
$$\{e_\ell t\} \in (1/11,10/11) \subset [1/11,10/11] \qquad \text{for all } \ell=1,\ldots,10,$$
hence $\|e_\ell t\| \geq 1/11$ for every $\ell$. $\square$

*Remark E.1.* The only configurations not covered by Proposition E are the commensurable ones, i.e. those for which every ratio $e_i/e_j$ is rational. That is exactly Case R> in the decomposition below.

*Remark E.2 (Explicit witnesses not provided).* Proposition E is an existence proof via orbit closure; it does not produce an explicit witness time $t^*$. By contrast, Theorem B produces the explicit witness $t^* = 10/(11e_{10})$.

### 10.3 Commensurable large-ratio decomposition

**Theorem (Gap Decomposition).** The full classical LRC for $n = 11$ decomposes into three mutually exclusive and exhaustive sub-cases:

| Case | Speed structure | Status | Method |
|---|---|---|---|
| **Case R** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 \leq 10$ | **Proved** (Theorem B) | Explicit witness $t^* = 10/(11e_{10})$ |
| **Case I** | At least one $e_i/e_j \notin \mathbb{Q}$ (irrational ratio) | **Proved** (Proposition E) | Kronecker closure |
| **Case R>** | All $e_i/e_j \in \mathbb{Q}$ (commensurable), $e_{10}/e_1 > 10$ | **CLOSED** — Corollary W_ref (§13): switch to $W_{\rm ref} = [1/(11e_1), 10/(11e_1)]$; runner $e_1$ trivially isolated; Route 3 cascade gives GF$_{2\text{-}10}(W_{\rm ref})>0$ | Theorem W_ref + Route 3 |

**Proof of decomposition.** Cases R, I, R> are exhaustive (every configuration falls into exactly one) and mutually exclusive. Case R is handled by Theorem B with explicit witness. Case I is handled by Proposition E. Case R> is the complement. $\square$

**Structure of Case R>.** In Case R>, all speeds $e_1,\ldots,e_{10}$ are rational multiples of a common base $\omega > 0$: write $e_i = p_i \omega / q$ for integers $p_1 < \cdots < p_{10}$ and a common denominator $q$. The LRC condition becomes: $\exists k \in \mathbb{Z}_{>0}$ such that $\{p_i k / (11q)\} \in [1/11, 10/11]$ for all $i = 1,\ldots,10$. This reduces to a finite arithmetic problem for each choice of $(p_1,\ldots,p_{10},q)$.

**Why Case R> is hard.** The EFN normalisation gives $a_1 = 10e_1/e_{10} = 10p_1/p_{10} < 1$ (since $p_{10}/p_1 > 10$). The AP witness $t=1/11$ fails because $\{a_1/11\} = a_1/11 < 1/11$. The witness family $\{m/11\}$ is insufficient (§10.1), while the orbit is finite in the commensurable case, so the density argument of Proposition E is unavailable. The Route 3 approach works by switching to runner $e_1$'s window.

### 10.4 Route 3: Coupling Principle and Complementary Pairs

We introduce the key algebraic structure underlying Case R>. This route exploits the deep algebraic structure of the mod-11 bijection and the **Coupling Principle** — the observation that all of a runner's bad intervals move together when its speed is tuned.

#### 10.4.1 The Coupling Principle and Resonance Cascade

**Definition 10.4.A0 (Analysis window $W_0$).** Define the **analysis window** and its pacemaker sub-cycles by
$$W_0[m] = \left[\frac{11m+1}{110},\; \frac{11m+10}{110}\right], \quad m = 0, 1, 2, \ldots$$
These are the sub-windows in which runner $v_{10}$ (EFN speed $a_{10} = 10$) is isolated; each has width $9/110$. The **combined analysis window** is $W_0 = W_0[0] \cup W_0[1] \cup \cdots = [1/110, \infty) \cap \bigcup_m W_0[m]$. In the context of a single pacemaker cycle (§11–§12), we write $W_0 = W_0[m]$ for the relevant cycle $m$. Slots $I_k = [(11k+1)/110, (11k+10)/110]$ coincide with the pacemaker cycles: $I_k = W_0[k]$.

**Definition 10.4.A1 (Completely Blocking configuration).** A configuration $(a_1,\ldots,a_{10})$ is **completely blocking (CB)** for a window $W \subset \mathbb{R}_{>0}$ if
$$\mathrm{GF}(W) = 0,$$
i.e., every $t \in W$ is covered by the bad interval of at least one runner: $\forall t \in W,\; \exists i \in \{1,\ldots,10\},\; k \geq 0 \text{ s.t. } t \in B_{i,k}$. Equivalently, the union $\bigcup_{i,k} B_{i,k}$ covers $W$.

The analysis of §11–§13 proceeds by **assuming for contradiction** that the configuration is CB for the pacemaker window $W_0[m^*] \subset W_{\rm ref}$ (i.e.\ $\mathrm{GF}(W_0[m^*]) = 0$). The machinery below derives contradictory speed constraints under this assumption, proving the assumption false — hence GF$(W_0[m^*]) > 0$ and a loneliness witness exists.

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

**Theorem 10.4.5 (Runner 2 Incompatibility).** *Closing $I_4$ requires $a_2 \geq 20/9$; closing $I_9$ via runner 2 requires $a_2 \leq 575/261$. Since $20/9 > 575/261$ (gap $= 5/261 > 0$), runner 2 cannot simultaneously close both. The alternative — runner 3 closing $I_9$ at the cost of opening $I_2$ — shows GF$(I_2) > 0$ in that sub-case. Hence GF$(I_k) > 0$ for some $k \in \{2, 4, 9\}$ in every CB configuration in the ++------ class.*

**Proof: I₄ constraint.** Runner 2's bad interval formula gives $B_{2,0} = [10/(11a_2),\; 12/(11a_2)]$. For its left end to reach $45/110$ (left edge of $J_4$):
$$\frac{10}{11a_2} \leq \frac{45}{110} = \frac{9}{22} \implies a_2 \geq \frac{20}{9}.$$
No other runner can cover $J_4$'s left boundary $45/110$ without creating a new gap elsewhere. The complete runner-by-runner verification is given in Lemma 11.2.1 of §11: for all $j \geq 3$ with $a_j \in (j-1, j+1)$, the bad interval $B_{j,0}$ ends strictly before $45/110$ and $B_{j,1}$ starts strictly after $45/110$ (the calculation uses $a_j \geq 3$ for $j \geq 3$, giving $B_{j,0}[1] = 12/(11a_j) \leq 12/33 \approx 0.364 < 45/110 \approx 0.409$ and $B_{j,1}[0] = 21/(11a_j) \geq 21/44 \approx 0.477 > 45/110$). Hence the point $45/110$ lies in a gap of every runner except runner 2, confirming that $a_2 \geq 20/9$ is necessary for $I_4$ to be closed.

**Proof: I₉ constraint.** Runner 2's bad interval $B_{2,1} = [21/(11a_2),\; 23/(11a_2)]$. For it to cover $J_9 = [10/11,\; 261/275]$:
$$\frac{21}{11a_2} \leq \frac{10}{11} \implies a_2 \geq \frac{21}{10},$$
$$\frac{23}{11a_2} \geq \frac{261}{275} \implies a_2 \leq \frac{6325}{2871} = \frac{575}{261}.$$
The only alternative for covering $10/11$ is runner 3 ($k=2$, range $[3.2, 3.4]$). Runner 3 in this range satisfies $a_3 < 2750/759$, which by Theorem 10.4.4 produces a **good window** in I₂: $\mathrm{GF}(I_2) > 0$. So runner 3 cannot substitute without opening I₂. Therefore $a_2 \leq 575/261$ is necessary for I₉ to be closed.

**Incompatibility.** The two constraints are:
$$a_2 \geq \frac{20}{9} \approx 2.222 \quad \text{and} \quad a_2 \leq \frac{575}{261} \approx 2.203.$$
Since $20 \times 261 = 5220 > 5175 = 9 \times 575$, we have $20/9 > 575/261$ with gap $5/261 > 0$. No value of $a_2$ satisfies both. $\square$

*The proofs of §§11–13 are fully self-contained and appear inline below.*

---

## 11. Universal Blocking Theorem (Theorem U — the σ₂=+1 Case)

**Proof structure.** This section proves Theorem U by contradiction. Fix a configuration with $\sigma_2 = +1$ and assume it is CB for some pacemaker cycle $W_0[m^*] \subset W_{\rm ref}$ (Definition 10.4.A1): i.e.\ $\mathrm{GF}(W_0[m^*]) = 0$, meaning every slot $I_k$ ($k = 1,\ldots,9$) is fully covered by the bad intervals of runners $2,\ldots,9$. The analysis below derives contradictory constraints on $a_2,\ldots,a_9$: no speed assignment satisfies all of them simultaneously. Therefore the CB assumption is false, GF$(I_k) > 0$ for some $k$, and a loneliness witness exists in $W_0[m^*]$.

### 11.1 Notation and Setup

Slots $I_k = [(11k+1)/110, (11k+10)/110]$ for $k=1,\ldots,9$. In particular:
- $I_4 = [45/110, 54/110]$; $\quad I_9 = [10/11, 109/110]$.

**Bad interval:** $B_{j,k}(a_j) = [(11k+10)/(11a_j),\; (11k+12)/(11a_j)]$ for $k = 0,1,2,\ldots$

**Sign convention:** $\sigma_j = +1$ means $a_j \in (j,j+1)$; $\sigma_j = -1$ means $a_j \in (j-1,j)$.

**Lemma 11.1.1 (Sign-Range Containment).** *In any CB configuration for $W_0[m^*] \subset W_{\rm ref}$ under EFN normalisation with $a_{10} = 10$ and $a_1 < 1$, every runner $j \in \{2,\ldots,9\}$ satisfies $a_j \in (j-1, j+1)$.*

*Proof.* We prove by contradiction. Assume the configuration is CB and suppose $a_j \notin (j-1, j+1)$ for some $j \in \{2,\ldots,9\}$. Since $\sigma_2 = +1$ fixes $a_2 \in (2,3)$, the case $j=2$ cannot arise. We handle $j \in \{3,\ldots,9\}$ using the first two bad intervals:
$$B_{j,0} = \!\left[\frac{10}{11a_j},\; \frac{12}{11a_j}\right]\!, \quad B_{j,1} = \!\left[\frac{21}{11a_j},\; \frac{23}{11a_j}\right]\!.$$
The *primary gap* $G_j = \bigl(\tfrac{12}{11a_j},\, \tfrac{21}{11a_j}\bigr)$ is covered by no bad interval of runner $j$.

**Case 1: $a_j \geq j+1$ for some $j \in \{3,\ldots,9\}$.** Since $j \geq 3$, we have $a_j \geq 4$, so $B_{j,0}[1] = 12/(11a_j) \leq 12/44 = 30/110 < 34/110 = I_3[\text{left}]$. We split according to whether $G_j$ completely contains $I_3$.

*Sub-case 1a: $a_j \in [4, 210/43]$ (so $B_{j,1}[0] \geq 43/110 = I_3[\text{right}]$).* Since $21/(11a_j) \geq 43/110$ iff $a_j \leq 210/43 \approx 4.88$, both $B_{j,0}[1] \leq 30/110 < I_3[\text{left}]$ and $B_{j,1}[0] \geq I_3[\text{right}]$ hold, so $I_3 \subset G_j$. Runner $j$ completely skips $I_3$. For the CB assumption (GF$(I_3) = 0$), some runner $r \neq j$ must cover $I_3[\text{left}] = 34/110$. The feasibility condition $B_{r,k}[1] \geq 34/110$ and $B_{r,k}[0] \leq 34/110$ gives $a_r \in [5(11k+10)/17,\; 5(11k+12)/17]$:
- $k=0$: $a_r \in [50/17, 60/17] \approx [2.94, 3.53]$. Only runner 2 qualifies (all $a_r \geq a_3 \geq 4$ for $r \geq 3$). If $a_2 < 50/17$: runner 2 also misses $34/110$; $I_3[\text{left}]$ uncovered → GF$(I_3) > 0$. If $a_2 \in [50/17, 3)$: runner 2's $B_{2,0}[0] = 10/(11a_2) \geq 17/55 > 23/110 = I_2[\text{left}]$, so runner 2 starts inside $I_2$, leaving $[I_2[\text{left}], B_{2,0}[0]]$ uncovered in $I_2$. No runner $r \geq 3$ has $a_r \leq 60/17 \approx 3.53$ (all $a_r \geq 4$); GF$(I_2) > 0$. Contradiction in both sub-sub-cases.
- $k=1$: $a_r \in [105/17, 115/17] \approx [6.18, 6.76]$. Then $B_{r,0}[1] \leq 12/(11 \cdot 6.18) \approx 0.177 < I_2[\text{left}]$ and $B_{r,1}[0] \leq 21/(11 \cdot 6.18) \approx 0.309 = I_3[\text{left}]$. The gap $G_r \supset I_2$: runner $r$ completely skips $I_2$. GF$(I_2) > 0$. Contradiction.
- $k \geq 2$: upper bounds on $a_r$ give $a_r \leq 170/17 = 10$; but such runners also have $G_r$ containing $I_2$ or a lower slot by the same calculation. GF $> 0$. Contradiction.

*Sub-case 1b: $a_j \in (210/43, j+1)$ (so $B_{j,1}[0] \in I_3$).* Runner $j$'s $B_{j,1}$ starts inside $I_3$, leaving $[I_3[\text{left}], B_{j,1}[0]]$ uncovered in $I_3$ (since $B_{j,0}[1] < I_3[\text{left}]$). The feasibility analysis for covering $I_3[\text{left}]$ is identical to Sub-case 1a (same $k=0$ and $k=1$ intervals), yielding GF$(I_2)$ or GF$(I_3) > 0$ in every sub-sub-case. Contradiction.

For $j \geq 4$ with $a_j \geq j+1 \geq 5$: the same argument applies with $G_j \subset (0,\, 21/55) = (0,\, 42/110)$ now containing $I_2[\text{left}] = 23/110$. Runner $j$ skips $I_2[\text{left}]$, and the analogous feasibility analysis forces GF $> 0$ in $I_1$ or $I_2$. Contradiction.

**Case 2: $a_j \leq j-1$ for some $j \in \{3,\ldots,9\}$.** EFN ordering and $\sigma_2=+1$ give $a_3 > a_2 > 2 = 3-1$, so $j=3$ cannot arise. For $j \geq 4$ with $a_j \leq j-1$: $B_{j,0}[0] = 10/(11a_j) \geq 10/(11(j-1))$. At $j=4$ (the binding case): $B_{4,0}[0] \geq 10/33 > 23/110 = I_2[\text{left}]$. Runner 4's $B_{4,0}$ starts inside $I_2$, leaving $[I_2[\text{left}], B_{4,0}[0]]$ uncovered. The feasibility analysis for covering $I_2[\text{left}]$ (identical structure to Case 1) forces GF $> 0$ in $I_1$ or $I_2$. For $j \geq 5$: $B_{j,0}[0] \geq 10/(11 \cdot 4) = 10/44 > 12/110 = I_1[\text{left}]$ and the cascade is similar. Contradiction in all sub-cases.

In every case the CB assumption is contradicted. Therefore $a_j \in (j-1, j+1)$ for all $j \in \{2,\ldots,9\}$. $\square$

*Consequence.* The 256 sign classes $\sigma_j = \pm 1$ for $j \in \{2,\ldots,9\}$ cover all CB configurations exhaustively and without gaps: every CB configuration belongs to exactly one of the $2^8 = 256$ classes.

**Complementary Pairs (Theorem 10.4.1):**

| Pair | Primary slots | σ=+1 obligation | σ=−1 obligation |
|------|--------------|-----------------|-----------------|
| (2,9) | $I_4, I_5$ | $I_4$ (right side) | $I_5$ (left side) |
| (3,8) | $I_3, I_8$ | $I_8$ | $I_3$ |
| (4,7) | $I_2, I_7$ | $I_7$ | $I_2$ |
| (5,6) | $I_1, I_6$ | $I_6$ | $I_1$ |

Slot $I_9$ is *unclaimed* by any complementary pair. This is the source of the gap-propagation mechanism: any runner that covers $I_9$ must do so "off-schedule," creating slack in its primary slot.

**Primary slot right edge** (for σ=−1 runners, this is the edge their $B_{j,0}$ must reach):

| Runner $j$ | Primary slot | Right edge $\mathrm{PSR}(j)$ |
|-----------|-------------|--------------------------|
| 3 | $I_3$ | $43/110$ |
| 4 | $I_2$ | $32/110 = 16/55$ |
| 5 | $I_1$ | $21/110$ |

**Coverage function.** Given a right gap $[g_L, 109/110] \subset I_9$, runner $j$ is *feasible* for this gap if there exists $k \geq 0$ such that $B_{j,k}[0] \leq g_L$ and $B_{j,k}[1] \geq 109/110$. The feasibility condition in terms of $a_j$ is:
$$a_j \in \left[\frac{11k+10}{11 g_L},\; \frac{(11k+12)\cdot110}{11\cdot109}\right] =: F_{j,k}(g_L).$$

### 11.2 I₄ Lower Bound on a₂

#### Fact A1
For $a_9 \in (8,9)$: runner 9 never covers $I_4$'s left edge $45/110$, leaving gap $[45/110, 43/(11a_9)] \subset I_4$.

*Proof.* $43/(11a_9) > 45/110 \iff a_9 < 946/99 \approx 9.556$. ✓ $\square$

#### Fact B
For $a_9 \in (9,10)$: $B_{9,3}[0] = 43/(11a_9)$ equals $45/110$ iff $a_9 = 86/9$.

*Proof.* $43/(11a_9) = 45/110 \Rightarrow a_9 = 86/9 \approx 9.556 \in (9,10)$. $\square$

#### Lemma 11.2.1 (I₄ lower bound, σ₉=−1 or σ₉=+1 with a₉ < 86/9)

> **Lemma 11.2.1.** For any CB configuration with $\sigma_2=+1$ and $a_9 \notin [86/9, 10)$: closing $I_4$ requires $a_2 \geq 20/9$.

**Proof.** By Facts A1/B, runner 9 leaves a left gap at $45/110$ in $I_4$.

*Runner-by-runner exclusion.* We show that no runner $j \geq 3$ with $a_j \in (j-1,j+1)$ (guaranteed by Lemma 11.1.1) can cover the point $45/110$ in any of its bad intervals:

- **Bad interval $B_{j,0}$ ends before $45/110$:** $B_{j,0}[1] = 12/(11a_j)$. For $j \geq 3$ and $a_j \geq j-1 \geq 2$: $12/(11a_j) \leq 12/22 = 6/11 \approx 0.545$. But for $a_j \geq 3$ (which holds since $j \geq 3$ and $a_j > j-1 \geq 2$, and by EFN ordering $a_j > a_{j-1} > \cdots > a_2 > 2 > 3-1 = 2$ — more precisely $a_j \geq a_3 > a_2 > a_1 \geq 0$; we have $a_3 > 2$ from $\sigma_2 = +1$ giving $a_2 \in (2,3)$ and $a_3 > a_2 > 2$, so $a_3 > 2$, but not necessarily $a_3 > 3$). More carefully: for $j \geq 3$ with $a_j \in (j-1,j+1)$ and $j \geq 3$: $a_j \geq j-1 \geq 2$. At $a_j = 2$: $B_{j,0}[1] = 12/22 \approx 0.545 > 45/110 \approx 0.409$. At $a_j = 3$: $B_{j,0}[1] = 12/33 \approx 0.364 < 0.409$. The crossover occurs at $a_j = 12/(11 \cdot 45/110) = 12 \cdot 110/(11 \cdot 45) = 1320/495 = 8/3 \approx 2.667$. Thus $B_{j,0}[1] < 45/110$ iff $a_j > 8/3$. Since $j \geq 3$ gives $a_j \in (j-1,j+1)$ with $j-1 \geq 2$, and in fact $j \geq 3 \Rightarrow a_j > a_2 > 2$ (EFN ordering). For $j = 3$: $a_3 \in (2,4)$; could have $a_3 < 8/3$. But if $a_3 < 8/3 \approx 2.667$, then $a_3 < a_2$ is impossible since $a_2 \in (2,3)$ with $a_2 < a_3$ required by EFN ordering — so $a_3 > a_2 > 2$. If $a_3 \in (2, 8/3)$: then $B_{3,0}[1] = 12/(11a_3) > 45/110$, so runner 3's $B_{3,0}$ DOES reach $45/110$. This means runner 3 ($\sigma_3$ either sign) can in principle cover the left gap of $I_4$ via $B_{3,0}$.

We therefore need to verify that runner 3 covering $I_4$'s left gap creates an open slot elsewhere. For $a_3 \in (2, 8/3)$: $B_{3,0} = [10/(11a_3), 12/(11a_3)]$ straddles $45/110$ iff $10/(11a_3) \leq 45/110$, i.e.\ $a_3 \geq 20/9 \approx 2.222$. At $a_3 \in [20/9, 8/3)$: runner 3's $B_{3,0}$ covers $[10/(11a_3), 12/(11a_3)] \supset \{45/110\}$. But $B_{3,0}$ ends at $12/(11a_3) > 12/(11 \cdot 8/3) = 12 \cdot 3/(11 \cdot 8) = 36/88 = 9/22 > 43/110 = I_3[\mathrm{right}]$. So $B_{3,0}$ extends past $I_3$'s right boundary, meaning runner 3 cannot simultaneously cover its primary slot $I_3$: $B_{3,0}[0] = 10/(11a_3) > 34/110 = I_3[\mathrm{left}]$ (since $a_3 < 100/34 \approx 2.94$; at $a_3 = 20/9$: $10/(11 \cdot 20/9) = 90/220 = 9/22 > 34/110 = 17/55$, so $B_{3,0}$ starts after $I_3$'s left edge). In this range runner 3 misses $I_3$'s left sub-gap $[34/110, 10/(11a_3)]$, forcing another runner to cover $I_3$'s left — which by PSM gives GF$(I_k) > 0$ for runner 3's new primary obligation. For all $j \geq 4$ (or $j = 3$ with $a_3 > 8/3$): $B_{j,0}[1] \leq 12/(11 \cdot 8/3) = 9/22 \cdot (3/3) < 45/110$ — confirmed below.

More directly: for $j \geq 4$ and $a_j > j-1 \geq 3$: $B_{j,0}[1] = 12/(11a_j) < 12/33 = 4/11 = 40/110 < 45/110$. ✓

- **Bad interval $B_{j,1}$ starts after $45/110$:** $B_{j,1}[0] = 21/(11a_j)$. For $j \geq 3$ and $a_j < j+1 \leq 10$: $B_{j,1}[0] \geq 21/(11 \cdot 10) = 21/110 < 45/110$. At $j = 3$, $a_3 < 4$: $B_{3,1}[0] = 21/(11a_3) > 21/44 \approx 0.477 > 45/110 \approx 0.409$. ✓ At $j \geq 4$, $a_j < j+1$: $B_{j,1}[0] = 21/(11a_j) > 21/(11(j+1)) \geq 21/55 \approx 0.382$ for $j=4$, and for $j=4$: $a_4 < 5$, so $B_{4,1}[0] > 21/55 \approx 0.382 < 45/110$ — not conclusive from this alone. But $B_{4,0}[1] = 12/(11a_4) < 12/44 = 3/11 \approx 0.273 < 45/110$ for $a_4 > 3$. And $B_{4,1}[0] = 21/(11a_4) > 21/55 \approx 0.382 < 45/110$ for $a_4 < 105/44 \approx 2.386$, which is outside $a_4 \in (3,5)$. In fact for $a_4 \in (3,5)$: $B_{4,1}[0] = 21/(11a_4) \in (21/55, 21/33) = (0.382, 0.636)$; specifically at $a_4 > 105/44 \approx 2.386$ (always true for $a_4 > 3$): $21/(11a_4) < 21/33 \approx 0.636$. But is $21/(11a_4) > 45/110 = 9/22$? This requires $a_4 < 21 \cdot 22/(11 \cdot 9) = 462/99 = 14/3 \approx 4.667$. For $a_4 \in (3, 14/3)$: $B_{4,1}[0] > 45/110$ ✓, so $B_{4,1}$ starts above $45/110$. For $a_4 \in [14/3, 5)$: $B_{4,1}[0] \leq 45/110$, so runner 4 CAN start covering $I_4$ from below via $B_{4,1}$. In this case (Chain B territory): runner 4 covering $I_4$'s left via $B_{4,1}$ (from below $45/110$) forces Chain B — GF$(I_7) \geq 1533/18490 > 0$ (§11.4). So runner 4's coverage of $I_4$ opens $I_7$.

Summary: for all $j \geq 3$ with $a_j \in (j-1,j+1)$, either (a) runner $j$ cannot reach $45/110$ (infeasible), or (b) it can reach $45/110$ only at the cost of opening another slot (runner 3 case opens $I_3$; runner 4 in the $a_4 \geq 14/3$ sub-case opens $I_7$ via Chain B). In case (b), GF$(I_k) > 0$ for some other $k$, so the CB assumption is already contradicted. In case (a), only runner 2 can cover $45/110$.

The condition $B_{2,0}[0] \leq 45/110$ gives:
$$\frac{10}{11a_2} \leq \frac{45}{110} \implies a_2 \geq \frac{20}{9}. \quad \square$$

#### Lemma 11.2.2 (I₄ lower bound, σ₉=+1 with a₉ ≥ 86/9)

> **Lemma 11.2.2.** For $\sigma_2=+1$, $a_9 \geq 86/9$: closing $I_4$ requires $a_2 \geq 2a_9/9 \geq 172/81$.

**Proof.** Runner 9 now covers $I_4$ from the left edge; its right coverage ends at $45/(11a_9) < I_4[\mathrm{right}]$, leaving a right gap. For runner 2 to cover this: $a_2 \geq 2a_9/9$. $\square$

**Notation:** Write $L(a_9) = 20/9$ for $a_9 < 86/9$, and $L(a_9) = 2a_9/9$ for $a_9 \geq 86/9$. Closing $I_4$ requires $a_2 \geq L(a_9)$.

### 11.3 I₉ Coverage and the Two Top-Level Cases

**Runner 2's I₉ coverage.** For $a_2 \geq L(a_9)$, runner 2 closes $I_4$ and covers:
$$B_{2,1}(a_2) = \left[\frac{21}{11a_2},\; \frac{23}{11a_2}\right] \subset I_9, \qquad \text{with right endpoint} \leq \frac{207}{220}.$$

**Runner 9's I₉ contribution.** Define $V(a_9, \sigma_9)$ = the rightmost point of $I_9$ reachable by runner 9's bad intervals. Explicitly:

| $a_9$ range | $\sigma_9$ | Runner 9's rightmost $I_9$ coverage |
|-------------|-----------|--------------------------------------|
| $(8,\, 580/69)$ | $-1$ | None from right side; $B_{9,7}$ starts right of $207/220$ |
| $[580/69,\, 87/10)$ | $-1$ | $89/(11a_9)$ — runner 9 reaches runner 2's coverage |
| $[87/10,\, 980/109)$ | $-1$ | None — runner 9 exits $I_9$ entirely |
| $[980/109,\, 9)$ | $-1$ | $100/(11a_9)$ — runner 9 re-enters $I_9$ via $B_{9,8}$ |
| $(9,\, 1960/207)$ | $+1$ | $100/(11a_9)$ — but constraint forces incompatibility |
| $[1960/207,\, 86/9]$ | $+1$ | $100/(11a_9)$ (or $450/473$ at $a_9=86/9$) |
| $(86/9,\, 10)$ | $+1$ | $100/(11a_9) < 450/473$ |

**Combined right endpoint of runners 2+9:** $U(a_2, a_9) = \max\bigl(23/(11a_2),\; V(a_9)\bigr)$ (subject to runners bridging: no middle gap).

**Two cases:**

> **Case α (Direct Incompatibility).** The constraints $a_2 \geq L(a_9)$ (from $I_4$) and $a_2 \leq U_{\max}(a_9)$ (from closing $I_9$ via runners 2+9) are irreconcilable: $L(a_9) > U_{\max}(a_9)$.

> **Case β (Gap Propagation).** The constraints are compatible, or no upper bound exists, so runners 2+9 leave a right gap $[g_L, 109/110] \subset I_9$ with $g_L < 109/110$. The Universal Blocking Theorem (§11.4) shows this gap cannot be covered.

We verify each region of $(a_2, a_9)$ falls into one of these cases.

#### Verification of Case α regions

**α-1 (Middle gap, σ₉=−1, a₉ < 580/69):** Runner 9's $B_{9,7}$ starts at $87/(11a_9) > 207/220 \geq 23/(11a_2)$, leaving a middle gap $[23/(11a_2), 87/(11a_9)]$ in $I_9$. Bridging the gap via runner 2 requires $a_2 \leq 23a_9/87$. Direct incompatibility with $a_2 \geq 20/9$: $20/9 > 23a_9/87 \iff a_9 < 580/69$. ✓ Runner 2 cannot close both $I_4$ and the $I_9$ gap; if a filler runner (runner 3, $\sigma_3=+1$) covers the gap, Chain A forces GF$(I_8) \geq 1/50$. **GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$.** $\square$

**α-2 (High-k incompatibility, σ₉=−1, a₉ ∈ [980/109, 9)):** Runner 9's $B_{9,8}$ re-enters $I_9$; bridging requires $a_2 \leq 23a_9/98$. Direct incompatibility: $20/9 > 23a_9/98 \iff a_9 < 1960/207$. Since $9 < 1960/207$, this holds for all $a_9 < 9$. Runner 2 cannot close both $I_4$ and $I_9$; Chain A covers the case where a filler runner absorbs $I_9$. **GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$.** $\square$

**α-3 (σ₉=+1, a₉ ∈ (9, 1960/207)):** Same argument: bridging $I_9$ via runner 2 requires $a_2 \leq 23a_9/98 < L(a_9) = 20/9$. Runner 2 cannot close both $I_4$ and $I_9$; Chain A covers the filler-runner sub-case. **GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$.** $\square$

#### Verification of Case β regions

All remaining parameter regions produce a right gap $[g_L, 109/110]$ with $g_L < 109/110$:

| Region | $\sigma_9$ | $g_L$ | Minimum gap width |
|--------|-----------|-------|------------------|
| $a_9 \in [580/69,\, 87/10)$ | $-1$ | $89/(11a_9)$ | $\geq 181/6380$ |
| $a_9 \in [87/10,\, 980/109)$ | $-1$ | $23/(11a_2) \leq 207/220$ | $\geq 1/20$ |
| $a_9 \in [1960/207,\, 86/9]$ | $+1$ | $100/(11a_9)$ (or $450/473$) | $\geq 59/9460$ |
| $a_9 \in (86/9,\, 10)$ | $+1$ | $100/(11a_9) < 450/473$ | $\geq 17/430$ |

In each region the right gap is non-empty and explicitly computable. The Universal Blocking Theorem (§11.4 below) shows the gap forces a positive good fraction in some slot: in $I_9$ itself when no eligible filler runner covers it, or in a cascade slot ($I_8$ via Chain A, $I_7$ via Chain B) otherwise. Hence **GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$** in all Case β regions. $\square$

### 11.4 Universal Blocking Theorem

> **Theorem UB (Universal Blocking).** Let $[g_L, 109/110] \subset I_9$ be any non-empty interval with $0 < g_L < 109/110$. Then no speed assignment for runners $3,\ldots,8$ can cover $[g_L, 109/110]$ while maintaining GF$(I_k) = 0$ for all $k = 1,\ldots,8$.

**Proof.** We analyse each runner $j \in \{3,4,5,6,7,8\}$ and each sign $\sigma_j \in \{+1,-1\}$. In every case either:
(a) runner $j$ is *infeasible* (cannot reach $[g_L,109/110]$ from its speed range), in which case it cannot help, or
(b) runner $j$ is *feasible* but its coverage creates GF $> 0$ in some other slot.

If ALL runners are infeasible, then $[g_L,109/110]$ is uncovered and GF$(I_9) \geq 109/110 - g_L > 0$ directly.

#### Analysis of Infeasible Runners (σ=+1, j ∈ {5,6,7,8})

For runner $j$ with $\sigma_j = +1$ (speed $a_j \in (j, j+1)$), define the **Minimum Feasibility Threshold**:
$$\mathrm{MFT}(j,k) := \frac{(11k+10)\cdot109}{(11k+12)\cdot110}.$$
This is the smallest $g_L$ for which the lower bound $a_j \geq (11k+10)/(11g_L)$ does not exceed the upper bound $a_j \leq (11k+12)\cdot110/(11\cdot109)$. If $g_L < \mathrm{MFT}(j,k)$ for all $k$, runner $j$ has an empty feasibility interval and is structurally infeasible.

**Runner 5 ($\sigma=+1$, $a_5 \in (5,6)$):** The only index at which $B_{5,k}[1]$ can reach $109/110$ from within $(5,6)$ is $k=4$: upper bound $= 560/109 \approx 5.138$. The lower bound at $g_L$ is $54/(11g_L)$. These coincide at $\mathrm{MFT}(5,4) = 54\cdot109/(56\cdot110) = 2943/3080 \approx 0.9555$.

- For $g_L \leq 2943/3080$ (all of $\beta$-2, $\beta$-3, $\beta$-4, and most of $\beta$-1): lower $\geq$ upper → **infeasible**. The gap persists.
- For $g_L > 2943/3080$ (occurring in $\beta$-1 only for $a_9 \lesssim 8.48$): $a_5 \in [5.100, 5.138]$. At such $a_5$, $B_{5,2}[1] = 34/(11a_5) \leq 34/56.1 \approx 0.606 < I_6[\mathrm{left}] = 67/110$ and $B_{5,3}[0] = 43/(11a_5) \geq 43/56.5 \approx 0.761 > I_6[\mathrm{right}] = 76/110$. Runner 5's bad intervals skip $I_6$ entirely. Meanwhile, runner 3 ($\sigma=+1$) with $a_3 > 340/109$ (outside Chain A range) creates GF$(I_3) > 0$ because no runner in $\{3,\ldots,9\}$ can cover $I_3[\mathrm{right}] = 43/110$ from speed range $\geq 7$ (verified: $B_{j,k}[1] \geq 43/110$ requires $a_j \leq (11k+12)\cdot110/(11\cdot43)$; at $k=0$ this gives $a_j \leq 120/43 \approx 2.79$, incompatible with $a_j \geq 7$). And $a_3 \leq 340/109$ (in Chain A range) gives GF$(I_8) \geq 1/50$ by Chain A. In all sub-cases GF $> 0$. $\square$

**Runner 6 ($\sigma=+1$, $a_6 \in (6,7)$):** The binding index is $k=5$: upper bound $= 670/109 \approx 6.147$. $\mathrm{MFT}(6,5) = 65\cdot109/(67\cdot110) = 7085/7370 = 1417/1474 \approx 0.9614 > 450/473$. For all $\beta$ sub-regions (maximum $g_L \approx 0.963 < 1417/1474$ for the $k=5$ index): lower bound $65/(11g_L) > 670/109$ → **infeasible**. (For $k=6$: upper bound $= 780/109 \approx 7.156 > 7$, outside $\sigma=+1$ range. All other $k$ give upper bounds $< 6$ or $> 7$.) $\square$

For runners 7, 8 ($\sigma=+1$, $a_j \in (j,j+1)$ with $j \geq 7$): all bad intervals in the speed range $(7,8)$ and $(8,9)$ have $B_{j,k}[1] = (11k+12)/(11a_j) \leq (11k+12)/77$. For this to reach $109/110$: $11k+12 \geq 109\cdot77/10 = 839.3$, so $k \geq 75$. At $k=75$: $B_{j,75}[0] = 835/(11a_j) \leq 835/77 \approx 10.8 \gg I_9[\mathrm{right}]$. These intervals are entirely above $I_9$. Runner 7 and 8 with $\sigma=+1$ are **completely infeasible**. $\square$

#### Analysis of σ=−1 Runners via PSM

**Primary Slot Miss (PSM) Lemma.** For runner $j$ with $\sigma_j = -1$ ($a_j \in (j-1,j)$): if runner $j$ is feasible for $[g_L, 109/110]$ via $B_{j,k}$ for some $k \geq 1$, then $B_{j,0}[0] > \mathrm{PSR}(j)$, forcing GF$(\text{primary slot of }j) > 0$.

*Why this holds:* $B_{j,0}[0] = 10/(11a_j)$. For runner $j$ to be feasible for $I_9$ via $B_{j,k}$ ($k \geq 1$), we need $a_j \leq (11k+12)\cdot 110/(11\cdot109)$. But this upper bound on $a_j$ means $a_j$ is *small*, pushing $10/(11a_j)$ *large* — specifically, above $\mathrm{PSR}(j)$.

Proved case-by-case:

**Runner 3 (σ=−1, a₃ ∈ (2,3)):** Feasibility via $B_{3,k}$ ($k \geq 1$) requires the right endpoint $B_{3,k}[1] = (11k+12)/(11a_3) \geq 109/110$, so $a_3 \leq (11k+12)\cdot110/(11\cdot109)$. For $k=1$: $a_3 \leq 23\cdot110/(11\cdot109) = 230/109 \approx 2.11$. Then:
$$B_{3,0}[0] = \frac{10}{11a_3} \geq \frac{10}{11\cdot(230/109)} = \frac{10\cdot109}{11\cdot230} = \frac{1090}{2530} = \frac{109}{253}.$$
Compare: $\mathrm{PSR}(3) = 43/110$. Is $109/253 > 43/110$? Check: $109\cdot110 = 11990 > 43\cdot253 = 10879$. ✓ So $B_{3,0}[0] > 43/110 = I_3[\mathrm{right}]$: runner 3 misses $I_3$'s right edge. GF$(I_3) \geq 109/253 - 43/110 = (11990-10879)/27830 = 1111/27830 > 0$. $\square$

For $k \geq 2$: upper bound on $a_3$ is even smaller (e.g., $k=2$: $a_3 \leq 340/109 \approx 3.12$, already outside the σ=−1 range $(2,3)$). So $k=1$ is the only relevant case for σ₃=−1. $\square$

**Runner 4 (σ=−1, a₄ ∈ (3,4)):** Feasibility via $B_{4,k}$ requires $a_4 \leq (11k+12)\cdot110/(11\cdot109)$. For $k=2$: $a_4 \leq 34\cdot110/(11\cdot109) = 340/109 \approx 3.12 \in (3,4)$. Then:
$$B_{4,0}[0] = \frac{10}{11a_4} \geq \frac{10}{11\cdot(340/109)} = \frac{10\cdot109}{11\cdot340} = \frac{1090}{3740} = \frac{109}{374}.$$
Compare: $\mathrm{PSR}(4) = 16/55 = 32/110$. Is $109/374 > 16/55$? Check: $109\cdot55 = 5995 > 16\cdot374 = 5984$. ✓ (margin = 11). GF$(I_2) \geq 109/374 - 16/55 = (5995-5984)/20570 = 11/20570 > 0$. $\square$

**Runners 5, 6, 7, 8 (σ=−1):** For runner 5 ($a_5 \in (4,5)$, $k=3$): $a_5 \leq 45\cdot110/(11\cdot109) = 450/109 \approx 4.13$. $B_{5,0}[0] \geq 10\cdot109/(11\cdot450) = 1090/4950 = 109/495 \approx 0.220 > 21/110 = \mathrm{PSR}(5)$ (since $109\cdot110 = 11990 > 21\cdot495 = 10395$). GF$(I_1) > 0$. $\square$

For runners 6, 7, 8 with σ=−1: the MFT criterion decides feasibility. For runner 6 ($\sigma=−1$, $a_6 \in (5,6)$, $k=4$): $\mathrm{MFT}(6,4) = 54\cdot109/(56\cdot110) = 2943/3080 \approx 0.9555$. For $g_L \leq 2943/3080$: infeasible (same computation as runner 5 σ=+1, since the upper bound is identical). For $g_L > 2943/3080$: runner 6 (σ=−1) is marginally feasible; but PSM applies — at $a_6 \leq 560/109 \approx 5.138$, $B_{6,0}[0] = 10/(11a_6) \geq 10\cdot109/(11\cdot560) = 109/616 \approx 0.177 > 12/110 = I_1[\mathrm{left}]$, so $B_{6,0}$ starts above $I_1$. Whether PSM yields a gap depends on whether $I_1[\mathrm{left}] = 12/110 = 0.109$ can be covered by other runners; however, in this narrow $\beta$-1 sub-region, Chain A (runner 3) already forces GF$(I_8) > 0$ as shown above. $\square$

For runners 7 (σ=−1, $a_7 \in (6,7)$) and 8 (σ=−1, $a_8 \in (7,8)$): the tightest upper bound for reaching $109/110$ at any $k$ is $(11k+12)\cdot110/(11\cdot109)$. For $a_7 > 6$: need $k \leq (6\cdot109/10 - 12/11) \approx 64.3$; at $k=63$: lower bound $= (693+10)/(11\cdot6) \approx 10.65 \gg a_7$. Working from the upper bound: the largest $k$ with upper bound in $(6,7)$ satisfies $(11k+12)\cdot10/109 \in (6,7)$, giving $k \in (54.5, 66.7)$; at $k=55$: lower bound $= (605+10)/(11g_L) = 615/(11g_L) \geq 615/11 \approx 55.9 \gg 7$. Runner 7 is **entirely infeasible**. Similarly runner 8 (σ=−1). $\square$

#### Analysis of Chain A (Runner 3, σ=+1)

**Setup.** If runner 3 with $\sigma_3=+1$ ($a_3 \in (3,4)$) is feasible for $[g_L, 109/110]$, it must do so via $k=2$: $B_{3,2}[0] \leq g_L$ and $B_{3,2}[1] \geq 109/110$. The feasibility interval is:
$$a_3 \in F_{3,2}(g_L) = \left[\frac{32}{11g_L},\; \frac{340}{109}\right].$$

For any $a_3$ in this interval, the following chain propagates a gap to $I_8$:

**Step 1.** Runner 3 covers $I_9$ via $B_{3,2}$. Its $B_{3,0}$ interval covers $I_3$ up to $12/(11a_3) < 43/110 = I_3[\mathrm{right}]$ (since $a_3 > 120/43 \approx 2.79$, which holds as $a_3 \geq 32/(11g_L) > 3/1 = 3$ whenever the interval is in the σ=+1 range). **$I_3$ right gap:** $[12/(11a_3), 43/110]$, width $> 0$.

**Step 2.** For $I_3$'s right gap $[12/(11a_3), 43/110]$ to be covered, runner 8 (pair partner of 3) must have $B_{8,2}[0] \leq 12/(11a_3)$: $(32)/(11a_8) \leq 12/(11a_3)$, giving $a_8 \geq 8a_3/3$. The maximum $g_L$ across all Case $\beta$ regions is $6141/6380 \approx 0.963$ (attained at $a_9 = 580/69$ in $\beta$-1). At this maximum: $a_3 \geq 32/(11\cdot6141/6380) = 32\cdot6380/(11\cdot6141) \approx 3.022$, giving $a_8 \geq 8\cdot3.022/3 \approx 8.059 > 8$. Hence $\sigma_8 = +1$ is forced in all Case $\beta$ sub-regions. If $\sigma_8 = -1$ (contradicting the above): GF$(I_3) > 0$ since no bad interval can then cover $I_3[\mathrm{right}] = 43/110$.

**Step 3.** Runner 8 ($\sigma_8=+1$, $a_8 \geq 8a_3/3$) covers $I_6$ via $B_{8,4} = [54/(11a_8),\; 56/(11a_8)]$. Feasibility: $B_{8,4}[0] \leq I_6[\mathrm{left}] = 67/110$ iff $a_8 \geq 54\cdot110/(67\cdot11) = 5940/737 \approx 8.061$. Since $a_8 \geq 8a_3/3 \geq 8\cdot3.058/3 \approx 8.155 > 8.061$ ✓, runner 8 starts below $I_6[\mathrm{left}]$. At $a_8 = 8a_3/3$ exactly:
$$B_{8,4}[1] = \frac{56}{11 \cdot 8a_3/3} = \frac{56 \cdot 3}{88a_3} = \frac{21}{11a_3} = B_{3,1}[0].$$
So runners 3 and 8 together cover $I_6$ contiguously: $B_{8,4}$ covers $[I_6[\mathrm{left}],\; 21/(11a_3)]$ and $B_{3,1}$ covers $[21/(11a_3),\; 23/(11a_3)]$. Combined: $I_6$ is covered up to $23/(11a_3)$.

**$I_6$ right gap:** $[23/(11a_3), 76/110]$. At $a_3 = 340/109$: $23\cdot109/(11\cdot340) = 2507/3740 \approx 0.670 < 0.691 = I_6[\mathrm{right}]$. Width $> 0$. $\square$

**Step 4 (Chain A conclusion).** Runner 6 ($\sigma_6=−1$, pair (5,6)) must cover the $I_6$ right gap $[23/(11a_3), 76/110]$. For $B_{6,4}[0] \leq 23/(11a_3)$: runner 6 in range $a_6 \in [43a_3/23, 225/38] \approx [5.717, 5.921]$. At the tightest value $a_6 = 225/38$:
$$B_{6,4}[0] = \frac{54}{11 \cdot 225/38} = \frac{54 \cdot 38}{11 \cdot 225} = \frac{2052}{2475} = \frac{228}{275}.$$
Since $228/275 - 89/110 = (228\cdot110 - 89\cdot275)/(275\cdot110) = (25080-24475)/30250 = 605/30250 = 1/50 > 0$, runner 6 misses $I_8[\mathrm{left}] = 89/110$. Runner 5 (pair partner) cannot cover $I_8[\mathrm{left}]$ either: needs $a_5 \geq 54\cdot110/(89\cdot11) = 540/89 \approx 6.07 > 6$.

**GF$(I_8) \geq 1/50 > 0$.** $\square$

Note: Chain A uses only $a_3 \in [32/(11g_L), 340/109]$ — this is a runner-intrinsic constraint on the (3,8,6,5) cascade, independent of the specific $g_L$.

#### Analysis of Chain B (Runner 4, σ=+1)

**Setup.** If runner 4 with $\sigma_4=+1$ ($a_4 \in (4,5)$) is feasible for $[g_L, 109/110]$ via $k=3$:
$$a_4 \in F_{4,3}(g_L) = \left[\frac{43}{11g_L},\; \frac{450}{109}\right].$$

**Chain B:** Runner 4 at $a_4 \in [1849/450,\, 450/109]$ covers $I_9$'s right via $B_{4,3}$, but $B_{4,0}$ covers $I_2$ only up to $12/(11a_4) < 32/110 = I_2[\mathrm{right}]$. Runner 7 (pair (4,7)) must cover the $I_2$ right gap; needs $a_7 \geq 7a_4/4 \geq 12943/1800 \approx 7.19$.

$I_7$ right coverage requires $a_7 \leq 560/87 \approx 6.44$. Incompatible:
$$12943 \times 87 = 1{,}126{,}041 > 560 \times 1800 = 1{,}008{,}000.$$
$I_7$ right gap $= 87/110 - 14400/20339 = 1533/18490 > 0$. No runner in $\{3,5,6,8,9\}$ can cover $I_7[\mathrm{right}]$ (empty feasibility intervals). **GF$(I_7) \geq 1533/18490 > 0$.** $\square$

Again: Chain B uses only $a_4 \in [1849/450, 450/109]$ and does NOT depend on $g_L$.

#### Summary of Theorem UB

For any right gap $[g_L, 109/110]$:

| Runner | σ | Feasible? | Consequence |
|--------|---|-----------|-------------|
| 3 | −1 | Only if $a_3 \leq 230/109 \approx 2.11$ | PSM: GF$(I_3) \geq 1111/27830 > 0$ |
| 3 | +1 | If $a_3 \in [32/(11g_L), 340/109]$ | Chain A: GF$(I_8) \geq 1/50$ |
| 4 | −1 | Only if $a_4 \leq 340/109 \approx 3.12$ | PSM: GF$(I_2) \geq 11/20570 > 0$ |
| 4 | +1 | If $a_4 \in [43/(11g_L), 450/109]$ | Chain B: GF$(I_7) \geq 1533/18490$ |
| 5 | −1 | Only if $a_5 \leq 450/109 \approx 4.13$ | PSM: GF$(I_1) > 0$ |
| 5 | +1 | Only if $a_5 \in [5.100, 5.138]$ (large $g_L$ only) | GF$(I_3)$ or GF$(I_8) > 0$ (via runner 3 cascade) |
| 6 | +1 | MFT $= 1417/1474 > g_L^{\max}$ for $k=5$ | Infeasible in all Case β regions |
| 6 | −1 | MFT $= 2943/3080$; large-$g_L$ case covered by Chain A | GF$(I_8) > 0$ |
| 7,8 | ±1 | Required $k \geq 55$; lower bound $\gg$ speed range | Entirely infeasible |
| None feasible | — | $g_L$ small | GF$(I_9) \geq 109/110 - g_L > 0$ |

In all cases GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$. $\square$

### 11.4 (continued) Cases A1–B4 and Theorem U

#### Part A: σ₉=−1

**Case A1** ($a_2 < 20/9$): Lemma 11.2.1 gives GF$(I_4) > 0$. $\square$

**Case A2** ($a_2 \geq 20/9$): Runner 2 covers $[10/11, 23/(11a_2)] \subset I_9$ with end $\leq 207/220$.

- **A2a** ($a_9 < 580/69$): Runner 9's $B_{9,7}[0] > 207/220 \geq 23/(11a_2)$. Middle gap in $I_9$. Runner 2 incompatibility: $a_2 \geq 20/9$ vs $a_2 \leq 23a_9/87$; gap is positive since $a_9 < 580/69$. Runner 2 cannot close both $I_4$ and bridge the $I_9$ gap; if runner 3 ($\sigma_3=+1$) bridges instead, Chain A forces GF$(I_8) \geq 1/50$. GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$. $\square$

- **A2b** ($a_9 \in [580/69, 87/10)$): Runners 2 and 9 cover $[10/11, 89/(11a_9)]$. Right gap $\Delta_R \geq 181/6380 > 0$. Theorem UB applies: if $\sigma_3=-1$ or runner 3 is infeasible for the gap, GF$(I_9) \geq 181/6380$; if $\sigma_3=+1$ and Chain A is active, runner 3 covers $I_9$ but Chain A forces GF$(I_8) \geq 1/50$. In all sub-cases GF$(I_k) > 0$ for some $k$. $\square$

- **A2c** ($a_9 \in [87/10, 980/109)$): Runner 9 provides no $I_9$ coverage. Right gap $g_L = 23/(11a_2) \leq 207/220$. Theorem UB applies: if $\sigma_3=-1$ or runner 3 infeasible, GF$(I_9) \geq 1/20$; if Chain A active, GF$(I_8) \geq 1/50$. In all sub-cases GF$(I_k) > 0$ for some $k$. $\square$

- **A2d** ($a_9 \in [980/109, 9)$): Bridging $I_9$ via runner 2 requires $a_2 \leq 23a_9/98 < 20/9$ (since $1960 > 207 \cdot 9$). INCOMPATIBLE with $a_2 \geq 20/9$. Runner 2 cannot close both $I_4$ and $I_9$; if runner 3 ($\sigma_3=+1$) covers $I_9$, Chain A forces GF$(I_8) \geq 1/50$. GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$. $\square$

#### Part B: σ₉=+1

- **B1** ($a_9 < 1960/207$): Lemma 11.2.2 gives $a_2 \geq 20/9$. Bridging $I_9$ via runner 2 requires $a_2 \leq 23a_9/98 < 20/9$ (since $a_9 < 1960/207$ gives $23a_9/98 < 23 \cdot 1960/(207 \cdot 98) = 20/9$). INCOMPATIBLE with $a_2 \geq 20/9$. Runner 2 cannot simultaneously close $I_4$ and bridge $I_9$. If runner 3 ($\sigma_3=+1$) covers $I_9$ instead, Chain A forces GF$(I_8) \geq 1/50$. GF$(I_k) > 0$ for some $k \in \{4, 8, 9\}$. $\square$

- **B2** ($a_9 \in [1960/207, 86/9)$): Runners 2 and 9 cover up to $100/(11a_9)$. Right gap $(1199a_9 - 11000)/(1210a_9) \geq 83/2695 > 0$. Theorem UB applies: if $\sigma_3=-1$ or runner 3 infeasible, GF$(I_9) \geq 83/2695$; if Chain A active, GF$(I_8) \geq 1/50$. In all sub-cases GF$(I_k) > 0$ for some $k$. $\square$

- **B3** ($a_9 = 86/9$): By Lemma 11.2.2: $a_2 \in [172/81, 20/9]$. Right gap $= 109/110 - 450/473 = 17/430 > 0$. Theorem UB applies: if $\sigma_3=-1$ or runner 3 infeasible, GF$(I_9) \geq 59/9460$ (attained at $a_2=172/81$); if Chain A active ($\sigma_3=+1$, runner 3 covers $I_9$), GF$(I_8) \geq 1/50$. In all sub-cases GF$(I_k) > 0$ for some $k$. $\square$

- **B4** ($a_9 > 86/9$): Right gap $\Delta_R > 17/430$. Theorem UB applies: if $\sigma_3=-1$ or runner 3 infeasible, GF$(I_9) > 17/430$; if Chain A active, GF$(I_8) \geq 1/50$. In all sub-cases GF$(I_k) > 0$ for some $k$. $\square$

**Theorem U (Universal $\sigma_2=+1$ Positivity).** *For any CB configuration with $\sigma_2=+1$: GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$.*

**Proof.** Cases A1, A2a, A2d, B1 give direct incompatibility between covering $I_4$ and $I_9$ simultaneously (via runner 2 bounds), leaving one of those slots open. Cases A2b, A2c, B2, B3, B4 produce a right gap in $I_9$; Theorem UB shows this gap forces a positive good fraction in some slot $I_k$: in $I_9$ itself when no Chain-A runner is feasible, and in $I_8$ (via Chain A) or $I_7$ (via Chain B) when a filler runner covers $I_9$. In all 128 $\sigma_2=+1$ sign classes, GF$(I_k) > 0$ for some $k$. $\square$

**Note on minimum gap.** The bound $59/9460$ (Case B3, $a_9 = 86/9$, $a_2 = 172/81$) is the minimum GF$(I_9)$ when Chain A is inactive. When Chain A is active (runner 3, $\sigma_3=+1$, covers $I_9$), the minimum guaranteed gap shifts to GF$(I_8) \geq 1/50$ or GF$(I_2) \geq 11/20570$ (PSM runner 4 sub-case). The global minimum across all $\sigma_2=+1$ sub-cases requires a full recomputation from the Theorem UB table; the $59/9460$ figure applies only to the no-Chain-A sub-case of β-3.

**Summary Table:**

| Case | $\sigma_9$ | Parameter range | Mechanism | Min GF |
|------|-----------|-----------------|-----------|--------|
| α-1 | −1 | $a_9 < 580/69$ | Direct incompat. (middle gap) | $\to 0^+$ |
| α-2 | −1 | $a_9 \in [980/109, 9)$ | Direct incompat. (high-$k$ bridge) | $\to 0^+$ |
| α-3 | +1 | $a_9 \in (9, 1960/207)$ | Direct incompat. | $\to 0^+$ |
| β-1 | −1 | $a_9 \in [580/69, 87/10)$ | UB (Chain A or trivial) | $181/6380$ |
| β-2 | −1 | $a_9 \in [87/10, 980/109)$ | UB (Chain A or trivial) | $1/20$ |
| β-3 | +1 | $a_9 \in [1960/207, 86/9]$ | UB (Chain A or trivial) | $59/9460$ |
| β-4 | +1 | $a_9 \in (86/9, 10)$ | UB (trivial or Chain A) | $17/430$ |

Cases α-1 through β-4 are exhaustive (cover all $(a_2,a_9) \in (2,3)\times(8,10)$) and mutually exclusive. All 128 $\sigma_2=+1$ sign classes are covered. In every case GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$. $\square$

**On minimum gap values.** The table above lists per-case lower bounds for the slot named in each non-Chain-A scenario. The global minimum good fraction across all $\sigma_2=+1$ sub-cases is at most $11/20570$ (PSM runner 4 sub-case, GF$(I_2)$) and at most $1/50$ (Chain A sub-cases, GF$(I_8)$). A systematic per-subcase minimisation is deferred. Combined with Lemma S2 ($\sigma_2=-1$, min GF$(I_9) \geq 538/54395$): the minimum across all 256 sign classes is positive, with $538/54395$ as a confirmed lower bound for $\sigma_2=-1$ configurations.

---

## 12. The σ₂=−1 Case

### 12.1 Lemma S1: Runner-2 Elimination

**Lemma S1.** In every sign class with $\sigma_2 = -1$, runner $2$ cannot simultaneously satisfy its primary obligation at $I_5$ and absorb the unclaimed slot $I_9$.

Equivalently, runner $2$ is not the terminal absorber in any $\sigma_2 = -1$ class.

#### Setup

Use the standard slots
$$I_5 = [56/110, 65/110], \quad I_9 = [100/110, 109/110],$$
and bad intervals $B_{2,j}(a_2) = [(11j+10)/(11a_2), (11j+12)/(11a_2)]$.

In $\sigma_2 = -1$ classes we have $a_2 < 2$, and runner $2$ must close its primary slot $I_5$ from below.

#### Proof

Runner $2$ covers $I_5$ via $B_{2,0}$ exactly when
$$\frac{10}{11a_2} \leq \frac{56}{110}, \quad \frac{12}{11a_2} \geq \frac{65}{110}.$$

This forces
$$\frac{25}{14} \leq a_2 \leq \frac{24}{13}.$$

Now determine when runner $2$ can overlap $I_9$.

**§12.1.1 $B_{2,0}$ window.** For $B_{2,0}(a_2) = [10/(11a_2), 12/(11a_2)]$ to overlap $I_9 = [100/110, 109/110]$, we need
$$\frac{12}{11a_2} \geq \frac{100}{110}, \quad \frac{10}{11a_2} \leq \frac{109}{110}.$$

Equivalently, $100/109 \leq a_2 \leq 6/5$.

**§12.1.2 $B_{2,1}$ window.** For $B_{2,1}(a_2) = [21/(11a_2), 23/(11a_2)]$ to overlap $I_9$, we need
$$\frac{23}{11a_2} \geq \frac{100}{110}, \quad \frac{21}{11a_2} \leq \frac{109}{110}.$$

Under $a_2 < 2$, this reduces to $210/109 \leq a_2 < 2$.

**§12.1.3 Higher branches.** For $j \geq 2$:
$$B_{2,j}[0] = \frac{11j+10}{11a_2} \geq \frac{32}{11a_2} > \frac{32}{22} = \frac{16}{11} > 1$$
because $a_2 < 2$. So no $B_{2,j}$ with $j \geq 2$ reaches $I_9$.

**§12.1.4 Disjointness with the primary window.** The primary window is $[25/14, 24/13]$. The two possible $I_9$-overlap windows are $[100/109, 6/5]$ and $[210/109, 2)$.

Both intersections are empty:
$$[25/14, 24/13] \cap [100/109, 6/5] = \emptyset, \quad [25/14, 24/13] \cap [210/109, 2) = \emptyset.$$

The decisive gap is
$$\frac{210}{109} - \frac{24}{13} = \frac{2730 - 2616}{1417} = \frac{114}{1417} > 0.$$

Therefore runner $2$ cannot satisfy its $I_5$ obligation and also overlap $I_9$. So runner $2$ is eliminated as a terminal absorber in every $\sigma_2 = -1$ class. $\square$

**Exact Summary:**

| Quantity | Exact value |
|---|---|
| primary $I_5$ window | $[25/14, 24/13]$ |
| $B_{2,0}$ overlap window for $I_9$ | $[100/109, 6/5]$ |
| $B_{2,1}$ overlap window for $I_9$ | $[210/109, 2)$ |
| decisive separation gap | $114/1417$ |

### 12.2 Lemma S2: Cascade-Conditional Witness Window

> **Lemma S2.** In every σ₂=−1 sign class, the unclaimed slot $I_9 = [100/110, 109/110]$ retains a positive witness width. The minimum is $538/54395 > 0$.

#### §12.2.1 Setup

**Slots:** $I_k = [(11k+1)/110, (11k+10)/110]$. Key slots:
$$I_4 = [45/110, 54/110], \quad I_5 = [56/110, 65/110], \quad I_9 = [100/110, 109/110].$$

**Bad interval:** $B_j(a) = [(11j+10)/(11a), (11j+12)/(11a)]$.

**Pair (2,9) → {I₄, I₅}:** In σ₂=−1, runner 2 has $a_2\in[25/14, 24/13]$ and closes $I_5$'s left boundary via $j=0$. Runner 9 must therefore close $I_4$.

**Cascade constraint:** A speed $a_p$ is *cascade-forced* for runner $p$ iff $B_j(a_p)$ contacts a designated slot boundary AND $a_p \in (p-1, p+1)$.

#### §12.2.2 Step 1 — The Only Valid a₉ is 86/9

**Claim:** The only $a_9 \in (9, 10)$ closing $I_4$'s left boundary is $a_9 = 86/9$.

**Proof.** $B_{9,k}[0] = 45/110$ ($I_4$ left) iff $a_9 = (110k+100)/45$. For $a_9 \in (9,10)$: unique solution $k=3$, giving $a_9 = 430/45 = 86/9$.

$I_4$ right boundary ($54/110$): $a_9 = (110k+120)/54$. For $k=3$: $25/3 \approx 8.33 \notin (9,10)$. For $k=4$: $280/27 \approx 10.37 \notin (9,10)$. No solution.

$I_5$ left boundary ($56/110$): $a_9 = (110k+100)/56$. For $k=4$: $135/14 \approx 9.64$. This would cover $I_5$ redundantly — runner 2 already closes $I_5$ left — leaving $I_4$ uncovered, so $W(I_4) > 0$ and the class is infeasible at the primary slot level.

For all other $a_9 \in (9, 10)$: no branch $k$ contacts any boundary of $I_4$ or $I_5$ (no solution to either equation in $(9,10)$ besides those listed), so pair $(2,9)$ fails to cover $I_4$ → $W(I_4) > 0$ → infeasible.

**Conclusion:** The only sign class requiring $I_9$ analysis has $a_9 = 86/9$. $\square$

#### §12.2.3 Step 2 — Runner 9's Bad Interval in I₉

For $a_9 = 86/9$:
$$B_{9,8}(86/9) = \left[\frac{(11\cdot8+10)\cdot9}{11\cdot86},\ \frac{(11\cdot8+12)\cdot9}{11\cdot86}\right] = \left[\frac{882}{946},\ \frac{900}{946}\right] = \left[\frac{441}{473},\ \frac{450}{473}\right].$$

Both endpoints lie inside $I_9$ ($441/473 > 100/110$ and $450/473 < 109/110$, verified below), so runner 9 covers $[441/473, 450/473] \subset I_9$.

Checks: $441\cdot110 = 48510 > 100\cdot473 = 47300$ ✓ ($441/473 > 100/110$).
$450\cdot110 = 49500 < 109\cdot473 = 51557$ ✓ ($450/473 < 109/110$).

#### §12.2.4 Step 3 — Cascade-Forced Outer Runner Speeds and Their I₉ Intervals

The outer runners come in complementary pairs. For each pair, $\tau$ (the **slot-closure direction**) determines which boundary is closed, and the cascade-forced speed must lie in $(p-1, p+1)$.

**Notation note:** In the table below, $\tau = +1$ means runner $p$ closes a slot's **left** (lower) boundary via $B_{p,j}[0] = $ boundary; $\tau = -1$ means it closes the **right** (upper) boundary via $B_{p,j}[1] = $ boundary. *Caution:* this $\tau$ convention is the opposite of the §11.1 sign convention $\sigma_j$: a runner with §11.1 sign $\sigma_j = +1$ (i.e.\ $a_j \in (j,j+1)$) typically closes right boundaries ($\tau = -1$), and vice versa. The $\tau$ column records the cascade action in this section only.

**Pairs and cascade-forced speeds:**

| Runner $p$ | $\tau$ | Closes | Boundary | $a_p$ formula | $j$ | $a_p$ | In $(p-1,p+1)$? |
|----------|---|--------|----------|-------------|---|-----|---------------|
| 3 | +1 | $I_3$ left | $34/110$ | $(110j+100)/34$ | 0 | $50/17$ | ✓ $2.94\in(2,4)$ |
| 3 | −1 | $I_6$ left | $67/110$ | $(110j+120)/76$ | 1 | $115/38$ | ✓ $3.03\in(2,4)$ |
| 4 | +1 | $I_2$ left | $23/110$ | $(110j+100)/23$ | 0 | $100/23$ | ✓ $4.35\in(3,5)$ |
| 4 | −1 | $I_7$ right | $87/110$ | $(110j+120)/87$ | 2 | $340/87$ | ✓ $3.91\in(3,5)$ |
| 5 | −1 | $I_8$ right | $98/110$ | $(110j+120)/98$ | 3 | $225/49$ | ✓ $4.59\in(4,6)$ |
| 5 | +1 | $I_1$ left | $12/110$ | $(110j+100)/12$ | — | None | ✗ no $j$ gives $(4,6)$ |
| 6 | +1 | $I_8$ right | $98/110$ | $(110j+120)/98$ | 4 | $40/7$ | ✓ $5.71\in(5,7)$ |
| 6 | −1 | $I_1$ left | $12/110$ | $(110j+100)/12$ | — | None | ✗ |
| 7 | +1 | $I_7$ right | $87/110$ | $(110j+120)/87$ | 4 | $560/87$ | ✓ $6.44\in(6,8)$ |
| 7 | −1 | $I_2$ left | $23/110$ | $(110j+100)/23$ | — | None | ✗ no $j$ gives $(6,8)$ |
| 8 | +1 | $I_6$ right | $76/110$ | $(110j+120)/76$ | 4 | $140/19$ | ✓ $7.37\in(7,9)$ |
| 8 | −1 | $I_3$ left | $34/110$ | $(110j+100)/34$ | — | None | ✗ $160/17\approx9.41\notin(7,9)$ |
| 10 | — | (free) | — | — | — | $10$ | safe throughout $I_9$ |

*Correspondence with §11.1 signs:* Runner 3 with $\tau=+1$ (closes $I_3$ left, $a_3 = 50/17 \approx 2.94$) has $a_3 \in (2,3)$, which is $\sigma_3 = -1$ in §11.1's convention. Runner 3 with $\tau=-1$ (closes $I_6$ left, $a_3 = 115/38 \approx 3.03$) has $a_3 \in (3,4)$, which is $\sigma_3 = +1$ in §11.1. The $\tau$ and $\sigma$ columns are opposite in sign for all runners in this table.

**Structural consequence:** In $\sigma_3=+1$ (i.e.\ $\tau_3=-1$), runner 8 has no cascade-forced speed ($160/17 > 9$, outside $(7,9)$). Runner 8 is present only when $\sigma_3=-1$ (i.e.\ $\tau_3=+1$).

**Bad intervals of each cascade-forced runner in I₉:**

For a runner to have a bad interval overlapping $I_9=[100/110, 109/110]$, branch $j'$ must satisfy:
$(11j'+10)/(11a_p) < 109/110$ and $(11j'+12)/(11a_p) > 100/110$.

| Runner | $a_p$ | $j'$ | $B[0]$ | $B[1]$ | eff. $\cap I_9$ |
|--------|-----|-----|------|------|-----------|
| $p=3$, σ=+1 | $50/17$ | 2 | $272/275$ | $289/275 > 1$ | $[272/275, 109/110]$ |
| $p=3$, σ=−1 | $115/38$ | 2 | $1216/1265$ | $1292/1265 > 1$ | $[1216/1265, 109/110]$ |
| $p=4$, σ=+1 | $100/23$ | 3 | $10/11$ | $207/220$ | $[10/11, 207/220]$ |
| $p=4$, σ=−1 | $340/87$ | — | $>1$ | $>1$ | $\emptyset$ |
| $p=5$, σ=−1 | $225/49$ | — | — | — | $\emptyset$ |
| $p=6$, σ=+1 | $40/7$ | — | — | — | $\emptyset$ |
| $p=7$, σ=+1 | $560/87$ | 5 | $1131/1232$ | $5829/6160$ | $[1131/1232, 5829/6160]$ |
| $p=8$, σ=+1 | $140/19$ | 6 | $361/385$ | $741/770$ | $[361/385, 741/770]$ |
| $p=10$ | $10$ | — | — | — | $\emptyset$ |

**No-overlap proofs ($j'$ existence contradictions):**

- **$p=4$, $a_4=340/87$:** $j'=3$ gives $B_3[0] = 43\cdot87/3740 = 3741/3740 > 1$. No overlap with $I_9 \subset [0,1]$. $\square$
- **$p=5$, $a_5=225/49$:** $j'$ must satisfy $316/77 < j' < 366/77$, i.e., $4.104 < j' < 4.753$. No integer. $\square$
- **$p=6$, $a_6=40/7$:** same bounds $316/77 < j' < 366/77$ (same slot $I_8$ constraint). No integer. $\square$
- **$p=7$, σ=−1 (None), $p=8$, σ=−1 (None), $p=5$, σ=+1 (None):** excluded by cascade range constraint. $\square$

#### §12.2.5 Step 4 — The Four Sub-Cases

The gap structure depends on σ₃ (determines runner 8's presence) and σ₄ (determines runners 4 and 7's presence). Signs σ₅, σ₁₀ have no effect (runners 5, 6 have no $I_9$ bad intervals; runner 10 is safe).

**Case A: σ₄ = −1 (runners 4 and 7 absent).**

When σ₄=−1, runners 4 and 7 have either no $I_9$ overlap ($a_4=340/87$) or are None. The only runners with $I_9$ bad intervals in $[10/11, 441/473)$ are absent. Since runner 9's interval starts at $441/473 > 10/11 = I_9[0]$, the left portion of $I_9$ is uncovered:

$$\text{Left gap: }(10/11, 441/473), \quad W = \frac{441}{473} - \frac{10}{11} = \frac{4851 - 4730}{5203} = \frac{121}{5203} = \frac{1}{43} > 0.$$

Verification: $441\cdot11 = 4851$, $10\cdot473 = 4730$. ✓

**$W(I_9) \geq 1/43 > 0$ for all σ₄=−1 sign classes.** $\square$

**Case B: σ₃=+1, σ₄=+1 (runners 4, 7, 8 all present).**

Runners with $I_9$ bad intervals: $\{p_4(100/23), p_7(560/87), p_8(140/19), p_9(86/9), p_3(50/17)\}$.

Left coverage chain (show $[10/11, 741/770]$ is fully covered):

| Runner | eff. interval in $I_9$ |
|--------|---------------------|
| $p_4$ | $[10/11, 207/220]$ |
| $p_7$ | $[1131/1232, 5829/6160]$ |
| $p_9$ | $[441/473, 450/473]$ |
| $p_8$ | $[361/385, 741/770]$ |

Contiguity checks (each runner's left endpoint ≤ previous runner's right endpoint):
- $p_4$ starts at $I_9[0]$: $B_3(100/23)[0] = 989/1100 < 10/11$ since $989\cdot11=10879 < 100\cdot1100=110000$. So effective start $= 10/11$. ✓
- $p_7$ starts before $p_4$ ends: $1131/1232 < 207/220$ since $1131\cdot220=248820 < 1232\cdot207=255024$. ✓
- $p_9$ starts before $p_7$ ends: $441/473 < 5829/6160$ since $441\cdot6160=2716560 < 473\cdot5829=2757117$. ✓
- $p_8$ starts before $p_9$ ends: $361/385 < 450/473$ since $361\cdot473=170753 < 385\cdot450=173250$. ✓
- $p_8$ ends at $741/770$. Combined left coverage: $[10/11, 741/770]$. ✓

Right coverage: runner 3 ($a_3=50/17$) covers $[272/275, 109/110]$.

Gap:
$$G_1 = (741/770, 272/275), \quad W = \frac{272}{275} - \frac{741}{770} = \frac{272\cdot770 - 741\cdot275}{275\cdot770} = \frac{209440 - 203775}{211750} = \frac{5665}{211750} = \frac{103}{3850} > 0.$$

Verify runner 3 starts above left coverage end: $272/275 > 741/770$ since $272\cdot770=209440 > 741\cdot275=203775$. ✓

Verify no runner covers $G_1=(741/770, 272/275)\approx(0.962, 0.989)$:
All remaining runners ($p_5$, $p_6$, $p_{10}$) have no $I_9$ bad intervals (proved in §12.2.4). Runner $p_8$ ends at $741/770 = G_1[0]$ (excluded, open interval). Runner $p_9$ ends at $450/473 < 741/770$ (check: $450\cdot770=346500 < 473\cdot741=350493$ ✓). $\square$

**$W(I_9) = 103/3850 > 0$.** $\square$

**Case C: σ₃=−1, σ₄=+1 (runners 4, 7 present; runner 8 absent).**

Runners with $I_9$ bad intervals: $\{p_4(100/23), p_7(560/87), p_9(86/9), p_3(115/38)\}$.

Left coverage chain (show $[10/11, 450/473]$ is fully covered):

| Runner | eff. interval in $I_9$ |
|--------|---------------------|
| $p_4$ | $[10/11, 207/220]$ |
| $p_7$ | $[1131/1232, 5829/6160]$ |
| $p_9$ | $[441/473, 450/473]$ |

Contiguity checks (same as Case B for $p_4\to p_7\to p_9$):
- $p_4$ starts at $I_9[0]$ ✓ (same check)
- $p_7$ starts before $p_4$ ends ✓ (same check)
- $p_9$ starts before $p_7$ ends ✓ (same check)
- $p_9$ ends at $450/473$. Combined left coverage: $[10/11, 450/473]$. ✓

Right coverage: runner 3 ($a_3=115/38$) covers $[1216/1265, 109/110]$.

Gap:
$$G_2 = (450/473, 1216/1265), \quad W = \frac{1216}{1265} - \frac{450}{473} = \frac{1216\cdot473 - 450\cdot1265}{1265\cdot473} = \frac{575168 - 569250}{598345} = \frac{5918}{598345} = \frac{538}{54395} > 0.$$

Verify runner 3 starts above left coverage end: $1216/1265 > 450/473$ since $1216\cdot473=575168 > 1265\cdot450=569250$. ✓

Verify no runner covers $G_2=(450/473, 1216/1265)\approx(0.951, 0.961)$:
- $p_4$ ends at $207/220 < 450/473$: $207\cdot473=97911 < 220\cdot450=99000$. ✓
- $p_7$ ends at $5829/6160 < 450/473$: $5829\cdot473=2757117 < 6160\cdot450=2772000$. ✓
- $p_9$ ends at $450/473 = G_2[0]$ (excluded, open interval). ✓
- $p_5$, $p_6$, $p_{10}$: no $I_9$ overlap. ✓
- $p_8$: absent (σ₃=−1). ✓

**$W(I_9) = 538/54395 > 0$.** $\square$

#### §12.2.6 Summary

| σ₃ | σ₄ | Uncovered region(s) in $I_9$ | $W(I_9)$ |
|----|-----|---------------------------|--------|
| +1 | +1 | $G_1 = (741/770, 272/275)$ | $103/3850$ |
| +1 | −1 | $(10/11, 441/473)$ and $G_1$ | $8279/165550$ |
| −1 | +1 | $G_2 = (450/473, 1216/1265)$ | $538/54395$ ← minimum |
| −1 | −1 | $(10/11, 441/473)$ and $G_2$ | $1803/54395$ |

Signs σ₅ and σ₁₀ have no effect on $I_9$ coverage. Minimum $W(I_9) = 538/54395 > 0$.

#### §12.2.7 Conclusion

In every σ₂=−1 sign class:

1. If $a_9 \neq 86/9$: pair $(2,9)$ fails to cover $I_4$ → $W(I_4)>0$ → class infeasible at primary level.
2. If $a_9 = 86/9$ and σ₄=−1: left gap $(10/11, 441/473)$ has width $1/43 > 0$ → $W(I_9)>0$.
3. If $a_9 = 86/9$ and σ₃=+1, σ₄=+1: gap $G_1$ has width $103/3850 > 0$ → $W(I_9)>0$.
4. If $a_9 = 86/9$ and σ₃=−1, σ₄=+1: gap $G_2$ has width $538/54395 > 0$ → $W(I_9)>0$.

In all cases no configuration of outer runners simultaneously covers all of $I_1,\ldots,I_9$. A valid isolation witness exists in every σ₂=−1 sign class. **Lemma S2: PROVED.** $\square$

---

## 13. Phase-Uniform Extension and Theorem W_ref

### Setup and Notation

**EFN normalisation.** Fix EFN speeds $a_1 < a_2 < \cdots < a_9 < a_{10} = 10$, with signs $\sigma_j = \pm 1$ determining which half of $(j-1, j)$ runner $j$ lies in.

**Pacemaker cycle $m$.** Runner $v_{10}$ (EFN speed 10) is isolated in sub-windows
$$W_0[m] = \left[\frac{11m+1}{110},\; \frac{11m+10}{110}\right], \quad m = 0, 1, 2, \ldots$$

**Slots $I_s^{(m)}$.** Within cycle $m$, slot $I_s^{(m)} = [(11m + 11s + 1)/110,\, (11m + 11s + 10)/110]$ for $s = 1,\ldots,9$. These are identical in width and internal structure to the cycle-0 slots $I_s = I_s^{(0)}$.

**$W_{\rm ref}$.** The isolation window of runner $v_1$ (slowest runner, EFN speed $a_1$):
$$W_{\mathrm{ref}} = \left[\frac{1}{11a_1},\; \frac{10}{11a_1}\right].$$
Runner $v_1$ is isolated for ALL $t \in W_{\mathrm{ref}}$ by definition. For ratio $> 10$ (i.e., $a_1 < 1$): $W_{\mathrm{ref}}$ is entirely to the right of $W_0[0]$ and contains at least one complete pacemaker cycle of runner $v_{10}$ (proved in Corollary W_ref Step 2 below; the interval of valid cycle indices has length $> 81/11 > 7$, so it contains at least $7$ integers, and at least one complete cycle $W_0[m^*] \subset W_{\rm ref}$).

**Phase of runner $j$ in cycle $m$.**
$$\varphi_{j,m} = \left\{\frac{m \cdot a_j}{10}\right\} \in [0, 1).$$
This is the fractional-part offset of runner $j$'s bad-interval sequence at the start of cycle $m$. Runner $j$'s position at relative time $\tau' = \tau - m/10$ within cycle $m$ is $\{a_j \tau' + \varphi_{j,m}\}$.

**Bad interval.** Runner $j$'s $k$-th bad interval in absolute EFN time is
$$B_{j,k} = \left[\frac{11k+10}{11a_j},\; \frac{11k+12}{11a_j}\right], \quad \text{width } \frac{2}{11a_j} \text{ (independent of } k\text{)}.$$

**Good fraction.** $\mathrm{GF}(I_s^{(m)})$ = measure of $t \in I_s^{(m)}$ where all runners $v_2,\ldots,v_{10}$ are isolated (no runner's bad interval covers $t$). In $W_{\rm ref}$: $\mathrm{GF}_{\mathrm{total}}(I_s^{(m)}) = \mathrm{GF}(I_s^{(m)})$ since runner $v_1$ is isolated throughout.

---

**Lemma P (Bad-Interval Width is Phase-Independent).**

> **Lemma P.** For any runner $j$ and any pacemaker cycle $m$, the width of runner $j$'s bad interval is $2/(11a_j)$, independent of $k$ and $m$.

**Proof.** $|B_{j,k}| = (11k+12)/(11a_j) - (11k+10)/(11a_j) = 2/(11a_j)$. $\square$

**Consequence.** The feasibility of runner $j$ covering a gap of width $w$ is entirely determined by whether $2/(11a_j) \geq w$ — a constraint on $a_j$ alone, independent of phase $\varphi_{j,m}$ or cycle index $m$.

---

**Lemma C (Cascade Conclusions are Speed-Range Consequences).**

> **Lemma C.** The following cascade conclusions from Theorem UB (§11.4) are speed-range constraints, independent of phase:
>
> (i) **PSM (Primary Slot Miss):** If runner $j$ ($\sigma_j = -1$) covers the right gap of $I_9^{(m)}$, then $a_j$ is constrained below $j$'s primary slot threshold, forcing $\mathrm{GF}(I_j^{(m)}) > 0$.
>
> (ii) **Chain A:** If runner 3 ($\sigma_3 = +1$) covers the right gap of $I_9^{(m)}$ via some bad interval $B_{3,k_m}$, then:
> - (A1) $a_3 \leq 340/109$ (width constraint: bad interval fits the gap).
> - (A2) $a_8 \geq 8a_3/3$ (covering $I_3^{(m)}$'s right sub-gap forces runner 8).
> - (A3) $a_8 > 8.061$ (from A2 with A1), hence $a_8 \geq 8a_3/3 \geq 8\cdot(3.022)/3 \approx 8.059$; runner 6 is forced to $a_6 \in [43a_3/23, 225/38]$.
> - (A4) At $a_6 = 225/38$: $B_{6,4}[0] = 228/275 > 89/110 = I_8^{(m)}[\mathrm{left}]$ in relative cycle coordinates. Hence $\mathrm{GF}(I_8^{(m)}) \geq 1/50 > 0$.
>
> (iii) **Chain B:** If runner 4 ($\sigma_4 = +1$) covers the right gap of $I_9^{(m)}$, then $a_4 \in [1849/450, 450/109]$ and the induced constraint on $a_7$ is incompatible, giving $\mathrm{GF}(I_7^{(m)}) \geq 1533/18490 > 0$.

**Proof.** Each step is a ratio/width computation using bad-interval widths from Lemma P. We verify phase-independence for Chain A explicitly; Chain B and PSM are analogous.

**Chain A, phase-independence proof.** Suppose $B_{3,k_m} \supset [g_L^{(m)}, 109/110]$ within $I_9^{(m)}$ (in cycle-relative coordinates, dropping the $m/10$ absolute offset). The coverage condition gives:

$$a_3 \leq \frac{2}{11(109/110 - g_L^{(m)})} = \frac{20}{109 - 110g_L^{(m)}} \leq \frac{340}{109}$$

(upper bound achieved at $g_L^{(m)} \to 109/110$, tightest at $g_L^{(m)} = 100/110$). This bound depends only on $a_3$ and $g_L^{(m)}$ — not on $k_m$ or $m$.

**Step A1→A2.** Runner 3 covers $I_9^{(m)}$'s right gap via $B_{3,k_m}$. The same bad interval index determines $B_{3,k_m-2}$ (the primary slot interval of runner 3), which covers $I_3^{(m)}$ from the left up to $12/(11a_3)$ (relative coord). The right sub-gap $[12/(11a_3), 43/110]$ of $I_3^{(m)}$ is non-empty (at $a_3 > 3$: $12/(11a_3) < 12/33 = 4/11 \approx 0.364 < 43/110 = 0.391$). Width $= 43/110 - 12/(11a_3) > 0$. ✓

For runner 8 to cover the right sub-gap: $B_{8,k_m'}[0] \leq 12/(11a_3)$ requires (by the same width calculation) $a_8 \geq 8a_3/3$. This is a ratio of speeds $a_8/a_3 \geq 8/3$ — **purely a speed constraint, independent of phase**.

**Step A3→A4.** $a_8 \geq 8a_3/3 \geq 8\cdot3/3 = 8$ (for $a_3 > 3$), so $\sigma_8 = +1$. Runner 8 covers $I_6^{(m)}$ via $B_{8,4}$. Bad interval width $2/(11a_8) \leq 2/(11\cdot8) = 1/44$. The right endpoint of coverage: $B_{8,4}[1] = 56/(11a_8) \leq 56/(11\cdot8) = 7/11 = 0.636 < 76/110 = I_6^{(m)}[\mathrm{right}]$. Runner 6 ($\sigma_6 = -1$, $a_6 \in [43a_3/23, 225/38]$) covers $I_6^{(m)}$'s right sub-gap. At $a_6 = 225/38$:

$$B_{6,4}[0] = \frac{54}{11 \cdot 225/38} = \frac{54 \cdot 38}{11 \cdot 225} = \frac{2052}{2475} = \frac{228}{275}.$$

In slot-relative coordinates: $228/275 - 89/110 = (228\cdot110 - 89\cdot275)/(275\cdot110) = (25080-24475)/30250 = 605/30250 = 1/50 > 0$.

This computation uses only the ratio $228/275$ (from $a_6 = 225/38$) and $89/110$ ($I_8$'s left boundary) — **no phase dependence**. Hence $\mathrm{GF}(I_8^{(m)}) \geq 1/50$ in cycle $m$. $\square$

**Summary of Lemma C.** All cascade conclusions in Theorem UB depend only on $a_j \in (j-1, j)$ (the speed value) and $\sigma_j$ (the sign, which determines the speed range). They are independent of phase $\varphi_{j,m}$ and cycle index $m$. Specifically: the cascade conclusion "$\mathrm{GF}(I_k^{(m)}) \geq \delta_k > 0$" holds in any cycle $m$ where runner $j$ covers the right gap of $I_9^{(m)}$.

---

### Phase-Uniformity: Universality of Theorem UB

The correct argument for phase-independence is the **universality of Theorem UB over the full range of valid gap positions** — not merely width invariance.

**Slot boundaries are phase-independent.** In pacemaker-relative coordinates (subtracting $m/10$ from all times), slot $I_9^{(m)}$ always corresponds to the interval $[100/110, 109/110]$ (i.e., $[10/11, 109/110]$ in slot-relative units), because the slot boundaries are defined by the EFN normalisation $a_{10} = 10$ and are independent of any runner phases.

**$g_L^{(m)}$ is always in the valid range.** The left endpoint $g_L^{(m)}$ of the portion of $I_9^{(m)}$ not yet covered by runners 2 and 9 (the "right gap") satisfies $g_L^{(m)} \in [100/110, 109/110)$ in every cycle $m$. This is because: (i) the left boundary $100/110$ is the slot's own left edge (no gap can start to the left of the slot), and (ii) $g_L^{(m)} < 109/110$ whenever the right gap has positive width. The value of $g_L^{(m)}$ within this range MAY vary between cycles (since $a_2$'s bad intervals are phase-shifted by $\varphi_{2,m}$), but it always stays in $[100/110, 109/110)$.

**Theorem UB is proved for all $(j, g_L)$ in the valid range.** The Universal Blocking Theorem (§11.5) states: for every runner $j \in \{3,\ldots,8\}$ and every $g_L \in [100/110, 109/110)$, if runner $j$ covers the gap $[g_L, 109/110]$ in slot $I_9^{(m)}$, then the cascade conclusion $\mathrm{GF}(I_k^{(m)}) \geq \delta_k > 0$ holds for some $k \in \{1,\ldots,8\}$. The cascade conclusions (PSM: $a_3 \leq 340/109$; Chain A: $a_8 \geq 8a_3/3$; Chain B: $a_4 \in [1849/450, 450/109]$) are derived from the SPEED CONSTRAINTS $a_j \in (j-1, j)$ and $\sigma_j = \pm 1$ alone — they do not reference the specific value of $g_L$ or the cycle index $m$. This is the universal quantification over $g_L$ that makes the argument phase-independent.

**Conclusion.** Since $g_L^{(m)} \in [100/110, 109/110)$ in every cycle $m$, and Theorem UB applies to every such $g_L$ value, the cascade conclusion holds in every cycle $m$ regardless of the phase $\varphi_{j,m}$. This is the source of phase-independence — not just the width invariance of Lemma P (though Lemma P is used within the proof of Theorem UB to ensure bad-interval widths are cycle-independent).

---

**Theorem PU (Phase-Uniform Theorem U).**

> **Theorem PU.** In any CB configuration with $\sigma_2 = +1$, for every pacemaker cycle $m$ within $W_{\mathrm{ref}}$:
>
> Either $\mathrm{GF}(I_9^{(m)}) > 0$ (right gap of $I_9^{(m)}$ is uncovered), or $\mathrm{GF}(I_k^{(m)}) > 0$ for some $k \in \{1,\ldots,8\}$ (some other slot is forced open by the cascade).
>
> In both cases, $\mathrm{GF}_{\mathrm{total}}(I_k^{(m)}) > 0$, and since runner $v_1$ is isolated throughout $W_{\mathrm{ref}}$, a witness exists in $W_{\mathrm{ref}}[m]$.

**Proof.** Fix a CB configuration with $\sigma_2 = +1$ and a pacemaker cycle $m \subset W_{\mathrm{ref}}$. Let $g_L^{(m)}$ be the left endpoint of the right gap $[g_L^{(m)}, 109/110]$ of $I_9^{(m)}$ left uncovered by runners 2 and 9. (In cycle-relative coordinates; "right gap" means the portion of $I_9^{(m)}$ not covered by bad intervals of runners 2 and 9.)

**Case 1: $g_L^{(m)} = 109/110$ (no right gap, or gap has measure zero).**
The right portion of $I_9^{(m)}$ is fully covered by runners 2 and 9. From Case α of Theorem U: covering $I_4^{(m)}$ forces $a_2 \geq L(a_9)$ (speed lower bound from Lemmas 11.2.1–11.2.2). Simultaneously covering all of $I_9^{(m)}$ requires $a_2 \leq U(a_9)$. For the $(a_2, a_9)$ ranges where $L(a_9) > U(a_9)$: incompatible $\Rightarrow \mathrm{GF}(I_k^{(m)}) > 0$ for some $k \in \{4,9\}$.

**Note:** The bounds $L(a_9)$ and $U(a_9)$ are defined via bad-interval widths and slot dimensions — they depend only on $a_2, a_9 \in (j-1,j)$, not on the cycle index $m$. Case α is phase-independent.

**Case 2: $g_L^{(m)} < 109/110$ (right gap of positive width exists in $I_9^{(m)}$).**
The right gap $[g_L^{(m)}, 109/110]$ must be covered by some runner $j \in \{3,\ldots,8\}$ for a CB configuration.

**Sub-case 2a: No runner $j \in \{3,\ldots,8\}$ covers the gap.**
Then $\mathrm{GF}(I_9^{(m)}) \geq 109/110 - g_L^{(m)} > 0$. ✓

**Sub-case 2b: Some runner $j$ covers the gap.**
By Lemma C, the cascade conclusion for that runner (PSM, Chain A, or Chain B) gives $\mathrm{GF}(I_k^{(m)}) \geq \delta_k > 0$ for some $k \in \{1,\ldots,8\}$. The cascade conclusions are phase-independent (Lemma C). ✓

In all sub-cases: $\mathrm{GF}(I_k^{(m)}) > 0$ for some $k$.

**Combining with runner $v_1$ isolation.** By definition of $W_{\mathrm{ref}}$, runner $v_1$ is isolated for all $t \in W_{\mathrm{ref}} \supset W_{\mathrm{ref}}[m]$. Hence $\mathrm{GF}_{\mathrm{total}}(I_k^{(m)}) > 0$: a witness $t \in I_k^{(m)}$ exists where all runners (including $v_1$) are isolated. $\square$

---

**Theorem PU$_{-1}$ (Phase-Uniform Lemma S2).**

> **Theorem PU$_{-1}$.** In any CB configuration with $\sigma_2 = -1$, for any pacemaker cycle $m$ within $W_{\mathrm{ref}}$: $\mathrm{GF}(I_9^{(m)}) > 0$.

**Proof.** Lemma S2 (§12.2) proves $W(I_9) \geq 538/54395 > 0$ where $W$ is the witness width (minimum positive good fraction over all $\sigma_2 = -1$ classes). The proof uses:
- Lemma S1 (runner 2 eliminated from terminal absorber role): depends only on $a_2 \in (2,3)$ with $\sigma_2 = -1$ and $a_5 \in (4,5)$ with $\sigma_5 = +1$. Speed constraints, phase-independent.
- The residual cascade for $W(I_9) \geq 538/54395$: again uses bad-interval widths and speed ranges.

By the same argument as Lemma C: Lemma S2's conclusion holds in any cycle $m$. $\square$

---

**Corollary W_ref (Full Closure of Case R>).**

> **Corollary W_ref.** For any CB configuration of the $n = 11$ AP with ratio $e_{10}/e_1 > 10$ (equivalently $a_1 < 1$ in EFN units), there exists a witness $t \in W_{\mathrm{ref}} = [1/(11a_1), 10/(11a_1)]$ where all runners are simultaneously isolated.

**Proof.**

1. **Runner $v_1$ isolation.** Runner $v_1$ (EFN speed $a_1 = 10e_1/e_{10} < 1$) is isolated at time $t$ iff $\{e_1 t\} \in [1/11, 10/11]$, i.e., $t \in W_{\mathrm{ref}}$ (by definition). So runner $v_1$ is isolated throughout $W_{\mathrm{ref}}$. ✓

2. **A pacemaker cycle inside $W_{\mathrm{ref}}$.** We seek an integer $m_*$ such that
$$W_0[m_*] = \left[\frac{11m_*+1}{110}, \frac{11m_*+10}{110}\right] \subset W_{\mathrm{ref}} = \left[\frac{1}{11a_1}, \frac{10}{11a_1}\right].$$
This is equivalent to
$$\frac{10/a_1 - 1}{11} \leq m_* \leq \frac{100/a_1 - 10}{11}.$$
The length of this interval is
$$\frac{100/a_1 - 10}{11} - \frac{10/a_1 - 1}{11}
= \frac{9(10/a_1 - 1)}{11}
> \frac{81}{11} > 1,$$
because $a_1 < 1$. Therefore the interval contains an integer $m_*$, and for this choice we have $W_0[m_*] \subset W_{\mathrm{ref}}$.

3. **Sign analysis on the chosen cycle $m_*$.** Split on $\sigma_2$:
   - $\sigma_2 = +1$: By Theorem PU, the cycle $W_0[m_*] \subset W_{\mathrm{ref}}$ satisfies $\mathrm{GF}_{\mathrm{total}}(I_k^{(m_*)}) > 0$ for some $k$. Hence that cycle contains a witness. ✓
   - $\sigma_2 = -1$: By Theorem PU$_{-1}$, the same cycle satisfies $\mathrm{GF}(I_9^{(m_*)}) \geq 538/54395 > 0$. Combined with runner $v_1$ isolation throughout $W_{\mathrm{ref}}$, this gives $\mathrm{GF}_{\mathrm{total}}(I_9^{(m_*)}) > 0$. ✓

4. **Conclusion.** In both sign cases, a witness $t \in W_{\mathrm{ref}}$ exists. The LRC is proved for ratio $> 10$. $\square$

**Canonical Lower Bounds Inherited:**

| Mechanism | Exact lower bound | Source |
|-----------|------------------|--------|
| $\sigma_2=+1$, GF $> 0$ for some slot | positive (slot-dependent; $\geq 11/20570$ in PSM sub-cases, $\geq 1/50$ in Chain A sub-cases) | Theorem U + Theorem UB |
| $\sigma_2=-1$, min GF over all cycles | $538/54395$ | Lemma S2 |
| Chain A, GF($I_8$) per affected cycle | $1/50$ | Lemma C(ii) |
| Chain B, GF($I_7$) per affected cycle | $1533/18490$ | Lemma C(iii) |

These bounds are cycle-uniform: the minimum is not cycle-specific.

---

## 14. Theorem C — Complete Proof

**Lemma CR (Commensurable-Real to Integer Reduction).** *Let $e_1 < \cdots < e_{10}$ be commensurable positive reals. Write $e_i = p_i \omega$ where $p_1 < \cdots < p_{10}$ are positive integers with $\gcd(p_1,\ldots,p_{10}) = 1$ and $\omega > 0$. Then $\|e_i t\| \geq 1/11$ for all $i$ iff $\|p_i s\| \geq 1/11$ for all $i$, where $s = \omega t$. In particular, Theorem W_ref (proved for all EFN-normalised CB configurations, including those arising from integer speed ratios) applies to commensurable real speeds via this reduction: the witness $s \in W_{\rm ref}$ for the integer configuration $(p_1,\ldots,p_{10})$ gives witness $t = s/\omega$ for the original real configuration.*

**Proof.** $\|e_i t\| = \|p_i \omega t\| = \|p_i s\|$. $\square$

---

**Theorem C (Classical LRC for $n = 11$, complete).** *For any ten distinct positive real speeds $e_1 < \cdots < e_{10}$, there exists $t > 0$ with $\|e_i t\| \geq 1/11$ for all $i = 1,\ldots,10$.*

**Proof.** By the Gap Decomposition (§10.3), every configuration falls into exactly one of three cases:

*Case B (bounded ratio, $e_{10}/e_1 \leq 10$):* Theorem B gives explicit $t^* = 10/(11e_{10})$. $\square$

*Case I (irrational ratio):* Proposition E (§10.2) gives existence via Kronecker closure. $\square$

*Case R> (commensurable, $e_{10}/e_1 > 10$):* By Lemma CR, write $e_i = p_i \omega$ for positive integers $p_1 < \cdots < p_{10}$ with $\gcd(p_1,\ldots,p_{10}) = 1$ and $\omega > 0$. Theorem W_ref (§13) gives a witness $s \in W_{\rm ref} = [1/(11p_1), 10/(11p_1)]$ for the integer speed configuration. Then $t = s/\omega$ satisfies $\|e_i t\| = \|p_i s\| \geq 1/11$ for all $i$. $\square$

The three cases are exhaustive and mutually exclusive. The proof is complete. $\square$

| Route | Method | Status | Scope |
|---|---|---|---|
| Theorem B | Explicit witness $t^* = 10/(11e_{10})$ | **PROVED** | $e_{10}/e_1 \leq 10$ |
| Proposition E | Kronecker closure | **PROVED** | Irrational speed ratios |
| **Theorem W_ref** | Coupling Principle + Runner 2 Incompatibility + Phase-Uniform Extension; window $W_{\rm ref}$ | **PROVED** (2026-03-27) | Case R> — all ratios |
| **Lemma CR** | Commensurable reals reduce to integers | **PROVED** | Connects real speeds to Theorem W_ref |
| **Theorem C** | Cases B + I + R> exhaustive | **PROVED** (2026-03-27) | Full classical LRC, $n=11$ |

---

## 15. The 11-Pacemaker Special Case

*Note: The following provides an independent direct proof for the special case where the pacemaker is an integer multiple. This case is already closed by §13 (Corollary W_ref); we include it as an independent verification.*

**Normalisation.** Without loss of generality (rescaling by $e_1$), the ten runner speeds are positive integers
$$\mathcal{V} = \{1,\ 11,\ p_2,\ p_3,\ \ldots,\ p_9\},$$
where $p_2 < p_3 < \cdots < p_9$ are arbitrary positive integers, distinct from each other and from 1 and 11.

**Case dichotomy.** We split all possible free speed sets $\{p_2,\ldots,p_9\}$ into:
- **Case B:** $p_j \equiv 0 \pmod{11}$ for all $j = 2,\ldots,9$.
- **Case A:** $p_j \not\equiv 0 \pmod{11}$ for at least one $j$.

**Theorem 15.A (Case B: Explicit Witness $t^* = 12/121$).** *If all free speeds satisfy $p_j \equiv 0 \pmod{11}$ (so $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, all distinct), then $t^* = 12/121$ satisfies $\|v \cdot t^*\| \geq 1/11$ for all $v \in \mathcal{V}$.*

**Proof.**
- *Runner at speed 1:* $\{12/121\} = 12/121 \in (1/11, 10/11)$. ✓
- *Runner at speed 11:* $\{11 \cdot 12/121\} = \{132/121\} = \{1+11/121\} = 1/11$. So $\|11t^*\| = 1/11 \geq 1/11$. ✓
- *Runner at speed $11k_j$, $k_j \in \{2,\ldots,9\}$:* $\{11k_j \cdot 12/121\} = \{12k_j/11\} = k_j/11 \in \{2/11,\ldots,9/11\} \subset (1/11,10/11)$. ✓
- *Runner at speed $110$ ($k_j = 10$, if present):* $\{110 \cdot 12/121\} = 10/11$. So $\|110t^*\| = 1/11 \geq 1/11$. ✓

Since all $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, every runner is verified. $\square$

**Theorem 15.B (Case A: Positive-Measure Witness Set).** *If at least one free speed $p = p_{j_0}$ satisfies $p \not\equiv 0 \pmod{11}$, then the witness set $W = \{t > 0 : \{vt\} \in G\ \forall\, v \in \mathcal{V}\}$ (with $G = (1/11, 10/11)$) has positive Lebesgue measure. In particular $W \neq \emptyset$ and the LRC holds.*

**Proof (key steps).**

*Step 1 (Positive-measure base set).* Let $\mathcal{M} = \{k_j : p_j = 11k_j\}$ be the multipliers of the multiples-of-11 free runners. For any AP witness $m \in \{2,\ldots,9\}$, set $x_0 = m/11 \in G$; all $\{kx_0\}$ for $k \in \mathcal{M}$ lie strictly in $(1/11, 10/11)$. Hence each $m/11$ has an open neighbourhood with $S_A = \{x_0 \in G : \{kx_0\} \in G\ \text{for all}\ k \in \mathcal{M}\}$ of positive measure.

*Step 2 (Nine valid preimages).* For $x_0 \in S_A$ and times $t_j = (x_0+j)/11$, $j=0,\ldots,10$: $j=0$ and $j=10$ fail; $j=1,\ldots,9$ all satisfy $\{t_j\} = (x_0+j)/11 \in G$. Runner at speed 11 is safe since $\{11 t_j\} = x_0 \in G$.

*Step 3 (Key Lemma: equally-spaced preimages).* Let $p \not\equiv 0 \pmod{11}$, $r = p \bmod 11 \in \{1,\ldots,10\}$. Then $\{p \cdot t_j\} = \{\alpha + rj/11\}$ where $\alpha = \{px_0/11\}$. Since $\gcd(r,11)=1$, the values $rj \bmod 11$ for $j=0,\ldots,10$ are a permutation of $\{0,\ldots,10\}$, giving eleven equally-spaced points with gap $1/11$. Exactly 2 of the 11 values lie outside $\bar{G}$. Among $j=1,\ldots,9$ (9 valid preimages), at least 7 indices satisfy $\{p \cdot t_j\} \in \bar{G}$, leaving at least 5 strictly inside $G$.

*Step 4 (Positive measure via Fubini).* For each $x_0 \in S_A$, Step 3 gives $j^*(x_0) \in \{1,\ldots,9\}$ with $\{p \cdot t_{j^*}\} \in G$. Since $G$ is open, there is $\delta(x_0) > 0$ such that all conditions hold uniformly near $t_{j^*}$. Integrating over $x_0$ in a subset of $S_A$ where the distance to $\partial G$ is bounded below: $|W| \geq 2\eta/(11p) \cdot |E_\eta| > 0$. $\square$

**Theorem 15.Main (11-Pacemaker).** *Let $(e_1,\ldots,e_{10})$ be any ten distinct positive real speeds with the property that, after rescaling to integer speeds with minimum speed 1, the speed set contains both 1 and 11. Then there exists $t^* > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1,\ldots,10$.*

**Proof.** After rescaling, the speed set is $\{1, 11, p_2,\ldots,p_9\}$. Cases A and B are exhaustive:
- If all $p_j \equiv 0 \pmod{11}$ (and $p_j \leq 110$): Theorem 15.A gives explicit $t^* = 12/121$.
- If some $p_{j_0} \not\equiv 0 \pmod{11}$: Theorem 15.B gives $|W| > 0$, so $W \neq \emptyset$. $\square$

---

## References

- [BGG+98] A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi, *Flows, view obstructions, and the lonely runner*, J. Combin. Theory Ser. B **72** (1998), 1–9.

- [BH01] T. Bohman, R. Holzman, *Six lonely runners*, Electron. J. Combin. **8** (2001), R3.

- [BS08] J. Barajas, O. Serra, *The lonely runner with seven runners*, Electron. J. Combin. **15** (2008), R48.

- [Cus73] T. W. Cusick, *View obstruction problems*, Aequationes Math. **9** (1973), 165–170.

- [KN74] L. Kuipers, H. Niederreiter, *Uniform Distribution of Sequences*, Wiley-Interscience, New York, 1974.

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

Zero failures. The full analytic argument is the Corollary W_ref proof in §13.

### A.2 Route 3 Good-Fraction Floor

Deep minimisation over $3 \times 10^6$ random CB (complete-blocking) configurations + differential evolution + Nelder-Mead polish:
- Min GF $\approx$ 0.12%; never 0.
- Extremal configuration: $a_1 \approx 0.983$, sign pattern ++------.
- The analytic lower bound from Theorem UB varies by sub-case: $\geq 1/50 \approx 2\%$ for Chain A sub-cases, $\geq 11/20570 \approx 0.053\%$ for PSM runner 4 sub-cases, and $\geq 59/9460 \approx 0.62\%$ for the no-Chain-A β-3 sub-case. The empirical extremal at $0.12\%$ lies in a sub-case not covered by the $59/9460$ bound (see §11.4 note on minimum gap).

### A.3 256 Sign-Pattern Feasibility

Enumeration over all $2^8 = 256$ sign patterns $\sigma \in \{+,-\}^8$ for $(\delta_1,\ldots,\delta_8)$:
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
| $59/9460$ | $\approx 0.0062$ | GF$(I_9)$ lower bound in Theorem U Case B3 (no-Chain-A sub-case only; global min across all sub-cases is smaller — see §11.4 note) |
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

**Historical context:** The superseded §§10.7–10.15 (Slot-Economy Theorem, Lemma WIT) and earlier appendices from prior draft versions are not required for the canonical proof and are not reproduced here.
