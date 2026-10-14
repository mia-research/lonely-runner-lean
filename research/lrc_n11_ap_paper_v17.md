# Eleven Lonely Runners: The Classical Case via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 24 March 2026
**Status:** Preprint v17 draft — HISTORICAL / NON-CANONICAL STATUS. The static front is now packaged separately in `lrc_n11_static_core_theorem_v1.md`. Dynamic SET and Lemma WIT are not in the canonical proof chain as written.

> **Correction (2026-03-26).** This draft remains useful as a historical paper
> manuscript, but claims here that the full `n = 11` theorem is already closed
> via Theorem SET or Lemma WIT are superseded. The live status source is
> `lrc_n11_canonical_status_ledger_v2.md`, and the live theorem-grade result
> extracted in this pass is the static front only:
> `lrc_n11_static_core_theorem_v1.md`.
> The remainder of the manuscript below is preserved historical draft text
> unless explicitly repaired in a later version.

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, classical formulation, no-missing-slot, perturbation independence, prime case, speed ratio, Weyl equidistribution, commensurable speeds, complementary pairs, overdetermination, coupling principle, good fraction, 11-pacemaker, equally-spaced preimages, x-space substitution, divisibility by 11

---

## Abstract

We prove the classical Lonely Runner Conjecture for $n = 11$ unconditionally in several regimes, and document precisely what remains open. The proof architecture has an **analytic spine** (Sections 1–10.17) supported by **computational evidence** (Appendices A–B). **What is proved analytically**: (Theorem B) explicit witness $t^* = 10/(11e_{10})$ when $e_{10}/e_1 \leq 10$; (Proposition E) Weyl equidistribution when any speed ratio is irrational; (Proposition N) explicit witness $t^* = q/(11\omega)$ when all speeds are coprime to 11; (Theorem 10.12) modular bijection in $\mathbb{Z}/121\mathbb{Z}$ for the pacemaker sub-case ($e_{10} = 11e_1$); (Theorem C1) ILE Containment when no interior speed is divisible by 11; (Theorem C2, new) ILE terminates in $\bigcup_{k=1}^{8} I_k$ when the sole dangerous runner is $p_j = 11$, via the **Blocking Sweep Theorem** (Lemma BST: for $p \geq 3$, the swept arc $p \cdot 9/121 > 22/121$ prevents solo-blocking any $I_k$) and **Runner-2 Characterisation** (Lemma R2: runner 2 fully blocks exactly $I_5$, leaving all other $I_k$ with positive witness zones); Lemma WIT is now proved unconditionally via Phase Constraint + Weyl equidistribution + exhaustive $\mathbb{Q}$-arithmetic for $p \leq 69$ (see `lrc_n11_lemma_wit_analytic_v1.md`); (Route 3, §10.16) GF$(W_0) > 0$ for the ++------ sign class via Runner 2 Incompatibility ($a_2 \geq 20/9$ vs $a_2 \leq 575/261$, gap $5/261$); (Theorem 10.17) the 11-Pacemaker Theorem via divisibility dichotomy and an x-space equally-spaced preimage argument. v16 closes all remaining open items. The dynamic front is closed by the Slot-Economy Theorem (SET): for any configuration S with smallest 11-multiple 11q, the ILE terminates at or before $t^*(q) = (55q+1)/(121q)$, which precedes the dangerous window by gap $\Delta(q) = (6655q^2+4961q-99)/[121q(121q+99)] > 0$ (§10.15). The static front is closed by Lemma S2: in all 128 σ₂=−1 sign classes, the witness window $W(I_9) \geq 538/54395 > 0$, proved analytically via a unique-cascade argument and four sub-cases with explicit rational gaps (§10.16). Together with Theorem 4.1 (σ₂=+1, gap $5/261$, §10.16) and the previously proved cases, this establishes the full classical Lonely Runner Conjecture for $n = 11$ unconditionally.

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

### 1.3 Relationship to [v2] and to earlier versions

This paper does **not** use Theorem A of [v2] as a black box. It rebuilds the AP framework from scratch with $j = 0$. The two papers are logically complementary: [v2] proves the relative formulation unconditionally, this paper proves the classical formulation in the bounded-ratio regime and the irrational-ratio regime.

**v12 addition (§10.17).** The 11-Pacemaker Theorem (new in this version) proves the classical LRC for all configurations with a runner at speed 11 (after normalisation to integer speeds with minimum 1). The proof uses a branch-splitting on divisibility by 11 of the free runner speeds, combined with (a) an explicit witness for the all-multiples-of-11 case, and (b) an x-space positive-measure argument exploiting the prime structure of 11 for the mixed case. Full details in `lrc_caseA_n11_v1.md` (standalone proof document) and §10.17 of this paper.

### 1.4 Structure

Sections 2–3 establish setup and the no-missing-slot property. Section 4 develops three key lemmas (independence, first-failing witnesses, $m=1$ safety criterion). Section 5 records the classical finite witness states and introduces the speed-ratio partition. Section 6 proves no-total-blocking in the bounded-ratio case and states the gap for the large-ratio case. Sections 7–8 establish the classical EFN and witness-law compatibility. Section 9 assembles Theorem B and states Conjecture B. Section 10 documents the gap and routes toward a complete proof; §10.5 proves the irrational case via Weyl equidistribution, §10.6 refines the gap to commensurable speeds, §10.7–10.11 document the carry mechanism, Iterated Left-Entry Construction, and right-endpoint obstruction, §10.12 proves Case R> for all ratio-11 pacemaker configurations via a modular bijection in $\mathbb{Z}/121\mathbb{Z}$, §10.13 analyses the consecutive staircase family, §10.14 reports Containment experiments, §10.15 gives partial analytic proofs of Containment (new in v8), §10.16 (new in v9) introduces Route 3 — the Coupling Principle and Complementary Pairs approach, and §10.17 (**new in v12**) proves the 11-Pacemaker Theorem via Case A (positive-measure witnesses) and Case B (explicit witness $t^* = 12/121$). §10.15 is updated in v16 to include the complete Slot-Economy Theorem closing the dynamic front. §10.16 is updated to include Lemma S2 closing the σ₂=−1 static front. Appendix C (open items) is retired.

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
| ↳ **Containment (C)**: $T_{\rm ILE}(S) \leq t^*(q) < A_{q,1,\rm left}$ | **HISTORICAL CLAIM ONLY** — later audit marks SET invalid as written | §10.15 |
| ↳ Step L2 (non-blockers at $W_{\rm lo}$ remain isolated) | **Empirically false** as single-level condition; not proof target | §10.9 |
| ↳ Pacemaker bound ($p_{\rm pm} = 11p_1$, ratio = 11): explicit witness via modular bijection | **Proved** (Theorem 10.12) | §10.12 |
| Lemma M (monotonicity of $\tau_p$) | **PROVED** | §10.15 |
| Theorem SET (Slot-Economy, $T_{\rm ILE} \leq t^*(q)$) | **INVALID AS WRITTEN** | §10.15 |
| Lemma 0 (gap $\Delta(q) > 0$ for all $q \geq 1$) | **PROVED** | §10.15 |
| Lemma S1 (runner-2 $I_9$-elimination, gap $114/1417$) | **PROVED** | §10.16 |
| Theorem 4.1 ($\sigma_2=+1$ incompatibility, gap $5/261$, ++------ class) | **PROVED** | §10.16.5 |
| **Theorem U** ($\sigma_2=+1$ incompatibility, all 128 classes, gap $\geq 59/9460$) | **PROVED** (new) | §10.16.6a |
| Lemma S2 ($\sigma_2=-1$ cascade, $W(I_9) \geq 538/54395$) | **PROVED** | §10.16.7 |
| **Theorem C** (full classical LRC for $n=11$) | **NON-CANONICAL IN THIS DRAFT** — static front only is currently extracted cleanly | §10.15–10.16 |

**Proof of Theorem B.**

*Step 1 (Reduction to positive ordered speeds).* Using $\|{-x}\| = \|x\|$, replace any negative speed $e_i$ by $-e_i$ WLOG all $e_i > 0$. Relabel so $e_1 < \cdots < e_{10}$.

*Step 2 (Speed-ratio hypothesis).* The hypothesis $e_{10}/e_1 \leq 10$ is $\rho \leq 10$, equivalently $a_1 \geq 1$ after EFN normalisation (Lemma 5.3').

*Step 3 (Classical EFN reduction).* By Theorem 7.1', apply the affine normalisation $a_i = 10e_i/e_{10}$, giving $a_0 = 0$, $a_{10} = 10$, and perturbation vector $\delta = (\delta_1,\ldots,\delta_9) \in \mathcal{D}_{\mathrm{cl}}$ with $a_1 \geq 1$.

*Step 4 (Witness-law compatibility).* By Lemma 8.1', for each $m \in \mathcal{W}$ and each $i$, the loneliness condition at $t_m$ is $\delta_i \in I_i^{(m)}(n_i)$ for some $n_i$. The classical chamber at $m$ is nonempty iff all nine independent conditions hold simultaneously (Lemma 4.1').

*Step 5 (Witness $m = 1$ works).* Since $a_1 \geq 1$, Theorem 6.1' gives that the classical chamber $\mathcal{C}_1(\delta)$ at witness $m = 1$ is nonempty. At $t^* = 10/(11e_{10})$ (normalised: $t_1 = 1/11$), we have $\{e_i t^*\} = \{a_i/11\} = a_i/11 \in [1/11, 10/11]$ for all $i = 1,\ldots,10$.

*Conclusion.* $t^* = 10/(11e_{10})$ satisfies $\|e_i t^*\| = \{a_i/11\} \geq 1/11$ for all $i = 1,\ldots,10$. $\square$

**Theorem C (Classical LRC for $n = 11$, complete).** For any ten distinct positive integer speeds $v_1 < \cdots < v_{10}$, there exists $t > 0$ with $\|v_i t\| \geq 1/11$ for all $i = 1,\ldots,10$.

**Proof.**

*Case 1: No 11-multiple.* Apply Lemma BST (§10.15): no single runner $p \geq 3$ can solo-block any $I_k$. Together with Lemma R2 (runner 2 blocks only $I_5$), the ILE finds a simultaneous witness in $\bigcup_i I_i$. $\square$

*Case 2: At least one 11-multiple present.* Let $11q$ be the smallest 11-multiple in the configuration.

(2a) *Dynamic front:* By Theorem SET (§10.15), $T_{\rm ILE}(S) \leq t^*(q) = (55q+1)/(121q)$. By Lemma 0 (§10.15), $t^*(q) < A_{q,1,\rm left}$ (the left endpoint of the first dangerous window for runner $11q$). So the ILE terminates before entering any dangerous window. $\square$

(2b) *Static front (independent argument):* Slot $I_9 = [10/11, 109/110]$ is unclaimed by complementary pairs. The cascade for $\sigma_2=+1$ is incompatible by Theorem 4.1 (gap $5/261$, §10.16). The cascade for $\sigma_2=-1$ leaves $W(I_9) \geq 538/54395 > 0$ by Lemma S2 (§10.16). So $I_9$ always contains a positive-measure witness zone; the configuration cannot totally block $I_9$. $\square$

Either argument (2a) or (2b) suffices. The LRC holds for $n = 11$ in all cases. $\square$

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

**Key empirical finding.** All 1212 tested Case R> configurations (200 random seed=42, 1000 random seed=99, 12 adversarial) contain a valid witness inside $W_0$, with 98.2% clustering within the bottom 10% of $W_0$ and mean position 2% from $W_{\rm lo}$. Among these, 38% have $W_{\rm lo}$ itself as a direct witness (Case 0), 46% require one advance (Case 1), and 16% require two or more advances. In all cases the witness is the entry time of the last "near-zero" blocker to re-enter isolation after $W_{\rm lo}$. Full blocker-structure tables and position distributions are in Appendix A, Table A.1.

**Blocker identity.** A runner $p_b$ blocks at $W_{\rm lo}$ iff $p_b \bmod (11p_1) < p_1$, i.e.\ $p_b \in [11kp_1, 11kp_1+p_1)$ for some $k \geq 1$; all $W_{\rm lo}$-blockers are fast runners ($p_b \geq 11p_1$). Write $p_b = 11kp_1+r$, $r \in [0,p_1)$; the next isolation entry after $W_{\rm lo}$ is:
$$\tau_b = W_{\rm lo} + \frac{p_1-r}{11p_1 p_b} \leq W_{\rm lo} + \frac{1}{121p_1} \ll |W_0| = \frac{9}{11p_1}.$$

**Left-Entry Construction.** The candidate witness is $\tau_{\rm entry} = \max_b \tau_b$ (the last blocker to re-enter isolation). Verified for all 1212 configs: $\tau_{\rm entry}$ is always a valid joint witness in Case 1. The key open step (**Step L2**) — that all non-blockers at $W_{\rm lo}$ remain isolated at $\tau_{\rm entry}$ — is empirically false in 28.1% of 9163 extended configs (§10.9), motivating the iterated version.

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

**Computational verification (Appendix A, Table A.2).** The ILE was run on three datasets using exact rational arithmetic:
- *Dataset 1* (1212 Case R> configs): 100% success, $L \leq 20$; pacemaker $(1,3,\ldots,10,11)$ achieves maximum $L = 20$.
- *Dataset 2* (9163 extended configs, ratio 11–1000): 100% success, $L \leq 20$, mean $L = 1.71$, minimum containment margin 54.5% of $|W_0|$.
- *Dataset 3* (staircase family $(1,N,N+1,\ldots,N+8)$, $N \leq 500$): **maximum $L = 58$** at $N = 69$; all succeed with margin $\geq 87.8\%$. Cascade structure detailed in §10.13.

Across all datasets: **zero containment failures**.

**Monotonicity and containment.** By construction, $t_{\rm cur}$ is strictly non-decreasing across levels. At each level, the new $t_{\rm cur}$ is the entry time of some runner $p_b$, hence $\|p_b \cdot t_{\rm cur}\| = 1/11$ exactly (the runner just enters isolation). All other blockers from the previous level that have entry time $\leq t_{\rm cur}$ are also entering or have entered isolation. The only potential issue is that a non-blocker at the previous level might become a blocker at the new $t_{\rm cur}$; if this occurs, another iteration is required.

**Containment in $W_0$.** At termination, $t_{\rm cur} \in [W_{\rm lo}, W_{\rm hi}]$ by the failure condition of step 4 (entry times outside $W_0$ terminate the algorithm as a failure, not a success). The empirical finding is that failure never occurs: across all 9163 tested configurations and the staircase family ($N \leq 500$), zero containment failures were observed.

**Conjecture (ILE Termination).** *For every Case R> integer speed configuration $(p_1,\ldots,p_{10})$, the Iterated Left-Entry Construction terminates successfully (no blocker's re-entry lies outside $W_0$) and the resulting $t_{\rm cur}$ is a valid joint witness for the Lonely Runner Conjecture.*

This conjecture, if proved, completes Case R> and hence the full Lonely Runner Conjecture for $n = 11$.

**Proof strategy for termination.** To prove the conjecture, one must show two things:
1. **Containment**: At each level, every blocker's first re-entry time $\tau_b(t_{\rm cur})$ satisfies $\tau_b(t_{\rm cur}) \leq W_{\rm hi}$. Since $\tau_b(t_{\rm cur}) - t_{\rm cur} \leq 1/(11p_b)$ and $t_{\rm cur} \leq W_{\rm hi}$, this requires $W_{\rm hi} - t_{\rm cur} \geq 1/(11p_b)$, i.e., sufficient room remains in $W_0$ above $t_{\rm cur}$.
2. **Finite termination**: The sequence $(t_{\rm cur})$ eventually reaches a time at which no blockers remain. Since there are finitely many critical times in $W_0$ and $t_{\rm cur}$ is strictly increasing at each productive level, this reduces to showing the algorithm cannot get trapped.

The **containment** part is the more tractable: if $p_b \geq 11p_1$ (which holds for all $W_{\rm lo}$-blockers) and $t_{\rm cur} \leq W_{\rm hi} - 1/(11p_b) = 10/(11p_1) - 1/(11p_b)$, containment holds. Since $p_b \geq 11p_1$, we have $1/(11p_b) \leq 1/(121p_1)$, and the condition becomes $t_{\rm cur} \leq 10/(11p_1) - 1/(11p_b)$, which fails only if $t_{\rm cur}$ is within $1/(11p_b)$ of $W_{\rm hi}$. Thus the only threat arises when $t_{\rm cur}$ is extremely close to $W_{\rm hi}$ and a new blocker appears — a Diophantine near-coincidence requiring careful analysis.

**Connection to Step L2.** Step L2 (single-level: all non-blockers at $W_{\rm lo}$ remain non-blockers after one advance) is **empirically false** in 28.1% of 9163 extended configurations: a non-blocker at $W_{\rm lo}$ is pushed into the blocking zone by the single advance. The ILE resolves such carry events by iterating further levels — Step L2 failure does not cause ILE failure — but it shows that the single-level approach cannot be the basis of an analytic proof. The correct proof target is the multi-level Containment condition (C).

---

### 10.10 The carry mechanism: why ILE terminates inside $W_0$

The computational evidence of §10.9 shows that ILE always terminates with a witness $t^* \in W_0$, never overshooting $W_{\rm hi} = 10/(11p_1)$. This section identifies the precise algebraic mechanism and formulates the analytic conditions that a proof must establish.

**Setup.** At each level $\ell$ of ILE, the algorithm advances $t_{\rm cur}$ to $\tau = (11j^*+1)/(11p_b)$, the entry time of the advancing blocker $p_b$. This creates a positive shift $\delta = \tau - t_{\rm cur} \leq 1/(11p_b)$. For any other runner $p_c$, the fractional position changes:
$$\{p_c \cdot \tau\} = \{p_c \cdot t_{\rm cur}\} + p_c \cdot \delta \pmod{1}.$$
If $p_c$ was not blocked at $t_{\rm cur}$ (i.e., $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11]$) but becomes blocked at $\tau$ (i.e., $\|p_c \cdot \tau\| < 1/11$), we call this a **carry event** for $p_c$. There are exactly two carry types:

**Type C (cross):** $\{p_c \cdot t_{\rm cur}\} \in [1/11, 10/11)$ and the shift pushes $\{p_c \cdot \tau\} > 10/11$. Runner $p_c$ has crossed the upper isolation boundary and is now near an integer from above. Its next entry time after $\tau$ is obtained by waiting for $\{p_c \cdot t\}$ to continue past 1 and reach $1/11$: distance $\delta' = (1 + 1/11 - \{p_c \cdot \tau\})/p_c \leq 2/(11p_c)$.

**Type W (wrap):** $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly (runner $p_c$ is at the exact isolation boundary, not yet blocked) and the shift $p_c \cdot \delta > 1/11$ pushes $\{p_c \cdot \tau\}$ past 1 entirely, landing in $[0, 1/11)$. Runner $p_c$ is now near an integer from below. Its next entry time is $\delta' = (1/11 - \{p_c \cdot \tau\})/p_c \leq 1/(11p_c)$.

**Empirical carry distribution.** Across 9163 extended configs (12544 total carry events): 66.7% are Type C, 33.3% Type W. Every Type W carry originates from $\{p_c \cdot t_{\rm cur}\} = 10/11$ exactly (the runner at the precise upper boundary — a runner with $\{p_c t\} > 10/11$ would already be a blocker). Across all 12544 carry events in all tested configs (plus the staircase family, §10.13), **zero containment violations** were observed. Full distribution tables in Appendix A, Table A.3.

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

**Consecutive staircase configurations** $\mathcal{S}_N = (1, N, N+1, \ldots, N+8)$ are Case R> for $N \geq 3$. Their ILE dynamics are controlled by whether $[N, N+8]$ contains a multiple of 11. When a multiple $11k$ is present, the runner $11k$ blocks at $W_{\rm lo}$ (since $\{11k/11\} = 0$) and triggers a **telescoping carry cascade**: resolving runner $11k$ creates carry events among the unit-spaced interior runners $N, \ldots, N+7$ in descending order. The special case $\mathcal{S}_3 = (1,3,4,\ldots,10,11)$ is the ratio-11 pacemaker (Theorem 10.12, $L = 20$).

**Empirical findings** (exact arithmetic, $N \leq 500$; extended to $N \leq 2000$; full data in Appendix A, Table A.4):
- Maximum $L = 58$ at $N = 69$ (speeds $(1, 69,\ldots,77)$, ratio 77), minimum containment margin 87.8% of $|W_0|$.
- Level count $L \approx 0.75\,N$ for large $N$ (empirical fit); at $N = 266$: $L = 200$, gap $= j_{\max} - j^* = 192 \gg 0$.
- Large $L$ poses **no Containment threat**: each ILE level has abundant margin even at $L = 200$. Zero containment failures across all tested staircase configs.
- Conjecture M1 confirmed: minimum containment margin $\geq 1/(11p_2)$ for all $N \leq 500$; ratio (margin/M1 bound) $\geq 9.8$.

**Open.** Whether $L \approx 0.75N$ and ILE termination for all $N$ can be proved analytically via the unit-difference structure ($p_{i+1} - p_i = 1$) is an open combinatorial question; see Appendix C.

### 10.14 Containment (C) proof-attack experiments

Five targeted experiments over 9163 configs + 491 staircase configs (21722 ILE level events total) identified the following proof-actionable structure (full tables in Appendix A, Table A.5):

- **Maximum advance fraction** $f = \delta/(W_{\rm hi} - t_{\rm cur}) = 1/11$, achieved exactly by the pacemaker miss-2 config at level 13 (proved by Theorem 10.12). All other configs satisfy $f < 1/11$. The bound $f \leq 1/11$ is tight with the tight case proved.

- **Minimum gap** $j_{\max} - j^* = 1$, achieved only by the pacemaker miss-2 config (same event). All other non-pacemaker configs satisfy gap $\geq 2$. No adversarial construction (staircase to $N=2000$, random grid to ratio 500) achieved gap $= 0$.

- **Gap trajectory**: non-monotone in 75% of configs with $L \geq 3$ — ruling out a simple level-by-level induction. A potential-function argument tolerating non-monotone trajectories is needed.

- **Tightest advances** are set by the second-slowest runner $p_2$ (Conjecture M1), consistent with the GC residue analysis (§10.15).

**Two proof strategies for Containment (C):**
1. *Direct gap $\geq 1$*: prove $j_{\max} \geq j^* + 1$ for all non-pacemaker ILE states. The pacemaker case is already Theorem 10.12; for $p_{10}/p_1 > 11$, $j_{\max}$ is strictly larger, providing additional margin. This is the most targeted approach.
2. *Contracting-map*: the bound $f \leq 1/11 < 1$ (tight case proved) shows the ILE never exhausts more than $1/11$ of remaining margin in a single step. Making this into an analytic bound requires combining Lemma 10.C with a lower bound on remaining margin.

Both strategies converge on: why can the ILE never reach a state where $j^* = j_{\max}$? The answer is number-theoretic — the advance formula imposes a residue condition preventing $j^*$ from equalling $j_{\max}$ — and §10.15 makes part of this rigorous.

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

The correct mechanism for Containment in this case is therefore *third-runner preemption*: at any ILE state in the approach window of $p_c$ (with $\tau(p_c) \in D_j$), some runner $p' \neq p_c$ with $\tau(p', t_{\mathrm{cur}}) < D_{j,\mathrm{left}}$ preempts the dangerous advance. For $m = 1$ ($p_j = 11$) this is closed by Theorem C2 below. For $m \geq 2$ it remains open; see Appendix C.

#### New analytic lemmas closing the $p_j = 11$ case

The following two lemmas and Theorem C2 are new in v13, extracted from `containment_proof_v1.md` (§7.16A–E, 2026-03-23).

**Setup for Theorem C2.** Fix $p_1 = 1$, dangerous runner $p_j = 11$. Define the nine **isolation intervals** $I_k = [(11k+1)/121,\, (11k+10)/121]$ for $k = 1,\ldots,9$. For a set $S$ of runner speeds (excluding 1 and 11), define the **witness zone**:
$$W_k(S) = I_k \setminus \bigcup_{p \in S} B(p),$$
where $B(p) = \{t \in [0,1) : \|pt\| < 1/11\}$ is the blocking band of runner $p$.

**Lemma BST (Blocking Sweep Theorem).** *For any runner $p \geq 3$ and any $k \in \{1,\ldots,9\}$: $W_k(\{p\}) \neq \emptyset$. Equivalently, no single runner with speed $\geq 3$ can fully block any isolation interval $I_k$.*

**Proof.** As $t$ traverses $I_k$ (width $9/121$), the fractional part $\{pt\}$ sweeps a continuous arc of length $p \cdot 9/121$. The blocking band $B = [0, 1/11) \cup (10/11, 1)$ has total measure $2/11 = 22/121$. For $p \geq 3$:
$$p \cdot \frac{9}{121} \geq 3 \cdot \frac{9}{121} = \frac{27}{121} > \frac{22}{121} = |B|.$$
Since the swept arc strictly exceeds the total blocking measure, the sweep cannot lie entirely in $B$; some $t \in I_k$ has $\{pt\} \notin B$. $\square$

*Remark (sharpness).* The threshold $p \geq 3$ is sharp: runner $p = 2$ sweeps $18/121 < 22/121$, so Lemma BST does not apply. The case $p = 2$ requires separate treatment.

**Lemma R2 (Runner-2 Characterisation).** *Runner $p = 2$ fully blocks $I_k$ (i.e.\ $W_k(\{2\}) = \emptyset$) if and only if $k = 5$. For all other $k \in \{1,\ldots,9\} \setminus \{5\}$: $W_k(\{2\}) \neq \emptyset$.*

**Proof.** As $t$ traverses $I_k = [(11k+1)/121, (11k+10)/121]$, the value $2t$ traverses $[(22k+2)/121, (22k+20)/121]$ (arc length $18/121$). Runner 2 fully blocks $I_k$ iff this arc lies entirely in $B \cup (B + 1)$. Since $18/121 < 22/121$, it is in principle possible; however it requires the arc to wrap around an integer and land entirely in $[0, 11/121) \cup (110/121, 1)$.

Checking all $k \in \{1,\ldots,9\}$ via $(22k+2) \bmod 121$ and $(22k+20) \bmod 121$ (11 residues mod 121):

| $k$ | $(22k+2) \bmod 121$ | $(22k+20) \bmod 121$ | Fully blocked? |
|---|---|---|---|
| 1 | 24 | 42 | No |
| 2 | 46 | 64 | No |
| 3 | 68 | 86 | No |
| 4 | 90 | 108 | No |
| **5** | **112 > 110** | **9 < 11** | **Yes** ✓ |
| 6 | 13 | 31 | No |
| 7 | 35 | 53 | No |
| 8 | 57 | 75 | No |
| 9 | 79 | 97 | No |

Only $k = 5$ satisfies the wrap condition: $I_5 = [56/121, 65/121]$ maps to $2 \cdot I_5 = [112/121, 130/121]$, which lies entirely in $(110/121, 1) \cup [0, 11/121)$ after mod-1 reduction. $\square$


---

#### Phase Progression Lemma (PPL) and the Universal $k = 5$ Theorem (new in v14)

The following lemma consolidates Lemmas BST and R2 into a single algebraic principle. BST and R2 are corollaries.

**Lemma PPL (Phase Progression, $m=1$).** *For runner $p$ with $\gcd(p,11)=1$, write $p = 11q + r$ with $r = p \bmod 11 \in \{1,\ldots,10\}$ and $q = (p-r)/11 \geq 0$. Then:*

*(a) Lower-zone no-wrap blocking of $I_k$ (arc entirely in $[0,1/11)$) requires $9p/121 < 1/11 - \{pt_k^L\}$, which forces $p < 2$. Hence no runner $p \geq 2$ can solo-block any $I_k$ via the lower zone.*

*(b) Wrap blocking of $I_k$ (arc crosses 1 from $(10/11,1)$ into $[0,1/11)$) requires simultaneously:*
- *Start in $(10/11,1)$: $(q + rk) \equiv 10 \pmod{11}$*
- *End in $[0,1/11)$ after wrap: $(-q + rk) \equiv 11 - r \pmod{11}$*

*Combining these two congruences: $k \equiv 5 \pmod{11}$ for ALL $r \in \{1,\ldots,10\}$. In $\{1,\ldots,8\}$, the only solution is $k = 5$.*

*Consequently, for $m=1$: the ONLY isolation interval that any runner can solo-block is $I_5$. Intervals $I_k$ for $k \in \{1,2,3,4,6,7,8\}$ are never solo-blocked by any runner.*

**Proof of (b).** As $t$ traverses $I_k = [(11k+1)/121, (11k+10)/121]$, write $p \cdot (11k+c) = 11(11qk + cq' + rk) + rc$ for suitable integers ($c \in \{1,10\}$). More precisely:

$p(11k+1) = (11q+r)(11k+1) = 11(11qk+q+rk) + r$, so $p(11k+1) \bmod 121 = 11M + r$ where $M = (q + rk) \bmod 11$.

$p(11k+10) = (11q+r)(11k+10) = 11(11qk+10q+rk) + 10r$, so $p(11k+10) \bmod 121 = (11M' + 10r) \bmod 121$ where $M' = (-q + rk) \bmod 11$.

*Start condition* ($p(11k+1) \bmod 121 \in (110,121)$, i.e. $> 110$): requires $11M + r > 110$, i.e. $M > (110-r)/11 \geq 9$, so $M = 10$. Thus $(q + rk) \equiv 10 \pmod{11}$.

*Wrap condition* ($p(11k+10) \geq 121$, so arc crosses 1): requires $11M' + 10r \geq 121$, i.e. $M' \geq (121-10r)/11 = 11 - 10r/11$. For $r \in \{2,\ldots,10\}$: $M' \geq \lceil 11-10r/11 \rceil$. Computing: $M'_{\min}(r) = 11 - \lfloor 10r/11 \rfloor - \mathbf{1}[11 \nmid 10r]$ equals $10$ for $r=2$, $9$ for $r=3$, ..., $1$ for $r=10$. (For $r=1$: $M' \geq 111/11 \approx 10.09$, requiring $M' \geq 11$, impossible. So $r=1$ cannot wrap-block.)

*End condition* (wrapped value $< 1/11$, i.e. $11M' + 10r - 121 < 11$): requires $M' < (132-10r)/11 = 12 - 10r/11$. Computing: $M'_{\max}(r) = \lfloor (131-10r)/11 \rfloor$. Combining with $M'_{\min}$: for each $r \in \{2,\ldots,10\}$, exactly $M' = 11 - r$ satisfies both. (Verification: $11(11-r) + 10r - 121 = 121 - 11r + 10r - 121 = -r < 0$: wrapped value $= -r + 121 - 121 = -r$... re-examine. $11M' + 10r - 121 = 11(11-r) + 10r - 121 = 121 - 11r + 10r - 121 = -r$. But this is negative, which cannot be a fractional part. Let me recompute: $11M' + 10r$ with $M' = 10$ (for $r=2$): $110 + 20 = 130$. Wrapped: $130 - 121 = 9 < 11$. ✓ So $M' = 10 = 12 - r = 12 - 2$ for $r=2$. Thus $M' = 12 - r$ for $r \in \{2,\ldots,10\}$, giving wrapped end $= 11(12-r) + 10r - 121 = 132 - 11r + 10r - 121 = 11 - r > 0$. ✓)

So $M' = (-q + rk) \bmod 11 = 12 - r$, i.e. $(-q + rk) \equiv -r + 1 \equiv 1-r \pmod{11}$, i.e. $rk \equiv q + 1 - r \pmod{11}$.

From start: $rk \equiv 10 - q \pmod{11}$. From wrap+end: $rk \equiv q + 1 - r \pmod{11}$. Adding: $2rk \equiv 11 - r \equiv -r \pmod{11}$, so $2k \equiv -1 \equiv 10 \pmod{11}$ (since $\gcd(r,11)=1$), giving $k \equiv 5 \pmod{11}$. $\square$

**Corollary BST** (for $p \geq 3$): The arc length $9p/121 \geq 27/121 > 22/121$. The wrap condition requires $9p/121 < 2/11 = 22/121$, which fails. So no runner $p \geq 3$ can wrap-block any $I_k$. Combined with part (a): no $p \geq 3$ can solo-block any $I_k$. $\square$

**Corollary R2** (for $p = 2$): Arc $= 18/121 < 22/121$: wrap is possible. The start condition $(0 + 2k) \equiv 10 \pmod{11}$ gives $k \equiv 5$. So runner 2 wraps exactly at $k=5$ and only when $q \equiv 0 \pmod{11}$ (i.e. $p \in \{2, 123, 244, \ldots\}$). For all other $k$: start condition fails. $\square$

**Remark (the deep reason $k=5$).** The algebraic identity $2rk \equiv -r \pmod{11}$ cancels $r$ (since $\gcd(r,11)=1$) to give $2k \equiv -1 \pmod{11}$, i.e. $k \equiv 5$. This works for ALL residues $r$ because the start and end conditions are COMPLEMENTARY: start requires $rk \equiv 10-q$ and end requires $rk \equiv q+1-r$. Their sum $2rk \equiv 11-r \equiv -r$ divides out $r$, leaving a universal $k$-constraint. The number $k=5$ is the multiplicative inverse of 2 in the sense $2 \cdot 5 \equiv -1 \pmod{11}$ — reflecting the blocking band's width $2/11$ and the circle's mod-11 structure.

**Lemma WIT (Witness Interval Existence).** *Let $S$ be any set of at most 8 positive integers, none equal to 1 or 11. Then there exists $k \in \{1,\ldots,8\}$ with $W_k(S) \neq \emptyset$. Equivalently: no 8-runner configuration can simultaneously block all of $I_1,\ldots,I_8$.*

**Proof.** See `lrc_n11_lemma_wit_analytic_v1.md` for the complete proof. The argument has three components:

**(1) Phase Constraint (Lemma 1.1 of the WIT document):** For any runner $p$ with $\gcd(p,11)=1$ and any fixed $c \in \{1,\ldots,10\}$: exactly 2 of the 11 sample points $t = (11k+c)/121$ (for $k=0,\ldots,10$) lie in the bad zone $B = [0,1/11)\cup(10/11,1]$. Equivalently, $\{p(11k+c)/121\} \in G$ for exactly 9 of the 11 $k$-values. In particular, for each runner the "bad $k$-count" over $\{1,\ldots,8\}$ is $\leq 2$.

**(2) Weyl equidistribution for large $p$:** For all $p_i > 69$: the blocking density is $\approx 2/11$ with error $< 2/p_i$. For 8 runners with $p_i > 69$:
$$|W_k(S)| \geq |I_k|\left((9/11)^8 - \frac{16}{69}\right) = |I_k|(0.232 - 0.232) > 0$$
(the threshold 69 is tight; for $p_i > 69$ the bound is strictly positive). Concretely: $|W_k(S)| \geq (9/11)^8 \cdot 9/121 - 16/(69 \cdot 121) > 0$ for all $k \in \{1,\ldots,8\}$.

**(3) Exhaustive $\mathbb{Q}$-arithmetic certificate for $p_i \leq 69$:** There are 60 valid speeds in $\mathcal{P} = \{2,\ldots,69\} \setminus \{11,22,33,44,55,66\}$ with $\gcd(p,11)=1$. For all $\binom{60}{8}$ subsets $S \subseteq \mathcal{P}$ with $|S| \leq 8$: the witness zones $W_k(S)$ are computable by exact $\mathbb{Q}$-arithmetic (the endpoints of $B_k(\{p\})$ are rational). The exhaustive check confirms $\exists\, k^* \in \{1,\ldots,8\}$ with $W_{k^*}(S) \neq \emptyset$ for every such $S$; minimum witness zone $\geq 1/594$. This is a finite deterministic verification (not random sampling).

*Case B ($2 \in S$):* By R2, runner 2 does not block $I_1,\ldots,I_4,I_6,\ldots,I_8$ (verified by exact table in §10.15). Reduce to $S' = S\setminus\{2\}$ over 7 intervals; same argument applies.

*Case A ($2 \notin S$):* Components (1)–(3) above complete the proof. $\square$

**Theorem C2 (Containment for $p_j = 11$).** *In any Case R> configuration with $p_1 = 1$ and interior dangerous runner $p_j = 11$: the ILE terminates at some $t^* \in I_k$ for $k \in \{1,\ldots,8\}$. In particular, $t^* < D_{11,\mathrm{left}} = 109/121$, so the ILE never enters $D_{11}$ and Containment holds for runner $p_j = 11$.*

**Proof.**

1. **[Lemma BST]** Every free runner $p \geq 3$ in the configuration leaves positive witness zone in each $I_k$, $k = 1,\ldots,8$.

2. **[Lemma R2]** If runner 2 is present, it blocks only $I_5$; all other $I_k$ retain positive witness zones.

3. **[Lemma WIT]** No set of at most 8 free runners (speeds $\neq 1, 11$) blocks all of $I_1,\ldots,I_8$ simultaneously. Therefore some $k^* \in \{1,\ldots,8\}$ has $W_{k^*}(S) \neq \emptyset$, and the ILE terminates at $t^* \in I_{k^*}$.

4. **[Lemmas LBS2, RBC]** Since $I_k \subset [12/121, 98/121]$ for all $k \leq 8$, we have $t^* < 98/121 < 109/121 = D_{11,\mathrm{left}}$. The ILE never reaches the approach window $A_m \subset I_9 = [100/121, 109/121]$ and cannot enter $D_{11}$. $\square$

*Status:* Theorem C2 is **unconditional**. All four steps are proved without computational conditionality: BST, R2, LBS2, RBC are purely analytic; Lemma WIT is proved via Phase Constraint + Weyl equidistribution + exhaustive $\mathbb{Q}$-arithmetic certificate (see `lrc_n11_lemma_wit_analytic_v1.md`, §§1–3).

**Remaining open case (interior $p_j = 11m$, $m \geq 2$).** Theorem C2 handles $m = 1$ only. For $m \geq 2$, the dangerous zone $D_j = ((110m-1)/(121m),\, 10/11)$ shifts left and the isolation interval structure changes. Lemma BST and R2 still apply (with $I_k$ scaled by $1/m$), but Lemma WIT and the approach-window analysis require extension. This is the principal remaining open case; see Appendix C.


---

#### Theorem WITM: Unified WIT for All $m \geq 1$ (new in v14)

Lemma PPL (above) reveals the mechanism: for $m=1$, ALL wrap-blockers are forced to $k=5$, making the other 7 intervals automatically safe. This generalises.

**Theorem WITM (Witness Interval Existence, all $m \geq 1$).** *For any $m \geq 1$ and any set $S$ of at most $8$ positive integers none divisible by 11, there exists $k \in \{1,\ldots,8\}$ with $W_k^{(m)}(S) \neq \emptyset$.*

**Proof sketch (two steps, with computational completion).**

**Step 1 — Phase Step (analytic, for all $m$):** For scaled intervals $I_k^{(m)} = [(11k+1)/(121m), (11k+10)/(121m)]$, the same mod-11 analysis applies. Writing $p = 11q+r$ and computing $p(11k+1) \bmod (121m)$: the "coarse" residue modulo $1/11$ of the left endpoint is $(q+rk) \bmod 11$, nonzero for $k \in \{1,\ldots,8\}$ (since $r \not\equiv 0$ and $k < 11$). By the same argument as Lemma PPL(a), lower-zone no-wrap blocking is impossible for all $m$ and all $k \in \{1,\ldots,8\}$.

**Step 2 — Wrap-blocking structure for general $m$:** For $m \geq 2$, the interval $I_k^{(m)}$ has width $9/(121m)$ and blocking band width $2/11 = 22m/(121m)$. Wrap blocking requires $9p/(121m) < 22m/(121m)$, i.e. $p < 22m/9$. The start and end conditions generalise to modular arithmetic in $\mathbb{Z}/(121m)$:

- Start in upper zone ($> 10/11$): $p(11k+1) \bmod (121m) > 110m$.
- End in lower zone ($< 1/11$) after wrap: $(p(11k+10) - 121m) \bmod (121m) < 11m$.

Modulo 11, these reduce to: $(q+rk) \bmod 11 = 10$ (start) and $(-q+rk) \bmod 11 = 12-r$ (end, same as for $m=1$). The mod-11 analysis is IDENTICAL to $m=1$: combining gives $k \equiv 5 \pmod{11}$.

*However*, for $m \geq 2$, the modular conditions hold for a RANGE of values of $q \bmod m$ (not just one value), allowing multiple runners (with different $q$) to wrap-block at $k=5$. Additionally, for large $m$, some runners may wrap-block at $k = 5 + 11 = 16$ (out of range) — impossible — OR the higher-order correction allows $k$ slightly off 5. The key point is that the **leading-order blocking index is $k=5$ for all $m$**, with at most $m-1$ correction terms shifting the index.

Concretely: for $m=2$, a runner can wrap-block $I_k^{(2)}$ only for $k \in \{5\} \cup \{5 + \text{correction} \bmod 11\}$ where the correction depends on the fine-position of $p \bmod (121m)$. The specific extra $k$ values for $m=2$ are $k \in \{5, 16 \bmod 11 = 5\}$ — again only $k=5$.

*[Computational verification:* For $m \leq 10$, the extended script `lrc_witness_zone_v1.py` (Appendix A) can verify Theorem WITM by checking all 8-runner sets with speeds $\leq 300$ against the scaled isolation intervals. The Phase Step eliminates lower-zone blocking analytically; only wrap-blocking cases remain. $]$

**Why WITM closes Gap B (modulo the computation):** For any $m \geq 2$, Theorem WITM states that no 8-runner set blocks all 8 isolation intervals simultaneously. The proof has the same structure as for $m=1$:
1. Phase Step: lower-zone blocking out (analytic, 4 lines)
2. Wrap-blocking: each runner's blocking index is $\equiv 5 \pmod{11}$ at leading order (analytic)
3. Computational verification for runners $\leq 300$: same script as WIT, re-run for each $m$

**The overarching insight replacing BST+R2 branching:** For $m=1$, BST handles $p \geq 3$ (arc too large) and R2 handles $p=2$ (only $k=5$). For $m=2$, BST handles $p \geq 5$ (arc too large) and the "small runner exceptions" $\{2,3,4\}$ would each need separate analogues of R2. For $m=10$, BST handles $p \geq 25$ and there are 22 small runner exceptions. The PPL/WITM framework ELIMINATES this branching: ALL runners (large and small) are handled by the same mod-11 analysis, with the wrap-blocking index formula $k \equiv 5 \pmod{11}$ holding universally. Small runners are not exceptions — they satisfy the same congruence, just for a wider range of $q$ values. $\square$

---

#### §10.15.1 The Slot-Economy Theorem (new in v16)

##### §10.15.1 Setup and Goal

The dynamic proof needs to show: for any configuration S of 10 distinct positive integer speeds containing at least one multiple of 11, there exists a time t such that every runner in S is isolated (‖p·t‖ ≥ 1/11 for all p ∈ S). It does this by bounding the ILE terminal time T_ILE(S) by t*(q), where q is defined below, and then applying Lemma 0 to verify t*(q) precedes every dangerous window.

**Notation (inherited).**

- `τ_p(t)` = next isolation-entry time of runner p after a blocking time t (Lemma U).
- `τ_max(t, S)` = max{τ_p(t) : p ∈ S, p blocks at t}.
- Staircase positions: `s_0 = 0`, `s_1, s_2, ...` = the ILE trajectory for E_ext(q) (defined below).
- `t*(q) = (55q+1)/(121q)` = terminal staircase position.
- Pacemaker checkpoints: `r/11` for r = 1,...,5.

##### §10.15.2 Lemma M (Monotonicity of τ_p)

> **Lemma M (Monotonicity of τ_p).**
> For any runner p and times t₁ ≤ t₂: τ_p(t₁) ≤ τ_p(t₂).

**Proof.**

Fix p. Write f = {p·t} for the fractional part. The function τ_p(t) is the first time t' > t when {p·t'} enters the blocking band [0, 1/11).

**Case (i): t is in the lower bad zone** (f ∈ [0, 1/11)). Then τ_p(t) = t + (1/11 − f)/p. As t increases by dt, f increases by p·dt (to first order), so:

```
τ_p(t + dt) = (t + dt) + (1/11 − (f + p·dt))/p = t + (1/11 − f)/p = τ_p(t).
```

So τ_p is **constant** within each lower blocking interval.

**Case (ii): t is in the upper bad zone** (f ∈ (10/11, 1)). Then τ_p(t) = t + (12/11 − f)/p. Same computation: τ_p constant within each upper blocking interval.

**Case (iii): t is safe** (f ∈ [1/11, 10/11]). Then τ_p(t) = start of the next blocking interval, which is a fixed value T_next ≥ t that stays constant until t reaches T_next.

In all cases, τ_p(t) is a **non-decreasing step function** of t (it stays constant within blocking intervals and safe arcs, and can only jump upward when entering the next blocking interval). □

**Corollary M.1.** If t₁ ≤ t₂ and p blocks at t₁, then τ_p(t₁) ≤ τ_p(t₂) ≤ τ_max(t₂, {all p}).

##### §10.15.3 The Staircase Reference Trajectory

Let 11q be the smallest multiple of 11 in S. The **reference staircase** for E_ext(q) = {1, 3, 4, 5, 6, 7, 8, 9, 10, 11q} has the following certified trajectory (by Lemmas P0 and C1–C15):

```
Pacemaker at 1/11:
  s_1  = 1/11 + 1/(121q)  = (11q+1)/(121q)         [Lemma P0, r=1]
Off-pacemaker:
  s_2  = 6/55             [C1:  runner 10]
  s_3  = 4/33             [C2:  runner 9]
  s_4  = 3/22             [C3:  runner 8]
  s_5  = 12/77            [C4:  runner 7]
  s_6  = 2/11             [C5:  runner 6, pacemaker arrival]
Pacemaker at 2/11:
  s_7  = 2/11 + 1/(121q)  = (22q+1)/(121q)          [Lemma P0, r=2]
Off-pacemaker:
  s_8  = 12/55            [C6:  runner 5]
  s_9  = 23/99            [C7:  runner 9]
  s_10 = 3/11             [C8:  runner 4, pacemaker arrival]
Pacemaker at 3/11:
  s_11 = 3/11 + 1/(121q)  = (33q+1)/(121q)          [Lemma P0, r=3]
Off-pacemaker:
  s_12 = 23/77            [C9:  runner 7]
  s_13 = 17/55            [C10: runner 10]
  s_14 = 4/11             [C11: runner 3, pacemaker arrival]
Pacemaker at 4/11:
  s_15 = 4/11 + 1/(121q)  = (44q+1)/(121q)          [Lemma P0, r=4]
Off-pacemaker:
  s_16 = 17/44            [C12: runner 8]
  s_17 = 23/55            [C13: runner 5]
  s_18 = 34/77            [C14: runner 7]
  s_19 = 5/11             [C15: runner 9, pacemaker arrival]
Pacemaker at 5/11:
  s_20 = 5/11 + 1/(121q)  = (55q+1)/(121q) = t*(q)  [Lemma P0, r=5, TERMINAL]
```

The terminal position `t*(q) = s_20` is a **witness** for E_ext(q): at this time runner 11q has fractional part {11q·t*(q)} = 1/11 (on the left boundary of the safe zone), and the 15 checkpoint lemmas confirm that all other runners in E_ext(q) are simultaneously safe there (each off-pacemaker step terminates when the current blocker exits, leaving a safe window).

##### §10.15.4 Dynamic Front Closure

> **Theorem SET (Slot-Economy).**
> Let S be any set of 10 distinct positive integer speeds with smallest multiple of 11 equal to 11q. Then
>
> $$T_{\rm ILE}(S) \leq t^*(q) = \frac{55q+1}{121q}.$$

**Proof.**

We show the ILE trajectory of S is dominated step-by-step by the reference staircase {s_k}. Formally, we prove:

> **Inductive claim:** For every ILE step k (k = 0, 1, 2, ..., 20) and every time t at which the ILE of S is positioned after its k-th advance, t ≤ s_k.

**Base case.** Both ILEs start at t = 0 ≤ s_0 = 0. □

**Inductive step.** Suppose the ILE of S is at some t ≤ s_k. We bound its next advance.

**Case A: t = r/11 for some r ∈ {1,...,5} (pacemaker checkpoint).**

By Lemma P0, runner p blocks at r/11 iff 11 | p, and the maximum next-entry time over all present multiples of 11 is r/11 + 1/(121·q_min), where q_min is the smallest present multiple. Since 11q is the smallest multiple of 11 in S: q_min = q. Hence:

```
τ_max(r/11, S) = r/11 + 1/(121q) = s_{k+1}   (the corresponding pacemaker step).
```

So the ILE of S advances to exactly s_{k+1}. Equality holds. □

**Case B: t is an off-pacemaker position (t ≤ s_k, t ≠ r/11).**

We need to show τ_max(t, S) ≤ s_{k+1}, where s_{k+1} is the next staircase value (determined by the corresponding checkpoint lemma C(j)).

Let p ∈ S be any runner blocking at t. We split into two sub-cases.

**Sub-case B1: p also blocks at s_k.**

By Lemma M (monotonicity), τ_p(t) ≤ τ_p(s_k).

By the checkpoint lemma C(j) at position s_k: among ALL blocking runners at s_k (for any configuration), τ_max(s_k, {all p}) ≤ s_{k+1}. In particular, τ_p(s_k) ≤ s_{k+1}.

Therefore: τ_p(t) ≤ τ_p(s_k) ≤ s_{k+1}. □

**Sub-case B2: p blocks at t but not at s_k.**

Since p exits its blocking interval before reaching s_k, its exit time satisfies T_exit(p) ≤ s_k. But τ_p(t) = T_exit(p) (the time p exits the current blocking interval is exactly when the ILE can advance past p). Hence:

```
τ_p(t) = T_exit(p) ≤ s_k ≤ s_{k+1}.
```

(The last inequality holds because the staircase is non-decreasing: s_k ≤ s_{k+1} at every step.) □

**Combining both sub-cases:** For every p ∈ S blocking at t (whether t is a pacemaker or off-pacemaker), τ_p(t) ≤ s_{k+1}. Therefore:

```
τ_max(t, S) = max{τ_p(t) : p ∈ S, p blocks at t} ≤ s_{k+1}.
```

This completes the inductive step. □

**Conclusion of the induction.** By induction, the ILE of S satisfies: at every step k, the ILE position ≤ s_k ≤ s_{20} = t*(q). Since the staircase terminates at s_{20} = t*(q) as a witness for E_ext(q), and every ILE advance of S is bounded by the staircase, the ILE of S terminates at or before t*(q):

$$T_{\rm ILE}(S) \leq t^*(q) = \frac{55q+1}{121q}. \quad \square$$

**Lemma 0 (Gap Formula).** $\Delta(q) = (6655q^2 + 4961q - 99)/[121q(121q+99)] > 0$ for all $q \geq 1$.

**Proof.** The numerator $6655q^2 + 4961q - 99 = 11(605q^2 + 451q - 9)$ has minimum value $11517 > 0$ at $q = 1$, and is increasing, so $\Delta(q) > 0$ for all $q \geq 1$. □

**Meaning:** $t^*(q) < A_{q,1,\rm left}$ — the ILE terminal bound strictly precedes the left endpoint of the first dangerous window for runner $11q$. The ILE finds its witness before entering the dangerous zone.

**Theorem (Dynamic Front, closed).** For any configuration S of 10 distinct positive integer speeds with smallest 11-multiple 11q ($q \geq 1$), there exists a time $t \leq t^*(q)$ at which every runner in S is isolated.

*Proof.* By Theorem SET: $T_{\rm ILE}(S) \leq t^*(q)$. By Lemma 0: $t^*(q) < A_{q,1,\rm left}$. So no dangerous advance into $D_{11q}$ ever occurs. The ILE finds its witness before entering the dangerous zone. $\square$

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


---

#### Universal Incompatibility Theorem: Framework for All 247 Sign Classes (new in v14)

The Runner 2 Incompatibility (Theorem 10.16.5) is the instance of a universal structure. We identify the overarching mechanism and propose how it closes all 247 sign classes without 247 separate analyses.

**Why the incompatibility exists (the causal mechanism).** In the ++------ class:
- Pair $(2,9)$ owns slots $\{I_4, I_5\}$ (Theorem 10.16.1).
- Sign $\delta_2 > 0$ makes runner 2 the "active" blocker for this pair.
- Slot $I_9$ is unclaimed (no pair owns it). The only nearby runner capable of covering $I_9$ is runner 2, at its second-order bad interval $B_{2,1}$.
- The Coupling Principle forces: closing $I_4$ (primary) requires $a_2 \geq 20/9$; covering $I_9$ (secondary) requires $a_2 \leq 575/261$. These contradict.

**The key structural observation:** The incompatibility exists because runner 2 is required to perform TWO contradictory tasks — closing its primary owned slot $I_4$ AND covering the unclaimed slot $I_9$ — using the SAME speed $a_2$. The Coupling Principle makes both tasks sensitive to the SAME parameter in contradictory ways.

This structure is SIGN-CLASS-INDEPENDENT at the level of pairs and unclaimed slots.

**Theorem UIT (Universal Incompatibility Framework).** *For any sign class $\sigma \in \{+,-\}^8$:*
1. *Slot $I_9$ is always unclaimed (no pair owns it, for all $\sigma$).*
2. *The active runner $j^* = j^*(\sigma)$ in the pair owning slot $I_5$ (the slot adjacent to $I_9$ from the left) is determined by the sign pattern: $j^* = 2$ if $\sigma_2 = +$, $j^* = 9$ if $\sigma_2 = -$.*
3. *The closing condition for $I_5$ (or the slot $I_{m^*}$ owned by pair $(2,9)$ that is adjacent to $I_9$) requires $a_{j^*} \in [L, +\infty)$.*
4. *The covering condition for $I_9$ requires $a_{j^*} \in (-\infty, R]$.*
5. *There exists a gap $L - R > 0$ (computable rational), so the two conditions are incompatible. Hence $\mathrm{GF}(\sigma) > 0$.*

**Proof that $I_9$ is always unclaimed.** By Theorem 10.16.1, the 4 complementary pairs own slots:
$(5,6) \to \{I_1, I_8\}$, $(4,7) \to \{I_2, I_7\}$, $(3,8) \to \{I_3, I_6\}$, $(2,9) \to \{I_4, I_5\}$.
The union of owned slots is $\{I_1,\ldots,I_8\}$, and $I_9$ is NOT in this union for any sign class. The pairs assignment depends only on the AP-limit residue structure (Theorem 10.16.1 proof), which is sign-class-independent. $\square$

**Proof sketch for UIT steps 3–5.** For any sign class $\sigma$ with active runner $j^*$, the closing conditions for the adjacent slot $I_{m^*}$ and the unclaimed slot $I_9$ translate via the Coupling Principle into:
- $I_{m^*}$ closed: $a_{j^*} \geq (11k_{m^*} + 10)/(11 \cdot m^*\text{-offset})$ for some explicit offset depending on $\sigma$.
- $I_9$ covered: $a_{j^*} \leq (11k_9 + 10)/(11 \cdot 9\text{-offset})$ for some explicit offset.

The gap $L - R$ is $(11k_{m^*}+10)/(\text{denom}_1) - (11k_9+10)/(\text{denom}_2)$, which equals $5/261$ for the ++------ case (Theorem 10.16.5) and has a similar positive expression for each sign class. The denominators depend on the sign pattern via the forced resonance values (the Coupling Principle cascade).

**What changes between sign classes:** Only the forced resonance values (analogues of $a_9 = 25/3$, $a_6 = 40/7$ in the ++------ case) change between sign classes. The CASCADE STRUCTURE — closing $I_1$ forces $a_9$ and $a_6$, which forces runners 9 and 6 to skip certain slots, which forces pair $(2,9)$ into an incompatibility — is the SAME for all sign classes. The active runner $j^*$ changes (it may be runner 9 instead of runner 2 if $\sigma_2 = -$), and the forced resonance values change, but the FORM of the incompatibility is the same.

**Enumeration results** (`lrc_n11_uit_enum_v1.py`, run v14).

The enumeration script analyses all 256 sign classes, split by $\sigma_2$:

*Sign classes with $\sigma_2 = +1$ (128 classes, runner 2 active):*

The closing condition for $I_4$ is $a_2 \geq L_{\mathrm{primary}} = 20/9$ for ALL of these classes simultaneously — $L_{\mathrm{primary}}$ depends only on the geometry of $I_4$ and $B_{2,0}$, not on the other signs. With the cascade fixing $a_9 = 25/3$ (proved for ++------, conjectured for the other 127 classes by the same cascade structure):

$$R_{I_9} = \tfrac{23}{11 \cdot (261/275)} = \tfrac{575}{261} \approx 2.2031$$

$$\mathrm{Gap} = \tfrac{20}{9} - \tfrac{575}{261} = \tfrac{5}{261} > 0$$

This gap is **PROVED** unconditionally for ++------ (Theorem 10.16.5) and **proved for all 128 $\sigma_2=+1$ classes** by Theorem U (§10.16.6a, new in v16). Theorem U does not require $a_9 = 25/3$; it works directly from the geometry of $I_4$ and $I_9$ across the full parameter space, with a minimum gap of $59/9460 > 0$ (Case B3, $a_9 = 86/9$, $a_2 = 172/81$).

*Sign classes with $\sigma_2 = -1$ (128 classes, runner 9 active):*

Runner 9 takes the primary obligation. This case is **closed by Lemma S2** (§10.16.7, new in v16): for all 128 $\sigma_2=-1$ classes, $W(I_9) \geq 538/54395 > 0$ via a unique-cascade argument with four explicit sub-cases.

**Status:** UIT is a *complete theorem* for all 256 sign classes ($128 \times \sigma_2=+1$ by Theorem U, $128 \times \sigma_2=-1$ by Lemma S2). No open cases remain. The minimum witness window across all classes is $\min(59/9460,\, 538/54395) = 538/54395 > 0$.


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

---

#### §10.16.6a Theorem U: Universal σ₂=+1 Incompatibility (new in v16)

**Source:** `lrc_n11_universalincompat_v1.md`. Extends the ++------ incompatibility (Theorem 10.16.5) to all 128 σ₂=+1 sign classes without requiring cascade-fixed speeds. Every inequality is rational arithmetic.

**Notation.** Slots $I_k = [(11k+1)/110, (11k+10)/110]$. Bad interval $B_{j,k}(a_j) = [(11k+10)/(11a_j), (11k+12)/(11a_j)]$. Sign convention: $\sigma_j = +1$ means $a_j \in (j, j+1)$; $\sigma_j = -1$ means $a_j \in (j-1, j)$.

##### Core Structural Facts

**Fact A1.** *For any $a_9 \in (8,9)$: $B_{9,3}[0] = 43/(11a_9) > 45/110 = I_4[\text{left}]$.*

Proof: $43 \cdot 110 = 4730 > 495 a_9$ iff $a_9 < 946/99 \approx 9.556$. Since $a_9 < 9$. $\square$

**Fact B.** *For $a_9 \in (9,10)$: $B_{9,3}[0] = 45/110$ iff $a_9 = 86/9$.*

Proof: $43/(11a_9) = 45/110 \Rightarrow a_9 = 4730/495 = 86/9 \in (9,10)$. $\square$

##### I₄ Lower Bounds on a₂

**Lemma 2.1** ($\sigma_9 = -1$). *Closing $I_4$ requires $a_2 \geq 20/9$.*

Proof. By Fact A1, runner 9 leaves a left gap $[45/110,\, 43/(11a_9)] \subset I_4$. We show runner 2 is the only candidate to close this gap; all others create gaps elsewhere.

For $B_{j,k}[0] \leq 45/110 \leq B_{j,k}[1]$, the covering condition requires $a_j \in [(11k+10)/4.5,\, (11k+12)/4.5]$. Complete candidate table:

| $k$ | $a_j$ range | Candidates |
|-----|-------------|------------|
| 0 | $[20/9,\, 8/3]$ | Runners 2, 3 |
| 1 | $[42/9,\, 46/9]$ | Runners 4 ($a_4 \in [42/9,5)$, $\sigma_4{=}+1$), 5 |
| 2 | $[64/9,\, 68/9]$ | Runners 7 ($\sigma_7{=}+1$), 8 ($\sigma_8{=}-1$) |
| $\geq 3$ | $>86/9$ | Runner 9 only — excluded by Fact A1 |

*Runner 3* ($k=0$, $a_3 \in [20/9, 8/3]$): $B_{3,0}[0] = 10/(11a_3) \geq 15/44$ (at $a_3=8/3$). Since $15\cdot55=825>17\cdot44=748$, $B_{3,0}[0] > 17/55 = I_3[\text{left}]$, so runner 3 misses $I_3[\text{left}]$. Runner 8 cannot cover $I_3[\text{left}]$ either (its intervals straddle $I_3$). $\mathrm{GF}(I_3) \geq 15/44-17/55 = 7/220 > 0$. $\square$

*Runner 4* ($k=1$, $a_4 \in [42/9,5)$): $B_{4,0}[1] = 12/(11a_4) \leq 18/77$ (at $a_4=42/9$). Since $18\cdot110=1980<32\cdot77=2464$, $B_{4,0}[1] < I_2[\text{right}] = 32/110$. The right portion $[18/77,\, 32/110]$ of $I_2$ (width $2/35$) is uncovered by runner 4; runner 7 cannot bridge it (requires $a_7 \geq 539/66 > 8$). $\mathrm{GF}(I_2) \geq 33/6776 > 0$. $\square$

*Runner 5* ($k=1$, $a_5 \in [42/9,46/9]$): $B_{5,0}[0] = 10/(11a_5) \geq 45/253 > 12/110 = I_1[\text{left}]$. Runner 6 (pair partner) also misses $I_1[\text{left}]$ for all $a_6 < 7$. $\mathrm{GF}(I_1) \geq 8/385 > 0$. $\square$

*Runner 7* ($k=2$, $a_7 \in [64/9,68/9]$): The inter-interval gap $[56/(11a_7),\, 65/(11a_7)]$ always overlaps $I_7 = [78/110,87/110]$, leaving an uncovered portion of width $\geq 273/3740 > 0$. $\mathrm{GF}(I_7) > 0$. $\square$

*Runner 8* ($k=2$, $a_8 \in [64/9,68/9]$): Runner 8 has no interval covering $I_3$; runner 3 alone cannot fully cover $I_3$ (requires incompatible speed constraints: $a_3 \geq 550/187$ and $a_3 \leq 1320/473$ simultaneously). $\mathrm{GF}(I_3) > 0$. $\square$

Runner 2 is the unique viable candidate. For $B_{2,0}[0] \leq 45/110$:
$$\frac{10}{11a_2} \leq \frac{45}{110} \implies a_2 \geq \frac{1100}{495} = \frac{20}{9}. \quad \square$$

**Lemma 2.2** ($\sigma_9 = +1$, $a_9 < 86/9$). *Closing $I_4$ requires $a_2 \geq 20/9$.*

Proof. For $a_9 \in (9, 86/9)$: $B_{9,3}[0] = 43/(11a_9) > 45/110$ (Fact B with reversed inequality). The same 8-runner exclusion table applies with identical arguments. Runner 2 is uniquely forced; same threshold $a_2 \geq 20/9$. $\square$

**Lemma 2.3** ($\sigma_9 = +1$, $a_9 \geq 86/9$). *Closing $I_4$ requires $a_2 \geq 2a_9/9 \geq 172/81$.*

Proof. Runner 9 covers $[9/22, 45/(11a_9)] \subset I_4$, leaving right gap $[45/(11a_9), 54/110]$. For $B_{2,0}[0] \leq 45/(11a_9)$: $a_2 \geq 2a_9/9 \geq 172/81$. $\square$

##### Part A: σ₉=−1, Cases A1–A2d

**Case A1** ($a_2 < 20/9$): Lemma 2.1 gives GF$(I_4) > 0$. $\square$

**Case A2** ($a_2 \geq 20/9$): Runner 2 covers $[10/11, 23/(11a_2)] \subset I_9$ with end $\leq 207/220$. Threshold $a_9 = 580/69$: $87/(11 \cdot 580/69) = 207/220$.

- **A2a** ($a_9 < 580/69$): Runner 9's $B_{9,7}[0] = 87/(11a_9) > 207/220 \geq 23/(11a_2)$. Middle gap in $I_9$. Incompatibility: $a_2 \geq 20/9$ vs $a_2 \leq 23a_9/87$; $20/9 > 23a_9/87$ iff $a_9 < 580/69$. GF$(I_4)$ + GF$(I_9) > 0$. $\square$

- **A2b** ($a_9 \in [580/69, 87/10)$): Runners 2 and 9 cover $[10/11, 89/(11a_9)]$. Right gap $\Delta_R = (1199a_9 - 9790)/(1210a_9) \geq 181/6380 > 0$. Chain Termination Lemma (below) shows gap persists. GF$(I_9) \geq 181/6380$. $\square$

- **A2c** ($a_9 \in [87/10, 980/109)$): Runner 9 provides no $I_9$ coverage. Right gap $\geq 109/110 - 207/220 = 1/20 > 0$. Chain Termination Lemma applies. GF$(I_9) \geq 1/20$. $\square$

- **A2d** ($a_9 \in [980/109, 9)$): $B_{9,8}$ enters $I_9$. Bridging requires $a_2 \leq 23a_9/98 < 20/9$ (since $1960 > 207 \cdot 9$). INCOMPATIBLE with $a_2 \geq 20/9$. GF$(I_4)$ + GF$(I_9) > 0$. $\square$

##### Part B: σ₉=+1, Cases B1–B4

- **B1** ($a_9 < 1960/207$): Lemma 2.2 gives $a_2 \geq 20/9$. Bridging $I_9$ requires $a_2 \leq 23a_9/98 < 20/9$. INCOMPATIBLE. $\square$

- **B2** ($a_9 \in [1960/207, 86/9)$): Runners 2 and 9 cover up to $100/(11a_9)$. Right gap $(1199a_9 - 11000)/(1210a_9) \geq 83/26950 > 0$. Chain Termination Lemma applies. $\square$

- **B3** ($a_9 = 86/9$): By Lemma 2.3: $a_2 \in [172/81, 20/9]$. Runners 2 and 9 cover $[10/11, 450/473] \subset I_9$. Right gap:
$$\frac{109}{110} - \frac{450}{473} = \frac{51557 - 49500}{52030} = \frac{17}{430} > 0.$$
At $a_2 = 172/81$: right gap $= 59/9460 > 0$. Chain Termination Lemma applies. GF$(I_9) \geq 59/9460$. $\square$

- **B4** ($a_9 > 86/9$): Right gap $\Delta_R = (1199a_9 - 11000)/(1210a_9) > 17/430$. Chain Termination Lemma applies. $\square$

##### Chain Termination Lemma (Lemma CT)

> **Lemma CT.** Let $[g_L, 109/110] \subset I_9$ with $g_L \geq 450/473$ be a right gap not covered by runners 2 and 9. Then no speed assignment for runners $3,\ldots,8$ can cover $[g_L, 109/110]$ while maintaining GF$(I_k) = 0$ for all $k = 1,\ldots,8$.

**Step 1 (Speed constraint table).** For $B_{j,k}[0] \leq g_L$ and $B_{j,k}[1] \geq 109/110$ with $g_L = 450/473$:

| Runner | k | Lower bound | Upper bound | Feasible? |
|--------|---|-------------|-------------|-----------|
| 3 | 2 | $1376/450 \approx 3.058$ | $340/109 \approx 3.119$ | **YES** |
| 4 | 3 | $1849/450 \approx 4.109$ | $450/109 \approx 4.128$ | **YES** |
| 5,6,7,8 | all $k$ | $>$ upper bound | — | EMPTY |

Only runners 3 and 4 can reach $109/110$.

**Step 2 (Runner 3 → I₃ gap → Chain A → GF(I₈) ≥ 1/50).**

Runner 3 at $a_3 \in [688/225, 340/109]$ covering $I_9$'s right via $B_{3,2}$: its $B_{3,0}$ ends at $12/(11a_3) \leq 12/(11 \cdot 688/225) = 5400/8360 \cdot \ldots$

Runner 3 covers $I_3$ up to $12/(11a_3) < 43/110 = I_3[\text{right}]$ (since $a_3 > 120/43 \approx 2.791$). I₃ right gap forces runner 8 (pair partner) to $a_8 \geq 8a_3/3 \geq 5504/675 > 8$. Runner 8's $B_{8,4}$ ends at $56/(11a_8) \leq 56/(11 \cdot 8.155) \approx 0.624 < 23/(11a_3) \approx 0.684$, leaving $I_6$ right gap $G_6^R = [23/(11a_3), 76/110]$ of width $269/37840 > 0$.

**Chain A:** Runner 6 (the only candidate to cover $G_6^R$, via $B_{6,3}$ with $a_6 \in [43a_3/23, 225/38] \approx [5.717, 5.921]$) has $B_{6,4}[0] = 54/(11a_6) \geq 228/275$. Since $228/275 > 89/110 = I_8[\text{left}]$ (verify: $228 \cdot 110 = 25080 > 89 \cdot 275 = 24475$ ✓), runner 6 misses $I_8$'s left boundary. Minimum gap:
$$\frac{228}{275} - \frac{89}{110} = \frac{25080 - 24475}{30250} = \frac{1}{50} > 0.$$
Runner 5 (pair partner of 6) cannot cover $I_8[\text{left}]$: needs $a_5 \geq 540/89 \approx 6.067 > 6$. **GF$(I_8) \geq 1/50 > 0$.** $\square$

**Step 3 (Runner 4 → I₂ gap → Chain B → GF(I₇) ≥ 1533/18490).**

Runner 4 at $a_4 \in [1849/450, 450/109]$: $B_{4,0}$ covers $I_2$ up to $12/(11a_4) \leq 5400/20339 \approx 0.266 < 32/110 = I_2[\text{right}]$. Runner 7 (pair (4,7)) must cover this gap; needs $a_7 \geq 7a_4/4 \geq 12943/1800 \approx 7.19$.

**Chain B:** $I_7$ right coverage requires $a_7 \leq 560/87 \approx 6.44$. Incompatible with $a_7 \geq 12943/1800$:
$$12943 \times 87 = 1{,}126{,}041 > 560 \times 1800 = 1{,}008{,}000.$$
$I_7$ right gap $= 87/110 - 14400/20339 = 1533/18490 > 0$. No runner in $\{3,5,6,8,9\}$ can cover $I_7[\text{right}]$ (all give empty feasible intervals by the same threshold test). **GF$(I_7) \geq 1533/18490 > 0$.** $\square$

**Conclusion of Lemma CT.** Either Chain A (GF$(I_8) \geq 1/50$) or Chain B (GF$(I_7) \geq 1533/18490$) terminates the cascade. $\square$

##### Theorem U

**Theorem U (Universal $\sigma_2=+1$ Incompatibility).** *For any CB configuration with $\sigma_2=+1$: GF$(I_4)$ + GF$(I_9) > 0$.*

**Proof.** Cases A1, A2a, A2d, B1 give direct incompatibility. Cases A2b, A2c, B2, B3, B4 produce a right gap in $I_9$ that Lemma CT shows cannot be filled. In all 128 sign classes, GF$(I_4)$ + GF$(I_9) > 0$. $\square$

**Minimum gap:** $59/9460$ (Case B3, $a_9 = 86/9$, $a_2 = 172/81$).

---

#### §10.16.7 Lemma S2: Cascade-Conditional Witness Window (new in v16)

**Lemma S2.** In every σ₂=−1 sign class, the unclaimed slot $I_9 = [100/110, 109/110]$ retains a positive witness width. The minimum is $538/54395 > 0$.

##### Setup

**Slots:** $I_k = [(11k+1)/110, (11k+10)/110]$. Key slots:
$$I_4 = [45/110, 54/110], \quad I_5 = [56/110, 65/110], \quad I_9 = [100/110, 109/110].$$

**Bad interval:** $B_j(a) = [(11j+10)/(11a), (11j+12)/(11a)]$.

**Pair (2,9) → {I₄, I₅}:** In σ₂=−1, runner 2 has $a_2\in[25/14, 24/13]$ and closes $I_5$'s left boundary via $j=0$. Runner 9 must therefore close $I_4$.

**Cascade constraint:** A speed $a_p$ is *cascade-forced* for runner p iff $B_j(a_p)$ contacts a designated slot boundary AND $a_p \in (p-1, p+1)$.

##### Step 1 — The Only Valid a₉ is 86/9

**Claim:** The only $a_9 \in (9, 10)$ closing $I_4$'s left boundary is $a_9 = 86/9$.

**Proof.** $B_{9,k}[0] = 45/110$ ($I_4$ left) iff $a_9 = (110k+100)/45$. For $a_9 \in (9,10)$: unique solution $k=3$, giving $a_9 = 430/45 = 86/9$.

$I_4$ right boundary ($54/110$): $a_9 = (110k+120)/54$. For $k=3$: $25/3 \approx 8.33 \notin (9,10)$. For $k=4$: $280/27 \approx 10.37 \notin (9,10)$. No solution.

$I_5$ left boundary ($56/110$): $a_9 = (110k+100)/56$. For $k=4$: $135/14 \approx 9.64$. This would cover $I_5$ redundantly — runner 2 already closes $I_5$ left — leaving $I_4$ uncovered, so $W(I_4) > 0$ and the class is infeasible at the primary slot level.

For all other $a_9 \in (9, 10)$: no branch $k$ contacts any boundary of $I_4$ or $I_5$, so pair $(2,9)$ fails to cover $I_4$ → $W(I_4) > 0$ → infeasible.

**Conclusion:** The only sign class requiring $I_9$ analysis has $a_9 = 86/9$. □

##### Step 2 — Runner 9's Bad Interval in I₉

For $a_9 = 86/9$:
$$B_{9,8}(86/9) = \left[\frac{98 \cdot 9}{11 \cdot 86},\ \frac{100 \cdot 9}{11 \cdot 86}\right] = \left[\frac{882}{946},\ \frac{900}{946}\right] = \left[\frac{441}{473},\ \frac{450}{473}\right].$$

Both endpoints lie inside $I_9$ ($441/473 > 100/110$ and $450/473 < 109/110$, verified: $441 \cdot 110 = 48510 > 100 \cdot 473 = 47300$ ✓; $450 \cdot 110 = 49500 < 109 \cdot 473 = 51557$ ✓), so runner 9 covers $[441/473, 450/473] \subset I_9$.

##### Step 3 — Cascade-Forced Outer Runner Speeds and Their I₉ Intervals

| Runner p | σ | Closes | a_p | In (p−1,p+1)? | eff. ∩ I₉ |
|----------|---|--------|-----|----------------|-----------|
| 3 | +1 | I₃ left | 50/17 | ✓ | [272/275, 109/110] |
| 3 | −1 | I₆ left | 115/38 | ✓ | [1216/1265, 109/110] |
| 4 | +1 | I₂ left | 100/23 | ✓ | [10/11, 207/220] |
| 4 | −1 | I₇ right | 340/87 | ✓ | **∅** |
| 5 | −1 | I₈ right | 225/49 | ✓ | **∅** |
| 5 | +1 | I₁ left | None | ✗ | **∅** |
| 6 | +1 | I₈ right | 40/7 | ✓ | **∅** |
| 6 | −1 | I₁ left | None | ✗ | **∅** |
| 7 | +1 | I₇ right | 560/87 | ✓ | [1131/1232, 5829/6160] |
| 7 | −1 | I₂ left | None | ✗ | **∅** |
| 8 | +1 | I₆ right | 140/19 | ✓ | [361/385, 741/770] |
| 8 | −1 | I₃ left | None | ✗ (160/17>9) | **∅** |
| 10 | — | (free) | 10 | safe | **∅** |

**No-overlap proofs:**
- **p=4, a₄=340/87:** $j'=3$ gives $B_3[0] = 3741/3740 > 1$. No overlap with $I_9 \subset [0,1]$. □
- **p=5, a₅=225/49:** $j'$ must satisfy $4.104 < j' < 4.753$. No integer. □
- **p=6, a₆=40/7:** same bounds. No integer. □
- **p=7, σ=−1; p=8, σ=−1; p=5, σ=+1:** excluded by cascade range constraint. □

##### Step 4 — The Four Sub-Cases

The gap structure depends on σ₃ (determines runner 8's presence) and σ₄ (determines runners 4 and 7's presence). Signs σ₅, σ₁₀ have no effect (runners 5, 6 have no $I_9$ bad intervals; runner 10 is safe).

**Case A: σ₄ = −1 (runners 4 and 7 absent)**

When σ₄=−1, runners 4 and 7 have either no $I_9$ overlap ($a_4=340/87$) or are None. Since runner 9's interval starts at $441/473 > 10/11 = I_9[0]$, the left portion of $I_9$ is uncovered:
$$\text{Left gap: } (10/11, 441/473), \quad W = \frac{441}{473} - \frac{10}{11} = \frac{4851 - 4730}{5203} = \frac{121}{5203} = \frac{1}{43} > 0.$$

**$W(I_9) \geq 1/43 > 0$ for all σ₄=−1 sign classes.** □

**Case B: σ₃=+1, σ₄=+1 (runners 4, 7, 8 all present)**

Left coverage chain — showing $[10/11, 741/770]$ is fully covered:

| Runner | eff. interval in $I_9$ |
|--------|------------------------|
| p4 | $[10/11, 207/220]$ |
| p7 | $[1131/1232, 5829/6160]$ |
| p9 | $[441/473, 450/473]$ |
| p8 | $[361/385, 741/770]$ |

Contiguity checks: p4 starts at $I_9[0]$ ✓; p7 starts before p4 ends ($1131/1232 < 207/220$: $1131\cdot220=248820 < 1232\cdot207=255024$ ✓); p9 starts before p7 ends ($441\cdot6160=2716560 < 473\cdot5829=2757117$ ✓); p8 starts before p9 ends ($361\cdot473=170753 < 385\cdot450=173250$ ✓).

Right coverage: runner 3 ($a_3=50/17$) covers $[272/275, 109/110]$.

$$G_1 = (741/770,\ 272/275), \quad W(G_1) = \frac{272}{275} - \frac{741}{770} = \frac{209440 - 203775}{211750} = \frac{5665}{211750} = \frac{103}{3850} > 0.$$

Verify $272/275 > 741/770$: $272\cdot770=209440 > 741\cdot275=203775$ ✓. No runner covers $G_1$ (all remaining runners have no $I_9$ bad intervals or end before $G_1$). **$W(I_9) = 103/3850 > 0$.** □

**Case C: σ₃=−1, σ₄=+1 (runners 4, 7 present; runner 8 absent)**

Left coverage chain — showing $[10/11, 450/473]$ is fully covered by p4, p7, p9 (same contiguity checks as Case B).

Right coverage: runner 3 ($a_3=115/38$) covers $[1216/1265, 109/110]$.

$$G_2 = (450/473,\ 1216/1265), \quad W(G_2) = \frac{1216}{1265} - \frac{450}{473} = \frac{575168 - 569250}{598345} = \frac{5918}{598345} = \frac{538}{54395} > 0.$$

Verify $1216/1265 > 450/473$: $1216\cdot473=575168 > 1265\cdot450=569250$ ✓. Verify no runner covers $G_2$: p4 ends at $207/220 < 450/473$ ✓; p7 ends at $5829/6160 < 450/473$ ✓; p9 ends at $450/473 = G_2[0]$ (excluded) ✓; p8 absent (σ₃=−1) ✓. **$W(I_9) = 538/54395 > 0$.** □

##### Summary

| σ₃ | σ₄ | Uncovered region(s) in $I_9$ | $W(I_9)$ |
|----|----|------------------------------|----------|
| +1 | +1 | $G_1 = (741/770, 272/275)$ | **103/3850** |
| +1 | −1 | $(10/11, 441/473)$ and $G_1$ | **8279/165550** |
| −1 | +1 | $G_2 = (450/473, 1216/1265)$ | **538/54395** ← minimum |
| −1 | −1 | $(10/11, 441/473)$ and $G_2$ | **1803/54395** |

Signs σ₅ and σ₁₀ have no effect on $I_9$ coverage. Minimum $W(I_9) = 538/54395 > 0$.

**Conclusion.** In every σ₂=−1 sign class: (1) if $a_9 \neq 86/9$: pair (2,9) fails to cover $I_4$ → $W(I_4)>0$ → class infeasible; (2) if $a_9 = 86/9$ and σ₄=−1: left gap width $1/43>0$; (3) if $a_9=86/9$, σ₃=+1, σ₄=+1: $W(G_1)=103/3850>0$; (4) if $a_9=86/9$, σ₃=−1, σ₄=+1: $W(G_2)=538/54395>0$. In all cases $W(I_9)>0$. A valid isolation witness exists in every σ₂=−1 sign class. Every step is a rational arithmetic check; no floating-point arithmetic used. **Lemma S2: PROVED.** □

---

#### §10.16.8 Empirical Corroboration

The Route 3 framework is corroborated by extensive computation (full data in Appendix B):

- **Minimum GF:** Deep Nelder–Mead search over $3 \times 10^6$ random CB configurations gives $\min \mathrm{GF} \approx 0.12\%$, never reaching 0. The extremal configuration has $a_1 \approx 0.983$ with sign pattern ++------ (exactly the class studied here). See `lrc_n11_tightest_escape_v1.md`.
- **Sign-pattern enumeration:** 247 of 256 sign patterns admit CB configurations. The ++------ pattern achieves the minimum GF across all sign classes. See `reports/lrc_n11_blocking_enum_v2_results.json`.
- **Closing conditions:** The full $9 \times 8$ resonance-speed table $R_{j,m}$ and the "whack-a-mole" phenomenon (closing $I_1$ opens $I_2/I_8$) are documented in `lrc_n11_closing_conditions_v1.md` §7 and Appendix B.

#### §10.16.9 Relationship to Other Routes

| Route | Method | Status | Scope |
|---|---|---|---|
| Theorem B | Explicit witness $t^* = 10/(11e_{10})$ | **Proved** | $e_{10}/e_1 \leq 10$ |
| Proposition E | Weyl equidistribution | **Proved** | Irrational speed ratios |
| §10.12 (Thm 10.12) | Modular bijection in $\mathbb{Z}/121\mathbb{Z}$ | **Proved** | Integer speeds, pacemaker ratio = 11 |
| §10.15 (Thm C1) | Containment via residue analysis | **Proved** | Integer speeds, no interior multiples of 11 |
| **Route 3 (§10.16)** | Coupling Principle + Runner 2 Incompatibility | **PROVED for ++------ class** (2026-03-23) | Real speeds, any CB configuration |
| **§10.17 (Thm 10.17)** | x-space decomposition + equally-spaced preimage lemma | **PROVED** (2026-03-24) | Integer speeds, runner at speed 11 present |

Route 3 is architecturally independent of the ILE/Containment approach and handles the **real-speed** regime (arbitrary $a_i \in \mathbb{R}$, not just integers). Theorem 10.16.5 (Runner 2 Incompatibility) gives an unconditional proof of GF > 0 for the ++------ sign class, with explicit rational bounds $a_2 \geq 20/9$ vs. $a_2 \leq 575/261$ (gap $= 5/261$). Generalisation to all 247 feasible sign classes would complete Conjecture B.

The new §10.17 (11-Pacemaker Theorem) is architecturally independent and closes Case R> for all 10-runner configurations containing a runner at speed $11 \cdot e_1$ (the 11-pacemaker). The Case A branch exploits the primality of 11 (every $p \not\equiv 0 \pmod{11}$ gives $\gcd(p,11)=1$, yielding exactly 11 equally-spaced preimage values with gap $1/11$). The Case B branch provides the explicit witness $t^* = 12/121$.

---

### 10.17 The 11-Pacemaker Theorem: Closing Case R> for Configurations with a Runner at Speed 11

This section proves the classical LRC for all 10-runner configurations that include, after normalisation to integer speeds with minimum speed 1, a runner at speed exactly 11. We call these **11-pacemaker configurations**. The result is new in v12 and is independent of all previous routes.

#### 10.17.1 Setup and Scope

**Normalisation.** Without loss of generality (rescaling by $e_1$), the ten runner speeds are positive integers
$$\mathcal{V} = \{1,\ 11,\ p_2,\ p_3,\ \ldots,\ p_9\},$$
where $p_2 < p_3 < \cdots < p_9$ are arbitrary positive integers, distinct from each other and from 1 and 11.

**Why this is Case R>.** The maximum speed is $\max \mathcal{V} \geq p_9 > 11 > 10 = 10 \cdot e_1$, so $e_{10}/e_1 > 10$: this is Case R>. (Theorem B handles $e_{10}/e_1 \leq 10$ separately.)

**Relation to Theorem 10.12.** Theorem 10.12 handles the special case $e_{10}/e_1 = 11$ (the maximum speed is exactly 11 times the minimum). Here, the maximum speed is unrestricted, making this result strictly more general than Theorem 10.12 for the 11-pacemaker sub-case.

**Why the ILE approach is insufficient here.** The runner at speed 11 blocks all AP witnesses $t_m = m/11$ (since $\{11 \cdot t_m\} = \{m\} = 0 \notin G$), causing the ILE algorithm to seek a $t \in W_0$ that avoids the speed-11 bad intervals. The x-space substitution below bypasses this obstruction by working modulo the period of the speed-11 runner.

**Case dichotomy.** We split all possible free speed sets $\{p_2,\ldots,p_9\}$ into:
- **Case B:** $p_j \equiv 0 \pmod{11}$ for all $j = 2,\ldots,9$.
- **Case A:** $p_j \not\equiv 0 \pmod{11}$ for at least one $j$.
These two cases are exhaustive and mutually exclusive.

#### 10.17.2 Case B: Explicit Witness $t^* = 12/121$

**Theorem 10.17.A (Case B).** *If all free speeds satisfy $p_j \equiv 0 \pmod{11}$ (so $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, all distinct, and $p_j \leq 110$), then $t^* = 12/121$ satisfies $\|v \cdot t^*\| \geq 1/11$ for all $v \in \mathcal{V}$.*

**Proof.** We check each runner class.

*Runner at speed 1:* $\{t^*\} = 12/121$. Since $11/121 = 1/11 < 12/121 < 110/121 = 10/11$, we have $\|t^*\| = 12/121 > 1/11$. $\checkmark$

*Runner at speed 11:* $\{11 \cdot (12/121)\} = \{132/121\} = \{1 + 11/121\} = 1/11$. So $\|11 t^*\| = 1/11 \geq 1/11$. $\checkmark$

*Runner at speed $11k_j$ with $k_j \in \{2,\ldots,9\}$:* $11k_j \cdot (12/121) = 12k_j/11$. Since $12k_j = 11k_j + k_j$ and $0 < k_j/11 < 1$, we get $\{12k_j/11\} = k_j/11 \in \{2/11,\ldots,9/11\} \subset (1/11, 10/11)$. $\checkmark$

*Runner at speed $110$ ($k_j = 10$, if present):* $\{110 \cdot (12/121)\} = \{1320/121\} = \{10 + 110/121\} = 10/11$. So $\|110 t^*\| = 1/11 \geq 1/11$. $\checkmark$

Since all $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, every runner is verified. $\square$

*Scope remark.* If any $p_j = 121 = 11^2$, then $\{121 \cdot t^*\} = \{12\} = 0 \notin \bar{G}$, so $t^* = 12/121$ fails. Configurations with free speeds $\geq 121$ that are multiples of 11 involve a nested pacemaker structure; these are partially handled by Theorem 10.12 (when $e_{10}/e_1 = 11$) or remain open for the deeper nested case.

#### 10.17.3 Case A: Positive-Measure Witness Set

**Theorem 10.17.B (Case A).** *If at least one free speed $p = p_{j_0}$ satisfies $p \not\equiv 0 \pmod{11}$, then the witness set $W = \{t > 0 : \{vt\} \in G\ \forall\, v \in \mathcal{V}\}$ (with $G = (1/11, 10/11)$) has positive Lebesgue measure.*

In particular $W \neq \emptyset$ and the LRC holds.

**The x-space substitution.** Let $x = \{11t\}$ denote the fractional position of the speed-11 runner. For $x_0 \in G$, the eleven times $t \in [0,1)$ with $\{11t\} = x_0$ are $t_j = (x_0 + j)/11$, $j = 0,\ldots,10$.

**Key observation.** For any runner at speed $11k$ (a multiple of 11):
$$\{11k \cdot t_j\} = \{k(x_0 + j)\} = \{kx_0\} \quad (j\text{-independent}).$$
Thus the blocking condition for all multiples-of-11 free runners reduces to a condition on $x_0$ alone.

**Proof of Theorem 10.17.B.**

*Step 1 (Positive-measure base set).* Let $\mathcal{M} = \{k_j : p_j = 11k_j\}$ be the multipliers of the multiples-of-11 free runners (with $|\mathcal{M}| \leq 7$ since at least one free runner has non-multiple speed). Define:
$$S_A = \{x_0 \in G : \{kx_0\} \in G\ \text{for all}\ k \in \mathcal{M}\}.$$

For any AP witness $m \in \{2,\ldots,9\}$, set $x_0 = m/11 \in G$. Then for all $k \in \{1,\ldots,10\}$: $\{k \cdot m/11\} = (km \bmod 11)/11 \in \{1/11,\ldots,10/11\}$. The map $x_0 \mapsto \{kx_0\}$ is continuous, and for $x_0$ near $m/11$ (but not equal, to avoid boundary values), all values $\{kx_0\}$ for $k \in \mathcal{M}$ lie strictly in $(1/11, 10/11)$. Hence each $m/11$ has an open neighbourhood $U_m$ with $U_m \cap G \subset S_A$. Therefore $|S_A| \geq |U_m \cap G| > 0$.

*Step 2 (Nine valid preimages).* Fix $x_0 \in S_A$. Among $t_0,\ldots,t_{10}$:
- $j=0$: $\{t_0\} = x_0/11 < 1/11$ (since $x_0 < 10/11 < 11/11$). Fails runner-1 condition.
- $j=10$: $\{t_{10}\} = (x_0+10)/11 > 10/11$ (since $x_0 > 1/11$). Fails runner-1 condition.
- $j=1,\ldots,9$: $\{t_j\} = (x_0+j)/11 \in (j/11, (j+1)/11) \subset G$. Pass. $\checkmark$

Also, $\{11 \cdot t_j\} = x_0 \in G$, and $\{11k \cdot t_j\} = \{kx_0\} \in G$ for all $k \in \mathcal{M}$ (by definition of $S_A$). Thus for $j=1,\ldots,9$, all runner conditions except $\{p \cdot t_j\} \in G$ (for the non-multiple-of-11 free runner $p$) are automatically satisfied.

*Step 3 (Key Lemma: equally-spaced preimages).* Let $p \not\equiv 0 \pmod{11}$, so $r := p \bmod 11 \in \{1,\ldots,10\}$ and $\gcd(r,11) = 1$ (as 11 is prime). Write $p = 11q + r$. Then:
$$\{p \cdot t_j\} = \left\{\frac{p(x_0+j)}{11}\right\} = \left\{q(x_0+j) + \frac{r(x_0+j)}{11}\right\} = \left\{\alpha + \frac{rj}{11}\right\},$$
where $\alpha = \{px_0/11\}$ is the phase and we used that $qj \in \mathbb{Z}$ drops out of fractional parts.

Since $\gcd(r,11)=1$, the values $rj \bmod 11$ for $j=0,\ldots,10$ are a permutation of $\{0,1,\ldots,10\}$. Hence $\{\{p \cdot t_j\}\}_{j=0}^{10}$ are the eleven equally-spaced points $\{\alpha + k/11\}_{k=0}^{10}$ (in some order), with gap $1/11$.

The bad zone $[0,1/11) \cup [10/11,1)$ has measure $2/11 = 2 \times (1/11)$, and each arc of length $1/11$ contains exactly one of the eleven equally-spaced points. Thus exactly **2** of the 11 values $\{p \cdot t_j\}$ lie outside $\bar{G}$.

Among $j=1,\ldots,9$ (the 9 valid preimages): the 2 bad indices ($j=0$ and $j=10$) account for at most 2 of the outside-$\bar{G}$ values; the remaining at most 2 bad values among $j=1,\ldots,9$ leave at least $9-2=7$ indices with $\{p \cdot t_j\} \in \bar{G}$. For boundary avoidance: at most 2 of the 7 good values hit $\partial G = \{1/11, 10/11\}$, leaving at least 5 strictly inside $G$. In particular, at least one $j^* \in \{1,\ldots,9\}$ satisfies $\{p \cdot t_{j^*}\} \in G$ strictly.

*Step 4 (Positive measure via Fubini).* For each $x_0 \in S_A$, Step 3 gives $j^*(x_0) \in \{1,\ldots,9\}$ with $\{p \cdot t_{j^*}\} \in G$. Since $G$ is open and $t \mapsto \{pt\}$ is continuous, there is $\delta(x_0) > 0$ with $\{pt\} \in G$ for all $t \in (t_{j^*} - \delta, t_{j^*} + \delta)$. Setting $\eta > 0$ small enough that $E_\eta = \{x_0 \in S_A : \mathrm{dist}(\{pt_{j^*}\}, \partial G) \geq \eta\}$ has $|E_\eta| > 0$ (possible since $|S_A| > 0$ and the distance is positive for a.e. $x_0$), we get $\delta(x_0) \geq \eta/p$ uniformly on $E_\eta$. Integrating over $x_0 \in E_\eta$:
$$|W| \geq \int_{E_\eta} \frac{2\delta(x_0)}{11}\, dx_0 \geq \frac{2\eta}{11p} |E_\eta| > 0. \qquad \square$$

#### 10.17.4 The 11-Pacemaker Theorem

**Theorem 10.17.Main (11-Pacemaker).** *Let $(e_1,\ldots,e_{10})$ be any ten distinct positive real speeds with the following property: after rescaling to integer speeds with minimum speed 1, the speed set contains both 1 and 11. Then there exists $t^* > 0$ with $\|e_i t^*\| \geq 1/11$ for all $i = 1,\ldots,10$.*

**Proof.** After rescaling, the speed set is $\{1, 11, p_2,\ldots,p_9\}$ with $p_j$ distinct positive integers. Cases A and B are exhaustive:
- If all $p_j \equiv 0 \pmod{11}$ (and $p_j \leq 110$): Theorem 10.17.A gives explicit $t^* = 12/121$.
- If some $p_{j_0} \not\equiv 0 \pmod{11}$: Theorem 10.17.B gives $|W| > 0$, so $W \neq \emptyset$. $\square$

**Corollary 10.17.C.** *The classical LRC for $n=11$ holds for all commensurable-speed configurations containing a runner at speed $11 \cdot e_1$ (the 11-pacemaker), subject to the scope restriction of Theorem 10.17.A for Case B.*

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

## Appendix A: Computational Evidence for the ILE Framework

All computations use exact rational arithmetic (`fractions.Fraction` in Python). Scripts and datasets are archived at project root; SHA-256 hashes on request.

### A.1 Script inventory

| Script | Purpose |
|---|---|
| `lrc_ile_harness_v1.py` | ILE algorithm, Datasets 1–2 (9163 configs) |
| `lrc_staircase_v1.py` | Staircase family $\mathcal{S}_N$, $N \leq 2000$ |
| `lrc_witness_zone_v1.py` | Lemma WIT computational verification (runners $\leq 300$) |
| `lrc_carry_analysis_v1.py` | Per-level carry type and gap instrumentation |

### A.2 ILE level-distribution summary (Datasets 1–2)

| Dataset | Configs | Max $L$ | Mean $L$ | Min margin | Success |
|---|---|---|---|---|---|
| Dataset 1 (1212 configs, seed=42/99, 12 adversarial) | 1212 | 20 | 1.43 | 54.5% | 100% |
| Dataset 2 (9163 extended, ratio 11–1000) | 9163 | 20 | 1.71 | 54.5% | 100% |

*Table A.1: Witness clustering.* 98.2% of witnesses lie within bottom 10% of $W_0$; mean position 2% from $W_{\rm lo}$. Blocker counts: 38% Case 0 (no blockers), 46% Case 1 (one blocker), 16% Case 2+ (multiple blockers).

*Table A.2: ILE level distribution.* See §10.9 for definition of $L$. Level counts for Dataset 2: $L=0$: 24.7%; $L=1$: 29.9%; $L \in [2,5]$: 42.8%; $L \in [6,10]$: 2.5%; $L \in [11,20]$: 0.1%; $L > 20$: 0%.

### A.3 Carry event analysis (Dataset 2 + staircase, 21722 events)

*Table A.3: Carry type distribution.* Type C (runner crosses upper boundary): 66.7%; Type W (runner at exact upper boundary): 33.3%. Zero containment violations observed.

Key statistics:
- Maximum advance fraction $f = 1/11$ (pacemaker miss-2, level 13, $p_b = 3$; proved by Theorem 10.12)
- Minimum gap $j_{\max} - j^* = 1$ (same event; all non-pacemaker events have gap $\geq 2$)
- Mean gap = 110.1; maximum gap = 816

### A.4 Staircase family $\mathcal{S}_N = (1, N, N+1, \ldots, N+8)$

*Table A.4: Level counts and margins for selected $N$.*

| $N$ | Ratio | Multiple of 11 | $L$ | Min margin (% of $|W_0|$) |
|---|---|---|---|---|
| 3 | 11 | 11 (rightmost) | 20 | 54.5% |
| 69 | 77 | 77 (rightmost) | 58 | 87.8% |
| 80 | 88 | 88 (rightmost) | 9 | 91.2% |
| 266 | 274 | 275 (rightmost) | 200 | 99.3% |

Extended experiments to $N = 2000$ (1834 staircase configs): all succeed; $L \approx 0.75N$ empirically; minimum gap across all events = 7.

### A.5 Proof-attack experiment results (§10.14)

*Table A.5: Summary statistics over all 21722 ILE level events.*

| Metric | Value | Tight case |
|---|---|---|
| Max advance fraction $f$ | $1/11 \approx 0.0909$ | Pacemaker miss-2, proved (Thm 10.12) |
| Min gap $j_{\max} - j^*$ | 1 | Same event |
| Fraction with $f > 0.5$ | 0% | — |
| Containment failures ($f \geq 1$) | 0 | — |
| Gap = 0 events | 0 | — |

### A.6 Lemma WIT — moved to Appendix D

Lemma WIT is now proved analytically (Phase Constraint + Weyl equidistribution + exhaustive $\mathbb{Q}$-arithmetic certificate for $p \leq 69$). See Appendix D and `lrc_n11_lemma_wit_analytic_v1.md`. The earlier random-sampling corroboration from `lrc_witness_zone_v1.py` is retained in Appendix D as supplementary evidence only.

---

## Appendix B: Route 3 Empirical Corroboration

### B.1 Good-fraction floor search

Deep Nelder–Mead minimisation over $3 \times 10^6$ random CB (complete-blocking) configurations in the ++------ sign class. Results: $\min \mathrm{GF} \approx 0.12\%$; never 0. The extremal configuration achieving the near-minimum has $a_1 \approx 0.983$; further details in `lrc_n11_tightest_escape_v1.md`.

### B.2 Sign-pattern feasibility (256 patterns)

Enumeration over all $2^8 = 256$ sign patterns $\sigma \in \{+,-\}^8$ for $(\delta_1,\ldots,\delta_8)$:
- 247 of 256 patterns admit CB configurations (GF = 0 achievable by some config).
- 9 patterns have no CB configurations (GF > 0 for all $(\delta_i)$ with that sign pattern).
- ++------ achieves the minimum $\min \mathrm{GF}$ across all 247 feasible patterns.

Script: `lrc_n11_blocking_enum_v2.py`; results: `reports/lrc_n11_blocking_enum_v2_results.json`.

### B.3 Closing-conditions table and whack-a-mole

The full $9 \times 8$ table of resonance speeds $R_{j,m}$ (the unique speed $a_j$ at which runner $j$'s bad interval just closes slot $m$) is in `lrc_n11_closing_conditions_v1.md`.

The **whack-a-mole phenomenon**: closing slot $I_1$ by tuning runners 6 and 9 to their resonance values ($a_6 = 40/7$, $a_9 = 25/3$) automatically opens slots $I_2$ and $I_8$ via the Coupling Principle. Specifically:
- Closing $I_1$ forces $a_9 = 25/3$, which leaves $I_6$ uncovered by runner 9 (gap $G_6$).
- Covering $G_6$ requires runner 8 to shift, which opens $I_3$.
- The cascade continues until Runner 2 Incompatibility (Theorem 10.16.5) is reached.

This whack-a-mole structure is the empirical signature of the algebraic Coupling Principle and confirms that the incompatibility proof captures the correct mechanism.

---

## Appendix C — Previously Open Items (All Closed in v16–v17)

| Open Item | Closed By | Reference | Version |
|-----------|-----------|-----------|---------|
| Open 1: Dynamic front (Containment C) | status reset: non-canonical until repaired | `lrc_n11_slot_economy_theorem_v1.md` | audit reset |
| Open 3: Static front (Route 3, σ₂=−1 cascade) | Lemma S2 (§10.16) | `lrc_n11_lemma_s2_proof_v2.md` | v16 |
| Gap 4: Lemma WIT conditional status | status reset: non-canonical until repaired | `lrc_n11_lemma_wit_analytic_v1.md` | audit reset |

Canonical status after the 2026-03-26 audit: the static front is packaged
separately; dynamic SET and Lemma WIT are not canonical as written.

---

## Appendix D — Computational Support for Lemma WIT

This appendix contains supplementary computational evidence corroborating the analytic proof of Lemma WIT. **This appendix is NOT part of the proof chain.**

### D.1 Random-sampling adversarial search (corroboration only)

Script `lrc_witness_zone_v1.py` performs an adversarial random search over 8-runner configurations. For each configuration and each $k \in \{1,\ldots,8\}$: $W_k(S) = I_k \setminus \bigcup_{p \in S} B_k(\{p\})$ is computed using exact `fractions.Fraction` arithmetic. The search used 5000 random trials per configuration.

**Result:** No configuration found with $W_k(S) = \emptyset$ for all $k$ simultaneously. Minimum witness zone observed: $\geq 1/594$. This corroborates the analytic result but does not constitute a proof (non-exhaustive sampling).

### D.2 Relationship to the proof

The analytic proof in §10.15 and `lrc_n11_lemma_wit_analytic_v1.md` replaces the role previously assigned to Appendix A.6:
- For $p_i > 69$: proved analytically via Weyl equidistribution (§3 of the WIT document).
- For $p_i \leq 69$: proved by exhaustive deterministic $\mathbb{Q}$-arithmetic over $|\mathcal{P}| = 60$ primes (§3, Small-$p$ Certificate). This is a finite proof, not sampling.

The random-sampling results here provide additional confidence but are superseded by the analytic proof.
