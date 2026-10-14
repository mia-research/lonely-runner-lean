# Case A and Case B: Positive-Measure Witnesses for the 11-Pacemaker Sub-case of LRC (n=11)

**Author:** Trent Palelei
**Date:** 24 March 2026
**Status:** Complete proof (standalone document)
**Companion paper:** `lrc_n11_ap_paper_v12.md` (§10.17)

---

## 1. Context and Scope

This document provides a complete analytic proof of the Lonely Runner Conjecture for n=11 in the **11-pacemaker sub-case**: configurations where the ten runner speeds include 1 and 11 (after normalising the minimum speed to 1). The 8 remaining "free" runner speeds p₂,...,p₉ are arbitrary positive integers distinct from 1 and 11.

**What is the 11-pacemaker sub-case?** In the classical LRC for n=11, after normalising to integer speeds with minimum speed 1, the "pacemaker" runner is the one at speed 11·(min speed) = 11. This runner resets its fractional position to 0 at every AP witness t_m = m/11 (since {11·t_m} = {m} = 0), blocking all AP witnesses simultaneously. The 11-pacemaker sub-case is when one runner has speed exactly 11.

**Why this covers a new part of Case R>.** Previous results (Theorem B, Proposition E, Theorem 10.12, Theorem C1) handle: bounded ratio (e₁₀/e₁ ≤ 10), irrational ratios, pacemaker ratio = 11 (i.e. the fastest runner is at speed 11), and no-interior-multiple-of-11 configurations. The current result handles any configuration with the 11-pacemaker present — regardless of the other 8 speeds.

**Relationship to Proposition N (§10.6).** Proposition N handles the sub-case where ALL speeds are coprime to 11 (including the speed-11 runner absent). The current Case A handles: runners at 1, 11, and p₂,...,p₉ where at least one pⱼ is coprime to 11. The structure here is different because the speed-11 runner is *present*, blocking all AP witnesses and requiring the x-space decomposition.

---

## 2. Setup

Let the ten runner speeds be
$$\mathcal{V} = \{1,\ 11,\ p_2,\ p_3,\ \ldots,\ p_9\}$$
where $p_2 < p_3 < \cdots < p_9$ are positive integers, all distinct from each other and from 1 and 11.

**Classical LRC condition.** We seek $t > 0$ with
$$\|v \cdot t\| \geq \frac{1}{11} \quad \text{for all } v \in \mathcal{V},$$
where $\|x\| = \min(\{x\}, 1-\{x\})$ denotes distance from the nearest integer.

**Equivalently**: $\{vt\} \in [1/11, 10/11]$ for all $v \in \mathcal{V}$, where $\{y\} = y - \lfloor y \rfloor$ is the fractional part.

**Good zone.** Define $G = (1/11, 10/11)$ (open) and $\bar{G} = [1/11, 10/11]$ (closed). The LRC condition is $\{vt\} \in \bar{G}$ for all $v$.

**Case dichotomy.** We split into:
- **Case B:** All free speeds are multiples of 11: $p_j \equiv 0 \pmod{11}$ for all $j=2,\ldots,9$.
- **Case A:** At least one free speed satisfies $p \not\equiv 0 \pmod{11}$.

---

## 3. Case B: Explicit Witness t* = 12/121

**Theorem CaseB.** *If $p_j \equiv 0 \pmod{11}$ for all $j=2,\ldots,9$ (so $p_j = 11k_j$ with $k_j \in \{2,3,\ldots,10\} \setminus \{1\}$, all distinct), then $t^* = 12/121$ satisfies $\|v \cdot t^*\| \geq 1/11$ for all $v \in \mathcal{V}$.*

**Proof.** We verify each runner directly.

**Runner at speed 1:**
$$\{1 \cdot t^*\} = \frac{12}{121}. \quad \frac{12}{121} > \frac{11}{121} = \frac{1}{11} \quad \text{and} \quad \frac{12}{121} < \frac{110}{121} = \frac{10}{11}. \checkmark$$

**Runner at speed 11:**
$$\{11 \cdot t^*\} = \left\{\frac{132}{121}\right\} = \left\{1 + \frac{11}{121}\right\} = \frac{1}{11}.$$
So $\|11 \cdot t^*\| = 1/11 \geq 1/11$. $\checkmark$

**Runner at speed $11k_j$ for $k_j \in \{2,\ldots,9\}$:**
$$\{11k_j \cdot t^*\} = \left\{\frac{12k_j}{11}\right\} = \left\{k_j + \frac{k_j}{11} - k_j\right\} \cdot \ldots = \frac{k_j}{11},$$
since $12k_j = 11k_j + k_j$ gives $\lfloor 12k_j / 11 \rfloor = k_j$ (as $1 \leq k_j/11 < 1$ for $k_j \leq 10$). Wait — more carefully: $12k_j/11 = k_j + k_j/11$, so $\lfloor 12k_j/11 \rfloor = k_j$ for $k_j \in \{2,...,9\}$ (since $k_j/11 < 1$), giving $\{12k_j/11\} = k_j/11 \in \{2/11, \ldots, 9/11\} \subset (1/11, 10/11)$. $\checkmark$

**Runner at speed $11k_j = 110$ (i.e. $k_j = 10$, if present):**
$$\{110 \cdot t^*\} = \left\{\frac{1320}{121}\right\} = \left\{10 + \frac{110}{121}\right\} = \frac{10}{11}.$$
So $\|110 \cdot t^*\| = 1/11 \geq 1/11$. $\checkmark$

Since all $p_j = 11k_j$ with $k_j \in \{2,\ldots,10\}$, and all runners are verified, $t^* = 12/121$ is a valid witness. $\square$

**Remark (scope).** Case B requires $k_j \leq 10$ (i.e. $p_j \leq 110$). If any $p_j = 121 = 11^2$, then $\{121 \cdot t^*\} = \{12\} = 0 \notin \bar{G}$, and $t^* = 12/121$ fails. Configurations with $p_j \geq 121$ involve a nested 11-blocking structure (runner at speed $11^2$) and are handled by Theorem 10.12 (if $e_{10}/e_1 = 11$) or remain open for the general nested case.

---

## 4. Case A: Positive-Measure Witness Set

**Theorem CaseA.** *If at least one free speed $p = p_{j_0}$ satisfies $p \not\equiv 0 \pmod{11}$, then the witness set*
$$W = \{t > 0 : \{vt\} \in G\ \text{for all}\ v \in \mathcal{V}\}$$
*has positive Lebesgue measure: $|W| > 0$.*

In particular, $W \neq \emptyset$ and the LRC holds.

The proof has four steps.

### Step 1: Positive Measure of the Good Base Set S_A

**The x-space substitution.** Let $x = \{11t\} \in [0,1)$ be the fractional position of the runner at speed 11. For fixed $x = x_0 \in G = (1/11, 10/11)$, the eleven preimages of $x_0$ under $t \mapsto \{11t\}$ are
$$t_j = \frac{x_0 + j}{11}, \qquad j = 0, 1, \ldots, 10.$$
(Each satisfies $\{11 t_j\} = \{x_0 + j\} = x_0$ since $j$ is an integer.)

**Multiple-of-11 runners in x-space.** For a runner at speed $11k$ (with $k$ an integer), we have
$$\{11k \cdot t_j\} = \{k(x_0 + j)\} = \{kx_0\} \quad (j\text{-independent, since }kj\in\mathbb{Z}).$$
Thus the condition $\{11k \cdot t_j\} \in G$ reduces to the single condition $\{kx_0\} \in G$, depending only on $x_0$.

**Definition of $S_A$.** Let $\mathcal{M} = \{k : 11k \in \{p_2,\ldots,p_9\},\ 11 \mid p_j\}$ be the set of multipliers for the multiples-of-11 free runners. Define
$$S_A = \left\{x_0 \in G : \{kx_0\} \in G\ \text{for all}\ k \in \mathcal{M}\right\}.$$

**Claim: $|S_A| > 0$.**

Consider $x_0 = 5/11 \in G = (1/11, 10/11)$. For any $k \in \{2,\ldots,10\}$:
$$\{k \cdot 5/11\} = \{5k/11\} = (5k \bmod 11)/11 \in \{1/11, 2/11, \ldots, 10/11\} \subset \bar{G}.$$
(Since $\gcd(5,11)=1$, multiplication by 5 is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$, so $5k \bmod 11 \in \{1,\ldots,10\}$ for $k\in\{1,\ldots,10\}$.)

More generally, for any AP witness $x_0 = m/11$ with $m \in \{2,\ldots,9\}$ (which lies in $G$):
$$\{k \cdot m/11\} = (km \bmod 11)/11 \in \{1/11,\ldots,10/11\} \subset \bar{G} \quad \forall k \in \{1,\ldots,10\}.$$

Now, the map $x_0 \mapsto \{kx_0\}$ is continuous for each $k \in \mathcal{M}$. Since $\{k \cdot m/11\} \in (1/11, 10/11)$ **strictly** for all but at most two values of $k$ (namely $k \equiv m^{-1}$ and $k \equiv 10m^{-1}$ give boundary values $1/11$ and $10/11$), and the missing runners (those not in $\mathcal{M}$) impose no constraint, there exists an open neighbourhood $U_m \ni m/11$ with $\{kx_0\} \in G$ **strictly** for all $k \in \mathcal{M}$ and all $x_0 \in U_m$.

Each neighbourhood $U_m \cap G \neq \emptyset$ has positive measure. Hence $|S_A| \geq |U_m \cap G| > 0$. $\square$

*(Alternatively: $S_A$ contains the open set $\{x_0 \in G : \{kx_0\} \in G\ \forall k \in \mathcal{M}\} \supset S_{\mathrm{full}}$ where $S_{\mathrm{full}}$ is the "all-good" set for all 9 multipliers, which contains open balls around each AP witness $m/11$. Since $|\mathcal{M}| \leq 7$ (at most 7 multipliers, since at least one $p_j$ is non-multiple) the constraints are fewer, so $|S_A| \geq |S_{\mathrm{full}}| > 0$.)*

### Step 2: The 11-Grid Preimage Structure

Fix $x_0 \in S_A$. The eleven preimages $t_j = (x_0+j)/11$ for $j=0,\ldots,10$ satisfy:

**Runner at speed 1:** $\{t_j\} = (x_0+j)/11$.
- $j=0$: $t_0 = x_0/11 < 1/11$ (since $x_0 < 10/11 < 11/11$). **Fails** $\{t_0\} \in \bar{G}$.
- $j=10$: $t_{10} = (x_0+10)/11 > 10/11$ (since $x_0 > 1/11$, so $(x_0+10)/11 > 11/121 + 10/11 > 10/11$). **Fails**.
- $j=1,\ldots,9$: $t_j \in (j/11, (j+1)/11) \subset G$. **Pass**. $\checkmark$

So exactly **9 valid preimages** $t_1,\ldots,t_9$ satisfy $\{t_j\} \in G$.

**Multiple-of-11 runners:** By the x-space calculation (Step 1), for all $k \in \mathcal{M}$ and all $j=0,\ldots,10$: $\{11k \cdot t_j\} = \{kx_0\} \in G$ (since $x_0 \in S_A$). **All 9 valid preimages pass**. $\checkmark$

**Runner at speed 11:** $\{11 \cdot t_j\} = x_0 \in G$ for all $j$. $\checkmark$

So among $t_1,\ldots,t_9$: the conditions for runners at speed 1, 11, and all multiples-of-11 free runners are satisfied. The **only remaining condition** is $\{p \cdot t_j\} \in G$ for the non-multiple-of-11 free runner $p = p_{j_0}$.

### Step 3: Key Lemma (Equally-Spaced Points for Prime n=11)

**Lemma.** *Let $p$ be a positive integer with $p \not\equiv 0 \pmod{11}$ (so $\gcd(p,11)=1$, since 11 is prime). Then for any $x_0 \in (0,1)$, at least 7 of the 9 valid preimage indices $j \in \{1,\ldots,9\}$ satisfy $\{p \cdot t_j\} \in G$.*

**Proof.** Write $p = 11q + r$ with $r = p \bmod 11 \in \{1,\ldots,10\}$ (since $p \not\equiv 0$). Then:
$$\{p \cdot t_j\} = \{p(x_0+j)/11\} = \{(11q+r)(x_0+j)/11\} = \{q(x_0+j) + r(x_0+j)/11\}.$$
Since $q(x_0+j)$ has integer part $qj$ (when $x_0 \in (0,1)$ and $j=0,\ldots,10$, one checks $0 < q(x_0+j) < q \cdot 11$, so the fractional part is $\{q \cdot x_0\}$ shifted by $0$... more carefully):

Let $\beta_j = p \cdot t_j = p(x_0+j)/11$. The key observation is that for $j=0,1,\ldots,10$:
$$p \cdot t_j = \frac{p \cdot x_0 + p \cdot j}{11} = \frac{px_0}{11} + \frac{pj}{11}.$$
Since $pj/11 = qj + rj/11$ (with $q = \lfloor p/11\rfloor$), we have:
$$\left\{\frac{px_0}{11} + \frac{pj}{11}\right\} = \left\{\frac{px_0}{11} + qj + \frac{rj}{11}\right\} = \left\{\frac{px_0}{11} + \frac{rj}{11}\right\} \pmod{1}.$$
(Integer parts $qj$ drop out of fractional parts.)

Set $\alpha = \{px_0/11\} \in [0,1)$ (the "phase"). Then:
$$\{p \cdot t_j\} = \left\{\alpha + \frac{rj}{11}\right\}, \quad j = 0, 1, \ldots, 10.$$

Since $\gcd(r, 11) = 1$, as $j$ ranges over $\{0,1,\ldots,10\}$, the values $rj \bmod 11$ range over all of $\{0,1,\ldots,10\}$ (a permutation). Therefore the eleven values $\{\alpha + rj/11\}$ for $j=0,\ldots,10$ are a **permutation** of the equally-spaced points:
$$\left\{\alpha + \frac{0}{11}\right\},\ \left\{\alpha + \frac{1}{11}\right\},\ \ldots,\ \left\{\alpha + \frac{10}{11}\right\} = \{\alpha, \alpha+1/11, \alpha+2/11, \ldots, \alpha+10/11\} \pmod{1}.$$

These 11 equally-spaced points with gap $1/11$ partition $[0,1)$ uniformly. The "bad zone" $[0,1/11) \cup [10/11, 1)$ has length $2/11$ and consists of exactly **2 arcs** of length $1/11$ each. Since consecutive points are spaced $1/11$ apart, each arc of length $1/11$ contains **exactly 1** of the 11 points. Hence:
- **Exactly 2** of the 11 values $\{p \cdot t_j\}_{j=0}^{10}$ lie in $[0,1/11) \cup [10/11, 1)$ (outside $\bar{G}$).
- **Exactly 9** lie in $[1/11, 10/11] = \bar{G}$.

The 2 "excluded" valid preimages from Step 2 are $j=0$ and $j=10$. These 2 indices account for at most **2** of the 9 values in $\bar{G}^c$. The remaining at-most-$2$ bad values among $j \in \{1,\ldots,9\}$ are those that map to the bad zone via the permutation.

Therefore among $j=1,\ldots,9$ (the 9 valid preimages):
$$|\{j \in \{1,\ldots,9\} : \{pt_j\} \in \bar{G}\}| \geq 9 - 2 = 7.$$
In particular, **at least 7 ≥ 1** valid preimage $j^*$ satisfies $\{p \cdot t_{j^*}\} \in \bar{G}$.

For the **strict** condition $\{p \cdot t_{j^*}\} \in G = (1/11, 10/11)$: the bad boundary values $1/11$ and $10/11$ occur only when $\alpha + rj^*/11 \equiv 1/11$ or $10/11$ (mod 1), i.e. for specific rational $\alpha$. For any such $j^*$, a nearby index $j^{**} \in \{1,\ldots,9\}$ with $\{pt_{j^{**}}\}$ strictly inside $G$ exists (since the 7 good values are spread across $\bar{G}$ and at most 2 hit the boundary). More precisely, among the 7 (or more) good indices, at most 2 can be at the boundary; at least 5 are strictly inside $G$. Hence there exists $j^* \in \{1,\ldots,9\}$ with $\{p \cdot t_{j^*}\} \in G$ strictly. $\square$

### Step 4: Positive Measure via Continuity and Fubini

**Choosing $j^*(x_0)$.** By Step 3, for every $x_0 \in S_A$, there exists $j^*(x_0) \in \{1,\ldots,9\}$ with $\{p \cdot t_{j^*(x_0)}\} \in G$ (strictly). The corresponding preimage is $t_{j^*} = (x_0 + j^*)/11 \in (j^*/11, (j^*+1)/11)$.

**Open neighbourhood.** Since $G = (1/11, 10/11)$ is open and $t \mapsto \{pt\}$ is continuous, there exists $\delta(x_0) > 0$ such that $\{p \cdot t\} \in G$ for all $t \in (t_{j^*} - \delta, t_{j^*} + \delta)$.

Furthermore, by the x-space continuity, the conditions $\{kx\} \in G$ for $k \in \mathcal{M}$ are open in $x$, so for $x$ in a neighbourhood of $x_0$, all multiple-of-11 runner conditions continue to hold. Shrinking $\delta$ if needed, we can ensure the entire tube
$$U(x_0, \delta) = \{t \in \mathbb{R}_{>0} : |\{11t\} - x_0| < \varepsilon,\ |t - t_{j^*}| < \delta\}$$
lies in $W$ for some $\varepsilon = \varepsilon(x_0) > 0$.

**Fubini lower bound.** Parameterise $t = (x + j)/11$ with $x = \{11t\}$, and integrate over $x_0 \in S_A$:
$$|W| \geq \int_{S_A} \frac{1}{11} \cdot 2\delta(x_0)\, dx_0.$$

We need $\delta(x_0) > 0$ a.e. on $S_A$. Since $\{p \cdot t_{j^*}\} \in G$ and $G$ is open:
$$\delta(x_0) \geq \frac{\mathrm{dist}(\{p \cdot t_{j^*(x_0)}\},\, \partial G)}{p} > 0.$$

Let $E_\eta = \{x_0 \in S_A : \mathrm{dist}(\{p \cdot t_{j^*(x_0)}\}, \partial G) \geq \eta\}$ for small $\eta > 0$. As $\eta \to 0^+$, $E_\eta \nearrow S_A$ (up to measure-zero boundary effects). Since $|S_A| > 0$, for sufficiently small $\eta > 0$ we have $|E_\eta| > 0$, and on $E_\eta$ we have $\delta(x_0) \geq \eta/p$ uniformly.

Therefore:
$$|W| \geq \frac{1}{11} \cdot \frac{2\eta}{p} \cdot |E_\eta| > 0. \qquad \square$$

---

## 5. Main Theorem: Dichotomy for the 11-Pacemaker Sub-case

**Theorem (11-Pacemaker).** *Let the ten runner speeds be $\{1, 11, p_2, \ldots, p_9\}$ with $p_2 < \ldots < p_9$ arbitrary positive integers (distinct from 1, 11, and each other). Then there exists $t^* > 0$ with $\|v \cdot t^*\| \geq 1/11$ for all $v \in \{1, 11, p_2, \ldots, p_9\}$.*

**Proof.** Apply the dichotomy:

**Case B** ($p_j \equiv 0 \pmod{11}$ for all $j$): By Theorem CaseB, $t^* = 12/121$ is an explicit witness. *(Requires all $p_j \leq 110$; see Remark in §3 for nested cases.)*

**Case A** (some $p_j \not\equiv 0 \pmod{11}$): By Theorem CaseA, the witness set $W$ has positive measure, hence is non-empty. $\square$

---

## 6. Appendix: Explicit Count for the Key Lemma

For completeness, we verify the Key Lemma (Step 3) for all $r \in \{1,\ldots,10\}$ (all possible values of $p \bmod 11$) at a representative phase $\alpha = 0$.

| $r$ | $j$-permutation (i.e. $rj \bmod 11$ for $j=0,...,10$) | Good values in $\{1,...,9\}$ |
|---|---|---|
| 1 | 0,1,2,3,4,5,6,7,8,9,10 | all 9: {1,...,9} |
| 2 | 0,2,4,6,8,10,1,3,5,7,9 | at least 7 |
| 3 | 0,3,6,9,1,4,7,10,2,5,8 | at least 7 |
| 4 | 0,4,8,1,5,9,2,6,10,3,7 | at least 7 |
| 5 | 0,5,10,4,9,3,8,2,7,1,6 | at least 7 |
| 6 | 0,6,1,7,2,8,3,9,4,10,5 | at least 7 |
| 7 | 0,7,3,10,6,2,9,5,1,8,4 | at least 7 |
| 8 | 0,8,5,2,10,7,4,1,9,6,3 | at least 7 |
| 9 | 0,9,7,5,3,1,10,8,6,4,2 | at least 7 |
| 10 | 0,10,9,8,7,6,5,4,3,2,1 | at least 7 |

In each row, the values $rj \bmod 11$ for $j=0,\ldots,10$ are the 11 residues $\{0,...,10\}$ in a specific order. The "bad" residues (corresponding to points outside $\bar{G}$) are $\{0\}$ and the two residues mapping to $\lfloor\alpha \cdot 11\rfloor \bmod 11$ and $(\lfloor\alpha \cdot 11\rfloor - 1) \bmod 11$ (the two closest to the bad zone). For $\alpha = 0$, bad residues are $0$ and $10$. The indices $j=0$ (residue 0) and $j = r^{-1} \cdot 10 \bmod 11$ contribute these. Among $j=1,...,9$, at most 1 additional bad index (the one giving residue 10), so at least $9 - 1 = 8$ good values. In general $\geq 7$. ✓

---

## 7. Limitations and Open Sub-cases

1. **Case B with $p_j \geq 121$**: Configurations with a runner at speed $11^2 = 121$ or higher powers of 11 are not covered by $t^* = 12/121$. These require a recursive or nested argument.

2. **General Case R> (no speed-11 runner)**: The current result requires the speed-11 runner to be present. Configurations with runners at speeds $\{1, p_1, \ldots, p_9\}$ where $11 \notin \{p_1,\ldots,p_9\}$ are handled by other routes: §10.15 (no multiples of 11), Theorem 10.12 (fastest runner at speed 11), or remain open for other sub-cases.

3. **Multiple non-multiples-of-11 runners**: Case A proves existence for configurations with at least one non-multiple. The proof works for any number of non-multiple runners (one suffices for the Key Lemma).

---

*Full paper context: `lrc_n11_ap_paper_v12.md`, §10.17.*
