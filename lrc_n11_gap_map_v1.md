# Gap Map: All-Witnesses-Blocked Region for $n=11$

**Date:** 2026-03-22
**Status:** Empirical Observation + Partial Analytic Structure
**Scope:** Classical EFN, $n=11$; speeds $a_i = i + \delta_i$, $a_{10}=10$; $|\delta_i| \leq 0.9$.

---

## 1. The $9 \times 10$ Blocking-Condition Matrix

**Lemma 8.1' (paper §8.1):** Runner $i$ is bad at witness $t_m = m/11$ iff
$$\delta_i \in \left(-\infty, \frac{1 - r_i(m) + 11n}{m}\right) \cup \left(\frac{10 - r_i(m) + 11n}{m}, +\infty\right)$$
for some integer $n$, where $r_i(m) = im \bmod 11 \in \{1,\ldots,10\}$.

For the **primary branch** ($n=0$):
- Above blocking: $\delta_i > \tau_+^{(i,m)} := (10 - r_i(m))/m$
- Below blocking: $\delta_i < \tau_-^{(i,m)} := (1 - r_i(m))/m$

**Classical AP residue table** $r_j(m) = jm \bmod 11$:

| $j\backslash m$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| **1** | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| **2** | 2 | 4 | 6 | 8 | 10| 1 | 3 | 5 | 7 | 9  |
| **3** | 3 | 6 | 9 | 1 | 4 | 7 | 10| 2 | 5 | 8  |
| **4** | 4 | 8 | 1 | 5 | 9 | 2 | 6 | 10| 3 | 7  |
| **5** | 5 | 10| 4 | 9 | 3 | 8 | 2 | 7 | 1 | 6  |
| **6** | 6 | 1 | 7 | 2 | 8 | 3 | 9 | 4 | 10| 5  |
| **7** | 7 | 3 | 10| 6 | 2 | 9 | 5 | 1 | 8 | 4  |
| **8** | 8 | 5 | 2 | 10| 7 | 4 | 1 | 9 | 6 | 3  |
| **9** | 9 | 7 | 5 | 3 | 1 | 10| 8 | 6 | 4 | 2  |

**Minimum $|\delta_j|$ for primary-branch blocking:**

| $j\backslash m$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|
| **1** | 0 | — | — | — | — | — | — | — | — | 0† |
| **2** | — | — | — | — | 0 | 0 | — | — | — | 0.10 |
| **3** | — | — | 0.33| 0 | — | — | 0 | — | — | 0.20 |
| **4** | — | — | 0 | — | — | — | — | 0 | — | 0.30 |
| **5** | — | 0 | — | — | — | — | — | — | 0 | 0.40 |
| **6** | — | 0 | — | — | — | — | — | — | 0 | 0.40 |
| **7** | — | — | 0 | — | — | — | — | 0 | — | 0.30 |
| **8** | — | — | — | 0 | — | — | 0 | — | — | 0.20 |
| **9** | — | — | — | — | 0 | 0 | — | — | — | 0.10 |

†Runner 1 cannot block $m=10$: above requires $\delta_1 > 0$ (infeasible for $a_1 < 1$); below requires $|\delta_1| > 0.9$ (outside domain). "—" means infeasible at primary branch within $|\delta_j| \leq 0.9$.

---

## 2. Sign Structure and Complementary Runner Pairs

**Definition.** For runner $j$, using the modular inverse $j^{-1} \bmod 11$:
- $m_j^+ = 10 j^{-1} \bmod 11$: the witness with $r_j(m_j^+) = 10$; blocking costs $\delta_j > 0$.
- $m_j^- = j^{-1} \bmod 11$: the witness with $r_j(m_j^-) = 1$; blocking costs $\delta_j < 0$.

Computed values ($1^{-1}=1$, $2^{-1}=6$, $3^{-1}=4$, $4^{-1}=3$, $5^{-1}=9$, $6^{-1}=2$, $7^{-1}=8$, $8^{-1}=7$, $9^{-1}=5$):

| $j$ | $j^{-1}$ | $m_j^+$ | $m_j^-$ | Sign incompatibility |
|---|---|---|---|---|
| 1 | 1 | 10 | 1 | Always blocks $m=1$ ($a_1 < 1$); cannot block $m=10$ |
| 2 | 6 | 5 | 6 | Cannot block both 5 and 6 simultaneously |
| 3 | 4 | 7 | 4 | Cannot block both 7 and 4 |
| 4 | 3 | 8 | 3 | Cannot block both 8 and 3 |
| 5 | 9 | 2 | 9 | Cannot block both 2 and 9 |
| 6 | 2 | 9 | 2 | Cannot block both 9 and 2 |
| 7 | 8 | 3 | 8 | Cannot block both 3 and 8 |
| 8 | 7 | 4 | 7 | Cannot block both 4 and 7 |
| 9 | 5 | 6 | 5 | Cannot block both 6 and 5 |

**Proposition (Complementary pairs — Proved).** The following pairs of runners together cover both witnesses in their pair, regardless of sign choices:

| Pair $(j, 11-j)$ | Witnesses | Argument |
|---|---|---|
| $(2, 9)$ | $\{5, 6\}$ | $m_2^+ = m_9^- = 5$, $m_2^- = m_9^+ = 6$; sign complement |
| $(3, 8)$ | $\{4, 7\}$ | $m_3^- = m_8^+ = 4$, $m_3^+ = m_8^- = 7$ |
| $(4, 7)$ | $\{3, 8\}$ | $m_4^- = m_7^+ = 3$, $m_4^+ = m_7^- = 8$ |
| $(5, 6)$ | $\{2, 9\}$ | $m_5^+ = m_6^- = 2$, $m_5^- = m_6^+ = 9$ |

**Consequence.** Witnesses $\{2,3,4,5,6,7,8,9\}$ are always collectively covered. Witness $m=1$ is always covered by runner 1. Only witness $m=10$ requires explicit assignment.

---

## 3. Witness $m=10$: The Binding Constraint

$r_j(10) = 11 - j$ for $j = 1,\ldots,9$. Blocking thresholds:

| $j$ | Above: $\delta_j >$ | Below: $\delta_j <$ |
|---|---|---|
| 2 | 0.10 | −0.80 |
| 3 | 0.20 | −0.70 |
| 4 | 0.30 | −0.60 |
| 5 | 0.40 | −0.50 |
| 6 | 0.50 | −0.40 |
| 7 | 0.60 | −0.30 |
| 8 | 0.70 | −0.20 |
| 9 | 0.80 | −0.10 |

**Sign compatibility with $m=10$:**
- Runner $j$ with $\delta_j > 0$ (covering $m_j^+$) can simultaneously cover $m=10$ iff $\delta_j > (j-1)/10$.
- Runner $j$ with $\delta_j < 0$ (covering $m_j^-$) can simultaneously cover $m=10$ iff $\delta_j < -(10-j)/10$.

The cheapest above-blocker of $m=10$ is runner 2 ($\delta_2 > 0.1$); the cheapest below-blocker is runner 9 ($\delta_9 < -0.1$). Both are compatible with their primary sign constraints ($m_2^+$ requires $\delta_2 > 0$; $m_9^-$ requires $\delta_9 < 0$).

---

## 4. The All-Blocked Region: Non-Emptiness Near $a_1 = 1$

**Claim 4.1 (Proved — Theorem B).** Any all-blocked configuration has $a_1 < 1$ (equivalently, $\delta_1 < 0$).

**Claim 4.2 (Proved — Claim 4.2 above + computation).** Complete-blocking configurations exist for arbitrarily small $|\delta_1|$. In particular, the all-blocked region has configurations with $a_1 \in (1 - 10^{-6}, 1)$.

**Proof of Claim 4.2.** Set $\delta_1 = -\epsilon$ for small $\epsilon > 0$. Runner 1 blocks $m=1$. Use the explicit blocking assignment where each complementary pair uses opposite signs: runner 3 covers $m=4$ (below, $r_3(4)=1$), runner 4 covers $m=3$ (below, $r_4(3)=1$), runner 7 covers $m=8$ (below, $r_7(8)=1$), runner 8 covers $m=7$ (below, $r_8(7)=1$), and runners 2,5,6,9 cover $m=5,2,9,6$ (above). Runner 2 with $\delta_2 = 0.15 > 0.1$ additionally covers $m=10$ (above, since $r_2(10)=9$ and threshold is $0.1$). The explicit configuration

$$\delta = (-10^{-3},\ +0.15,\ -0.05,\ -0.05,\ +0.05,\ +0.05,\ -0.05,\ -0.05,\ +0.05)$$

with $a = (0.999,\ 2.15,\ 2.95,\ 3.95,\ 5.05,\ 6.05,\ 6.95,\ 7.95,\ 9.05,\ 10)$ is complete-blocking (computationally verified: all 10 witnesses blocked). $\square$

**Key implication.** The negative-perturbation strategy **fails**: it cannot close a neighbourhood of $a_1 = 1$. The all-blocked region is present arbitrarily close to the $a_1 = 1$ boundary.

---

## 5. Sign Pattern Enumeration — Computational Results

Systematic search over all 256 sign patterns $(\text{sgn}(\delta_2),\ldots,\text{sgn}(\delta_9)) \in \{+,-\}^8$, 50 random starts per pattern:

| Quantity | Result |
|---|---|
| Feasible patterns | 256 / 256 (all feasible) |
| Min GF found per pattern | 4.35% (sign: $++++ ----$, i.e., $j=2,3,4,5$ positive; $j=6,7,8,9$ negative) |
| Patterns with min GF < 1.5% | 0 / 256 |
| §10.1 example GF | 12.62% |

**The 50-start search is not exhaustive.** The true global minimum (0.84%, from 3M-sample seeded DE) is within these patterns but not identified by this search. All patterns clearly stay well above zero.

**Extremal sign pattern** ($++++ ----$):
$$\delta \approx (-0.039,\ +0.526,\ +0.612,\ +0.479,\ +0.726,\ -0.094,\ -0.556,\ -0.280,\ -0.693)$$
$a_i \approx (0.961,\ 2.526,\ 3.612,\ 4.479,\ 5.726,\ 5.906,\ 6.444,\ 7.720,\ 8.307,\ 10)$, GF = 4.32%.

---

## 6. The §10.1 Example: Blocking Assignment

$a = (0.5,\ 2.2,\ 11/3,\ 33/7,\ 5.5,\ 6,\ 7,\ 8,\ 9,\ 10)$, $\max|\delta_j| = 5/7 \approx 0.714$.

| Witness $m$ | Blocker $j$ | $\{a_j t_m\}$ | Direction |
|---|---|---|---|
| 1 | 1 | $1/22 \approx 0.045$ | below |
| 2 | 5 | $\{5.5 \cdot 2/11\} = 0$ | exact zero |
| 3 | 3 | $\{(11/3) \cdot 3/11\} = 0$ | exact zero |
| 4 | 5 | $\{5.5 \cdot 4/11\} = 0$ | exact zero |
| 5 | 2 | $\{2.2 \cdot 5/11\} = 0$ | exact zero |
| 6 | 3 | $\{(11/3) \cdot 6/11\} = 0$ | exact zero |
| 7 | 4 | $\{(33/7) \cdot 7/11\} = 0$ | exact zero |
| 8 | 5 | $\{5.5 \cdot 8/11\} = 0$ | exact zero |
| 9 | 3 | $\{(11/3) \cdot 9/11\} = 0$ | exact zero |
| 10 | 2 | $\{2.2 \cdot 10/11\} = 0$ | exact zero |

Sign pattern: $\delta_j > 0$ for $j \in \{2,3,4,5\}$; $\delta_j = 0$ for $j \in \{6,7,8,9\}$.
Good fraction in $W_0$: 12.62%. LRC witness $t = 4/17 \in W_0$, margin $\approx 0.018 > 1/11$.

---

## 7. Summary: What the Gap Map Establishes

| Component | Status |
|---|---|
| All-blocked requires $a_1 < 1$ | **Proved** (Theorem B) |
| All-blocked region exists near $a_1 = 1^-$ | **Proved** (Claim 4.2) |
| All-blocked region empty for $\delta_1 \in (-c, 0)$ | **False** — does not close |
| Sign complementarity (4 runner pairs) | **Proved** analytically |
| $m=10$ is the binding witness | **Established** |
| All 256 sign patterns are feasible | **Empirical** (computational) |
| Min GF > 0 across all sign patterns (coarse) | **Empirical** — 4.35% with 50 starts |
| True global min GF ≈ 0.84% | **Empirical** (3M+ samples + DE) |
| Min GF > 0 analytically | **OPEN** — Route 3 Step 4 |

**Core obstruction.** The all-blocked region has positive measure in $\delta$-space for all $a_1 \in (0,1)$. Any proof of $\text{GF} > 0$ must work within the all-blocked region (not just show it is non-empty). Route 3 reduces this to: no complete-blocking configuration has its bad sets covering all of $W_0$. The sign structure and complementary-pair analysis characterise the blocking but do not directly bound the coverage; that geometric step remains the open core of the proof.
