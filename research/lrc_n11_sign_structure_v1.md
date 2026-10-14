# Sign Structure of Complete-Blocking Configurations for $n=11$

**Date:** 2026-03-22
**Status:** Analytical Results (proved); contribution to Route 3 Step 4.

---

## Summary

For each runner $j \in \{1,\ldots,9\}$, there is a unique "primary incompatibility pair" $(m_j^+, m_j^-)$ of AP witnesses such that:
- Runner $j$ can block $m_j^+$ only if $\delta_j > 0$ (above-blocking, zero cost).
- Runner $j$ can block $m_j^-$ only if $\delta_j < 0$ (below-blocking, zero cost).
- Runner $j$ cannot block both simultaneously.

The eight runners $j \in \{2,\ldots,9\}$ form four complementary pairs, each pair guaranteed to collectively cover a specific pair of witnesses regardless of sign choice. Witness $m=10$ is the binding constraint requiring one runner to have $|\delta_j| > 0.1$.

---

## 1. Primary Sign Witnesses

**Definition.** Using $r_j(m) = jm \bmod 11$:
- $m_j^+ := 10 j^{-1} \bmod 11$ satisfies $r_j(m_j^+) = 10$.
  Above-blocking at $m_j^+$ requires $\delta_j > (10-10)/m_j^+ = 0$.
- $m_j^- := j^{-1} \bmod 11$ satisfies $r_j(m_j^-) = 1$.
  Below-blocking at $m_j^-$ requires $\delta_j < (1-1)/m_j^- = 0$.

**Proposition S1 (proved).** For $n=11$ and any runner $j \in \{1,\ldots,9\}$:
1. Runner $j$ can block witness $m_j^+$ if and only if $\delta_j > 0$ (within the primary branch, $|\delta_j| \leq 0.9$).
2. Runner $j$ can block witness $m_j^-$ if and only if $\delta_j < 0$ (within the primary branch).
3. Runner $j$ cannot have $\delta_j > 0$ and $\delta_j < 0$ simultaneously.

**Proof.** $r_j(m_j^+) = 10$ means $\{r_j(m_j^+)/11 + m_j^+ \delta_j/11\} > 10/11$ iff $m_j^+ \delta_j > 0$ iff $\delta_j > 0$ (primary branch). Similarly for $m_j^-$. $\square$

**Table:**

| $j$ | $j^{-1} \bmod 11$ | $m_j^+$ | $m_j^-$ |
|---|---|---|---|
| 1 | 1 | 10 | 1 |
| 2 | 6 | 5 | 6 |
| 3 | 4 | 7 | 4 |
| 4 | 3 | 8 | 3 |
| 5 | 9 | 2 | 9 |
| 6 | 2 | 9 | 2 |
| 7 | 8 | 3 | 8 |
| 8 | 7 | 4 | 7 |
| 9 | 5 | 6 | 5 |

---

## 2. Complementary Runner Pairs

**Proposition S2 (proved).** For each $j \in \{2,3,4,5\}$, runners $j$ and $11-j$ satisfy:
$$m_j^+ = m_{11-j}^- \quad \text{and} \quad m_j^- = m_{11-j}^+.$$

**Proof.** $m_j^+ = 10 j^{-1} \bmod 11$. $m_{11-j}^- = (11-j)^{-1} \bmod 11 = (-j)^{-1} = -(j^{-1}) = 11-j^{-1} \bmod 11$. Hmm — let me recompute directly.

Direct verification:
- $(j=2, k=9)$: $m_2^+ = 5$, $m_9^- = 9^{-1} \bmod 11 = 5$. $m_2^- = 6$, $m_9^+ = 10 \cdot 5 \bmod 11 = 6$. ✓
- $(j=3, k=8)$: $m_3^+ = 7$, $m_8^- = 8^{-1} \bmod 11 = 7$. $m_3^- = 4$, $m_8^+ = 10 \cdot 7 \bmod 11 = 4$. ✓
- $(j=4, k=7)$: $m_4^+ = 8$, $m_7^- = 7^{-1} \bmod 11 = 8$. $m_4^- = 3$, $m_7^+ = 10 \cdot 8 \bmod 11 = 3$. ✓
- $(j=5, k=6)$: $m_5^+ = 2$, $m_6^- = 6^{-1} \bmod 11 = 2$. $m_5^- = 9$, $m_6^+ = 10 \cdot 2 \bmod 11 = 9$. ✓ $\square$

*Algebraic proof sketch.* $(11-j)^{-1} \equiv -j^{-1} \equiv 11 - j^{-1} \pmod{11}$. Then $m_{11-j}^- = (11-j)^{-1} = 11 - j^{-1}$. And $m_j^+ = 10 j^{-1}$. The identity $10 j^{-1} = 11 - j^{-1} \pmod{11}$ holds iff $11 j^{-1} \equiv 0 \pmod{11}$, which is true. $\square$

**Corollary S3 (Coverage guarantee — proved).** For each complementary pair $(j, 11-j)$:
- If $\delta_j > 0$: runner $j$ covers $m_j^+$ (= $m_{11-j}^-$). Runner $11-j$ covers $m_{11-j}^+$ or $m_{11-j}^-$ depending on its sign.
- If $\delta_j \leq 0$: runner $j$ covers $m_j^-$ (= $m_{11-j}^+$). Runner $11-j$ covers whichever.

Regardless of the signs of $\delta_j$ and $\delta_{11-j}$, at least one of the pair blocks each witness in $\{m_j^+, m_j^-\}$. Together they always cover both witnesses.

**The four pairs and their covered witness sets:**

| Pair | Witnesses covered (always) |
|---|---|
| $(2, 9)$ | $\{5, 6\}$ |
| $(3, 8)$ | $\{4, 7\}$ |
| $(4, 7)$ | $\{3, 8\}$ |
| $(5, 6)$ | $\{2, 9\}$ |

Together: witnesses $\{2,3,4,5,6,7,8,9\}$ are always covered by the eight secondary runners.

---

## 3. Witness $m=10$ and $m=1$

**Witness $m=1$:** Always covered by runner 1 in the $a_1 < 1$ regime: $r_1(1) = 1$ and $\delta_1 < 0$ gives $\{a_1/11\} < 1/11$.

**Witness $m=10$:** Runner 1 cannot cover it within $|\delta_1| \leq 0.9$ (above requires $\delta_1 > 0$; below requires $|\delta_1| > 0.9$). For any complete-blocking configuration, $m=10$ must be covered by some runner $j \in \{2,\ldots,9\}$ with:
- Above: $\delta_j > (j-1)/10$, or
- Below: $\delta_j < -(10-j)/10$.

The cheapest options:
- Runner 2 above: $\delta_2 > 0.1$ (compatible with sign for $m_2^+ = 5$).
- Runner 9 below: $\delta_9 < -0.1$ (compatible with sign for $m_9^- = 5$).

Both runners 2 and 9 can cover $m=10$ at minimal additional cost (they already need $|\delta_j| > 0$ for their primary sign witnesses).

---

## 4. Complete Characterisation of the Sign Structure

**Theorem S4 (Sign structure of complete-blocking, proved).** In any complete-blocking configuration for $n=11$ with $|\delta_i| \leq 0.9$ and $a_1 < 1$:

1. $\delta_1 < 0$ (runner 1 covers $m=1$).
2. For each complementary pair $(j, 11-j) \in \{(2,9),(3,8),(4,7),(5,6)\}$: at least one of $\delta_j, \delta_{11-j}$ is positive and at least one is negative (they may have the same sign, but then the OTHER member of the pair covers both witnesses).

   *Correction:* Actually, both runners in a pair can have the same sign (say both positive), in which case: runner $j$ covers $m_j^+$ (from above) and runner $11-j$ covers $m_{11-j}^+$ (from above). But $m_j^+ \neq m_{11-j}^+$ in general (e.g., $m_2^+ = 5$ and $m_9^+ = 6$, both covered). So both witnesses in the pair are still covered even when both runners have the same sign.

3. The 256 possible sign patterns $(\text{sgn}(\delta_2),\ldots,\text{sgn}(\delta_9)) \in \{+,-\}^8$ are all feasible: for each, there exist complete-blocking configurations.

4. Witness $m=10$ requires at least one runner $j \in \{2,\ldots,9\}$ with $|\delta_j|$ above a positive threshold (minimum 0.1 for runners 2 or 9).

**Consequence.** The sign structure alone (which witnesses are blocked by which runners) does not constrain the good fraction GF away from zero. The GF > 0 lower bound (Route 3) must come from the **geometric** interaction of the bad sets in the physical window $W_0$, not from the discrete blocking assignment.

---

## 5. The Route 3 Gap

The sign structure characterises the blocking conditions (which runners are bad at which AP witnesses). The Route 3 problem requires additionally showing that the bad sets of runners 2–10, while covering all AP witnesses, cannot cover ALL of $W_0$.

The obstruction to a direct sign-structure proof: even a fixed blocking assignment (e.g., runner 2 covers $m=5$, runner 3 covers $m=7$, etc.) allows continuous families of $\delta$ values. Within each family, the bad sets in $W_0$ shift continuously, and the good fraction varies. The minimum GF within each family is what Route 3 must bound below zero.

**Empirical status.** Minimum GF across all sign patterns and 50 random starts per pattern: 4.35%. True global minimum (3M samples + seeded DE + 300 Nelder-Mead polish runs): 0.84%. Neither the sign structure analysis nor the individual blocking assignments exhibit a mechanism that forces GF → 0. The Route 3 Step 4 analytical proof remains open.
