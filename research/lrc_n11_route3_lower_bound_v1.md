# Route 3 Lower Bound — Structural Analysis

**Date:** 2026-03-22
**Status:** Key structural result found; analytical proof of c_M > 0 partly established.

---

## The Runner 10 Slot Structure

Runner 10 has speed exactly 10 (fixed). Its **good intervals** (where it is lonely) in $W_0$ are:
$$I_{m-1} = \left[\frac{m-1}{10} + \frac{1}{110},\ \frac{m-1}{10} + \frac{10}{110}\right], \quad m = 2, \ldots, 10.$$
Each has width $9/110 \approx 0.082$ and contains **exactly one AP witness** $t_m = m/11$.

**Position of $t_m$ within $I_{m-1}$:**
| $m$ | Left dist | Right dist | Asymmetry |
|---|---|---|---|
| 2 | $8/110$ | $1/110$ | Strongly right-leaning |
| 3 | $7/110$ | $2/110$ | |
| 4 | $6/110$ | $3/110$ | |
| 5 | $5/110$ | $4/110$ | Nearly centred |
| 6 | $4/110$ | $5/110$ | Nearly centred |
| 7 | $3/110$ | $6/110$ | |
| 8 | $2/110$ | $7/110$ | |
| 9 | $1/110$ | $8/110$ | |
| 10 | $0$ | $9/110$ | Exactly at left boundary |

---

## Key Structural Theorem (Candidate)

**Theorem R3 (Candidate):** For any complete-blocking configuration with $|\delta_i| \leq 0.9$ and $0 < a_1 < 1$, all 9 runner 10 good intervals $I_1, \ldots, I_9$ cannot be simultaneously fully covered by the bad sets of runners 2–9.

**Evidence:** Exhaustive computational search over $3 \times 10^6$ complete-blocking configurations finds minimum GF $\geq 0.84\%$ with no improvement from 300 Nelder-Mead polish runs or seeded differential evolution.

---

## The Coverage Argument (Partial Proof)

**Blocking at AP witness $t_m$:**

For each $m$, the blocking runner $j_m$ has:
- Speed $a_{j_m} \geq j_m - 0.9$, hence $j_m \in \{2, \ldots, 9\}$ (runner 1 cannot block $t_m$ for $m \geq 2$, runner 10 never blocks).
- Bad interval half-width $h_{j_m} = 1/(11 a_{j_m})$.

For $j_m = 2$ (minimum-speed valid blocker), $h_2 = 1/(11 a_2)$ with $a_2 \in [1.1, 2.9]$.

**Single-runner coverage condition:** Runner $j_m$ covers all of $I_{m-1}$ iff $h_{j_m} \geq \max(\text{left\_dist}, \text{right\_dist})$:

| $m$ | Condition for full coverage |
|---|---|
| 2–4 | $a_{j_m} \leq 1.67$ — only runner 2 at $a_2 \leq 1.67$ can cover alone |
| 5–6 | $a_{j_m} \leq 2.00$ — borderline for runner 2 at $a_2 = 2$ |
| 7–9 | $a_{j_m} \leq 1.67$ — only runner 2 again |
| 10 | $a_{j_m} \leq 1.11$ — essentially only runner 2 at min speed |

---

## The Pivotal Case: $m = 5$

**$t_5 = 5/11$ is the most centred AP witness in its slot** (left = right = $5/110 = 1/22$).

To block $t_5$, runner 2 needs $r_2(5) + 5\delta_2 \notin [1, 10] \pmod{11}$. Since $r_2(5) = 10$:
- Block from above: $\delta_2 > 0 \Rightarrow a_2 > 2 \Rightarrow h_2 < 1/22 = 5/110$. **Cannot cover left gap.**
- Block from below: $\delta_2 < -9/5 = -1.8$. **Impossible** ($|\delta_2| \leq 0.9$).

**Consequence (Proposition R3-A):** For any complete-blocking configuration, runner 2 blocking $t_5$ from above leaves an **uncovered left gap** in $I_4$ of width:
$$\Delta_{\text{left}} = \frac{5}{110} - \frac{10\delta_2 - 1}{11 a_2} > 0.$$

For $a_2 = 2.1$ ($\delta_2 = 0.1$): $\Delta_{\text{left}} = 5/110 - 1/(11 \times 2.1) \approx 0.024$.

**However:** Multiple runners can cooperate to fill this gap (runners 5, 7 have incidental bad intervals in $I_4$). In the unperturbed case, runners 2 + 5 + 7 together cover all of $I_4$. **Proposition R3-A does not directly give a positive lower bound on the global GF.**

---

## Why Total Coverage Fails Empirically

For ALL 9 runner 10 good intervals to be simultaneously covered requires:
- In $I_4$ (contains $t_5$): runners 2, 5, 7 cooperate (blocking $t_5$ and incidental coverage)
- In $I_5$ (contains $t_6$): runner 2 blocking $t_6$ from below ($\delta_2 < 0$)
- **Contradiction!** $I_4$ requires $\delta_2 > 0$ (to block $t_5$ from above) and $I_5$ requires $\delta_2 < 0$ (to block $t_6$ from below).

**Specifically:**
- $r_2(5) = 10$: Runner 2 blocks $t_5$ from above iff $\delta_2 > 0$.
- $r_2(6) = 1$: Runner 2 blocks $t_6$ from below iff $\delta_2 < 0$.

Runner 2 cannot simultaneously block $t_5$ AND $t_6$. So different runners must block each. This creates cascading coverage requirements.

The specific bottleneck from computation: the extremal config has runner 3 blocking witnesses $m = 3, 6, 9$ (three witnesses) — its bad intervals are spread across 3 different runner 10 slots, but each slot has a small uncovered portion that other runners partially cover. The minimum positive GF ($\approx 0.84\%$) is the measure of the irreducible gap that no combination of runners can close while maintaining complete-blocking.

---

## Formal Lower Bound (Incomplete)

**Route toward full proof:**

**Step 1:** Runner 2 has $r_2(5) = 10$ and $r_2(6) = 1$. It blocks $t_5$ XOR $t_6$ (not both), so one of $\{t_5, t_6\}$ is blocked by runner $j \in \{3, \ldots, 9\}$ with $a_j \geq 3 - 0.9 = 2.1$.

**Step 2:** For runner $j$ (speed $a_j \geq 2.1$) blocking $t_5$ or $t_6$: $h_j = 1/(11 a_j) \leq 1/23.1 \approx 0.043 < 5/110$. The blocking runner leaves a gap of width $\geq 5/110 - h_j > 0$ on the far side of the centred AP witness.

**Step 3:** The gap must be covered by "incidental" bad intervals of other runners. These incidental intervals are **not constrained by the complete-blocking condition** — they coincidentally land in $I_4$ or $I_5$. For them to fully cover the gap requires specific speed relationships between runners.

**Step 4 (open):** Show that the specific speed relationships required to cover all gaps simultaneously across $I_1, \ldots, I_9$ are incompatible with the complete-blocking condition on $t_2, \ldots, t_{10}$.

This step requires a detailed combinatorial case analysis that remains incomplete.

---

## Summary Status

| Component | Status |
|---|---|
| CB is open, $S_M$ is compact | **PROVED** |
| GF is Lipschitz on $S_M$ | **PROVED** |
| GF achieves minimum on $S_M$ | **PROVED** |
| Minimum $\geq 0.84\%$ | **EMPIRICAL** (3M+ samples, 300 polish, seeded DE) |
| Minimum $> 0$ analytically | **OPEN** — Step 4 of coverage argument incomplete |

**Empirical Route 3** is established: the minimum GF is bounded away from zero across all tested complete-blocking configurations. The **analytical Route 3** requires completing the coverage incompatibility argument.

The key obstruction to analytical completion: runner 2's sign constraint ($\delta_2 > 0$ for $t_5$, $\delta_2 < 0$ for $t_6$) gives SIGN INCOMPATIBILITY — one of these witnesses must be blocked by a faster runner, which leaves a provably positive gap in one runner 10 slot. But covering that gap incidentally remains possible unless we can show the required coverage is incompatible with the complete-blocking conditions on the remaining 8 witnesses.
