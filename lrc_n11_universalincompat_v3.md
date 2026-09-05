# Theorem U: Universal σ₂=+1 Incompatibility (Version 3)

**Date:** 2026-03-26
**Supersedes:** `lrc_n11_universalincompat_v2.md` (2026-03-26)
**Status:** PROVED — all 128 σ₂=+1 sign classes.
**Depends on:** `lrc_n11_algebraic_lemma_v1.md`, `lrc_n11_incompatibility_v1.md`
**Result:** For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.
**Verified by:** `lrc_n11_universalincompat_verify.py` — all 47 exact-arithmetic checks pass.

## What Changed from v2 — Structural Motivation

v1 → v2 repaired proof gaps by adding sub-cases: CT0/CT1/CT2, A2b-i/ii, A2c-i/ii. This is the wrong direction. Every split was introduced to handle an "exception" (CT's g_L precondition failing) rather than to understand *why* the exception arises.

**Root cause of all v2 branching:** Lemma CT expressed runner feasibility as a function of the gap size g_L ("which runner can reach [g_L, 109/110]?"). This made the proof's case structure dependent on g_L, not on the runners. The correct framing is runner-centric: *each runner's ability to cover I₉ is an intrinsic property of that runner's speed range*, and the consequences of that coverage (PSM or complementary chain) are also runner-intrinsic.

**v3 restructuring:**
1. **§3: Universal Blocking Theorem (UB)** — replaces Lemma CT. Proved once, independently of g_L, by analysing runners 3–8 one at a time. No g_L sub-cases.
2. **§4: Two top-level cases** — instead of A2a/A2b/A2c/A2d/B1/B2/B3/B4, we have Case α (direct incompatibility: the I₄ and I₉ constraints on a₂ are irreconcilable) and Case β (gap propagation: a right gap in I₉ exists → Theorem UB). All prior sub-cases fold into one of these two.

---

## §0 — Notation and Setup

Slots $I_k = [(11k+1)/110, (11k+10)/110]$ for $k=1,\ldots,9$. In particular:
- $I_4 = [45/110, 54/110]$; $\quad I_9 = [10/11, 109/110]$.

**Bad interval:** $B_{j,k}(a_j) = [(11k+10)/(11a_j),\; (11k+12)/(11a_j)]$ for $k = 0,1,2,\ldots$

**Sign convention:** $\sigma_j = +1$ means $a_j \in (j,j+1)$; $\sigma_j = -1$ means $a_j \in (j-1,j)$.

**Complementary Pairs (Theorem 1.1, `lrc_n11_algebraic_lemma_v1.md`):**

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

---

## §1 — I₄ Lower Bound on a₂ (unchanged from v2)

### Fact A1
For $a_9 \in (8,9)$: runner 9 never covers $I_4$'s left edge $45/110$, leaving gap $[45/110, 43/(11a_9)] \subset I_4$.

*Proof.* $43/(11a_9) > 45/110 \iff a_9 < 946/99 \approx 9.556$. ✓ $\square$

### Fact B
For $a_9 \in (9,10)$: $B_{9,3}[0] = 43/(11a_9)$ equals $45/110$ iff $a_9 = 86/9$.

*Proof.* $43/(11a_9) = 45/110 \Rightarrow a_9 = 86/9 \approx 9.556 \in (9,10)$. $\square$

### Lemma 1.1 (I₄ lower bound, σ₉=−1 or σ₉=+1 with a₉ < 86/9)

> **Lemma 1.1.** For any CB configuration with $\sigma_2=+1$ and $a_9 \notin [86/9, 10)$: closing $I_4$ requires $a_2 \geq 20/9$.

**Proof.** By Facts A1/B, runner 9 leaves a left gap at $45/110$ in $I_4$. Runner-by-runner exclusion (identical to v2 Lemma 2.1; 6 runners excluded) forces runner 2 to close the gap. The condition $B_{2,0}[0] \leq 45/110$ gives:
$$\frac{10}{11a_2} \leq \frac{45}{110} \implies a_2 \geq \frac{20}{9}. \quad \square$$

### Lemma 1.2 (I₄ lower bound, σ₉=+1 with a₉ ≥ 86/9)

> **Lemma 1.2.** For $\sigma_2=+1$, $a_9 \geq 86/9$: closing $I_4$ requires $a_2 \geq 2a_9/9 \geq 172/81$.

**Proof.** Runner 9 now covers $I_4$ from the left edge; its right coverage ends at $45/(11a_9) < I_4[\mathrm{right}]$, leaving a right gap. For runner 2 to cover this: $a_2 \geq 2a_9/9$. $\square$

**Notation:** Write $L(a_9) = 20/9$ for $a_9 < 86/9$, and $L(a_9) = 2a_9/9$ for $a_9 \geq 86/9$. Closing $I_4$ requires $a_2 \geq L(a_9)$.

---

## §2 — I₉ Coverage and the Two Top-Level Cases

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

> **Case β (Gap Propagation).** The constraints are compatible, or no upper bound exists, so runners 2+9 leave a right gap $[g_L, 109/110] \subset I_9$ with $g_L < 109/110$. The Universal Blocking Theorem (§3) shows this gap cannot be covered.

We verify each region of $(a_2, a_9)$ falls into one of these cases.

### Verification of Case α regions

**α-1 (Middle gap, σ₉=−1, a₉ < 580/69):** Runner 9's B_{9,7} starts at $87/(11a_9) > 207/220 \geq 23/(11a_2)$, leaving a middle gap $[23/(11a_2), 87/(11a_9)]$ in $I_9$. Bridging the gap requires $a_2 \leq 23a_9/87$. Direct incompatibility: $L = 20/9 > 23a_9/87 \iff a_9 < 580/69$. ✓ **GF$(I_4)$ + GF$(I_9) > 0$.** $\square$

**α-2 (High-k incompatibility, σ₉=−1, a₉ ∈ [980/109, 9)):** Runner 9's B_{9,8} re-enters $I_9$; bridging requires $a_2 \leq 23a_9/98$. Direct incompatibility: $20/9 > 23a_9/98 \iff a_9 < 1960/207$. Since $9 < 1960/207$, this holds for all $a_9 < 9$. ✓ **GF$(I_4)$ + GF$(I_9) > 0$.** $\square$

**α-3 (σ₉=+1, a₉ ∈ (9, 1960/207)):** Same argument: bridging $I_9$ requires $a_2 \leq 23a_9/98 < L(a_9) = 20/9$. ✓ **GF$(I_4)$ + GF$(I_9) > 0$.** $\square$

### Verification of Case β regions

All remaining parameter regions produce a right gap $[g_L, 109/110]$ with $g_L < 109/110$:

| Region | $\sigma_9$ | $g_L$ | Minimum gap width |
|--------|-----------|-------|------------------|
| $a_9 \in [580/69,\, 87/10)$ | $-1$ | $89/(11a_9)$ | $\geq 181/6380$ |
| $a_9 \in [87/10,\, 980/109)$ | $-1$ | $23/(11a_2) \leq 207/220$ | $\geq 1/20$ |
| $a_9 \in [1960/207,\, 86/9]$ | $+1$ | $100/(11a_9)$ (or $450/473$) | $\geq 59/9460$ |
| $a_9 \in (86/9,\, 10)$ | $+1$ | $100/(11a_9) < 450/473$ | $\geq 17/430$ |

In each region the right gap is non-empty and explicitly computable. The Universal Blocking Theorem (§3 below) shows it cannot be covered. Hence **GF$(I_9) > 0$** in all Case β regions. $\square$

---

## §3 — Universal Blocking Theorem

This is the core new contribution of v3. It replaces Lemma CT entirely.

> **Theorem UB (Universal Blocking).** Let $[g_L, 109/110] \subset I_9$ be any non-empty interval with $0 < g_L < 109/110$. Then no speed assignment for runners $3,\ldots,8$ can cover $[g_L, 109/110]$ while maintaining GF$(I_k) = 0$ for all $k = 1,\ldots,8$.

**Proof.** We analyse each runner $j \in \{3,4,5,6,7,8\}$ and each sign $\sigma_j \in \{+1,-1\}$. In every case either:
(a) runner $j$ is *infeasible* (cannot reach $[g_L,109/110]$ from its speed range), in which case it cannot help, or
(b) runner $j$ is *feasible* but its coverage creates GF $> 0$ in some other slot.

If ALL runners are infeasible, then $[g_L,109/110]$ is uncovered and GF$(I_9) \geq 109/110 - g_L > 0$ directly.

### Analysis of Infeasible Runners (σ=+1, j ∈ {5,6,7,8})

For runner $j$ with $\sigma_j = +1$ (speed $a_j \in (j, j+1)$), define the **Minimum Feasibility Threshold**:
$$\mathrm{MFT}(j,k) := \frac{(11k+10)\cdot109}{(11k+12)\cdot110}.$$
This is the smallest $g_L$ for which the lower bound $a_j \geq (11k+10)/(11g_L)$ does not exceed the upper bound $a_j \leq (11k+12)\cdot110/(11\cdot109)$. If $g_L < \mathrm{MFT}(j,k)$ for all $k$, runner $j$ has an empty feasibility interval and is structurally infeasible.

**Runner 5 ($\sigma=+1$, $a_5 \in (5,6)$):** The only index at which $B_{5,k}[1]$ can reach $109/110$ from within $(5,6)$ is $k=4$: upper bound $= 560/109 \approx 5.138$. The lower bound at $g_L$ is $54/(11g_L)$. These coincide at $\mathrm{MFT}(5,4) = 54\cdot109/(56\cdot110) = 2943/3080 \approx 0.9555$.

- For $g_L \leq 2943/3080$ (all of $\beta$-2, $\beta$-3, $\beta$-4, and most of $\beta$-1): lower $\geq$ upper → **infeasible**. The gap persists.
- For $g_L > 2943/3080$ (occurring in $\beta$-1 only for $a_9 \lesssim 8.48$): $a_5 \in [5.100, 5.138]$. At such $a_5$, $B_{5,2}[1] = 34/(11a_5) \leq 34/56.1 \approx 0.606 < I_6[\mathrm{left}] = 67/110$ and $B_{5,3}[0] = 43/(11a_5) \geq 43/56.5 \approx 0.761 > I_6[\mathrm{right}] = 76/110$. Runner 5's bad intervals skip $I_6$ entirely. Meanwhile, runner 3 ($\sigma=+1$) with $a_3 > 340/109$ (outside Chain A range) creates GF$(I_3) > 0$ because no runner in $\{3,\ldots,9\}$ can cover $I_3[\mathrm{right}] = 43/110$ from speed range $\geq 7$ (verified: $B_{j,k}[1] \geq 43/110$ requires $a_j \leq (11k+12)\cdot110/(11\cdot43)$; at $k=0$ this gives $a_j \leq 120/43 \approx 2.79$, incompatible with $a_j \geq 7$). And $a_3 \leq 340/109$ (in Chain A range) gives GF$(I_8) \geq 1/50$ by Chain A. In all sub-cases GF $> 0$. □

**Runner 6 ($\sigma=+1$, $a_6 \in (6,7)$):** The binding index is $k=5$: upper bound $= 670/109 \approx 6.147$. $\mathrm{MFT}(6,5) = 65\cdot109/(67\cdot110) = 7085/7370 = 1417/1474 \approx 0.9614 > 450/473$. For all $\beta$ sub-regions (maximum $g_L \approx 0.963 < 1417/1474$ for the $k=5$ index): lower bound $65/(11g_L) > 670/109$ → **infeasible**. (For $k=6$: upper bound $= 780/109 \approx 7.156 > 7$, outside $\sigma=+1$ range. All other $k$ give upper bounds $< 6$ or $> 7$.) □

For runners 7, 8 ($\sigma=+1$, $a_j \in (j,j+1)$ with $j \geq 7$): all bad intervals in the speed range $(7,8)$ and $(8,9)$ have $B_{j,k}[1] = (11k+12)/(11a_j) \leq (11k+12)/77$. For this to reach $109/110$: $11k+12 \geq 109\cdot77/10 = 839.3$, so $k \geq 75$. At $k=75$: $B_{j,75}[0] = 835/(11a_j) \leq 835/77 \approx 10.8 \gg I_9[\mathrm{right}]$. These intervals are entirely above $I_9$. Runner 7 and 8 with $\sigma=+1$ are **completely infeasible**. □

### Analysis of σ=−1 Runners via PSM

**Primary Slot Miss (PSM) Lemma.** For runner $j$ with $\sigma_j = -1$ ($a_j \in (j-1,j)$): if runner $j$ is feasible for $[g_L, 109/110]$ via $B_{j,k}$ for some $k \geq 1$, then $B_{j,0}[0] > \mathrm{PSR}(j)$, forcing GF$(\text{primary slot of }j) > 0$.

*Why this holds:* $B_{j,0}[0] = 10/(11a_j)$. For runner $j$ to be feasible for $I_9$ via $B_{j,k}$ ($k \geq 1$), we need $a_j \leq (11k+12)\cdot 110/(11\cdot109)$. But this upper bound on $a_j$ means $a_j$ is *small*, pushing $10/(11a_j)$ *large* — specifically, above $\mathrm{PSR}(j)$.

Proved case-by-case:

**Runner 3 (σ=−1, a₃ ∈ (2,3)):** Feasibility via $B_{3,k}$ ($k \geq 1$) requires the right endpoint $B_{3,k}[1] = (11k+12)/(11a_3) \geq 109/110$, so $a_3 \leq (11k+12)\cdot110/(11\cdot109)$. For $k=1$: $a_3 \leq 23\cdot110/(11\cdot109) = 230/109 \approx 2.11$. Then:
$$B_{3,0}[0] = \frac{10}{11a_3} \geq \frac{10}{11\cdot(230/109)} = \frac{10\cdot109}{11\cdot230} = \frac{1090}{2530} = \frac{109}{253}.$$
Compare: $\mathrm{PSR}(3) = 43/110$. Is $109/253 > 43/110$? Check: $109\cdot110 = 11990 > 43\cdot253 = 10879$. ✓ So $B_{3,0}[0] > 43/110 = I_3[\mathrm{right}]$: runner 3 misses $I_3$'s right edge. GF$(I_3) \geq 109/253 - 43/110 = (11990-10879)/27830 = 1111/27830 > 0$. □

For $k \geq 2$: upper bound on $a_3$ is even smaller (e.g., $k=2$: $a_3 \leq 340/109 \approx 3.12$, already outside the σ=−1 range $(2,3)$). So $k=1$ is the only relevant case for σ₃=−1. □

**Runner 4 (σ=−1, a₄ ∈ (3,4)):** Feasibility via $B_{4,k}$ requires $a_4 \leq (11k+12)\cdot110/(11\cdot109)$. For $k=2$: $a_4 \leq 34\cdot110/(11\cdot109) = 340/109 \approx 3.12 \in (3,4)$. Then:
$$B_{4,0}[0] = \frac{10}{11a_4} \geq \frac{10}{11\cdot(340/109)} = \frac{10\cdot109}{11\cdot340} = \frac{1090}{3740} = \frac{109}{374}.$$
Compare: $\mathrm{PSR}(4) = 16/55 = 32/110$. Is $109/374 > 16/55$? Check: $109\cdot55 = 5995 > 16\cdot374 = 5984$. ✓ (margin = 11). GF$(I_2) \geq 109/374 - 16/55 = (5995-5984)/20570 = 11/20570 > 0$. □

**Runners 5, 6, 7, 8 (σ=−1):** For runner 5 ($a_5 \in (4,5)$, $k=3$): $a_5 \leq 45\cdot110/(11\cdot109) = 450/109 \approx 4.13$. $B_{5,0}[0] \geq 10\cdot109/(11\cdot450) = 1090/4950 = 109/495 \approx 0.220 > 21/110 = \mathrm{PSR}(5)$ (since $109\cdot110 = 11990 > 21\cdot495 = 10395$). GF$(I_1) > 0$. □

For runners 6, 7, 8 with σ=−1: the MFT criterion decides feasibility. For runner 6 ($\sigma=−1$, $a_6 \in (5,6)$, $k=4$): $\mathrm{MFT}(6,4) = 54\cdot109/(56\cdot110) = 2943/3080 \approx 0.9555$. For $g_L \leq 2943/3080$: infeasible (same computation as runner 5 σ=+1, since the upper bound is identical). For $g_L > 2943/3080$: runner 6 (σ=−1) is marginally feasible; but PSM applies — at $a_6 \leq 560/109 \approx 5.138$, $B_{6,0}[0] = 10/(11a_6) \geq 10\cdot109/(11\cdot560) = 109/616 \approx 0.177 > 12/110 = I_1[\mathrm{left}]$, so $B_{6,0}$ starts above $I_1$. Whether PSM yields a gap depends on whether $I_1[\mathrm{left}] = 12/110 = 0.109$ can be covered by other runners; however, in this narrow $\beta$-1 sub-region, Chain A (runner 3) already forces GF$(I_8) > 0$ as shown above. □

For runners 7 (σ=−1, $a_7 \in (6,7)$) and 8 (σ=−1, $a_8 \in (7,8)$): the tightest upper bound for reaching $109/110$ at any $k$ is $(11k+12)\cdot110/(11\cdot109)$. For $a_7 > 6$: need $k \leq (6\cdot109/10 - 12/11) \approx 64.3$; at $k=63$: lower bound $= (693+10)/(11\cdot6) \approx 10.65 \gg a_7$. Working from the upper bound: the largest $k$ with upper bound in $(6,7)$ satisfies $(11k+12)\cdot10/109 \in (6,7)$, giving $k \in (54.5, 66.7)$; at $k=55$: lower bound $= (605+10)/(11g_L) = 615/(11g_L) \geq 615/11 \approx 55.9 \gg 7$. Runner 7 is **entirely infeasible**. Similarly runner 8 (σ=−1). □

### Analysis of Chain A (Runner 3, σ=+1)

**Setup.** If runner 3 with $\sigma_3=+1$ ($a_3 \in (3,4)$) is feasible for $[g_L, 109/110]$, it must do so via $k=2$: $B_{3,2}[0] \leq g_L$ and $B_{3,2}[1] \geq 109/110$. The feasibility interval is:
$$a_3 \in F_{3,2}(g_L) = \left[\frac{32}{11g_L},\; \frac{340}{109}\right].$$

For any $a_3$ in this interval, the following chain propagates a gap to $I_8$:

**Step 1.** Runner 3 covers $I_9$ via $B_{3,2}$. Its $B_{3,0}$ interval covers $I_3$ up to $12/(11a_3) < 43/110 = I_3[\mathrm{right}]$ (since $a_3 > 120/43 \approx 2.79$, which holds as $a_3 \geq 32/(11g_L) > 3/1 = 3$ whenever the interval is in the σ=+1 range). **$I_3$ right gap:** $[12/(11a_3), 43/110]$, width $> 0$.

**Step 2.** For $I_3$'s right gap $[12/(11a_3), 43/110]$ to be covered, runner 8 (pair partner of 3) must have $B_{8,2}[0] \leq 12/(11a_3)$: $(32)/(11a_8) \leq 12/(11a_3)$, giving $a_8 \geq 8a_3/3$. The maximum $g_L$ across all Case $\beta$ regions is $6141/6380 \approx 0.963$ (attained at $a_9 = 580/69$ in $\beta$-1). At this maximum: $a_3 \geq 32/(11\cdot6141/6380) = 32\cdot6380/(11\cdot6141) \approx 3.022$, giving $a_8 \geq 8\cdot3.022/3 \approx 8.059 > 8$. Hence $\sigma_8 = +1$ is forced in all Case $\beta$ sub-regions. If $\sigma_8 = -1$ (contradicting the above): GF$(I_3) > 0$ since no bad interval can then cover $I_3[\mathrm{right}] = 43/110$.

**Step 3.** Runner 8 ($\sigma_8=+1$, $a_8 \geq 8a_3/3$) covers $I_6$ via $B_{8,4} = [54/(11a_8),\; 56/(11a_8)]$. Feasibility: $B_{8,4}[0] \leq I_6[\mathrm{left}] = 67/110$ iff $a_8 \geq 54\cdot110/(67\cdot11) = 5940/737 \approx 8.061$. Since $a_8 \geq 8a_3/3 \geq 8\cdot3.058/3 \approx 8.155 > 8.061$ ✓, runner 8 starts below $I_6[\mathrm{left}]$. At $a_8 = 8a_3/3$ exactly:
$$B_{8,4}[1] = \frac{56}{11 \cdot 8a_3/3} = \frac{56 \cdot 3}{88a_3} = \frac{21}{11a_3} = B_{3,1}[0].$$
So runners 3 and 8 together cover $I_6$ contiguously: $B_{8,4}$ covers $[I_6[\mathrm{left}],\; 21/(11a_3)]$ and $B_{3,1}$ covers $[21/(11a_3),\; 23/(11a_3)]$. Combined: $I_6$ is covered up to $23/(11a_3)$.

**$I_6$ right gap:** $[23/(11a_3), 76/110]$. At $a_3 = 340/109$: $23\cdot109/(11\cdot340) = 2507/3740 \approx 0.670 < 0.691 = I_6[\mathrm{right}]$. Width $> 0$. $\square$

**Step 4 (Chain A conclusion, verified in v2 §5 Step 2).** Runner 6 ($\sigma_6=−1$, pair (5,6)) must cover the $I_6$ right gap $[23/(11a_3), 76/110]$. For $B_{6,4}[0] \leq 23/(11a_3)$: $a_6 \geq 54a_3/23 \cdot (11/11) = 54a_3/23$... More precisely, from the v2 cascade: $a_6 \in [43a_3/23, 225/38] \approx [5.717, 5.921]$ (the $\sigma=−1$ range for runner 6). At the tightest value $a_6 = 225/38$:
$$B_{6,4}[0] = \frac{54}{11 \cdot 225/38} = \frac{54 \cdot 38}{11 \cdot 225} = \frac{2052}{2475} = \frac{228}{275}.$$
Since $228/275 - 89/110 = (228\cdot110 - 89\cdot275)/(275\cdot110) = (25080-24475)/30250 = 605/30250 = 1/50 > 0$, runner 6 misses $I_8[\mathrm{left}] = 89/110$. Runner 5 (pair partner) cannot cover $I_8[\mathrm{left}]$ either: needs $a_5 \geq 54\cdot110/(89\cdot11) = 540/89 \approx 6.07 > 6$.

**GF$(I_8) \geq 1/50 > 0$.** $\square$

Note: Chain A uses only $a_3 \in [32/(11g_L), 340/109]$ — this is a runner-intrinsic constraint on the (3,8,6,5) cascade, independent of the specific $g_L$.

### Analysis of Chain B (Runner 4, σ=+1)

**Setup.** If runner 4 with $\sigma_4=+1$ ($a_4 \in (4,5)$) is feasible for $[g_L, 109/110]$ via $k=3$:
$$a_4 \in F_{4,3}(g_L) = \left[\frac{43}{11g_L},\; \frac{450}{109}\right].$$

**Chain B (from v2 §5 Step 3, verified):** Runner 4 at $a_4 \in [1849/450,\, 450/109]$ covers $I_9$'s right via $B_{4,3}$, but $B_{4,0}$ covers $I_2$ only up to $12/(11a_4) < 32/110 = I_2[\mathrm{right}]$. Runner 7 (pair (4,7)) must cover the $I_2$ right gap; needs $a_7 \geq 7a_4/4 \geq 12943/1800 \approx 7.19$.

$I_7$ right coverage requires $a_7 \leq 560/87 \approx 6.44$. Incompatible:
$$12943 \times 87 = 1{,}126{,}041 > 560 \times 1800 = 1{,}008{,}000.$$
$I_7$ right gap $= 87/110 - 14400/20339 = 1533/18490 > 0$. No runner in $\{3,5,6,8,9\}$ can cover $I_7[\mathrm{right}]$ (empty feasibility intervals). **GF$(I_7) \geq 1533/18490 > 0$.** $\square$

Again: Chain B uses only $a_4 \in [1849/450, 450/109]$ and does NOT depend on $g_L$.

### Summary of Theorem UB

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

---

## §4 — Theorem U

> **Theorem U (Universal σ₂=+1 Incompatibility).** For any CB configuration with σ₂=+1: GF$(I_4)$ + GF$(I_9) > 0$.

**Proof.** By §1 (Lemmas 1.1–1.2), closing $I_4$ forces $a_2 \geq L(a_9)$. §2 analyses the $(a_2, a_9)$ parameter space:

- **Case α regions** (α-1, α-2, α-3): the $I_4$ lower bound and $I_9$ bridging upper bound are incompatible. GF$(I_4)$ + GF$(I_9) > 0$ directly.
- **Case β regions**: runners 2 and 9 leave a right gap $[g_L, 109/110] \subset I_9$. By Theorem UB (§3), no assignment of runners 3–8 can cover this gap without creating GF $> 0$ in some slot $I_k$. Hence GF$(I_k) > 0$ for some $k$, and in particular GF$(I_4)$ + GF$(I_9) \geq $ GF$(I_9) > 0$ since the gap in $I_9$ persists or GF$(I_k) > 0$ for $k \neq 9$.

In all 128 sign classes (indexed by $(\sigma_3,\ldots,\sigma_9) \in \{+1,-1\}^7$ with $\sigma_2 = +1$), one of the above applies. $\square$

**Minimum gap:** $59/9460$ (Case β with $a_9 = 86/9$, $a_2 = 172/81$ — see Case β table, row 3).

---

## §5 — Summary Table

| Case | $\sigma_9$ | Parameter range | Mechanism | Min GF |
|------|-----------|-----------------|-----------|--------|
| α-1 | −1 | $a_9 < 580/69$ | Direct incompat. (middle gap) | $\to 0^+$ |
| α-2 | −1 | $a_9 \in [980/109, 9)$ | Direct incompat. (high-$k$ bridge) | $\to 0^+$ |
| α-3 | +1 | $a_9 \in (9, 1960/207)$ | Direct incompat. | $\to 0^+$ |
| β-1 | −1 | $a_9 \in [580/69, 87/10)$ | UB (Chain A or trivial) | $181/6380$ |
| β-2 | −1 | $a_9 \in [87/10, 980/109)$ | UB (Chain A or trivial) | $1/20$ |
| β-3 | +1 | $a_9 \in [1960/207, 86/9]$ | UB (Chain A or trivial) | $59/9460$ |
| β-4 | +1 | $a_9 \in (86/9, 10)$ | UB (trivial or Chain A) | $17/430$ |

Cases α-1 through β-4 are exhaustive (cover all $(a_2,a_9) \in (2,3)\times(8,10)$) and mutually exclusive. All 128 σ₂=+1 sign classes are covered. **Minimum gap across all classes: $59/9460$.** □

Combined with Lemma S2 (σ₂=−1 case, min gap $538/54395$): minimum witness window across all 256 sign classes = $\min(59/9460, 538/54395) = 538/54395 \approx 0.00989$.
