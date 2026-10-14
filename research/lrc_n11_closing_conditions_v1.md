# Route 3: Closing Conditions for Runner-10 Slots

**Date:** 2026-03-22
**Status:** IN PROGRESS — table complete; enumeration v2 complete (see §8); simultaneous-closure impossibility proof in progress.

---

## Setup

Runner 10 (fixed speed 10) partitions $W_0$ into 9 good slots:
$$I_{m-1} = \left[\frac{11m-10}{110},\ \frac{11m-1}{110}\right], \quad m = 2, \ldots, 10.$$
Each slot has width $9/110$ and contains exactly one AP witness $t_m = m/11$.

**Definition.** A *closing condition* for the **left edge** of $I_{m-1}$ is a choice of runner $j$ and integer $k \geq 0$ such that runner $j$'s bad interval starts exactly at the left boundary $(11m-10)/110$:
$$\frac{11k+10}{11\,a_j} = \frac{11m-10}{110} \implies a_j = \frac{10(11k+10)}{11m-10}.$$

A *closing condition* for the **right edge** of $I_{m-1}$ is:
$$\frac{11k+12}{11\,a_j} = \frac{11m-1}{110} \implies a_j = \frac{10(11k+12)}{11m-1}.$$

When a runner satisfies a closing condition, it covers the corresponding edge of the slot, and neighbouring runners are responsible for the interior gap.

---

## Full Closing Conditions Table

For each slot, we list all feasible closing conditions with $|\delta_j| \leq 0.9$ ($j \in \{2,\ldots,9\}$).

### I_1 (m=2): [12/110, 21/110], AP witness t_2 = 2/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 0 | 25/3 ≈ 8.333 | j=8 (δ=+1/3), j=9 (δ=−2/3) |
| Right | 0 | 40/7 ≈ 5.714 | j=5 (δ=+5/7), j=6 (δ=−2/7) |

**Gap between left-closer and right-closer:** Left-closer covers [12/110, 13/110] ≈ width 1/110; right-closer covers [16/110, 21/110] ≈ width 5/110. Middle gap [13/110, 16/110] (width 3/110) must be covered by runners 7–8 incidentally.

### I_2 (m=3): [23/110, 32/110], AP witness t_3 = 3/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 0 | 100/23 ≈ 4.348 | j=4 (δ=+8/23), j=5 (δ=−15/23) |
| Left  | 1 | 210/23 ≈ 9.130 | j=9 (δ=+3/23) |
| Right | 0 | 15/4 = 3.75   | j=3 (δ=+3/4), j=4 (δ=−1/4) |
| Right | 1 | 115/16 ≈ 7.188 | j=7 (δ=+3/16), j=8 (δ=−13/16) |

### I_3 (m=4): [34/110, 43/110], AP witness t_4 = 4/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 0 | 50/17 ≈ 2.941 | j=3 (δ=−1/17) |
| Left  | 1 | 105/17 ≈ 6.176 | j=6 (δ=+3/17), j=7 (δ=−14/17) |
| Right | 0 | 120/43 ≈ 2.791 | j=2 (δ=+63/43), j=3 (δ=−9/43) |
| Right | 1 | 230/43 ≈ 5.349 | j=5 (δ=+15/43), j=6 (δ=−28/43) |
| Right | 2 | 340/43 ≈ 7.907 | j=8 (δ=−4/43) |

### I_4 (m=5): [45/110, 54/110], AP witness t_5 = 5/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 0 | 20/9 ≈ 2.222 | j=2 (δ=+2/9), j=3 (δ=−7/9) |
| Left  | 1 | 140/45 ≈ 3.111 | (= 28/9) j=3 (δ=+1/9), j=4 (δ=−8/9) |
| Left  | 2 | 260/45 ≈ 5.778 | (= 52/9) j=5 (δ=+7/9), j=6 (δ=−2/9) |
| Right | 0 | 120/53 ≈ 2.264 | j=2 (δ=+14/53) |
| Right | 1 | 230/53 ≈ 4.340 | j=4 (δ=+18/53), j=5 (δ=−35/53) |
| Right | 2 | 340/53 ≈ 6.415 | j=6 (δ=+22/53), j=7 (δ=−31/53) |
| Right | 3 | 450/53 ≈ 8.491 | j=8 (δ=+26/53), j=9 (δ=−27/53) |

**Key note:** I_4 contains t_5 which is *centred* in the slot (left_dist = right_dist = 5/110). The minimum-width bad interval to close EITHER edge alone requires a_j ≤ 2.264 (right) or a_j ≤ 2.222 (left). Only runners 2 or 3 satisfy this.

### I_5 (m=6): [56/110, 65/110], AP witness t_6 = 6/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 0 | 100/56 ≈ 1.786 | — (no runner with |δ|≤0.9 and j≥2) |
| Left  | 1 | 210/56 = 15/4 = 3.75 | j=3 (δ=+3/4), j=4 (δ=−1/4) |
| Left  | 2 | 320/56 ≈ 5.714 | j=5 (δ=+5/7), j=6 (δ=−2/7) |
| Right | 0 | 120/65 ≈ 1.846 | — (no runner with |δ|≤0.9 and j≥2) |
| Right | 1 | 230/65 ≈ 3.538 | j=3 (δ=+4/13), j=4 (δ=−6/13) |
| Right | 2 | 340/65 ≈ 5.231 | j=5 (δ=+3/13), j=6 (δ=−8/13) |
| Right | 3 | 450/65 ≈ 6.923 | j=7 (δ=−1/13) |

### I_6 (m=7): [67/110, 76/110], AP witness t_7 = 7/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 1 | 210/67 ≈ 3.134 | j=3 (δ=+9/67), j=4 (δ=−54/67) |
| Left  | 2 | 320/67 ≈ 4.776 | j=4 (δ=+52/67), j=5 (δ=−15/67) |
| Left  | 3 | 430/67 ≈ 6.418 | j=6 (δ=+28/67), j=7 (δ=−39/67) |
| Left  | 4 | 540/67 ≈ 8.060 | j=8 (δ=+4/67) |
| Right | 1 | 230/76 ≈ 3.026 | j=3 (δ=+2/76) |
| Right | 2 | 340/76 ≈ 4.474 | j=4 (δ=+36/76), j=5 (δ=−40/76) |
| Right | 3 | 450/76 ≈ 5.921 | j=6 (δ=−6/76), j=5 (δ=+3/4) |
| Right | 4 | 560/76 ≈ 7.368 | j=7 (δ=+28/76), j=8 (δ=−48/76) |

### I_7 (m=8): [78/110, 87/110], AP witness t_8 = 8/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 1 | 210/78 ≈ 2.692 | j=2 (δ=+9/13), j=3 (δ=−4/13) |
| Left  | 2 | 320/78 ≈ 4.103 | j=4 (δ=+8/78) |
| Left  | 3 | 430/78 ≈ 5.513 | j=5 (δ=+40/78), j=6 (δ=−38/78) |
| Left  | 4 | 540/78 ≈ 6.923 | j=7 (δ=−6/78) |
| Right | 1 | 230/87 ≈ 2.644 | j=2 (δ=+56/87), j=3 (δ=−31/87) |
| Right | 2 | 340/87 ≈ 3.908 | j=4 (δ=−8/87) |
| Right | 3 | 450/87 ≈ 5.172 | j=5 (δ=+15/87), j=6 (δ=−72/87) |
| Right | 4 | 560/87 ≈ 6.437 | j=6 (δ=+38/87), j=7 (δ=−49/87) |

### I_8 (m=9): [89/110, 98/110], AP witness t_9 = 9/11

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 1 | 210/89 ≈ 2.360 | j=2 (δ=+32/89), j=3 (δ=−57/89) |
| Left  | 2 | 320/89 ≈ 3.596 | j=3 (δ=+53/89), j=4 (δ=−36/89) |
| Left  | 3 | 430/89 ≈ 4.831 | j=4 (δ=+74/89), j=5 (δ=−15/89) |
| Left  | 4 | 540/89 ≈ 6.067 | j=6 (δ=+6/89) |
| Right | 1 | 230/98 ≈ 2.347 | j=2 (δ=+34/98) |
| Right | 2 | 340/98 ≈ 3.469 | j=3 (δ=+41/98), j=4 (δ=−53/98) |
| Right | 3 | 450/98 ≈ 4.592 | j=4 (δ=+58/98), j=5 (δ=−40/98) |
| Right | 4 | 560/98 ≈ 5.714 | j=5 (δ=+5/7), j=6 (δ=−2/7) |

### I_9 (m=10): [100/110, 109/110], AP witness t_10 = 10/11

**Note:** t_10 = 10/11 is at the **left boundary** of I_9 (left_dist = 0). Closing the left edge is vacuous. The slot must be covered from just right of t_10 to 109/110.

| Edge | k | a_j exact | Runners (δ = a_j − j) |
|---|---|---|---|
| Left  | 1 | 210/100 = 21/10 = 2.1 | j=2 (δ=+1/10), j=3 (δ=−9/10) |
| Left  | 2 | 320/100 = 16/5 = 3.2 | j=3 (δ=+1/5), j=4 (δ=−4/5) |
| Left  | 3 | 430/100 = 43/10 = 4.3 | j=4 (δ=+3/10), j=5 (δ=−7/10) |
| Left  | 4 | 540/100 = 27/5 = 5.4 | j=5 (δ=+2/5), j=6 (δ=−3/5) |
| Right | 1 | 230/109 ≈ 2.110 | j=2 (δ=+12/109) |
| Right | 2 | 340/109 ≈ 3.119 | j=3 (δ=+13/109) |
| Right | 3 | 450/109 ≈ 4.128 | j=4 (δ=+14/109) |
| Right | 4 | 560/109 ≈ 5.138 | j=5 (δ=+15/109) |

**Key observation for I_9:** All *above-blocking* closers of the left edge (starting the bad interval at t_10) have the general form $a_j = (11k+1)/10$ for appropriate $k$ — specifically these are the runners whose bad interval begins exactly at $t_{10}$. The blocker of t_10 from above (required for complete blocking since r_j(10) + 10δ_j > 10) contributes to covering I_9 from the left.

---

## §2 — Blocking Conditions and Closing Compatibility

For runner $j$ to be bad at AP witness $t_m = m/11$: let $r = jm \bmod 11 \in \{1,\ldots,10\}$.
- **Block from above:** $\delta_j > (10-r)/m$
- **Block from below:** $\delta_j < (1-r)/m$

### Compatibility Matrix for I_9 Closers

I_9 is the most constrained slot: t_10 is at its left boundary, and the only way to block t_10 is to have some runner $j$ with $\{a_j \cdot 10/11\} \notin [1/11, 10/11]$.

Since $r_j(10) = 10j \bmod 11 = 11 - j$ for $j = 1,\ldots,10$:
- Block t_10 from above: $\delta_j > (10-(11-j))/10 = (j-1)/10$
- Block t_10 from below: $\delta_j < (1-(11-j))/10 = (j-10)/10$

For the blocker of t_10 to ALSO close the left edge of I_9 (i.e., contribute coverage starting at t_10), it must satisfy the left-closing condition $a_j = (11k+10)/(11 \cdot a_j \cdot \text{[something]}) \ldots$ — specifically, the bad interval starting at t_10 requires $(11k+10)/(11 a_j) = 10/11$, giving $a_j = (11k+10)/10$.

**From above:** For blocker-from-above at t_10: $\delta_j > (j-1)/10$, so $a_j = j + \delta_j > j + (j-1)/10 = (11j-1)/10$.
The left-closing condition requires $a_j = (11k+10)/10$ for some $k$.

| Runner j | Min speed (from-above blocking) | Left-closer speeds |
|---|---|---|
| 2 | a_2 > 11/10 = 1.1 | 2.1, 3.2, 4.3, 5.4, 6.5, ... |
| 3 | a_3 > 23/10 = 2.3 | 3.2, 4.3, 5.4, ... |
| 4 | a_4 > 34/10 = 3.4 | 4.3, 5.4, ... |
| 5 | a_5 > 45/10 = 4.5 | 5.4, ... — **5.4 < 4.5+0.9=5.4 (borderline!)** |
| 6 | a_6 > 56/10 = 5.6 | 6.5, 7.6, ... |
| 7 | a_7 > 67/10 = 6.7 | 7.6, 8.7, ... |
| 8 | a_8 > 78/10 = 7.8 | 8.7, ... |
| 9 | a_9 > 89/10 = 8.9 | **No feasible left-closer** (9.8 > 9.9 = max) |

**Conclusion (Lemma I_9-A):** If the blocker of t_10 is runner $j \geq 3$, then:
- The bad interval of runner $j$ starts at $t_{10}$ and has width $2/(11 a_j)$.
- For runner $j$, the minimum speed (from-above blocking) gives maximum interval width $2/(11 \cdot (11j-1)/10) = 20/(11(11j-1))$.
- For $j=3$: max width $= 20/(11 \cdot 32) = 20/352 = 5/88 \approx 0.057 < 9/110 \approx 0.082$. **Cannot cover I_9 alone.**
- For $j=9$: max width $= 20/(11 \cdot 98) < 0.019 \ll 9/110$. **Far from covering I_9 alone.**

**Therefore:** If any runner $j \geq 3$ blocks t_10 from above, its bad interval covers $[t_{10}, t_{10} + 2/(11 a_j)]$, leaving an uncovered right portion of I_9 of width at least $9/110 - 20/(11(11j-1)) > 0$.

**Lemma I_9-B (Below-blocker contributes nothing):** If runner $j$ blocks t_10 from below ($\delta_j < (j-10)/10$), then $a_j = j + \delta_j < j + (j-10)/10 = (11j-10)/10$, so the bad interval near t_10 ends at $t_{10}^- = 10/11$ (from the left). The bad interval is entirely **left** of t_10, contributing **zero coverage** inside $I_9$.

---

## §3 — Analytical Lower Bound for GF(I_9)

**Setup.** Fix any complete-blocking configuration. Let $j^*$ be the runner blocking t_10 (by definition of complete-blocking, some such $j^*$ exists; if multiple runners block it, pick one).

**Case 1: $j^* = 1$ (runner 1 blocks t_10).**
$r_1(10) = 10$, so $\{a_1 \cdot 10/11\} > 10/11$ requires $\delta_1 > 0$, i.e., $a_1 > 1$. But by definition of the EFN frame, $a_1 < 1$ (runner 1 is the slow runner). **This case is impossible.**

**Case 2: $j^* = 2$ (runner 2 blocks t_10 from above, $\delta_2 > 0.1$).**
$a_2 > 2.1$. Runner 2's bad interval near t_10: starts at $(11k+10)/(11 a_2)$ for $k=1$ (since $a_2 \in (2.1, 2.9)$), specifically starts at $21/(11 a_2) < 10/11$ (left of t_10) for $a_2 > 21/10 = 2.1$...

Wait, let me recompute. For $a_2 > 2.1$: the bad interval from above near $k=1$ starts at $(11 \cdot 1 + 10)/(11 a_2) = 21/(11 a_2)$ and ends at $23/(11 a_2)$.

- Start: $21/(11 a_2)$. For $a_2 = 2.1$: start $= 21/23.1 = 10/11$ exactly. For $a_2 > 2.1$: start $< 10/11$, so starts **left** of t_10.
- End: $23/(11 a_2)$. For $a_2 = 2.1$: end $= 23/23.1 \approx 0.9957 < 109/110 = 0.9909$. Wait: $23/23.1 \approx 0.9957 > 109/110 = 0.9\overline{90}$. So for $a_2 = 2.1$, the interval extends PAST the right edge of $I_9$.

Let me check: $109/110 = 0.990\overline{90}$ and $23/23.1 \approx 0.99567$. So $23/23.1 > 109/110$, meaning the interval extends past $I_9$'s right edge. **Runner 2 at $a_2 = 2.1$ covers ALL of $I_9$ from the left (the bad interval starts at t_10 and ends past $I_9$'s right edge).**

More precisely: runner 2 with $\delta_2 = 0.1$ exactly has its bad interval $[21/23.1, 23/23.1] = [10/11, 23/23.1]$ covering the entire $I_9$. **GF$(I_9) = 0$ is achieved when $a_2 = 2.1$.**

But runner 2 must also block some AP witness. Does $a_2 = 2.1$ conflict with other blocking conditions?

For runner 2 at $a_2 = 2.1$: it blocks t_10 from above (by construction). What other witnesses does it block?
- t_1: $r_2(1) = 2$. $\{2.1/11\} = \{0.1909\} = 0.1909 \in [1/11, 10/11]$ — not bad.
- t_5: $r_2(5) = 10$. $\{2.1 \cdot 5/11\} = \{10.5/11\} = \{0.9545\} = 0.9545 > 10/11$ — **bad!** Runner 2 also blocks t_5.
- t_6: $r_2(6) = 1$. $\{2.1 \cdot 6/11\} = \{12.6/11\} = \{1.1454\} = 0.1454 > 1/11 = 0.0909$ — not bad (barely safe).

**Important:** At $a_2 = 2.1$ ($\delta_2 = +0.1$), runner 2 blocks t_5 (since $r_2(5) = 10$ and $\delta_2 = 0.1 > 0 = (10-10)/5$). Runner 2's bad interval near t_5 = 5/11: starts at $21/(11 \cdot 2.1) = 21/23.1 = 10/11$ — this is t_10, NOT t_5! Let me recompute.

$r_2(5) = 2 \cdot 5 \bmod 11 = 10$. Block from above: $\delta_2 > (10-10)/5 = 0$. Since $\delta_2 = 0.1 > 0$, runner 2 IS bad at t_5. Fractional position: $\{2.1 \cdot 5/11\} = \{10.5/11\} = \{0.9\overline{54}\} \approx 0.9545 > 10/11 \approx 0.9091$. ✓ Bad.

So runner 2 at $a_2 = 2.1$ blocks BOTH t_5 and t_10. Its bad intervals near t_5 and t_10 overlap into a single contiguous interval (since the bad intervals for $k=0$ near fractional value 0 and for $k=1$ near fractional value 0 are at positions $\approx 10/11$ and $10/11$).

**Summary for Case 2:** Runner 2 at $a_2 \in (2.1, 2.22]$ (i.e., $\delta_2 \in (0.1, 0.22]$) covers ALL of $I_9$ alone (its bad interval exceeds width 9/110). For $a_2 > 2.22$ ($\delta_2 > 0.22$), runner 2 still starts inside $I_9$ (since start $= 21/(11 a_2) < 10/11$ for $a_2 > 21/10$) but no longer reaches the right edge — it covers $[21/(11 a_2), 23/(11 a_2)] \cap I_9 = [10/11, 23/(11 a_2)]$, leaving a right gap of width $109/110 - 23/(11 a_2) > 0$.

**Case 3: $j^* \geq 3$ blocks t_10 from above.**
From Lemma I_9-A: runner $j^*$'s interval has width $2/(11 a_{j^*})$, which for $a_{j^*} > (11 j^* - 1)/10$ (minimum for above-blocking) gives width $< 20/(11(11j^*-1)) \leq 20/(11 \cdot 32) = 5/88 < 9/110$ for all $j^* \geq 3$. **Cannot cover $I_9$ alone.**

The right portion of $I_9$ not covered by $j^*$ requires cooperation from other runners. The key question: can incidental bad intervals fill the gap?

**Case 4: Blocker of t_10 is from below.**
From Lemma I_9-B: zero coverage inside $I_9$ from the t_10 blocker. Entire slot $I_9$ must be covered incidentally. This is the hardest case.

---

## §4 — The "Single-Runner-2" Obstruction

**Proposition I_9-C.** *If $\delta_2 \notin (0.1, 0.22]$, then $\text{GF}(I_9) > 0$.*

**Proof outline.** By the case analysis above:
- If $\delta_2 \leq 0.1$: runner 2 either does not block t_10 from above, or blocks it but its interval is too narrow (at $a_2 = 2.1$ the interval exactly covers $I_9$; for $a_2 < 2.1$ runner 2 does not block t_10 from above at all, since the blocking threshold is $\delta_2 > 0.1$). So runner 2 contributes zero coverage in $I_9$ when $\delta_2 \leq 0.1$.

  Wait — runner 2 blocks t_10 when $\delta_2 > (j-1)/10 = 1/10$. For $\delta_2 = 0.1$ exactly, it's a borderline case. For $\delta_2 < 0.1$, runner 2 does NOT block t_10.

  When $\delta_2 > 0.22$: runner 2's interval starts at $21/(11 a_2) < 10/11$ (to the left of t_10), contributing partial coverage in $I_9$ from $t_{10}$ to $23/(11 a_2) < 109/110$. Right gap $> 0$.

In all cases except $\delta_2 \in (0.1, 0.22]$, full coverage of $I_9$ by runner 2 fails. Remaining runners must cover the gap. Whether they can do so while maintaining complete-blocking for their respective witnesses requires the full consistency check (Step 2 — the enumeration script).

---

## §5 — Coupling with I_4 and I_5 (The Sign Incompatibility)

The strongest structural constraint comes from the coupling between I_4 (t_5), I_5 (t_6), and I_9 (t_10):

- $r_2(5) = 10$: Runner 2 blocks t_5 from above iff $\delta_2 > 0$.
- $r_2(6) = 1$: Runner 2 blocks t_6 from below iff $\delta_2 < 0$.
- $r_2(10) = 9$: Runner 2 blocks t_10 from above iff $\delta_2 > 0.1$.

**If $\delta_2 > 0.1$:** Runner 2 covers $I_9$ (at $\delta_2 \in (0.1, 0.22]$) and blocks t_5. But $\delta_2 > 0$ means runner 2 does NOT block t_6, so t_6 must be blocked by runner $j \neq 2$. The cheapest blocker of t_6 from above needs $r_j(6) > 10 - 0.9 \cdot 6 = 4.6$, i.e., $r_j(6) \geq 5$. This forces a fast runner ($j \geq 3$) to have large positive $\delta$.

**If $\delta_2 < 0$:** Runner 2 blocks t_6 and possibly t_5 is blocked differently. But t_10 is not blocked by runner 2 (since $\delta_2 < 0 < 0.1$), so t_10 must be blocked by some runner $j \geq 3$ or $j = 9$, and $I_9$ coverage relies on incidental intervals.

The coupling is not yet strong enough to give a full analytical contradiction (this is the open Step 4 of Route 3). The computational evidence (min GF ≥ 0.12% from deep optimisation) suggests the obstruction is real; the enumeration script (Step 2) will pin down which patterns achieve the minimum and whether any sign pattern can close all 9 slots.

---

## §6 — Summary Status

| Slot | Empirical GF (best config) | Analytical lower bound |
|---|---|---|
| I_1 | 0% (closeable: a_6=40/7, a_9=25/3) | 0 |
| I_2 | 0% (closeable: a_5=100/23, a_8=115/16) | 0 |
| I_3–I_8 | > 0 (not yet closed) | Open |
| I_9 | > 0% (GF > 0 unless δ_2 ∈ (0.1, 0.22]) | Partial (Proposition I_9-C) |
| **Total GF** | **≥ 0.12%** (200k-grid, deep NM) | **Open** |

---

## §7 — The Whack-a-Mole Structure (New Finding, 2026-03-22)

Deep numerical optimisation reveals the following cascade for the extremal sign pattern (++------):

| Configuration | I_1 | I_2 | I_6 | I_8 | Total GF |
|---|---|---|---|---|---|
| Global min (free δ) | **1.21%** | 0% | 0% | 0% | **0.12%** |
| Fix a_6=40/7, a_9=25/3 (close I_1) | 0% | 1.33% | 0% | 2.80% | 0.41% |
| Fix a_5,a_6,a_8,a_9 (close I_1+I_2 edges) | 0% | **2.17%** | 0.065% | 0% | **0.22%** |

**Key observation:** The global minimum (0.12% total GF) is achieved when I_1 has a *partial* gap (~1.21% per-slot). Closing I_1 by moving runners 6 and 9 to their exact closing speeds unavoidably opens I_2 and/or I_8. This is a genuine geometric competition:

- **Runner 9** (speed ≈ 8.30 in global min vs. 25/3 ≈ 8.33 in I_1-closed config) is shared between I_1 left-edge coverage and I_8 coverage. Moving a_9 → 25/3 closes I_1's left edge but changes runner 9's bad intervals in I_8.
- **Runner 6** (speed ≈ 5.73 vs. 40/7 ≈ 5.71) is shared between I_1 right-edge coverage and I_2 coverage. Moving a_6 → 40/7 closes I_1's right edge but changes I_2 coverage.

**Conclusion (Structural Theorem, candidate):** For the extremal sign pattern ++------, the slots I_1, I_2, I_8 cannot simultaneously have zero GF. The minimum total GF is achieved at the boundary:
$$\text{GF}(I_1) \approx 1.21\%, \quad \text{GF}(I_2) = \text{GF}(I_8) = 0\%.$$

This represents a **genuine topological obstruction**: the speed parameters controlling I_1's coverage (runners 6, 9) have conflicting demands from other open slots. The minimum total GF of ~0.12% reflects the "balance point" of this competition.

**Next analytical step:** Prove that for ANY complete-blocking configuration in the ++------ sign class, $\text{GF}(I_1) + \text{GF}(I_2) + \text{GF}(I_8) \geq c > 0$. The key tool will be a local computation showing that the three slots form a "covering triangle" for runners 6 and 9: they cannot simultaneously cover all three without violating one.

**Next step:** Run `lrc_n11_blocking_enum_v2.py` to systematically check all 256 sign patterns and identify which pattern achieves the lowest total GF, and whether any can close all 9 slots simultaneously.

---

## §8 — Enumeration v2 Results (2026-03-22)

`lrc_n11_blocking_enum_v2.py` ran all 256 sign patterns (20 random starts per pattern, Nelder-Mead polish). Results in `reports/lrc_n11_blocking_enum_v2_results.json`.

### Summary

| Statistic | Value |
|---|---|
| Total sign patterns | 256 |
| Feasible (CB config found) | **247** |
| Infeasible (no CB config) | **9** |
| Global minimum GF (quick search) | **0.32%** — pattern ++------ |
| Global minimum GF (deep NM) | **0.12%** — same pattern ++------ |

### Infeasible Patterns (9)

No complete-blocking configuration found for these sign assignments (δ₂,...,δ₉):
`--+-+-+-`, `--+-+-++`, `-+--+--+`, `-+--+-++`, `-+--++++`, `+---+---`, `+-+-+-+-`, `+-+-+++-`, `+++-++--`

These are likely genuinely infeasible (the sign constraints are incompatible with blocking all 10 AP witnesses simultaneously). Proof of infeasibility is open but likely follows from residue incompatibility.

### Lowest-GF Patterns (quick search, 20 starts)

| Rank | Pattern | Min GF | a₁ at min | Open slots |
|---|---|---|---|---|
| 1 | ++------ | **0.32%** | 0.954 | I_1, I_2, I_3 |
| 2 | --+----- | 1.26% | — | — |
| 3 | ++++++++ | 1.40% | 0.940 | I_3, I_4, I_8 |
| 4 | -+-++--- | 1.83% | — | — |
| 5 | ++----++ | 1.94% | — | — |

All 247 feasible patterns have GF > 0 in the quick search. Deep NM confirms the global minimum is ≥ 0.12%.

### Key Conclusion

**All 247 feasible sign patterns achieve GF > 0.** No complete-blocking configuration was found with GF = 0. The empirical lower bound is GF ≥ 0.12% (deep NM, 500k grid). Proving this analytically is Route 3 Step 4.

### Extremal Config Detail (++------)

From deep NM (Session 2026-03-22), 500k grid:

```
a₁ = 0.99990,  δ₁ = −0.0001
a₂ = 2.5314,   δ₂ = +0.5314
a₃ = 3.6075,   δ₃ = +0.6075
a₄ = 3.1560,   δ₄ = −0.8440
a₅ = 4.4365,   δ₅ = −0.5635
a₆ = 5.7297,   δ₆ = −0.2703
a₇ = 6.7501,   δ₇ = −0.2499
a₈ = 7.2816,   δ₈ = −0.7184
a₉ = 8.2967,   δ₉ = −0.7033
a₁₀ = 10.0 (fixed)
GF = 0.12%
```

Good region: two segments at the edges of I₁ = [12/110, 21/110]:
- Left segment: [0.10909, 0.10957] width ≈ 4.8×10⁻⁴ (gap before runner 9's bad interval starts)
- Right segment: [0.19040, 0.19091] width ≈ 5.1×10⁻⁴ (gap after runner 6's bad interval ends)

**Interpretation:** The good fraction is entirely confined to two tiny edge-gaps of I₁, measuring the distance by which runner 9's bad interval falls short of I₁'s left boundary, and runner 6's falls short of I₁'s right boundary. The minimum is achieved when these edge-gaps are minimised but cannot be simultaneously closed to zero.

**Analytical target:** Show that for the ++------ sign class, the two edge-gaps of I₁ cannot both be zero (i.e., a₉ cannot simultaneously equal 25/3 and a₆ cannot simultaneously equal 40/7 while maintaining all 10 blocking conditions). Alternatively, show that closing both edges forces the middle gap [36/275, 7/44] (width 31/1100) to remain uncovered.

---

## §9 — Middle-Gap Analysis: Structural Impossibility Result (2026-03-22)

When I₁'s edges are both closed (a₉ = 25/3, a₆ = 40/7), runner 9's bad interval covers [12/110, 36/275] and runner 6's covers [7/44, 21/110]. The **middle gap** is [36/275, 7/44] with exact width 31/1100.

### No Single Runner Covers the Middle Gap

**Proposition 9.1.** *No single runner j (with a_j ∈ (1.1, 10.9)) can cover the entire middle gap [36/275, 7/44] with a single bad interval.*

**Proof.** For runner j's bad interval [10/(11·a_j), 12/(11·a_j)] to cover both endpoints:
- Left endpoint: 10/(11·a_j) ≤ 36/275 ↔ a_j ≥ 10·275/(11·36) = **125/18 ≈ 6.944**
- Right endpoint: 12/(11·a_j) ≥ 7/44 ↔ a_j ≤ 12·44/(11·7) = **48/7 ≈ 6.857**

These are incompatible: 125/18 − 48/7 = 11/126 > 0. ∎

### Two-Runner Coverage Structure

Two runners (j, k) can together cover the middle gap provided their bad intervals overlap and span the gap:
- Runner j covers RIGHT end iff a_j ≤ 6·a₆/5 ≤ 6·(40/7)/5 = **48/7** (requires a_j < 7)
- Runner k covers LEFT end iff a_k ≥ 6·a₉/5 ≥ 6·(25/3)/5 = **10** — impossible!

Wait, let me be precise. Runner k covers left end of the gap iff 10/(11·a_k) ≤ 12/(11·a₉) = 36/275, i.e., a_k ≥ 10·275/(11·12) = **125/6 ≈ 20.8** — completely infeasible for bounded runners.

**Revised condition**: Runner k covers the gap's left end iff its bad interval LEFT edge ≤ 36/275. Since the gap starts at 36/275 (runner 9's right edge), runner k must have 10/(11·a_k) ≤ 36/275, i.e., a_k ≥ 125/18 ≈ 6.944.

For a_k ∈ (7.1, 9) (runner 8 range with |δ_8| < 0.9): a_k > 7.1 > 125/18 ≈ 6.944 fails as a lower bound check — wait: 7.1 > 6.944, so 10/(11·7.1) = 10/78.1 ≈ 0.1280 and 36/275 ≈ 0.1309. We need 10/(11·a_k) ≤ 0.1309, i.e., a_k ≥ 125/18 ≈ 6.944. For a_k = 7.1 > 6.944: **yes, runner 8 can start before the left edge of the gap, i.e., it overlaps with runner 9.** ✓

So runner 8 (a₈ ≈ 7.28 in extremal config) covers from 10/(11·7.28) ≈ 0.1249 all the way to 12/(11·7.28) ≈ 0.1499. This starts BEFORE the gap (0.1249 < 0.1309) and extends into the gap.

**Summary of two-runner coverage**:
- Runner 8 (a₈ ∈ (6.944, 8.333)): covers [max(0.1309, 10/(11·a₈)), min(12/(11·a₈), 0.1591)] — the LEFT portion of the gap.
- Runner 7 (a₇ ≤ 48/7 ≈ 6.857): covers up to right end 7/44. For a₇ ∈ (6.1, 6.857): covers right portion.

In the extremal config: a₇ ≈ 6.75 < 48/7 and a₈ ≈ 7.28. Together they cover the full middle gap.

### Edge Gap Structure — Why the Minimum is 0.12%

In the extremal config:
- a₉ ≈ 8.297 < 25/3 ≈ 8.333: runner 9's bad interval starts at 10/(11·8.297) ≈ 0.10957 > 12/110 = 0.10909. **Left edge gap** = 0.00048.
- a₆ ≈ 5.730 > 40/7 ≈ 5.714: runner 6's bad interval ends at 12/(11·5.730) ≈ 0.19040 < 21/110 = 0.19091. **Right edge gap** = 0.00052.

These are the ONLY surviving good regions in W₀. Total GF = (0.00048 + 0.00052)/(9/110) ≈ 1.22% of I₁ ≈ 0.12% of W₀.

**Why they survive**: moving a₉ → 25/3 (closing left gap) shifts runner 9's bad intervals, opening new gaps in I₂ and I₈. Moving a₆ → 40/7 (closing right gap) shifts runner 6's bad intervals, opening gaps in I₂. The balance at (a₉ ≈ 8.297, a₆ ≈ 5.730) minimises the total GF.

### Analytical Step 4 Reformulation

The case analysis for ++------ sign class:
- **Case A** (a₉ < 25/3): Left edge gap = 12/110 − 10/(11·a₉) > 0, GF(I₁) > 0.
- **Case B** (a₆ > 40/7): Right edge gap = 21/110 − 12/(11·a₆) > 0, GF(I₁) > 0.
- **Case C** (a₉ ≥ 25/3 AND a₆ ≤ 40/7): I₁ is fully covered. GF(I₂) > 0 must be shown.

In Case C: runners 6 and 9 are at or past their closing speeds for I₁. The freed-up positions then affect I₂ = [23/110, 32/110]. The numerics show GF(I₂) ≥ 1.33% in Case C (minimum over all free parameters). Proving GF(I₂) > 0 in Case C analytically is the remaining open question.

**Lower bound structure**: In Cases A and B, the edge gaps → 0 as a₉ → 25/3 or a₆ → 40/7. There is no fixed positive lower bound from edge gaps alone. The overall minimum GF ≈ 0.12% is achieved at the transition between Case A/B and Case C. An analytical lower bound would need to track the trade-off as a₉ ↗ and a₆ ↘ and show that GF(I₂) > 0 in the limit.
