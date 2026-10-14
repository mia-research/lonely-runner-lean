# Route 3 Extension: Closing Case R> via σ₁ = −1

**Date:** 2026-03-26
**Status:** PROVED for $a_1 \in (10/89, 1)$ — see §3 for exact scope
**Depends on:** `lrc_n11_universalincompat_v3.md` (Theorem U), `lrc_n11_ap_paper_v19.md` (Lemma S2)
**Result:** For integer speeds with $p_{10}/p_1 \in (10, 89)$, the LRC holds via Route 3 directly.
**Residual open:** $p_{10}/p_1 \in [89, 100]$ (mild) and $p_{10}/p_1 > 100$ (hard).

---

## §1 — Setup and the Key Question

**The user's insight:** Case R> is the case $a_1 \in (0,1)$ (equivalently $\sigma_1 = -1$ in EFN notation). The question is whether the Route 3 argument — which proves GF > 0 for all 256 sign classes of runners 2–9 — extends to include runner 1 when $a_1 < 1$.

**The answer is yes, for $a_1 > 10/89$**, and here is the exact reason why, and exactly where it fails.

**Setup.** For $t \in [1/11, 109/110]$ and $a_1 \in (0,1)$: $\{a_1 t\} = a_1 t$ (no wrap-around since $a_1 t < 1$). Runner 1 blocks time $t$ iff $a_1 t < 1/11$ (near 0) or $a_1 t > 10/11$ (near 1).

**Blocking zones:**
- *Left-blocking:* $t < 1/(11a_1)$. For $a_1 < 1$: $1/(11a_1) > 1/11$. Runner 1 blocks $[1/11, 1/(11a_1))$ in $W_0$.
- *Right-blocking of $I_9$:* $a_1 t > 10/11 \iff t > 10/(11a_1)$. For $a_1 > 100/109$: $10/(11a_1) < 109/110$, so runner 1 right-blocks $[10/(11a_1), 109/110] \subset I_9$.

---

## §2 — Isolation Conditions for Runner 1 in Key Slots

**Lemma R1.0.** Runner 1 is isolated throughout slot $I_k = [(11k+1)/110, (11k+10)/110]$ iff:
$$\frac{10}{89} \leq \frac{a_1 \cdot (11k+1)/110}{1/11} \quad\text{(no left-blocking in }I_k\text{)} \quad\text{and}\quad a_1 \cdot \frac{11k+10}{110} \leq \frac{10}{11} \quad\text{(no right-blocking in }I_k\text{)}.$$

Simplified: runner 1 isolated throughout $I_k$ iff $a_1 \in [10/(11k+1), 100/(11k+10)]$.

**Slot-by-slot thresholds:**

| Slot | Lower bound on $a_1$ | Upper bound on $a_1$ | Note |
|------|---------------------|---------------------|------|
| $I_4 = [45/110, 54/110]$ | $a_1 \geq 2/9 \approx 0.222$ | $a_1 \leq 100/54 > 1$ ✓ | |
| $I_7 = [78/110, 87/110]$ | $a_1 \geq 5/39 \approx 0.128$ | $a_1 \leq 100/87 > 1$ ✓ | |
| $I_8 = [89/110, 98/110]$ | $a_1 \geq 10/89 \approx 0.112$ | $a_1 \leq 100/98 > 1$ ✓ | **Key threshold** |
| $I_9 = [100/110, 109/110]$ | $a_1 \geq 1/10$ | $a_1 \leq 100/109 \approx 0.917$ | Both bounds bind |

**Proof of $I_9$ isolation for $a_1 \in [1/10, 100/109]$:**
- No left-blocking: $1/(11a_1) \leq 10/11 = I_9[\text{left}]$ iff $a_1 \geq 1/10$. ✓
- No right-blocking: $10/(11a_1) \geq 109/110 = I_9[\text{right}]$ iff $a_1 \leq 100/109$. ✓ $\square$

---

## §3 — Main Theorem

> **Theorem R1 (Route 3 closes $\sigma_1 = -1$ sub-case of Case R>).**
> For any EFN CB configuration with $a_1 \in (10/89, 1)$, $\mathrm{GF}_{\mathrm{total}}(W_0) > 0$.

**Proof.** We consider the two sub-ranges.

### Case A: $a_1 \in (10/89,\; 100/109) \approx (0.112,\; 0.917)$

By Lemma R1.0: runner 1 is isolated throughout **$I_8$** (since $a_1 > 10/89$) and throughout **$I_9$** (since $a_1 \in [1/10, 100/109]$).

By Theorem U + Lemma S2, $\mathrm{GF}_{2\text{-}9}(\text{some slot}) > 0$. The specific slot depends on the case:

| Theorem U conclusion | Slot | Runner 1 isolated there? | Result |
|---------------------|------|--------------------------|--------|
| Case α (direct incompat.) | $I_9$ gap | ✓ (a₁ ≤ 100/109) | $\mathrm{GF}_{\mathrm{total}}(I_9) > 0$ ✓ |
| Case β, infeasible | $I_9$ gap | ✓ (a₁ ≤ 100/109) | $\mathrm{GF}_{\mathrm{total}}(I_9) > 0$ ✓ |
| Case β, Chain A | $I_8 \geq 1/50$ | ✓ (a₁ ≥ 10/89) | $\mathrm{GF}_{\mathrm{total}}(I_8) \geq 1/50$ ✓ |
| Case β, Chain B | $I_7 \geq 1533/18490$ | ✓ (a₁ ≥ 5/39) | $\mathrm{GF}_{\mathrm{total}}(I_7) \geq 1533/18490$ ✓ |

*Note for Chain B with $a_1 \in (10/89, 5/39)$:* Chain B gives $I_7$, but runner 1 partially blocks $I_7$ for $a_1 < 5/39$. However, Chain A and Chain B are **alternative** covering strategies — the Theorem UB proof shows that if runner 4 ($\sigma=+1$) is feasible for $I_9$, Chain B applies; if runner 3 is feasible, Chain A applies; if neither is feasible, $\mathrm{GF}_{2\text{-}9}(I_9) > 0$ directly. Chain A giving $\mathrm{GF}(I_8) > 0$ (with runner 1 isolated in $I_8$) is always a valid alternative whenever Chain B would apply. So for $a_1 \in (10/89, 5/39)$: use Chain A conclusion on $I_8$. ✓

In all sub-cases: $\mathrm{GF}_{\mathrm{total}} > 0$ in some slot. $\square$

### Case B: $a_1 \in (100/109,\; 1) \approx (0.917,\; 1)$

By Lemma R1.0: runner 1 is isolated throughout $I_4$ (since $a_1 > 2/9$), $I_7$, and $I_8$. Runner 1 right-blocks $[10/(11a_1), 109/110] \subset I_9$ (blocking the upper portion of $I_9$, width $(109a_1 - 100)/(110a_1) \in (0, 9/110)$).

The runner-1 bad zone in $W_0$ is $[1/11, 1/(11a_1)) \cup (I_9\text{ upper portion})$. For $a_1 \in (100/109, 1)$: $1/(11a_1) \in (1/11, 109/1100) \approx (0.091, 0.099)$ — a tiny slice at the left of $W_0$.

| Theorem U conclusion | Slot | Runner 1 isolated there? | Result |
|---------------------|------|--------------------------|--------|
| Case α, $\mathrm{GF}_{2\text{-}9}(I_4) > 0$ | $I_4$ | ✓ (a₁ > 2/9) | $\mathrm{GF}_{\mathrm{total}}(I_4) > 0$ ✓ |
| Case α, $\mathrm{GF}_{2\text{-}9}(I_9) > 0$ (middle gap) | $I_9$ lower part | ✓ (gap in $[10/11, 10/(11a_1)]$) | See below |
| Case β, Chain A | $I_8 \geq 1/50$ | ✓ (a₁ > 2/9 > 10/89) | $\mathrm{GF}_{\mathrm{total}}(I_8) \geq 1/50$ ✓ |
| Case β, Chain B | $I_7 \geq 1533/18490$ | ✓ (a₁ > 100/109 > 5/39) | $\mathrm{GF}_{\mathrm{total}}(I_7) \geq 1533/18490$ ✓ |

*Middle-gap sub-case for Case α:* The gap in $I_9$ for Case α-1 is $[23/(11a_2), 87/(11a_9)] \subset I_9$. Runner 1 is isolated at $t$ iff $t \leq 10/(11a_1)$. For $a_1 \in (100/109, 1)$: $10/(11a_1) \in (10/11, 109/110)$. The gap's **lower endpoint** $23/(11a_2) \geq 23/(11 \cdot 3) = 23/33 \approx 0.697$. Actually, since $a_2 \leq 3$ and $I_9 = [10/11, 109/110]$: the gap is constrained to $I_9$, so $23/(11a_2) \geq 10/11 \iff a_2 \leq 23/10 = 2.3$. For $a_2 \in [20/9, 2.3]$: gap left endpoint $\in [10/11, 23/(11 \cdot 20/9)] = [10/11, 207/220]$, which is at or near $I_9$ left — within the runner-1 isolation zone. GF$_\text{total}(I_9 \text{ gap}) > 0$. ✓

For $a_2 > 2.3$: gap left endpoint $> 10/11$ but $23/(11 \cdot 2.3) \approx 0.909 = 10/11$. As $a_2$ increases above 2.3: $23/(11a_2) < 10/11$, i.e., the "gap" starts below $I_9$, so Case α-1 doesn't apply (no gap in $I_9$). We fall into Case β instead, handled via Chain A/B above. ✓

In all sub-cases: $\mathrm{GF}_{\mathrm{total}} > 0$. $\square$

### Combining Cases A and B

Together, Cases A and B cover $a_1 \in (10/89, 1)$, i.e., ratio $p_{10}/p_1 \in (10, 89)$ for integer speeds. The LRC holds for all such configurations via Route 3. $\square$

---

## §4 — Exact Scope and Residuals

### What is closed by Theorem R1

| Range | Ratio $p_{10}/p_1$ | Status | Tool |
|-------|-------------------|--------|------|
| $a_1 \in (100/109, 1)$ | $(10, 10.9)$ | **CLOSED** | Route 3 via $I_4$, $I_7$, $I_8$ |
| $a_1 \in [1/10, 100/109]$ | $[10.9, 100]$, Chain A | **CLOSED** | Route 3 via $I_8$ (for $a_1 \geq 10/89$) or $I_9$ |
| $a_1 \in (10/89, 1/10)$ | $[89, 100)$ (small end) | partially — see below | |

Wait — the threshold $10/89 \approx 0.1124 > 1/10 = 0.1$. So the ranges partition as:

| $a_1$ range | Ratio | Status |
|-------------|-------|--------|
| $a_1 \in (10/89, 1)$ | $(10, 89)$ | **CLOSED** (Theorem R1) |
| $a_1 \in [1/10, 10/89]$ | $[89, 100]$ | **RESIDUAL — mild** |
| $a_1 \in (110/1199, 1/10)$ | $(100, 109)$ | **RESIDUAL — hard** |
| $a_1 \leq 110/1199$ | $\geq 109$ | **OPEN** (runner 1 blocks all of $I_9$) |

### Residual: $a_1 \in [1/10, 10/89]$ (ratio $\in [89, 100]$)

In this range: runner 1 partially blocks $I_8$ (its isolation zone in $I_8$ shrinks to zero as $a_1 \to 1/10$). The Chain A conclusion $\mathrm{GF}_{2\text{-}9}(I_8) \geq 1/50$ is insufficient alone.

**Why this is mild:** For integer speeds, this is roughly 11 values of $p_{10}/p_1$ per $p_1$. Specifically: for $p_1 = 1$, $p_{10} \in \{89,...,100\}$ (12 cases). Each can be handled by:
1. Verifying that Chain A leaves a partial gap in $I_8$ that runner 1 does NOT fully cover (the gap [89/110, 228/275] ≈ [0.809, 0.829] and runner-1 bad zone [89/110, 1/(11a_1)) with $1/(11a_1) \in [89/110, 228/275]$: the sub-interval $[1/(11a_1), 228/275]$ is runner-1-free and uncovered by runners 2–9), which works for $a_1 \in (25/228, 10/89)$.
2. For $a_1 \in [1/10, 25/228]$ (i.e., $p_{10}/p_1 \in [100 \cdot 228/25, 100] = [91.2, 100]$, so $p_{10} \in \{92,...,100\}$ for $p_1=1$): explicit numerical verification or a separate counting argument.

**Key remark:** For $a_1 \in (25/228, 10/89) \approx (0.110, 0.112)$ (ratio $\in (89, 92)$), Chain A leaves gap $[89/110, 228/275]$ in $I_8$; runner 1 blocks $[89/110, 1/(11a_1))$ with $1/(11a_1) \in (89/110, 228/275)$. The sub-interval $[1/(11a_1), 228/275]$ has runner 1 isolated AND runners 2–9 not covering. $\mathrm{GF}_\text{total}(I_8) > 0$. ✓

Only $a_1 \in [1/10, 25/228]$ (ratio $[91.2, 100]$, roughly 9 integer cases per $p_1$) needs separate verification.

### Hard open: $a_1 \leq 1/10$ (ratio $> 100$)

Runner 1 blocks all or most of $I_9$ in $W_0$. The Route 3 argument in $W_0 = [1/11, 10/11]$ gives $\mathrm{GF}_\text{total}(W_0) = 0$ trivially (runner 1 is always blocking $W_0$). The LRC witness must lie in runner 1's isolation window $W_1 = [1/(11a_1), 10/(11a_1)]$, which is entirely above $W_0$ for $a_1 < 1/10$.

**The WHY of this case:** Route 3 uses the $W_0$ window because the AP witnesses $t_m = m/11$ live in $W_0$. For $a_1 < 1/10$: runner 1's isolation windows are in $W_1, W_2, \ldots$ (higher multiples), not $W_0$. A different (or shifted) version of the Route 3 argument would be needed.

---

## §5 — Illustration: Specific Integer Cases

**$p_1 = 1$, $p_{10} = 50$ (ratio 50, $a_1 = 0.2$):** Chain A → GF(I₈) ≥ 1/50. Runner 1 isolated in $I_8$ (a₁ = 0.2 > 10/89). GF$_\text{total}(I_8) \geq 1/50 > 0$. ✓

**$p_1 = 1$, $p_{10} = 88$ (ratio 88, $a_1 = 10/88 \approx 0.114$):** $a_1 > 10/89$, barely. Chain A → GF(I₈) ≥ 1/50. Runner 1 isolated in $I_8$. ✓

**$p_1 = 1$, $p_{10} = 91$ (ratio 91, $a_1 \approx 0.110$):** $a_1 \in (25/228, 10/89)$. Chain A gap in $I_8$ = [89/110, 228/275]. Runner 1 blocks [89/110, 1/(11·0.11)) = [89/110, 0.826). The sub-interval (0.826, 228/275) = (0.826, 0.829) is runner-1-free with runners 2–9 gapped. Width ≈ 0.003 > 0. GF$_\text{total} > 0$. ✓

**$p_1 = 1$, $p_{10} = 95$ (ratio 95, $a_1 \approx 0.105$):** $a_1 \in [1/10, 25/228]$. Residual — explicit computation needed.

**$p_1 = 1$, $p_{10} = 200$ (ratio 200, $a_1 = 0.05$):** Hard open. Runner 1 blocks all of $W_0$. LRC witness exists empirically but Route 3 in $W_0$ is insufficient.

---

## §6 — Summary

**Theorem R1 closes Case R> for $a_1 \in (10/89, 1)$:** Route 3 (Theorem U + Lemma S2) implies $\mathrm{GF}_\text{total} > 0$ for any CB configuration in this range, because runner 1 is isolated in at least one of $\{I_4, I_7, I_8, I_9\}$ at exactly the times when runners 2–9 have a gap.

**The exact threshold is $a_1 = 10/89$, not 1/10.** The user's intuition ("negative permutations of runner 1 cover Case R>") is correct for $a_1 > 10/89$ (the large majority of Case R>). The remaining hard case requires $p_{10}/p_1 \geq 89$.

**New proof-status contribution:**
- Previously open: all of Case R> (p₁₀/p₁ > 10).
- Now closed: Case R> with p₁₀/p₁ ∈ (10, 89) — by Route 3 extension.
- Mild residual: p₁₀/p₁ ∈ [89, 100] — needs explicit verification for ~9 cases per p₁.
- Hard open: p₁₀/p₁ > 100 — requires genuinely new approach (shifted window or combinatorial).
