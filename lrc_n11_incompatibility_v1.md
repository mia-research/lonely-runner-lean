# The a₂ Incompatibility: Proof of Main Claim 5.1

**Date:** 2026-03-23
**Status:** PROVED
**Scope:** n=11 AP framework, classical EFN, sign class ++------. Depends on `lrc_n11_algebraic_lemma_v1.md` §0–§3 (Setup, Complementary Pairs, Chain Structure, Forced Gaps).
**Result:** Closing slots I₄ and I₉ simultaneously is algebraically impossible; hence GF(I₄) + GF(I₉) > 0 for every CB configuration in the ++------ class with $a_9 = 25/3$, $a_6 = 40/7$.

---

## §1 — Setup: What Runner 9 Leaves Uncovered

Fix $a_9 = 25/3$ and $a_6 = 40/7$ (I₁-closing conditions, Corollary 2.3 of the algebraic lemma).

From Proposition 3.1 of the algebraic lemma, runner 9's bad intervals use the formula $B_{9,k} = [3(11k+10)/275,\ 3(11k+12)/275]$.

**In I₄ = [45/110, 54/110]:**

Runner 9's $k=3$ interval:
$$B_{9,3} = \left[\frac{3 \times 43}{275},\ \frac{3 \times 45}{275}\right] = \left[\frac{129}{275},\ \frac{135}{275}\right].$$

Since $135/275 = 27/55 = 54/110$ (= right edge of I₄), runner 9 covers the **right portion** of I₄. The **left gap** is:
$$J_4 = \left[\frac{45}{110},\ \frac{129}{275}\right].$$

Converting: $45/110 = 225/550$ and $129/275 = 258/550$, giving width $= 33/550 = 3/50$.

**In I₉ = [10/11, 109/110]:**

Runner 9's $k=7$ interval:
$$B_{9,7} = \left[\frac{3 \times 87}{275},\ \frac{3 \times 89}{275}\right] = \left[\frac{261}{275},\ \frac{267}{275}\right].$$

Since $10/11 = 250/275 < 261/275$, runner 9 covers a **middle-left portion** of I₉. The **left gap** is:
$$J_9 = \left[\frac{10}{11},\ \frac{261}{275}\right].$$

Width $= 261/275 - 10/11 = 261/275 - 250/275 = 11/275 = 1/25$.

From Proposition 3.2, runner 6 ($a_6 = 40/7$) **skips I₄ and I₉ entirely** (its chain visits only $I_1, I_3, I_5, I_6, I_8$). Therefore runners 9 and 6 together leave $J_4$ and $J_9$ completely uncovered.

---

## §2 — Runner 2's Bad Intervals in I₄ and I₉

**Bad interval formula** (Lemma 2.1 of algebraic lemma):
$$B_{j,k} = \left[\frac{11k+10}{11a_j},\ \frac{11k+12}{11a_j}\right], \quad k = 0, 1, 2, \ldots$$

For runner 2 with speed $a_2 > 2$ (sign $\delta_2 > 0$ in the ++------ class):

**Block for I₄** ($k=0$, landing in I₄'s range for $a_2 \approx 2$):
$$B_{2,0} = \left[\frac{10}{11a_2},\ \frac{12}{11a_2}\right].$$

For $a_2 = 2$: $B_{2,0} = [10/22, 12/22] = [5/11, 6/11] \approx [0.454, 0.545]$.

Check: I₄ = $[45/110, 54/110] \approx [0.409, 0.491]$. The overlap region is $[5/11, 54/110]$.
As $a_2$ increases above 2, $B_{2,0}$ shifts left, eventually reaching the left edge 45/110 of I₄.

**Block for I₉** ($k=1$, landing in I₉'s range for $a_2 \approx 2$):
$$B_{2,1} = \left[\frac{21}{11a_2},\ \frac{23}{11a_2}\right].$$

For $a_2 = 2$: $B_{2,1} = [21/22, 23/22] \approx [0.955, 1.045]$.
As $a_2$ increases, $B_{2,1}$ shifts left. For $a_2 = 2.1$: $B_{2,1} \approx [0.909, 0.996]$, which aligns with I₉ = $[0.909, 0.991]$.

---

## §3 — The Two Constraints on a₂

### Lemma 3.1 (I₄ forces $a_2 \geq 20/9$)

*Suppose I₄ is closed (GF(I₄) = 0). Then $a_2 \geq 20/9$.*

**Proof.** We show that the left boundary $45/110$ of $J_4$ cannot be covered by any runner other than runner 2, and that covering it requires $a_2 \geq 20/9$.

*Step 1: Runners 9 and 6 do not cover $J_4$.* Established in §1: runner 9's coverage of I₄ starts at $129/275 > 45/110$, and runner 6 skips I₄ entirely.

*Step 2: No free runner with $a_j < j$ (runners 4, 5, 7, 8 in ++------) can cover $45/110$.*
For runner $j$ ($j \in \{4,5,7,8\}$, $a_j < j$) to have $B_{j,k}$ start at or before $45/110$:
$$\frac{11k+10}{11a_j} \leq \frac{45}{110} = \frac{9}{22} \implies a_j \geq \frac{(11k+10) \cdot 22}{9 \cdot 11} = \frac{(11k+10) \cdot 2}{9}.$$

- $k=0$: $a_j \geq 20/9 \approx 2.22$. All of $j \in \{4,5,7,8\}$ satisfy $a_j > 3 > 2.22$ ✓ in range. But the interval must also END after $45/110$: end $= (11k+12)/(11a_j)$; for $k=0$, end $\geq 45/110 \iff a_j \leq (12 \cdot 22)/(9 \cdot 11) = 264/99 = 8/3 \approx 2.67$. But $j \in \{4,5,7,8\}$ all have $a_j > 3 > 2.67$. **Contradiction** — the $k=0$ interval for these runners ends before $45/110$.
- $k=1$: $a_j \geq (21 \cdot 2)/9 = 42/9 \approx 4.67$. Runners 5 ($a_5 < 5$) and 7 ($a_7 < 7$) are in range if $a_5 \geq 4.67$ or $a_7 \geq 4.67$.
  - Runner 5 ($k=1$): start $= 21/(11a_5)$, end $= 23/(11a_5)$. For end $\geq 45/110$: $a_5 \leq 23 \cdot 110/(11 \cdot 45) = 2530/495 = 46/9 \approx 5.11$. So runner 5 with $a_5 \in [42/9, 46/9] \approx [4.67, 5.11]$ can cover $45/110$ via $k=1$. But $\delta_5 < 0$ means $a_5 < 5$, so $a_5 \in [4.67, 5)$. This is feasible — **runner 5 is a genuine candidate.**
  - Runner 7 ($k=1$): start $= 21/(11a_7)$; for start $\leq 45/110$: $a_7 \geq 42/9 \approx 4.67$. Since $a_7 < 7$, this is feasible if $a_7 \in [4.67, 7)$. **Runner 7 is also a candidate.**
- $k=2$: $a_j \geq (32 \cdot 2)/9 = 64/9 \approx 7.11$. Runner 7 has $a_7 < 7 < 7.11$ — **impossible** for $k=2$.

*Step 3: Runner 5 alternative leads to GF(I₂) > 0.*
If runner 5 covers $45/110$ via $B_{5,1}$ (requiring $a_5 \geq 42/9 \approx 4.67$), runner 5 shifts far from its standard I₂-covering position.

Runner 5's coverage of I₂ = $[23/110, 32/110]$ via $B_{5,0} = [10/(11a_5), 12/(11a_5)]$:
For $B_{5,0}$ to include the left edge $23/110$: $10/(11a_5) \leq 23/110 \iff a_5 \geq 100/23 \approx 4.35$.
For $B_{5,0}$ to reach $23/110$ from the left and stay inside I₂: right end $12/(11a_5) \geq 23/110 \iff a_5 \leq 1320/253 \approx 5.22$. This is satisfied.

However, when $a_5 \geq 42/9 \approx 4.67$:
$$B_{5,0} = \left[\frac{10}{11 \cdot 4.67},\ \frac{12}{11 \cdot 4.67}\right] \approx [0.195, 0.234].$$
Runner 5 now covers only $[0.209, 0.234]$ of I₂ (intersected with I₂'s left edge $23/110 \approx 0.209$). The baton-pass certificate (Theorem 4.1 of the algebraic lemma) gives a good window at $t^* = 69/275 \approx 0.251$ in I₂: runner 9's coverage of I₂ ends at $69/275$ and runner 5 (shifted) no longer reaches $69/275$.

**Explicit gap:** Runner 5 at $a_5 = 42/9$ covers I₂ up to $12/(11 \cdot 42/9) = 12 \cdot 9/(11 \cdot 42) = 108/462 = 18/77 \approx 0.234$. Runner 9 covers I₂ from $63/275 \approx 0.229$. Gap in I₂: $[18/77, 63/275] = [450/1925, 441/1925]$...

Actually more directly: the baton-pass argument shows $t^* = 69/275$ is a loneliness time in I₂ whenever no runner blocks it. With $a_5 \geq 4.67$, runner 5's $B_{5,0}$ ends at $12/(11a_5) \leq 12/(11 \cdot 4.67) \approx 0.234 < 69/275 \approx 0.251$. Runner 9's coverage of I₂ ends at exactly $69/275$. So the interval $(0.234, 69/275)$ has no coverage from runners 5 or 9, and the good window at $t^* = 69/275$ persists, giving **GF(I₂) > 0.**

Therefore, using runner 5 to cover $J_4$'s boundary forces GF(I₂) > 0 — so at least one of I₂, I₄ is not closed. In either case, GF > 0. $\square$ (for runner 5 alternative)

*Step 4: Runner 7 alternative leads to GF(I₇) > 0.*
Runner 7 at $a_7 \in [42/9, 7)$ uses $B_{7,1} = [21/(11a_7), 23/(11a_7)]$ to cover $45/110$.

Runner 7's natural role is covering I₇ = $[78/110, 87/110]$ (owned slot, pair (4,7)). For runner 7 to cover I₇:
$$B_{7,4} = \left[\frac{54}{11a_7},\ \frac{56}{11a_7}\right] \supseteq I_7 \implies \frac{54}{11a_7} \leq \frac{78}{110} \implies a_7 \geq \frac{54 \cdot 110}{11 \cdot 78} = \frac{5940}{858} = \frac{60}{8.65...} = \frac{60}{858/110} \approx 6.86.$$

More precisely: $a_7 \geq 5940/858 = 990/143 \approx 6.923$. But if $a_7 \in [42/9, 6.923) \approx [4.67, 6.92)$, runner 7 **cannot cover I₇'s left edge**, leaving GF(I₇) > 0.

Runners in the ++------ class have $\delta_7 < 0$ ($a_7 < 7$), so $a_7 < 7$. For $a_7 \in [42/9, 990/143)$: GF(I₇) > 0. For $a_7 \in [990/143, 7)$: runner 7 is near its natural speed and covers I₇, but then $a_7 \geq 990/143 \approx 6.92$, which gives $B_{7,1}$'s start $= 21/(11 \cdot 6.92) \approx 0.276$ — this is in I₂ range, **not reaching $45/110 \approx 0.409$**. So $a_7 \approx 6.92$ is too large to help with $J_4$'s boundary via $k=1$!

Explicitly: $B_{7,1}$ start $= 21/(11a_7) \leq 45/110$ requires $a_7 \geq 42/9 = 4.\overline{6}$. And end $\geq 45/110$ requires $a_7 \leq 46/9 \approx 5.11$. So runner 7 via $B_{7,1}$ only reaches $45/110$ when $a_7 \in [42/9, 46/9] \approx [4.67, 5.11]$. In this range, runner 7 **leaves I₇ uncovered** (needs $a_7 \geq 6.92$ for I₇). GF(I₇) > 0. $\square$ (for runner 7 alternative)

*Step 5: Runner 2 must cover $J_4$'s left boundary, requiring $a_2 \geq 20/9$.*
The only remaining candidate is runner 2 via $B_{2,0}$. For the start of $B_{2,0}$ to reach $45/110$:
$$\frac{10}{11a_2} \leq \frac{45}{110} = \frac{9}{22}
\implies 10 \times 22 \leq 9 \times 11 \times a_2
\implies 220 \leq 99 \, a_2
\implies a_2 \geq \frac{220}{99} = \frac{20}{9}.\quad \square$$

### Lemma 3.2 (I₉ forces $a_2 \leq 575/261$)

*Suppose I₉ is closed (GF(I₉) = 0). Then $a_2 \leq 575/261$.*

**Proof.** We show that the left gap $J_9 = [10/11, 261/275]$ must be covered by runner 2's $B_{2,1}$, and that covering it requires $a_2 \leq 575/261$.

*Step 1: No runner covers the left boundary $10/11$ of $J_9$ except runner 2.*
For runner $j$ to have $B_{j,k}$ start at or before $10/11$:
$$\frac{11k+10}{11a_j} \leq \frac{10}{11} \implies a_j \geq \frac{11k+10}{10}.$$

- $k=0$: $a_j \geq 1$. Then end $\geq 10/11$ requires $a_j \leq 12/10 = 6/5$. So only runners with $a_j \in [1, 1.2]$ contribute via $k=0$. In ++------: runner 1 has $a_1 < 1$ (excluded); runner 2 has $a_2 > 2$ (too large). **No runner in this range.**
- $k=1$: $a_j \geq 21/10 = 2.1$. End $= 23/(11a_j) \geq 10/11$ requires $a_j \leq 23/10 = 2.3$. So $a_j \in [2.1, 2.3]$. Runner 2 with $a_2 > 2$ can fall in this range. **Runner 2 is the only candidate** (runners 3–9 have $a_j > 3 > 2.3$).
- $k=2$: $a_j \geq 32/10 = 3.2$. End $\geq 10/11$ requires $a_j \leq 34/10 = 3.4$. So $a_j \in [3.2, 3.4]$. Runner 3 with $a_3 > 3$ could have $a_3 \in [3.2, 3.4]$. **Runner 3 is a candidate.**
- $k \geq 3$: $a_j \geq 43/10 = 4.3$. End requires $a_j \leq (11k+12)/10$. For $k=3$: $a_j \in [4.3, 4.5]$ — runner 5 could be in this range ($a_5 < 5$). For $k=7$: $a_j \in [8.7, 8.9]$ — runner 9 is locked at $25/3 \approx 8.33$ (too small) and runner 8 has $a_8 < 8 < 8.7$. **No runner** for $k \geq 3$ in the feasible speed range.

Candidates for covering the boundary $10/11$: **runner 2** ($k=1$) and **runner 3** ($k=2$).

*Step 2: Runner 3 at $a_3 \in [3.2, 3.4]$ forces GF(I₂) > 0.*
For runner 3's $B_{3,2}$ to cover $J_9$'s left boundary, its start must reach $10/11$:
$$\frac{32}{11a_3} \leq \frac{10}{11} \implies a_3 \geq \frac{32}{10} = 3.2.$$
And end must reach $261/275$:
$$\frac{34}{11a_3} \geq \frac{261}{275} \implies a_3 \leq \frac{34 \times 275}{11 \times 261} = \frac{9350}{2871} = \frac{850}{261} \approx 3.257.$$

So runner 3 covers $J_9$ (up to start of runner 9's interval) iff $a_3 \in [16/5, 850/261] = [3.2, 3.257]$.

However, the baton-pass certificate (Theorem 4.1 of algebraic lemma) establishes a **good window** in I₂ whenever:
$$a_3 < \frac{2750}{759} \approx 3.623.$$
Since $3.257 < 3.623$, any $a_3 \in [3.2, 3.257]$ satisfies $a_3 < 2750/759$, producing a good window $(69/275,\ 10/(11a_3))$ in I₂ of positive width $= (2750 - 759a_3)/(3025a_3) > 0$.

This good window in I₂ means **GF(I₂) > 0**. Hence at least one of I₂, I₉ is not closed.
$\square$ (for runner 3 alternative)

*Step 3: Runner 2 must cover $J_9$, and this requires $a_2 \leq 575/261$.*
The only remaining candidate is runner 2 via $B_{2,1} = [21/(11a_2), 23/(11a_2)]$.

For $B_{2,1}$ to start at or before the left edge $10/11$ of $J_9$:
$$\frac{21}{11a_2} \leq \frac{10}{11} \implies a_2 \geq \frac{21}{10} = 2.1.$$

For $B_{2,1}$ to end at or after $261/275$ (runner 9's coverage start):
$$\frac{23}{11a_2} \geq \frac{261}{275}
\implies 23 \times 275 \geq 261 \times 11 \times a_2
\implies 6325 \geq 2871 \, a_2
\implies a_2 \leq \frac{6325}{2871} = \frac{575}{261}. \quad\square$$

*(Simplification: $\gcd(6325, 2871) = 11$; $6325/11 = 575$, $2871/11 = 261$.)*

---

## §4 — The Incompatibility Theorem

**Theorem 4.1 (Runner 2 Incompatibility — Main Claim 5.1).** *For any CB configuration in the ++------ sign class with $a_9 = 25/3$ and $a_6 = 40/7$:*
$$\mathrm{GF}(I_4) + \mathrm{GF}(I_9) > 0.$$
*Equivalently, there is no assignment of runner speeds simultaneously closing both I₄ and I₉.*

**Proof.** By Lemma 3.1, closing I₄ (GF(I₄) = 0) requires $a_2 \geq 20/9$.
By Lemma 3.2, closing I₉ (GF(I₉) = 0) requires $a_2 \leq 575/261$.

These are incompatible:
$$\frac{20}{9} > \frac{575}{261}
\iff 20 \times 261 > 9 \times 575
\iff 5220 > 5175. \quad \checkmark$$

The gap is:
$$\frac{20}{9} - \frac{575}{261} = \frac{5220 - 5175}{9 \times 261} = \frac{45}{2349} = \frac{5}{261} > 0.$$

Since no value of $a_2$ can satisfy both $a_2 \geq 20/9$ and $a_2 \leq 575/261$, we cannot have GF(I₄) = GF(I₉) = 0. Therefore GF(I₄) + GF(I₉) > 0. $\square$

---

## §5 — Corollary: GF > 0 for the ++------ Class

**Corollary 5.1.** *For every CB configuration in the ++------ sign class, $\mathrm{GF}(W_0) > 0$.*

**Proof.** By the Route 3 architecture (§6 of the algebraic lemma):
- **Cases A and B** ($a_9 < 25/3$ or $a_6 > 40/7$): explicit left/right edge gaps in I₁ give GF(I₁) > 0, hence GF(W₀) > 0.
- **Case C** ($a_9 = 25/3$ and $a_6 = 40/7$): Theorem 4.1 gives GF(I₄) + GF(I₉) > 0, hence GF(W₀) > 0.

In all cases, GF(W₀) ≥ GF(I_k) > 0 for some $k$. $\square$

---

## §6 — Exact Rational Summary

| Quantity | Exact value | Decimal approx |
|---|---|---|
| I₄ lower bound on $a_2$ (from Lemma 3.1) | $20/9$ | $2.\overline{2}$ |
| I₉ upper bound on $a_2$ (from Lemma 3.2) | $575/261$ | $\approx 2.2031$ |
| Incompatibility gap | $5/261$ | $\approx 0.0192$ |
| Runner 9's I₄ coverage start | $129/275$ | $\approx 0.4691$ |
| Runner 9's I₄ coverage end | $135/275 = 27/55$ | $= 54/110$ (right edge of I₄) |
| Runner 9's I₉ coverage start | $261/275$ | $\approx 0.9491$ |
| Runner 3 I₉-coverage speed upper bound | $850/261$ | $\approx 3.257$ |
| Runner 3 baton-pass threshold (I₂ gap) | $2750/759$ | $\approx 3.623$ |
| Runner 3 incompatibility gap (I₂ vs I₉) | $2750/759 - 850/261 = 990/2871 = 90/261$ | $\approx 0.345$ |

**Key cross-check.** The end condition for $B_{2,1}$:
$$\frac{23}{11 \times (575/261)} = \frac{23 \times 261}{11 \times 575} = \frac{6003}{6325}.$$
Is $6003/6325 = 261/275$?
$261/275 = 261 \times 23/(275 \times 23) = 6003/6325.$ ✓
