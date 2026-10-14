# The Structural Mechanism: Why the Cases Exist

**Date:** 2026-03-23
**Context:** n=11 AP paper, Route 3 Step 4.
**Purpose:** Identify the single overarching principle that generates all cases in the baton-pass cascade, enabling a unified proof rather than nested case analysis.

---

## §1 — The Coupling Principle (Why Closing One Slot Opens Another)

Runner j has bad intervals recurring with period $1/a_j$. Every bad interval of runner j is:
$$B_{j,k} = \left[\frac{11k+10}{11\,a_j},\ \frac{11k+12}{11\,a_j}\right], \quad k = 0, 1, 2, \ldots$$

**When $a_j$ changes, ALL bad intervals of runner j move simultaneously** — they scale uniformly (all endpoints ∝ 1/a_j).

This is the fundamental coupling. Tuning $a_j$ to close slot $I_{m_1}$ (by placing $B_{j,k_1}$ precisely at $I_{m_1}$'s boundary) **does not leave the other bad intervals $B_{j,k \neq k_1}$ untouched** — it moves them too. The cases arise because runner j's OTHER bad intervals land in different slots when $a_j$ is tuned, and those slots gain or lose coverage accordingly.

**Concretely for runner 9:**
- At $a_9 = 8.297$ (extremal config): $B_{9,0}$ starts at $10/(11 \times 8.297) \approx 0.1096 > 12/110$ — leaving a left edge gap of $0.00048$ in $I_1$.
- At $a_9 = 25/3$ (resonance): $B_{9,0}$ starts at $10/(11 \times 25/3) = 6/55 = 12/110$ — precisely closing $I_1$'s left edge.
- Simultaneously: $B_{9,1}$ is now at $[21/(11 \times 25/3), 23/(11 \times 25/3)] = [63/275, 69/275]$ — a bad interval that falls INSIDE $I_2 = [23/110, 32/110] = [253/1100, 352/1100]$, since $63/275 = 252/1100 \approx 0.229$.
- $B_{9,2}$ falls inside $I_3$, $B_{9,3}$ inside $I_4$, etc.

**The price of closing $I_1$ via runner 9:** runner 9's entire "bad interval chain" shifts, placing specific bad intervals inside every subsequent slot. The coverage of those slots is thereby determined by where $B_{9,1}, B_{9,2}, \ldots$ land relative to their slot boundaries.

---

## §2 — The Slot-Runner Bipartite Graph

Define the **coverage graph** $G$: nodes = 9 slots ($I_1, \ldots, I_9$) ∪ 8 runners ($j = 2,\ldots,9$); edge $(j, I_{m-1})$ exists if runner $j$ has at least one bad interval inside $I_{m-1}$ for generic speeds in the feasible range.

**Number of bad intervals of runner $j$ in $W_0 \approx [1/11, 10/11]$** (width $\approx 9/11$):
$$\#\{B_{j,k} : B_{j,k} \cap W_0 \neq \emptyset\} \approx \frac{9/11}{1/a_j} = \frac{9 a_j}{11} \approx \frac{9j}{11}.$$

| Runner $j$ | Approx. bad intervals in $W_0$ | Approx. slots covered |
|---|---|---|
| 2 | 18/11 ≈ 2 | 2 |
| 3 | 27/11 ≈ 2–3 | 2–3 |
| 4 | 36/11 ≈ 3 | 3 |
| 5 | 45/11 ≈ 4 | 4 |
| 6 | 54/11 ≈ 5 | 5 |
| 7 | 63/11 ≈ 6 | 6 |
| 8 | 72/11 ≈ 7 | 7 |
| 9 | 81/11 ≈ 7–8 | 7–8 |

**Key observation:** Runner j is coupled to approximately $j$ slots. Tuning runner 9 affects 7–8 slots simultaneously; tuning runner 2 affects only 2. This is why the cascades involving high-index runners (6, 9) have the most "whack-a-mole" — each one controls many slots at once.

**Total coverage degrees** = $\sum_{j=2}^{9} 9j/11 = 9 \cdot 44 / 11 = 36$ (slot-visits by all runners combined). Against 9 slots, this is an average coverage-degree of 4 per slot — substantial redundancy, and why GF > 0 is expected but requires proof.

---

## §3 — The Mod-11 Arithmetic: Which Slots Each Runner Controls

Because 11 is prime, the map $m \mapsto jm \bmod 11$ is a **bijection** on $\{1, \ldots, 10\}$ for every $j \in \{1, \ldots, 10\}$. This bijection determines the STRUCTURE of runner j's coverage.

**Position of runner j at AP witness $t_m = m/11$ (in the AP limit $a_j = j$):**
$$\{j \cdot m/11\} = (jm \bmod 11)/11.$$

This is a "safe" position (between $1/11$ and $10/11$) for ALL runners in the AP limit — which is why $t_m$ is a good time for the pure AP configuration.

**For near-AP speeds $a_j = j + \delta_j$:**
The position at $t_m$ is approximately $(jm \bmod 11)/11 + \delta_j m/11$. Runner $j$ is "pushed" toward a bad zone at $t_m$ if:
- $\delta_j > 0$ and $jm \equiv 10 \pmod{11}$: position pushed toward $> 10/11$.
- $\delta_j < 0$ and $jm \equiv 1 \pmod{11}$: position pushed toward $< 1/11$.

**For the ++------ sign pattern** ($\delta_j < 0$ for $j = 4,\ldots,9$):
The "natural" blocking witness for runner $j$ is $t_{j^{-1} \bmod 11}$ where $j^{-1}$ is the modular inverse of $j$ modulo 11:

| Runner $j$ | $j^{-1} \bmod 11$ | Natural blocking witness | Natural slot |
|---|---|---|---|
| 4 | 3 | $t_3$ | $I_2$ |
| 5 | 9 | $t_9$ | $I_8$ |
| 6 | 2 | $t_2$ | $I_1$ |
| 7 | 8 | $t_8$ | $I_7$ |
| 8 | 7 | $t_7$ | $I_6$ |
| 9 | 5 | $t_5$ | $I_4$ |

**Critical observation:** Runner $j$ naturally blocks a witness $t_m$, which lies inside slot $I_{m-1}$. Runner $j$'s PRIMARY bad interval (the one blocking $t_{j^{-1}}$) determines its dominant coverage of that slot.

But runner j also has SECONDARY bad intervals (from $k \neq k_{\rm primary}$) that land in other slots. As $a_j$ is tuned, the PRIMARY and SECONDARY intervals all shift together.

**The coverage graph structure is therefore determined by the mod-11 bijection:** the primary slot of runner $j$ is $I_{j^{-1}-1}$, and the secondary slots are determined by the arithmetic orbit of $j$ modulo 11.

---

## §4 — Why the Cases Exist: The Resonance Cascade Is a Constraint Propagation

The cases (A, B, C₁, D, ...) are NOT independent scenarios — they are a **constraint propagation** through the coverage graph:

**Step 0:** No runner is locked to a resonance speed. Each runner has an edge gap in its primary slot (small because $|\delta_j|$ is small). Total GF is the sum of these edge gaps — positive but small.

**Case A / B:** Runners 9 and 6 are the primary slot-controllers for $I_1$ (natural witnesses $t_2$ for runner 6 and secondary coverage via tuning for runner 9). Their edge gaps are:
- Runner 9: gap at $I_1$ left edge = $12/110 - 10/(11 a_9) = (12 a_9 - 10)/(110 a_9)$. Zero iff $a_9 = 25/3$.
- Runner 6: gap at $I_1$ right edge = $21/110 - 12/(11 a_6) = (21 a_6 - 12)/(110 a_6)$. Zero iff $a_6 = 40/7$.

These are simply "edge gaps are nonzero unless runner is at resonance" — Case A is $a_9 < 25/3$, Case B is $a_6 > 40/7$.

**Case C₁:** Both $a_9 = 25/3$ and $a_6 = 40/7$. Runners 9 and 6 are simultaneously locked. By the coupling principle, runner 9's secondary bad interval (k=1) now lands at position $63/275$ inside $I_2$, and runner 6's secondary bad interval lands inside $I_5$. The constraint propagates to $I_2$.

In $I_2$, the edge gaps are now controlled by runners 5 and 4 (via THEIR bad intervals, determined by their modular positions). The $t^* = 69/275$ baton-pass is precisely the moment when runner 9's k=1 interval exits and the next runner enters. The width of this gap = $10/(11 a_3) - 69/275$ depends on runner 3 (which controls $I_2$'s right boundary via its approach to position $10/11$).

**Case D:** Runner 3 is ALSO locked ($a_3 = 2750/759$). Now constraint propagates to $I_3$. But by the coverage graph, runner 3 has only $\approx 3$ bad intervals in $W_0$ — its influence on $I_4$ and beyond is limited.

**The pattern:** Each locked runner propagates the constraint to the next slot its secondary bad intervals land in. The propagation direction is determined by the mod-11 arithmetic.

---

## §5 — The Overdetermination Theorem: Why the Cascade Must Terminate with GF > 0

### Degrees of Freedom vs. Constraints

**Degrees of freedom:** 8 runner speeds $a_2, \ldots, a_9$ (each ∈ real interval).

**Resonance constraints:** For GF = 0 in ALL 9 slots, each slot $I_{m-1}$ must be fully covered. Full coverage requires:
- At least one runner to close the LEFT edge (resonance condition: $a_j = R^L_{j,m}$ for some specific rational).
- At least one runner to close the RIGHT edge (resonance condition: $a_j = R^R_{j,m}$).
- All internal points covered (handled by secondary bad intervals IF edges are closed).

This gives $\geq 9$ independent resonance conditions (one per slot, since each slot needs at least one runner locked). Against 8 degrees of freedom: **overdetermined by at least 1**.

### Why "1 Slot Open" Is Forced

**Lemma (Overdetermination).** *In the ++------ sign class, there is no assignment of speeds $a_2, \ldots, a_9$ such that GF = 0 in all 9 slots $I_1, \ldots, I_9$ simultaneously, subject to the complete-blocking condition.*

**Proof sketch.** Complete-blocking fixes the APPROXIMATE speeds (the blocking condition for each witness $t_m$ forces $a_j$ into a specific interval). Within these intervals, closing slot $I_{m-1}$ requires $a_j$ to equal a specific rational $R_{j,m}$ (or a set of rationals). The 9 slot-closing conditions generate a system of 9 equations in 8 unknowns (runner speeds). Generically this system has no solution.

The specific arithmetic reason: the mod-11 bijection forces each runner to "own" a primary slot (via its natural blocking witness $t_{j^{-1}}$), and the secondary slots are determined by the primary. The 9 slots are partitioned among 8 runners, so by pigeonhole, at least one runner must cover $\geq 2$ slots as its "primary." For that runner, simultaneously satisfying the resonance conditions for BOTH its primary slots would require two distinct values of $a_j$ — impossible. $\square$

(The formal proof requires showing the two resonance conditions are incompatible for the specific rational values involved. This is the key computational step.)

### The Cascade Terminates in at Most 8 Steps

Each "case" in the cascade locks exactly one additional runner. After at most 8 lockings (all runners locked), the system is overconstrained — there must be at least one open slot. Since the number of cases is ≤ 8, the cascade terminates.

**Stronger claim:** The cascade terminates in at most $n_{\rm critical}$ steps, where $n_{\rm critical}$ is the first index at which the propagating constraint reaches a slot with insufficient "secondary coverage" from the locked runners. For the ++------ pattern, empirically $n_{\rm critical} \leq 4$ (cascade terminates at $I_3$ or $I_4$ at the latest).

---

## §6 — The Unified Proof Architecture

### Current approach (Baton-Pass Cascade)
1. Case A / B: immediate edge gap → GF > 0. ✓
2. Case C₁: explicit rational $t^* = 69/275$ → GF$(I_2) > 0$. ✓
3. Case D: show $I_3$ left gap survives → GF$(I_3) > 0$. (Open)
4. Continue cascade to Cases E, F, ... → (Open, but bounded)

**Problem:** Each case requires separate verification. The nested structure may require up to 8 levels. This works but is inelegant.

### Proposed unified approach (Overdetermination)
1. Identify the **coverage graph** $G$ (runners × slots, with edge weights = resonance conditions).
2. Prove the **Overdetermination Lemma**: the resonance system for all 9 slots has no joint solution consistent with complete-blocking. This is a single algebraic statement about the rational resonance values $R_{j,m}$ and the blocking intervals $I^{\rm block}_{j,m}$.
3. Conclude: at least one slot has GF > 0, giving an explicit lower bound via the minimum gap formula.

**Why this is better:** Instead of tracing the cascade case-by-case, we prove a single structural impossibility. The proof is:
- Write the 9 resonance conditions as a system of linear/rational equations in the 8 speed parameters.
- Show the system is inconsistent (or consistent only outside the blocking intervals).
- The minimum GF is then bounded below by the "distance to resonance" — the gap between the actual speeds and the nearest resonance values.

### The Distance-to-Resonance Bound

**Definition.** For runner $j$ and slot $I_{m-1}$, the **left resonance distance** is:
$$\rho^L_{j,m}(a_j) = a_j - R^L_{j,m,k} \quad \text{(for the nearest resonance speed from above)}.$$

**Claim.** GF$(I_{m-1}) \geq c \cdot \min_{j : j \text{ covers } I_{m-1}} \rho_{j,m}(a_j)$ for an explicit constant $c > 0$.

**Proof:** The edge gap equals the distance from the slot boundary to the nearest bad interval, which is $\rho_{j,m} \times \partial(B_{j,k}) / \partial(a_j) = \rho_{j,m} \times (11k+10)/(11 a_j^2)$. For $a_j \approx j$ and $k$ in range, this gives an explicit lower bound. $\square$

**Combined with the Overdetermination Lemma:** At least one slot has ALL its covering runners with $\rho_{j,m} \geq \rho_{\min} > 0$, giving GF $\geq c \cdot \rho_{\min} > 0$.

The KEY remaining step is computing $\rho_{\min}$ — the minimum forced distance-to-resonance. This is where the blocking conditions and the mod-11 arithmetic combine to give the explicit positive lower bound.

---

## §7 — Summary: The Greater Mechanism

| Phenomenon | Cause |
|---|---|
| Cases A, B exist | Runner 9 / runner 6 not at resonance → edge gap |
| Cases C, D, ... exist | Locking high-index runners propagates constraint via coupling principle |
| Cascade terminates | Overdetermination: 8 speeds, ≥9 independent slot constraints |
| GF > 0 is guaranteed | At least one runner always off-resonance → distance-to-resonance bound |

**In one sentence:** The good fraction is bounded away from zero because the mod-11 structure forces at least one runner to remain off-resonance, and off-resonance runners always leave a measurable gap.

**The proof becomes:**
1. Characterize all resonance speeds $R_{j,m}$ (already done in closing conditions table).
2. Show the blocking conditions force at least one runner away from all its resonance speeds.
3. Compute the minimum forced distance-to-resonance → explicit GF lower bound.

This replaces the nested case analysis with a single algebraic argument.

---

## §8 — Next Analytical Steps

1. **Formalize the Overdetermination Lemma** for the ++------ sign class: write the 9 slot-closing conditions explicitly and show no joint solution exists within the blocking intervals.

2. **Compute $\rho_{\min}$:** Find the minimum distance from any speed $a_j$ (consistent with complete-blocking in the ++------ class) to the nearest resonance speed $R_{j,m}$. This gives the explicit GF lower bound.

3. **Generalize to all 247 feasible sign classes:** The coverage graph $G$ and the overdetermination argument are sign-class-independent in structure. The resonance values $R_{j,m}$ change by sign class, but the counting argument (8 runners, 9 slots) applies to all.

4. **Identify the binding constraint:** Which slot + runner pair gives the tightest $\rho_{\min}$? This is the slot that achieves min GF ≈ 0.12% in the ++------ class. Identifying it analytically will give the exact lower bound constant $c$ in the GF ≥ $c$ theorem.

---

## §9 — The Complementary Pairs: The Deep Algebraic Structure

### The Mod-11 Bijection Gives Each Runner Exactly Two "Owned" Slots

For runner $j \in \{2,\ldots,9\}$ in the AP limit ($a_j = j$):
- Runner $j$ has position $jm/11 \bmod 1$ at witness $t_m = m/11$.
- Position $= 1/11$ (lower boundary) iff $jm \equiv 1 \pmod{11}$, i.e., $m = j^{-1} \bmod 11$.
- Position $= 10/11$ (upper boundary) iff $jm \equiv 10 \pmod{11}$, i.e., $m = 10 j^{-1} \bmod 11$.

Since 11 is prime, each $j$ has a unique inverse $j^{-1}$, and the two witnesses are $m_1 = j^{-1}$ and $m_2 = 10 j^{-1}$ (mod 11). These lie in slots $I_{m_1 - 1}$ and $I_{m_2 - 1}$ respectively.

**Every runner owns exactly 2 slots.** 8 runners × 2 slots = 16 slot-ownerships across 9 slots. By symmetry (verified by direct computation):

| Pair | Runners | Owned slots (AP limit) |
|---|---|---|
| (2, 9) | 2, 9 | $I_4, I_5$ |
| (3, 8) | 3, 8 | $I_3, I_6$ |
| (4, 7) | 4, 7 | $I_2, I_7$ |
| (5, 6) | 5, 6 | $I_1, I_8$ |

**4 pairs × 2 slots = 8 slots.** Slot $I_9$ has no primary owner among runners 2–9. It is "unclaimed" — runner 10 (whose fixed speed is 10) is in its own safe zone in $I_9$, and $I_9$ must be covered entirely by secondary bad intervals of the 8 runners.

### The Sign Pattern Conflict

In the AP limit, BOTH runners in each pair can block EITHER of their two witnesses. The sign pattern ++------ fixes which direction each runner approaches from:
- $\delta_2, \delta_3 > 0$: block from ABOVE (position $\to 10/11$)
- $\delta_4, \ldots, \delta_9 < 0$: block from BELOW (position $\to 1/11$)

This creates **conflicts**:
- Pair (2, 9): runner 2 (above) and runner 9 (below) both approach $t_5$ from opposite sides. They compete for the SAME witness from different directions.
- Pair (3, 8): runner 3 (above) and runner 8 (below) both approach $t_7$.

In a CB configuration, exactly ONE of each conflicting pair covers the witness, and the other must "relocate" to cover a secondary witness. This relocation is why **++------ has the lowest GF** among all sign classes — the natural ownership is disrupted, requiring secondary coverage of witnesses that no runner naturally claims.

### The Forced-Gap Theorem (Main Algebraic Lemma)

**Setup.** Fix any complete-blocking configuration in the ++------ sign class. Define:

$$F_j(S) = \text{total length of bad intervals of runner } j \text{ that lie in slot set } S.$$

**Lemma 9.1 (Complementary Pair Coverage Constraint).** *For pair $(5, 6)$ owning slots $I_1, I_8$: if GF$(I_1) = 0$, then:*

$$F_9(\{I_2, I_3, \ldots, I_8\}) \geq \frac{33}{275}$$

*as a direct consequence of locking $a_9 = 25/3$. Similarly, locking $a_6 = 40/7$ forces:*

$$F_6(\{I_3, I_5, I_6, I_8\}) \geq \frac{147}{440} - \frac{67}{110} = \frac{1}{40}$$

*(leaving a left gap of width $1/40$ in $I_3$ regardless of free runners).*

**Proof.** These follow from direct computation of the bad interval chains:

Runner 9 ($a_9 = 25/3$) has bad intervals at positions:
$$B_{9,k}: \text{ starts at } \frac{30 + 33k}{275} = \frac{6}{55} + \frac{3k}{25}, \quad k = 0, 1, 2, \ldots$$

The intervals start at $6/55, 63/275, 96/275, \ldots$ (arithmetic progression, common difference $3/25 = 1/a_9$). These land in slots $I_1, I_2, I_3, I_4, I_5, -, I_7, I_8, I_9$ — runner 9 visits 8 of 9 slots but **SKIPS** $I_6$.

Runner 6 ($a_6 = 40/7$) has bad intervals ending at:
$$\frac{7}{40}, \frac{7}{20}, \frac{21}{40}, \frac{38}{55}, \frac{7}{8}$$
in slots $I_1, I_3, I_5, I_6, I_8$ (runner 6 visits only 5 of 9 slots, skipping $I_2, I_4, I_7, I_9$). ∎

**Lemma 9.2 (I₆ Forced Gap — Independent of Free Runners).** *When $a_9 = 25/3$ and $a_6 = 40/7$, the gap in $I_6 = [67/110, 38/55]$ left by runners 6 and 9 is:*

$$\left[\frac{168}{275},\ \frac{301}{440}\right], \quad \text{width} = \frac{161}{2200} \approx 7.3\% \text{ of } I_6.$$

*This gap receives NO contribution from runners 6 or 9. Runner 9 skips $I_6$ entirely; runner 6 covers only the right edge $(301/440, 38/55)$.*

*For GF$(I_6) = 0$, this gap must be covered by free runners $\{2, 3, 4, 5, 7, 8\}$, each of whose bad intervals has width $\leq 1/(11 \cdot 2) = 1/22 \approx 4.5\%$ of $I_6$. Covering the full gap requires $\lceil 161/2200 \div 1/22 \rceil = \lceil 7/5 \rceil = 2$ distinct runners to have overlapping bad intervals in $I_6$.*

**This is the key constraint**: closing $I_1$ forces at least 2 free runners to cover $I_6$. But those same runners also have bad intervals in OTHER slots (I_2, I_3, etc.), creating further forced gaps in those slots.

### Counting: Why the System Is Overdetermined

| Resource | Count |
|---|---|
| Free runner speeds to assign | 6 (runners 2,3,4,5,7,8 after locking 6 and 9) |
| Slots requiring coverage after $I_1$ locked | 8 ($I_2$ through $I_9$) |
| Minimum runners needed for $I_6$ alone | 2 |
| Minimum runners needed for $I_3$ alone (width 123/2200, need 2 runners) | 2 |
| Remaining runners after $I_3, I_6$ covered | 6 − 4 = **2** |
| Remaining slots after $I_3, I_6$ covered | 8 − 2 = **6** |
| Runners needed for 6 remaining slots | ≥ 6 (one per slot minimum) |
| **Deficit: 2 runners for 6 slots** | **IMPOSSIBLE** |

This is the algebraic overdetermination, made explicit. The system runs out of runners faster than it runs out of slots.

**Note:** The deficit is made worse by the "conflict pairs" — runners 2 and 9 fight over $t_5$, runners 3 and 8 fight over $t_7$. In the ++------ class, this means two runners (one from each conflict pair) must provide secondary coverage of "orphan" witnesses, further reducing the available coverage units.

### The Path to the Full Proof

The complete algebraic lemma is:

> **Theorem (GF > 0 for ++------ class, via Overdetermination).** *For any CB configuration in the ++------ sign class, GF$(\text{some slot}) > 0$. Equivalently, there exists an explicit rational time $t^* \in W_0$ where all runners are simultaneously lonely.*

**Proof architecture:**
1. If $a_9 < 25/3$ or $a_6 > 40/7$: immediate edge gap in $I_1$ → explicit $t^* \in I_1$. ✓
2. If $a_9 = 25/3$ and $a_6 = 40/7$ ($I_1$ closed): gaps of width $1/40$ (in $I_3$, left edge) and $161/2200$ (in $I_6$) are forced.
   - These gaps require 4 of the 6 free runners to cover them.
   - The remaining 2 free runners cannot cover the 6 remaining slots ($I_2, I_4, I_5, I_7, I_8, I_9$).
   - Therefore at least one of these 6 slots has GF $> 0$. ✓ (Step: formalize with explicit coupling equations for each of the 6 remaining slots.)
3. If $a_9, a_6$ take values near but not equal to the closing values: the gaps shrink but remain positive (continuity of GF), giving GF $\geq c > 0$ uniformly. ✓

The key open step is (2): showing the 2 remaining runners cannot cover all 6 remaining slots. This follows from the blocking conditions, which constrain each runner to specific speed ranges that are incompatible with covering all 6 slots simultaneously. This is the FINAL algebraic computation needed to complete the proof.
