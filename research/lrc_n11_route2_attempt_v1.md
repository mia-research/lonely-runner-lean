# Route 2 — Explicit Overlap Bound: Analytic Attempt

**Date:** 2026-03-22
**Status:** PARTIAL — density argument yields |Good| ≥ 0, not |Good| > 0; fundamental obstruction identified.

---

## Setup

**EFN frame:** speeds $a_i = i + \delta_i$ ($i=1,\ldots,9$), $a_{10} = 10$.
**Window:** $W_0 = \bigl[\tfrac{1}{11a_1},\, \tfrac{10}{11a_1}\bigr]$, $|W_0| = \tfrac{9}{11a_1}$.
Runner 1 is lonely throughout $W_0$ by definition.

**Bad set of runner $i$ in $W_0$:**
$$B_i = \{t \in W_0 : \{a_i t\} \notin [1/11,\, 10/11]\} \quad (i = 2,\ldots,10).$$
**Good set:** $G = W_0 \setminus \bigcup_{i=2}^{10} B_i$.

**Objective:** Show $|G| > 0$ for every complete-blocking configuration.

---

## Step 1 — Density of Each Bad Set

**Claim:** For each $i \in \{2,\ldots,10\}$, the bad density satisfies
$$\frac{|B_i|}{|W_0|} = \frac{2}{11}.$$

**Justification (exact):** Runner $i$ has speed $a_i = i + \delta_i$. Its bad set in $[0,\infty)$ is periodic with period $1/a_i$; within each period, bad measure is $2/(11a_i)$, giving density exactly $2/11$ on any interval whose length is an integer multiple of $1/a_i$.

For non-integer multiples, the deviation from $2/11$ is at most $2/(11 a_i \cdot |W_0|) = 2a_1/(9 a_i)$. For $a_i \geq 2$ and $a_1 < 1$, this is $< 1/9$.

**Exact density** holds when $a_i |W_0| = 9 a_i/(11 a_1)$ is an integer multiple of 1 (i.e., $9 a_i/(11 a_1) \in \mathbb{Z}$). For generic (irrational ratio) configurations, Weyl's theorem gives exact density $2/11$ in the limit.

We proceed with $|B_i| = (2/11)|W_0|$ as exact; the endpoint correction does not affect the qualitative argument.

---

## Step 2 — The Density Bound

$$\sum_{i=2}^{10} |B_i| = 9 \times \frac{2}{11} |W_0| = \frac{18}{11} |W_0|.$$

**Key observation:** $18/11 > 1$. The bad sets cannot all be disjoint — their total measure exceeds $|W_0|$.

**Minimum required pairwise overlap:**

$$\sum_{2 \leq i < j \leq 10} |B_i \cap B_j \cap W_0| \geq \frac{1}{2}\left(\sum_i |B_i| - |W_0|\right) = \frac{1}{2}\cdot\frac{7}{11}|W_0| = \frac{7}{22}|W_0|.$$

*(This follows because if $f(t) = \sum_{i=2}^{10}\mathbf{1}_{t \in B_i}$, then $\int_{W_0} f = (18/11)|W_0|$, and $\int_{W_0} f \leq |W_0| + \sum_{i<j}|B_i \cap B_j|$ when counted with multiplicity.)*

---

## Step 3 — What the Density Argument Gives

By inclusion-exclusion:
$$\left|\bigcup_{i=2}^{10} B_i\right| \leq \sum_i |B_i| = \frac{18}{11}|W_0|.$$

But this upper bound exceeds $|W_0|$, so it gives no useful bound on $|G|$.

**Lower bound via overlaps:**
$$\left|\bigcup_{i=2}^{10} B_i\right| = \sum_i |B_i| - \sum_{i<j}|B_i \cap B_j| + \ldots \leq \sum_i |B_i| - \sum_{i<j}|B_i \cap B_j|.$$

For $|G| > 0$, we need $\left|\bigcup B_i\right| < |W_0|$, i.e.,
$$\sum_{i<j} |B_i \cap B_j| > \sum_i |B_i| - |W_0| = \frac{7}{11}|W_0|.$$

So we need: **total pairwise overlap $> (7/11)|W_0|$.**

---

## Step 4 — Where Route 2 Breaks Down

**The density argument alone cannot establish $|G| > 0$.**

The reason: Even though the total pairwise overlap must be $\geq (7/22)|W_0|$ (from Step 2), this is NOT sufficient to conclude the union $\bigcup B_i$ has measure $< |W_0|$. The inclusion-exclusion bound requires all higher-order terms, not just pairwise.

**Concrete obstruction (construction):**

Consider 9 intervals each of length $2/11$, packed so that each overlaps the next by $1/11$:
- $B_i = [(i-2)/11,\, i/11]$ for $i = 2,\ldots,10$, within $W_0 = [0, 10/11]$.

Then $\sum|B_i| = 18/11$, pairwise overlaps sum to $8 \times 1/11 = 8/11 > 7/11$ ✓, but $|\bigcup B_i| = |[0, 10/11]| = 10/11 = |W_0|$, so $|G| = 0$.

**Conclusion:** The pairwise overlap condition $(> 7/11)|W_0|$ is *necessary* but not *sufficient* for $|G| > 0$. To deduce $|G| > 0$ analytically, we need to show the union is STRICTLY less than $|W_0|$ — which requires either:

(a) A point in $W_0$ not covered by any $B_i$ (constructive), or
(b) A higher-order inclusion-exclusion bound showing the union has gaps.

---

## Step 5 — Why the AP Witness Blocking Condition Does Not Close the Gap

The complete-blocking assumption says: for each AP witness $t_m = m/11 \in W_0$, at least one runner $j_m \in \{1,\ldots,9\}$ is bad at $t_m$. This means:
$$t_m \in B_{j_m} \quad \text{for each } m \text{ with } t_m \in W_0.$$

This is a **finite set of constraints** (at most 10 points). The bad sets $B_i$ are constrained to *pass through* these points, but have freedom elsewhere in $W_0$.

**Example showing AP constraints alone are insufficient:**

Take $a_1 = 0.5$ ($\delta_1 = -0.5$), so $W_0 = [2/11, 20/11]$. AP witnesses in $W_0$: $t_2, \ldots, t_{10}$. Suppose each $t_m$ is blocked by a distinct runner $j_m$. The bad interval of runner $j_m$ near $t_m$ has width $\approx 2/(11 j_m)$. These 9 intervals (one per witness) have total width $\sum_{j=2}^{10} 2/(11j) \approx 0.53$. The remaining portion of $W_0$ (total length $9/(11 \times 0.5) \approx 1.64$) is NOT constrained by the AP blocking condition alone.

So between the AP witnesses, the bad sets could cover $W_0$ completely without violating the blocking conditions at the witnesses themselves — at least in principle.

---

## Step 6 — Why LRC Still Holds (Empirical)

Despite the failure of Route 2, computational evidence over $> 450{,}000$ complete-blocking configurations shows the minimum good fraction in $W_0$ is $\approx 2\%$, never reaching 0.

**The actual mechanism appears to be:** The EFN speeds $a_i \approx i$ enforce specific relationships between the bad intervals of different runners. Specifically:

1. **Speed near-commensurability:** $a_i/a_j \approx i/j$ forces the bad intervals of runners $i$ and $j$ to nearly align whenever $im \equiv 0 \pmod{11}$ (which never happens for $i \in \{1,\ldots,10\}$, $m \in \{1,\ldots,10\}$, by the no-missing-slot property).

2. **The binding runner (infimum argument):** For any complete-blocking config, the infimum of $\max_i|\delta_i|$ is $1/10$, not achieved. Near-infimum configs ($\max|\delta_i| \approx 1/10$) concentrate all the "action" near one AP witness. Away from that witness, the bad intervals are weakly perturbed from their AP positions, and the Weyl-type equidistribution argument applies approximately.

3. **No fully-commensurable extremal:** The minimum good fraction appears bounded below by a constant $c > 0$, suggesting a structural reason (likely modular) that prevents the bad sets from achieving full coverage.

---

## Summary

| Step | Result |
|---|---|
| Density argument | Proves total pairwise overlap $\geq (7/22)|W_0|$, but NOT $|G| > 0$ |
| AP witness blocking | 10 finite constraints; insufficient to control $B_i$ coverage globally |
| Route 2 verdict | **FAILS to close the gap analytically** |
| Obstruction | Existence of configurations where bad sets can pack to cover $W_0$ without violating AP blocking (not seen computationally, but not ruled out analytically) |

**Next step:** Computational minimisation of good fraction to find tightest near-failure configuration and understand the mechanism preventing $|G| = 0$.

---

## Appendix: Explicit Pairwise Overlap at AP Witnesses

At AP witness $t_m = m/11$, runner $i$ has fractional position $\{r_i(m)/11 + m\delta_i/11\}$ where $r_i(m) = im \bmod 11$.

For runners $i$ and $j$ both bad near $t_m$, their bad intervals in $t$-space must overlap. The overlap width is approximately:
$$\text{overlap}(i,j,m) = \max\left(0,\; \frac{1}{11 a_i} + \frac{1}{11 a_j} - \left|t_{i,m}^{\rm bad} - t_{j,m}^{\rm bad}\right|\right)$$
where $t_{i,m}^{\rm bad}$ is the centre of runner $i$'s nearest bad interval to $t_m$.

Summing over AP witnesses in $W_0$ and over pairs $(i,j)$ does not yield a clean lower bound without controlling $|t_{i,m}^{\rm bad} - t_{j,m}^{\rm bad}|$, which depends on the specific $\delta$ values.
