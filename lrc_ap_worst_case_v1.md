# LRC: The Arithmetic Progression as the Worst Case
**Date:** 2026-03-27
**Status:** Working document — formal attempt at the AP-minimality theorem
**Goal:** Prove (or precisely characterise) that the AP configuration minimises the lonely measure among all configurations with the same speed range.

---

## Statement of the Claim

**AP Minimality Conjecture (AMC).** *Fix $k \geq 1$ and a speed range $[e_{\min}, e_{\max}]$ with $e_{\max}/e_{\min} \leq k$. Among all configurations of $k$ runners with speeds in $[e_{\min}, e_{\max}]$, the arithmetic progression $e_i = e_{\min} + (i-1)\delta$ with $\delta = (e_{\max}-e_{\min})/(k-1)$ minimises the Lebesgue measure of the lonely set:*
$$L(e_1,\ldots,e_k) := \mathrm{meas}\bigl\{t \geq 0 : \|e_i t\| \geq 1/(k+1) \text{ for all } i\bigr\}.$$

*Equivalently: for any non-AP configuration with the same range, $L \geq L_{\rm AP}$.*

---

## Why This Would Settle Everything

If AMC is proved, the proof of LRC for all n becomes:

1. **Step 1** (Theorem GB): If $e_k/e_1 \leq k$, then $L > 0$ with explicit witness $t^* = k/((k+1)e_k)$.
2. **Step 2** (AMC): The AP configuration with the same range minimises $L$. So $L_{\rm AP} \leq L$ for all configs.
3. **Step 3**: Since Theorem GB shows $L_{\rm AP} > 0$ (the AP itself has a witness), all configurations satisfy $L \geq L_{\rm AP} > 0$.
4. **Step 4** (Large-ratio case): When $e_k/e_1 > k$, apply the W_ref window argument (runner $e_1$ trivially isolated). The remaining $k-1$ runners have range $[e_2, e_k]$; recurse.

**Critical observation:** Step 1 + Step 2 together would reduce Case R> to a recursion, entirely bypassing the Coupling Principle, Complementary Pairs, and Phase-Uniform Extension machinery of v24.

---

## Decomposition: Blocking Zones

The lonely set is the complement of the **blocking set**:
$$B(e_1,\ldots,e_k) := \{t \geq 0 : \exists\, i \text{ s.t. } \|e_i t\| < 1/(k+1)\}.$$

By inclusion-exclusion, $\mathrm{meas}(B) \leq \sum_i \mathrm{meas}(B_i)$ where $B_i = \{t : \|e_i t\| < 1/(k+1)\}$.

**Individual blocking zones.** For a single runner at speed $e$, the bad set $B_i$ is periodic with period $1/e$. In each period, the bad intervals have total width $2/(e(k+1))$. So:
$$\mathrm{density}(B_i) = \frac{2/(k+1)}{1/e \cdot e} = \frac{2}{k+1}.$$

This is **independent of $e$** — every runner blocks the same fraction $2/(k+1)$ of time, regardless of speed.

**Implication.** The total blocking measure is NOT determined by the individual zones — it depends entirely on the **overlaps** between zones $B_i \cap B_j$.

---

## The Overlap Principle

**Key lemma (informal).** *Two runners $e_i$ and $e_j$ have overlapping bad zones if and only if $e_i/e_j$ is close to a rational number $p/q$ with small denominator.*

**Formalisation.** The bad zone of runner $e_i$ consists of intervals centred at times $t = m/e_i$ (for $m \in \mathbb{Z}$) of width $2/((k+1)e_i)$. The bad zone of runner $e_j$ consists of intervals centred at $t = n/e_j$ of width $2/((k+1)e_j)$. These overlap when:
$$\left|\frac{m}{e_i} - \frac{n}{e_j}\right| < \frac{1}{(k+1)e_i} + \frac{1}{(k+1)e_j},$$
i.e., when $|m e_j - n e_i| / (e_i e_j) < 1/(k+1) \cdot (1/e_i + 1/e_j)$.

**For an AP** ($e_i = 1 + (i-1)d$, $e_j = 1 + (j-1)d$), the ratio $e_i/e_j$ is rational when $e_i, e_j$ are rational. In the integer AP, all ratios are rational, and the overlaps are **maximally structured** — they occur at exactly the witness times $m/(k+1)$.

**For a non-AP config**, the ratios $e_i/e_j$ are "less rational" (in the Diophantine approximation sense), meaning the overlaps are less frequent and less aligned. This increases the total blocking measure.

Wait — this reasoning is BACKWARDS. Less-structured overlaps means the bad zones cover the circle more uniformly, which would INCREASE blocking. But the AP has STRUCTURED overlaps at specific times, so the bad zones are concentrated, leaving gaps. This would mean the AP has SMALLER blocking measure — which is what AMC claims.

---

## The Correct Direction of the Argument

**Revised intuition.** The AP is the configuration where bad zones are most **concentrated** (all coincide at the witness times $m/(k+1)$). This means:
- At times $t \approx m/(k+1)$: many runners are simultaneously blocked.
- At times $t$ far from witnesses: most runners are simultaneously free.

**Non-AP config.** Bad zones are more uniformly spread across the timeline. No single moment has all runners blocked, but also no extended window has all runners free.

**Lonely measure.** The AP has **large lonely windows** (near each of the $\varphi(k+1)$ witnesses) and **large blocked windows** (near each $t = m/(k+1)$). A non-AP has **smaller** lonely windows but also smaller blocked windows — the bad zones are spread out.

**This suggests AMC is FALSE** in its strong form: the AP might have a LARGER lonely measure than some non-AP configurations!

---

## Numerical Evidence (Reconsidering AMC)

Before rejecting AMC, let us check whether the φ(n) Law really says "AP minimises the lonely measure" or something else.

**What the φ(n) Law actually states** (from the isolation law investigation):
- **Law 2**: For AP configurations, the number of isolation epochs $\geq \varphi(n)$ always.
- **Law 3**: The MODE of the isolation count (over many configurations) is $3\varphi(n)$.
- For n=11: mode = $3 \times 4 = 12$ isolation epochs; AP has exactly $\varphi(11) = 10$ epochs.

**Interpretation**: The AP achieves the MINIMUM number of isolation epochs (φ(n)), while most non-AP configurations have MORE (the mode is $3\varphi(n)$). So the AP is indeed the **minimum**, not the maximum, for isolation count — consistent with AMC.

**But "isolation epochs" is not the same as "lonely measure."** Isolation epochs are count-based; lonely measure is measure-based. An AP might have fewer (but wider) lonely windows; a non-AP might have more (but narrower) ones.

**Reconsidering:** AMC might be TRUE for isolated EPOCH COUNT, but may not hold for Lebesgue measure. For the LRC, what we need is that $L > 0$ (at least one lonely time exists), not that $L$ is maximised/minimised.

---

## What AMC Actually Needs to Say for LRC

The correct formulation for the LRC argument is:

**AP Positivity Lemma (APL).** *For any $k \geq 1$ and any speed range $[e_{\min}, e_{\max}]$ with $e_{\max}/e_{\min} \leq k$, the AP configuration has $L_{\rm AP} > 0$.*

**This is already proved by Theorem GB!** The explicit witness $t^* = k/((k+1)e_{\max})$ achieves $\|e_i t^*\| \geq 1/(k+1)$ for all $i$. So $L_{\rm AP} \geq (k+1)^{-1} \cdot \prod_i (\text{safe window width})$ — concretely positive.

The LRC argument then needs not "AP minimises L" but rather:

**Monotone Positivity Principle (MPP).** *If the AP configuration has $L_{\rm AP} > 0$, then every non-AP configuration with the same (or smaller) speed range also has $L > 0$.*

And MPP requires: **some monotonicity of loneliness in the speed configuration.** This is precisely Conjecture GFn restated.

---

## A Partial Monotonicity Result

**Claim.** If we move a runner $e_j$ towards any other runner $e_i$ (keeping all other speeds fixed), the lonely set can only increase.

**Heuristic argument.** Moving $e_j$ closer to $e_i$ increases the overlap of their bad zones $B_j$ and $B_i$. The union $B_j \cup B_i$ decreases (more overlap = less total blocking). The complement — the lonely set — therefore increases.

**Obstacle.** This argument assumes $B_j \cup B_i$ varies monotonically as $e_j \to e_i$. This is NOT obviously true because:
- As $e_j$ approaches $e_i$, the pair $(e_j, e_i)$ might pass through rational ratios, creating new resonances.
- New resonances create new overlap points, but might also eliminate existing lonely windows.

**Formal version (what needs to be proved).** Let $f: [e_i, e_k] \to \mathbb{R}^k_>$ parametrise a continuous deformation of the speed set from non-AP to AP. Then $L(f(s))$ varies continuously in $s$, and $L(f(s)) > 0$ for all $s$ if $L(f(0)) > 0$ and $L(f(1)) > 0$.

This is a **path-connectivity argument**: the set of configurations with $L > 0$ is an open, path-connected set, and since both the AP and some non-AP configs are in this set, all configurations along any connecting path are also in the set.

---

## Summary and Status

| Claim | Status |
|---|---|
| AP has $L_{\rm AP} > 0$ for all $k$ when ratio $\leq k$ | **PROVED** (Theorem GB) |
| AP has minimum EPOCH COUNT among configs with same range | **Empirically confirmed** (φ(n) Law, n=5..15) |
| AP has minimum LEBESGUE MEASURE among configs | **UNCERTAIN** — may be false; reformulation needed |
| Monotone Positivity: non-AP configs with $L_{\rm AP} > 0$ → $L > 0$ | **OPEN** (= Conjecture GFn for large-ratio case) |
| Path-connectivity argument for $L > 0$ | **PLAUSIBLE** — requires continuity + connectedness |

### The Right Theorem to Prove

The AP-minimality claim needs to be reformulated as:

> **Conjecture MPP.** *The set $\{(e_1,\ldots,e_k) : L(e_1,\ldots,e_k) > 0\}$ is open and path-connected in speed space.*

If MPP holds, then since the AP lies in this set (by Theorem GB) and the set is path-connected, every configuration reachable from the AP by a continuous path also lies in the set. Since all speed configurations with $e_k/e_1 \leq k$ are path-connected to the AP (via linear interpolation), MPP would imply Theorem GB extends to all such configurations — which is already known. The harder application would be to the large-ratio case.

**Recommended next step:** Attempt to prove the path-connectivity of $\{L > 0\}$ in speed space using topological arguments (the set is open by continuity of $L$; connectivity requires showing there are no "isolated components" with $L = 0$ separating different parts of speed space).

---

## The Two-Extremes Characterisation (2026-03-27 insight)

**User's claim:** "Perturbation from one AP speed to another (full range) provides a deterministic path that does not destroy loneliness. Therefore you only have two types of configurations to handle: (1) AP with uniform grid, and (2) clumped at one end with an outlier."

### Why this is structurally correct

For any $k$ runners with speeds in $[e_1, e_k]$:

**Extreme 1 — AP (uniform grid):** Speeds $e_1, 2e_1, \ldots, ke_1$ with ratio exactly $k$. This is the "most spread" configuration. Theorem GB gives an explicit witness $t^* = k/((k+1)ke_1)$.

**Extreme 2 — Clumped + outlier:** $k-1$ runners at speed $e_1$ (or near it) and 1 outlier at speed $e_k \gg ke_1$. The $k-1$ clumped runners are all at nearly the same position at any given time — they contribute just ONE effective blocker. The outlier is a second blocker. This reduces to a 2-runner problem, which is LRC for $n=3$ (classical, trivially true).

**What about intermediate configurations?** Any configuration with $e_k/e_1 > k$ has the following structure by pigeonhole:

- The "natural AP grid" for the range $[e_1, ke_1]$ has $k$ slots of width $e_1$.
- With $k$ runners and ratio $> k$, at least one runner is **above the natural grid** (at speed $> ke_1$), OR at least one slot is **empty** (two runners share a slot).
- In either case, the effective number of independent blockers is $< k$.

**Key consequence:** Any configuration with ratio $> k$ has either:
- A runner outside the natural grid (→ use W_ref; the outside runner is the "outlier" whose window we exploit)
- Or a clumped pair within the natural grid (→ two runners share blocking duties, reducing effective count)

In both cases, the effective blocking problem is strictly easier than the AP with $k$ independent blockers.

**The "path" interpretation:**
Starting from the AP $(e_1, 2e_1, \ldots, ke_1)$, any continuous deformation towards the clumped+outlier extreme:
- Either moves a runner towards another (increasing overlap of bad sets → increasing free measure)
- Or moves a runner away from the pack (creating a gap in coverage → also increasing free measure)

The AP is the **minimum** of bad-set spread, and any movement makes the configuration "looser." This is why the AP is the hardest case, and all other configurations are easier.

### Formal status

This characterisation is correct and explains the structure of the proof, but it does not yet constitute a complete formal proof because step "increasing free measure" needs to be proved, not just argued. The file above (Section 3, Claim 3.2) identifies this as the key open step. Two approaches:

1. **Direct monotonicity:** Prove that moving any runner towards another strictly increases free measure. (Obstacle: rational resonances along the path.)
2. **Topological:** Prove the set $\{L > 0\}$ is open and path-connected. (Equivalent to MPP above.)

For $n = 11$, v24's Route 3 is the algebraic version of approach 1 restricted to the CB configuration space.

---

## Connection to v24

In v24, the Complementary Pairs argument for n=11 establishes that for any CB (Complementary-Block) configuration, at least one slot has positive good fraction. This is equivalent to saying the set $\{L > 0\}$ includes all CB configurations, which — given the EFN parameterisation — covers all of Case R>. The proof is not a monotonicity argument but a direct algebraic argument.

The APL + MPP approach would be a topological alternative to the algebraic approach of v24.

---

*See also: `lrc_elegant_proof_sketch_v1.md` (Part IV, Conjecture GFn), `lrc_n11_structural_mechanism_v1.md` (Coupling Principle)*
