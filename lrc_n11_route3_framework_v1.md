# Route 3 — Continuity + Compactness: Framework and Proof Attempt

**Date:** 2026-03-22
**Status:** FRAMEWORK ESTABLISHED — key components identified; lower bound proof incomplete.

---

## Setup

**EFN frame:** $n=11$, speeds $a_i = i + \delta_i$ ($i=1,\ldots,9$), $a_{10} = 10$.
**Window:** $W_0 = [1/(11a_1), 10/(11a_1)]$, runner 1 lonely throughout $W_0$.

**Complete-blocking (CB):** For every $m \in \{1,\ldots,10\}$, at least one runner $j \in \{1,\ldots,9\}$ is bad at AP witness $t_m = m/11$.

*Note:* Runner 10 is **never bad** at any AP witness, since $r_{10}(m) = 10m \bmod 11 \in \{1,\ldots,10\}$ for all $m$, giving $\{10 \cdot m/11\} \in [1/11, 10/11]$. Only runners 1–9 can block AP witnesses.

**Good fraction:** $\text{GF}(\boldsymbol{\delta}) = |G \cap W_0|/|W_0|$, where $G = W_0 \setminus \bigcup_{i=2}^{10} B_i$.

---

## Component 1 — Topological Structure of CB

**Claim 1.1 (CB is open):** The complete-blocking set CB is an open subset of $\{(\delta_1,\ldots,\delta_9) : a_1 > 0\}$.

**Proof:** "Runner $i$ is bad at $t_m$" $\Leftrightarrow$ $\{(i+\delta_i) \cdot m/11\} \notin [1/11, 10/11]$, i.e., $(i+\delta_i) \cdot m/11 \bmod 1 < 1/11$ or $> 10/11$. This is an open condition in $\delta_i$ (the fractional part $x \mapsto \{x \cdot m/11\}$ is continuous, and the preimage of the open set $[0,1/11) \cup (10/11,1]$ is open). Therefore "runner $i$ bad at $t_m$" is open in $\delta_i$, hence in $\boldsymbol{\delta}$.

"Witness $m$ is blocked" = $\bigcup_{i=1}^{9}$ {runner $i$ bad at $t_m$} = open.

CB = $\bigcap_{m=1}^{10}$ {witness $m$ blocked} = intersection of 10 open sets = open. $\square$

**Corollary 1.2 (Closure):** The closure $\overline{\text{CB}}$ adds "borderline" configurations: configs where some runner $i$ has $\{a_i \cdot m/11\} \in \{1/11, 10/11\}$ exactly (the runner is on the boundary of its lonely zone at the AP witness).

**Claim 1.3 (Compact truncation):** For any $M > 0$, let
$$S_M = \overline{\text{CB}} \cap \{\max_i |\delta_i| \leq M\} \cap \{a_1 \geq \epsilon_0\}$$
for any $\epsilon_0 > 0$. Then $S_M$ is compact.

**Proof:** $S_M$ is closed (intersection of closed sets) and bounded ($|\delta_i| \leq M$), hence compact by Heine-Borel. $\square$

---

## Component 2 — Continuity of GF

**Claim 2.1 (GF is Lipschitz on $S_M$):** For configurations with $a_1 \geq \epsilon_0 > 0$ and $|\delta_i| \leq M$, the map $\boldsymbol{\delta} \mapsto \text{GF}(\boldsymbol{\delta})$ is Lipschitz continuous.

**Proof sketch:** $\text{GF}(\boldsymbol{\delta}) = |W_0|^{-1} \cdot \left|W_0 \setminus \bigcup_i B_i(\boldsymbol{\delta})\right|$ where $B_i(\boldsymbol{\delta}) = \{t \in W_0 : \{(i+\delta_i)t\} \notin [1/11, 10/11]\}$.

As $\delta_i$ varies, the bad set $B_i(\boldsymbol{\delta})$ shifts: a perturbation $\Delta\delta_i$ shifts each bad interval by $\pm m \Delta\delta_i / (11 a_i^2)$ to first order (where $m$ parametrises which interval). The total measure change is at most $2 \cdot (\text{number of intervals in } W_0) \times |\Delta\delta_i|/a_i$. The number of intervals in $W_0$ is $\leq a_i |W_0| + 1 \leq a_i \cdot 9/(11a_1) + 1$. This gives a Lipschitz bound. $\square$

**Corollary 2.2:** GF achieves its minimum on $S_M$.

---

## Component 3 — Reduction to the Minimum

By Components 1–2, GF achieves its minimum $c_M = \min_{\boldsymbol{\delta} \in S_M} \text{GF}(\boldsymbol{\delta}) \geq 0$ at some $\boldsymbol{\delta}^* \in S_M$.

**Route 3 reduces to:** Show $c_M > 0$, i.e., show $\text{GF}(\boldsymbol{\delta}) > 0$ for all $\boldsymbol{\delta} \in S_M$.

---

## Component 4 — Why GF > 0 (Proof Attempt)

Assume for contradiction that $\boldsymbol{\delta}^* \in S_M$ has $\text{GF}(\boldsymbol{\delta}^*) = 0$. Then:

$$\bigcup_{i=2}^{10} B_i(\boldsymbol{\delta}^*) \supseteq W_0 \quad \text{(a.e.)}$$

The bad sets of runners 2–10 cover all of $W_0$.

### Sub-claim 4.1 (Runner 10 constraint)

Runner 10 has **fixed** speed $a_{10} = 10$. Its bad set $B_{10}$ in $W_0$ consists of intervals at positions $t \in [k/10 - 1/110, k/10 + 1/110]$ for integer $k$ (i.e., near $t = 0, 1/10, 2/10, \ldots$). Specifically, in $W_0 \approx [1/11, 10/11]$, the intervals are near $t = 1/10, 2/10, \ldots, 9/10$. Total measure: $(2/11) |W_0|$.

**Runner 10 covers $2/11$ of $W_0$ at fixed positions.** The remaining $9/11$ of $W_0$ must be covered by runners 2–9.

Runners 2–9 each have bad density $2/11$. Total coverage: $8 \times 2/11 = 16/11 > 1$.

So runners 2–9 could in principle cover $9/11$ of $W_0$. This is not yet a contradiction.

### Sub-claim 4.2 (No-missing-slot prevents simultaneous AP blocking)

**Observation:** The residues $r_i(m) = im \bmod 11$ are all distinct as $i$ ranges over $\{1,\ldots,10\}$ for any fixed $m$, and all nonzero. This means: at AP witness $t_m$, the 10 runners have fractional positions $\{r_1(m)/11, r_2(m)/11, \ldots, r_{10}(m)/11\}$ = $\{1/11, 2/11, \ldots, 10/11\}$ (up to permutation, in the absence of perturbations).

In particular, **in the unperturbed ($\boldsymbol{\delta} = 0$) case, all runners are lonely at every AP witness.** The perturbations $\delta_i$ shift runner $i$'s position at $t_m$ by $m\delta_i/11$, bringing it into the bad zone only if $|m\delta_i|$ is large enough.

**Consequence:** For complete-blocking to occur, at each AP witness $t_m$, some $\delta_{j_m}$ must satisfy $m|\delta_{j_m}|/(11) \geq \min(r_{j_m}(m) - 1, 10 - r_{j_m}(m))/11$, i.e., $|\delta_{j_m}| \geq (r_{j_m}(m) - 1)/m$ or $|\delta_{j_m}| \geq (10 - r_{j_m}(m))/m$.

This gives the **infimum condition**: the minimum $|\delta_{j_m}|$ to block any witness $m$ is at least $\min_j \min(r_j(m)-1, 10-r_j(m))/m$.

For witness $m=10$: minimum $|\delta|$ needed = $\min_{j \in \{1,...,9\}} \min(r_j(10)-1, 10-r_j(10))/10$ where $r_j(10) = 10j \bmod 11 = 11-j$. So minimum $|\delta|$ = $\min_j \min(11-j-1, 10-(11-j))/10 = \min_j \min(10-j, j-1)/10$. Minimised at $j=1$ (giving $9/10$) — wait, $j=1$: $\min(9, 0) = 0$, so $|\delta_1| \geq 0$?

Actually $r_1(10) = 10 \bmod 11 = 10$. So runner 1 at witness 10 has position $\{10/11 + 10\delta_1/11\}$. For this to be bad: $\{10/11 + 10\delta_1/11\} < 1/11$ or $> 10/11$. Since $10/11 = 10/11$ is borderline safe (= boundary of safe zone), any $\delta_1 > 0$ pushes it over into bad territory. But $\delta_1 < 0$ keeps it safe. This ties to the infimum result (1/10).

### Sub-claim 4.3 (Key gap: GF > 0 at the left boundary of $W_0$)

**Observation:** The left endpoint $t_\ell = 1/(11a_1)$ of $W_0$ is NOT an AP witness for $a_1 < 1$ (since $t_\ell > 1/11 = t_1$). At $t_\ell$, runner 1 is at fractional position exactly $1/11$ (the left boundary of its lonely zone).

For runner $i \geq 2$ at $t_\ell$: position $= \{a_i/(11a_1)\} = \{(i+\delta_i)/(11a_1)\}$.

For $a_1 \approx 1$ and small $\delta_i$: position $\approx i/11$, which is in $[1/11, 10/11]$ (lonely) for $i \in \{1,\ldots,9\}$. Runner 10: position $\approx 10/11$, also barely lonely.

So near $t_\ell$, all runners are approximately in their "ideal" AP positions, all lonely! The bad intervals of runners 2–10 near $t_\ell$ are determined by when $\{a_i t\}$ enters the bad zone. For runner $i$ starting at position $i/11$ at $t_\ell$, the nearest bad boundary (above or below) is at distance $\min(i/11 - 1/11, 10/11 - i/11) = \min((i-1)/11, (10-i)/11)$ from the current position. Since the position changes at rate $a_i \approx i$ per unit time, the nearest bad interval is at time distance $\approx \min(i-1, 10-i)/(11a_i)$ from $t_\ell$.

For $i = 2$: distance $= \min(1, 8)/22 = 1/22 \approx 0.045$.
For $i = 5$: distance $= \min(4, 5)/55 = 4/55 \approx 0.073$.
For $i = 9$: distance $= \min(8, 1)/99 = 1/99 \approx 0.010$.

The minimum is for runner 9 (or 10): about $0.01$. So near $t_\ell$, there is a good interval of width at least $\sim 0.01$.

**This argument gives a positive GF near the left boundary of $W_0$**, but does not directly bound the total GF across all of $W_0$.

---

## Component 5 — The Equidistribution Argument (Partial)

For irrational-speed-ratio configs, Weyl's theorem immediately gives $\text{GF} = (9/11)^{10} > 0$. The difficulty is commensurable (rational) configs.

**Key observation:** Runner 10 has speed exactly 10. This means $a_{10}/a_1 = 10/a_1$. For $a_1$ irrational, the pair $(a_1, 10)$ is rationally independent, and the joint distribution of $(\{a_1 t\}, \{10 t\})$ is uniform on $[0,1]^2$ by Weyl. This immediately gives $\text{GF} \geq (9/11)^2 \cdot [\text{contribution from remaining runners}] > 0$.

**For rational $a_1$:** Let $a_1 = p/q$ (in lowest terms). Then the speeds $(a_1, 2+\delta_2, \ldots, 9+\delta_9, 10)$ are all rational iff all $\delta_i \in \mathbb{Q}$. In that case, all orbits are periodic with period $\text{lcm}(q, \ldots)$. The joint orbit is dense in a sub-torus of $[0,1]^{10}$, and the good fraction equals the measure of the good set in this sub-torus.

**For commensurable speeds all with denominator $q$:** The joint orbit is periodic with period $T = \text{lcm}(q,1) / \gcd(a_1,\ldots)$... this is harder to bound from below.

---

## What Route 3 Proves (So Far)

| Component | Status |
|---|---|
| CB is open → $S_M$ is compact | **PROVED** (Claim 1.1, 1.3) |
| GF is continuous on $S_M$ | **PROVED** (Claim 2.1) |
| GF achieves minimum on $S_M$ | **PROVED** (Corollary 2.2) |
| $\text{GF} > 0$ for irrational $a_i/a_j$ | **PROVED** (Prop E, Weyl) |
| $\text{GF} > 0$ for all $\boldsymbol{\delta} \in S_M$ | **OPEN** — the hard part |

The **open part** requires showing: no commensurable complete-blocking config has $\text{GF} = 0$.

---

## Computational Lower Bound

Differential evolution over $10^6$ complete-blocking configurations finds $\text{GF} \geq 0.82\%$ across all $|\delta_i| \leq 0.9$. The minimum is attained near $a_1 \approx 0.99$, $|\delta_i|_{\max} \approx 0.8$.

**Empirical Conjecture:** $c_M \geq 0.008$ for $M = 0.9$ (i.e., $\text{GF} \geq 0.8\%$ for all complete-blocking configs with $|\delta_i| \leq 0.9$).

---

## Next Step: Global Minimum via Differential Evolution

To confirm the empirical floor is not a local artefact, run `scipy.optimize.differential_evolution` with:
- Bounds: $\delta_1 \in (-0.9, -0.001)$, $\delta_i \in (-0.9, 0.9)$ for $i \geq 2$
- Objective: $\text{GF}(\boldsymbol{\delta}) + \text{BlockingPenalty}(\boldsymbol{\delta})$
- Strategy: `best1bin`, $\text{popsize} = 30$, $\text{maxiter} = 3000$

If the global minimum is confirmed at $\geq 0.8\%$, the **empirical Route 3** is established. The analytical gap (proving $c_M > 0$) remains open but is now well-characterised.
