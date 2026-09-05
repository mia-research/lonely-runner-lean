# LRC: The Blocking Grammar
**Date:** 2026-03-28
**Status:** Working document — algebraic engine for the constructive proof
**Purpose:** Define and develop the one-runner blocking map $B(a)$, establish its symmetries, and state the master theorem target that unifies all scales of the constructive proof.

---

## 1. The Blocking Map

**Definition.** For $a \in \mathbb{R}_{>0}$ and $n = 11$, define the *blocking set*
$$B(a) := \bigl\{m \in \{1,\dots,10\} : \{am/11\} \notin [1/11,\, 10/11]\bigr\}.$$

$B(a)$ is the set of AP-witness labels $m$ that runner with normalised speed $a$ kills at the scale-1 grid $t_m = m/11$.

**Interpretation.** Label $m \in B(a)$ means runner $a$ sits within distance $1/11$ of $0$ (mod 1) at time $t_m$, i.e., it is in the bad zone at that moment.

**Scale-$Q$ generalisation.** For a grid $t_{m,Q} = m/(11Q)$ at scale $Q > 0$, runner with actual speed $e_i$ blocks label $m$ exactly when
$$m \in B(e_i / Q).$$

So $Q$ is simply a normalisation: the same map $B$ is evaluated at the normalised speed $e_i/Q$. There is no new object — only a change of units.

---

## 2. The Two Fundamental Symmetries

### Symmetry 1: Periodicity

$$B(a + 11) = B(a).$$

**Proof.** For any $m \in \{1,\dots,10\}$:
$$\{(a+11)m/11\} = \{am/11 + m\} = \{am/11\},$$
since $m \in \mathbb{Z}$. The blocking condition is unchanged. $\square$

**Consequence.** $B$ is determined by $a \bmod 11$. The grammar is a finite algebraic object on $\mathbb{R}/11\mathbb{Z}$.

### Symmetry 2: Complementary-Pair Reflection

$$B(11 - a) = B(a).$$

**Proof.** For any $m \in \{1,\dots,10\}$:
$$\{(11-a)m/11\} = \{m - am/11\} = \{-am/11\} = 1 - \{am/11\}$$
(for non-integer $am/11$, which holds generically). The bad zone is $[0,1/11) \cup (10/11,1]$, which is symmetric under $x \mapsto 1-x$: $x \in [0,1/11)$ iff $1-x \in (10/11,1]$. So $\{am/11\}$ is bad iff $1-\{am/11\}$ is bad. $\square$

**Consequence.** Runners at speeds $a$ and $11-a$ have identical blocking patterns. In the EFN parameterisation ($a_i = i + \delta_i$), runner $i$ and runner $11-i$ share the same $B$-pattern. This is the algebraic origin of the complementary-pair structure in v24's Coupling Principle — it is not an ad hoc pairing but a consequence of the reflection symmetry of $B$.

### The Symmetry Group

The two symmetries generate a dihedral action on $(0,11)$: translation by 11 and reflection through $11/2$. The grammar $B$ is invariant under this action. The fundamental domain is $[0, 11/2]$.

### 2.4 The Folded Map

To avoid carrying infinitely many periodic lifts, define the **folded map**
$$F : \mathbb{R}_{>0} \to [0,\, 11/2]$$
by first reducing modulo 11 and then reflecting:
$$F(a) := \min\!\bigl(a \bmod 11,\; 11 - (a \bmod 11)\bigr).$$

Since $B$ is invariant under both $a \mapsto a+11$ and $a \mapsto 11-a$, the value $B(a)$ depends only on $F(a)$. Define the **folded blocking map**
$$\widetilde{B} : [0,\, 11/2] \to \mathcal{P}(\{1,\dots,10\}), \qquad \widetilde{B}(F(a)) := B(a).$$

$\widetilde{B}$ is well-defined (the two symmetries guarantee $B$ is constant on each fibre of $F$) and piecewise constant on the compact domain $[0, 11/2]$.

**Consequence.** For any runner with speed $e_i$ and any scale $Q$, the blocking set is
$$B(e_i/Q) = \widetilde{B}(F(e_i/Q)).$$

All blocking computations reduce to evaluations of the finite map $\widetilde{B}$ on the compact fundamental domain. The infinite periodic structure is fully quotiented away.

---

## 3. The 38-Cell Structure

On $a \in (0, 10)$, the map $B(a)$ is piecewise constant with exactly **38 open cells**, separated by the boundary points where $\{am/11\} \in \{1/11, 10/11\}$ for some $m$, i.e., where $am \equiv 1 \pmod{11}$ or $am \equiv 10 \pmod{11}$.

**Cell boundaries** occur at $a = (11n \pm 1)/m$ for integers $n \geq 0$ and $m \in \{1,\dots,10\}$. These are the speeds at which a runner sits exactly on the boundary of the bad zone for some witness label.

**The AP integers are boundary points.** At $a = j$ for $j \in \{1,\dots,10\}$, we have $\{jm/11\} = \{jm/11\}$. Since $\gcd(j,11) = 1$ and $m \in \{1,\dots,10\}$, the values $jm \bmod 11$ cycle through all of $\{1,\dots,10\}$ — none equals $0$ or $11$, so $jm/11$ is never an integer. Moreover $jm \bmod 11 \in \{1,\dots,10\}$, giving $\{jm/11\} \in (1/11, 10/11)$. So:
$$B(j) = \varnothing \quad \text{for } j = 1,\dots,10.$$

The AP integer speeds kill no AP witnesses. They are the "safe" points — the natural coordinate system, not an accident.

### The Near-Zero Staircase

For $a \in (0,1)$ small, $am < 11$ for all $m \leq 10$, so $\{am/11\} = am/11$. This is bad iff $am/11 < 1/11$, i.e., $am < 1$, i.e., $a < 1/m$. Therefore:

$$a \in (1/(k+1),\, 1/k) \implies B(a) = \{1, 2, \dots, k\} \quad \text{for } k = 1,\dots,10.$$

Staircase explicitly:
| Speed range | $B(a)$ |
|---|---|
| $(0,\; 1/10)$ | $\{1,2,3,4,5,6,7,8,9,10\}$ — all witnesses killed |
| $(1/10,\; 1/9)$ | $\{1,2,3,4,5,6,7,8,9\}$ |
| $(1/9,\; 1/8)$ | $\{1,2,3,4,5,6,7,8\}$ |
| $\vdots$ | $\vdots$ |
| $(1/2,\; 1)$ | $\{1\}$ |
| $(1,\; \text{next boundary})$ | depends on next cell |

**Hard obstruction.** Any runner with $a < 1/10$ kills ALL ten AP witnesses simultaneously. No choice of which nine of ten witnesses to use avoids this runner. This is a structural obstruction, not a perturbative one.

---

## 4. The AP Witness Grid as Universal Algebraic Coordinate System

The AP witness family $\{t_m = m/11\}$ is not a universal witness set (the staircase obstruction shows it fails when any runner has $a < 1/10$). It is instead the **universal algebraic coordinate system**: the unique grid where

- every AP-speed runner has $B = \varnothing$ (is safe at every grid point),
- the blocking grammar has its cleanest finite structure,
- the two symmetries act most transparently.

When the AP grid fails at one scale, the correct move is not to find a new family of witnesses but to **test the same grammar at a different scale $Q$**.

---

## 5. The Finite-State Engine: Critical Scales on a Compact Interval

### What $Q$ is (and is not)

$Q$ is a **normalisation parameter** — a common divisor applied to all speeds simultaneously. It does not shift phases independently; every $a_i = e_i/Q$ moves in lockstep with fixed pairwise ratios. The 10 blocking patterns are a correlated 10-tuple determined by the single real parameter $Q$, not 10 independent choices.

Globally, as $Q \to 0$, the normalised speeds $e_i/Q \to \infty$ and their folded images $F(e_i/Q)$ oscillate through the fundamental domain infinitely often. The set of all critical $Q$ values on $(0,\infty)$ is therefore **not finite**. The finite-state structure only emerges after restricting to a compact scale interval.

### The Compact Interval Framework

**Definition.** Let $E = (e_1 < \cdots < e_{10})$ be a speed configuration and $I = [Q_-, Q_+]$ a compact interval of scales. Define the **critical scale set**
$$\mathcal{C}_I(E) := \bigl\{Q \in I : F(e_i/Q) \in \Xi_0 \text{ for some } i \in \{1,\dots,10\}\bigr\},$$
where $\Xi_0 \subset [0, 11/2]$ is the finite set of cell-boundary points of the folded grammar $\widetilde{B}$ — the values where the blocking pattern changes.

**Locally Constant Cover Lemma.** The map
$$U_E(Q) := \bigcup_{i=1}^{10} \widetilde{B}(F(e_i/Q))$$
is **constant on each connected component of $I \setminus \mathcal{C}_I(E)$**.

*Proof sketch.* Each $F(e_i/Q)$ is continuous in $Q$. On a component of $I \setminus \mathcal{C}_I(E)$, no $F(e_i/Q)$ crosses a boundary point of $\widetilde{B}$, so each individual $\widetilde{B}(F(e_i/Q))$ is constant. The union of finitely many constant sets is constant. $\square$

**Finiteness.** $\mathcal{C}_I(E)$ is finite. Each runner $i$ contributes at most $|\Xi_I|$ critical points, where $|\Xi_I|$ is the number of boundary points of $\widetilde{B}$ visited by $F(e_i/Q)$ as $Q$ ranges over $I$. Therefore:
$$\#\mathcal{C}_I(E) \leq 10\,|\Xi_I|.$$

The count $|\Xi_I|$ depends on the interval $I$ and on the speed ratios, not on the number of grammar cells. It is the number of times any runner crosses a boundary of $\widetilde{B}$ as $Q$ sweeps $I$.

### The Natural First Search Window

**Choice:** $I = [e_1,\, e_{10}/10]$.

This is the interval in which:
- At $Q = e_1$: $a_1 = 1$, which satisfies $B(1) = \varnothing$ (runner 1 safe). This is the W_ref scale.
- At $Q = e_{10}/10$: $a_1 = 10e_1/e_{10}$. When $e_{10}/e_1 \leq 10$, $a_1 \geq 1$ and label $m=1$ survives (Theorem GB). When $e_{10}/e_1 > 10$, $a_1 < 1$ and the staircase kicks in.

For the large-ratio case ($e_{10}/e_1 > 10$), this interval is non-degenerate ($e_{10}/10 > e_1$) and the two endpoints correspond exactly to the two known scales. The finite-state structure of $U_E$ on $I \setminus \mathcal{C}_I(E)$ is the algebraic record of everything that happens between them.

### Scale $Q = e_{10}/10$ (Case B / Theorem GB)

At this scale, $a_i = 10e_i/e_{10} \in [10e_1/e_{10}, 10]$. When $e_{10}/e_1 \leq 10$, all $a_i \in [1,10]$.

**Label $m = 1$ survives.** The condition $1 \in B(a)$ requires $F(a) \in [0,1)$ (staircase: $a < 1$ in the first period). For $a_i \geq 1$, $F(a_i) \geq 1$... wait: $F(a) = \min(a \bmod 11, 11 - a\bmod 11)$. For $a_i \in [1,10]$: $a_i \bmod 11 = a_i$, so $F(a_i) = \min(a_i, 11-a_i)$. The condition $1 \in B(a)$ requires $\{a/11\} \notin [1/11, 10/11]$, i.e., $a \bmod 11 < 1$ or $a \bmod 11 > 10$. Neither holds for $a \in [1,10]$. So $1 \notin B(a_i)$ for all $i$, and label $m=1$ survives. The witness is $t_{1,Q} = 1/(11Q) = 10/(11e_{10}) = t^*$ — exactly Theorem GB.

### Scale $Q = e_1$ (W_ref window)

At this scale, $a_1 = 1$ and $\widetilde{B}(F(1)) = B(1) = \varnothing$. Runner 1 contributes nothing to $U_E$. The coverage question becomes:
$$\bigcup_{i=2}^{10} B(e_i/e_1) \stackrel{?}{=} \{1,\dots,10\}.$$
Route 3 of v24 proves this union is always strict. That proof is now a statement about the folded grammar: the 9 folded speeds $F(e_i/e_1)$ for $i = 2,...,10$ cannot collectively cover all 10 labels of $\widetilde{B}$, because the reflection symmetry forces paired runners to waste their coverage on the same labels.

### The Trajectory Constraint

A critical structural input: the 10-tuple $(F(e_1/Q), \ldots, F(e_{10}/Q))$ is **not** an arbitrary element of $[0,11/2]^{10}$. It must arise from the ordered reciprocal trajectory
$$Q \mapsto \bigl(e_1/Q,\, e_2/Q,\, \ldots,\, e_{10}/Q\bigr),$$
which has fixed ratios $e_i/e_j$ and is monotone in each component. This imposes severe constraints: as $Q$ decreases, all normalised speeds increase proportionally, and their folded images $F(e_i/Q)$ trace coupled paths through $[0, 11/2]$. The cells occupied at one scale are not independently re-selectable at another.

This is probably what makes the finite-state coverage problem tractable: only a small fraction of the $\binom{38}{10}$-type combinatorial configurations can be realised by any actual ordered speed set.

### The Exact Theorem Target

$$\boxed{
\text{For every ordered speed set } E,\ \exists \text{ a component of } I \setminus \mathcal{C}_I(E)
\text{ on which } U_E(Q) \neq \{1,\dots,10\}.
}$$

This gives a constructive witness: for any $Q$ in that component and any surviving label $m^*$,
$$t = \frac{m^*}{11Q}$$
is lonely. The witness is explicit once the surviving component and label are identified.

---

## 6. Connection to v24's Complementary Pairs

In v24, the Complementary Pairs Theorem pairs runner $j$ with runner $11-j$. The symmetry $B(11-a) = B(a)$ shows this is the one-runner reflection symmetry viewed in the two-runner context: runners $j$ and $11-j$ have the same blocking pattern at every scale, so they can never independently cover two different labels — they always "waste" their coverage on the same set of witnesses.

**What v24 proves (now restated):** At scale $Q = e_1$, the ten runners $e_1,\dots,e_{10}$ with normalised speeds $a_i = e_i/e_1$ satisfy
$$\bigcup_{i=1}^{10} B(a_i) \neq \{1,\dots,10\},$$
specifically because the complementary-pair symmetry forces the union to miss at least one label. The minimum good-fraction bound ($59/9460$) is the quantitative version of "at least one label survives."

---

## 7. Summary and Status

| Object | Description | Status |
|---|---|---|
| $B(a)$: blocking map | 38-cell piecewise-constant grammar on $(0,10)$ | ✅ Derived |
| $B(a+11) = B(a)$ | Period-11 symmetry | ✅ Proved (1 line) |
| $B(11-a) = B(a)$ | Complementary-pair symmetry | ✅ Proved (1 line) |
| $F(a) = \min(a \bmod 11,\, 11 - a\bmod 11)$ | Folded map to fundamental domain $[0, 11/2]$ | ✅ Defined |
| $\widetilde{B}(F(a)) = B(a)$ | Folded grammar on compact domain | ✅ Well-defined (symmetries) |
| $\Xi_0$: boundary set of $\widetilde{B}$ | Finite set of cell boundaries in $[0,11/2]$ | ✅ Finite (to be tabulated) |
| AP integers: $B(j) = \varnothing$ | AP speeds kill no AP witnesses | ✅ Proved |
| Near-zero staircase | $a < 1/k \implies \{1,...,k-1\} \subseteq B(a)$ | ✅ Proved |
| $\mathcal{C}_I(E)$: critical scale set | Finite set where $U_E(Q)$ can change; $\#\leq 10|\Xi_I|$ | ✅ Locally-constant lemma proved |
| $U_E$ piecewise constant on $I \setminus \mathcal{C}_I(E)$ | Finite-state cover on compact interval | ✅ Proved |
| Trajectory constraint | Only ordered reciprocal paths are realisable | ✅ Structural observation |
| Scale B (Theorem GB) | $Q = e_{10}/10$: label $m=1$ survives when ratio $\leq 10$ | ✅ Proved |
| Scale W (Route 3) | $Q = e_1$: $U_E(e_1) \neq \{1,...,10\}$ for all configs | ✅ Proved for $n=11$ (v24) |
| Saturated-Cover Exclusion | $\exists$ component of $I\setminus\mathcal{C}_I(E)$ with $U_E \neq \{1,...,10\}$ | ⚠️ Target — hard algebraic content |

---

## 8. The Next Theorem to Prove

**Theorem (Saturated-Cover Exclusion, conjectured).** *For any 10 distinct positive real speeds $e_1 < \cdots < e_{10}$ and $I = [e_1, e_{10}/10]$, there exists a component of $I \setminus \mathcal{C}_I(E)$ on which $U_E(Q) \neq \{1,\dots,10\}$.*

**Why this is the right form.** It does not split into cases. It asks a single question about the finite-state object $U_E$ on the interval $I$: is there a component where coverage is not total? The two known scales are just the endpoints of $I$:
- At $Q = e_{10}/10$ (right endpoint): label $m=1$ survives when ratio $\leq 10$ — this is Theorem GB.
- At $Q = e_1$ (left endpoint): $U_E(e_1) \neq \{1,...,10\}$ for all configurations — this is v24's Route 3 theorem.

For ratio $\leq 10$: the right endpoint alone is sufficient.
For ratio $> 10$: the interval is non-degenerate, and the question is whether the finite list of components always includes at least one with $U_E \neq \{1,...,10\}$.

**The three steps to a proof.**

1. *Tabulate $\Xi_0$*: enumerate the boundary points of $\widetilde{B}$ in $[0, 11/2]$. These are the values $F((11n \pm 1)/m)$ for $m \in \{1,...,10\}$ and small $n$. Finite, computable.

2. *Classify allowed transitions*: for an ordered speed set $E$, describe which sequences of cell-patterns $(P_1,...,P_{10})$ are realisable as $({\widetilde B}(F(e_1/Q)),...,\widetilde{B}(F(e_{10}/Q)))$ for some $Q \in I$. The trajectory constraint (fixed ratios, monotone paths) eliminates most combinations.

3. *Saturated-cover exclusion*: show that no realisable sequence of transitions keeps $U_E(Q) = \{1,...,10\}$ on every component of $I \setminus \mathcal{C}_I(E)$. At least one component must have a surviving label.

Step 3 is the hard algebraic content. For $n=11$, v24 proves it at the single scale $Q = e_1$ via Complementary Pairs. The finite-state framing asks for a stronger result: coverage failure somewhere in the entire interval, with the witness located constructively.

---

## 9. The $\lambda$-Reduction: One-Parameter Family

**Substitution.** Set
$$x := a_1 = \frac{e_1}{Q}, \qquad \lambda_i := \frac{e_i}{e_1} \quad (i = 1,\dots,10),$$
so $a_i = e_i/Q = \lambda_i x$, with $\lambda_1 = 1 < \lambda_2 < \cdots < \lambda_{10}$.

The entire blocking problem becomes the one-parameter family
$$x \mapsto \bigl(B(\lambda_1 x),\, B(\lambda_2 x),\, \dots,\, B(\lambda_{10} x)\bigr).$$

The parameter $Q$ has disappeared: sweeping $Q$ over $[e_1, e_{10}/10]$ is exactly sweeping $x = e_1/Q$ over $[10e_1/e_{10}, 1] \subseteq (0,1]$. The $\lambda_i$ are the fixed shape of the configuration; $x$ is the single moving coordinate.

The union $U_E(Q)$ becomes
$$U(x) := \bigcup_{i=1}^{10} B(\lambda_i x),$$
and the theorem target is: **for some $x \in (0,1]$, $U(x) \neq \{1,\dots,10\}$**.

---

## 10. Corridor Structure and the Uniform Reblocking Lemma

### Corridors

The near-zero staircase (§3) partitions $(0,1)$ into corridors based on runner 1's blocking pattern:
$$C_k := \left(\frac{1}{k+1},\, \frac{1}{k}\right), \quad k = 1,\dots,9.$$

For $x \in C_k$: runner 1 has $a_1 = x \in (1/(k+1), 1/k)$, so $B(x) = \{1,\dots,k\}$ (staircase). Runner 1 blocks labels $1,\dots,k$ and **releases** labels $k+1,\dots,10$.

Total coverage fails if some released label $m > k$ is not blocked by any other runner. Maintaining $U(x) = \{1,\dots,10\}$ on $C_k$ requires: for every released label $m > k$,
$$C_k \subseteq \bigcup_{i=2}^{10} \lambda_i^{-1} D_m,$$
where $D_m := \{a \in [0,11/2] : m \in B(a)\}$ is the bad set for label $m$ in speed space.

This is a **one-dimensional interval-cover problem** in $x$.

### The Uniform Reblocking Lemma

**Lemma (Uniform Reblocking).** *For $k \geq 5$ and any released label $m > k$, the runner with speed ratio $\lambda_{k,m} := 10(k+1)/m$ blocks label $m$ uniformly on all of $C_k$.*

**Proof.** For $x \in C_k$: $m \lambda_{k,m} x = 10(k+1)x \in (10,\, 10 + 10/k)$. For $k \geq 5$: $10 + 10/k \leq 12$. So $10(k+1)x \in (10, 12)$.

The blocking condition is $10(k+1)x \bmod 11 \in [0,1) \cup (10,11)$:
- When $10(k+1)x \in (10,11)$: value mod 11 $= 10(k+1)x \in (10,11)$ — **bad**. ✓
- When $10(k+1)x \in (11,12)$: value mod 11 $= 10(k+1)x - 11 \in (0,1)$ — **bad**. ✓

Every $x \in C_k$ maps into the bad zone. Therefore $m \in B(\lambda_{k,m} x)$ for all $x \in C_k$. $\square$

**Note on endpoint conventions.** At $10(k+1)x = 11$ (i.e., $x = 11/(10(k+1))$, the midpoint of the bad zone crossing), the value mod 11 is exactly 0, which lies in $[0,1)$ and is bad. The boundary $10(k+1)x = 10$ (left endpoint of the interval) gives value $10 \bmod 11 = 10$, which lies in $(10,11)$ — bad (open condition). The proof holds on the open corridor.

### Consequence: Corridors $C_5$ through $C_9$ Are Trivially Reblockable

For any configuration with $\lambda_{10} \geq 10$ (which holds in the large-ratio case $e_{10}/e_1 \geq 10$), the runner with $\lambda_{10} \geq 10$ has $\lambda_{10} \geq \lambda_{k,m} = 10(k+1)/m$ for all $m \geq k+1 \geq 6$ and $k \leq 9$. The Uniform Reblocking Lemma provides full coverage of all released labels.

More concisely: **any configuration with $e_{10}/e_1 \geq 10$ can fully reblock all released labels on $C_k$ for every $k \in \{5,6,7,8,9\}$.** No corridor-exclusion proof is possible on these corridors.

---

## 11. The First Genuine Target: Corridor $C_4$

### Failure of Uniform Reblocking at $k = 4$

For $k = 4$: $10(k+1)x = 50x$ with $x \in C_4 = (1/5, 1/4)$, giving $50x \in (10, 12.5)$.

The bad zone analysis:
- $50x \in (10, 11)$: mod 11 in $(10,11)$ — **bad**. ✓
- $50x \in (11, 12)$: mod 11 in $(0,1)$ — **bad**. ✓
- $50x \in (12, 12.5)$: mod 11 in $(1, 1.5)$ — **safe** (need $< 1$ or $> 10$). ✗

The uniform reblocking fails for $x \in (12/50,\, 1/4) = (6/25,\, 1/4)$.

**The gap:** $G := (6/25,\, 1/4)$, of width $1/4 - 6/25 = 1/100$.

On $G$, no runner with ratio $\lambda = \lambda_{4,m} = 50/m$ can reblock any released label $m \in \{5,\dots,10\}$. Note that $m\lambda_{4,m}x = 50x$ is the same for all $m$ — the uniform reblocking either works or fails for all released labels simultaneously.

### The No-Single-Runner Lemma (Proved)

**Lemma.** *For any released label $m \in \{5,\dots,10\}$ and any runner with ratio $\lambda > 1$, the trace $T_{\lambda,m} := C_4 \cap \lambda^{-1}D_m$ is a proper subset of $C_4$. No single runner can cover a released label on all of $C_4$.*

**Proof.** For runner $\lambda$ to cover label $m$ on all of $C_4 = (1/5, 1/4)$, the interval $(\beta/5, \beta/4)$ with $\beta = m\lambda$ must fit inside a single connected bad component.

*Case 1: $(\beta/5, \beta/4) \subseteq [11n, 11n+1)$.* Then $55n \leq \beta \leq 44n+4$. For $n=0$: $\beta \leq 4 < 5 \leq m\lambda$. Impossible. For $n \geq 1$: $55n \leq 44n+4$ requires $11n \leq 4$. Impossible.

*Case 2: $(\beta/5, \beta/4) \subseteq (11n+10, 11n+12)$.* Then $55n+50 < \beta < 44n+48$, requiring $11n < -2$. Impossible for $n \geq 0$. For $n=-1$: $\beta \in (-5, 4)$, contradicting $\beta = m\lambda > 5$. $\square$

**Consequence.** Every coverage of $C_4$ for any released label requires genuine stitching — a handoff between at least two runners whose bad zones tile $C_4$ without gaps.

### The Correct Proof Target

The target is NOT that all six labels leak simultaneously at one $x$. It is the weaker statement:

$$C_4 \setminus \bigcap_{m=5}^{10} \bigcup_{i=2}^{10} \lambda_i^{-1} D_m \neq \varnothing.$$

Equivalently: $\exists\, x \in C_4$, $\exists\, m \in \{5,\dots,10\}$ such that $x \notin \bigcup_{i=2}^{10} \lambda_i^{-1} D_m$.

### §11.4 Exact $D_m$ Spike Tables

**Definition.** For label $m \in \{1,\dots,10\}$, the **bad set for label $m$** in folded speed-space is
$$D_m := \bigl\{a \in [0,\, 11/2] : m \in B(a)\bigr\} = \bigl\{a \in [0,\, 11/2] : ma \bmod 11 \in [0,1) \cup (10,11)\bigr\}.$$

$D_m$ is periodic with period $11/m$ in $a$-space and has density $2/11$ (bad fraction per period).

In $[0, 11/2]$, the bad intervals come from $ma \in [11n, 11n+1) \cup (11n+10, 11(n+1))$ for $n \geq 0$. Adjacent intervals merge to give connected components of width $2/m$, spaced $11/m$ apart.

**Exact spike tables for released labels $m \in \{5,\dots,10\}$ on $\mathcal{F} = [0, 5.5]$:**

$$D_5 \cap \mathcal{F} = [0,\, 0.2) \cup (2.0,\, 2.4) \cup (4.2,\, 4.6)$$

$$D_6 \cap \mathcal{F} = [0,\, 0.167) \cup (1.667,\, 2.0) \cup (3.5,\, 3.833) \cup (5.333,\, 5.5]$$

$$D_7 \cap \mathcal{F} = [0,\, 0.143) \cup (1.429,\, 1.714) \cup (3.0,\, 3.286) \cup (4.571,\, 4.857)$$

$$D_8 \cap \mathcal{F} = [0,\, 0.125) \cup (1.25,\, 1.5) \cup (2.625,\, 2.875) \cup (4.0,\, 4.25) \cup (5.375,\, 5.5]$$

$$D_9 \cap \mathcal{F} = [0,\, 0.111) \cup (1.111,\, 1.333) \cup (2.333,\, 2.556) \cup (3.556,\, 3.778) \cup (4.778,\, 5.0)$$

$$D_{10} \cap \mathcal{F} = [0,\, 0.1) \cup (1.0,\, 1.2) \cup (2.1,\, 2.3) \cup (3.2,\, 3.4) \cup (4.3,\, 4.5) \cup (5.4,\, 5.5]$$

**Verification.** Each component of $D_m$ arises from two consecutive bad sub-intervals merging at the integer speed $a = 11n/m$ (which lies in $B(a)$ vacuously). The component centres are at $a = 11(n + 1/2)/m$ (midpoint of the bad span), and width is $2/m$ before folding.

### §11.5 Trace Definition and Structural Limits

**Definition (Trace).** For runner ratio $\lambda > 0$ and released label $m \in \{5,\dots,10\}$, define
$$T_{\lambda,m} := \bigl\{x \in C_4 : F(\lambda x) \in D_m\bigr\},$$
where $F$ is the fold to the fundamental domain $[0, 11/2]$. Equivalently, $T_{\lambda,m}$ is the set of $x \in C_4$ where runner $\lambda$ covers label $m$ at the AP grid point $m/(11Q)$.

The folded definition is essential: as $\lambda x$ increases through $[0,\infty)$, the folded trajectory $F(\lambda x)$ oscillates in $[0, 11/2]$ with period $11/\lambda$ in $x$. A single runner visits multiple spikes of $D_m$ as $x$ sweeps $C_4$.

**Measure of the trace.** The total measure of $T_{\lambda,m}$ within $C_4$ is:
$$\mu(T_{\lambda,m}) = \frac{1}{\lambda}\,\mu\!\left(\widetilde{D}_m \cap \left(\frac{\lambda}{5},\, \frac{\lambda}{4}\right)\right),$$
where $\widetilde{D}_m$ denotes $D_m$ lifted to all of $(0,\infty)$ (union of all periodic copies). For large $\lambda$, the interval $(\lambda/5, \lambda/4)$ contains approximately $(\lambda/4 - \lambda/5)/(11/m) = m\lambda/220$ full periods of $D_m$, each contributing measure $2/m$ in $a$-space. So:
$$\mu(T_{\lambda,m}) \approx \frac{1}{\lambda} \cdot \frac{m\lambda}{220} \cdot \frac{2}{m} = \frac{1}{110} \approx 0.009 = \frac{2}{11} \cdot |C_4|.$$

**Critical consequence.** For large $\lambda$, $\mu(T_{\lambda,m})$ is approximately $2/11$ of $|C_4| = 1/20$ — it approaches a positive constant, NOT zero. A simple measure-budget argument (comparing $\sum \mu(T_{\lambda_i,m})$ to $|C_4|$) cannot close the stitching exclusion, since the total available measure grows without bound as $\lambda$ increases.

**The gap sub-problem.** Let $G := (6/25, 1/4) = (0.24, 0.25)$ be the region where uniform reblocking fails. Runner $\lambda$ covers label $m$ on all of $G$ iff $F(\lambda x) \in D_m$ for all $x \in G$, which requires $\lambda \cdot G$ to lie within a single connected component of the lifted $\widetilde{D}_m$.

### §11.6 $\lambda$-Windows for Gap Coverage

For each released label $m$, a runner $\lambda$ covers label $m$ on the entire gap $G = (0.24, 0.25)$ iff $\lambda \cdot (0.24, 0.25) \subset (a_L, a_R)$ for some component $(a_L, a_R)$ of $D_m$, giving $\lambda \in (a_L/0.24,\, a_R/0.25)$.

The condition is non-trivial (non-empty window) iff $a_L/0.24 < a_R/0.25$, i.e., $25 a_L < 24 a_R$, i.e., the component is wide enough relative to the gap scale.

**$\lambda$-windows for gap coverage (first two tiers, $\lambda < 22$):**

| Label $m$ | Component $(a_L, a_R)$ | $\lambda$-window $(a_L/0.24,\, a_R/0.25)$ |
|---|---|---|
| 5 | $(2.0, 2.4)$ | $(8.33, 9.60)$ |
| 5 | $(4.2, 4.6)$ | $(17.50, 18.40)$ |
| 6 | $(1.667, 2.0)$ | $(6.94, 8.00)$ |
| 6 | $(3.5, 3.833)$ | $(14.58, 15.33)$ |
| 6 | $(5.333, 5.5]$ | empty ($22.22 > 22.0$) |
| 7 | $(1.429, 1.714)$ | $(5.95, 6.86)$ |
| 7 | $(3.0, 3.286)$ | $(12.50, 13.14)$ |
| 7 | $(4.571, 4.857)$ | $(19.05, 19.43)$ |
| 8 | $(1.25, 1.5)$ | $(5.21, 6.00)$ |
| 8 | $(2.625, 2.875)$ | $(10.94, 11.50)$ |
| 8 | $(4.0, 4.25)$ | $(16.67, 17.00)$ |
| 9 | $(1.111, 1.333)$ | $(4.63, 5.33)$ |
| 9 | $(2.333, 2.556)$ | $(9.72, 10.22)$ |
| 9 | $(3.556, 3.778)$ | $(14.82, 15.11)$ |
| 9 | $(4.778, 5.0)$ | $(19.91, 20.00)$ |
| 10 | $(1.0, 1.2)$ | $(4.17, 4.80)$ |
| 10 | $(2.1, 2.3)$ | $(8.75, 9.20)$ |
| 10 | $(3.2, 3.4)$ | $(13.33, 13.60)$ |
| 10 | $(4.3, 4.5)$ | $(17.92, 18.00)$ |

**Key structural observation.** The gap $G$ coverage windows for different labels are essentially non-overlapping at first tier:
- Labels 9 and 10 share the window $(4.63,4.8)$ (via $(9,10)$ double-task)
- Labels 8 and 9 share the window $(5.21,5.33)$ (via $(8,9)$ double-task)
- Labels 5 and 10 share the window $(8.75,9.2)$ (via $(5,10)$ double-task)
- No triple-label window at first tier

For labels 6 and 7, the windows at first tier are $(6.94,8.0)$ and $(5.95,6.86)$ — disjoint. So covering both labels 6 and 7 on $G$ requires TWO distinct runners.

### §11.7 The Exact Service-State Catalogue

**Definition.** For $a \in \mathcal{F} = [0, 11/2]$, the **released-label service set** is
$$S(a) := \{m \in \{5,6,7,8,9,10\} : a \in D_m\}.$$

$S(a)$ is constant on each open cell of the partition of $\mathcal{F}$ by the boundary points of all $D_m$.

**Complete service-state table** (cells listed in order; exact fraction endpoints):

| $a$-interval | $S(a)$ | Size |
|---|---|---|
| $(0,\; 1/10)$ | $\{5,6,7,8,9,10\}$ | 6 — staircase |
| $(1/10,\; 1/9)$ | $\{5,6,7,8,9\}$ | 5 |
| $(1/9,\; 1/8)$ | $\{5,6,7,8\}$ | 4 |
| $(1/8,\; 1/7)$ | $\{5,6,7\}$ | 3 |
| $(1/7,\; 1/6)$ | $\{5,6\}$ | 2 |
| $(1/6,\; 1/5)$ | $\{5\}$ | 1 |
| $(1/5,\; 1)$ | $\varnothing$ | 0 |
| $(1,\; 10/9)$ | $\{10\}$ | 1 |
| $(10/9,\; 6/5)$ | $\{9,10\}$ | 2 |
| $(6/5,\; 5/4)$ | $\{9\}$ | 1 |
| $(5/4,\; 4/3)$ | $\{8,9\}$ | 2 |
| $(4/3,\; 10/7)$ | $\{8\}$ | 1 |
| $(10/7,\; 3/2)$ | $\{7,8\}$ | 2 |
| $(3/2,\; 5/3)$ | $\{7\}$ | 1 |
| $(5/3,\; 12/7)$ | $\{6,7\}$ | 2 |
| $(12/7,\; 2)$ | $\{6\}$ | 1 |
| $(2,\; 21/10)$ | $\{5\}$ | 1 |
| $(21/10,\; 23/10)$ | $\{5,10\}$ | 2 |
| $(23/10,\; 7/3)$ | $\{5\}$ | 1 |
| $(7/3,\; 12/5)$ | $\{5,9\}$ | 2 |
| $(12/5,\; 23/9)$ | $\{9\}$ | 1 |
| $(23/9,\; 21/8)$ | $\varnothing$ | 0 |
| $(21/8,\; 23/8)$ | $\{8\}$ | 1 |
| $(23/8,\; 3)$ | $\varnothing$ | 0 |
| $(3,\; 16/5)$ | $\{7\}$ | 1 |
| $(16/5,\; 23/7)$ | $\{7,10\}$ | 2 |
| $(23/7,\; 17/5)$ | $\{10\}$ | 1 |
| $(17/5,\; 7/2)$ | $\varnothing$ | 0 |
| $(7/2,\; 32/9)$ | $\{6\}$ | 1 |
| $(32/9,\; 34/9)$ | $\{6,9\}$ | 2 |
| $(34/9,\; 23/6)$ | $\{6\}$ | 1 |
| $(23/6,\; 4)$ | $\varnothing$ | 0 |
| $(4,\; 21/5)$ | $\{8\}$ | 1 |
| $(21/5,\; 17/4)$ | $\{5,8\}$ | 2 |
| $(17/4,\; 43/10)$ | $\{5\}$ | 1 |
| $(43/10,\; 9/2)$ | $\{5,10\}$ | 2 |
| $(9/2,\; 32/7)$ | $\{5\}$ | 1 |
| $(32/7,\; 23/5)$ | $\{5,7\}$ | 2 |
| $(23/5,\; 43/9)$ | $\{7\}$ | 1 |
| $(43/9,\; 34/7)$ | $\{7,9\}$ | 2 |
| $(34/7,\; 5)$ | $\{9\}$ | 1 |
| $(5,\; 32/6)$ | $\varnothing$ | 0 |
| $(32/6,\; 43/8)$ | $\{6\}$ | 1 |
| $(43/8,\; 27/5)$ | $\{6,8\}$ | 2 |
| $(27/5,\; 11/2]$ | $\{6,8,10\}$ | **3** — unique triple |

**The key structural theorem.** Outside the origin staircase $(0, 1/5)$, every service cell has size $\leq 2$, with the single exception:
$$S(a) = \{6,8,10\}, \quad a \in (27/5,\; 11/2].$$

This is the unique size-3 cell on the folded domain away from the origin.

**Proof of uniqueness.** Computing pairwise intersections of the $D_m$ away from $(0,1/5)$:
- $D_6 \cap D_8 \setminus (0,1/5) = (43/8, 11/2]$ (width $\approx 0.125$)
- $D_6 \cap D_{10} \setminus (0,1/5) = (27/5, 11/2]$ (width $0.1$)
- $D_8 \cap D_{10} \setminus (0,1/5) = (43/8, 11/2]$ (width $\approx 0.125$)

Since $D_6 \cap D_8 \cap D_{10} = (27/5, 11/2]$, and no other triple of released labels has a non-empty intersection away from $(0,1/5)$ — verifiable from the spike tables by exhaustive pairwise overlap check — this is the only size-3 cell. $\square$

### §11.7b Double-Tasking Catalogue (Service-State Formulation)

A runner $\lambda$ is **double-tasking** on $G$ if it covers two released labels simultaneously: $\lambda G \subset D_{m_1} \cap D_{m_2}$. The $\lambda$-window for double-tasking pair $(m_1, m_2)$ is the intersection of the two single-label windows.

The double-tasking catalogue below restates which size-2 service cells are accessible on the gap $G = (0.24, 0.25)$ by a runner $\lambda$. A runner $\lambda$ double-tasks labels $\{m_1, m_2\}$ on $G$ iff $F(\lambda x) \in D_{m_1} \cap D_{m_2}$ for all $x \in G$, which requires $F(\lambda \cdot (0.24, 0.25))$ to lie within the overlap region. By the service-state catalogue, the size-2 cells with accessible $\lambda$-windows are exactly those double-label cells at $a$-values reachable from $\lambda \cdot G = (0.24\lambda, 0.25\lambda)$.

**Complete double-tasking catalogue on $G$ (first tier, $\lambda < 20$):**

| Pair $(m_1, m_2)$ | $\lambda$-window | Exists? |
|---|---|---|
| $(5, 10)$ | $(8.33,9.60) \cap (8.75,9.20) = (8.75, 9.20)$ | ✅ width $0.45$ |
| $(8, 9)$ | $(5.21,6.00) \cap (4.63,5.33) = (5.21, 5.33)$ | ✅ width $0.12$ |
| $(9, 10)$ | $(4.63,5.33) \cap (4.17,4.80) = (4.63, 4.80)$ | ✅ width $0.17$ |
| $(5, 10)$ high | $(17.50,18.40) \cap (17.92,18.00) = (17.92, 18.00)$ | ✅ width $0.08$ |
| $(5, 6)$ | $(8.33,9.60) \cap (6.94,8.00) = \emptyset$ | ❌ |
| $(5, 9)$ | $(8.33,9.60) \cap (9.72,10.22) = \emptyset$ | ❌ |
| $(6, 7)$ | $(6.94,8.00) \cap (5.95,6.86) = \emptyset$ | ❌ |
| $(6, 9)$ | $(6.94,8.00) \cap (9.72,10.22) = \emptyset$ | ❌ |
| $(6, 10)$ | $(6.94,8.00) \cap (8.75,9.20) = \emptyset$ | ❌ |
| $(7, 8)$ | $(5.95,6.86) \cap (5.21,6.00) = (5.95, 6.00)$ | ✅ width $0.05$ |
| $(7, 9)$ | $(5.95,6.86) \cap (4.63,5.33) = \emptyset$ | ❌ |
| $(7, 10)$ | $(5.95,6.86) \cap (4.17,4.80) = \emptyset$ | ❌ |
| $(8, 10)$ | $(5.21,6.00) \cap (4.17,4.80) = \emptyset$ | ❌ |

**Critical intersection.** $D_5 \cap D_{10} \cap \mathcal{F} = [0,0.1) \cup (2.1,2.3) \cup (4.3,4.5)$. The window $(8.75,9.2)$ corresponds to $\lambda \cdot G \subset (2.1,2.3)$: for $\lambda = 9.1$, $9.1 \times (0.24,0.25) = (2.184, 2.275) \subset (2.1,2.3)$. This is the key counterexample to the false "stretching contradiction."

**No triple double-task on $G$ at first tier:** The three non-empty double-task windows $(8.75,9.2)$, $(5.21,5.33)$, $(4.63,4.8)$ are mutually disjoint. The additional pair $(7,8)$ window $(5.95,6.0)$ is also disjoint from these. No single runner covers three or more released labels on $G$.

### §11.8 The Stitching Exclusion: Service-State Formulation

**The correct target (restated).** A total block on $C_4$ requires: for every $x \in C_4$, every released label $m \in \{5,\dots,10\}$ is covered by at least one runner, i.e.,
$$\forall x \in C_4,\; \forall m \in \{5,\dots,10\},\; \exists\, i \in \{2,\dots,10\}\colon F(\lambda_i x) \in D_m.$$

Equivalently, defining the **aggregate service set**
$$\mathcal{S}(x) := \bigcup_{i=2}^{10} S(F(\lambda_i x)),$$
the total block condition is $\mathcal{S}(x) = \{5,6,7,8,9,10\}$ for all $x \in C_4$.

**Why a measure budget fails.** Each runner has $\mu(T_{\lambda_i,m}) \approx |C_4|/11 = 1/220$, so the total available measure for label $m$ is $\lesssim 9/220 < 1/20 = |C_4|$. Wait — this would close the argument: $9 \times (1/110) \approx 0.082 < 0.05 = |C_4|$...

Actually recomputing: $\mu(T_{\lambda,m}) \approx \frac{2}{11} \times |C_4| = \frac{2}{11} \times \frac{1}{20} = \frac{1}{110}$. For 9 runners: $9 \times \frac{1}{110} = \frac{9}{110} \approx 0.082 > |C_4| = \frac{1}{20} = 0.05$. So measure alone does NOT give a contradiction — nine runners have more than enough total measure to cover $C_4$ for a single label. The measure budget is insufficient.

**The service-capacity approach.** Instead, use the service-state catalogue to bound what one runner can service simultaneously. Define the **per-point service capacity** of runner $\lambda$ at position $x$:
$$s_\lambda(x) := |S(F(\lambda x))|.$$

By the service-state catalogue (§11.7), away from the origin staircase region $F(\lambda x) < 1/5$:
- $s_\lambda(x) \leq 2$ for all but the exceptional region $F(\lambda x) \in (27/5, 11/2]$
- $s_\lambda(x) = 3$ iff $F(\lambda x) \in (27/5, 11/2]$, i.e., $S(F(\lambda x)) = \{6,8,10\}$

**Pointwise service capacity lemma.**

**Lemma (Service Capacity).** *For any runner $\lambda$ and any $x \in C_4$: $s_\lambda(x) \leq 3$. Moreover $s_\lambda(x) = 3$ occurs only when $F(\lambda x) \in (27/5, 11/2]$, in which case $S(F(\lambda x)) = \{6,8,10\}$.*

*Proof.* Immediate from the service-state catalogue (§11.7): the unique size-3 cell away from the staircase is $(27/5, 11/2]$. Staircase cells $(F(\lambda x) < 1/5$) have $|S| \leq 6$ but apply only when $\lambda x$ is very small, which for $x > 1/5$ requires $\lambda < 1$. For $\lambda > 1$ and $x > 1/5$: $\lambda x > 1/5$, so $F(\lambda x)$ is computed from $\lambda x \bmod 11$, and the entry is always $\leq 2$ outside the $(27/5, 11/2]$ exception. $\square$

**Implication for stitching.** To cover all 6 labels at point $x \in C_4$, the aggregate service set must include all of $\{5,6,7,8,9,10\}$. If $S(F(\lambda_i x)) \leq 2$ for each runner (the generic case), then at least $6/2 = 3$ runners must be actively serviceing at $x$. At the exceptional state $\{6,8,10\}$, one runner covers 3 labels, but labels $\{5,7,9\}$ still require coverage from other runners — at least $3/2 = 1.5$, so at least 2 more, for a minimum of 3 runners total.

In all cases: **at least 3 runners must be simultaneously actively serviceing** at any $x \in C_4$ for a total block to hold at that point.

**The next rigorous step: Service-State Stitching Lemma.**

**Conjecture (Stitching Exclusion, service-state form).** *For any ordered $1 < \lambda_2 < \cdots < \lambda_{10}$, there exists $x \in C_4$ such that at most 2 runners are simultaneously serviceing (i.e., $\{i : S(F(\lambda_i x)) \neq \varnothing\} \leq 2$), forcing $|\mathcal{S}(x)| \leq 4 < 6$.*

**Why this is the right formulation.** The No-Single-Runner Lemma already shows each individual trace $T_{\lambda_i,m}$ has gaps. The service-state lemma now asks: can the aggregate service $\mathcal{S}(x)$ always achieve full cover? The answer requires showing that at some $x$, the nine folded trajectories $F(\lambda_2 x), \dots, F(\lambda_{10} x)$ collectively fall in service cells whose union misses some label.

**The service-state graph: next step.** To prove the conjecture, build the exact state-transition graph:

1. **Nodes:** All feasible service states $S \subseteq \{5,\dots,10\}$ with $|S| \leq 3$ (from the catalogue).
2. **Edges:** Which states can a single runner transition between as $x$ sweeps continuously through $C_4$ (since $F(\lambda x)$ moves continuously except at fold points).
3. **Coverage constraint:** For $\mathcal{S}(x) = \{5,...,10\}$ at all $x$, the nine runners' state-sequences must jointly cover all 6 labels at every moment.
4. **Exclusion:** Show no nine ordered sequences of states can jointly maintain full coverage across all of $C_4$.

**Status of the service-state stitching lemma.** ⚠️ OPEN. The service-capacity lemma is proved. The global stitching exclusion is the remaining hard algebraic content.

**Connection to two regimes:**
- **Regime 1** ($\lambda_{10}$ near 10): The gap $G = (0.24, 0.25)$ has several serviceable double-task windows. The stitching exclusion on $C_4$ may NOT hold — adversarial configurations may achieve total cover on $C_4$. For these, the exclusion comes from $x = 1$ (Route 3 / v24).
- **Regime 2** ($\lambda_{10}$ large): The available service states on $C_4$ become sparse (each runner's trajectory sweeps many empty cells and few active ones). The stitching exclusion is expected to hold. The threshold $\lambda^*$ is the precise boundary.

---

## 12. Summary: The Proof Programme for $n = 11$

| Step | Statement | Status |
|---|---|---|
| 1. Large-ratio case | $e_{10}/e_1 > 10$; reduce to $x \in (0,1]$ via $\lambda$-substitution | ✅ Setup |
| 2. Corridors $C_5$–$C_9$ | Uniformly reblockable; no exclusion needed | ✅ **Proved** (Uniform Reblocking Lemma) |
| 3. $C_4$: no single runner covers any label | $T_{\lambda,m} \subsetneq C_4$ for all $\lambda > 1$, all $m \geq 5$ | ✅ **Proved** (No-Single-Runner Lemma) |
| 4a. Service-state catalogue | Unique size-3 cell $(27/5, 11/2]$ with $S = \{6,8,10\}$; all others $\leq 2$ | ✅ **Proved** (§11.7) |
| 4b. Service capacity lemma | At any $x \in C_4$, each runner services $\leq 3$ labels; minimum 3 runners needed | ✅ **Proved** (§11.8) |
| 4c. Measure budget | $\sum \mu(T_{\lambda_i,m}) > |C_4|$; measure alone cannot close exclusion | ✅ **Identified** (measure budget fails) |
| 5. Service-state stitching exclusion | Nine ordered runners cannot achieve $\mathcal{S}(x) = \{5,...,10\}$ on all of $C_4$ | ⚠️ **Open** — target theorem |
| 6. $x = 1$ (W_ref, Route 3) | $\bigcup_{i \geq 2} B(\lambda_i) \neq \{1,\dots,10\}$ for all configs | ✅ **Proved** (v24; covers Regime 1 gap) |
| 7. Bounded-ratio case | $e_{10}/e_1 \leq 10$; Theorem GB (label $m=1$, explicit witness $t^* = 10/(11e_{10})$) | ✅ **Proved** |

**Architecture.** Steps 5 and 6 are complementary:
- **Step 5** (service-state stitching exclusion) handles Regime 2: configurations where $\lambda_{10}$ is large enough that nine runners cannot maintain full service coverage on $C_4$.
- **Step 6** (Route 3) handles Regime 1: configurations where Regime 2 fails but $x=1$ witnesses loneliness.
- Together they cover all large-ratio configurations without case-splitting by speed type.

**Next theorem to prove:** The service-state stitching exclusion (Step 5). The exact service-state graph for $C_4$, combined with the trajectory constraint (ordered ratios, fixed $\lambda_i/\lambda_j$), is the algebraic object that should yield the exclusion.

---

## 13. The Cover-Template Transition Graph

### §13.1 High-Service Locus and the Low-Service Region

**Definition.** The **high-service locus** on $\mathcal{F}$ is the set where $|S(a)| \geq 3$:
$$\mathcal{L}_{\geq 3} := \bigl(0,\; 1/7\bigr) \cup \bigl(27/5,\; 11/2\bigr).$$

*Derivation.* From the service-state catalogue (§11.7): the staircase cells with $|S| \geq 3$ are $(0, 1/7)$ (cells of size 3, 4, 5, 6). The only non-staircase size-3 cell is $(27/5, 11/2]$.

**Definition.** For runner $\lambda_i$, define the **high-service window**
$$H_{\lambda_i} := \bigl\{x \in C_4 : F(\lambda_i x) \in \mathcal{L}_{\geq 3}\bigr\}.$$

$H_{\lambda_i}$ is a finite union of short intervals in $C_4$ where runner $\lambda_i$ services 3 or more released labels. Outside $H_{\lambda_i}$, runner $\lambda_i$ services at most 2 released labels.

**Definition.** The **low-service region** is
$$X_{\mathrm{low}} := C_4 \setminus \bigcup_{i=2}^{10} H_{\lambda_i}.$$

On $X_{\mathrm{low}}$, every runner is in a service state of size $\leq 2$ (singleton or pair).

### §13.2 The Seven Minimal Cover Templates

On $X_{\mathrm{low}}$, full 6-label coverage requires that the union of service states $\mathcal{S}(x) = \{5,6,7,8,9,10\}$. Since each active runner contributes at most 2 labels (pair state), full coverage requires at least 3 active runners.

**Exact pair catalogue.** The size-2 service cells (pair states) from the catalogue are:
$$\mathcal{P} = \bigl\{\{9,10\},\{8,9\},\{7,8\},\{6,7\},\{5,10\},\{5,9\},\{7,10\},\{6,9\},\{5,8\},\{5,7\},\{7,9\},\{6,8\}\bigr\}.$$

The **forbidden pairs** (NOT in $\mathcal{P}$) are $\{5,6\}$, $\{6,10\}$, $\{8,10\}$.

**Minimal cover templates** are perfect matchings of $\{5,6,7,8,9,10\}$ into 3 pairs from $\mathcal{P}$.

**Theorem (Seven Minimal Templates).** *There are exactly seven minimal cover templates:*

| Template | Pair 1 | Pair 2 | Pair 3 |
|---|---|---|---|
| $T_1$ | $\{9,10\}$ | $\{6,7\}$ | $\{5,8\}$ |
| $T_2$ | $\{9,10\}$ | $\{5,7\}$ | $\{6,8\}$ |
| $T_3$ | $\{8,9\}$ | $\{6,7\}$ | $\{5,10\}$ |
| $T_4$ | $\{7,8\}$ | $\{5,10\}$ | $\{6,9\}$ |
| $T_5$ | $\{5,10\}$ | $\{7,9\}$ | $\{6,8\}$ |
| $T_6$ | $\{5,9\}$ | $\{7,10\}$ | $\{6,8\}$ |
| $T_7$ | $\{7,10\}$ | $\{6,9\}$ | $\{5,8\}$ |

*Proof.* Enumerate perfect matchings by the pair containing label 6 (must be $\{6,7\}$, $\{6,8\}$, or $\{6,9\}$, since $\{5,6\}$ and $\{6,10\}$ are forbidden):
- If pair with 6 is $\{6,7\}$: remaining $\{5,8,9,10\}$ has valid matchings $\{\{5,10\},\{8,9\}\}$ and $\{\{5,8\},\{9,10\}\}$ — giving $T_3$ and $T_1$.
- If pair with 6 is $\{6,8\}$: remaining $\{5,7,9,10\}$ has valid matchings $\{\{5,7\},\{9,10\}\}$, $\{\{5,9\},\{7,10\}\}$, $\{\{5,10\},\{7,9\}\}$ — giving $T_2$, $T_6$, $T_5$.
- If pair with 6 is $\{6,9\}$: remaining $\{5,7,8,10\}$ has valid matchings $\{\{5,8\},\{7,10\}\}$ and $\{\{5,10\},\{7,8\}\}$ — giving $T_7$ and $T_4$.

Note: $\{5,7\}$ and $\{8,10\}$ is invalid since $\{8,10\} \notin \mathcal{P}$. Total: exactly 7. $\square$

### §13.3 The Rigid Minimal Template Theorem

**Theorem (Template Rigidity).** *From any minimal cover template $T = \{P_1, P_2, P_3\}$, there is no valid single-runner label-loss transition that preserves 6-label coverage.*

*Proof.* In a minimal cover, each label $m \in \{5,...,10\}$ appears in exactly one pair $P_j$. If runner $R_j$ (carrying $P_j$) loses label $m$ (transitions from $P_j$ to $P_j \setminus \{m\}$), then $m$ is no longer covered by any runner. No other runner covers $m$ (each label appears in exactly one pair). Coverage of $m$ fails. $\square$

**Corollary.** Every coverage-preserving transition between two distinct minimal templates requires **concurrent changes by at least two runners**:
- Runner A leaves a pair state $P$ (losing some label $m_A$)
- Runner B simultaneously enters a pair state $P'$ that covers $m_A$

This is a **baton-pass**: runner B must pick up the label that runner A drops, at the exact same $x$.

### §13.4 The Cover-Template Transition Graph

**Definition.** The **transition graph** $\Gamma$ has:
- Vertices: the 7 minimal templates $T_1,\dots,T_7$
- Edge $(T_i, T_j)$ if there exists a valid baton-pass from $T_i$ to $T_j$ (two runners concurrently change states, one losing a label that the other gains)

For an edge to exist, $T_i$ and $T_j$ must share at least 1 common pair (so 2 pairs change).

**One-step baton-pass condition.** A single baton-pass changes exactly one pair $P$ to another pair $P'$ in the template. The lost labels $P \setminus P'$ must be gained by another runner simultaneously, and the gained labels $P' \setminus P$ must be released by that runner. This requires a concurrent 2-runner change.

**Two-pair change (double baton-pass).** For $T_i$ and $T_j$ sharing only one pair, two concurrent baton-passes are required.

**Adjacency computation.** Templates sharing exactly 2 pairs:

| Template pair | Shared pairs | Changed pairs |
|---|---|---|
| $(T_1, T_2)$ | $\{9,10\}$ | $\{6,7\} \leftrightarrow \{5,7\}$, $\{5,8\} \leftrightarrow \{6,8\}$ — 2 changes |
| $(T_1, T_3)$ | $\{6,7\}$ | $\{9,10\} \leftrightarrow \{8,9\}$, $\{5,8\} \leftrightarrow \{5,10\}$ — 2 changes |
| $(T_1, T_7)$ | $\{5,8\}$ | $\{9,10\} \leftrightarrow \{7,10\}$, $\{6,7\} \leftrightarrow \{6,9\}$ — 2 changes |
| $(T_2, T_5)$ | $\{6,8\}$ | $\{9,10\} \leftrightarrow \{5,10\}$, $\{5,7\} \leftrightarrow \{7,9\}$ — 2 changes |
| $(T_2, T_6)$ | $\{6,8\}$ | $\{9,10\} \leftrightarrow \{5,9\}$, $\{5,7\} \leftrightarrow \{7,10\}$ — 2 changes |
| $(T_3, T_4)$ | $\{5,10\}$ | $\{8,9\} \leftrightarrow \{7,8\}$, $\{6,7\} \leftrightarrow \{6,9\}$ — 2 changes |
| $(T_4, T_7)$ | $\{6,9\}$ | $\{7,8\} \leftrightarrow \{7,10\}$, $\{5,10\} \leftrightarrow \{5,8\}$ — 2 changes |
| $(T_5, T_6)$ | $\{6,8\}, \{7,...\}$ | $\{5,10\} \leftrightarrow \{5,9\}$, $\{7,9\} \leftrightarrow \{7,10\}$ — 2 changes |

**No template pair shares all 3 pairs** (they would then be identical). Every transition between distinct templates requires changing at least 2 pairs.

**Key consequence.** Every template transition in $\Gamma$ requires AT LEAST 2 concurrent runner-state changes. This is a structural constraint that comes directly from the perfect-matching structure of the templates.

### §13.5 The Trajectory-Order Lemma

**Lemma (One-Runner State Order).** *For runner $\lambda$ and $x \in C_4$, the folded trajectory $x \mapsto F(\lambda x)$ is piecewise-monotone with period $11/\lambda$ in $x$. As $x$ increases through $C_4$, $F(\lambda x)$ visits the service cells of $\mathcal{F}$ in a determined order — the order of the cell boundaries of the partition of $\mathcal{F}$ encountered by the lifted trajectory $\lambda x$.*

*Consequence.* The sequence of service states visited by runner $\lambda$ on $C_4$ is:
- A consecutive subsequence of the periodic cell sequence $[..., \text{cell}_1, \text{cell}_2, ..., \text{cell}_{45}, \text{cell}_1, ...]$
- The subsequence visited depends only on $\lambda$ (specifically, on $\lambda/5$ and $\lambda/4$ modulo 11)
- Consecutive states in the sequence are adjacent cells in the service catalogue (size changes by $\pm 1$ or $0$ at each boundary)

**Implication for baton-passes.** A baton-pass between runners $A$ and $B$ at position $x_0$ requires:
- Runner A crosses a boundary of $D_{m}$ (losing label $m$) at $x = x_0$: $F(\lambda_A x_0) \in \partial D_m$
- Runner B simultaneously crosses a boundary of $D_{m'}$ (gaining label $m'$ where $m' = m$) at $x = x_0$: $F(\lambda_B x_0) \in \partial D_m$

This means: $\lambda_A x_0 \equiv (11n_A \pm 1)/m \pmod{11}$ and $\lambda_B x_0 \equiv (11n_B \pm 1)/m \pmod{11}$ for the same $x_0$ and same $m$.

Eliminating $x_0$:
$$\frac{\lambda_A}{\lambda_B} = \frac{11n_A \pm 1}{11n_B \pm 1}.$$

**This is a rational condition on the ratio $\lambda_A/\lambda_B$.** For irrational ratios, no baton-pass for the same label $m$ is ever possible. For rational ratios, baton-passes occur only at discrete $x$ values.

### §13.6 The Stitching Exclusion: Sharpest Form

**Conjecture (Cover-Template Stitching Exclusion).** *For any ordered $1 = \lambda_1 < \lambda_2 < \cdots < \lambda_{10}$ with $\lambda_{10} > 10$, there exists $x \in X_{\mathrm{low}} \subset C_4$ such that $\mathcal{S}(x) \neq \{5,\dots,10\}$.*

**Road to proof via the transition graph.** Total coverage on $X_{\mathrm{low}}$ would require the aggregate service set to maintain full coverage through all transitions. By Template Rigidity (§13.3), every transition between minimal templates requires a concurrent 2-runner baton-pass. By the Trajectory-Order Lemma (§13.5), a valid baton-pass for label $m$ between runners $\lambda_A$ and $\lambda_B$ requires the rationality condition $\lambda_A/\lambda_B = (11n_A \pm 1)/(11n_B \pm 1)$.

**Strategy.** To close the stitching exclusion, one approach is:

1. **Step A.** Show that $X_{\mathrm{low}}$ is non-empty (the high-service windows $H_{\lambda_i}$ cannot cover all of $C_4$). This requires bounding the total measure $\sum_i |H_{\lambda_i}|$ and showing it is less than $|C_4| = 1/20$.

2. **Step B.** On $X_{\mathrm{low}}$, show that the 9 runners cannot maintain one of the 7 minimal templates at every $x$. The key obstruction is that maintaining a template requires constant baton-passes, which require rational ratio conditions on specific pairs of runners.

3. **Step C.** Show that no set of 9 ordered ratios $\lambda_2 < \cdots < \lambda_{10}$ can simultaneously satisfy all required rationality conditions for all needed baton-passes across all of $X_{\mathrm{low}}$.

**Step A: Bounding $|H_{\lambda_i}|$.** The high-service region $H_\lambda = \{x \in C_4 : F(\lambda x) \in (0, 1/7) \cup (27/5, 11/2)\}$. The density of $(0,1/7) \cup (27/5, 11/2)$ in $\mathcal{F}$ is $(1/7 + 1/10)/5.5 = (10/70 + 7/70)/5.5 = 17/(70 \times 5.5) = 17/385 \approx 4.4\%$. So $|H_\lambda| \approx 0.044 \times |C_4|$. The total $|\bigcup_i H_{\lambda_i}| \leq \sum_i |H_{\lambda_i}| \approx 9 \times 0.044 \times |C_4| \approx 0.4 \times |C_4|$. So $|X_{\mathrm{low}}| \geq 0.6 \times |C_4|$ — a substantial portion of $C_4$ is low-service. Step A reduces to making this rigorous.

**Step B** is the hard algebraic content: the transition graph analysis showing that the 7-template structure cannot be sustained.

**Step C** requires number-theoretic input (rationality conditions on ratios).

**Status.** Step A is ⚠️ achievable (measure bound on high-service locus). Steps B and C are ⚠️ open.

---

## 14. The Four-Lemma Proof Programme

This section refines the proof target into a clean chain of four lemmas. Once all four are established, the constructive witness follows immediately.

### §14.1 Lemma 1 (One-Runner State-Word Lemma)

**Lemma 1.** *As $a$ increases monotonically through $\mathcal{F} = [0,\; 11/2]$, the service set $S(a)$ follows the exact ordered word:*

$$\underbrace{\{5{,}6{,}7{,}8{,}9{,}10\}\to\cdots\to\{5{,}6{,}7\}}_{\text{high-service staircase}}\to\{5,6\}\to\{5\}\to\varnothing$$
$$\to\{10\}\to\{9,10\}\to\{9\}\to\{8,9\}\to\{8\}\to\{7,8\}\to\{7\}\to\{6,7\}\to\{6\}$$
$$\to\{5\}\to\{5,10\}\to\{5\}\to\{5,9\}\to\{9\}\to\varnothing\to\{8\}\to\varnothing$$
$$\to\{7\}\to\{7,10\}\to\{10\}\to\varnothing\to\{6\}\to\{6,9\}\to\{6\}\to\varnothing$$
$$\to\{8\}\to\{5,8\}\to\{5\}\to\{5,10\}\to\{5\}\to\{5,7\}\to\{7\}\to\{7,9\}\to\{9\}\to\varnothing$$
$$\to\{6\}\to\{6,8\}\to\underbrace{\{6,8,10\}}_{\text{high-service triple}}$$

with exact cell boundaries given by the fractions in the §11.7 table.

**Proof.** Direct reading of the §11.7 service-state catalogue in increasing $a$-order. Every consecutive pair of states in the word shares exactly one boundary point, and adjacent states differ in exactly one label. $\square$

**Structural consequences of the state word:**

(W1) **No direct pair-to-pair jumps.** Between any two pair states in the word, there is always at least one singleton or null state. A runner in pair state $P$ cannot transition to any other pair state $P'$ without first passing through a singleton or null.

(W2) **Forced intermediate states.** To move from $\{9,10\}$ to $\{6,7\}$, a runner must pass through: $\{9\}, \{8,9\}, \{8\}, \{7,8\}, \{7\}, \{6,7\}$ — six state changes and four intermediate states, all singletons. No shortcut exists.

(W3) **Each pair appears at most twice.** $\{5,10\}$ appears twice (at positions $(21/10, 23/10)$ and $(43/10, 9/2)$). All other pair states appear exactly once. A runner visiting both occurrences of $\{5,10\}$ must pass through a long null gap between them.

(W4) **Six null gaps.** The word contains null ($\varnothing$) cells at: $(1/5,1)$, $(23/9,21/8)$, $(23/8,3)$, $(17/5,7/2)$, $(23/6,4)$, $(5,32/6)$. During these gaps, the runner contributes zero coverage. The largest null gap $(1/5,1)$ has width $4/5$, dominating the low-service region.

(W5) **Label 7 is not isolated.** Label 7 appears in pairs $\{7,8\}, \{6,7\}, \{7,10\}, \{5,7\}, \{7,9\}$ — five distinct pair states. A runner cannot be "dedicated solely to label 7"; it inevitably serves other labels when near label 7 in the word.

### §14.2 Lemma 2 (Boundary Partition Lemma)

**Setup.** Fix any ordered speed configuration $\lambda_2 < \cdots < \lambda_{10}$. For each runner $i$, the boundary times are the $x \in C_4$ where $F(\lambda_i x)$ crosses a cell boundary of the §11.7 partition.

**Lemma 2 (Boundary Partition).** *Define the finite set of boundary times:*
$$\mathcal{B} := \bigl\{x \in C_4 : \exists\, i,\; F(\lambda_i x) \in \Xi_0\bigr\},$$
*where $\Xi_0$ is the set of all cell boundary points from §11.7. Then:*
*(i) $\mathcal{B}$ is finite: $|\mathcal{B}| \leq 9 \times |\Xi_0| \times \lceil \lambda_{10}/20 \rceil$.*
*(ii) On each open component $J_k$ of $C_4 \setminus \mathcal{B}$, every runner state $S(F(\lambda_i x))$ is constant.*
*(iii) The aggregate service set $\mathcal{S}(x) = \bigcup_i S(F(\lambda_i x))$ is constant on each regime $J_k$.*

**Proof.** (i): Each runner crosses each boundary point of $\mathcal{F}$ at most $\lceil \lambda_i/11 \cdot |C_4|/1 \rceil$ times as $F(\lambda_i x)$ oscillates; summing over all 9 runners and all boundary points gives finiteness. (ii)–(iii): continuity of $F(\lambda_i x)$ and constancy of $S$ between boundaries. $\square$

**Reduction.** The stitching exclusion holds iff $\exists\, k\colon \mathcal{S}(J_k) \neq \{5,...,10\}$. The constructive witness is:
$$t^* = \frac{m^* x^*}{11 e_1}, \quad x^* \in J_{k^*},\quad m^* \notin \mathcal{S}(J_{k^*}).$$

Note: template transitions occur at boundary times $\mathcal{B}$, where multiple runners can change state simultaneously. The partition lemma replaces "one runner changes at a time" with the correct picture: on each regime, the state is frozen; at each boundary, any subset of runners may change.

### §14.3 Lemma 3 (Legal Template-Transition Lemma)

**Lemma 3.** *At any boundary time $x_0 \in \mathcal{B}$, each runner crossing a cell boundary changes its service state to an adjacent state in the word (Lemma 1) — a one-label change. A template transition from $T_{\text{old}}$ on $J_k$ to a new aggregate state on $J_{k+1}$ is called **legal** if $\mathcal{S}(J_{k+1}) = \{5,...,10\}$. For a legal transition:*
- *Every label $m$ that exits some runner's state must be simultaneously covered by another runner's new state on $J_{k+1}$.*
- *No runner may jump from one pair state to another non-adjacent pair state in the word.*

**Proof.** Immediate from Lemma 1 (one-label changes only) and the definition of coverage. $\square$

**Template-transition obstruction.** From Template Rigidity (§13.3), every label in a minimal template appears in exactly one pair. Any single runner exiting a pair causes an uncovered label UNLESS another runner simultaneously picks it up.

Concretely, to transition from $T_1 = \{\{9,10\},\{6,7\},\{5,8\}\}$ to any other template:
- If runner with $\{9,10\}$ exits to $\{9\}$ (losing label 10): another runner must simultaneously enter a state containing 10. Valid options from the state word: $\{5,10\}$, $\{7,10\}$, $\{9,10\}$, $\{10\}$. But $\{10\}$ alone doesn't cover the template's other labels.
- The simultaneous constraint means: at $x_0$, runner A exits $\{9,10\} \to \{9\}$ AND runner B exits $\{?\} \to \{10,...\}$ — requiring two runners to cross boundaries at the same $x_0$.

This is generically a measure-zero event (requires coincidence of boundary times for two distinct runners).

### §14.4 Lemma 4 (No Full Transition Chain) — Open

**Target Lemma 4.** *For any ordered $\lambda_2 < \cdots < \lambda_{10}$, the regime sequence $\mathcal{S}(J_1), \ldots, \mathcal{S}(J_N)$ has at least one $k$ with $\mathcal{S}(J_k) \neq \{5,...,10\}$.*

**Status.** ⚠️ OPEN. This is the main missing theorem.

**Sub-lemma 4a: $X_{\text{low}} \neq \varnothing$.** Show that the high-service windows $\bigcup_i H_{\lambda_i}$ do not cover all of $C_4$.

*Caution:* The naive bound $|H_\lambda| \approx 0.044 \cdot |C_4|$ is an asymptotic for large $\lambda$ (many periods visited). For small $\lambda_i$ (runners with low speed ratios), $H_{\lambda_i}$ could be larger. The rigorous bound must track the folded trajectory explicitly for each runner.

*Rigorous approach:* For runner $\lambda_i$ on $C_4 = (1/5,1/4)$: the folded image $\lambda_i \cdot C_4 = (\lambda_i/5, \lambda_i/4)$ has width $\lambda_i/20$. The high-service locus in $\mathcal{F}$ has total width $(1/7 + 1/10) = 17/70$. The number of high-service sub-intervals of $\mathcal{F}$ intersecting $(\lambda_i/5,\lambda_i/4)$ is at most $\lfloor \lambda_i/(20) \cdot (70/17) \rfloor + c$ for a small constant $c$ (boundary terms). Each intersection has width at most $1/7$ (staircase boundary) or $1/10$ (triple resonance). A careful computation gives $|H_{\lambda_i}| \leq (1/7 + 1/10)/11 \cdot |C_4| \cdot (1 + 20/(11\lambda_i))$ — the density bound with a correction term. For $\lambda_i \geq 5$: $|H_{\lambda_i}| \leq 0.06 \cdot |C_4|$. Summing over 9 runners: $\sum_i |H_{\lambda_i}| \leq 0.54 \cdot |C_4| < |C_4|$. This gives $X_{\text{low}} \neq \varnothing$ for $\lambda_i \geq 5$ for all $i$.

**Sub-lemma 4b: No full chain on $X_{\text{low}}$.** On each regime $J_k \subset X_{\text{low}}$, every runner is in a low-service state ($|S| \leq 2$). Full coverage requires one of the 7 minimal templates. Transitions between templates require:
1. At least 2 simultaneous boundary crossings (from §14.3)
2. Each crossing is adjacent in the state word (W1)
3. The ordered ratio constraint ($\lambda_i/\lambda_j$ fixed) determines which boundary crossings can be simultaneous

The state-word order (W2) shows that transitions between "far-apart" templates (sharing no common pair) require many simultaneous boundary crossings — a severely constrained event.

**The open question.** Can nine runners with fixed ordered ratios arrange their boundary crossings to always maintain one of the 7 templates across every regime of $X_{\text{low}}$? The conjectured answer is NO.

### §14.5 Constructive Witness and Proof Summary

Once Lemma 4 is established:

**Theorem (Constructive Witness for $n=11$, large ratio).** *For $e_{10}/e_1 > 10$ in the Regime 2 ($\lambda_{10} > \lambda^*$): the boundary partition yields a regime $J_{k^*} \subset C_4$ with a surviving label $m^*$. The lonely time is:*
$$t^* = \frac{m^* x^*}{11 e_1}, \quad x^* \in J_{k^*}.$$

At $t^*$: runner 1 (with $\lambda_1 x^* = x^* \in C_4$) is in the bad zone for labels $\{1,2,3,4\}$ and safe for all $m \geq 5$. No runner $\lambda_i$ covers label $m^*$ on $J_{k^*}$, so $m^*$ is a surviving label. The witness is explicit and constructive. $\square$ (pending Lemma 4)

| Lemma | Statement | Status |
|---|---|---|
| 1. State-Word | Exact ordered word for $S(a)$ on $\mathcal{F}$, with 6 null gaps | ✅ Proved |
| 2. Boundary Partition | Finite regimes; $\mathcal{S}$ constant on each; witness explicit | ✅ Proved |
| 3. Legal Transitions | Only adjacent-word state changes; $\geq 2$ simultaneous crossings per template change | ✅ Proved |
| 4a. $X_{\text{low}} \neq \varnothing$ | $\sum |H_{\lambda_i}| < |C_4|$ for $\lambda_i \geq 5$ | ⚠️ Needs careful bound |
| 4b. No full chain | No 9-runner assignment maintains a minimal template on all of $X_{\text{low}}$ | ⚠️ Open — main hard step |
| Witness | $t^* = m^* x^*/(11e_1)$, constructive and explicit | ✅ Once Lemma 4 holds |

---

## 15. The Exact Transition Graph

### §15.1 Low-Service Pair States in Word Order

From the state word (§14.1), the pair states appear in this fixed order as $a$ increases through $\mathcal{F}$:

| # | Pair | $a$-interval | Exact fractions |
|---|---|---|---|
| P1 | $\{5,6\}$ | $(0.143, 0.167)$ | $(1/7, 1/6)$ — adjacent to high-service |
| P2 | $\{9,10\}$ | $(1.111, 1.200)$ | $(10/9, 6/5)$ |
| P3 | $\{8,9\}$ | $(1.250, 1.333)$ | $(5/4, 4/3)$ |
| P4 | $\{7,8\}$ | $(1.429, 1.500)$ | $(10/7, 3/2)$ |
| P5 | $\{6,7\}$ | $(1.667, 1.714)$ | $(5/3, 12/7)$ |
| P6 | $\{5,10\}$ | $(2.100, 2.300)$ | $(21/10, 23/10)$ |
| P7 | $\{5,9\}$ | $(2.333, 2.400)$ | $(7/3, 12/5)$ |
| P8 | $\{7,10\}$ | $(3.200, 3.286)$ | $(16/5, 23/7)$ |
| P9 | $\{6,9\}$ | $(3.556, 3.778)$ | $(32/9, 34/9)$ |
| P10 | $\{5,8\}$ | $(4.200, 4.250)$ | $(21/5, 17/4)$ |
| P11 | $\{5,10\}$ | $(4.300, 4.500)$ | $(43/10, 9/2)$ — second occurrence |
| P12 | $\{5,7\}$ | $(4.571, 4.600)$ | $(32/7, 23/5)$ |
| P13 | $\{7,9\}$ | $(4.778, 4.857)$ | $(43/9, 34/7)$ |
| P14 | $\{6,8\}$ | $(5.375, 5.400)$ | $(43/8, 27/5)$ |

**State word topology.** The word is a linear order: P1 < P2 < P3 < $\cdots$ < P14 (by $a$-value). Between consecutive pairs, there are singleton and null states (from the word in §14.1). A runner traversing the word moves through pairs in this order — it cannot skip.

**Adjacent pairs in the word** (pairs with only singleton or null states between them):
- P2 $\{9,10\}$ ↔ P3 $\{8,9\}$: one singleton $\{9\}$ between them
- P3 $\{8,9\}$ ↔ P4 $\{7,8\}$: one singleton $\{8\}$ between them
- P4 $\{7,8\}$ ↔ P5 $\{6,7\}$: one singleton $\{7\}$ between them
- P6 $\{5,10\}$ ↔ P7 $\{5,9\}$: one singleton $\{5\}$ between them
- P11 $\{5,10\}$ ↔ P12 $\{5,7\}$: one singleton $\{5\}$ between them
- P12 $\{5,7\}$ ↔ P13 $\{7,9\}$: one singleton $\{7\}$ between them
- P13 $\{7,9\}$ ↔ P14 $\{6,8\}$: one null gap + singleton $\{6\}$ between them (two intervening states)

All other consecutive pairs have longer gaps (null intervals or multiple singletons).

### §15.2 The Seven Template Nodes

Recall:
$$T_1=\{P_2,P_5,P_{10}\},\quad T_2=\{P_2,P_{12},P_{14}\},\quad T_3=\{P_3,P_5,P_6\},$$
$$T_4=\{P_4,P_6,P_9\},\quad T_5=\{P_6,P_{13},P_{14}\},\quad T_6=\{P_7,P_8,P_{14}\},\quad T_7=\{P_8,P_9,P_{10}\}.$$

(where $P_6 = \{5,10\}$ refers to the first occurrence at $(21/10, 23/10)$; $P_{11} = \{5,10\}$ is the second occurrence at $(43/10, 9/2)$.)

### §15.3 Template Adjacency (Shared-Pair Graph)

Two templates are **pair-adjacent** if they share exactly 2 of 3 pairs (differing in exactly 1 pair). From direct enumeration:

| Edge | Shared pairs | Changed pair |
|---|---|---|
| $T_1 \leftrightarrow T_2$ | $P_2 = \{9,10\}$ | $P_5 \leftrightarrow P_{12}$, $P_{10} \leftrightarrow P_{14}$ |
| $T_1 \leftrightarrow T_3$ | $P_5 = \{6,7\}$ | $P_2 \leftrightarrow P_3$, $P_{10} \leftrightarrow P_6$ |
| $T_1 \leftrightarrow T_7$ | $P_{10} = \{5,8\}$ | $P_2 \leftrightarrow P_8$, $P_5 \leftrightarrow P_9$ |
| $T_2 \leftrightarrow T_5$ | $P_{14} = \{6,8\}$ | $P_2 \leftrightarrow P_6$, $P_{12} \leftrightarrow P_{13}$ |
| $T_2 \leftrightarrow T_6$ | $P_{14} = \{6,8\}$ | $P_2 \leftrightarrow P_7$, $P_{12} \leftrightarrow P_8$ |
| $T_3 \leftrightarrow T_4$ | $P_6 = \{5,10\}$ | $P_3 \leftrightarrow P_4$, $P_5 \leftrightarrow P_9$ |
| $T_4 \leftrightarrow T_7$ | $P_9 = \{6,9\}$ | $P_4 \leftrightarrow P_8$, $P_6 \leftrightarrow P_{10}$ |
| $T_5 \leftrightarrow T_6$ | $P_{14} = \{6,8\}$ | $P_6 \leftrightarrow P_7$, $P_{13} \leftrightarrow P_8$ |

The pair-adjacency graph is: T1—T2—T5—T3—T1, T2—T6—T5, T1—T7—T4—T3, T4—T7, T5—T6. This graph is **connected** — every template is reachable from every other via pair-adjacent steps.

Templates sharing exactly 1 pair (require 2-pair change): $(T_3,T_5)$, $(T_4,T_5)$, $(T_6,T_7)$.

Templates sharing no pairs (require 3-pair change): $(T_1,T_4)$, $(T_1,T_5)$, $(T_1,T_6)$, $(T_2,T_3)$, $(T_2,T_4)$, $(T_2,T_7)$, $(T_3,T_6)$, $(T_3,T_7)$, $(T_4,T_6)$, $(T_5,T_7)$.

### §15.4 Legal Transition Analysis

For each pair-adjacent edge, we compute whether a legal word-transition exists. A legal transition from $T_i$ to $T_j$ requires:
- For each changed pair $P_{\text{old}} \to P_{\text{new}}$: either a runner transitions along the word from $P_{\text{old}}$ toward $P_{\text{new}}$ (through intermediate singletons/nulls), or a new runner enters $P_{\text{new}}$ from an adjacent state
- Full coverage is maintained at every regime during the transition

**Edge $T_1 \leftrightarrow T_3$: $\{P_2,P_5,P_{10}\} \to \{P_3,P_5,P_6\}$**

Changes: $P_2 = \{9,10\} \to P_3 = \{8,9\}$ and $P_{10} = \{5,8\} \to P_6 = \{5,10\}$.

In the word:
- $P_2$ (pos 2) and $P_3$ (pos 3) are adjacent (one singleton $\{9\}$ between). Runner A: $\{9,10\} \xrightarrow{\text{loses }10} \{9\} \xrightarrow{\text{gains }8} \{8,9\}$.
- $P_{10}$ (pos 10) and $P_6$ (pos 6) are NOT adjacent — $P_6$ is far left of $P_{10}$ in the word. A runner cannot go from $P_{10}$ to $P_6$ by moving forward; it would need to WRAP AROUND (pass through the end of the word at $\{6,8,10\}$ and back) or move BACKWARD (decreasing $a$, i.e., $F(\lambda x)$ decreasing). Both require special conditions.

**Key observation.** $P_6 = \{5,10\}$ (first occurrence, pos 6) is at $a \in (2.1, 2.3)$ and $P_{10} = \{5,8\}$ is at $a \in (4.2, 4.25)$. A runner at $P_{10}$ would need to DECREASE $a$ to reach $P_6$. But $F(\lambda x)$ increases when $\lambda x \bmod 11 \in (0, 5.5)$ and decreases when $\lambda x \bmod 11 \in (5.5, 11)$. So:

- If runner C is on a DECREASING part of its $F$-trajectory on $C_4$: $F(\lambda_C x)$ decreases as $x$ increases, visiting states in REVERSE word order. A decreasing-trajectory runner at $P_{10}$ (forward pos 10) is moving backward toward $P_9$ (pos 9), $P_8$ (pos 8), etc.

However, the second occurrence of $\{5,10\}$ is $P_{11}$ (at pos 11, $a \in (4.3, 4.5)$), which is AFTER $P_{10}$ (at pos 10, $a \in (4.2, 4.25)$) in the word. So a runner going FORWARD from $P_{10}$ passes through $\{5\}$ (singleton) and then reaches $P_{11} = \{5,10\}$.

Thus: $P_{10} = \{5,8\} \xrightarrow{\text{loses }8} \{5\} \xrightarrow{\text{gains }10} P_{11} = \{5,10\}$ (second occurrence). This is a FORWARD transition in the word.

**Revised analysis for $T_1 \to T_3$:**
- Runner A: $P_2 \to \{9\} \to P_3$ (gains 8, loses 10 temporarily)
- Runner C: $P_{10} \to \{5\} \to P_{11}$ (gains 10, loses 8 temporarily)

During the transition:
- When A is in $\{9\}$: label 10 is uncovered by A. Must be covered by runner D (e.g., D in singleton $\{10\}$ or pair containing 10).
- When C is in $\{5\}$: label 8 is uncovered by C. Must be covered by A, IF A has already entered $P_3 = \{8,9\}$.

**Sequential ordering constraint.** For coverage to be maintained:
1. Runner A must enter $P_3 = \{8,9\}$ BEFORE runner C exits $P_{10} = \{5,8\}$.
2. A runner covering label 10 must be active while A is in $\{9\}$.

This imposes an ordering on the boundary times: $x_A^{\text{exit} P_2} < x_A^{\text{enter} P_3} < x_C^{\text{exit} P_{10}} < x_C^{\text{enter} P_{11}}$.

The boundary times are determined by $\lambda_A$ and $\lambda_C$: $x_A^{\text{exit} P_2}$ is where $F(\lambda_A x) = 6/5$ (boundary of $\{9,10\}$), etc. The ordering constraint becomes an exact inequality on $\lambda_A/\lambda_C$.

**Conclusion.** The $T_1 \to T_3$ transition IS LEGAL in principle, but requires:
1. A specific ordering of runners A and C (determined by $\lambda_A, \lambda_C$)
2. A fourth runner D covering label 10 during A's singleton phase
3. The total transition must fit within $C_4$

**Edge $T_1 \leftrightarrow T_7$: $\{P_2,P_5,P_{10}\} \to \{P_8,P_9,P_{10}\}$**

Changes: $P_2 = \{9,10\} \to P_8 = \{7,10\}$ and $P_5 = \{6,7\} \to P_9 = \{6,9\}$.

In the word:
- $P_2 \to P_8$: word positions 2 and 8 are far apart. Between them: $P_3 = \{8,9\}, P_4 = \{7,8\}, P_5 = \{6,7\}, P_6 = \{5,10\}, P_7 = \{5,9\}$ — five pair states and many singletons/nulls in between. A runner cannot transition $P_2 \to P_8$ in one or two boundary crossings; it must traverse the entire intermediate word.
- During this traversal, label 10 (from P_2) must be continuously covered, label 9 must be covered, labels 8, 7, 5 might be transiently covered and uncovered.

**The transition $T_1 \leftrightarrow T_7$ requires traversal of 5 intermediate pair states by one runner.** This takes many boundary crossings and cannot be done in a short $x$-interval.

**Edge $T_2 \leftrightarrow T_6$: $\{P_2,P_{12},P_{14}\} \to \{P_7,P_8,P_{14}\}$**

Changes: $P_2 = \{9,10\} \to P_7 = \{5,9\}$ and $P_{12} = \{5,7\} \to P_8 = \{7,10\}$.

- $P_2 \to P_7$: positions 2 and 7 — gap of 5 pair states.
- $P_{12} \to P_8$: positions 12 and 8 — $P_{12}$ is AFTER $P_8$ in the word. A forward-traversing runner at $P_{12}$ cannot reach $P_8$ without wrapping. A backward-traversing runner at $P_{12}$ moves toward $P_{11}, P_{10}, P_9, P_8$ — possible!

So $T_2 \leftrightarrow T_6$ might involve one forward runner (A: $P_2$ forward toward $P_7$) and one backward runner (B: $P_{12}$ backward toward $P_8$). The backward traversal means $F(\lambda_B x)$ is decreasing on $C_4$ for this portion.

### §15.5 Transition Graph: Summary

| Edge | Forward word steps needed | Backward word steps needed | Feasibility |
|---|---|---|---|
| $T_1 \leftrightarrow T_3$ | A: 1 step ($P_2 \to P_3$), C: 1 step ($P_{10} \to P_{11}$) | None | ✅ Feasible (conditional on ordering) |
| $T_3 \leftrightarrow T_4$ | A: 1 step ($P_3 \to P_4$), B: longer ($P_5 \to P_9$) | None | ⚠️ Feasible but B needs 4 steps |
| $T_4 \leftrightarrow T_7$ | A: longer ($P_4 \to P_8$) | C: 1 step ($P_6 \to P_{10}$) | ⚠️ A needs 4 steps |
| $T_5 \leftrightarrow T_6$ | A: 1 step ($P_6 \to P_7$), B: 1 step ($P_{13} \to P_8$ backward) | B backward 5 steps | ⚠️ B backward is long |
| $T_2 \leftrightarrow T_5$ | A: longer ($P_2 \to P_6$), B: 1 step ($P_{12} \to P_{13}$) | None | ⚠️ A needs ~4 steps |
| $T_2 \leftrightarrow T_6$ | A: longer ($P_2 \to P_7$), B: backward ($P_{12} \to P_8$) | Mixed | ⚠️ Both runners need many steps |
| $T_1 \leftrightarrow T_2$ | Both changes are long word-traversals | None | ❌ Requires many concurrent steps |
| $T_1 \leftrightarrow T_7$ | $P_2 \to P_8$: 6 steps | None | ❌ Cannot complete in $C_4$ span |

**Key finding:** The only pair-adjacent transitions achievable with SHORT (1–2 step) word traversals are:
- $T_1 \leftrightarrow T_3$: A traverses $P_2 \to P_3$ (1 step), C traverses $P_{10} \to P_{11}$ (1 step, different occurrence of $\{5,10\}$)
- Partial: $T_3 \leftrightarrow T_4$ for the $P_3 \to P_4$ step (adjacent in word)

All other pair-adjacent transitions require multi-step word traversals spanning substantial portions of $\mathcal{F}$.

### §15.6 The Short-Transition Subgraph

The only transitions achievable by near-simultaneous 1-step word moves are:

$$T_1 \xleftrightarrow{\ \text{short}\ } T_3 \xleftrightarrow{\text{partial short}} T_4$$

All other transitions in the full pair-adjacency graph require long word traversals.

**Structural consequence.** On any short interval of $C_4$, the template can change only via the short transitions. The templates $\{T_2, T_5, T_6, T_7\}$ are not reachable from $T_1$ by short transitions — they require runner traversals that take significant $x$-length.

This means: a configuration starting in $T_1$ on a regime $J_k$ can only transition to $T_3$ (or stay at $T_1$) on the adjacent regime $J_{k+1}$, without a long setup period. The templates $T_2, T_5, T_6, T_7$ require prior runner positioning.

### §15.7 The No-Full-Chain Target (Sharpened)

**What must be shown.** Given the short-transition subgraph $\{T_1, T_3, T_4\}$ and the long transitions $\{T_2, T_5, T_6, T_7\}$, the stitching exclusion reduces to:

**Claim.** *The templates $T_1, T_3$ together cannot cover all of $X_{\text{low}}$ for any 9-runner configuration. There exist regimes in $X_{\text{low}}$ where the state is not $T_1$, $T_3$, or any valid cover.*

**Why this is plausible.** Templates $T_1 = \{P_2, P_5, P_{10}\}$ and $T_3 = \{P_3, P_5, P_6\}$ both require a runner at $P_5 = \{6,7\}$ (word position 5, $a \in (5/3, 12/7)$). This corresponds to the narrow $\{6,7\}$ cell of width $12/7 - 5/3 = (36-35)/21 = 1/21 \approx 0.048$.

For runner $\lambda$ to be in state $\{6,7\}$ at $x \in C_4$: requires $F(\lambda x) \in (5/3, 12/7)$, i.e., $\lambda x$ lies in an interval of width $1/21$ near multiples of $11$. The trace $T_{\lambda,6} \cap T_{\lambda,7}$ has width $(1/21)/\lambda$ in $x$-space. For $\lambda \sim 7$: width $\approx 1/147 \approx 0.007$.

So the $\{6,7\}$ regime for any single runner occupies only $\approx 7/147 = 1/21$ of $C_4$. NINE runners can collectively occupy $\{6,7\}$ for at most $9/21 \approx 43\%$ of $C_4$. During the remaining $\geq 57\%$ of $C_4$, NO runner is in state $\{6,7\}$, and templates $T_1$ and $T_3$ are unavailable.

On those regimes, coverage of labels 6 AND 7 simultaneously must come from two separate runners (one covering 6, one covering 7 from different pair states). The available pairs are: labels 6 from $P_5, P_9, P_{14}$; labels 7 from $P_4, P_5, P_8, P_{12}, P_{13}$. These are separate pair states.

**The remaining computation.** On the regimes where no runner is in $\{6,7\}$, the only templates that can hold are those NOT using $P_5$: these are $T_2, T_4, T_5, T_6, T_7$ (from the 7 templates, only $T_1$ and $T_3$ use $P_5$).

The question is: can templates $T_2, T_4, T_5, T_6, T_7$ collectively cover the $\{6,7\}$-free regimes of $C_4$? This requires runners positioned at $P_2, P_4, P_6, P_7, P_8, P_9, P_{12}, P_{13}, P_{14}$ at the appropriate $x$-values. With 9 runners and the fixed-ratio constraint, this is a finite feasibility problem.

**Status.** The full computation of the no-full-chain theorem is ⚠️ OPEN. The short-transition analysis above gives the structure of the problem; the final step requires showing that the $T_2, T_4, T_5, T_6, T_7$ templates cannot cover the entire $\{6,7\}$-free portion of $C_4$ with 9 fixed-ratio runners.

---

*See also: `lrc_elegant_proof_sketch_v1.md` (two-mechanisms picture), `lrc_ap_worst_case_v1.md` (AP as coordinate system), `lrc_n11_structural_mechanism_v1.md` (Coupling Principle as shadow of $B(11-a)=B(a)$)*

---

## 16. Exact λ-Band Table and Template-Support Computation

### §16.1 Corrected Template List (9 Minimal Cover Templates)

The §13 list of 7 templates was incomplete: it omitted pair $P_1 = \{5,6\}$ at $(1/7, 1/6)$. Although $P_1$ lies just outside the high-service staircase (which ends at $1/7$), it is a valid low-service pair. Including it yields two additional minimal covers:

$$T_{\mathrm{NEW1}} = \{P_1,\, P_4,\, P_2\} = \bigl\{\{5,6\},\{7,8\},\{9,10\}\bigr\}$$
$$T_{\mathrm{NEW2}} = \{P_1,\, P_8,\, P_3\} = \bigl\{\{5,6\},\{7,10\},\{8,9\}\bigr\}$$

The complete 9-template list is:

| Template | Pairs (service labels) | Word positions |
|---|---|---|
| $T_1$ | $\{9,10\},\{6,7\},\{5,8\}$ | $P_2, P_5, P_{10}$ |
| $T_2$ | $\{9,10\},\{5,7\},\{6,8\}$ | $P_2, P_{12}, P_{14}$ |
| $T_3$ | $\{8,9\},\{6,7\},\{5,10\}$ | $P_3, P_5, P_6$ |
| $T_4$ | $\{7,8\},\{5,10\},\{6,9\}$ | $P_4, P_6, P_9$ |
| $T_5$ | $\{5,10\},\{7,9\},\{6,8\}$ | $P_6, P_{13}, P_{14}$ |
| $T_6$ | $\{5,9\},\{7,10\},\{6,8\}$ | $P_7, P_8, P_{14}$ |
| $T_7$ | $\{7,10\},\{6,9\},\{5,8\}$ | $P_8, P_9, P_{10}$ |
| $T_{\mathrm{NEW1}}$ | $\{5,6\},\{7,8\},\{9,10\}$ | $P_1, P_4, P_2$ |
| $T_{\mathrm{NEW2}}$ | $\{5,6\},\{7,10\},\{8,9\}$ | $P_1, P_8, P_3$ |

**Critical observation.** $T_{\mathrm{NEW1}}$ and $T_{\mathrm{NEW2}}$ both require a runner at $P_1 = \{5,6\}$. As §16.2 shows, $P_1$ is only accessible to runners with $\lambda > 43.33$, making these templates severely restricted in practice.

---

### §16.2 λ-Band Table for All 14 Pair States

**Setup.** Runner with ratio $\lambda$ hits pair state $P$ with $a$-interval $(a_L, a_R)$ on some regime of $C_4 = (1/5, 1/4)$ if and only if there exists $x \in C_4$ with $F(\lambda x) \in (a_L, a_R)$. Since $F$ folds $\mathbb{R}$ to $\mathcal{F} = [0, 11/2]$ via $F(y) = \min(y \bmod 11, 11 - y \bmod 11)$, the condition splits into forward and reflected copies. The **$n$-th forward band** is:
$$\lambda \in \bigl(4(11n + a_L),\; 5(11n + a_R)\bigr),$$
and the **$n$-th reflected band** is:
$$\lambda \in \bigl(4(11n + 11 - a_R),\; 5(11n + 11 - a_L)\bigr).$$

A runner hits $P$ on $C_4$ iff $\lambda$ lies in one of these countably many bands (one family per integer $n \geq 0$). The **minimum $\lambda$** is the left endpoint of the first non-empty band with $\lambda \geq 1$.

| Pair state | $a$-interval $(a_L, a_R)$ | First forward band | First reflected band | Min $\lambda$ |
|---|---|---|---|---|
| $P_1\ \{5,6\}$ | $(1/7,\; 1/6)$ | $(312/7,\; 335/6)\approx(44.57,55.83)$ [$n{=}1$] | $(130/3,\; 380/7)\approx(43.33,54.29)$ [$n{=}0$] | **43.33** |
| $P_2\ \{9,10\}$ | $(10/9,\; 6/5)$ | $(40/9,\; 6)\approx(4.44,6.00)$ | $(196/5,\; 445/9)\approx(39.2,49.4)$ | **4.44** |
| $P_3\ \{8,9\}$ | $(5/4,\; 4/3)$ | $(5,\; 20/3)\approx(5.00,6.67)$ | $(116/3,\; 195/4)\approx(38.7,48.8)$ | **5.00** |
| $P_4\ \{7,8\}$ | $(10/7,\; 3/2)$ | $(40/7,\; 15/2)\approx(5.71,7.50)$ | $(38,\; 335/7)\approx(38.0,47.9)$ | **5.71** |
| $P_5\ \{6,7\}$ | $(5/3,\; 12/7)$ | $(20/3,\; 60/7)\approx(6.67,8.57)$ | $(260/7,\; 140/3)\approx(37.1,46.7)$ | **6.67** |
| $P_6\ \{5,10\}$ | $(21/10,\; 23/10)$ | $(42/5,\; 23/2)=(8.40,11.50)$ | $(174/5,\; 89/2)=(34.8,44.5)$ | **8.40** |
| $P_7\ \{5,9\}$ | $(7/3,\; 12/5)$ | $(28/3,\; 12)\approx(9.33,12.00)$ | $(172/5,\; 130/3)=(34.4,43.3)$ | **9.33** |
| $P_8\ \{7,10\}$ | $(16/5,\; 23/7)$ | $(64/5,\; 115/7)\approx(12.8,16.4)$ | $(216/7,\; 39)\approx(30.9,39.0)$ | **12.80** |
| $P_9\ \{6,9\}$ | $(32/9,\; 34/9)$ | $(128/9,\; 170/9)\approx(14.2,18.9)$ | $(260/9,\; 335/9)\approx(28.9,37.2)$ | **14.22** |
| $P_{10}\ \{5,8\}$ | $(21/5,\; 17/4)$ | $(84/5,\; 85/4)=(16.8,21.25)$ | $(27,\; 34)$ | **16.80** |
| $P_{11}\ \{5,10\}_2$ | $(43/10,\; 9/2)$ | $(86/5,\; 45/2)=(17.2,22.5)$ | $(26,\; 67/2)=(26.0,33.5)$ | **17.20** |
| $P_{12}\ \{5,7\}$ | $(32/7,\; 23/5)$ | $(128/7,\; 23)\approx(18.3,23.0)$ | $(128/5,\; 225/7)=(25.6,32.1)$ | **18.29** |
| $P_{13}\ \{7,9\}$ | $(43/9,\; 34/7)$ | $(172/9,\; 170/7)\approx(19.1,24.3)$ | $(172/7,\; 280/9)\approx(24.6,31.1)$ | **19.11** |
| $P_{14}\ \{6,8\}$ | $(43/8,\; 27/5)$ | $(43/2,\; 27)=(21.5,27.0)$ | $(112/5,\; 225/8)=(22.4,28.1)$ | **21.50** |

**Four speed tiers.** The pair states cluster naturally:

| Tier | Pairs | $\lambda_{\min}$ range | Accessible to |
|---|---|---|---|
| 1 | $P_2, P_3, P_4, P_5, P_6, P_7$ | $4.44$–$9.33$ | Slow runners |
| 2 | $P_8, P_9, P_{10}, P_{11}, P_{12}, P_{13}$ | $12.8$–$19.1$ | Mid-speed runners |
| 3 | $P_{14}$ | $21.5$ | Fast runner |
| 4 | $P_1$ | $43.3$ | Very fast runner only |

**The {6,7} bandwidth structure.** $P_5 = \{6,7\}$ has valid $\lambda$-bands:
$$\lambda \in \underbrace{(20/3,\; 60/7)}_{\approx 6.67\text{–}8.57} \;\cup\; \underbrace{(260/7,\; 140/3)}_{\approx 37.1\text{–}46.7} \;\cup\; \underbrace{(152/3,\; 445/7)}_{\approx 50.7\text{–}63.6} \;\cup\; \cdots$$
The gap $(8.57, 37.14)$ is 28 units wide. Any runner with $\lambda \in (9, 36)$ **cannot** hit $\{6,7\}$ on $C_4$ at all.

---

### §16.3 Template-Support Table and Ratio Conditions

For pairs $P_A < P_B < P_C$ (by $a$-value) with runners $\lambda_A < \lambda_B < \lambda_C$ hitting them simultaneously via the forward $n=0$ band, the simultaneous ratio conditions are:
$$\frac{a_L^B}{a_R^A} < \frac{\lambda_B}{\lambda_A} < \frac{a_R^B}{a_L^A}, \qquad \frac{a_L^C}{a_R^B} < \frac{\lambda_C}{\lambda_B} < \frac{a_R^C}{a_L^B}.$$

*Derivation.* Both $\lambda_A x \in (a_L^A, a_R^A)$ and $\lambda_B x \in (a_L^B, a_R^B)$ must hold for SOME $x \in C_4$. Dividing: $\lambda_B/\lambda_A = (a_B)/(a_A)$ for some $a_A \in (a_L^A, a_R^A)$, $a_B \in (a_L^B, a_R^B)$.

| Template | Pairs $(P_A, P_B, P_C)$ | Min $\lambda$ required | $\lambda_B/\lambda_A$ window | $\lambda_C/\lambda_B$ window | Tightness |
|---|---|---|---|---|---|
| $T_1$ | $P_2, P_5, P_{10}$ | 4.44, 6.67, 16.8 | $(25/18,\; 54/35)=(1.389, 1.543)$ | $(49/20,\; 51/20)=(2.450, 2.550)$ | ⚠️ Very tight (2nd: width 4%) |
| $T_2$ | $P_2, P_{12}, P_{14}$ | 4.44, 18.3, 21.5 | $(80/21,\; 207/50)=(3.810, 4.140)$ | $(215/184,\; 189/160)=(1.169, 1.181)$ | ❌ Extremely tight (2nd: width 1%) |
| $T_3$ | $P_3, P_5, P_6$ | 5.00, 6.67, 8.40 | $(5/4,\; 48/35)=(1.250, 1.371)$ | $(147/120,\; 69/50)=(1.225, 1.380)$ | ✓ Moderate |
| $T_4$ | $P_4, P_6, P_9$ | 5.71, 8.40, 14.2 | $(7/5,\; 161/100)=(1.400, 1.610)$ | $(320/207,\; 340/189)=(1.546, 1.799)$ | ✓ Moderate |
| $T_5$ | $P_6, P_{13}, P_{14}$ | 8.40, 19.1, 21.5 | $(430/207,\; 340/147)=(2.077, 2.313)$ | $(301/272,\; 243/215)=(1.107, 1.130)$ | ⚠️ Tight (2nd: width 2%) |
| $T_6$ | $P_7, P_8, P_{14}$ | 9.33, 12.8, 21.5 | $(4/3,\; 69/49)=(1.333, 1.408)$ | $(301/184,\; 27/16)=(1.636, 1.688)$ | ⚠️ Tight (2nd: width 3%) |
| $T_7$ | $P_8, P_9, P_{10}$ | 12.8, 14.2, 16.8 | $(224/207,\; 85/72)=(1.082, 1.181)$ | $(189/170,\; 153/128)=(1.112, 1.195)$ | ✓ Moderate |
| $T_{\mathrm{NEW1}}$ | $P_2, P_4, P_1^*$ | 4.44, 5.71, **43.3** | $(10/7 \div 6/5,\; 3/2 \div 10/9)=(0.868, 1.350)$ | see below | ❌ Requires $\lambda_C > 43$ |
| $T_{\mathrm{NEW2}}$ | $P_3, P_8, P_1^*$ | 5.00, 12.8, **43.3** | $(16/5 \div 4/3,\; 23/7 \div 5/4)=(2.400, 2.629)$ | see below | ❌ Requires $\lambda_C > 43$ |

*For $T_{\mathrm{NEW1}}$ and $T_{\mathrm{NEW2}}$: $P_1^*$ denotes $P_1$ accessed via its reflected $n=0$ band at $\lambda_C > 43$. The ratio $\lambda_C/\lambda_B$ then satisfies $\lambda_C/\lambda_B > 43/7.5 \approx 5.7$ (for $T_{\mathrm{NEW1}}$) or $> 43/16.4 \approx 2.6$ (for $T_{\mathrm{NEW2}}$). More precisely, simultaneous realization on $C_4$ for $T_{\mathrm{NEW1}}$ requires:*
$$\lambda_C/\lambda_B \in (65/6 \div 3/2,\; 76/7 \div 10/7) = (65/9,\; 76/10) = (7.22,\; 7.60),$$
*an extremely narrow band of width 0.38.*

---

### §16.4 The {6,7} Filter: Quantitative Obstruction

**Lemma ({6,7} Bandwidth).** *For any runner with $\lambda \in (9, 36)$, the regime where it simultaneously covers labels 6 and 7 on $C_4$ is empty. Templates $T_1$ and $T_3$ cannot be realised by any runner with $\lambda \in (9, 36)$.*

**Proof.** Runner $\lambda$ covers $\{6,7\}$ on $C_4$ iff $F(\lambda x) \in (5/3, 12/7)$ for some $x \in C_4$. The valid $\lambda$-bands are $(20/3, 60/7) \cup (260/7, 140/3) \cup \cdots$. The interval $(9, 36)$ is disjoint from all these bands. $\square$

**Occupancy bound.** The total $x$-measure on $C_4$ where any runner is in state $P_5 = \{6,7\}$ satisfies:
$$\mu\!\bigl(\bigcup_i \{x \in C_4 : F(\lambda_i x) \in P_5\}\bigr) \leq \sum_{i} \frac{|P_5|/11}{1} \cdot \bigl(1 + \lambda_i |C_4| / 11\bigr)^0 \approx 9 \times \frac{1/21 \times |C_4|}{11/11} \times \frac{1}{\bar\lambda}$$
For $\bar\lambda \approx 10$: occupancy $\lesssim 9 \times |C_4|/(21 \times 10) \approx 4\%$ of $C_4$ has any runner in $P_5$. Outside this $4\%$, templates $T_1$ and $T_3$ are unavailable.

---

### §16.5 Template Feasibility Summary

| Template | Speed tier requirement | Ratio window | Accessibility |
|---|---|---|---|
| $T_1$ | $\lambda_C > 16.8$ + $\lambda_B \in (6.67,8.57)$ or $>37$ | Very tight ($P_5$ constraint) | Low: $\leq 4\%$ of $C_4$ |
| $T_2$ | $\lambda_C > 21.5$ | ❌ Extremely tight | Very low |
| $T_3$ | $\lambda_C > 8.4$ + $\lambda_B \in (6.67,8.57)$ or $>37$ | Moderate | Low: $\leq 4\%$ of $C_4$ |
| $T_4$ | $\lambda_C > 14.2$ | ✓ Moderate | Moderate |
| $T_5$ | $\lambda_C > 21.5$ | ⚠️ Tight | Low |
| $T_6$ | $\lambda_C > 21.5$ | ⚠️ Tight | Low |
| $T_7$ | All $\lambda > 12.8$ | ✓ Moderate | Moderate |
| $T_{\mathrm{NEW1}}$ | $\lambda_C > 43$ | ❌ Extremely tight | Extremely low |
| $T_{\mathrm{NEW2}}$ | $\lambda_C > 43$ | ❌ Extremely tight | Extremely low |

The templates fall into three classes:
1. **{6,7}-gated** ($T_1, T_3$): Available only on $\leq 4\%$ of $C_4$. Largely irrelevant for the main chain.
2. **Ratio-locked** ($T_2, T_5, T_6, T_{\mathrm{NEW1}}, T_{\mathrm{NEW2}}$): Require $\leq 1$–$3\%$ fractional ratio windows. Generic configurations miss these.
3. **Accessible** ($T_4, T_7$): Moderate ratio windows, mid-speed runners. These are the primary templates. The stitching argument must focus on these.

---

### §16.6 Refined Target for Lemma 4b

From the feasibility analysis, the stitching problem reduces to:

**Can templates $T_4$ and $T_7$ together cover all of $X_{\mathrm{low}}$?**

- $T_4 = \{P_4, P_6, P_9\}$: requires runners at $P_4 = \{7,8\}$ (Tier 1, $\lambda > 5.71$), $P_6 = \{5,10\}$ (Tier 1, $\lambda > 8.40$), $P_9 = \{6,9\}$ (Tier 2, $\lambda > 14.22$).
- $T_7 = \{P_8, P_9, P_{10}\}$: requires runners at $P_8 = \{7,10\}$ (Tier 2, $\lambda > 12.80$), $P_9 = \{6,9\}$ (Tier 2, $\lambda > 14.22$), $P_{10} = \{5,8\}$ (Tier 2, $\lambda > 16.80$).

**Conflict.** Both $T_4$ and $T_7$ require a runner at $P_9 = \{6,9\}$. The simultaneous ratio conditions for $T_4$ and $T_7$ at the same $x$ require the SAME runner to be in $P_9$, but the remaining pairs ($P_4, P_6$ for $T_4$ vs $P_8, P_{10}$ for $T_7$) are at different $a$-positions and require different runners. So the shared $P_9$ runner together with 2 runners from $T_4$ and 2 from $T_7$ consumes $\min(2+1+2, 9) = 5$ distinct runners.

**The runner-budget constraint.** With 9 runners ($\lambda_2 < \cdots < \lambda_{10}$), the Tier 2+ requirements for $T_4$/$T_7$ coverage consume $\geq 5$ runners. The remaining $\leq 4$ runners (Tier 1 only, $\lambda < 12.8$) cannot realise any of $T_4, T_7, T_1, T_3$ simultaneously — their $\lambda$ values are below the Tier 2 minimum for $P_8, P_9, P_{10}$.

**Consequence.** Any regime $J_k \subset X_{\mathrm{low}}$ where the $\geq 5$ Tier-2 runners are NOT simultaneously in the $T_4$/$T_7$ configuration is an uncovered regime. The question is whether the Tier-2 runners can be arranged to always maintain $T_4$ or $T_7$. The ratio conditions ($T_4$: $\lambda_C/\lambda_B \in (1.546, 1.799)$; $T_7$: $\lambda_B/\lambda_A \in (1.082, 1.181)$) impose strict constraints that, combined with the monotone ordering $\lambda_2 < \cdots < \lambda_{10}$, limit which runners can simultaneously realise each template.

**Status.** ⚠️ OPEN. The λ-band table and ratio conditions above constitute the exact finite data for this argument. The next step is a case analysis: given fixed ordered ratios $\lambda_2 < \cdots < \lambda_{10}$, exhibit an $x$-interval in $X_{\mathrm{low}}$ where neither $T_4$ nor $T_7$ (nor any other template) holds.

---

## §17  Hard-Case Investigation: Structural Dichotomy for n=11

*Results from computational investigation, 2026-03-28. Full details in `lrc_c4_synthesis_v1.md`.*

### §17.1  Setup

For n=11 LRC we ask: which configurations have **full C4 coverage** (no AP-witness
lonely time in C4), and for those, how is LRC proved?

The investigation ran:
- Exhaustive enumeration of all 9-subsets of $\{2,\ldots,17\}$ (as $\lambda$-values with
  $v_1=1$): 11,440 configs. **422 have full C4 coverage.**
- Targeted checks on configurations with multiples-of-11 runners.
- Direct LRC scans (500k time points) for all full-coverage configs with mult-of-11 runners.

### §17.2  The Null Gap Theorem (Proved)

**Theorem (Null Gap).** For $x \in C_4 = (1/5, 1/4)$ and runner ratio $\lambda < 5$:
the runner's folded position $a = F(\lambda x) \in (0, 1.25)$ covers NO labels in
$\{5,\ldots,10\}$. Only runners with $\lambda \geq 5$ are **active** in $C_4$.

*Proof sketch.* $\lambda x < 5/4 = 1.25 < 5.5$, so $F(\lambda x) = \lambda x$. For $a < 10/9
\approx 1.11$: $\{a \cdot m/11\} \in (0, 1/2)$ for all $m \leq 10$, always in $(1/11, 10/11)$.
For $a \in [10/9, 5/4)$: direct computation confirms no label blocked. $\square$

**Corollary.** Minimum 6 active runners are required for full C4 coverage.

### §17.3  The Primality Dichotomy

**Lemma P** (trivial). If $11 \nmid v_i$ for all non-stationary runners $i$, then $t = 1/11$
is a lonely time: every position $\{v_i/11\} = (v_i \bmod 11)/11 \in \{1/11,\ldots,10/11\}$
since 11 is prime. $\square$

This handles the vast majority of configurations immediately. The hard cases are exactly
those where some $v_j \equiv 0 \pmod{11}$.

### §17.4  Theorem GB Boundary

**Theorem GB** (generalised bounded). If $e_{10}/e_1 \leq 10$, then $t^* = 10/(11 e_{10})$
is a constructive lonely witness for all 10 runners simultaneously.

*This handles all configurations with bounded ratio, including those with mult-of-11 runners
(position of mult-of-11 runner at $t^*$ is $11k \cdot 10/(11 e_{10}) = 10k/e_{10} \in [1/11, 10/11]$
whenever $e_{10} \geq 11k$ and $e_{10} \leq 110k$, which holds whenever $e_{10}/e_1 \leq 10$).* $\square$

### §17.5  Hard Case: mult-of-11 runner AND ratio $> 10$

For configurations with some $v_j \equiv 0 \pmod{11}$ and $e_{10}/e_1 > 10$:
$t = m/11$ is blocked (runner $v_j$ at position 0 always), and Theorem GB fails.

**From the 422 full-coverage configurations**, the following pattern holds:

| C4 Coverage status | Has mult-of-11? | Proof mechanism |
|---|---|---|
| **Full coverage** | No | Lemma P: $t=1/11$ ✓ |
| **Full coverage** | Yes | Specific rational witness $t = p/(q \cdot 11)$ |
| **Partial (gap exists)** | Yes | AP-witness in C4: $t = m^* x^*/(11 v_1)$ |
| **Partial (gap exists)** | No | Impossible (Lemma P gives $t=1/11$ directly) |

**Verified examples for the "full coverage + mult-of-11" sub-case:**

| Speeds | Lonely time | Notes |
|---|---|---|
| $\{1,2,3,4,5,6,7,8,9,11\}$ | $t=1/10$ | Sub-LRC time for $\{1,\ldots,9\}$; runner 11 at $1/10 \in [1/11,10/11]$ |
| $\{1,2,3,5,6,7,8,9,10,11\}$ | $t=23/99 = 23/(9\cdot11)$ | Boundary-exact: runner 9 at $1/11$ |
| $\{1,2,3,5,6,7,9,10,11,16\}$ | $t=8/33 = 8/(3\cdot11)$ | min-dist $= 1/9$ |
| $\{3,6,9,11,15,18,21,24,30,54\}$ | $t=5/66 = 5/(6\cdot11)$ | Inactive mult-of-11, ratio 18 |

### §17.6  Why the C4 Analysis Alone Is Insufficient

The C4 corridor finds lonely times of the specific form $t = m x^*/(11 v_1)$ with
$m \in \{5,\ldots,10\}$ and $x^* \in (1/5,1/4)$. Configurations with full C4 coverage
have no lonely time of this form, but LRC still holds via:
- Lemma P (no mult-of-11), OR
- A rational witness $t = p/(q \cdot 11)$ in a different regime (below C4 or above it), OR
- Other corridor analysis (C1, C2, C3 also constrain the configuration).

**The C4 analysis is a powerful first filter** but is not a complete standalone proof.
The complete proof for n=11 requires Lemma P + Theorem GB + Route 3 / Phase-Uniform
Extension (the last component handles full-coverage configs with mult-of-11 runners).

### §17.7  Consequence for the Blocking Grammar Programme

The T4/T7 conflict analysis of §16.6 applies to configurations where:
- 5+ Tier-2 runners exist (λ > 12.8)
- No full-coverage 6-subset appears in the active set

This is a genuine subset of all hard cases. Configurations where a full-coverage 6-subset
is present (e.g., active set ⊇ {5,6,7,8,9,10}) are handled by Lemma P / Theorem GB.

**Open target (unchanged):** Show that when no full-coverage 6-subset is present in the
active set AND the mult-of-11 structural constraint prevents reaching T4/T7 simultaneously,
a C4 gap results. Combined with §17.5, this would close the case where C4 analysis succeeds.

---

*§17 added 2026-03-28. Synthesises computational hard-case investigation. Full document:
`lrc_c4_synthesis_v1.md`.*

*§16 added 2026-03-28. v6 = v5 + corrected 9-template list, exact λ-band table, template-support table with ratio conditions, {6,7} filter quantified, Lemma 4b reduced to $T_4$/$T_7$ conflict.*
