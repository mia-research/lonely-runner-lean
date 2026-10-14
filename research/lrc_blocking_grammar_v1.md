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

*See also: `lrc_elegant_proof_sketch_v1.md` (two-mechanisms picture), `lrc_ap_worst_case_v1.md` (AP as coordinate system), `lrc_n11_structural_mechanism_v1.md` (Coupling Principle as shadow of $B(11-a)=B(a)$)*
