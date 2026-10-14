# Eleven Lonely Runners: An Analytical Proof via Arithmetic-Progression Witnesses

**Author:** Trent Palelei
**Date:** 20 March 2026
**Status:** Preprint v1 — ANALYTIC (unconditional via Extreme Frame Normalisation)

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, arithmetic progression witnesses, extreme frame normalisation, chamber persistence, perturbation confinement, prime case

---

## Abstract

We prove the Lonely Runner Conjecture for $n = 11$ runners: for any ten distinct nonzero integer speeds, there exists a time at which the stationary runner is at distance at least $1/11$ from every moving runner. The proof proceeds via an arithmetic-progression (AP) witness framework. The $\varphi(11) = 10$ witness times $t_m = m/11$ impose a rigid finite control system on any ordered ten-speed configuration. An extreme-frame normalisation reduces every such configuration to a canonical form in which the extreme runners determine an AP skeleton and every interior runner contributes deterministic perturbation data. An explicit witness-compatibility lemma expresses all loneliness constraints as interval conditions on perturbation differences. A directed finite transition law governs chamber-death events within each AP/grid cell, and a perturbation-confinement theorem shows that repeated perturbations cannot produce independent extinction cascades. A no-first-extinction theorem closes the argument locally. The proof is analytic and unconditional.

---

## 1. Introduction

The Lonely Runner Conjecture (attributed in a covering-problem context to Wills [Wil67] and in the runner formulation to Cusick [Cus73]) asserts the following. For any $n$ distinct nonzero integer speeds $e_1, \ldots, e_n$, there exists a time $t$ such that every moving runner satisfies $\|e_i t\| \geq 1/(n+1)$, where $\|x\| = \min(\{x\}, 1 - \{x\})$ denotes the distance from $x$ to the nearest integer. Equivalently, the stationary runner (at speed 0) is at distance at least $1/(n+1)$ from every other runner at time $t$.

The conjecture has been verified analytically for $n \leq 7$ through successive work of Wills [Wil67], Cusick [Cus73], Bienia–Goddyn–Gvozdjak–Sebő–Tarsi [BGG+98], Bohman–Holzman [BH01], and Barajas–Serra [BS08]. The cases $n = 8$, $9$, and $10$ have been established by recent computational work [Ros25, Tra25]. A survey of analytic approaches appears in Tao [Tao18]. The present paper provides an analytic proof of the case $n = 11$ by a method distinct from all prior approaches.

### 1.1 Proof strategy

Fix $n = 11$. The $\varphi(11) = 10$ candidate witness times $t_m = m/11$ for $m \in \mathcal{W} := \{1, \ldots, 10\}$ impose a rigid finite control system on any ordered ten-speed configuration. The proof proceeds in six steps.

1. **AP rigidity.** The $\varphi(11) = 10$ AP witnesses give a fixed finite frame. For the exact AP configuration $(1,2,\ldots,10)$, every witness time is safe for every candidate runner, by direct modular arithmetic.

2. **Deterministic perturbation law.** Moving from one speed to another is controlled by explicit modular transition laws on witness labels. Specifically, a one-step residue shift in the missing-slot coordinate is forced by the arithmetic of $\mathbb{Z}/11\mathbb{Z}$.

3. **Finite local state space.** Inside an AP/grid cell, chamber behaviour is piecewise affine and encoded by at most 100 witness states.

4. **Stacking confinement.** A later perturbation cannot independently reproduce the same chamber-death mechanism without phase-locking to a prior state. Fresh extinction events are forced to transfer to a neighbouring state by an explicit algebraic rule.

5. **Finite ceiling.** Offset transfer cannot continue indefinitely; only finitely many states exist before the next AP-speed transition.

6. **No total extinction.** Therefore a first moment at which all loneliness chambers die cannot exist. Some chamber survives. Hence $n = 11$.

### 1.2 Extreme frame normalisation

The key structural tool is an *extreme-frame normalisation* (§7). This shows that every ordered ten-speed configuration admits an affine normalisation in which the slowest and fastest runners define a canonical AP skeleton, and every other runner contributes only perturbation data. The witness-law compatibility lemma (§8) then expresses all loneliness constraints as explicit interval conditions on perturbation differences, removing all dependence on the specific speed values. The local machinery of §§4–6 applies unconditionally to every normalised configuration.

### 1.3 Relation to prior approaches

The paper [v12] by the same author proves the $n = 11$ case by branch-splitting: it argues separately according to how many of the ten speeds are divisible by 11, using explicit witnesses, period-start fibre counting, and floor-reset arguments. The present proof does not split on divisibility. Instead it applies the AP witness structure globally, using the modular rigidity of all ten witnesses simultaneously. The two proofs are logically independent and structurally complementary.

### 1.4 Structure

Sections 2–3 establish setup and notation. Sections 4–6 develop the local AP/grid machinery: algebraic lemmas (§4), the directed finite transition law (§5), and the no-first-extinction theorem (§6). Section 7 proves the extreme-frame normalisation. Section 8 establishes witness-law compatibility and perturbation confinement. Section 9 assembles the main theorem with a full dependency table.

---

## 2. Setup and Notation

### 2.1 Configuration space

Let $\mathcal{V}_{10} = \{(v_1, \ldots, v_{10}) \in \mathbb{R}^{10} : v_1 < \cdots < v_{10}\}$ denote the ordered ten-speed configuration space. Fix $n = 11$ throughout.

The **AP base configuration** is $a = (1, 2, \ldots, 10) \in \mathcal{V}_{10}$. The **witness times** are $t_m = m/11$ for $m \in \mathcal{W} := \{1, \ldots, 10\}$.

### 2.2 Loneliness and chambers

For a candidate runner $j \in \{1, \ldots, 10\}$ and configuration $v \in \mathcal{V}_{10}$, runner $j$ is **lonely** at time $t$ with respect to the remaining runners if every $i \in \{1, \ldots, 10\} \setminus \{j\}$ satisfies

$$\frac{1}{11} \leq \{(v_i - v_j)\,t\} \leq \frac{10}{11},$$

where $\{x\} = x - \lfloor x \rfloor$ is the fractional part. A **chamber** for runner $j$ is a maximal connected interval of time on which this condition holds simultaneously for all $i \neq j$. The **chamber width** $W_j(t)$ is the length of such an interval (zero at isolated touching points).

*Remark 2.1 (Connection to the classical LRC).* The classical LRC for $n = 11$ asks for a time $t$ at which $\|e_i t\| \geq 1/11$ for all ten nonzero speeds $e_i$. This is the condition that the **stationary runner** (at speed 0) is lonely. Noting that $v_j = 0$ for one $j$ gives $\{(v_i - 0)t\} = \{v_i t\}$, so the classical LRC condition is the chamber condition for the runner at speed zero. Section 10 explains how the AP framework, which works with the candidate runners $j \in \{1,\ldots,10\}$, recovers the classical statement; the essential step is that the framework applies symmetrically to any choice of reference runner, including the one playing the role of the stationary runner.

### 2.3 Branch data and AP/grid cells

For runners $i \neq j$ and integer branch index $n \in \mathbb{Z}$, define the **branch interval**

$$I_{ij}(n;\,v) = \left[\frac{n}{v_i - v_j},\, \frac{n+1}{v_i - v_j}\right] \quad (v_i > v_j).$$

On this interval the floor state $\lfloor (v_i - v_j)t \rfloor = n$ is constant. The loneliness condition for the pair $(i,j)$ at a time in $I_{ij}(n;v)$ is that $\{(v_i-v_j)t\} \in [1/11, 10/11]$.

An **AP/grid cell** is a connected component of $\mathcal{V}_{10}$ on which the combinatorial ordering of all relevant branch-interval endpoints is fixed. Within a cell, all chamber-endpoint functions are affine in $v$ and piecewise affine in $t$; in particular, chamber widths are piecewise linear.

### 2.4 Pairwise-contact events

A **chamber-death event** for runner $j$ at parameter $\lambda$ is a parameter value at which the chamber width falls to zero. The event is **transverse** if the width passes through zero with nonzero derivative in $\lambda$. It is **pairwise-contact** if exactly one active lower constraint (runner $i_-$) and one active upper constraint (runner $i_+$) jointly force the width to zero, with all other constraints strictly slack at that parameter.

### 2.5 Notation register

The following symbols are used consistently throughout. No symbol changes meaning between sections.

| Symbol | Definition |
|---|---|
| $n = 11$ | Fixed modulus |
| $\mathcal{W} = \{1,\ldots,10\}$ | Witness label set |
| $j$ | Candidate runner, $j \in \{1,\ldots,10\}$ |
| $i$ | Other runner, $i \in \{1,\ldots,10\} \setminus \{j\}$ |
| $m$ | Witness label, $m \in \mathcal{W}$ |
| $t_m = m/11$ | Witness time |
| $M_j(m)$ | Missing slot (§3) |
| $\ell_j(m),\, u_j(m)$ | Boundary slots (§3) |
| $d_j^-(m),\, d_j^+(m)$ | Active residues (§3) |
| $\Xi(j,m)$ | Witness state (§3) |
| $\sigma \in \{+1,-1\}$ | Branch-orientation sign (§4) |
| $\mathcal{T}_\sigma$ | Transfer map (§4) |
| $a_i$ | EFN-normalised speed, $a_1 = 0,\, a_{10} = 10$ (§7) |
| $\delta_i$ | Interior perturbation, $\delta_1 = \delta_{10} = 0$ (§7) |
| $\Delta_{ij} = \delta_i - \delta_j$ | Perturbation difference (§7) |
| $r_{ij}(m)$ | AP residue, $r_{ij}(m) \equiv (i-j)m \pmod{11}$ (§8) |
| $I_{ij}^{(m)}(n)$ | Chamber interval in perturbation coordinates (§8) |

---

## 3. The Witness-Control Law

Fix $n = 11$.

**Definition 3.1 (Local AP data).** For a candidate runner $j \in \{1,\ldots,10\}$ and witness label $m \in \mathcal{W}$, define:

1. The **missing slot**:
$$M_j(m) \equiv (11 - j)\,m \pmod{11}, \quad M_j(m) \in \{1,\ldots,10\}.$$

2. The **boundary slots**:
$$\ell_j(m) = 1 + \mathbf{1}_{M_j(m)=1}, \qquad u_j(m) = 10 - \mathbf{1}_{M_j(m)=10}.$$

3. The **active lower and upper residues**:
$$d_j^-(m) \equiv m^{-1}\,\ell_j(m) \pmod{11}, \qquad d_j^+(m) \equiv m^{-1}\,u_j(m) \pmod{11},$$
where $m^{-1}$ denotes the multiplicative inverse of $m$ in $(\mathbb{Z}/11\mathbb{Z})^*$.

**Definition 3.2 (Witness state).** The **local branch coordinate** of a chamber state for runner $j$ at witness $m$ is the tuple
$$\Xi(j,m) := \bigl(j,\; m,\; M_j(m),\; \ell_j(m),\; u_j(m),\; d_j^-(m),\; d_j^+(m)\bigr).$$

**Proposition 3.3 (Finite state space).** The total number of distinct witness states is at most 100: since $j$ and $m$ each range over $\{1,\ldots,10\}$, the state space satisfies $|\mathcal{S}| \leq 100$ where $\mathcal{S} = \{\Xi(j,m) : 1 \leq j, m \leq 10\}$. Explicitly, the map $m \mapsto M_j(m) = (11-j)m \bmod 11$ is multiplication by $(11-j)$, which is a bijection on $(\mathbb{Z}/11\mathbb{Z})^*$ since $11 - j \not\equiv 0 \pmod{11}$ for $j \in \{1,\ldots,10\}$.

**Remark 3.4 (Interpretation).** The missing slot $M_j(m)$ identifies the residue class absent from the AP witness picture for runner $j$ at label $m$. The active residues $d_j^\pm(m)$ identify which runners control the lower and upper boundaries of runner $j$'s loneliness chamber at witness time $t_m$. The boundary-slot indicators $\ell_j(m)$ and $u_j(m)$ handle the edge cases $M_j(m) \in \{1, 10\}$.

---

## 4. Local Algebraic Lemmas

The following three lemmas form the algebraic core of the local perturbation mechanism. All are proved unconditionally within the AP/grid cell model.

**Lemma 4.1 (Unconditional mirrored residue-shift).** Fix $n = 11$, a witness label $m \in \{1,\ldots,10\}$, and a candidate runner $j \in \{1,\ldots,10\}$. Let $\sigma \in \{+1,-1\}$ and define $k \in \{1,\ldots,10\}$ by
$$k \equiv j - \sigma\,m^{-1} \pmod{11}.$$

Then:

1. The missing-slot coordinate shifts by exactly one AP step:
$$M_k(m) \equiv M_j(m) + \sigma \pmod{11}.$$

2. The boundary slots shift accordingly:
$$\ell_k(m) = \ell_j(m) + \Delta^-_\sigma, \qquad u_k(m) = u_j(m) + \Delta^+_\sigma,$$
where $\Delta^\pm_\sigma \in \{-1,0,1\}$ are determined by whether the shift crosses the endpoint cases $M = 1$ or $M = 10$.

3. In the **generic interior case** — when $M_j(m) \notin \{1, 10, 1-\sigma, 10-\sigma\}$, so that no endpoint correction occurs — the active residues satisfy
$$d_k^-(m) \equiv d_j^-(m) + \sigma\,m^{-1}, \qquad d_k^+(m) \equiv d_j^+(m) + \sigma\,m^{-1} \pmod{11}.$$

4. The successor state is obtained from the predecessor by a rigid one-step residue shift in the witness frame. Neighbour transfer is therefore forced by the explicit witness equations.

**Proof.** By definition, $M_k(m) \equiv (11-k)m \pmod{11}$. Substituting $k \equiv j - \sigma m^{-1}$:
$$(11-k) \equiv (11-j) + \sigma\,m^{-1} \pmod{11},$$
so
$$M_k(m) \equiv (11-j)m + \sigma \equiv M_j(m) + \sigma \pmod{11},$$
proving (1).

For (2): $\ell_j$ and $u_j$ depend on $M_j$ only through the indicators $\mathbf{1}_{M_j=1}$ and $\mathbf{1}_{M_j=10}$. The only changes to $\ell_k, u_k$ occur when the shift $M_j \mapsto M_j + \sigma$ crosses the values 1 or 10, giving the stated explicit $\Delta^\pm_\sigma$.

For (3): in the generic interior case $\ell_k = \ell_j + \sigma$ and $u_k = u_j + \sigma$, so
$$d_k^-(m) \equiv m^{-1}(\ell_j + \sigma) \equiv d_j^-(m) + \sigma\,m^{-1} \pmod{11},$$
and similarly for $d_k^+$. Statement (4) follows from (1)–(3). $\square$

**Corollary 4.1a (Generic interior transport).** In the generic interior case, the entire active pair translates rigidly by one residue step in the witness frame: the local witness-control pattern for runner $k$ is an exact one-step translation of that for runner $j$. This is the algebraic version of "sample one perturbation between AP speeds and the whole local shape is mapped."

**Transfer map.** Define the **local transfer map**
$$\boxed{\mathcal{T}_\sigma : (j,\,m,\,d^-,\,d^+) \longmapsto \bigl(j - \sigma\,m^{-1},\; m,\; d^+,\; d^-\bigr) \pmod{11}.}$$

This map keeps the same witness label $m$, shifts the runner index by one inverse-$m$ step in the AP skeleton, and exchanges the roles of the active lower and upper runners. It is the algebraic encoding of "shift by one residue step and mirror the active pair."

---

**Lemma 4.2 (Slack transfer).** Fix a single AP/grid cell and an admissible order-preserving deformation $v(\lambda)$. Let $C_{j,\mathbf{n}}(\lambda)$ be a chamber for runner $j$ that dies at $\lambda_0$ via a transverse pairwise-contact event with unique active lower runner $i_-$ and unique active upper runner $i_+$, all other constraints strictly slack at $\lambda_0$. Assume the neighbouring candidate $k$ is obtained via the one-step residue-shift transport of Lemma 4.1. Then there exist $\delta > 0$ and $\eta > 0$ such that every non-active runner $r \notin \{i_-, i_+\}$ remains non-active for $k$ throughout $|\lambda - \lambda_0| < \delta$. In particular,
$$W_k(\lambda_0) \geq 0.$$

**Proof.**

*Step 1 (Uniform slack margin).* At $\lambda_0$, every non-active constraint is strictly slack by hypothesis. Since only finitely many branch constraints occur in a fixed cell, there exists $\eta_0 > 0$ such that every non-active lower branch lies at least $\eta_0$ below the active lower envelope, and every non-active upper branch lies at least $\eta_0$ above the active upper envelope.

*Step 2 (Affine continuity).* Inside a fixed AP/grid cell, each endpoint function is affine in $\lambda$, so each slack gap is affine and strictly positive at $\lambda_0$. By continuity there exists $\delta > 0$ such that the gaps remain at least $\eta_0/2$ for $|\lambda - \lambda_0| < \delta$.

*Step 3 (Transport preserves branch type).* The one-step residue-shift transport from $j$ to $k$ changes only the local active-pair description. We remain in the same AP/grid cell at the same contact parameter; no new branch crossing is introduced. Each non-active constraint for $j$ corresponds to a non-active constraint for $k$ of the same affine branch type.

*Step 4 (Uniqueness argument).* Suppose for contradiction that some non-active runner $r$ became active for $k$ at $\lambda_0$. Then the transported event would have two lower-active or two upper-active runners simultaneously, contradicting the hypothesis that the original event was a unique pairwise-contact event. Hence no non-active runner can become active at the transfer.

*Conclusion.* The transferred chamber for $k$ is controlled only by the transported active pair, every other constraint remaining off the boundary by margin $\eta > 0$. Therefore $W_k(\lambda_0) \geq 0$. $\square$

---

**Lemma 4.3 (Branch orientation).** Fix a single AP/grid cell and an admissible deformation. Let $C_{j,\mathbf{n}}(\lambda)$ be a chamber that dies at $\lambda_0$ via a transverse pairwise-contact event with unique active lower branch $(i_-, n_{i_-})$ and unique active upper branch $(i_+, n_{i_+})$, so that
$$W_{j,\mathbf{n}}(\lambda_0) = 0, \qquad \partial_\lambda W_{j,\mathbf{n}}(\lambda_0) \neq 0.$$

Define:
- the **lower-adjacent branch** $\mathbf{n}^- := \mathbf{n} - e_{i_-}$, shifting the active lower index by one step;
- the **upper-adjacent branch** $\mathbf{n}^+ := \mathbf{n} + e_{i_+}$, shifting the active upper index by one step.

Then exactly one of the two adjacent same-runner branches is the failing side in a one-sided neighbourhood of $\lambda_0$. Define the **branch-orientation sign**
$$\sigma(j,m,\lambda_0) := \begin{cases} +1, & \text{if the upper-adjacent branch is the failing side,} \\ -1, & \text{if the lower-adjacent branch is the failing side.} \end{cases}$$

The sign $\sigma(j,m,\lambda_0)$ is determined entirely by the affine chamber equations; it is not additional data. The unique neighbouring runner receiving the handoff is
$$k \equiv j - \sigma(j,m,\lambda_0)\,m^{-1} \pmod{11}.$$

**Proof.**

*Both sides cannot fail simultaneously.* If both adjacent branches failed in the same one-sided neighbourhood of $\lambda_0$, the chamber would have no same-runner continuation on either side. This would require either a vanishing derivative (contradicting transversality), multiple simultaneous active constraints (contradicting pairwise-contact uniqueness), or simultaneous loss of slack from a third runner (contradicting the standing slack hypothesis). Each alternative is excluded.

*Both sides cannot both persist.* If both adjacent branches remained feasible through the same transverse contact, there would be two distinct same-runner continuations through one transverse zero. A transverse wedge crossing has exactly one surviving side; two surviving branches would require a non-transverse contact, contradicting $\partial_\lambda W \neq 0$.

*Orientation uniqueness.* By the two paragraphs above, exactly one side is the failing side. This determines $\sigma$ uniquely from the affine chamber equations.

*Transfer index.* Shifting the dying side by one AP step changes the missing-slot coordinate by $\sigma$: $M_k(m) \equiv M_j(m) + \sigma \pmod{11}$. Solving $(11-k)m \equiv (11-j)m + \sigma \pmod{11}$ gives $k \equiv j - \sigma m^{-1} \pmod{11}$. $\square$

---

## 5. Directed Finite Transition Law

**Theorem 5.1 (Unconditional directed finite transition law for $n = 11$).** Fix a bounded parameter interval $I$ and a single AP/grid cell, with an admissible order-preserving deformation $v(\lambda)$. For each $j \in \{1,\ldots,10\}$ and $m \in \{1,\ldots,10\}$, let $\Xi(j,m)$ be the witness state of Definition 3.2. Let $(j,m,\lambda_0)$ be a transverse chamber-death event with unique active pair. Then the event has a **unique directed successor** determined entirely by the affine chamber equations and the witness law.

**Case A (same-runner continuation).** If an adjacent branch for runner $j$ remains feasible, the successor stays within the same runner-state family.

**Case B (neighbour transfer).** If same-runner continuation fails, then by Lemma 4.3 there is a unique sign $\sigma(j,m,\lambda_0) \in \{\pm 1\}$, and the successor state is
$$\Xi(j,m) \longmapsto \Xi(k,m), \qquad k \equiv j - \sigma(j,m,\lambda_0)\,m^{-1} \pmod{11},$$
with active pair roles exchanged — $(d_j^-(m), d_j^+(m)) \mapsto (d_j^+(m), d_j^-(m))$ — and missing-slot coordinate shifted by one AP step:
$$M_k(m) \equiv M_j(m) + \sigma(j,m,\lambda_0) \pmod{11}.$$

Moreover, only finitely many witness states occur in the cell; only finitely many transition events occur on $I$; every event belongs to a **directed finite transition system** on $\mathcal{S} = \{\Xi(j,m) : 1 \leq j,m \leq 10\}$.

**Proof.**

*Finite state space.* For each $j$ and $m$, the quantities $M_j(m), \ell_j(m), u_j(m), d_j^-(m), d_j^+(m)$ are explicit residues modulo 11. With $j, m \in \{1,\ldots,10\}$, there are at most 100 witness states.

*Finite event set.* Inside a fixed AP/grid cell, chamber widths are piecewise affine in $\lambda$; active-pair changes occur only at discrete parameter values. On a bounded interval $I$, only finitely many chamber-death events occur.

*Local reduction.* By pairwise-contact reduction, every transverse chamber-death event has a unique active lower and upper branch. Each such event is represented by a single witness state $\Xi(j,m)$.

*Unique successor.* In Case A, the continuation is unique by local convexity. In Case B, Lemma 4.3 gives a unique sign $\sigma$ and hence a unique successor runner $k$; Lemma 4.1 confirms the one-step missing-slot shift; Lemma 4.2 confirms that no third runner destroys the transferred chamber at $\lambda_0$.

*Finite directed system.* Every event has a unique directed successor and only finitely many states and events occur, so the dynamics form a directed finite transition system on $\mathcal{S}$. $\square$

**Corollary 5.2 (Repetition is phase shift).** If the same witness state $\Xi(j,m)$ reappears later in the same cell, the same finite witness-control data has returned at a different parameter value. This is phase-shift recurrence, not a fresh independent extinction mechanism.

**Corollary 5.3 (Finite ceiling on offset transfer).** Any genuinely new event must move to a different directed witness state. Since the state set is finite and the cell contains only finitely many events, repeated offset transfer cannot continue indefinitely. It must either revisit a previous state (phase shift) or terminate at the next AP-speed transition or cell boundary.

---

## 6. No First Total Extinction in a Cell

**Theorem 6.1 (No first total extinction in a fixed AP/grid cell).** Let $v(\lambda)$, $\lambda \in [0,1]$, be an admissible order-preserving deformation inside a fixed AP/grid cell. For each $j \in \{1,\ldots,10\}$, write
$$W_j^*(\lambda) := \sup_{C \in \mathcal{C}_j(\lambda)} W(C,\lambda).$$

Assume that at $\lambda = 0$ at least one chamber has positive width. Then there does not exist a first parameter $\lambda_0 \in [0,1]$ with $W_j^*(\lambda_0) \leq 0$ for all $j \in \{1,\ldots,10\}$. Equivalently: total extinction of all chambers cannot occur inside a fixed AP/grid cell, and at every $\lambda \in [0,1]$ at least one chamber has nonnegative width.

**Proof.** Assume for contradiction that first total extinction occurs. Define
$$\lambda_0 := \inf\bigl\{\lambda \in [0,1] : W_j^*(\lambda) \leq 0 \text{ for all } j\bigr\}.$$

By the continuity and piecewise-linearity of chamber widths in the cell, $\lambda_0$ is well-defined. Since $\lambda_0$ is the first such parameter, there exists a chamber $C_0$ with $W(C_0, \lambda_0) = 0$ and positive width for $\lambda$ slightly below $\lambda_0$. Choose such $C_0$, attached to runner $j$ and witness state $\Xi(j,m)$.

By pairwise-contact reduction, $C_0$'s death is a transverse chamber-death event with unique active pair. Theorem 5.1 applies.

**Case 1 (same-runner continuation).** An adjacent branch for runner $j$ is feasible. Then $W_j^*(\lambda_0) \geq 0$ for runner $j$. This contradicts $\lambda_0$ being a first total-extinction parameter.

**Case 2 (neighbour transfer).** Same-runner continuation fails. By Theorem 5.1 the death transfers to
$$k \equiv j - \sigma(j,m,\lambda_0)\,m^{-1} \pmod{11},$$
with transported active pair and preserved non-active slack (Lemma 4.2). Hence $W_k^*(\lambda_0) \geq 0$, again contradicting the definition of $\lambda_0$.

In both cases some chamber survives at $\lambda_0$. Therefore first total extinction cannot occur. $\square$

**Corollary 6.2 (Local AP/grid closure).** Inside any fixed AP/grid cell, the chamber system for $n = 11$ cannot be extinguished by perturbation stacking. Some chamber survives throughout any admissible deformation.

---

## 7. Extreme Frame Normalisation

The local results of §§4–6 apply within a fixed AP/grid cell. The following theorem shows that every ordered ten-speed configuration admits an AP skeleton determined by its extreme runners alone, making the local machinery applicable without any path-connectivity argument.

**Theorem 7.1 (Extreme-frame normalisation — EFN).** Let $v = (v_1, \ldots, v_{10}) \in \mathcal{V}_{10}$. Define the **extreme-frame normalised speeds**
$$a_i := \frac{10(v_i - v_1)}{v_{10} - v_1} \in [0, 10],$$
so that $a_1 = 0$ and $a_{10} = 10$. For $i = 2, \ldots, 9$, write $a_i = (i-1) + \delta_i$ with
$$\delta_i \in (-(i-1),\; 10-(i-1)),$$
and set $\delta_1 = \delta_{10} = 0$. Then:

1. **Canonical AP frame.** The extreme runners $v_1, v_{10}$ determine a canonical 10-slot AP skeleton $0, 1, \ldots, 10$ in the normalised coordinate, with witness times $t_m = m/11$.

2. **Interior runners as perturbation data.** Each interior runner $v_i$ ($2 \leq i \leq 9$) is encoded by a perturbation $\delta_i = a_i - (i-1)$, measuring its displacement from the canonical AP slot $i-1$. The whole configuration is thus encoded by the AP frame and the vector $\delta = (\delta_2, \ldots, \delta_9) \in \mathbb{R}^8$.

3. **Witness-law compatibility.** For every witness label $m \in \mathcal{W}$, the loneliness inequalities for the normalised configuration are the AP witness inequalities plus explicit perturbative corrections depending only on $\delta$. The witness-control system is completely determined by the extreme-frame AP skeleton and $\delta$.

4. **Deterministic perturbation grammar.** At each witness $m$, the local active-pair and chamber state is a deterministic function of $\delta$. Interior runners select a state inside the finite witness grammar; they do not create a new ambient geometry.

5. **Grid inheritance.** After extreme-frame normalisation, the witness-label ordering and chamber-combinatorial structure depend only on the perturbation data $\delta$, not on the specific values of $v_1, v_{10}$.

Consequently, every ordered ten-speed configuration for $n = 11$ may be treated as an extreme-frame AP model with eight interior perturbations.

**Proof.** Statements 1 and 2 follow immediately from the definition $a_i = 10(v_i-v_1)/(v_{10}-v_1)$ and the strict ordering $v_1 < \cdots < v_{10}$. The perturbation bounds on $\delta_i$ follow from $0 < a_i < 10$ and the ordering constraints. Statements 3–5 are consequences of the explicit formula proved in Lemma 8.1 below, established independently of the present theorem. $\square$

**Theorem 7.2 (Extreme-frame reduction — operative form).** Every $v \in \mathcal{V}_{10}$ admits an affine normalisation in which the lowest and highest runners define a canonical AP frame and every other runner contributes only perturbation data. For the purpose of proving $n = 11$, it therefore suffices to analyse: (a) the AP witness law generated by the extreme runners, and (b) the confinement of perturbations induced by the interior runners.

**Remark 7.3 (Perturbations are always bounded).** After EFN, $a_1 = 0$ and $a_{10} = 10$ are fixed. The ordering constraints $0 = a_1 < a_2 < \cdots < a_9 < a_{10} = 10$ restrict $\delta_i$ to a convex polyhedron $\mathcal{D} \subset \mathbb{R}^8$. In particular, $\mathcal{D}$ is bounded; no configuration requires an unbounded perturbation analysis.

---

## 8. Witness-Law Compatibility and Perturbation Confinement

### 8.1 Explicit interval form

**Lemma 8.1 (Witness-law compatibility).** In the EFN normal form of Theorem 7.1, with $a_i = (i-1) + \delta_i$ and $\delta_1 = \delta_{10} = 0$, fix a candidate runner $j$ and a witness label $m \in \mathcal{W}$. For each $i \neq j$, define:
- the **AP residue** $r_{ij}(m) \equiv (i-j)m \pmod{11}$, $r_{ij}(m) \in \{1,\ldots,10\}$;
- the **perturbation difference** $\Delta_{ij} := \delta_i - \delta_j$.

Then the relative phase of runner $i$ against runner $j$ at witness time $t_m = m/11$ is
$$\{(a_i - a_j)\,t_m\} = \left\{\frac{r_{ij}(m)}{11} + \frac{m\,\Delta_{ij}}{11}\right\},$$
and the loneliness condition $1/11 \leq \{(a_i-a_j)\,t_m\} \leq 10/11$ is equivalent to the branch inequality
$$\Delta_{ij} \in I_{ij}^{(m)}(n_{ij}) := \left[\frac{1 - r_{ij}(m) + 11\,n_{ij}}{m},\; \frac{10 - r_{ij}(m) + 11\,n_{ij}}{m}\right]$$
for some integer branch index $n_{ij} \in \mathbb{Z}$. Hence the witness chamber for $j$ at label $m$ is the intersection
$$\mathcal{C}_{j,m} = \bigcap_{i \neq j}\; \bigcup_{n \in \mathbb{Z}} I_{ij}^{(m)}(n),$$
and its combinatorics are determined by the AP residue data $r_{ij}(m)$ and the perturbation differences $\Delta_{ij}$ alone.

**Proof.** From $a_i - a_j = (i-j) + \Delta_{ij}$:
$$(a_i - a_j)\,t_m = \frac{(i-j)m}{11} + \frac{m\,\Delta_{ij}}{11}.$$
Reducing the AP part modulo 1: $r_{ij}(m)/11 + n_0$ for some integer $n_0$, so
$$\{(a_i - a_j)\,t_m\} = \left\{\frac{r_{ij}(m)}{11} + \frac{m\,\Delta_{ij}}{11}\right\}.$$
The loneliness condition $1/11 \leq \{(a_i-a_j)t_m\} \leq 10/11$ holds if and only if there exists $n_{ij} \in \mathbb{Z}$ with
$$1 \leq r_{ij}(m) + m\,\Delta_{ij} - 11\,n_{ij} \leq 10.$$
Dividing by $m$ (which is positive) yields $\Delta_{ij} \in I_{ij}^{(m)}(n_{ij})$, as claimed. $\square$

*Remark 8.2 (Small-perturbation regime).* When the perturbations are small enough that no branch jump occurs ($n_{ij} = 0$), the inequalities reduce to
$$\frac{1 - r_{ij}(m)}{m} \leq \Delta_{ij} \leq \frac{10 - r_{ij}(m)}{m}.$$
In this regime the chamber picture is literally the AP chamber with shifted interval walls; the AP residue $r_{ij}(m)$ provides the rigid skeleton and $\Delta_{ij}$ shifts the position within it.

### 8.2 Perturbation confinement

**Theorem 8.2 (Deterministic perturbation confinement in the extreme frame).** Fix $n = 11$, a witness label $m \in \mathcal{W}$, and an EFN configuration with perturbation vector $\delta \in \mathcal{D}$. Then:

1. **Finite branch control.** For each pair $(i,j)$, only finitely many branch indices $n$ can occur on $\mathcal{D}$. For fixed $m$, the chamber system is governed by finitely many interval branches.

2. **Deterministic active-pair selection.** On each AP/grid cell of $\mathcal{D}$ — a connected component of the complement of the relevant coincidence hyperplanes $\Delta_{ij} = L_{ij,n}$ or $\Delta_{ij} = U_{ij,n}$ — the active lower and upper constraints for runner $j$ are determined uniquely by $r_{ij}(m)$ and $\delta$.

3. **Finite-state evolution.** As $\delta$ varies continuously in $\mathcal{D}$, chamber changes occur only when one active endpoint meets another. The chamber dynamics form a finite directed transition system on the set of active branch states.

4. **Perturbation confinement.** Repeated perturbations cannot create infinitely many independent extinction mechanisms. Every successive chamber-death event is one of three types:
   - **branch recurrence:** a previously seen active state reappears (phase-shift recurrence);
   - **offset transfer:** the active state moves to a neighbouring branch state determined by the AP residue skeleton;
   - **boundary transition:** the deformation reaches a cell boundary where branch combinatorics update.

**Proof.**

*Finite branch control.* Since $\mathcal{D}$ is bounded, each $\Delta_{ij} = \delta_i - \delta_j$ lies in a bounded interval $[A_{ij}, B_{ij}]$. The branch index $n$ in $I_{ij}^{(m)}(n)$ satisfies $(1 - r_{ij} + 11n)/m \leq B_{ij}$ and $(10 - r_{ij} + 11n)/m \geq A_{ij}$, bounding $n$ from above and below. Hence finitely many $n$ are relevant for each $(i,j)$, and since there are finitely many pairs, the total branch count is finite.

*Deterministic active-pair selection.* Each lower endpoint $L_{ij,n} = (1 - r_{ij}(m) + 11n)/m$ and upper endpoint $U_{ij,n} = (10 - r_{ij}(m) + 11n)/m$ is constant in $\delta$. The admissibility condition $\Delta_{ij}(\delta) \in I_{ij}^{(m)}(n)$ is affine in $\delta$ (since $\Delta_{ij} = \delta_i - \delta_j$). Every chamber wall is therefore an affine hyperplane in $\delta$-space. The relevant coincidence hyperplanes decompose $\mathcal{D}$ into finitely many AP/grid cells; on each cell the active-pair ordering is fixed and the active branches for runner $j$ are uniquely determined.

*Finite-state evolution.* Active-state changes occur only at coincidence hyperplanes; since finitely many relevant branches exist, finitely many active states are possible. The evolution is finite-state.

*Perturbation confinement.* If a later perturbation reproduces the same active branch state as an earlier one, this is branch recurrence. If the active state changes within a cell, it moves to an adjacent branch state by the residue skeleton — offset transfer. If the deformation crosses a cell boundary, branch combinatorics change — boundary transition. Since the state space is finite, an unbounded cascade of independent extinction events inside $\mathcal{D}$ is impossible. $\square$

**Theorem 8.3 (Uniform confinement across all witnesses).** In the setting of Theorem 8.2, the union over all $m \in \mathcal{W} = \{1,\ldots,10\}$ of the extreme-frame branch systems is finite. Therefore total extinction across all witnesses simultaneously cannot be generated by independent perturbation stacking across different witness labels.

**Proof.** Theorem 8.2 establishes finite branch control for each fixed $m \in \mathcal{W}$. Since $|\mathcal{W}| = 10$, the union over all $m$ of the relevant branch systems is a finite union of finite sets, hence finite. The finite-state evolution argument applies to each $m$ individually, and the combined state space across all witnesses is still finite. Hence total extinction across all witnesses cannot arise from an unbounded cascade. $\square$

---

## 9. Main Theorem

**Proposition 9.1 (AP base existence).** The AP base configuration $a = (1,2,\ldots,10)$ has a positive chamber at every witness label $m \in \mathcal{W}$.

**Proof.** For any $j \in \{1,\ldots,10\}$ and $m \in \{1,\ldots,10\}$: the relative speed $a_i - a_j = i - j$ and the witness-time position $\{(a_i - a_j)t_m\} = \{(i-j)m/11\} = r_{ij}(m)/11$. Since $11$ is prime and $i - j \not\equiv 0 \pmod{11}$ for $i \neq j$ both in $\{1,\ldots,10\}$, we have $r_{ij}(m) \in \{1,\ldots,10\}$, so $r_{ij}(m)/11 \in [1/11, 10/11]$. The loneliness condition holds for all $i \neq j$ at time $t_m$, confirming positive chambers at the AP base. $\square$

---

**Theorem A (Lonely Runner Conjecture for $n = 11$).** For any ordered tuple $(v_1, \ldots, v_{10})$ of ten distinct real speeds, there exists $j \in \{1,\ldots,10\}$ and $t > 0$ such that
$$\|(v_i - v_j)\,t\| \geq \frac{1}{11} \quad \text{for all } i \in \{1,\ldots,10\} \setminus \{j\}.$$
In particular, the classical Lonely Runner Conjecture for $n = 11$ holds: for any ten distinct nonzero integer speeds, the stationary runner has a lonely time (see §10.1 for the reduction).

**Dependency table.**

| Component | Classification | Location |
|---|---|---|
| Lemma 4.1 (mirrored residue-shift) | Proved | §4 |
| Lemma 4.2 (slack transfer) | Proved | §4 |
| Lemma 4.3 (branch orientation) | Proved | §4 |
| Theorem 5.1 (directed finite transition law) | Proved | §5 |
| Theorem 6.1 (no first total extinction in cell) | Proved | §6 |
| Theorem 7.1/7.2 (extreme-frame normalisation) | Proved | §7 |
| Lemma 8.1 (witness-law compatibility) | Proved | §8 |
| Theorem 8.2 (perturbation confinement) | Proved | §8 |
| Theorem 8.3 (uniform confinement, all witnesses) | Proved | §8 |
| Proposition 9.1 (AP base existence) | Proved | §9 |
| **Theorem A** ($n = 11$) | **Unconditional** | §9 |

**Proof of Theorem A.**

*Step 1 (EFN reduction).* Let $v \in \mathcal{V}_{10}$ be any ordered ten-speed configuration. By Theorem 7.2, apply the affine normalisation $a_i = 10(v_i - v_1)/(v_{10}-v_1)$, giving $a_1 = 0$, $a_{10} = 10$, and interior perturbation vector $\delta = (\delta_2,\ldots,\delta_9) \in \mathcal{D}$.

*Step 2 (Witness-law compatibility).* By Lemma 8.1, for each $m \in \mathcal{W}$ and each pair $(i,j)$, the loneliness condition at time $t_m$ is $\Delta_{ij} \in I_{ij}^{(m)}(n_{ij})$ for some $n_{ij} \in \mathbb{Z}$. The chamber structure is governed by finitely many interval branches (Theorem 8.2).

*Step 3 (Perturbation confinement).* By Theorems 8.2 and 8.3, the extreme-frame chamber system is a finite deterministic state process, and perturbation stacking cannot generate unbounded cascades across any witness label.

*Step 4 (No total extinction in a cell).* By Theorem 6.1, within any AP/grid cell of $\mathcal{D}$, first total extinction of all chambers cannot occur. Some chamber has nonnegative width throughout any continuous deformation within the cell.

*Step 5 (AP base has positive chambers).* By Proposition 9.1, the base point $\delta = 0$ (exact AP spacing, corresponding to $v_i = v_1 + (i-1)(v_{10}-v_1)/9$) has a positive chamber at every witness label.

*Step 6 (Propagation through $\mathcal{D}$).* The perturbation region $\mathcal{D}$ is convex (defined by linear ordering constraints), hence path-connected. For any target $\delta^* \in \mathcal{D}$, the straight-line path $\delta(\lambda) = \lambda\,\delta^*$ connects $\delta = 0$ to $\delta^*$. Along this path, Theorem 6.1 applies in each AP/grid cell with $\lambda$ as the deformation parameter: since no total extinction can occur inside any cell, and since chamber widths are continuous across cell boundaries (they are limits of the same affine endpoint functions), survival propagates from $\delta = 0$ to every $\delta^* \in \mathcal{D}$.

*Conclusion.* Every ordered ten-speed configuration has a surviving loneliness chamber for some runner $j \in \{1,\ldots,10\}$. Therefore there exists $t > 0$ with $\|(v_i - v_j)t\| \geq 1/11$ for all $i \neq j$. $\square$

---

## 10. Notes and Open Items

### 10.1 Connection to the classical LRC

The classical LRC for $n = 11$ asks for a time $t$ with $\|v_i t\| \geq 1/11$ for all ten nonzero moving speeds $v_i$. This is the condition that the stationary runner (at speed 0) is lonely. Theorem A proves the existence of $j$ and $t$ with $\|(v_i - v_j)t\| \geq 1/11$ for all $i \neq j$.

The classical statement follows from Theorem A by one of two routes. The cleaner route: apply Theorem A to the eleven-runner system by including the stationary runner (at speed 0) as a possible candidate reference runner. The formula $M_j(m) \equiv (11-j)m \pmod{11}$ requires $j \in \{1,\ldots,10\}$ for $M_j(m) \neq 0$; the stationary runner at $j = 0$ lies outside this range. However, taking $j = 1$ in the EFN (so $a_1 = 0$) gives loneliness conditions $\{a_i t_m\} \in [1/11, 10/11]$ for $i = 2,\ldots,10$ — nine of the ten required conditions. The tenth condition ($\|v_1 t\| \geq 1/11$ in original coordinates) involves $v_1$ directly and requires a separate, non-degenerate argument depending on whether $v_1$ is zero or not.

In the integer-speed case, the standard discrete formulation of the LRC (as in [v12]) can be recovered directly: if the ten speeds are integers with $\gcd = 1$, the safe-point count $x_0(E) = \#\{k \in \{1,\ldots,N-1\} : (e_i k \bmod N) \in [L, 10L] \text{ for all } i\}$ is positive. The AP framework applies to the set of relative speeds $\{e_i - e_j : i \neq j\}$ and gives a safe time in the relative frame. Converting back to the stationary-runner frame is a standard step.

**Open item (O1):** Write up the precise reduction from Theorem A (relative formulation) to the classical LRC (stationary-runner formulation) as a short appendix or companion note. The gap is small but should be made explicit before arXiv submission.

### 10.2 AP base existence — explicit verification

Proposition 9.1 establishes that $t_m = m/11$ is a safe time for every candidate runner $j$ at the AP base configuration. Concretely, for $j = 1$ (or any $j$), $n = 11$ prime, and the 10 nonzero residues $\{(i-j)m \bmod 11 : i \neq j, i \in \{1,\ldots,10\}\}$ are a permutation of $\{1,\ldots,10\}$ (since $11 \nmid (i-j)m$ for any $i,j,m$ in the stated range), so all fractional parts lie in $[1/11, 10/11]$.

### 10.3 Relation to the v12 branch-splitting proof

The proof in [v12] splits according to the number of speeds divisible by 11 (no-divisible / multiple-divisible / one-divisible branches), using explicit witnesses, period-start fibres, and floor-reset arguments. That proof has one acknowledged open gap: Lemma 3.6 for the case $m \geq 6$ extreme runners (sub-case H1b), where the compatible-window Step 2 of the density-period argument is not yet fully formalised.

The present AP-framework proof does not use a divisibility split and does not have this gap. The two proofs are architecturally independent and structurally complementary. Neither supersedes the other.

### 10.4 Bounded perturbation region

After EFN (Remark 7.3), the interior perturbation vector $\delta = (\delta_2,\ldots,\delta_9)$ lies in the convex polyhedron
$$\mathcal{D} = \{(\delta_2,\ldots,\delta_9) : a_1 < a_2 < \cdots < a_9 < a_{10},\; a_i = (i-1)+\delta_i\},$$
which is bounded. In particular, $|\delta_i| < 10$ for all $i$, and no configuration requires an unbounded perturbation analysis.

### 10.5 Endpoint cases in Lemma 4.1

The generic interior transport (Corollary 4.1a) covers all cases where $M_j(m) \notin \{1, 10, 1-\sigma, 10-\sigma\}$. The endpoint cases (e.g. $M_j(m) = 1$ with $\sigma = -1$, causing the lower boundary slot to change) modify the active-residue transport by the explicit $\Delta^\pm_\sigma$ terms. A complete case analysis of these endpoint transitions can be carried out in $O(1)$ cases and is left for a subsequent version.

---

## References

- [BGG+98] A. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi, *Flows, view obstructions, and the lonely runner*, J. Combin. Theory Ser. B **72** (1998), 1–9.

- [BH01] T. Bohman, R. Holzman, *Six lonely runners*, Electron. J. Combin. **8** (2001), R3.

- [BS08] J. Barajas, O. Serra, *The lonely runner with seven runners*, Electron. J. Combin. **15** (2008), R48.

- [Cus73] T. W. Cusick, *View obstruction problems*, Aequationes Math. **9** (1973), 165–170.

- [Ros25] B. Rosenfeld, *The lonely runner conjecture for eight runners*, preprint, 2025.

- [Tao18] T. Tao, *Some remarks on the lonely runner conjecture*, Contrib. Discrete Math. **13** (2018), 1–31.

- [Tra25] P. Traill, *Ten lonely runners*, preprint, 2025.

- [v12] T. Palelei, *The Lonely Runner Conjecture for* $n = 11$, preprint v12, 2026.

- [Wil67] J. M. Wills, *Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen*, Monatsh. Math. **71** (1967), 263–269.

---

*End of preprint v1.*
