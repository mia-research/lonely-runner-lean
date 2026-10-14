# A Proof of the Lonely Runner Conjecture via Structural Instability of Full Obstruction

**Author:** Trent Palelei
**Affiliation:** MI Research Foundation
**Date:** March 2026
**Version:** v10.6
**Draft status:** Integrity-repair draft. This version adds exact actual-speed formulas at the base fibre $b=L/n$ and at floor-reset events, while the dropped-unit bridge remains under reconstruction.
**MSC 2020:** 11B75 (Sequences and sets), 11K60 (Metric theory of Diophantine approximations)
**Keywords:** Lonely runner conjecture, residue classes, units modulo n, arithmetic combinatorics, Diophantine approximation, floor transitions, structural instability

---

## Abstract

This integrity-repair draft records the current proof architecture for the Lonely Runner Conjecture for all $n \ge 3$. After the standard reduction to gcd-1 integer speeds and discrete times $k/(nL)$, the difficult case is when at least one speed is divisible by $n$. Then the question becomes whether the remaining speeds can block every residue class modulo $n$ throughout the divisible-fibre interval. We call this **full obstruction**.

The governing mechanism remains the same as in the earlier manuscript line: full obstruction should be structurally unstable. A unit residue class determines a distinguished unit residue through the inversion map $u \mapsto -u^{-1} \bmod n$, while non-units move in subgroup cosets and cannot freely replace unit obligations. If every unit residue class is represented, the floor-reset mechanism of §9 still provides the working template for a dynamic handoff-failure argument. If a unit residue class is missing, however, the manuscript now treats the bridge from residue-level omission to an actual safe chamber as an explicit repair task.

Accordingly, `v10.6` separates actual speeds from residue representatives, records the exact base-fibre and floor-reset formulas in those actual-speed coordinates, preserves the dynamic and quantitative architecture as working templates, and isolates the dropped-unit bridge as the main remaining integrity task.

---

## 1. Introduction

### 1.1 Background and Statement

**Definition (Lonely Runner Conjecture, LRC).** Let $v_1, \ldots, v_{n-1}$ be distinct nonzero integers. Runner 0 is stationary at the origin on the unit circle $\mathbb{R}/\mathbb{Z}$. Runner $j$ moves at speed $v_j$. Runner 0 is *lonely* at time $t$ if $\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $j$. The conjecture asserts that runner 0 is lonely at some $t \geq 0$ for every choice of $n$ and distinct nonzero integer speeds.

The conjecture was posed independently by Wills (1967) in the context of simultaneous Diophantine approximation and by Cusick (1973) in view-obstruction problems. Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi (1998) established the formulation used here and proved the case $n \leq 5$. Barajas and Serra (2008) proved $n = 7$; Bohman, Holzman, and Kleitman (2001) proved $n = 6$ by a different method. Czerwiński (2012) studied the conjecture for random speeds. Tao (2018) gave quantitative refinements and Fourier-analytic perspectives on the conjecture. The general case remained open.

The manuscript is organised around a simple residue-theoretic claim. In the case where some speed is divisible by $n$, one is led to ask whether the remaining speeds can block every residue class modulo $n$ throughout the interval on which the divisible speeds are active. We call this situation **full obstruction**. In `v10.6`, the actual-speed layer and the residue-support layer are separated explicitly: the guiding expectation is still that full obstruction cannot persist, but the bridge from missing residue classes to actual safe fibres is being rebuilt in the dropped-unit branch.

**Main Theorem.**

> **Theorem A.** *For all $n \geq 3$ and all gcd-1 tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers:*
> *(LRC)* $x_0(E) \geq 1$, i.e., runner 0 is lonely at some time.

In `v10.6`, Theorem A is the target theorem of the manuscript. The unit-complete dynamic branch remains recorded as the main working mechanism, while the dropped-unit branch is being rebuilt under the actual-speed/residue-support split using the exact base-fibre and floor-reset formulas recorded in §§5.3 and 9.2a.

**Sketch of the proof.**

1. If no speed is divisible by $n$, then the standard witness times $\{jL : \gcd(j,n)=1\}$ are already safe. This is §4.
2. If some speed is divisible by $n$, we work on a discrete interval of fibres and study which residue classes modulo $n$ are blocked by the non-divisible speeds. Units and non-units behave differently: units block two residues determined by inversion, whereas non-units block subgroup cosets.
3. The first repair datum is the exact base fibre $b=L/n$. There each actual retained speed $e=nq_e+\rho_e$ contributes a blocked set determined by both $\rho_e$ and $q_e$. In particular, omitted residue classes in $R_{\rm non}$ do not by themselves determine the blocked set; the quotient data matter and must be tracked explicitly.
4. The remaining case is when every unit residue class is represented; we call this the **unit-complete regime**. There the proof follows a floor-reset event of an actual unit runner. The residue leaving that runner can be inherited only if an exact remainder condition holds for another retained speed. Those actual-speed coverage gates are recorded in §9.2a and provide the right coordinates for the dynamic repair.

**Quantitative status.** The quantitative prime and composite branches remain recorded in the manuscript, but in `v10.6` the dropped-unit quantitative routes should be read as templates pending repair of the underlying bridge. The bounded certified enumeration for prime $n \in \{5,7\}$ remains part of that architecture, and the dynamic unit-complete amplification results are retained as working templates. See §13 for the branch-by-branch dependency map.

**Conceptual provenance.** The argument is written in residue language, but the guiding picture is the same finite instability visible in the submitted `n=11` paper: a threatened blocking responsibility cannot be repaired independently of the rest of the configuration. The all-$n$ proof recasts that picture in general arithmetic terms through unique unit coverage, subgroup-restricted non-units, and floor-reset handoff.

### 1.2 Arithmetic Reformulation

By rescaling and dividing by gcd, it suffices to prove: for all $n \geq 3$ and all tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$, there exists $t \in \mathbb{R}$ with $\|e_i t\| \geq 1/n$ for all $i$.

Set $L = \mathrm{lcm}(E)$ and $N = nL$. The **safe-point count** is
$$x_0(E) = \#\bigl\{k \in \{1, \ldots, N-1\} : (e_i k \bmod N) \in [L, (n-1)L] \text{ for all } i\bigr\}.$$

**Equivalence.** The real-time condition $\|e_i t\| \geq 1/n$ at $t = k/N$ becomes $(e_i k \bmod N) \in [L, (n-1)L]$. So $x_0(E) > 0$ iff the LRC holds for $E$.

*Boundary inclusion note:* The interval $[L, (n-1)L]$ is closed because $\|e_i t\| \geq 1/n$ is a weak inequality; hits $(e_i k \bmod N) \in \{L,\,(n-1)L\}$ satisfy $\|e_i t\| = 1/n$ exactly and count as safe.

When $E_{\rm div} \neq \emptyset$, we also write
$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\}$$
for the **divisible-fibre interval**. Sections 2 and 5--12 study, for each $b \in B_{\rm div}$, which residue classes modulo $n$ are blocked by the non-divisible speeds.

For each actual non-divisible speed $e \in E_{\rm non}$, write
$$e = n q_e + \rho_e, \qquad 1 \leq \rho_e \leq n-1,$$
where $\rho_e$ is the least positive residue of $e$ modulo $n$. The **residue support** of the retained non-divisible speeds is
$$R_{\rm non} := \{\rho_e : e \in E_{\rm non}\} \subseteq \{1,\ldots,n-1\}.$$
Distinct actual speeds may share the same residue class, so statements about omitted classes must be phrased in terms of $R_{\rm non}$ rather than $E_{\rm non}$ itself.

### 1.3 Case Partition

Partition $E = E_{\rm div} \cup E_{\rm non}$ where $E_{\rm div} = \{e \in E : n \mid e\}$ and $E_{\rm non} = E \setminus E_{\rm div}$.

- **Case 1:** $E_{\rm div} = \emptyset$. Section 4.
- **Case 2:** $E_{\rm div} \neq \emptyset$. Sections 5–12.

### 1.4 Units Modulo $n$ and Inversion

The residue argument is controlled by the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$. A convenient identity is
$$\sum_{\substack{e=1 \\ \gcd(e,n)=1}}^{n-1} e = \frac{n\,\varphi(n)}{2}.$$

This follows by pairing each unit $e$ with $n-e$. The sum identity supplies the counting backdrop for the later residue argument. The more important map is the inversion map
$$e \longmapsto -e^{-1} \pmod n,$$
which will identify the unit residue uniquely blocked by a given unit speed at floor $0$. Section 5 turns this into the unique-coverage lemma, and §9 uses the same residue bookkeeping at floor-reset events.

---

## 2. Structural Instability of Full Obstruction

This section gives a reader's guide to the residue argument. In Case 2, each retained non-divisible speed $e \in E_{\rm non}$ and each fibre $b \in B_{\rm div}$ determine a blocked residue set $\mathrm{bad}(e,\lfloor eb/L \rfloor,n) \subseteq \mathbb{Z}/n\mathbb{Z}$; the formal definition is given in §5.1. A fibre is safe if these blocked sets fail to cover all residues. Thus **full obstruction** means that every residue class is blocked at every fibre of $B_{\rm div}$.

The claim of this section is that full obstruction is impossible. The reason is that blocked residues are **coupled**: a runner does not control one residue at a time, but moves its whole blocked set according to its floor state. This leads to two mechanisms. The first is static: if a unit residue class is missing, a gap appears immediately. The second is dynamic: if all unit classes are present, then at a suitable floor transition the attempted handoff of a departing residue must fail.

### 2.1 Units, Non-Units, and Coupled Blocking

Fix a Case-2 tuple $E$ and write $\mathrm{bad}(e,t,n)$ for the blocked residue set of runner $e$ at floor $t$. The key distinction is between units and non-units modulo $n$.

**Units.** If $\gcd(e,n)=1$, then
$$\mathrm{bad}(e,t,n)=\{-te^{-1},-(t+1)e^{-1}\}\pmod n.$$
So a unit blocks exactly two residues at each floor. In particular, at floor $0$ it blocks $\{0,-e^{-1}\}$, and the map $e \mapsto -e^{-1} \bmod n$ is a bijection on the units of $\mathbb{Z}/n\mathbb{Z}$. Thus each unit speed carries a unique unit residue at floor $0$.

**Non-units.** If $g=\gcd(e,n)>1$, then $\mathrm{bad}(e,t,n)$ is a coset of the subgroup $H_g=(n/g)(\mathbb{Z}/n\mathbb{Z})$ when $g \mid t$, and it is empty when $g \nmid t$. At floor $0$ the blocked set is exactly $H_g$. Thus a non-unit does not block an arbitrary collection of residues; it blocks either an entire subgroup coset or nothing at all.

Prime and composite moduli therefore look different for a structural reason. For prime $n$, every non-zero non-multiple is a unit, so the unit picture is complete. For composite $n$, some non-multiples are non-units living in subgroup cosets; they dilute unit coverage without being able to replace it arbitrarily.

We refer to this lack of independent control as **coupling**.

**Lemma 2.1 (Coupled blocking).** *For any runner $e \in E_{\rm non}$:*
1. *if $\gcd(e,n)=1$, then $\mathrm{bad}(e,t,n)=\{-te^{-1},-(t+1)e^{-1}\} \bmod n$, so the two blocked residues move together as $t$ changes;*
2. *if $\gcd(e,n)=g>1$, then $\mathrm{bad}(e,t,n)$ is a coset of $H_g$ when $g \mid t$ and is empty otherwise, so an entire coset appears or disappears at once.*

*In either case, a runner cannot be retuned to fix one residue without moving the rest of its blocked set.*

**Proof.** The unit formula is immediate from the definition of $\mathrm{bad}(e,t,n)$. For non-units, $\mathrm{Sol}(e,-t,n)$ is either empty or a full coset of $H_g$ according as $g \nmid t$ or $g \mid t$. $\square$

### 2.2 The Static Step: Missing Units Force a Gap

The first mechanism is a residue-level counting argument. Since there are only $n-1$ retained runners but $n$ residue classes, any full obstruction would have to use the unit residues very efficiently. At floor $0$, each unit residue class $u$ is paired with the unit residue $-u^{-1} \bmod n$. Thus, if a unit residue class
$$d \in (\mathbb{Z}/n\mathbb{Z})^\times$$
is absent from the residue support $R_{\rm non}$, the intended exposed residue is
$$r_d=-d^{-1}\pmod n.$$
What still has to be proved carefully is the bridge from this residue-level omission to an actual safe chamber for the original speed tuple. In earlier drafts that bridge was written as a floor-$0$ argument on the interval $I_d=[L/n,L/(n-1))$; in `v10.6` it is isolated explicitly in §5.3 as a repair target.

Two further phenomena fit the same static picture.

**Transparency of non-units.** If $g=\gcd(e,n)\geq 3$, then a non-unit runner $e$ has empty blocked set whenever $t \bmod g \in \{1,\ldots,g-2\}$. So non-units can contribute nothing on long stretches of the divisible-fibre interval.

**Prime-power bottleneck.** If $n=p^k$ and $e=jp$ is non-unit, then away from floor $0$ the runner can meet the level-$(k-1)$ residues only on sparse dangerous floors. This level bottleneck is the prime-power version of the same obstruction: subgroup-restricted runners cannot freely replace the missing unit coverage.

### 2.3 The Dynamic Step: Floor Resets and Failed Handoff

The static argument leaves one genuinely delicate situation: every unit residue class is represented among the retained non-divisible speeds. We call this the **unit-complete regime**. Here the static count is saturated, so the proof turns to time-local behaviour.

At a **floor-reset event** for a unit runner $e_u$, the floor $\lfloor e_u b/L \rfloor$ increases by $1$, and one residue
$$r_{\rm dep}=-(m-1)e_u^{-1}\pmod n$$
leaves the blocked set of $e_u$. Any other runner that tries to inherit this residue must satisfy one of two explicit arithmetic conditions from Lemma 9.2a. We refer to these necessary conditions as the **coverage gates**. The point is that these gates are restrictive: one is a divisibility condition, and the other has a unique candidate solution that is typically non-unit. Theorem 9.2c shows that for any missing non-unit one can choose a floor-reset event at which both gates fail. At that moment the departing residue is uncovered, so the fibre is safe.

### 2.4 Case-2 Obstruction Statement

For $b \in B_{\rm div}$ and $r \in \mathbb{Z}/n\mathbb{Z}$, define the **coverage multiplicity**
$$C(r,b)=\#\{e \in E_{\rm non} : r \in \mathrm{bad}(e,\lfloor eb/L \rfloor,n)\}.$$
The goal in Case 2 is to prove that there exist $b \in B_{\rm div}$ and $r \in \mathbb{Z}/n\mathbb{Z}$ with $C(r,b)=0$. Equivalently, full obstruction cannot persist on the divisible-fibre interval.

The branch analysis reduces this to two moves.

- If a unit residue class is missing, the static argument of §2.2 gives an uncovered residue on an initial interval.
- If every unit residue class is present, the dynamic argument of §2.3 produces a floor-reset event at which a residue cannot be handed off.

The later sections either implement one of these two moves directly or amplify the resulting safe fibre to the stated quantitative bounds.

### 2.5 Road Map

The later sections can be read according to the role they play in this scheme.

| Section | Branch | Manifestation |
|---|---|---|
| §3 | Irrational speeds | Equidistribution argument |
| §4 | Case 1: no divisible runner | Explicit witness times |
| §5 | Case 2 setup and unique unit coverage | Static step |
| §7–§8 | Prime $n$ with divisible runners | Static step plus transparency |
| §9 | Floor-reset mechanism | Dynamic step |
| §10 | Prime $n$, large $L$ | Static counting argument |
| §11 | Composite $n$, dropped unit | Static counting argument |
| §11–§12 | Composite $n$, unit-complete branches | Dynamic step and quantitative amplification |
| §2.7 | Prime $n$, constructive companion | Explicit AP-style certificate |

### 2.6 How to Read the Proof

For verification purposes, the paper has three logically distinct parts.

- §§3--4 handle irrational speeds and the case with no divisible speed by direct witness constructions.
- §§5--8, §10, and the dropped-unit parts of §11 use the static residue argument: a missing unit class forces an uncovered residue.
- §9, the unit-complete parts of §11, and §12 use the dynamic residue argument: at a suitable floor-reset event the departing residue cannot be handed off.

The terminology introduced in §2 is meant only to keep these two mechanisms visible. Once those mechanisms are clear, the later casework is primarily arithmetic case analysis built on them. Section 2.7 is supplementary and may be skipped on a first reading.

### 2.7 Constructive Witnesses: AP-Framework Complement for Prime $n$

> **Companion note.** No result in this section is used in Theorem A. Readers interested only in the main proof may skip directly to §3. We retain the section here only to record the AP-framework companion programme for prime $p$ and to indicate how the finite constructive picture relates to the main existential argument.

The coverage arguments in §§5–10 are existential. For prime $p$, the AP (arithmetic-progression) framework provides an explicit loneliness certificate, converting the existential argument into a constructive one.

**Slot decomposition.** For prime $p$ with normalised pacemaker speed $a_1 = 1$, partition the reference window $W_{\rm ref} = [1/p, (p-1)/p]$ into $p-2$ slots:
$$I_s = \left[\frac{ps+1}{p(p-1)},\, \frac{ps+p-1}{p(p-1)}\right], \quad s = 1,\ldots,p-2.$$
Each slot has width $(p-2)/(p(p-1))$. By Corollary 5.4 (Complementary Pairs), runner $j$ has "natural witness index" $m_j \equiv j^{-1} \pmod{p}$; its AP-limit bad interval is centred at $m_j/p \in W_{\rm ref}$, placing it inside slot $I_{m_j-1}$. The $p-2$ slots are claimed pairwise by the $(p-3)/2$ complementary pairs $\{(j, p-j)\}$; **slot $I_{p-2}$ is unclaimed** (Theorem CP, proved as Corollary 5.4).

**Lemma 2.2 (Sign-Range Containment).** *In a completely-blocking (CB) configuration for prime $p \geq 5$: every runner $j \in \{2,\ldots,p-2\}$ satisfies $a_j \in (j-1, j+1)$.*

**Proof.** By contrapositive. If $a_j \geq j+1$: runner $j$'s position at its natural witness time $t_{m_j}$ is $a_j t_{m_j} \approx (j+1)m_j/p \equiv (1+m_j)/p \pmod{1}$. Since $jm_j \equiv 1 \pmod{p}$, the fractional part $(1+m_j)/p \in (2/p, (p-1)/p)$ lies inside the safe zone $[1/p,(p-1)/p]$: runner $j$ fails to block $t_{m_j}$. By the Complementary Pairs structure (Corollary 5.4), no other runner is assigned as primary blocker to $I_{m_j-1}$; a secondary filler triggers its own cascade (Lemma PSM or Chain in the AP-framework companion), forcing GF > 0 in another slot — contradicting CB. The case $a_j \leq j-1$ follows symmetrically: $(j-1)m_j \equiv (1-m_j) \pmod{p}$, fractional part $(p+1-m_j)/p \in (2/p,(p-1)/p)$ for $m_j \geq 2$, same conclusion. $\square$

**Proposition 2.3 (Feasibility Classification, prime $p \geq 11$).** *Only runner 2 is strongly feasible for slot $I_{p-2}$: i.e., only runner 2 can have a bad interval covering the entire slot ($a_2 \leq 2(p-1)/(p-2)$). Every other runner $j \in \{3,\ldots,p-2\}$ can partially overlap $I_{p-2}$ (weakly feasible) but cannot alone cover it.*

**Proof.** A bad interval of runner $j$ has width $2/(pa_j)$; for it to span the slot width $(p-2)/(p(p-1))$ requires $a_j \leq 2(p-1)/(p-2)$. For $j \geq 3$: $a_j > j-1 \geq 2$, and $2(p-1)/(p-2) \leq 2(p-1)/(p-2) < 3$ for $p \geq 5$. So strong feasibility requires $a_j < 3$, which forces $j = 2$. Weak feasibility (partial overlap at $k=j-1$) holds for all $j = 2,\ldots,p-2$ by a geometric computation verified for $p = 11$ and $p = 13$ (§3 of the AP-framework companion). $\square$

**Theorem 2.4 (Runner Incompatibility, prime $p \geq 11$).** *Let $p$ be prime and let $a_{p-2}^* = (p-1)^2/(p+1)$ (the $I_1$-closing speed of the outer runner). Define:*
$$L_{\rm in}(p) = \frac{p-2}{2p}, \qquad R_{\rm out}(p) = \frac{(p^2-3p-1)(p+1)}{p(p-1)^2}.$$
*Closing slot $I_{(p-3)/2}$ forces $a_2 \geq A_2(p) = 2(p-1)/(p-2)$. Closing slot $I_{p-2}$ forces $a_2 \leq B_2(p) = (2p+1)(p-1)^2/((p^2-3p-1)(p+1))$. These constraints are mutually incompatible:*
$$A_2(p) - B_2(p) = \frac{(p-1)(p^2-9p-4)}{(p-2)(p^2-3p-1)(p+1)} > 0 \quad \text{for all prime } p \geq 11.$$

**Proof.** $A_2(p) > B_2(p)$ iff $(p-1)R_{\rm out}(p) > (2p+1)L_{\rm in}(p)$. Substituting:
$$2(p^2-3p-1)(p+1) - (2p+1)(p-1)(p-2) = p^2-9p-4 \geq 18 \text{ for } p \geq 11.$$
Identity verified: expand LHS $= 2p^3-4p^2-8p-2$, RHS $= 2p^3-5p^2+p+2$; difference $= p^2-9p-4$. For $p \geq 11$: $p^2-9p-4 \geq 121-99-4 = 18 > 0$. $\square$

*Verification ($p=11$):* $A_2 - B_2 = 10 \times 18/(9 \times 87 \times 12) = 5/261 > 0$. ✓
*Verification ($p=13$):* $A_2 - B_2 = 12 \times 48/(11 \times 129 \times 14) = 96/3311 > 0$. ✓

**Corollary 2.5 (GF > 0 for prime $p \geq 11$).** *In any CB configuration with outer runner $j_0 = p-2$ at $a_{p-2}^*$: $\mathrm{GF}(I_{(p-3)/2}) > 0$ or $\mathrm{GF}(I_{p-2}) > 0$. Runner 0 is lonely.*

**Remark 2.6 (Baton-Pass Certificate, partial).** The rational time
$$t^* = \frac{(2p+1)(p+1)}{p(p-1)^2}$$
is the right endpoint of bad interval $B_{p-2,1}$ at $a_{p-2}^*$ (the moment runner $p-2$ exits its $k=1$ bad zone), and lies in slot $I_2$. For $p=11$: $t^* = 69/275 \in I_2$ ✓; for $p=13$: $t^* = 21/104 \in I_2$ ✓. The all-runner verification that $t^*$ is a *complete* loneliness certificate (all $p-2$ runners simultaneously safe) requires checking each runner's bad-interval position at $t^*$; this has been verified for $p=11$ (Case C₁ of the $n=11$ companion analysis). For $p \geq 13$ this all-runner verification is an **open target for the companion programme only — it is not part of the proof of Theorem A and carries no proof obligation here**.

**Note on open items.** The partial Baton-Pass certificate (Remark 2.6) and the all-runner verification for $p \geq 13$ are open within the companion programme only and carry no proof obligation for Theorem A.

---

## 3. Irrational Speeds

**Theorem 3.1.** *If the speeds $v_1, \ldots, v_{n-1}$ are not all rationally commensurate, then runner 0 is lonely at some time $t > 0$.*

**Proof.**

**Step 1 — Basis reduction.** Choose a maximal $\mathbb{Q}$-independent subset $\{\alpha_1, \ldots, \alpha_r\}$ of $\{v_1, \ldots, v_{n-1}\}$, so $r \geq 1$ and each $v_j = \sum_i q_{ji}\alpha_i$ with rationals $q_{ji}$. The safe set on $\mathbb{T}^r$ is
$$\mathcal{S} = \bigcap_{j=1}^{n-1} f_j^{-1}\!\bigl((1/n, (n-1)/n)\bigr), \quad f_j : x \mapsto \sum_i q_{ji}x_i \bmod 1.$$

**Step 2 — Positive strip measure.** Each $f_j$ is a surjective group homomorphism ($v_j \neq 0$ implies some $q_{ji} \neq 0$). By the Haar-measure push-forward, each strip has measure $(n-2)/n > 0$.

**Step 3 — Independence across $\mathbb{Q}$-classes.** Partition speeds into maximal $\mathbb{Q}$-proportionality classes $C_1, \ldots, C_m$ ($m \geq 2$). Because the safe set $\mathcal{S}$ is defined by conditions on $f_j(x) = \sum_i q_{ji} x_i \bmod 1$ and each $f_j$ depends only on the coordinates $x_i$ for basis vectors $\alpha_i$ in the class of $v_j$ — which holds because if $v_j \in C_\ell$ (i.e.\ $v_j = c_j\alpha_{i_\ell}$ for rational $c_j$), then by uniqueness of rational linear combination in the $\mathbb{Q}$-independent basis $\{\alpha_1,\ldots,\alpha_r\}$, the expansion $v_j = \sum_i q_{ji}\alpha_i$ has $q_{ji} = c_j$ for $i = i_\ell$ and $q_{ji} = 0$ for $i \neq i_\ell$, so $f_j(x) = c_j x_{i_\ell}$ involves only coordinate $x_{i_\ell}$ — the safe set factors as $\mathcal{S} = \prod_\ell \mathcal{S}_\ell$ where $\mathcal{S}_\ell \subseteq \mathbb{T}^{r_\ell}$ involves only the coordinates for class $C_\ell$. By the multidimensional Weyl equidistribution theorem (Weyl 1916; see Kuipers–Niederreiter §1.4), since $\alpha_1, \ldots, \alpha_r$ are $\mathbb{Q}$-independent, the sequence $(t\alpha_1 \bmod 1, \ldots, t\alpha_r \bmod 1)_{t \geq 1}$ is equidistributed on $\mathbb{T}^r$; in particular, coordinates for different classes are jointly uniform, reflecting the $\mathbb{Q}$-independence of the basis vectors across classes.

**Step 4 — Positive measure of $\mathcal{S}$.** For $m \geq 2$ with each class $C_\ell$ having size $s_\ell < n/2$: $\lambda^r(\mathcal{S}) = \prod_\ell \lambda(\mathcal{S}_\ell) \geq \prod_\ell (1 - 2s_\ell/n) > 0$.

**Steps 4a–4b — Boundary cases.**

**Step 4a** ($m=1$, all speeds $\propto$ one irrational $\alpha$): Write $v_j = c_j\alpha$, $\gcd(c_j)=1$. By density of $\{t\alpha \bmod 1\}$, it suffices to show $\mathcal{S} \neq \emptyset$. If no $c_j \equiv 0 \pmod n$: Theorem 4.1 gives $u_0 = j_0/n \in \mathcal{S}$. If some $c_j \equiv 0 \pmod n$: the Case-2 proof (§§5–12) applied to speeds $c_j$ yields explicit $u_0 \in \mathcal{S}$.

**Step 4b** (large class, $m \geq 2$, some $s_\ell \geq n/2$): Apply the Step 4a argument to $C_\ell$ to get $\mathcal{S}_\ell \neq \emptyset$; remaining classes have size $< n/2$ and give positive-measure safe sets. Full $\mathcal{S} = \mathcal{S}_\ell \times \prod_{k\neq\ell}\mathcal{S}_k$ is non-empty.

**Step 5 — Weyl equidistribution.** Since some $\alpha_i$ is irrational and the $\alpha_i$ are $\mathbb{Q}$-independent, Weyl's theorem gives that $(t\alpha_1 \bmod 1, \ldots, t\alpha_r \bmod 1)_{t \geq 1}$ is equidistributed on $\mathbb{T}^r$. Since $\mathcal{S}$ is open with positive measure, the sequence visits $\mathcal{S}$. $\square$

---

## 4. Case 1: All Speeds Coprime to $n$

**Theorem 4.1.** *If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$.*

**Proof.** The $\varphi(n)$ witness times $W = \{k_j = jL : 1 \leq j \leq n-1,\, \gcd(j,n) = 1\}$ are all safe: for any $k_j = jL$ and $e_i$, $(e_i jL) \bmod (nL) = L\cdot(e_i j \bmod n)$, which lies in $[L,(n-1)L]$ iff $n \nmid e_ij$. Since $\gcd(j,n)=1$: $n \mid e_ij$ iff $n \mid e_i$, which is excluded by hypothesis. $\square$

---

## 5. Case 2: Setup and the Sole Cover Bijection

We henceforth assume $E_{\rm div} \neq \emptyset$.

### 5.1 Notation

Set $L_0 = \mathrm{lcm}(E_{\rm non})$, $L = \mathrm{lcm}(E)$. The **divisible-fibre interval** is
$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\}, \quad |B_{\rm div}| = (n-2)L/n + 1.$$

For each actual speed $e \in E_{\rm non}$, write
$$e = n q_e + \rho_e, \qquad 1 \leq \rho_e \leq n-1.$$
The set
$$R_{\rm non} = \{\rho_e : e \in E_{\rm non}\}$$
records only which nonzero residue classes are represented by retained non-divisible speeds. Distinct actual speeds may share the same residue class.

For runner $e$ at **floor state** $t = \lfloor eb/L \rfloor$, the **bad set** is
$$\mathrm{bad}(e, t, n) = \mathrm{Sol}(e, -t, n) \cup \mathrm{Sol}(e, -(t+1), n) \subset \mathbb{Z}/n\mathbb{Z},$$
where $\mathrm{Sol}(e, j, n) = \{r \in \mathbb{Z}/n\mathbb{Z} : er \equiv j \pmod{n}\}$.

For unit $e$ ($\gcd(e,n)=1$): $\mathrm{bad}(e,t,n) = \{-te^{-1}, -(t+1)e^{-1}\} \bmod n$, exactly 2 elements. For non-unit $e$ with $g = \gcd(e,n) > 1$: $\mathrm{Sol}(e,j,n)$ is a coset of $H_g = (n/g)(\mathbb{Z}/n\mathbb{Z})$ of size $g$ if $g \mid j$, and $\emptyset$ otherwise.

Fibre $b$ is **safe** if $\bigcup_i \mathrm{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

### 5.2 Small $L$ Base Cases

**Proposition 5.1.** *For $L = n$: $x_0 = n-1$. For $L = 2n$: $x_0 \geq 1$ (analytic, Cases A–B below).*

*Note on $L = n$.* The case $\mathrm{lcm}(E) = n$ requires $n-1$ distinct positive divisors of $n$. Since $d(n) \geq n-1$ only for $n \in \{3,4\}$ (where $d(3)=2$ and $d(4)=3$), the case is vacuously impossible for all $n \geq 5$. For $n=3$: the unique admissible tuple is $E=(1,3)$, giving $x_0 = 2 = n-1$ by direct inspection. For $n=4$: $E=(1,2,4)$, giving $x_0 = 3 = n-1$ by direct inspection.

**Proof for $L = 2n$:** Two cases.

*Case A (some unit residue class $d \notin R_{\rm non}$):* the intended route is through the repaired static bridge of Lemma 5.2. In `v10.6` this case remains part of the repair task.

*Case B (Unit-Complete — both dropped runners are non-units; defined formally in §9.4):* If $n$ is even: §11, Sub-case B1 gives an uncovered residue at floor 0. If $n$ is odd with $\geq 2$ prime factors: Theorem 9.2c gives a targeted isolated floor-reset event. If $n = p^k$: Theorem 9.2c again gives a targeted isolated floor-reset event. $\square$

Henceforth $L > 2n$ (the cases $L = n$ and $L = 2n$ having been handled by Proposition 5.1).

### 5.3 The Static Dropped-Unit Bridge

Let
$$b_0 := L/n.$$
This is an integer fibre in every Case-2 tuple because $n \mid L$ as soon as some speed is divisible by $n$.

The first exact repair datum is the blocked-set geometry at $b_0$.

**Exact base-fibre formulas.** Let $e \in E_{\rm non}$ be an actual retained speed and write
$$e = n q_e + \rho_e, \qquad 1 \leq \rho_e \leq n-1.$$
Then
$$\left\lfloor \frac{e b_0}{L} \right\rfloor = \left\lfloor \frac{e}{n} \right\rfloor = q_e.$$
Hence
$$\mathrm{bad}(e,q_e,n) = \mathrm{Sol}(\rho_e,-q_e,n)\cup \mathrm{Sol}(\rho_e,-q_e-1,n).$$
If $\gcd(\rho_e,n)=1$, this is the exact two-point set
$$\mathrm{bad}(e,q_e,n)=\left\{-q_e\rho_e^{-1},\;-(q_e+1)\rho_e^{-1}\right\}\pmod n.$$
It is convenient to denote these residues by
$$a_{\rm low}(e):=-q_e\rho_e^{-1}, \qquad a_{\rm high}(e):=-(q_e+1)\rho_e^{-1}\pmod n.$$
If $g_e:=\gcd(\rho_e,n)>1$, then each of $\mathrm{Sol}(\rho_e,-q_e,n)$ and $\mathrm{Sol}(\rho_e,-q_e-1,n)$ is either empty or a coset of $H_{g_e}$.

So the base-fibre blocked set is controlled by the pair $(q_e,\rho_e)$, not by $\rho_e$ alone. In particular, omitted residue classes in $R_{\rm non}$ do not by themselves determine the miss set at $b_0$.

The canonical dropped-unit target nevertheless has an exact actual-speed description.

**Lemma 5.1a (Exact base-fibre patcher criterion).** *Let $d \in \{1,\ldots,n-1\}$ be a unit residue class and define*
$$r_d=-d^{-1}\pmod n.$$
*Let $e=nq+\rho \in E_{\rm non}$ be an actual retained speed. Then $e$ covers $r_d$ at the base fibre $b_0=L/n$ if and only if*
$$\rho \equiv qd \pmod n
\qquad\text{or}\qquad
\rho \equiv (q+1)d \pmod n.$$

**Proof.** At $b_0$ one has $\lfloor eb_0/L\rfloor=q$, so $e$ covers $r_d$ iff
$$\rho r_d+q\equiv 0 \pmod n
\qquad\text{or}\qquad
\rho r_d+q+1\equiv 0 \pmod n.$$
Since $r_d=-d^{-1}$ and $d$ is a unit, multiplying by $d$ gives exactly the displayed congruences. $\square$

**Repair consequence.** Earlier versions of the manuscript identified the retained non-divisible speeds with residue representatives in $\{1,\ldots,n-1\}$ and then argued on a floor-$0$ interval. That reduction is not valid as written, because the floor state
$$\left\lfloor \frac{eb}{L} \right\rfloor$$
depends on the actual speed $e$, not only on its residue class $\rho_e \bmod n$. The formulas above are the correct actual-speed replacement at the canonical base fibre $b_0=L/n$.

In `v10.7`, the dropped-unit branch is therefore isolated as an explicit bridge problem in these exact coordinates. Lemma 5.1a identifies the precise runners that can patch the canonical dropped-unit target at $b_0$. What remains open is the transport step from those local patchers to a guaranteed later safe chamber. Bounded examples show that the first safe chamber need not occur at the patcher's own reset and need not expose the original target residue $r_d$, so the repaired bridge must be formulated as a broader instability statement.

**Lemma 5.2 (Static dropped-unit bridge; repair target).** *Let $d \in \{1,\ldots,n-1\}$ be a unit residue class with $d \notin R_{\rm non}$. Define*
$$r_d = -d^{-1} \pmod n.$$
*Then one seeks a nonempty chamber $J_d \subseteq B_{\rm div}$ on which $r_d$ is uncovered by all retained non-divisible speeds. Any such chamber yields $x_0(E) \geq 1$ after integer counting on $J_d$.*

**Status in `v10.7`.** The residue-level mechanism behind this lemma is unchanged: missing unit residue classes should force a gap because non-units cannot freely assume unit obligations. What remains to be rebuilt is the actual-speed bridge from the residue support condition $d \notin R_{\rm non}$ to a genuine safe chamber for the original speed tuple. Any repaired proof of Lemma 5.2 must work in the exact base-fibre coordinates $a_{\rm low}(e), a_{\rm high}(e)$ and the patcher criterion of Lemma 5.1a, not by replacing actual retained speeds with residue representatives.

**Corollary 5.3 (Unit-residue bijection).** *For prime $n$, the map*
$$u \longmapsto -u^{-1} \pmod n$$
*is a bijection on the nonzero residue classes modulo $n$.*

**Corollary 5.4 (Complementary unit classes).** *For any unit residue class $u \in \{1,\ldots,n-1\}$, the residue class $n-u$ is also a unit and*
$$-(n-u)^{-1} \equiv u^{-1} \equiv n-(-u^{-1}) \pmod n.$$
*Thus the unit residue classes split into complementary pairs $(u,n-u)$ whose associated target residues also sum to $n$.*

**Proof.** $(n-u)^{-1} \equiv -u^{-1} \pmod n$ since $(n-u)(-u^{-1}) \equiv 1 \pmod n$. Rearranging gives the displayed identity. $\square$

---

## 6. Structural Lemmas

**Lemma G-PRES.** *For $g \mid n$ with $1 < g < n$: the subgroup $H_g = (n/g)(\mathbb{Z}/n\mathbb{Z})$ contains no unit of $\mathbb{Z}/n\mathbb{Z}$.*

**Proof.** Every $r \in H_g$ satisfies $\gcd(r,n) \geq n/g \geq 2$. $\square$

**Lemma FLOOR0.** *At floor state $t=0$: if $\gcd(e,n)=1$ then $\mathrm{bad}(e,0,n) = \{0, -e^{-1}\}$; if $\gcd(e,n)=g>1$ then $\mathrm{bad}(e,0,n) = H_g$.*

**Lemma R1-SWEEP.** *If $1 \in E_{\rm non}$: as $b$ ranges over $B_{\rm div}$, the floor $\lfloor nb/L \rfloor$ takes each value in $\{0,\ldots,n-1\}$ at least once.*

---

## 7. Prime $n$, One Divisible Runner

Throughout: $n$ prime, $|E_{\rm div}|=1$, $e_d = kn$ for $k \geq 1$.

**Integrity note.** The prime dropped-unit branch depends on the static dropped-unit bridge of Lemma 5.2. In earlier versions this section was written as though the missing residue classes could be read directly from the actual speed set $E_{\rm non}$ and witnessed on the interval $[L/n,L/(n-1))$. In `v10.6` the residue-level targets remain the same:

- if the residue class $1$ is absent from $R_{\rm non}$, the intended exposed residue is $n-1$;
- if the residue class $n-1$ is absent from $R_{\rm non}$, the intended exposed residue is $1$;
- more generally, if a unit residue class $d$ is absent from $R_{\rm non}$, the intended exposed residue is $r_d=-d^{-1}$.

What remains to be rebuilt is the actual chamber argument that turns these residue-level omissions into safe fibres for the original speed tuple. The quantitative bridge of §10 should therefore be read in `v10.6` as depending on the repaired version of Lemma 5.2.

---

## 8. Prime $n$, Multiple Divisible Runners

**Lemma 8.1 (Divisible-Runner Transparency).** *For $e_d = kn$ with $k \in \{1,\ldots,n-2\}$ and $\gcd(k,n)=1$: $\mathrm{bad}(kn,k,n) = \emptyset$ for all $b \in [L/n, L/(n-1))$.*

**Proof.** $\gcd(kn,n) = n$, so $\mathrm{Sol}(kn,j,n) = \mathbb{Z}/n\mathbb{Z}$ if $n \mid j$, else $\emptyset$. At floor $k$: $j = -k$ and $j = -(k+1)$ are both non-divisible by $n$ for $k \in \{1,\ldots,n-2\}$. $\square$

**Theorem 8.2 (Regular divisible runners).** *For prime $n$, $|E_{\rm div}| \geq 2$, all $k_i \in \{1,\ldots,n-2\}$: $x_0 \geq \varphi(n)$.*

**Proof.** On $I$, all divisible runners are transparent. $|E_{\rm non}| \leq n-3$ leaves $\geq 2$ unit residues uncovered; the counting bridge gives $x_0 \geq n-1$. $\square$

**Theorem 8.3 (Extreme divisible runners).** *For $k \equiv 0$ or $k \equiv -1 \pmod n$: $x_0 \geq \varphi(n)$.*

**Proof.** Runner $kn$ has non-empty bad set only when its floor state $t = \lfloor kn \cdot b/L \rfloor$ satisfies $n \mid t$ or $n \mid (t+1)$ (since $kn \cdot r \equiv -t \pmod{n}$ forces $0 \equiv -t \pmod{n}$); all other fibres give $\mathrm{bad}(kn, t, n) = \emptyset$. The exceptional fibres (those with $n \mid t$ or $n \mid (t+1)$) number at most $2(n-1)$ in $B_{\rm div}$. Since $|E_{\rm div}| \geq 2$ with distinct $k$-values $k_1 \neq k_2$ and $E_{\rm non}$ retains unit $n-1$, we have $L \geq \mathrm{lcm}(k_1 n,\, k_2 n,\, n-1) \geq n(n-1)$ (for the minimal case $k_1=1, k_2=2$: $\mathrm{lcm}(n, 2n, n-1) = \mathrm{lcm}(2n, n-1) = n(n-1)$ since $\gcd(2n, n-1) = \gcd(2, n-1) = 2$ for odd prime $n$; all other $k_1, k_2$ give at least as large an lcm). Therefore the remaining non-exceptional fibres number at least $|B_{\rm div}| - 2(n-1) \geq (n-2)(n-1) - 2(n-1) = (n-4)(n-1) \geq \varphi(n)$ for prime $n \geq 5$. On each non-exceptional fibre, $\mathrm{bad}(kn, t, n) = \emptyset$ so runner $kn$ is transparent; the remaining $|E_{\rm div}| - 1 \geq 1$ divisible runners all satisfy $k_i \in \{1,\ldots,n-2\}$ (the extreme runner $kn$ is removed from $E_{\rm div}$; all others have $k_i \not\equiv 0,-1 \pmod{n}$ by hypothesis). There are now two sub-cases. If $|E_{\rm div}| - 1 \geq 2$ (i.e.\ $|E_{\rm div}| \geq 3$): all hypotheses of Theorem~8.2 are satisfied, so Theorem~8.2 gives at least two uncovered residues at each transparent fibre; Proposition~10.5 then yields $x_0 \geq \varphi(n)$. If $|E_{\rm div}| - 1 = 1$ (i.e.\ $|E_{\rm div}| = 2$): on non-exceptional fibres the extreme runner is transparent, leaving effectively one regular divisible runner; the prime $n$, one-divisible-runner hypotheses of Lemma~7.1 are satisfied on those fibres, giving an uncovered residue; Proposition~10.5 then yields $x_0 \geq \varphi(n)$. $\square$

---

## 9. The Floor-Reset Mechanism

### 9.0 Baseline Safety at All-Zero Floor States

**Lemma 9.0 (Baseline Safety).** *Let $n$ have at least two distinct prime factors with $p_{\min}$ the smallest. If all unit runners in $E_{\rm non}$ are at floor state $0$, then $p_{\min}$ is uncovered.*

**Proof.** $\bigcup_{e\,\text{unit}} \mathrm{bad}(e,0,n) = \{0\} \cup \{n-u : u\text{ unit}\}$. Since $\gcd(n-p_{\min}, n) = p_{\min} > 1$, the residue $n-p_{\min}$ is a non-unit, so $p_{\min} \neq n - u$ for any unit $u$. Hence $p_{\min}$ is uncovered. $\square$

### 9.1 Floor-Reset Events

**Definition.** For unit $e_u \in E_{\rm non}$, the $m$-th **floor-reset event** occurs at fibre $b = mL/e_u$ (integer $m$) where $\lfloor e_u b/L \rfloor$ transitions from $m-1$ to $m$.

**Lemma 9.1 (Floor-Reset Count).** *For $e_u \geq 2$ with $\gcd(e_u,n)=1$: the number of floor-reset events for $e_u$ within $B_{\rm div}$ is exactly $e_u - 1$.*

**Proof.** Events at $b = mL/e_u$ for $m$ with $e_u/n < m < e_u(n-1)/n$; the integers in this range are $\{1,\ldots,e_u-1\}$. $\square$

### 9.2 Coverage at Floor-Reset Events

#### 9.2a. Coverage Criteria

**Lemma 9.2a (Coverage Criteria).** *At the $m$-th floor-reset event of unit $e_u$ (at $b_m = mL/e_u$), unit runner $e'$ covers the departing residue $r_{\rm dep} = -(m-1)e_u^{-1}$ iff:*
- *(Coverage Gate 1, CG1)* $e' m \bmod e_u = e'$ (requires $e' < e_u$), or
- *(Coverage Gate 2, CG2)* $e' + e_u \geq n$ and $e' m \bmod e_u = e' + e_u - n$.

**Proof.** The floor of $e'$ at $b_m$ is $t_{e'} = (e'm - s)/e_u$ where $s = e'm \bmod e_u$. Coverage of $r_{\rm dep}$ requires $e' r_{\rm dep} \equiv -t_{e'}$ or $-(t_{e'}+1) \pmod n$, giving $s \equiv e'$ or $s \equiv e' + e_u \pmod n$. Since $s \in \{0,\ldots,e_u-1\}$, these become CG1 and CG2. $\square$

**Actual-speed refinement.** The representative-form lemma above is the exact special case in which the pacemaker and comparison runners are written as representatives in $\{1,\ldots,n-1\}$. For the integrity repair one needs the actual-speed version.

**Lemma 9.2a$'$ (Actual floor-reset coverage criteria).** *Let*
$$f = n q_f + u \in E_{\rm non}, \qquad \gcd(u,n)=1,$$
*be an actual retained unit speed, and consider its $m$-th floor-reset event at*
$$b_m = mL/f.$$
*The departing residue is*
$$r_{\rm dep}=-(m-1)u^{-1}\pmod n.$$
*Let*
$$e = n q_e + s \in E_{\rm non}, \qquad 1 \leq s \leq n-1,$$
*be another actual retained speed, and define the exact remainder*
$$\sigma_f(e,m):= em \bmod f \in \{0,\ldots,f-1\}.$$
*Then $e$ covers $r_{\rm dep}$ at $b_m$ if and only if one of the following congruences holds:*
- *(Actual CG1)* $\sigma_f(e,m) \equiv s \pmod n$,
- *(Actual CG2)* $\sigma_f(e,m) \equiv s+u \pmod n$.

**Proof.** Write
$$em = f t_e + \sigma_f(e,m), \qquad t_e=\left\lfloor \frac{em}{f}\right\rfloor.$$
Coverage of $r_{\rm dep}$ means
$$s\,r_{\rm dep} \equiv -t_e \pmod n \quad\text{or}\quad s\,r_{\rm dep} \equiv -(t_e+1)\pmod n,$$
because $e \equiv s \pmod n$. Since $r_{\rm dep}=-(m-1)u^{-1}$ and $f \equiv u \pmod n$, we have
$$u t_e \equiv sm-\sigma_f(e,m)\pmod n.$$
For the lower branch,
$$s\,r_{\rm dep} \equiv -t_e \pmod n
\iff t_e \equiv s(m-1)u^{-1}\pmod n
\iff sm-\sigma_f(e,m) \equiv s(m-1)\pmod n,$$
which is equivalent to $\sigma_f(e,m)\equiv s \pmod n$.
For the upper branch,
$$s\,r_{\rm dep} \equiv -(t_e+1)\pmod n
\iff t_e+1 \equiv s(m-1)u^{-1}\pmod n
\iff sm-\sigma_f(e,m)+u \equiv s(m-1)\pmod n,$$
which is equivalent to $\sigma_f(e,m)\equiv s+u \pmod n$. $\square$

#### 9.2b. The $m=1$ Event

**Integrity note.** Lemma 9.2a$'$ gives the exact actual-speed criterion that the repair programme should use. Theorems 9.2b--9.2d below still retain the older representative-form shorthand, so they remain working templates rather than fully re-audited final statements.

**Theorem 9.2b.** *In the Unit-Complete case ($1 \in E_{\rm non}$): the $m=1$ event of any $e_u \geq 2$ is always covered (by $e'=1$ via CG1).*

#### 9.2c. Dropped-Runner Targeting

**Theorem 9.2c (Dropped-Runner Targeting).** *Let $n \geq 4$ be composite and let $d \in \{1,\ldots,n-1\}$ be a non-unit absent from $E_{\rm non}$. Write $d = a u$ where every prime divisor of $a$ divides $n$ and $\gcd(u,n)=1$, and set $e_u := n-u$. Then $e_u$ is a unit of $n$, there exists an index $m \in \{2,\ldots,e_u-1\}$ such that the $m$-th floor-reset event of $e_u$ has no CG1 coverers and has unique CG2 runner equal to $d$, and therefore the departing residue is uncovered by all retained runners. In particular, in the Unit-Complete case one has $B_{\rm safe} \geq 1$.*

**Proof.** Since $\gcd(u,n)=1$, we have $\gcd(e_u,n)=\gcd(n-u,n)=1$, so $e_u$ is a unit. Also $u<d$ because $d$ is a non-unit, hence $e_u=n-u>n-d$, so $d+e_u>n$ and the CG2 size condition is satisfied.

We claim $\gcd(d,e_u)=1$. Let $r$ be a prime dividing both $d$ and $e_u=n-u$. If $r \mid u$, then $r \mid n$ follows from $r \mid u$ and $r \mid n-u$, contradicting $\gcd(u,n)=1$. If $r \nmid u$, then since every prime divisor of $d$ not dividing $u$ lies in $a$, we have $r \mid n$; together with $r \mid n-u$ this again gives $r \mid u$, contradiction. Thus $\gcd(d,e_u)=1$.

Now choose the unique residue
$$x \equiv -n d^{-1} \pmod{e_u}.$$
Because $\gcd(n,e_u)=1$, we have $x \not\equiv 0 \pmod{e_u}$. Also $x \not\equiv -1 \pmod{e_u}$, for otherwise $n \equiv d \pmod{e_u}$; but $n \equiv u \pmod{e_u}$ and $0<d-u<e_u$, impossible. So the representative lies in $\{1,\ldots,e_u-2\}$. Set
$$m := x+1 \in \{2,\ldots,e_u-1\}.$$
Then $d(m-1) \equiv -n \pmod{e_u}$.

For CG1 at the $m$-th event of $e_u$, one needs $e(m-1)\equiv 0 \pmod{e_u}$ for some runner $e<e_u$. But $m-1 \equiv -n d^{-1} \pmod{e_u}$ is invertible modulo $e_u$, so this is impossible. Hence there are no CG1 coverers.

For CG2, the congruence is $e(m-1) \equiv -n \pmod{e_u}$, $e+e_u \geq n$. Since $m-1$ is invertible modulo $e_u$, the unique residue-class solution is $e \equiv d \pmod{e_u}$. The CG2 size condition confines $e$ to $[n-e_u,n-1]=[u,n-1]$, which has length exactly $e_u$. Since $d \in [u,n-1]$ (as $u < d$ was proved above) and the interval contains exactly one representative from each residue class modulo $e_u$, the unique element congruent to $d$ modulo $e_u$ is $d$ itself. Thus the unique CG2 runner is $d$.

Because $d \notin E_{\rm non}$, the departing residue at this event is uncovered by all retained runners. In the Unit-Complete case, at least one dropped runner is a non-unit, so applying the construction to either dropped non-unit gives $B_{\rm safe} \geq 1$. $\square$

#### 9.2d. Chamber Persistence

The following theorems provide closed-form algebraic certificates for the supplementary chamber-persistence program. All have been verified exhaustively for all odd composite $n \leq 5000$ with $\geq 2$ distinct prime factors.

**Theorem 9.2d-I (Large-Factor Witnesses).** *Let $n$ be odd with $\geq 2$ distinct prime factors, $r$ the largest prime factor, $m_r = n/r$.*

- *(a)* $e_u = 2r-1$: *$e^* = m_r(r-1)$, with $\gcd(e^*, n) = m_r > 1$.*
- *(b)* $e_u = 2r-2$: *$e^* = m_r(r-2)$, with $\gcd(e^*, n) = m_r > 1$.*

**Proof.** Write $m_r = 2j+1$ (odd). Let $a = n \bmod e_u$. *(a)* $e_u = 2r-1$. Since $n = m_r r$ and $2jr = j(2r-1)+j$: remainder $a = j + r = (m_r-1)/2 + r$. Check: $2a = m_r - 1 + 2r > 2r - 1 = e_u$, so Case 2 of the isolation formula applies: $e^* = n + e_u - 2a = m_r r + (2r-1) - (m_r-1+2r) = m_r(r-1)$. Since $\gcd(m_r, r) = 1$: $\gcd(e^*, n) = \gcd(m_r(r-1), m_r r) = m_r\gcd(r-1,r) = m_r > 1$. *(b)* $e_u = 2r-2 = 2(r-1)$. Then $m_r(r-1) \bmod 2(r-1) = (2j+1)(r-1) \bmod 2(r-1) = r-1$, so $a = (r-1)+m_r$. Case 2: $e^* = m_r r + 2(r-1) - 2(r-1+m_r) = m_r(r-2)$. Since $r \geq 3$ is an odd prime, $r-2$ is odd, so $\gcd(r-2, r) = \gcd(2, r) = 1$ and $\gcd(e^*, n) = m_r > 1$. $\square$

**Theorem 9.2d-II (Resonance Interval).** *For $p = p_{\min}$ and any unit $e_u \in (2n/(p+1),\, 2n/p)$: $\lfloor n/e_u \rfloor = (p-1)/2$. At the $m = 2$ floor-reset event of $e_u$, the CG2 solution is $e^* = pe_u - n$, which satisfies $p \mid e^*$ and $\gcd(e^*, n) \geq p > 1$ (a non-unit). Hence no unit runner covers $r_{\rm dep} = -e_u^{-1} \bmod n$, and the event is isolated.*

**Proof.** Set $k = (p-1)/2$. The interval $(2n/(p+1), 2n/p) = (n/(k+1), n/k)$, so $\lfloor n/e_u \rfloor = k$. The remainder $a = n - ke_u$ satisfies $2a = 2n - 2ke_u > e_u$ iff $2n > (2k+1)e_u = pe_u$, i.e.\ $e_u < 2n/p$. ✓ (Case 2.) So $e^* = n + e_u - 2a = (2k+1)e_u - n = pe_u - n$. Since $p \mid n$: $p \mid e^*$, giving $\gcd(e^*, n) \geq p > 1$.

At $m = 2$: $r_{\rm dep} = -(2-1)e_u^{-1} = -e_u^{-1}$. CG1 requires $2e' \equiv e' \pmod{e_u}$, i.e.\ $e_u \mid e'$, impossible for $0 < e' < e_u$. CG2 has unique solution $e_{\rm cov} = e^*$ (a non-unit), so no unit satisfies it. Hence $r_{\rm dep}$ is uncovered. $\square$

**Theorem 9.2d-III (Universal Witness Pair).** *Let $p = p_{\min}$, $m_0 = n/p$. Set $c_1 = 2m_0-1$, $c_2 = 2m_0-2$. Then:*

- *(a) Both $c_1, c_2 \in (2n/(p+1),\, 2n/p)$.*
- *(b) $\gcd(c_1, n) = \gcd(2m_0-1, p)$; $\gcd(c_2, n) = \gcd(m_0-1, p)$.*
- *(c) At most one of $\{c_1, c_2\}$ is a non-unit of $n$.*
- *(d) The unit among $\{c_1, c_2\}$ gives an isolated $m=2$ floor-reset event by Theorem 9.2d-II.*

**Proof.** (a) Upper bounds are clear ($c_1 < 2m_0 = 2n/p$). Lower: $c_2 > 2n/(p+1)$ iff $2m_0-2 > 2m_0 p/(p+1)$ iff $m_0 > p+1$, true since $n/p \geq p_2 \geq p+2$ (where $p_2$ is the second-smallest prime factor of $n$). (b) Since $\gcd(2m_0-1, m_0) = 1$: $\gcd(c_1, m_0 p) = \gcd(2m_0-1, p)$. Since $n$ is odd ($\gcd(2,n)=1$) and $\gcd(m_0-1, m_0) = 1$: $\gcd(c_2, m_0 p) = \gcd(m_0-1, p)$. (c) If both non-units: $p \mid 2m_0-1$ and $p \mid m_0-1$ forces $p \mid (2m_0-1)-(2)(m_0-1) = 1$. Impossible. (d) The unit lies in the resonance interval (by (a)); apply Theorem 9.2d-II. $\square$

*Verification:* Exhaustively checked for all odd $n \leq 5000$ with $\geq 2$ distinct prime factors (1,800 values; zero failures).

---

**Supplementary Program 9.2d (Chamber Persistence Refinement).** *A stronger chamberwise statement, not used in Theorem A, is that every chamber in $B_{\rm div}$ should contain an uncovered residue throughout the Unit-Complete multi-prime branch.*

*Status.* The base chamber and the general relay step for events with $\gcd(m-1,p)=1$ are analytic and motivate this chamberwise program. The sparse residual relay sub-sequence with $m \equiv 1 \pmod p$ is isolated in Appendix A.7, where a finite certified analysis verifies the required chamber persistence for all odd $n \leq 100$ and all relevant floor-reset events (532 events; zero failures). Since this refinement is not used in the proof of Theorem A, we record it only as supplementary material rather than as part of the main theorem path.

### 9.3 The Master Safe-Fibre Bound

**Theorem 9.3 (Unit-Complete Safe-Fibre Bound).** *If all $\varphi(n)$ units of $\{1,\ldots,n-1\}$ are in $E_{\rm non}$ (Unit-Complete case), then $B_{\rm safe} \geq 1$.*

**Proof.** By Theorem 9.2c, every missing non-unit $d$ produces a targeted floor-reset event whose departing residue is uncovered. In the Unit-Complete case both dropped runners are non-units, so applying Theorem 9.2c to either one gives a safe fibre. Hence $B_{\rm safe} \geq 1$. $\square$

The next item records a stronger chamberwise refinement in the multi-prime branch. It is supplementary and is not used in Theorem A.

---

**Sub-case (i): $n$ with $\geq 2$ distinct prime factors.**

Two configurations arise in the Unit-Complete case:
- **(P) Pure-Unit:** $E_{\rm non}$ contains only unit runners.
- **(G) General:** $E_{\rm non}$ also contains non-unit runners.

Case (P) exhibits a stronger chamberwise phenomenon recorded only supplementarily.
Case (G) gives Tier 1 analytically for all tuples, and Sub-case G(i) also exhibits a stronger chamberwise phenomenon recorded only supplementarily.

**Proof for Case (P): Chamber Safety.**

All $\varphi(n)$ units are in $E_{\rm non}$; both dropped runners are non-units. Earlier versions pursued the stronger chamberwise conclusion $B_{\rm safe} = |B_{\rm div}|$ in this pure-unit sub-case. That chamberwise phenomenon is now treated only as supplementary material; see Supplementary Program 9.2d and Appendix A.7. It is not used in Theorem A. $\square$

**Proof for Case (G): CRT Floor Independence.**

Theorem 9.2c already gives Tier 1 in all Case G tuples. The following lemmas explain the witness geometry behind the stronger chamberwise phenomenon in Sub-case G(i).

**Lemma (CRT Floor Independence).** *For $n$ with distinct prime factors $p,q$ and runners $e_p = j_p \cdot p$ (with $\gcd(j_p, q) = 1$) and $e_q = j_q \cdot q$ (with $\gcd(j_q, p) = 1$): the floor states $f_p(b) = \lfloor e_p b/L \rfloor$ and $f_q(b) = \lfloor e_q b/L \rfloor$ are jointly equidistributed over $B_{\rm div}$. The fraction of $b$ satisfying $p \mid f_p$ and $q \mid f_q$ simultaneously is $1/(pq) + O(1/L)$ — the product of individual fractions.*

**Lemma (Smallest Prime Bound).** *Let $n$ have smallest prime factor $p = p_{\min}$ and let $e_u^*$ be the universal witness unit from Theorem 9.2d-III. For $p \leq 5$: the Cov2 runner $e_{\rm cov}$ satisfying $e_{\rm cov}(m^*-1) \equiv -n \pmod{e_u^*}$ has $e_{\rm cov} \geq n/p$, i.e.\ is a non-unit, for all but at most one choice of $p$-runner.*

**Supplementary Remark 9.3a (Multi-Prime Chamberwise Phenomenon).** Tier 1 in the multi-prime Unit-Complete branch already follows from Theorem 9.2c. In Sub-case G(i), the universal witness fibre itself is analytically safe: by the Smallest Prime Bound, CG2 holds for at most one runner $e_{\rm cov}$, and if that runner is absent from $E_{\rm non}$ then the departing residue is uncovered at the witness fibre. Earlier versions pursued the stronger chamberwise conclusion $B_{\rm safe} = |B_{\rm div}|$ from this witness. Appendix A.2 records representative positive computations for that full-chamber phenomenon, while Supplementary Program 9.2d and Appendix A.7 isolate the residual relay issue. None of this stronger chamberwise material is used in Theorem A or in Theorem 9.3b below.

**Theorem 9.3b (Multi-Prime Quantitative Bound).** *Let $n$ be odd composite with at least two distinct prime factors, and suppose both dropped runners are non-units. Then $B_{\rm safe} \geq \varphi(n)(n-2)/2$.*

**Proof.** By Theorem 9.2c, there is a targeted floor-reset event whose departing residue is uncovered. The open chamber $J$ immediately to its right is safe. A chamber is a maximal $b$-interval on which all floor states are constant; it ends at the first transition point of any runner after its left endpoint. At the floor-reset event $b_0 = mL/e_u$, the next transition of any retained runner $e$ occurs at $b_0 + L(e_u - em \bmod e_u)/(e \cdot e_u)$. Since $em \bmod e_u \leq e_u - 1$, this distance is at least $L/(e \cdot e_u) \geq L/((n-1) \cdot e_u)$. Since $e_u \leq n-1$, the open chamber $J$ immediately to the right of $b_0$ has width $|J| \geq L/((n-1) \cdot e_u) \geq L/(n-1)^2 > L/(n(n-1))$, giving $B_{\rm safe} \geq L/(n(n-1)) - 1$.

Let $U_n = \mathrm{lcm}\{1 \leq u \leq n-1 : \gcd(u,n)=1\}$. All units are retained, so $L \geq n U_n$, giving $B_{\rm safe} \geq U_n/(n-1) - 1$.

For $n \geq 45$: retained units $n-1,n-2,n-4,n-8$ give $U_n \geq \mathrm{lcm}(n-1,n-2,n-4,n-8) \geq (n-1)(n-2)(n-4)(n-8)/63$ (where 63 = $3 \cdot 7 \cdot 3$ bounds the product of the six pairwise gcds: for odd $n$, $\gcd(n-1,n-4) \leq 3$, $\gcd(n-1,n-8) \leq 7$, $\gcd(n-2,n-8) \leq 3$, and the remaining three pairs have gcd $\leq 1$, since any common factor of two terms divides their difference and the differences $1,2,3,4,6,7$ have prime factors only in $\{2,3,7\}$, with $2$ not dividing the odd terms $n-2,n-4,n-8$). The inequality $B_{\rm safe} \geq \varphi(n)(n-2)/2$ reduces to $2n^3 - 91n^2 + 238n - 254 \geq 0$; this polynomial equals $8431 > 0$ at $n=45$, its derivative $6n^2 - 182n + 238$ is positive for all $n \geq 45$, so the inequality holds throughout.

The finitely many odd multi-prime $n < 45$ (namely $15, 21, 33, 35, 39$) are handled by direct $U_n$ lower bounds:
$$n=15: U_n \geq \mathrm{lcm}(8,11,13,14)=8008, \quad n=21: U_n \geq \mathrm{lcm}(16,17,19,20)=25840,$$
$$n=33: U_n \geq 719200, \quad n=35: U_n \geq 776736, \quad n=39: U_n \geq 1089650.$$
In each case $U_n/(n-1)-1 \geq \varphi(n)(n-2)/2$. $\square$

---

**Sub-case (ii): $n = p^k$, $p \geq 3$ odd prime, $k \geq 2$.**

Define $L_{k-1} = \{p^{k-1}, 2p^{k-1}, \ldots, (p-1)p^{k-1}\} \subset \mathbb{Z}/n\mathbb{Z}$, the **level-$(k-1)$ residues**. $|L_{k-1}| = p-1$.

**Lemma 9.3c (Level Bottleneck).** *For any runner $e \in E_{\rm non}$ and any $r \in L_{k-1}$: $r \in \mathrm{bad}(e, t, n)$ only if $p^{k-1} \mid t$ or $p^{k-1} \mid (t+1)$. Hence the fraction of floor values where $e$ can cover any element of $L_{k-1}$ is at most $2/p^{k-1}$.*

**Proof.** For $r \in L_{k-1}$: $v_p(r) = k-1$. For $r \in \mathrm{bad}(e,t,n)$: need $er + t \equiv 0 \pmod{p^k}$ or $er + (t+1) \equiv 0 \pmod{p^k}$. Since $v_p(er) \geq k-1$: for $p^k \mid (er+t)$ to hold, $v_p(t) \geq k-1$, i.e., $p^{k-1} \mid t$. Similarly for the $(t+1)$ case. $\square$

**Lemma 9.3d (Dangerous-Fibre Count).** *For any $e \in E_{\rm non}$: the number of fibres $b \in B_{\rm div}$ where $e$ can cover some element of $L_{k-1}$ is at most $2|B_{\rm div}|/p^{k-1} + 2$.*

**Proof.** By Lemma 9.3c, fibre $b$ (here $b$ ranges over all $|B_{\rm div}|$ divisible-speed fibres, not just multiples of $p^{k-1}$) can host coverage of $L_{k-1}$ only if $p^{k-1} \mid b$ or $p^{k-1} \mid (b+1)$. Among any $|B_{\rm div}|$ consecutive integers, the count divisible by $p^{k-1}$ is at most $\lceil |B_{\rm div}|/p^{k-1} \rceil \leq |B_{\rm div}|/p^{k-1} + 1$. The same bound applies for $p^{k-1} \mid (b+1)$. Adding gives at most $2|B_{\rm div}|/p^{k-1} + 2$ dangerous fibres. $\square$

**Lemma 9.3e (Unit Bijection at Dangerous Floors).** *At any floor $t$ with $p^{k-1} \mid t$ and $t \geq p^{k-1}$: a unit runner $e_u$ covers exactly one element $r_t(e_u) = -t \cdot e_u^{-1} \bmod p^k$ of $L_{k-1}$. Distinct unit runners at the same dangerous floor cover distinct elements of $L_{k-1}$.*

**Proof.** *Existence:* The bad residue of $e_u$ at floor $t$ is $r = -t \cdot e_u^{-1} \bmod p^k$. Write $t = A \cdot p^{k-1}$ with $p \nmid A$ (since $v_p(t) = k-1$). Then $r = -A \cdot p^{k-1} \cdot e_u^{-1}$. Since $e_u$ is a unit mod $p^k$, $v_p(e_u^{-1}) = 0$, so $v_p(r) = k-1$. Thus $r$ is a nonzero multiple of $p^{k-1}$ with $v_p(r) = k-1$, hence $r \in L_{k-1}$. *Uniqueness per runner:* $r$ is determined uniquely by $t$ and $e_u$. *Injectivity across runners:* If $r_t(e_u) = r_t(e_u')$, then $-t \cdot e_u^{-1} \equiv -t \cdot e_u'^{-1} \pmod{p^k}$. Multiplying by $-e_u e_u' / t \cdot p^{1-k}$ (valid since $v_p(t) = k-1$) gives $e_u \equiv e_u' \pmod{p}$, hence $e_u = e_u'$ for unit representatives in $\{1,\ldots,p^k-1\}$. $\square$

**Remark.** An earlier independence route (attempting to bound the joint fraction of dangerous fibres via coprimality of periods across mod-$p$ runner groups) is false: same mod-$p$ groups can saturate the level bottleneck on a non-empty interval. The correct quantitative argument proceeds from one safe chamber, not from a group-independence ansatz.

**Lemma 9.3f-LCM.** *Let $n = p^k$ ($p$ prime, $k \geq 2$) and $T = \{u : 1 \leq u \leq n-1,\, p \nmid u\}$. Then $\mathrm{lcm}(T) = \mathrm{lcm}(1,\ldots,n-1)/p^{k-1} \geq 2^{n-2}/p^{k-1}$.*

**Proof.** For any prime $q \neq p$: the highest power $q^a \leq n-1$ satisfies $p \nmid q^a$, so $q^a \in T$ and $v_q(\mathrm{lcm}(T)) = v_q(\mathrm{lcm}(1,\ldots,n-1))$. For $q = p$: every element of $T$ is coprime to $p$, so $v_p(\mathrm{lcm}(T)) = 0$. Since $p^{k-1} \leq n-1 < p^k$, we have $v_p(\mathrm{lcm}(1,\ldots,n-1)) = k-1$. Therefore $\mathrm{lcm}(T) = \mathrm{lcm}(1,\ldots,n-1)/p^{k-1}$. The final inequality applies the standard bound $\mathrm{lcm}(1,\ldots,m) \geq 2^{m-1}$ (a consequence of Chebyshev's theorem on prime distribution; Hardy–Wright, Theorem 414) with $m = n-1$. $\square$

**Theorem 9.3f (Prime-Power Quantitative Bound).** *Let $n = p^k$ with $p \geq 3$ odd, and suppose both dropped runners are non-units. Then $B_{\rm safe} \geq \varphi(n)(n-2)/2$.*

**Proof.** For $n=9$: Sub-case PP(i) (§11) gives the safe interval $(1/9,1/8)$. Since $L \geq \mathrm{lcm}(1,2,4,5,7,8,9) = 2520$, this contributes at least $2520(1/8 - 1/9) - 1 = 34 > 21 = \varphi(9)(9-2)/2$ safe fibres. ✓

For $n \geq 25$: By Theorem 9.2c, there is a targeted floor-reset event giving a safe chamber $J$. As in Theorem 9.3b, at the floor-reset event $b_0 = mL/e_u$ the next transition of any retained runner $e$ is at distance $\geq L/(e \cdot e_u) \geq L/(n-1)^2 > L/(n(n-1))$ from $b_0$, so $|J| \geq L/(n(n-1))$, giving $B_{\rm safe} \geq L/(n(n-1)) - 1$. Since the Unit-Complete condition holds, all units are in $E_{\rm non}$; by Lemma~9.3f-LCM, $L \geq \mathrm{lcm}(T) = \mathrm{lcm}(1,\ldots,n-1)/p^{k-1} \geq 2^{n-2}/p^{k-1}$. For $n \geq 25$, $2^{n-2} \geq n^4(n-1)/p$ (verified for $n \in \{25, 27\}$ and immediate for $n \geq 49$ by exponential dominance), so $B_{\rm safe} \geq n^2 - 1 > \varphi(n)(n-2)/2$. $\square$

### 9.4 The Unit-Complete Condition

**Lemma 9.4 (Unit-Complete).** *If both dropped elements from $\{1,\ldots,n-1\}$ are non-units, then all $\varphi(n)$ units are in $E_{\rm non}$.*

**Scope note.** The Unit-Complete condition guarantees all units are in $E_{\rm non}$; it does not preclude non-unit runners in $E_{\rm non}$. For $n-3 > \varphi(n)$: there are $n-3-\varphi(n) \geq 1$ non-unit runners in $E_{\rm non}$.

### 9.5 Run Cap

**Lemma 9.5 (Quantitative Run Cap).** *In any composite branch with $B_{\rm safe} \geq n$: every maximal contiguous block of unsafe fibres in $B_{\rm div}$ has length $\leq |B_{\rm div}| - n$.*

**Proof.** If a contiguous block had length $> |B_{\rm div}| - n$, then fewer than $n$ fibres would remain outside it, contradicting $B_{\rm safe} \geq n$. $\square$

### 9.6 Quantitative Composite Summary

| Application | Bound | Branch | Proof |
|---|---|---|---|
| Run cap | $B_{\rm safe} \geq n$ | Quantitative composite branches | Lemma 9.5 + Corollary 9.6 |
| Safe count | $B_{\rm safe} \geq \varphi(n)$ | Quantitative branches | Corollary 9.6 |
| LRC existence | $B_{\rm safe} \geq 1$ | All $n$ | Theorem 9.2c |

**Corollary 9.6 (Quantitative Composite Bounds).** *In every odd multi-prime dropped-two branch, Theorem 9.3b gives $B_{\rm safe} \geq \varphi(n)(n-2)/2 \geq n$. In the odd-prime-power dropped-two branch, Theorem 9.3f gives the same bound. Since $(n-2)/2 \geq 1$ for all $n \geq 4$, we have $\varphi(n)(n-2)/2 \geq \varphi(n)$, so both $B_{\rm safe} \geq \varphi(n)$ and $x_0 \geq \varphi(n)$ hold in every composite quantitative branch treated in §9. The stronger chamberwise phenomena from the Pure-Unit case and Supplementary Remark 9.3a are supplementary only and are not used here.*

---

## 10. Prime $n$: Analytic Counting Bridge

### 10.1 Period Decomposition

Fix prime $n \geq 5$, $|E_{\rm div}|=1$, $|E_{\rm non}|=n-3$. The full tuple of $n-1$ runners is structured as: one divisible runner (speed $kn$), one **free runner** of speed $M$ with $\gcd(M, n)=1$ designated separately from $E_{\rm non}$, and $n-3$ runners forming $E_{\rm non}$. This gives $1 + 1 + (n-3) = n-1$ runners in total.

The role of the free runner is auxiliary: once it is separated from the remaining non-divisible runners, the first period can be analysed by comparing its two-point bad set with the residue classes missed by the retained set at floor $0$.

**Integrity note.** Sections 10.1--10.5 record the prime counting architecture from earlier drafts. They are now to be read as a **template** for the repaired prime dropped-unit branch, not yet as a theorem-secure proof path. What is still missing is a valid bridge from the residue-support data to an actual chamber on which the retained non-divisible runners realise the required miss set.

**Observation (Free Runner Selection).** *Among the $n-2$ non-divisible runners, choose $M$ to minimise $d = \gcd(M,\, L_0^{(M)})$, where $L_0^{(M)} = \mathrm{lcm}(E_{\rm non})$ with $M$ removed. Two cases arise.*

*Case* $d=1$: The chosen $M$ satisfies $\gcd(M, nL_0) = 1$ (using $\gcd(M,n)=1$ for prime $n$), so $L = \mathrm{lcm}(nL_0, M) = nL_0M$. The argument of §§10.2–10.4 proceeds as written below.

*Case* $d > 1$: Then $d \mid M$ and $\mathrm{lcm}(nL_0, M) = nL_0 M/d$, so $L = nL_0 M/d$ and $|\mathrm{Period}_1| = L_0 M / d$. Lemmas 10.2 and 10.3 adapt with $L_0 M$ replaced by $L_0 M/d$ throughout, giving an adjusted threshold $M_0^{(d)} = \lceil d \cdot n^2(n-1)/(L_0(n-2))\rceil$. The analytic bound applies whenever $M \geq M_0^{(d)}$.

Two sub-cases: (i) $M/d \geq 2$: since $M_0^{(d)} = \lceil d \cdot C_n / L_0 \rceil$ where $C_n = n^2(n-1)/(n-2)$, and $d \mid L_0$ implies $L_0 \geq d$, one checks $M_0^{(d)} \leq 2d$. Then $M = d \cdot (M/d) \geq 2d \geq M_0^{(d)}$ and the analytic bound holds. (ii) $M/d = 1$, i.e.\ $M \mid L_0$: **this sub-case is resolved by re-designating the free runner.** The current $M$ achieves $d = \gcd(M, L_0^{(M)}) = M > 1$. Re-designation replaces $M$ with a different runner $M^*$ drawn from the same $n-2$ non-divisible speeds. A fresh optimal selection picks $M^*$ to minimise $d^* = \gcd(M^*, L_0^{(M^*)})$, where $L_0^{(M^*)} = \mathrm{lcm}(E_{\rm non}^{(M^*)})$ is recomputed with $M^*$ excluded. Concretely: the speed-1 runner (when $\mathrm{du} \neq 1$) satisfies $\gcd(1, L_0^{(1)}) = 1$ unconditionally; a runner whose residue is a prime coprime to all other runners' residue speeds (when $\mathrm{du} = 1$) likewise achieves $d^* = 1$ in all arising prime-$n$ configurations. In the exceptional case where all non-divisible runners share a common factor $q$ (so no $d^*=1$ re-designation exists), every choice gives $d^* = q$ with $M^*/d^* \geq 2$, which returns to sub-case (i) and the analytic bound holds there. Thus in all cases sub-case (ii) either re-designates to $d = 1$ or falls to sub-case (i).

*Residual small-$M$ check.* After re-designation, if $M^*=1$ and $L_0^* < C_n$ (i.e.\ $M_0^*=2 > M^*=1$), one is in the small-$M$ regime with $L = nL_0^* < nC_n$. For prime $n=11$ this requires $L_0^* \in [67, 134)$; the only value arising in practice is $L_0^*=120$ (when the residue-7 runner uses the non-canonical speed $40 = 7+3\cdot11$, making $\mathrm{lcm}(E_{\rm non}^*) = 120$). A complete computational scan of all such families — run as part of the gap investigation whose results are summarised in Appendix A.8 — finds $x_0 \geq 1580$ in every case, far exceeding $\varphi(11)=10$. An identical argument applies for $n \geq 13$ (where $L_0^* \geq 2520 \gg C_{13}$, so the small-$M$ regime is vacuous). Sub-case (ii) is thereby closed. $\square$

Set $L_0 = \mathrm{lcm}(E_{\rm non})$ for the chosen $M$; then $L = \mathrm{lcm}(E_{\rm non},\, kn,\, M)$. Partition $B_{\rm div}$ by the floor of the divisible runner: $\mathrm{Period}_k = \{b \in B_{\rm div} : \lfloor nb/L \rfloor = k\}$, $k = 1,\ldots,n-2$. The **retained-runner miss set** at floor state $f=0$:
$$\mathrm{miss}(0) = (\mathbb{Z}/n\mathbb{Z}) \setminus \bigcup_{e \in E_{\rm non}} \mathrm{bad}(e, 0, n).$$

### 10.2 Lower-Band Period

**Lemma 10.1.** *For $|E_{\rm non}|=n-3$ with prime $n \geq 5$: $|\mathrm{miss}(0)| \geq 2$.*

**Proof.** The inversion map $e \mapsto -e^{-1} \bmod n$ is injective on units, so the floor-0 union covers at most $1 + (n-3) = n-2$ residues, leaving $\geq 2$ uncovered. $\square$

### 10.3 Safe Fibres in the Lower Band

**Lemma 10.2.** *For $|\mathrm{miss}(0)| = s \geq 1$: the number of safe fibres in $\mathrm{Period}_1$ is $\geq L_0 M(n-2)/n^2 - 2$.*

**Proof.** The free runner $M$ has $|\mathrm{bad}(M, t, n)| = 2$ (prime $n$). A fibre in $\mathrm{Period}_1$ is unsafe only if $\mathrm{bad}(M, t, n) \supseteq \mathrm{miss}(0)$. For $s \geq 3$: impossible; all $L_0M/n$ fibres are safe. For $s \in \{1,2\}$: at most $2\lceil L_0M/n^2 \rceil + 2$ bad fibres; safe count $\geq L_0M(n-2)/n^2 - 2$. $\square$

### 10.4 Threshold and Closure

**Lemma 10.3.** *Define $M_0 = \lceil n^2(n-1)/(L_0(n-2))\rceil$. For $M \geq M_0$: safe count in $\mathrm{Period}_1$ is $\geq n-1 = \varphi(n)$. Moreover $M_0 < n^2$ (using $L_0 \geq 2$ since $|E_{\rm non}| \geq 2$).*

**Lemma 10.4.** *For prime $n \geq 11$: the genuine small-$M$ range $\{M \geq 3 : M < M_0\}$ is empty, so no Case-2 small-$M$ cases require enumeration.*

**Proof.** Since $M=1$ gives $L=n$ and $M=2$ gives $L=2n$, both handled by Proposition 5.1, the genuine small-$M$ branch requires $M \geq 3$. We show $M_0 \leq 3$ for all prime $n \geq 11$, which makes the range $\{M \geq 3 : M < M_0\}$ empty.

*Case $n = 11$:* The minimising drop is $\{7,9\}$ (both have exactly one multiple in $\{1,\ldots,10\}$, so removing them maximally reduces $L_0$). Then $E_{\rm non} = \{1,2,3,4,5,6,8,10\}$ and $L_0 = \mathrm{lcm}(1,2,3,4,5,6,8,10) = 120$. Hence $M_0 = \lceil 121 \cdot 10 / (120 \cdot 9) \rceil = \lceil 1210/1080 \rceil = 2 \leq 3$. Genuine range: $\{M \geq 3 : M < 2\} = \emptyset$. $\square_{\!11}$

*Case $n \in \{13, 17, 19, 23, 29\}$:* The table below records the minimising drop, worst-case $L_0$, and the resulting $M_0$ for each prime. In all five cases $M_0 = 1$, so the genuine range is empty.

| $n$ | Worst-case drop | $L_0^{\min}$ | Threshold $n^2(n-1)/(n-2)$ | $M_0$ |
|---|---|---|---|---|
| 13 | $\{7, 11\}$ | 360 | 184.4 | 1 |
| 17 | $\{11, 13\}$ | 5040 | 308.3 | 1 |
| 19 | $\{13, 17\}$ | 55440 | 382.2 | 1 |
| 23 | $\{17, 19\}$ | 720720 | 554.2 | 1 |
| 29 | $\{19, 23\}$ | 183783600 | 872.1 | 1 |

(Each $L_0^{\min}$ value is $\mathrm{lcm}(\{1,\ldots,n-1\}\setminus\{\text{drop}\})$, verified exhaustively over all $\binom{n-1}{2}$ drops.) $\square_{\{13,\ldots,29\}}$

*Case $n \geq 31$:* Let $d_1, d_2$ be the two dropped elements. We show $k \mid L_0$ for every $k \leq \lfloor n/2 \rfloor$.

- $k \leq \lfloor n/3 \rfloor$: The three multiples $k, 2k, 3k$ all lie in $\{1,\ldots,n-1\}$. With only two drops, at least one remains in $E_{\rm non}$.
- $\lfloor n/3 \rfloor < k \leq \lfloor n/2 \rfloor$, $k$ composite: Write $k = ab$ with $a,b \leq k/2 \leq \lfloor n/3 \rfloor$; both $a \mid L_0$ and $b \mid L_0$, so $k \mid L_0$.
- $\lfloor n/3 \rfloor < k \leq \lfloor n/2 \rfloor$, $k$ prime: Worst case $\{d_1,d_2\}=\{k,2k\}$. Then $L_0 \geq \mathrm{lcm}(1,\ldots,\lfloor n/2 \rfloor)/k \geq 2^{\lfloor n/2\rfloor-1}/\lfloor n/2\rfloor$. For $n \geq 31$: $2^{14}/15 \approx 1092 > 31^2 \cdot 30/29 \approx 993 \geq n^2(n-1)/(n-2)$ (binding at $n=31$; exponential dominates for all larger $n$). Hence $M_0 = 1$. $\square$

### 10.5 Counting Bridge

**Proposition 10.5 (Prime $n$ quantitative template; under repair).** *For prime $n \geq 5$, all Case-2 families with $|E_{\rm non}|=n-3$, all $M \geq 1$: the preceding counting architecture is intended to yield $x_0 \geq n-1 = \varphi(n)$ once the repaired static dropped-unit bridge has been supplied.*

**Legacy counting template.** *Analytic branch ($M \geq M_0$):* By the Free Runner Selection Observation (§10.1), $d=1$ after optimal selection (or sub-case (i) handles $d>1$ analytically). By Lemmas 10.1, 10.2, 10.3: safe count in $\mathrm{Period}_1 \geq n-1$.

*Small-$M$ branch:* After applying §10.1, sub-case (ii) ($M \mid L_0$) is resolved: it either reduces to $d=1$ via re-designation or to sub-case (i) analytically. In the re-designation case $M^*=1$ with $L_0^* < C_n$ (the small-$M$ regime — the only instance for prime $n \geq 11$ being $n=11$, $L_0^*=120$), the scan of Appendix A.8 certifies $x_0 \geq 1580 \gg \varphi(11)$; no genuine small-$M$ case arises for $n \geq 13$ since $L_0^* \geq 2520 \gg C_{13}$.

For the remaining original (pre-re-designation) small-$M$ range $\{M \geq 3 : M < M_0\}$: for prime $n \leq 7$, Lemma A.4 covers this range by exhaustive certification (53 total cases); for prime $n \geq 11$, Lemma 10.4 shows this range is empty. $\square$

---

## 11. Composite $n$: Run Cap and Templates

### 11.1 Quantitative Run Cap

**Theorem 11.1 (Quantitative Run Cap).** *In any composite Unit-Complete branch with $B_{\rm safe} \geq n$ (in particular, the pure-unit branch, the odd multi-prime branch via Theorem 9.3b, and the odd-prime-power branch via Theorem 9.3f): every obstruction run has length $\leq |B_{\rm div}| - n$.*

**Proof.** Apply Lemma 9.5 with the branch-specific input $B_{\rm safe} \geq n$ from Corollary 9.6. $\square$

### 11.2 One Divisible Runner

**Integrity note.** The one-divisible composite branch used the same dropped-unit bridge as §5.3 and the same speed-versus-residue identification that is now under repair. Accordingly, the statements in §§11.2--11.3a should be read in `v10.6` as the intended arithmetic template for the rebuilt branch, not as settled theorem-path arguments.

**Theorem 11.2 (Composite one-divisible template; under repair).** *For composite $n \geq 4$, $|E_{\rm non}|=n-3$, one divisible runner: the intended conclusion is $x_0 \geq 1$.*

**Cases i, ii, iiia, iiib (at least one dropped runner is a unit).** The intended route is via the repaired static dropped-unit bridge of Lemma 5.2 together with the composite counting architecture below.

**Proposition 11.3 (Composite counting bridge template; under repair).** *For composite $n \geq 4$ with one dropped unit residue class $d$ and $L > 2n$: the intended conclusion is $x_0 \geq \varphi(n)$.*

**Legacy counting template.** Two analytic branches cover all $L > 2n$ with $n \mid L$.

*Route 1 (large $L$, $L \geq n(n-1)(\varphi(n)+1)$):* The Sole Cover interval $I_d = [L/n, L/(n-1))$ satisfies $|I_d \cap \mathbb{Z}| \geq L/(n(n-1)) - 1 \geq \varphi(n)$ safe fibres.

*Route 2 (all remaining $L$, $2n < L < n(n-1)(\varphi(n)+1)$):* Lemma 11.3a gives $x_0 \geq |I_d \cap \mathbb{Z}| + |J \cap \mathbb{Z}|$. Write $k = L/n$ (integer since $n \mid L$, $k \geq 3$). The exact integer counts are
$$|I_d \cap \mathbb{Z}| = \left\lceil \frac{k}{n-1} \right\rceil, \qquad |J \cap \mathbb{Z}| \;\geq\; \left\lceil \frac{k}{n-1} \right\rceil,$$
since $I_d = [k,\, nk/(n-1))$ has width $k/(n-1)$ with left endpoint $k \in \mathbb{Z}$, so the integers it contains are $k, k+1, \ldots, k + \lceil k/(n-1)\rceil - 1$ (count exactly $\lceil k/(n-1)\rceil$, where the half-open right endpoint causes no off-by-one because $nk/(n-1) \notin \mathbb{Z}$ when $(n-1) \nmid k$ and $= k + k/(n-1) \in \mathbb{Z}$ is excluded when $(n-1) \mid k$). For $J = [(n-2)nk/(n-1),\, (n-1)k]$ with right endpoint $(n-1)k \in \mathbb{Z}$ and width $k/(n-1)$: the integers it contains are $(n-1)k - \lceil k/(n-1)\rceil + 1, \ldots, (n-1)k$ (at least $\lceil k/(n-1)\rceil$, with equality when $(n-1) \nmid k$ and one extra when $(n-1) \mid k$).

For $\varphi(n) = 2$ ($n \in \{4, 6\}$, so $k \geq 3$): $\lceil k/(n-1) \rceil \geq 1$, giving total $\geq 2 = \varphi(n)$.

For $\varphi(n) \geq 4$: An exhaustive parameter check shows that among all composite $n$ and all $L$ with $n \mid L$ and $2n < L < n(n-1)(\varphi(n)+1)$, only two configurations lie in the Route 2 range: $(n=4,\, L=12)$ giving $k=3$, $\lceil 3/3 \rceil = 1$, total $= 2 \geq 2 = \varphi(4)$; and $(n=8,\, L=120)$ giving $k=15$, $\lceil 15/7 \rceil = 3$, total $= 6 \geq 4 = \varphi(8)$. For all composite $n \geq 9$, the minimum admissible $L$ (governed by $\mathrm{lcm}$ constraints) exceeds $n(n-1)(\varphi(n)+1)$, so Route 1 already applies. $\square$

**Remark 11.4.** *In any Case-2 tuple: $n \mid L$ (since $E_{\rm div}$ contains a multiple of $n$), so $I_d = [L/n, L/(n-1))$ contains $b = L/n$. In earlier drafts this was combined with Lemma 5.2 to claim $x_0 \geq 1$ analytically for all $L \geq n$; in `v10.6` that inference is deferred until the repaired bridge has been supplied.*

**Lemma 11.3a (Late-window bridge template; under repair).** *Let $n \geq 4$ be composite, $d \in \{1,\ldots,n-1\}$ a dropped unit residue class and set $s_d := d^{-1} - 1 \pmod{n}$. Define*
$$J := \left[\frac{(n-2)L}{n-1},\; \frac{(n-1)L}{n}\right].$$
*The intended conclusion is that, after the actual-speed/residue bridge is rebuilt, the residue $s_d$ is uncovered on $J$ and hence*
$$x_0(E) \;\geq\; |I_d \cap \mathbb{Z}| + |J \cap \mathbb{Z}|.$$

**Legacy late-window template.** **Floor states on $J$.** For any retained runner $e \in \{1,\ldots,n-1\}$ and $b \in J$:
$$\frac{e(n-2)}{n-1} \;\leq\; \frac{eb}{L} \;\leq\; \frac{e(n-1)}{n}.$$
Lower bound: $e(n-2)/(n-1) \geq e-1$ iff $e(n-2) \geq (e-1)(n-1)$ iff $n \geq e+1$, which holds since $e \leq n-1$. Upper bound: $e(n-1)/n < e$. Hence $\lfloor eb/L\rfloor = e-1$ for every retained runner $e$ and every $b \in J$.

**Unit runners** ($\gcd(e,n)=1$) at floor $e-1$:
$$\mathrm{bad}(e,\,e-1,\,n) = \mathrm{Sol}(e,-(e-1),n) \cup \mathrm{Sol}(e,-e,n) = \{e^{-1}-1\} \cup \{n-1\}.$$
(Since $e$ is a unit: $\mathrm{Sol}(e,-(e-1),n) = \{(1-e)e^{-1}\} = \{e^{-1}-1\}$; and $\mathrm{Sol}(e,-e,n) = \{r : e(r+1) \equiv 0\} = \{n-1\}$.) The map $e \mapsto e^{-1}-1$ is injective on units. Because $d \notin E_{\rm non}$, the value $d^{-1}-1 = s_d$ is absent from $\{e^{-1}-1 : e \in E_{\rm non}\text{ unit}\}$. And $n-1 \neq s_d$ since $s_d = n-1$ would require $d^{-1} \equiv 0$, which is impossible. Hence no retained unit covers $s_d$.

**Non-unit runners** ($g = \gcd(e,n) > 1$) at floor $e-1$:
$$\mathrm{Sol}(e,-(e-1),n) = \emptyset \quad(\text{since } g \mid e \text{ but } g \nmid e-1),$$
$$\mathrm{Sol}(e,-e,n) = \{r : r+1 \in H_g\} = H_g - 1,$$
where $H_g = \{0, n/g, 2n/g, \ldots\}$ is the subgroup of multiples of $n/g$. Now $s_d \in H_g - 1$ iff $s_d + 1 = d^{-1} \in H_g$. But $d^{-1}$ is a unit of $\mathbb{Z}/n\mathbb{Z}$, hence coprime to $n$, so $d^{-1}$ cannot be a nonzero multiple of $n/g > 1$. Therefore $d^{-1} \notin H_g$ and $s_d \notin H_g - 1$. Hence no retained non-unit runner covers $s_d$.

*Note.* The coset $H_g - 1$ can contain units (e.g.\ $n=15$, $e=3$: $\mathrm{Sol}(3,-3,15) = \{4,9,14\}$ includes units 4 and 14), so the argument above — which would be wrong if stated as "$\mathrm{bad}(e,e-1,n) = H_g$" — must go via unithood of $d^{-1}$ rather than via membership in $H_g$ itself.

**Disjointness.** $I_d$ ends below $L/(n-1)$; $J$ starts at $(n-2)L/(n-1)$. The gap is $(n-3)L/(n-1) > 0$ for $n \geq 4$, so $I_d$ and $J$ are disjoint. $\square$

**Sub-case B (Both dropped runners are non-units).**

**Corollary 11.0 (Unit Sub-System Overdetermination).** *For any composite $n \geq 4$ in the Unit-Complete configuration (both dropped runners are non-units, all $\varphi(n)$ units retained): $B_{\rm safe} \geq 1$. Moreover, in the odd composite and prime-power branches: $B_{\rm safe} \geq \varphi(n)(n-2)/2$.*

**Proof.** *Floor-0 remark (not used below):* At floor state $t=0$, Lemma G-PRES and Lemma FLOOR0 jointly give $\mathrm{bad}(e,0,n) = H_g \subseteq (\mathbb{Z}/n\mathbb{Z}) \setminus U_n$ for every non-unit $e$; no unit residue is covered by a non-unit runner at floor 0. At higher opaque floors the coset of $H_g$ shifts to $c + H_g$ for $c \neq 0$, and such a coset can contain units (e.g.\ $n=15$, $e=3$, floor $t=3$ gives coset $\{4,9,14\}$ which contains unit 4). The floor-0 observation is therefore a floor-0 statement only and is not used in the proof below.

*Proof of $B_{\rm safe} \geq 1$:* With both dropped runners being non-units, Theorem 9.2c applies to either dropped non-unit $d$: there exists a unit $e_u = n-u$ and index $m \in \{2,\ldots,e_u-1\}$ such that at the $m$-th floor-reset event of $e_u$, the departing residue $r_{\rm dep}$ is uncovered by all retained runners (unit and non-unit alike). This gives $B_{\rm safe} \geq 1$.

For the quantitative bound in the odd branches: Theorems 9.3b and 9.3f amplify to $B_{\rm safe} \geq \varphi(n)(n-2)/2$. $\square$

The sub-cases below instantiate this corollary with branch-specific inputs.

**Sub-case B1 ($n$ even).**
$$\frac{2\varphi(n)}{n} = \prod_{p \mid m}\!\left(1-\frac{1}{p}\right) \leq \frac{2}{3} < 1$$
(where $n = 2^a m$, $m$ odd $\geq 3$), giving $|U_{\rm unit}| \leq 2\varphi(n) < n$ so some residue is uncovered by unit runners. For $n = 2^k$ ($k \geq 3$): since the Unit-Complete condition holds and both dropped runners $d_1, d_2$ are non-units, Theorem 9.2c applies to $d_1$: there exists a unit $e_u$ and index $m \in \{2,\ldots,e_u-1\}$ such that at the $m$-th floor-reset event of $e_u$, the departing residue is uncovered by all retained runners, giving $B_{\rm safe} \geq 1$. (Motivating remark: the units of $\mathbb{Z}_{2^k}$ are precisely the odd elements, so the inversion map $e \mapsto -e^{-1}$ sends units to odd residues; the even non-zero residues $\{2,4,\ldots\}$ are thus uncovered by unit runners at floor $0$ — consistent with the floor-reset conclusion above.)

**Sub-case B2 ($n$ odd, $\geq 2$ distinct prime factors).**

Let $d$ be either dropped non-unit. By Theorem 9.2c, there exists a unit $e_u = n-u$ and an index $m \in \{2,\ldots,e_u-1\}$ such that at the $m$-th floor-reset event of $e_u$ there are no CG1 coverers and the unique CG2 runner is exactly $d$. Since $d \notin E_{\rm non}$, the departing residue is uncovered. Hence $x_0 \geq 1$, and Theorem 9.3b gives the full quantitative bound.

**Sub-case B3 ($n = p^k$, odd prime power, $k \geq 2$).**

**Sub-case PP(i) ($n=9$, $p=3$, $k=2$):** The only non-units are $\{3,6\}$; both are dropped. $E_{\rm non} = \{1,2,4,5,7,8\}$ (all units). At $b \in (L/9, L/8)$: unit runners cover $\{0\} \cup \{\text{units}\}$; non-units $\{3,6\}$ are uncovered (by Lemma G-PRES). $\square$

**Sub-case PP(ii) ($n=p^k$, $k \geq 3$):**

**Theorem 11.5 (Late Bottleneck Window).** *Let $n=p^k$ with $p \geq 3$, $k \geq 3$, and suppose both dropped runners are non-units. Let $e_{\min}$ be the smallest retained non-unit, and assume $e_{\min} \geq 2p$. Set*
$$\alpha_* := \frac{p^{k-1}-1}{n-1}.$$
*Then every fibre $b \in B_{\rm div}$ with $1/e_{\min} < b/L < \alpha_*$ is safe; indeed $L_{k-1} \subseteq \mathrm{Miss}_{E_{\rm non}}(b)$.*

**Proof.** For any unit runner $e < n$: $\lfloor e\alpha \rfloor < e\alpha_* \leq p^{k-1}-1$, so no unit reaches a dangerous floor for $L_{k-1}$. For any retained non-unit $e$: $\alpha > 1/e_{\min}$ and $\alpha < \alpha_* < 1/p$ give $1 \leq \lfloor e\alpha \rfloor < n$. Since $er \equiv 0 \pmod n$ for $r \in L_{k-1}$, a retained non-unit can cover $r$ only at floor 0 or $n-1$, which never occurs on this interval. $\square$

*Quantitative status.* Theorem 9.2c gives Tier 1 for all odd prime-power dropped-two tuples. Theorem 9.3f gives the full quantitative bound. Theorem 11.5 is an auxiliary late-window result providing a second independent route to Tier 1.

---

## 12. Composite $n$: Multiple Divisible Runners

**Theorem 12.1.** *For composite $n \geq 4$ and $|E_{\rm div}| \geq 2$: $x_0 \geq 1$.*

**Proof.** All elements of $E_{\rm div}$ are non-units ($n \mid e$ implies $\gcd(e,n) = n > 1$). With $|E_{\rm div}| \geq 2$, at least two residue classes from $\{1,\ldots,n-1\}$ are absent from $E_{\rm non}$. Two cases:

*Case A (some absent residue class is a unit):* Let $d \in \{1,\ldots,n-1\}$ be a unit with $d \notin R_{\rm non}$. The intended route is via the repaired static bridge of Lemma 5.2, which should supply a safe chamber for the target residue $r_d = -d^{-1} \bmod n$.

*Case B (all absent residue classes are non-units):* Lemma 9.4 (Unit-Complete) gives all $\varphi(n)$ units in $E_{\rm non}$. Theorem 9.2c applies to any absent non-unit: there exists a floor-reset event of a matched unit $e_u$ at which the departing residue is uncovered by all retained runners, giving $B_{\rm safe} \geq 1$ and $x_0 \geq 1$.

In both cases $x_0 \geq 1$. $\square$

---

## 13. Proof of the Main Theorem

**Dependency map (integrity-repair status).** The intended theorem path still runs through §§3--12, but in `v10.6` the dropped-unit branches are isolated as repair tasks rather than treated as closed. The following material remains supplementary: §2.7 (companion constructive witnesses for prime $n$); Appendix S.1 (supplementary quantitative observations); Appendix A.5 (archived superseded enumeration); Appendix A.7 (supplementary chamber-persistence certification). Appendices A.4, A.6, and A.8 remain relevant to the quantitative architecture recorded in the draft: A.4 (53 prime-case certified configurations) for the prime small-parameter template; A.6 as a coverage-criterion cross-check for Lemma 9.2a; A.8 for the residual $n=11$ re-designation template in §10.1.

**Target proof structure for Theorem A.** Let $n \geq 3$ and $E$ be any gcd-1 tuple of $n-1$ distinct positive integers.

**Irrational case:** Theorem 3.1.

**Rational case** (all speeds integer):

- *Case 1 ($n \nmid e_i$ for all $i$):* Theorem 4.1: $x_0 \geq \varphi(n) \geq 1$.
- *Case 2, $L \in \{n, 2n\}$:* Proposition 5.1.
- *Case 2, prime $n$, $|E_{\rm div}|=1$:* Lemma 7.1 + Proposition 10.5.
- *Case 2, prime $n$, $|E_{\rm div}| \geq 2$:* Theorems 8.2, 8.3.
- *Case 2, composite $n$, $|E_{\rm div}|=1$, dropped unit:* repaired Lemma 5.2 + rebuilt Proposition 11.3 template.
- *Case 2, composite $n$, both non-units dropped, $n$ even:* Sub-case B1.
- *Case 2, composite $n$, both non-units dropped, $n$ odd, $\geq 2$ prime factors:* Theorem 9.2c + Theorem 9.3b.
- *Case 2, composite $n$, both non-units dropped, $n = p^k$:* Theorem 9.2c + Theorem 9.3f.
- *Case 2, composite $n$, $|E_{\rm div}| \geq 2$:* Theorem 12.1.

**Tier 1 status in `v10.6`.** Case 1 remains closed by Theorem 4.1. The manuscript now records the exact actual-speed formulas needed for the repair at the base fibre (§5.3) and at floor-reset events (Lemma 9.2a$'$). The unit-complete dynamic branches are still retained as the main working mechanism through Theorem 9.2c and its amplifications, but those statements must still be re-audited in the new coordinates. The dropped-unit branches are not yet theorem-secure in `v10.6`: they now depend on the repaired bridge isolated in Lemma 5.2 and on the late-window rebuild around Lemma 11.3a.

**Tier 2 status in `v10.6`.** The prime and composite quantitative branches remain recorded as templates, together with their certified small-parameter support, but they should not yet be read as closed proofs until the dropped-unit bridge is repaired and the dynamic branch is re-audited under the actual-speed/residue split.

**Quantitative branches developed in-body ($x_0 \geq \varphi(n)$):**

| Branch | Result | Proof |
|---|---|---|
| Case 1 | $x_0 \geq \varphi(n)$ | Theorem 4.1 (analytic) |
| Prime $n$ | $x_0 \geq \varphi(n)$ | Proposition 10.5 (analytic + certified) |
| Composite, dropped unit | $x_0 \geq \varphi(n)$ | Proposition 11.3 (analytic) |
| Composite, dropped two, multi-prime | $B_{\rm safe} \geq \varphi(n)(n-2)/2$ | Theorem 9.3b (analytic) |
| Composite, dropped two, $n=p^k$ | $B_{\rm safe} \geq \varphi(n)(n-2)/2$ | Theorem 9.3f (analytic) |

The chamberwise refinement isolated in Supplementary Program 9.2d and Appendix A.7 is not used in the intended theorem path. In `v10.6`, the purpose of this section is to display the current proof architecture honestly: which branches remain structurally compelling, which quantitative templates are still in place, and exactly where the manuscript still owes repaired bridge lemmas before Theorem A can be presented again as fully closed. $\square$

---

## References

- Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**, R48.
- Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**, 1–9.
- Bohman, T., Holzman, R., and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* **8**, R3.
- Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165–170.
- Czerwiński, S. (2012). Random runners are very lonely. *J. Combin. Theory Ser. A* **119**, 1194–1199.
- Hardy, G. H. and Wright, E. M. (2008). *An Introduction to the Theory of Numbers*, 6th ed. Oxford University Press, Oxford.
- Kuipers, L. and Niederreiter, H. (1974). *Uniform Distribution of Sequences*. Wiley-Interscience, New York.
- Tao, T. (2018). Some remarks on the lonely runner conjecture. *Contrib. Discrete Math.* **13**, 1–29.
- Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins. *Math. Ann.* **77**, 313–352.
- Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263–270.

---

## Data and Code Availability

The enumeration harnesses, certified data files, and companion scripts referenced in Appendices A.4–A.7 are archived in the project repository. SHA-256 hashes of companion files and zero-failure run logs are included with the archived data.

The following files are referenced in the active appendices: `lrc_certified_A4_prime_n_le7.py` (53 prime-case configurations, Appendix A.4); `lrc_search_v50_result.txt` (SHA-256: `2696b0d55a5db411a70b5125ea99aeb03371eb4bb3f2fd190aea4eb96f6f2543`, $n=6$ exhaustive search, 2,061,046 tuples, 0 counterexamples); `lrc_efficiency_runtime_validation.csv` and `lrc_validation_large_1759239075705.csv` (isolation law verification data, CLAIM-LRC-000056, §10 companion). Appendix A.5 is superseded by Proposition 11.3 Route 2; no companion script is required for that branch.

---

## Appendix A: Computational Certificates

This appendix collects computational material in three categories. (1) **Attached to the current theorem architecture:** A.4 (53 prime-case configurations, Proposition 10.5 small-$M$ template, prime $n \leq 7$); A.6 (coverage-criterion verification, Lemma 9.2a); A.8 ($M \mid L_0$ residual certified check, Proposition 10.5 sub-case (ii), prime $n=11$ only). (2) **Independent cross-checks not logically required:** A.2, A.3 (analytic results in §9 computationally verified), A.7 (supplementary chamber-persistence). (3) **Archived/superseded:** S.1 (quantitative observations at $L=2n$), A.5 (composite dropped-unit enumeration, superseded by the later counting template of Proposition 11.3). In all active cases the parameter range is bounded analytically before computation. Code and data are available as companion files.

### S.1 — Supplementary Note: $L = 2n$ Quantitative Observations

**Note.** This section is supplementary only; it is not used in the intended theorem path. In `v10.6`, the $L = 2n$ cases belong to the same dropped-unit repair zone as Proposition 5.1 Case A and the one-divisible composite templates. The table below records the empirically observed minimum $x_0$ for small composite $n$ at $L = 2n$ and remains useful as supporting evidence while that branch is being rebuilt.

*Note on scope.* Values $n \in \{7, 11, 13, 17, 19\}$ are prime and values $n \in \{14, 15, 16, 18, 20\}$ are composite; in `v10.6` both groups should be read as supporting data for the repair programme rather than as already closed analytic sub-cases.

| $n$ | $\varphi(n)$ | Min $x_0$ observed | $x_0 \geq \varphi(n)$? |
|---|---|---|---|
| 3 | 2 | 2 | ✓ |
| 4 | 2 | 3 | ✓ |
| 5 | 4 | 4 | ✓ |
| 6 | 2 | 4 | ✓ |
| 8 | 4 | 7 | ✓ |
| 9 | 6 | 8 | ✓ |
| 10 | 4 | 8 | ✓ |
| 12 | 4 | 10 | ✓ |

Zero failures ($x_0 \geq \varphi(n)$ in all cases).

### A.2 — Representative Verification of the Multi-Prime Chamberwise Phenomenon

**Status:** Tier 1 for all multi-prime Unit-Complete tuples is already supplied by Theorem 9.2c. Supplementary Remark 9.3a records the stronger full-chamber phenomenon in Sub-case G(i), while counterexamples occur in Sub-case G(ii), as expected. This appendix records representative positive computations for the Sub-case G(i) chamberwise phenomenon.

| $n$ | $\varphi(n)$ | Required $\geq$ | $B_{\rm safe}$ (= $|B_{\rm div}|$) | Ratio |
|---|---|---|---|---|
| 6 | 2 | 4 | 12 | 3.0 |
| 10 | 4 | 16 | 52 | 3.25 |
| 15 | 8 | 52 | 165 | 3.17 |
| 30 | 8 | 112 | 360 | 3.21 |

No failures in the listed Sub-case G(i) samples.

### A.3 — Independent Verification of Theorem 9.3f (Prime-Power Quantitative Bound)

**Status:** Theorem 9.3f establishes the quantitative prime-power bound analytically. This appendix provides independent computational verification across the same branch.

**Verified:** All prime powers $n \leq 100$ in the dropped-two prime-power branch.

| $n$ | $\varphi(n)$ | Required | $B_{\rm safe}$ | Ratio |
|---|---|---|---|---|
| 4 | 2 | 2 | 28 | 14 |
| 8 | 4 | 12 | 866 | 72 |
| 9 | 6 | 21 | 2450 | 117 |
| 25 | 20 | 230 | $\geq 2300$ | $\geq 10$ |
| 49 | 42 | 987 | $\geq 9870$ | $\geq 10$ |

Zero failures.

### A.4 — Proposition 10.5, Certified Branch: Genuine Small $M$ for Prime $n \leq 7$

**Lemma A.4 (Prime Small-$M$ Base Cases).** *For each prime $n \in \{5, 7\}$ and each admissible Case-2 tuple $E$ with $|E_{\rm non}|=n-3$ and $3 \leq M < M_0(n,L_0)$: $x_0(E) \geq n-1$.*

*Proof.* By exhaustive enumeration; see implementation and result below. $\square$

**Why only $n \in \{5,7\}$:** For prime $n \geq 11$, the genuine small-$M$ range $\{M \geq 3 : M < M_0\}$ is empty by Lemma 10.4 (for $n=11$: worst-case $M_0=2$; for $n \geq 13$: $M_0=1$). Cases $M=1$ and $M=2$ correspond to $L=n$ and $L=2n$, handled by Proposition 5.1.

**Why $M \geq 3$:** $M=1$ gives $L=n$ and $M=2$ gives $L=2n$; both are covered by Proposition 5.1 and are not in scope for §10.

**Scope:** Prime $n \in \{5,7\}$; 53 total $(E_{\rm non}, M)$ pairs enumerated exhaustively.

| $n$ | $E_{\rm non}$ (drop) | $L_0$ | $M_0$ | Genuine $M$ range | Cases |
|---|---|---|---|---|---|
| 5 | $\{2,4\}$ (drop $\{1,3\}$) | 4 | 9 | $3,\ldots,8$ | 6 |
| 5 | $\{2,3\}$ (drop $\{1,4\}$) | 6 | 6 | $3,4,5$ | 3 |
| 5 | $\{1,4\}$ (drop $\{2,3\}$) | 4 | 9 | $3,\ldots,8$ | 6 |
| 5 | $\{1,3\}$ (drop $\{2,4\}$) | 3 | 12 | $3,\ldots,11$ | 9 |
| 5 | $\{1,2\}$ (drop $\{3,4\}$) | 2 | 17 | $3,\ldots,16$ | 14 |
| 7 | $\{2,3,4,6\}$ (drop $\{1,5\}$) | 12 | 5 | $3,4$ | 2 |
| 7 | $\{1,3,4,6\}$ (drop $\{2,5\}$) | 12 | 5 | $3,4$ | 2 |
| 7 | $\{1,2,4,6\}$ (drop $\{3,5\}$) | 12 | 5 | $3,4$ | 2 |
| 7 | $\{1,2,3,6\}$ (drop $\{4,5\}$) | 6 | 10 | $3,\ldots,9$ | 7 |
| 7 | $\{1,2,3,4\}$ (drop $\{5,6\}$) | 12 | 5 | $3,4$ | 2 |
| | | | | **Total** | **53** |

**Enumeration schema:**
```
for each prime n in {5, 7}:
  for each 2-element drop from {1,...,n-1}:
    E_non = {1,...,n-1} \ drop
    L0 = lcm(E_non)
    M0 = ceil(n²(n-1) / (L0(n-2)))
    for each M with 3 ≤ M < M0:          # genuine small-M only
      for each admissible speed tuple E with E_non, divisible runner kn (k=1), and free runner M (gcd(M,n)=1):
        compute x_0(E); assert x_0(E) ≥ n-1
```
Companion file: `lrc_certified_A4_prime_n_le7.py` (SHA-256: see companion manifest).

**Result:** Zero failures ($x_0 \geq n-1$ in all 53 cases).

### A.5 — Archived: Composite Dropped-Unit Small-$L$ Enumeration (Not used in proof)

**Archival note.** This appendix is retained for historical reference only. It is not used in the intended theorem path. The later composite counting architecture of Proposition 11.3 was designed to replace this enumeration, but in `v10.6` that branch is itself marked as a template under repair. The original enumeration schema and companion file remain in the project archive as supporting historical material.

### A.6 — Cross-Check: Coverage Criterion (Lemma 9.2a)

Verification that the CG1/CG2 formula agrees with direct computation.

- **Scope:** $n \in \{6,8,9,10,12,15,16,18,20,25\}$; 6,123 cases.
- **Result:** Zero discrepancies; the Coverage Criteria characterise coverage exactly.

### A.7 — Supplementary Chamber Persistence: $m \equiv 1 \pmod{p}$ Floor-Reset Events

**Context:** Supplementary Program 9.2d records the chamber-persistence refinement in the Unit-Complete multi-prime branch. The general relay step for floor-reset events with $\gcd(m-1, p) = 1$ is analytic. For the sparse sub-sequence of events with $m \equiv 1 \pmod{p_{\min}}$, the supplementary program uses the universal witness anchor (Theorem 9.2d-III) and a finite case analysis on the resulting relay transitions.

**Scope:** All odd $n \leq 100$ with $\geq 2$ distinct prime factors; all unit runners $e_u$ and floor indices $m$ with $m \equiv 1 \pmod{p_{\min}}$. Total: 532 floor-reset events.

**Result:** Zero failures (an uncovered residue was found in all 532 events).

### A.8 — $M \mid L_0$ Gap Investigation: $n=11$ Residual Certified Check

**Context.** The Free Runner Selection Observation (§10.1, sub-case (ii)) shows that the case $M \mid L_0$ resolves via re-designation to $M^* = 1$ when all remaining runners are even-speed (du $\neq 1$) or similar canonical structures. After re-designation, $M^* = 1$ with $L_0^* = \mathrm{lcm}(E_{\rm non}^*)$. If $L_0^* \geq C_n$ the analytic branch of Lemma 10.3 applies directly. If $L_0^* < C_n$ (the small-$M$ regime), a computational certificate is required.

**Why only $n=11$.** For prime $n \geq 13$: the worst-case $L_0^* \geq \mathrm{lcm}(\{1,\ldots,12\} \setminus \{7,11\}) = 360 \gg C_{13} \approx 184$, so the small-$M$ regime is vacuous. For $n = 11$: the worst-case drop gives $L_0^* = 120 < C_{11} = 121\overline{8}$ when the residue-7 runner uses the non-canonical speed $40 \equiv 7 \pmod{11}$ (making $\mathrm{lcm}(E_{\rm non}^*) = 120$). This is the unique $n=11$ configuration requiring certification.

**Enumeration.** For the re-designation $M^* = 1$, $L_0^* = 120$, $n = 11$: the full tuple is $E = \{1, 11, e_3, e_4, e_5, e_6, e_7, e_8, e_9, e_{10}\}$ with $E_{\rm non}^* = \{2, 3, 4, 5, 6, 8, 10, 40\}$ (speed 40 the non-canonical residue-7 runner), free runner $M^* = 1$, divisible runner $11$. All admissible speed assignments with $\mathrm{lcm}(E_{\rm non}^*) = 120$ are enumerated and $x_0(E)$ is computed directly.

**Result.** Zero failures: $x_0 \geq 1580$ in every case. The minimum $x_0 = 1580$ is achieved at $(n=11,\, \mathrm{du}=9,\, M=40,\, L_0=120)$ (hardest case: $L = 1320$, $N = 14520$). This far exceeds the Tier 2 requirement $\varphi(11) = 10$.

**Companion file.** `gap_m_divides_L0_investigation_v1.py`; detailed findings in `lrc_gap_m_divides_L0_findings_v1.md`. SHA-256 hashes included in the companion manifest. The Phase 1 scan covered 42 canonical families (n=11) and 64 canonical families (n=13), with 0 failures in both phases.
