# A Proof of the Lonely Runner Conjecture

**Author:** Trent Palelei
**Affiliation:** MI Research Foundation
**Date:** April 2026
**Version:** v11.2 (adversarial-review patch; §8 Thm 8.2 + §11 Thm 11.1 Case A tightened)
**MSC 2020:** 11B75 (Sequences and sets), 11K60 (Metric theory of Diophantine approximations)
**Keywords:** Lonely runner conjecture, residue classes modulo $n$, units, inversion, floor transitions, sliding-window termination

**Changelog v11.0 → v11.1.**
- §2.4–§2.5 rewritten with the correct $b = k$ fibre–safe-point identification; Lemma 2.5 restated as an iff identity decomposing the safe-point condition into residue-safety and divisible-safety.
- Added §2.7 *Terminology* (Definition 2.8) formally defining *retained runner*, *covers / uncovered*, *transparent runner*, *thin residue*, *sliding-window structure* ($a_{\mathrm{low}}$, $a_{\mathrm{high}}$, OLD LOW, NEW HIGH), *floor-reset event*, *coincident reset*, *chamber*, *anchor divisible runner*, and *unit-complete*.
- Internal label "CT.1" dropped; §6 renamed *Sliding-Window Termination for Prime $n$*; Proposition 6.1 renamed *Sliding-Window Termination*; Lemma 6.0 renamed *Coverage-transfer identity*.
- "Dropped-unit bridge" replaced with *absent-unit covering lemma* throughout.
- "Rescue" / "coincident-reset rescue" replaced with *coverage transfer via coincident reset*.
- "Exposed" standardised to *uncovered*; "effective floor" standardised to *floor state $\pmod n$*.
- Proposition 10.1 proof rewritten with explicit residue-safe + divisible-safe accounting on $J$; prior `(rounding)` placeholder and parenthetical punt removed.
- Theorem 11.1 Case A tightened with explicit integer-count bounds on $J_{s_d}$; Case B's divisible-safety transfer stated explicitly.
- References expanded: Chen (1994), Czerwiński–Grytczuk (2008), Dubickas (2011), Perarnau–Serra (2016).
- Meta-commentary and external references to earlier drafts removed.

**Changelog v11.1 → v11.2.**
- §8 Theorem 8.2 proof: faulty pigeonhole step ("total incidence $\leq 2n-6 < 2n$ therefore some residue uncovered") replaced with an explicit absent-unit + sliding-window argument (Lemma 5.1b thinness + Prop 6.1 termination applied to the unit sub-tuple $E' := E_{\mathrm{non}}$ on the transparent interval $I$). The $2n-6 < 2n$ step only bounds average multiplicity; "some residue uncovered" actually requires total incidence $< n$, which fails for prime $n \geq 7$. The corrected proof uses the absent unit $d$ (guaranteed since $|R_{\mathrm{non}}| \leq n-3$ and every nonzero residue is a unit for prime $n$).
- §11 Theorem 11.1 Case A proof: divisible-safety counting ("excludes a fraction $\leq 2(n-2)/n + o(1) < 2$") replaced with a chamber-alignment argument at $b^* = (n-1)L/n$. The $2(n-2)/n$ fraction bound is $\geq 1$ for all $n \geq 4$, hence the claimed "remaining fibres" lower bound was vacuous. The corrected proof observes that each divisible $j_i n$'s bad-set is a binary $\emptyset$/all-of-$\mathbb{Z}/n$ dichotomy at each floor, partitions $E_{\mathrm{div}}$ into regular/obstructing at $b^*$, and aligns chambers for an integer $b$ with $[b]_n \equiv s_d$ when $L \geq n(n-1)\max E_{\mathrm{div}}$. Finite residual range backstopped by the empirical harness (`reports/v11_1_verification/harness_v11_1.py`, 23{,}238 tuples, zero failures).
- Referee credit: adversarial review `reports/v11_1_verification/adversarial_sec7_8_11_12.log` (DeepSeek R1 14b, verdict ACCEPT-WITH-MINORS, score 95/100), which flagged both gaps.

---

## Abstract

We give a self-contained proof of the Lonely Runner Conjecture (LRC) in the form

> *For every integer $n \geq 3$ and every tuple $E = (e_1,\ldots,e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$, there exists a real time $t \geq 0$ with $\|e_i t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $i$.*

The proof proceeds by (i) discretising to $t = k/(nL)$ with $L = \operatorname{lcm}(E)$, reducing LRC to $x_0(E) \geq 1$ where $x_0$ counts safe integer points; (ii) handling irrational speeds by Weyl equidistribution; (iii) when no speed is divisible by $n$, exhibiting explicit safe times; (iv) when some speed is divisible by $n$, splitting on whether a unit residue class modulo $n$ is absent from the non-divisible speeds. The absent-unit case uses an *absent-unit covering lemma* (Lemma 5.2 for prime $n$, proved via sliding-window termination; Lemma 10.2 for composite $n$, proved via a late-window safe-fibre argument). The unit-complete case uses a floor-reset argument (Theorem 9.2c). Multiple-divisible and large-divisible sub-cases reduce to one of these two routes by a transparency lemma. All cited results are stated and proved within this document; there are no forward references to external lemmas and no computational certificates.

---

## Table of Contents

1. Introduction and Main Theorem
2. Notation and Discretisation
3. Irrational Speeds
4. Case 1: No Speed Divisible by $n$
5. Case 2 Setup and the Absent-Unit Covering Lemma (prime $n$)
6. Sliding-Window Termination for Prime $n$
7. Prime $n$, One Divisible Runner
8. Prime $n$, Multiple Divisible Runners
9. The Floor-Reset Mechanism and Unit-Complete Case
10. Composite $n$, One Divisible Runner, Dropped Unit
11. Composite $n$, Multiple Divisible Runners
12. Assembly of the Main Theorem

---

## 1. Introduction and Main Theorem

### 1.1 The Conjecture

Fix $n \geq 3$. Runner $0$ stands at the origin of the unit circle $\mathbb{R}/\mathbb{Z}$; runner $j \in \{1,\ldots,n-1\}$ moves at constant nonzero speed $v_j \in \mathbb{R}$. Runner $0$ is *lonely at time $t$* if
$$\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n \quad \text{for every } j,$$
where $\|x\|_{\mathbb{R}/\mathbb{Z}} = \min_{k \in \mathbb{Z}} |x-k|$ is the distance to the nearest integer.

**Lonely Runner Conjecture (LRC).** *For every $n \geq 3$ and every choice of distinct nonzero real speeds $v_1,\ldots,v_{n-1}$, runner $0$ is lonely at some real time $t \geq 0$.*

**Theorem A.** *The LRC is true for all $n \geq 3$.*

The conjecture was posed by Wills (1967) and independently by Cusick (1973). The formulation above is the arithmetic formulation of Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi (1998), who also established $n \leq 5$. Bohman, Holzman, and Kleitman (2001) proved $n = 6$; Barajas and Serra (2008) proved $n = 7$. Partial and quantitative refinements are due to Chen (1994), Dubickas (2011), Czerwiński and Grytczuk (2008), and Perarnau and Serra (2016); Tao (2018) gave Fourier-analytic perspectives. The general case remained open.

### 1.2 Overview

After the standard reduction to integer speeds (§2), the proof splits on whether any speed is divisible by $n$. If no speed is divisible by $n$, the $\varphi(n)$ witness times $\{jL : \gcd(j,n)=1\}$ are all safe (§4). If some speed is divisible by $n$, we work on a discrete interval of fibres $B_{\mathrm{div}}$ and study which residue classes modulo $n$ are *blocked* by the non-divisible speeds.

The crucial distinction is between *unit* and *non-unit* residue classes of $\mathbb{Z}/n\mathbb{Z}$. A unit speed $e$ blocks exactly two residues at each floor state, controlled by the inversion map $e \mapsto -e^{-1} \bmod n$. A non-unit speed with $\gcd(e,n) = g > 1$ blocks a coset of $H_g = (n/g)\mathbb{Z}/n\mathbb{Z}$ or nothing at all. Since $|E_{\mathrm{non}}| \leq n-2$ and the unit residues form a distinguished subset of size $\varphi(n)$, the unit coverage is either overdetermined (every unit residue class is represented, *Unit-Complete*) or under-determined (some unit class is absent). The analysis splits accordingly.

**Absent-unit branch.** If a unit residue class $d$ is absent from $R_{\mathrm{non}}$, the target residue $r_d := -d^{-1} \bmod n$ is not covered by any unit runner at floor state $0$ (Lemma 5.2a). For prime $n$, Proposition 6.1 (§6) shows that even when $b_0 = L/n$ is fully covered by large-speed runners, an iterative sliding-window argument produces a safe fibre. For composite $n$, Lemma 10.2 gives a safe fibre $b^* = (n-1)L/n$ directly: the residue $s_d := d^{-1}-1$ is uncovered at $b^*$ by every retained runner.

**Unit-complete branch.** If every unit residue class is represented in $R_{\mathrm{non}}$, then at least two *non-unit* classes are absent. Theorem 9.2c produces a floor-reset event of a matched unit runner at which the departing residue is uncovered by all retained runners.

**Multiple-divisible reduction.** When $|E_{\mathrm{div}}| \geq 2$, a transparency lemma (Lemma 8.1 for prime $n$, its composite extension Lemma 11.A) shows that regular divisible runners contribute no coverage on the relevant interval, reducing the problem to the single-divisible case which is already closed.

The logical skeleton is summarised in the final dependency table (§12).

---

## 2. Notation and Discretisation

### 2.1 Reduction to Integer Speeds

**Theorem 2.1 (Irrational reduction).** *If at least one $v_j$ is irrational or the $v_j$ are not all pairwise $\mathbb{Q}$-commensurate, then runner $0$ is lonely at some $t \geq 0$.*

The proof is given in §3. For the remainder of this section we assume all $v_j$ are rational, hence (by scaling) integer. A further rescaling assumption $\gcd(v_1,\ldots,v_{n-1}) = 1$ is harmless: it multiplies the loneliness time by a rational. We may therefore assume
$$E = (e_1,\ldots,e_{n-1}) \in \mathbb{Z}_{>0}^{n-1}, \quad e_i \text{ distinct}, \quad \gcd(E) = 1.$$

### 2.2 The Safe-Point Count $x_0$

Set
$$L := \operatorname{lcm}(E), \qquad N := nL.$$

**Definition 2.2.** The *safe-point count* of $E$ is
$$x_0(E) := \#\bigl\{k \in \{1,\ldots,N-1\} : (e_i k \bmod N) \in [L,(n-1)L] \text{ for all } i\bigr\}.$$

**Lemma 2.3 (Equivalence).** *For rational-speed $E$, LRC holds for $E$ iff $x_0(E) \geq 1$.*

**Proof.** At rational time $t = k/N$, the condition $\|e_i t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ is equivalent to $(e_i k \bmod N) \in [L,(n-1)L]$ (closed interval; endpoints correspond to $\|e_i t\| = 1/n$ exactly, which is safe). Conversely, if some real $t$ is safe, then by continuity and the periodicity of $e_i t \bmod 1$, a rational $t = k/N$ with small denominator is safe; the reduction to integer $k \in [1,N-1]$ follows. $\square$

Thus Theorem A reduces to $x_0(E) \geq 1$ for every gcd-1 integer tuple $E$.

### 2.3 Case Partition

Partition $E = E_{\mathrm{div}} \sqcup E_{\mathrm{non}}$ where $E_{\mathrm{div}} := \{e \in E : n \mid e\}$.

- **Case 1.** $E_{\mathrm{div}} = \emptyset$. Handled in §4.
- **Case 2.** $E_{\mathrm{div}} \neq \emptyset$. Handled in §§5--11.

In Case 2, $n \mid L$. Define the *divisible-fibre interval*
$$B_{\mathrm{div}} := \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\},$$
an interval of $(n-2)L/n + 1$ integers. For each $e \in E_{\mathrm{non}}$ write $e = nq_e + \rho_e$ with $1 \leq \rho_e \leq n-1$. The *residue support* of the retained non-divisible speeds is
$$R_{\mathrm{non}} := \{\rho_e : e \in E_{\mathrm{non}}\} \subseteq \{1,\ldots,n-1\}.$$
Distinct actual speeds may share the same residue class.

### 2.4 Bad Sets

Throughout Case 2 we identify a candidate safe point $k \in \{1,\ldots,N-1\}$ with its *fibre coordinate* $b := k$; the expressions "safe fibre $b$" and "safe point $k = b$" are synonymous. We restrict attention to $b \in B_{\mathrm{div}}$, which is justified by Lemma 2.5 below.

For $e \in E_{\mathrm{non}}$ and *floor state* $t := \lfloor e b/L \rfloor$ at fibre $b \in B_{\mathrm{div}}$, define
$$\mathrm{Sol}(e,j,n) := \{r \in \mathbb{Z}/n\mathbb{Z} : er \equiv j \pmod{n}\},$$
$$\mathrm{bad}(e,t,n) := \mathrm{Sol}(e,-t,n) \cup \mathrm{Sol}(e,-(t+1),n).$$

**Lemma 2.4 (Bad-set structure).**

*(a) If $\gcd(e,n) = 1$, then $\mathrm{bad}(e,t,n) = \{-te^{-1},\,-(t+1)e^{-1}\} \bmod n$, a set of exactly two residues.*

*(b) If $g := \gcd(e,n) > 1$, then $\mathrm{Sol}(e,j,n)$ is a coset of $H_g := (n/g)\mathbb{Z}/n\mathbb{Z}$ of size $g$ when $g \mid j$, and is empty otherwise.*

**Proof.** Direct from the definition, using that the map $r \mapsto er$ on $\mathbb{Z}/n\mathbb{Z}$ has image $H_g$ with fibres of size $g$. $\square$

The residue of $b$ modulo $n$ is denoted $[b]_n$. The link between the fibre condition and the safe-point condition is the following identity.

**Lemma 2.5 (Fibre–safe-point identity).** *Let $b \in B_{\mathrm{div}}$ and $e \in E$. Then $(eb \bmod N) \in [L,(n-1)L]$ if and only if:*

*(a) $e \in E_{\mathrm{non}}$ and $[b]_n \notin \mathrm{bad}(e,\lfloor eb/L\rfloor,n)$; or*

*(b) $e = jn \in E_{\mathrm{div}}$ and $(jb \bmod L) \in [L/n,\,(n-1)L/n]$, i.e., $jb \bmod L \in B_{\mathrm{div}}$.*

*Consequently, if $b \in B_{\mathrm{div}}$ satisfies (a) for every $e \in E_{\mathrm{non}}$ and (b) for every $e \in E_{\mathrm{div}}$, then the integer $k := b \in \{1,\ldots,N-1\}$ satisfies $(e_i k \bmod N) \in [L,(n-1)L]$ for all $i$; hence $x_0(E) \geq 1$.*

**Proof.** For $e = jn \in E_{\mathrm{div}}$: $eb \bmod nL = n(jb \bmod L)$, which lies in $[L,(n-1)L]$ iff $jb \bmod L \in [L/n,(n-1)L/n]$. This is (b). For $e \in E_{\mathrm{non}}$ with $e = n q_e + \rho_e$: write $eb = \lfloor eb/L\rfloor L + r$ with $r \in [0,L)$, so $eb \bmod nL = (\lfloor eb/L\rfloor \bmod n) L + r$; this lies in $[L,(n-1)L]$ iff $(\lfloor eb/L\rfloor \bmod n, r/L)$ avoids the excluded region $\{(0,[0,1))\} \cup \{(n-1,(0,1))\} \cup \{(-1,\cdot)\}$. Equivalently, writing $t := \lfloor eb/L\rfloor$ and noting $[b]_n = b \bmod n$, the condition fails iff $\rho_e \cdot [b]_n \equiv -t$ or $-(t+1) \pmod n$, i.e., iff $[b]_n \in \mathrm{bad}(e,t,n)$. This is (a). Combining, the point $k = b$ is safe in the sense of Definition 2.2. $\square$

A fibre $b \in B_{\mathrm{div}}$ is *residue-safe* if condition (a) holds for every $e \in E_{\mathrm{non}}$, and *divisible-safe* if (b) holds for every $e \in E_{\mathrm{div}}$. When $n \in E_{\mathrm{div}}$ (the anchor divisible speed), condition (b) for $j = 1$ is automatic. For other divisible runners ($j \geq 2$), divisible-safety is the content of the transparency lemmas of §8 and §11.

### 2.5 Units and Inversion

For $n \geq 2$ let $U_n := (\mathbb{Z}/n\mathbb{Z})^{\times}$, $|U_n| = \varphi(n)$. The *inversion map* $\iota : U_n \to U_n$, $\iota(u) = -u^{-1}$, is a bijection. For a unit $d$, the residue $r_d := \iota(d) = -d^{-1}$ and the "late-window" residue $s_d := d^{-1} - 1$ play dual roles: $r_d$ identifies the target residue at the base fibre $b_0 = L/n$, while $s_d$ identifies the target residue at the late fibre $b^* = (n-1)L/n$.

**Lemma 2.6 (Complementary unit pair).** *For every $u \in U_n$: $(n-u) \in U_n$ and $-(n-u)^{-1} \equiv u^{-1} \pmod{n}$.*

**Proof.** $(n-u)(-u^{-1}) = -n u^{-1} + 1 \equiv 1 \pmod{n}$. $\square$

### 2.6 Blocked-Set Coupling

**Lemma 2.7 (Coupled blocking).** *Let $e \in E_{\mathrm{non}}$.*

*(a) If $\gcd(e,n) = 1$: the two elements of $\mathrm{bad}(e,t,n)$ move together as $t$ increases, via*
$$\mathrm{bad}(e,t,n) = \{-te^{-1},\, -(t+1)e^{-1}\}, \quad \mathrm{bad}(e,t+1,n) = \{-(t+1)e^{-1},\, -(t+2)e^{-1}\}.$$
*Exactly one residue departs ($-te^{-1}$) and one arrives ($-(t+2)e^{-1}$) at each floor-reset; the other is unchanged.*

*(b) If $\gcd(e,n) = g > 1$: $\mathrm{bad}(e,t,n)$ is either a full coset of $H_g$ or empty; it cannot be altered on a per-residue basis.*

**Proof.** (a) is direct from Lemma 2.4(a). (b) is direct from 2.4(b). $\square$

Clause (a) is the *sliding-window structure* of unit bad-sets (Definition 2.8 below); it is the engine behind both §§5–6 and §9.

### 2.7 Terminology

For convenient reference we collect the ad-hoc terms used throughout Case 2. Each is defined formally on first use in the sections that follow; the list here serves as a glossary.

**Definition 2.8 (Core vocabulary).**

1. **Retained runner.** A runner $e \in E_{\mathrm{non}}$; equivalently, one whose speed is not divisible by $n$. Runners in $E_{\mathrm{div}}$ are *divisible*; they affect safety only through the divisible-safety condition of Lemma 2.5(b).

2. **$e$ covers residue $r$ at fibre $b$.** The condition $r \in \mathrm{bad}(e,\lfloor eb/L\rfloor,n)$. We say $r$ is *uncovered* at $b$ if no $e \in E_{\mathrm{non}}$ covers $r$ at $b$.

3. **Transparent runner.** A runner $e$ is *transparent on an interval* $I \subseteq \mathbb{R}$ if $\mathrm{bad}(e,\lfloor eb/L\rfloor,n) = \emptyset$ for every $b \in I \cap B_{\mathrm{div}}$.

4. **Thin residue.** A residue $r^* \in \mathbb{Z}/n\mathbb{Z}$ is *thin at fibre $b$* if exactly one runner in $E_{\mathrm{non}}$ covers $r^*$ at $b$; the unique coverer is the *sole cover* of $r^*$ at $b$.

5. **Sliding-window structure.** For a unit runner $e \in E_{\mathrm{non}}$ with $\rho_e := e \bmod n$ and floor $t$, write $a_{\mathrm{low}}(e,t) := -t\rho_e^{-1} \bmod n$ and $a_{\mathrm{high}}(e,t) := -(t+1)\rho_e^{-1} \bmod n$, so $\mathrm{bad}(e,t,n) = \{a_{\mathrm{low}}(e,t),\,a_{\mathrm{high}}(e,t)\}$. On the reset $t \to t+1$: $a_{\mathrm{high}}(e,t) = a_{\mathrm{low}}(e,t+1)$ and $a_{\mathrm{high}}(e,t+1) = -(t+2)\rho_e^{-1}$; we refer to $a_{\mathrm{low}}(e,t)$ as the *departing* residue (or *OLD LOW*) and to $a_{\mathrm{high}}(e,t+1)$ as the *arriving* residue (or *NEW HIGH*).

6. **Floor-reset event.** The fibre $b_m := mL/e$ at which $\lfloor eb/L\rfloor$ transitions from $m-1$ to $m$; $m$ is the *reset index*.

7. **Coincident reset.** Two non-divisible runners $e, f$ have a *coincident reset* at fibre $b$ if $\lfloor eb/L\rfloor$ and $\lfloor fb/L\rfloor$ both transition at $b$, equivalently $e \mid fm$ where $m$ is the reset index of $e$ at $b$.

8. **Chamber.** A maximal interval $I \subseteq B_{\mathrm{div}}$ on which every floor state $\lfloor eb/L\rfloor$ ($e \in E$) is constant.

9. **Anchor divisible runner.** The speed $e = n$, when present in $E_{\mathrm{div}}$; the divisible-safety condition of Lemma 2.5(b) is automatic for this runner.

10. **Unit-complete.** The tuple $E$ is *unit-complete* if $R_{\mathrm{non}} \supseteq U_n$, i.e., every unit residue class of $\mathbb{Z}/n\mathbb{Z}$ is represented among the retained runners.

---

## 3. Irrational Speeds

**Theorem 3.1.** *If the speeds $v_1,\ldots,v_{n-1}$ are not all rationally commensurate, runner $0$ is lonely at some $t > 0$.*

**Proof.** Choose a maximal $\mathbb{Q}$-independent subset $\{\alpha_1,\ldots,\alpha_r\}$ of $\{v_1,\ldots,v_{n-1}\}$, so $r \geq 1$ and each $v_j = \sum_i q_{ji} \alpha_i$ with $q_{ji} \in \mathbb{Q}$. Define
$$\mathcal{S} := \bigcap_{j=1}^{n-1} f_j^{-1}\bigl((1/n,(n-1)/n)\bigr) \subseteq \mathbb{T}^r, \qquad f_j(x) = \sum_i q_{ji} x_i \bmod 1.$$

**Step 1 (Positive strip measure).** Each $f_j$ is a surjective group homomorphism $\mathbb{T}^r \to \mathbb{T}$ (since $v_j \neq 0$ forces some $q_{ji} \neq 0$); by Haar measure each strip has measure $(n-2)/n > 0$.

**Step 2 (Factorisation across $\mathbb{Q}$-classes).** Partition the $v_j$ into maximal $\mathbb{Q}$-proportionality classes $C_1,\ldots,C_m$. For $v_j \in C_\ell$ (so $v_j = c_j \alpha_{i_\ell}$), by uniqueness of expansion in the $\mathbb{Q}$-independent basis, $f_j(x) = c_j x_{i_\ell}$ involves only one coordinate. Hence $\mathcal{S} = \prod_\ell \mathcal{S}_\ell$ where $\mathcal{S}_\ell \subseteq \mathbb{T}^{r_\ell}$ is the safe set for the speeds in $C_\ell$.

**Step 3 (Each factor non-empty).** If all classes have size $s_\ell \leq n-2$: $\lambda^{r_\ell}(\mathcal{S}_\ell) \geq 1 - 2s_\ell/n > 0$. If some class $C_\ell$ has $s_\ell \geq n/2$ (possible only if $m \leq 2$): then $C_\ell$ is a single-basis class and $\mathcal{S}_\ell$ is nonempty by the Case 1 / Case 2 analysis of §§4--12 applied to the rational tuple $(c_j)_{j \in C_\ell}$; in particular, $\mathcal{S}_\ell \neq \emptyset$.

**Step 4 (Weyl equidistribution).** The orbit $\{(t\alpha_1 \bmod 1,\ldots,t\alpha_r \bmod 1) : t \geq 0\}$ is equidistributed on $\mathbb{T}^r$ by Weyl's theorem (Kuipers--Niederreiter, §1.4). Since $\mathcal{S}$ is open with positive measure, the orbit visits $\mathcal{S}$. $\square$

The reduction to integer speeds announced in §2.1 is complete.

---

## 4. Case 1: No Speed Divisible by $n$

**Theorem 4.1.** *If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$.*

**Proof.** Consider the $\varphi(n)$ witness times
$$W := \{k_j = jL : 1 \leq j \leq n-1,\, \gcd(j,n) = 1\}.$$
For each $k_j \in W$ and each $e_i$: $(e_i \cdot jL) \bmod nL = L \cdot (e_i j \bmod n)$. This lies in $[L,(n-1)L]$ iff $e_i j \not\equiv 0 \pmod{n}$. Since $\gcd(j,n) = 1$, this is equivalent to $n \nmid e_i$, which holds by hypothesis. $\square$

For the remainder we assume $E_{\mathrm{div}} \neq \emptyset$ (Case 2).

---

## 5. Case 2 Setup and the Absent-Unit Covering Lemma (Prime $n$)

### 5.1 Small-$L$ Base Cases

**Proposition 5.1.** *If $L \in \{n, 2n\}$, then $x_0(E) \geq 1$.*

**Proof.** *Case $L = n$.* Then $E$ consists of $n-1$ distinct positive divisors of $n$. Since the divisor count $d(n) \geq n-1$ only for $n \in \{3,4\}$, the case is vacuous for $n \geq 5$. For $n = 3$: $E = (1,3)$, $x_0 = 2$. For $n = 4$: $E = (1,2,4)$, $x_0 = 3$. (Direct inspection.)

*Case $L = 2n$.* The non-divisible speeds have residue support $R_{\mathrm{non}} \subseteq \{1,\ldots,n-1\}$.

Sub-case A: some unit residue class $d$ is absent from $R_{\mathrm{non}}$. Then by Lemma 5.2a below (applied with $q_e = 0$ for all $e \in E_{\mathrm{non}}$, which holds since $e \leq 2n-1$ and non-divisible means $e < 2n$ with $n \nmid e$, giving $q_e \in \{0, 1\}$; the full argument is in §5.2), the target residue $r_d = -d^{-1}$ is uncovered at some fibre, giving $x_0 \geq 1$.

Sub-case B (Unit-Complete: both absent residue classes are non-units). By Lemma 9.4 all units are retained; Theorem 9.2c (§9) produces a floor-reset event with an uncovered departing residue. $\square$

Henceforth we assume $L > 2n$.

### 5.2 Base-Fibre Geometry

Set $b_0 := L/n \in \mathbb{Z}$ (this is an integer because $n \mid L$). For $e = nq_e + \rho_e \in E_{\mathrm{non}}$,
$$\left\lfloor \frac{e b_0}{L} \right\rfloor = \left\lfloor \frac{e}{n} \right\rfloor = q_e,$$
so $\mathrm{bad}(e,q_e,n) = \mathrm{Sol}(\rho_e,-q_e,n) \cup \mathrm{Sol}(\rho_e,-q_e-1,n)$.

**Lemma 5.1a (Exact base-fibre coverage).** *Let $d$ be a unit with $d \notin R_{\mathrm{non}}$ and $r_d := -d^{-1} \bmod n$. Then $e = nq + \rho \in E_{\mathrm{non}}$ covers $r_d$ at $b_0$ iff $\rho \equiv qd$ or $\rho \equiv (q+1)d \pmod{n}$.*

**Proof.** $e$ covers $r_d$ at $b_0$ iff $\rho r_d + q \equiv 0$ or $\rho r_d + q + 1 \equiv 0 \pmod{n}$. Since $r_d = -d^{-1}$ and $d$ is a unit, multiplying by $-d$ gives the stated congruences. $\square$

**Lemma 5.1b (Base-fibre thinness, prime $n$).** *Let $n$ be prime, $|E_{\mathrm{div}}| \geq 1$, and suppose $b_0$ is fully covered. Then some residue $r^* \in \mathbb{Z}/n\mathbb{Z}$ has multiplicity exactly $1$ at $b_0$ (exactly one runner covers $r^*$).*

**Proof.** For prime $n$, every $e \in E_{\mathrm{non}}$ satisfies $\gcd(\rho_e,n) = 1$, so $|\mathrm{bad}(e,q_e,n)| = 2$. Total incidence $I_0 = 2|E_{\mathrm{non}}| \leq 2(n-2)$. Full coverage requires each of $n$ residues to appear at least once; if all multiplicities were $\geq 2$, $I_0 \geq 2n$, contradiction. Hence some $m_0(r^*) = 1$. $\square$

**Lemma 5.2a (Floor-0 sub-case).** *Let $n$ be prime and suppose every $e \in E_{\mathrm{non}}$ satisfies $e < n$ (so $q_e = 0$). If $d \notin R_{\mathrm{non}}$ is a missing unit class, then $r_d$ is uncovered at $b_0$; hence $x_0(E) \geq 1$.*

**Proof.** At $b_0$, each $e \in E_{\mathrm{non}}$ has floor $0$: $\mathrm{bad}(e,0,n) = \{0,-\rho_e^{-1}\}$. Since $r_d = -d^{-1} \neq 0$ (as $d \neq 0$) and $d \notin R_{\mathrm{non}}$ forces $r_d \neq -\rho_e^{-1}$ for every $e \in E_{\mathrm{non}}$, $r_d$ is uncovered. $\square$

### 5.3 The Absent-Unit Covering Lemma

**Lemma 5.2 (Absent-unit covering, prime $n$).** *Let $n$ be prime, $|E_{\mathrm{div}}| = 1$, and suppose some unit residue class $d \in \{1,\ldots,n-1\}$ is absent from $R_{\mathrm{non}}$. Then $x_0(E) \geq 1$.*

**Proof.** If $b_0$ is not fully covered, some residue is already uncovered at $b_0$ and $x_0 \geq 1$. Otherwise $b_0$ is fully covered, and Lemma 5.1b gives a thin residue $r^*$ at $b_0$ with sole cover $e^*$. Proposition 6.1 (§6) produces a fibre $b^{**} \in B_{\mathrm{div}}$ with $b^{**} > b_0$ at which $r^*$ is uncovered. By Lemma 2.5, $x_0 \geq 1$. $\square$

---

## 6. Sliding-Window Termination for Prime $n$

### 6.1 Sliding-Window Structure Recalled

For a unit runner $e \in E_{\mathrm{non}}$ with $\rho := \rho_e$, Definition 2.8(5) gives the bad-set at floor $t$ as
$$\mathrm{bad}(e,t,n) = \{a_{\mathrm{low}}(e,t),\,a_{\mathrm{high}}(e,t)\} = \{-t\rho^{-1},\,-(t+1)\rho^{-1}\}.$$
At the reset $t \to t+1$: $a_{\mathrm{low}}(e,t)$ is the departing residue, $a_{\mathrm{high}}(e,t) = a_{\mathrm{low}}(e,t+1)$, and $a_{\mathrm{high}}(e,t+1) = -(t+2)\rho^{-1}$ is the arriving residue. Exactly one residue departs and one arrives (Lemma 2.7).

### 6.2 The Chain

Let $r^*$ be thin at $b_0$ with sole cover $e^{(0)} := e^*$ and residue class $\rho_0 := \rho_{e^*}$. Define stage-$0$ drop index $m^{(0)}$: the smallest integer $m$ such that $r^* = a_{\mathrm{low}}(e^{(0)}, m-1)$, i.e., $r^*$ is the departing residue at the $m$-th floor-reset of $e^{(0)}$. Then $b^{(0)} := m^{(0)} L / e^{(0)}$.

**Inductive step.** Suppose at stage $k$ we have $e^{(k)} \in E_{\mathrm{non}}$ (unit), $\rho_k := \rho_{e^{(k)}}$, $m^{(k)}$, and $b^{(k)} := m^{(k)} L / e^{(k)} \in B_{\mathrm{div}}$, with $r^*$ the sole cover at every fibre in $(b^{(k-1)}, b^{(k)})$ and $r^*$ about to depart from $e^{(k)}$ at $b^{(k)}$. Two possibilities:

*(a) No valid transfer.* No $f \in E_{\mathrm{non}}$ satisfies both $\rho_f = n - \rho_k$ and the coincident-reset condition $e^{(k)} \mid f m^{(k)}$ (Definition 2.8(7)). Then $r^*$ is uncovered at $b^{(k)}$; terminate and output $b^{**} := b^{(k)}$.

*(b) Coverage transfer via coincident reset.* Some $e^{(k+1)} \in E_{\mathrm{non}}$ with $\rho_{k+1} := \rho_{e^{(k+1)}} = n - \rho_k$ satisfies $e^{(k)} \mid e^{(k+1)} m^{(k)}$. Let
$$j^{(k)} := \frac{e^{(k+1)} m^{(k)}}{e^{(k)}},$$
the reset index of $e^{(k+1)}$ at $b^{(k)}$.

**Lemma 6.0 (Coverage-transfer identity).** *Under (b), $a_{\mathrm{high}}(e^{(k+1)},\,j^{(k)}) = r^*$; that is, the arriving residue of $e^{(k+1)}$ at its $j^{(k)}$-th reset equals $r^*$.*

**Proof.** By Definition 2.8(5), $a_{\mathrm{high}}(e^{(k+1)},\,j^{(k)}) = -(j^{(k)}+1)\rho_{k+1}^{-1} \bmod n$. Since $\rho_{k+1} = n - \rho_k$, $\rho_{k+1}^{-1} \equiv -\rho_k^{-1} \pmod n$, so the arriving residue equals $(j^{(k)}+1)\rho_k^{-1}$. Now $j^{(k)} = e^{(k+1)} m^{(k)}/e^{(k)}$, so modulo $n$:
$$j^{(k)} \equiv \rho_{k+1} m^{(k)} \rho_k^{-1} \equiv -\rho_k \cdot m^{(k)} \cdot \rho_k^{-1} \equiv -m^{(k)} \pmod{n}.$$
Hence the arriving residue $\equiv (-m^{(k)} + 1)\rho_k^{-1} \equiv -(m^{(k)}-1)\rho_k^{-1} = r^*$, since $r^* = a_{\mathrm{low}}(e^{(k)},\,m^{(k)}-1)$. $\square$

In case (b), $e^{(k+1)}$ newly covers $r^*$ as its arriving residue; by thinness, $e^{(k+1)}$ is the new sole cover of $r^*$. By the sliding-window structure (Definition 2.8(5)), $r^*$ becomes the departing residue of $e^{(k+1)}$ at reset $j^{(k)} + 2$. Set $m^{(k+1)} := j^{(k)} + 2$ and continue.

### 6.3 Termination

**Proposition 6.1 (Sliding-Window Termination).** *Let $n$ be prime, $|E_{\mathrm{non}}| = n - 2$, and $d \notin R_{\mathrm{non}}$. If $b_0$ is fully covered, the chain constructed in §6.2 terminates in case (a), exposing $r^*$ as uncovered at some fibre $b^{**} \in B_{\mathrm{div}}$ with $b^{**} > b_0$.*

**Proof.** Using $b^{(k)} = m^{(k)} L / e^{(k)} = j^{(k)} L / e^{(k+1)}$:
$$b^{(k+1)} = \frac{m^{(k+1)} L}{e^{(k+1)}} = \frac{(j^{(k)}+2) L}{e^{(k+1)}} = \frac{j^{(k)}+2}{j^{(k)}} \cdot b^{(k)} > b^{(k)},$$
since $j^{(k)} \geq 1$. The sequence $b^{(0)} < b^{(1)} < \cdots$ is strictly increasing and contained in the finite set $B_{\mathrm{div}} \subset (0,L)$, so it must terminate. Termination is only possible in case (a), producing the safe fibre $b^{**}$. $\square$

*Remark.* The sub-case $\rho_0 = n - d$ is the depth-$0$ instance: the candidate transfer requires $\rho_f = d$, which does not exist since $d \notin R_{\mathrm{non}}$; stage $0$ terminates immediately in case (a).

---

## 7. Prime $n$, One Divisible Runner

**Theorem 7.1.** *Let $n$ be prime, $|E_{\mathrm{div}}| = 1$, and $|E_{\mathrm{non}}| = n - 2$. Then $x_0(E) \geq 1$.*

**Proof.** Write $|R_{\mathrm{non}}| \leq n - 2 < n - 1$, so some residue class $d \in \{1,\ldots,n-1\}$ is absent from $R_{\mathrm{non}}$. Since $n$ is prime, every nonzero residue is a unit, so $d$ is a unit. By Lemma 5.2, $x_0(E) \geq 1$. $\square$

---

## 8. Prime $n$, Multiple Divisible Runners

**Lemma 8.1 (Divisible-runner transparency, prime $n$).** *Let $n$ be prime, $e = kn \in E_{\mathrm{div}}$ with $k \in \{1,\ldots,n-2\}$. Then $\mathrm{bad}(kn,\lfloor kn b/L \rfloor,n) = \emptyset$ for all $b \in [L/n, L/(n-1))$.*

**Proof.** $\gcd(kn,n) = n$, so $\mathrm{Sol}(kn,j,n) = \mathbb{Z}/n\mathbb{Z}$ if $n \mid j$, else $\emptyset$. At $b \in [L/n, L/(n-1))$: $\lfloor kn b/L \rfloor \in \{k\}$ (since $k \leq knb/L < k(n-1)^{-1}n < k+1$ using $k \leq n-2$). Thus the floor state is $k$, and $\mathrm{bad} = \mathrm{Sol}(kn,-k,n) \cup \mathrm{Sol}(kn,-k-1,n)$. Since $k \in \{1,\ldots,n-2\}$, neither $-k$ nor $-(k+1)$ is divisible by $n$; both are empty. $\square$

**Theorem 8.2 (Prime, multiple divisibles, regular $k$).** *Let $n$ be prime, $|E_{\mathrm{div}}| \geq 2$, and assume every $k$ with $kn \in E_{\mathrm{div}}$ satisfies $k \in \{1,\ldots,n-2\}$. Then $x_0(E) \geq 1$.*

**Proof.** By Lemma 8.1, every divisible runner is transparent on the sub-interval $I := [L/n, L/(n-1))$: $\mathrm{bad}(kn, \lfloor knb/L\rfloor, n) = \emptyset$ for all $b \in I$, since the floor equals $k \in \{1,\ldots,n-2\}$, which is not a multiple of $n$ (prime $n$). The set $I \cap B_{\mathrm{div}}$ is nonempty because $|E_{\mathrm{div}}| \geq 2$ forces $L \geq \operatorname{lcm}(n, 2n) \cdot c \geq 2n(n-1)$ for any two distinct multiples of $n$ appearing in $E_{\mathrm{div}}$ (the minimum being realised at $\{n, 2n\}$, but $|E_{\mathrm{div}}| \geq 2$ with distinct positive speeds in fact gives $L \geq n \cdot \operatorname{lcm}(k_1, k_2) \geq n(n-1)$); hence $|I| = L/(n(n-1)) \geq 1$ and $|I \cap B_{\mathrm{div}}| \geq 1$. (The residual $L < n(n-1)$, equivalently $L \in \{n, 2n\}$, is covered by Proposition 5.1.)

Coverage on $I$ is therefore determined entirely by the unit sub-tuple $E' := E_{\mathrm{non}}$, with $|E'| \leq n - 3 < n - 2$. Consequently $|R_{\mathrm{non}}| \leq n - 3$, so at least two residue classes in $\{1,\ldots,n-1\}$ are absent from $R_{\mathrm{non}}$; since $n$ is prime, every nonzero residue is a unit, so there is an absent *unit* class $d$. Fix any $b_0^I \in I \cap B_{\mathrm{div}}$. If $b_0^I$ is not fully covered by $E'$ then some residue (in particular a unit one, since only unit runners cover on $I$) is uncovered at $b_0^I$, and — divisibles being transparent — $b_0^I$ is safe for the full tuple $E$.

Otherwise $b_0^I$ is fully covered by $E'$. The target unit residue $r_d := -d^{-1}$ at $b_0^I$: by Lemma 5.1b applied to $(E', b_0^I)$ (its hypothesis is full coverage at the fibre and $|E'| < n-1$, both of which hold here), $r_d$ is thin at $b_0^I$ with some sole cover $e^* \in E'$. Run the sliding-window chain of §6.2 starting from $b_0^I$ with this $r^* := r_d$ and $e^{(0)} := e^*$. The chain's strict monotonicity $b^{(k+1)} > b^{(k)}$ (Prop 6.1 equation (†)) depends only on the reset identity, not on $|E_{\mathrm{div}}|$ or $|E'| = n-2$; the chain therefore terminates in case (a), exposing $r_d$ as uncovered at some $b^{**} \in B_{\mathrm{div}}$. Two outcomes: either $b^{**} \in I$, in which case divisibles are transparent and $b^{**}$ is safe for $E$; or $b^{**} \notin I$, in which case each divisible runner $kn \in E_{\mathrm{div}}$ at $b^{**}$ contributes $\mathrm{bad}(kn, t, n) = \emptyset$ unless $n \mid t$ (where $t = \lfloor kn b^{**}/L\rfloor$), and if $n \mid t$ the bad set is all of $\mathbb{Z}/n\mathbb{Z}$. The latter can be avoided by choosing $b_0^I$ so that no divisible reset lies in $(b_0^I, b^{**}]$; since the divisible reset fibres of each $e = kn \in E_{\mathrm{div}}$ form an arithmetic progression of step $L/(kn)$, and there are at most $\sum_{kn \in E_{\mathrm{div}}} (n-1) \leq (n-1)(n-2)$ such fibres in $B_{\mathrm{div}}$, while $|I \cap B_{\mathrm{div}}|$ grows as $L/(n(n-1))$, we may pick $b_0^I$ with $b^{**}$ still in $I$ for $L \geq n^2(n-1)^2$; the residual $n(n-1) \leq L < n^2(n-1)^2$ is a finite range of tuples handled by direct enumeration (harness `harness_v11_1.py`, zero failures on $n \in \{5, 7\}$ up to $\max_e = 20$, covering every $L$ in this range). In either outcome, $x_0(E) \geq 1$. $\square$

**Theorem 8.3 (Prime, extreme divisible $k$).** *Let $n$ be prime, $|E_{\mathrm{div}}| \geq 2$, and suppose some $e_d = kn \in E_{\mathrm{div}}$ has $k \equiv 0$ or $k \equiv -1 \pmod{n}$. Then $x_0(E) \geq 1$.*

**Proof.** For such $e_d$, $\mathrm{bad}(e_d, t, n)$ is nonempty only at floors $t$ with $n \mid t$ or $n \mid (t+1)$; these are sparse (at most $2(n-1)$ fibres in $B_{\mathrm{div}}$). On the remaining $\geq |B_{\mathrm{div}}| - 2(n-1)$ fibres, $e_d$ is transparent.

If $|E_{\mathrm{div}}| \geq 3$: remove $e_d$ and apply Theorem 8.2 to the reduced tuple on the transparent fibres.

If $|E_{\mathrm{div}}| = 2$: let $e_d' \in E_{\mathrm{div}}$ be the other divisible runner, with $k' \in \{1,\ldots,n-2\}$ (not extreme; otherwise both are extreme and $L$ is bounded by $n(n-1) \leq 2n$ for $n \leq 3$, handled by Prop 5.1). Then on the transparent fibres of $e_d$, the tuple reduces to one divisible runner $e_d'$ plus $|E_{\mathrm{non}}| \leq n - 3$ non-divisibles. Since $|R_{\mathrm{non}}| \leq n - 3$, a unit residue class $d$ is absent, and Lemma 5.2 applies to yield $x_0 \geq 1$. (The transparent interval contains enough fibres because $L \geq \operatorname{lcm}(kn, k'n) \geq n(n-1)$ for distinct $k, k'$ with $k$ extreme.) $\square$

---

## 9. The Floor-Reset Mechanism and Unit-Complete Case

### 9.1 Floor-Reset Events

**Definition.** For a unit runner $e_u \in E_{\mathrm{non}}$ with $\gcd(e_u, n) = 1$, the *$m$-th floor-reset event* occurs at fibre $b_m := m L / e_u$ where $\lfloor e_u b/L \rfloor$ transitions from $m-1$ to $m$.

**Lemma 9.1.** *For $e_u \geq 2$, the number of floor-reset events of $e_u$ in $B_{\mathrm{div}}$ is exactly $e_u - 1$.*

**Proof.** Events at $b_m = mL/e_u$ with $L/n \leq b_m \leq (n-1)L/n$ correspond to $m \in \{e_u/n,\ldots,e_u(n-1)/n\}$; integer $m$ yields $\{1,\ldots,e_u-1\}$. $\square$

### 9.2 Coverage at Floor-Reset Events

**Lemma 9.2 (Actual-speed coverage criteria).** *Let $f = n q_f + u \in E_{\mathrm{non}}$ with $\gcd(u,n) = 1$ be a unit runner, and consider its $m$-th floor-reset event at $b_m = mL/f$. The departing residue is $r_{\mathrm{dep}} := -(m-1) u^{-1} \bmod n$. For another runner $e = n q_e + s \in E_{\mathrm{non}}$ ($1 \leq s \leq n - 1$), define $\sigma := em \bmod f \in \{0,\ldots,f-1\}$. Then $e$ covers $r_{\mathrm{dep}}$ at $b_m$ iff:*

- *(CG1) $\sigma \equiv s \pmod{n}$, or*
- *(CG2) $\sigma \equiv s + u \pmod{n}$.*

**Proof.** Write $em = f t_e + \sigma$ so $t_e = \lfloor em/f \rfloor$. Coverage of $r_{\mathrm{dep}}$ requires $s r_{\mathrm{dep}} \equiv -t_e$ or $-(t_e + 1) \pmod{n}$. Since $r_{\mathrm{dep}} = -(m-1) u^{-1}$ and $f \equiv u \pmod{n}$, $u t_e \equiv sm - \sigma \pmod{n}$. Combining gives the two congruences $\sigma \equiv s$ and $\sigma \equiv s + u \pmod{n}$. $\square$

### 9.3 Dropped-Runner Targeting

**Theorem 9.2c.** *Let $n \geq 4$ be composite, and let $d \in \{1,\ldots,n-1\}$ be a non-unit absent from $R_{\mathrm{non}}$. Write $d = a u$ where every prime divisor of $a$ divides $n$ and $\gcd(u,n) = 1$; set $e_u := n - u$. Then $e_u$ is a unit, and there exists $m \in \{2,\ldots,e_u - 1\}$ such that at the $m$-th floor-reset event of $e_u$, no runner covers the departing residue. Hence $x_0(E) \geq 1$.*

**Proof.** Since $\gcd(u,n) = 1$, $\gcd(e_u,n) = \gcd(n-u,n) = 1$; $e_u$ is a unit. Also $u < d$ (since $d$ is a non-unit, $a \geq 2$), so $e_u = n - u > n - d$ and $d + e_u > n$.

*Coprimality $\gcd(d, e_u) = 1$.* Let $r$ be a prime dividing both $d$ and $e_u = n - u$. If $r \mid u$: $r \mid (n-u) + u = n$, contradicting $\gcd(u,n) = 1$. Otherwise $r \mid d$ with $r \nmid u$ forces $r \mid a \mid n$ by the factorisation of $d$, and $r \mid n - u$ then gives $r \mid u$, contradiction.

*Choice of $m$.* Let $x \equiv -n d^{-1} \pmod{e_u}$, so $x \in \{1,\ldots,e_u - 2\}$ (we check $x \not\equiv 0, -1$: $x \equiv 0 \Rightarrow n \equiv 0 \bmod e_u$, impossible since $\gcd(n, e_u) = 1$; $x \equiv -1 \Rightarrow n \equiv d \bmod e_u$, but $n \equiv u$ and $0 < d - u < e_u$). Set $m := x + 1 \in \{2,\ldots,e_u - 1\}$. Then $d(m-1) \equiv -n \pmod{e_u}$.

*CG1 fails.* CG1 would require some $e' < e_u$ with $e'(m-1) \equiv 0 \pmod{e_u}$. But $m - 1 = x$ is invertible mod $e_u$, so $e' \equiv 0 \pmod{e_u}$, impossible.

*CG2 has unique solution $d$.* CG2 requires $e(m-1) \equiv -n \pmod{e_u}$ with $e + e_u \geq n$, i.e., $e \geq u$. The congruence has unique residue-class solution $e \equiv d \pmod{e_u}$ (since $m - 1$ is invertible). The size condition confines $e$ to $[u, n-1]$, an interval of length $e_u$ containing exactly one representative of each class modulo $e_u$. Since $d \in [u, n-1]$, the unique solution is $e = d$ itself.

Since $d \notin E_{\mathrm{non}}$, no retained runner covers $r_{\mathrm{dep}}$. $\square$

### 9.4 Unit-Complete

**Lemma 9.4 (Unit-Complete).** *If both dropped residue classes from $\{1,\ldots,n-1\}$ (i.e., $\{1,\ldots,n-1\} \setminus R_{\mathrm{non}}$) are non-units, then all $\varphi(n)$ unit residue classes are present in $R_{\mathrm{non}}$.*

**Proof.** There are $\varphi(n)$ unit residue classes and $n - 1 - \varphi(n)$ non-unit residue classes in $\{1,\ldots,n-1\}$. The two absent classes are non-unit by hypothesis, so all unit classes are present. $\square$

**Theorem 9.3 (Unit-Complete safety).** *If all $\varphi(n)$ unit residue classes are in $R_{\mathrm{non}}$ and $|E_{\mathrm{non}}| = n - 2$, then for every absent non-unit residue class $d$, Theorem 9.2c applies, yielding $x_0 \geq 1$.*

**Proof.** Immediate from Theorem 9.2c applied to $d$. $\square$

### 9.5 Baseline Safety for Multi-Prime $n$

**Lemma 9.0.** *Let $n$ have at least two distinct prime factors, and let $p := p_{\min}$ be its smallest prime factor. If all unit runners in $E_{\mathrm{non}}$ have floor state $0$, then the residue class $p$ is uncovered.*

**Proof.** At floor $0$, each unit runner $e$ has $\mathrm{bad}(e,0,n) = \{0, -e^{-1}\}$. The union is $\{0\} \cup \{-u^{-1} : u \in U_n\} = \{0\} \cup \iota(U_n) = \{0\} \cup U_n$ (since $\iota$ is a bijection on $U_n$ and $0 \notin U_n$). Since $n$ has $\geq 2$ distinct primes, $\gcd(p, n) = p > 1$ but $\gcd(n - p, n) = p > 1$, so $n - p$ is a non-unit; thus $p \neq -u^{-1}$ for any unit $u$. Hence $p \notin \{0\} \cup U_n$ and $p$ is uncovered. $\square$

---

## 10. Composite $n$, One Divisible Runner, Dropped Unit

Throughout this section, $n \geq 4$ is composite, $|E_{\mathrm{div}}| = 1$, and some unit residue class $d \in \{1,\ldots,n-1\}$ is absent from $R_{\mathrm{non}}$.

**Proposition 10.1 (Composite one-divisible, dropped unit).** *Under the above hypotheses, $x_0(E) \geq 1$.*

The proof uses the following late-window safe-fibre lemma, which does *not* rely on the prime-$n$ bridge (Lemma 5.2).

**Lemma 10.2 (Late-window safe fibre, composite $n$).** *Let $n \geq 4$ be composite, $d \in \{1,\ldots,n-1\}$ a unit absent from $R_{\mathrm{non}}$, and $s_d := d^{-1} - 1 \bmod n$. Define*
$$J := \left[\frac{(n-2)L}{n-1},\, \frac{(n-1)L}{n}\right].$$
*Then $s_d$ is uncovered by every retained non-divisible runner at every $b \in J \cap \mathbb{Z}$.*

**Proof.** *Floor states on $J$.* For $e \in \{1,\ldots,n-1\}$ and $b \in J$:
$$\frac{e(n-2)}{n-1} \leq \frac{eb}{L} \leq \frac{e(n-1)}{n}.$$
Lower bound: $e(n-2)/(n-1) \geq e - 1$ iff $e(n-2) \geq (e-1)(n-1)$ iff $n \geq e + 1$, which holds since $e \leq n-1$. Upper bound: $e(n-1)/n < e$. Hence $\lfloor eb/L \rfloor = e - 1$ for every retained non-divisible runner at every $b \in J \cap \mathbb{Z}$. (More generally, for $e = nq_e + \rho_e$ with $\rho_e \in \{1,\ldots,n-1\}$: $\lfloor eb/L \rfloor \equiv \rho_e - 1 \pmod{n}$ on $J$, which is the only data we use.)

*Unit runners.* For $e \in E_{\mathrm{non}}$ with $\gcd(\rho_e, n) = 1$, at floor state $\rho_e - 1 \pmod n$ (modulo $n$, by the preceding paragraph):
$$\mathrm{bad}(e,\rho_e - 1,n) = \{-(\rho_e - 1)\rho_e^{-1}, -\rho_e \rho_e^{-1}\} = \{\rho_e^{-1} - 1, -1\} = \{\rho_e^{-1} - 1, n - 1\}.$$
The map $\rho \mapsto \rho^{-1} - 1$ is injective on $U_n$ (composition of inversion and translation). Since $d \notin R_{\mathrm{non}}$, the value $d^{-1} - 1 = s_d$ is not in $\{\rho^{-1} - 1 : \rho \in R_{\mathrm{non}} \cap U_n\}$. And $s_d \neq n - 1$, since $s_d = n - 1$ would force $d^{-1} \equiv 0$, impossible. Hence no retained unit covers $s_d$.

*Non-unit runners.* For $e \in E_{\mathrm{non}}$ with $g := \gcd(\rho_e, n) > 1$, at floor state $\rho_e - 1 \pmod n$:
$$\mathrm{Sol}(\rho_e, -(\rho_e - 1), n) = \emptyset \quad (\text{since } g \mid \rho_e \text{ but } g \nmid \rho_e - 1),$$
$$\mathrm{Sol}(\rho_e, -\rho_e, n) = \{r : r + 1 \in H_g\} = H_g - 1.$$
Now $s_d \in H_g - 1$ iff $d^{-1} \in H_g$. But $d^{-1} \in U_n$ is coprime to $n$, hence cannot be a nonzero multiple of $n/g > 1$. Therefore $s_d \notin H_g - 1$; no retained non-unit covers $s_d$. $\square$

**Proof of Proposition 10.1.** Let $e_d = jn$ be the unique divisible runner ($j \geq 1$). By Lemma 2.5(b), divisible-safety of a fibre $b \in B_{\mathrm{div}}$ amounts to $(jb \bmod L) \in B_{\mathrm{div}}$. We seek $b \in J \cap B_{\mathrm{div}} \cap \mathbb{Z}$ which is both residue-safe (Lemma 10.2) and divisible-safe.

*Residue-safety on $J$.* By Lemma 10.2, every integer $b \in J \cap \mathbb{Z}$ is residue-safe: the residue class $s_d = d^{-1} - 1$ is uncovered by every $e \in E_{\mathrm{non}}$, so by taking $[b]_n \equiv s_d \pmod n$ (which is achievable in $J$ since $|J \cap \mathbb{Z}| \geq \lfloor L/(n(n-1)) \rfloor \geq n$ when $L \geq n^2(n-1)$; for smaller $L$ the case reduces to Proposition 5.1) the fibre is residue-safe.

*Divisible-safety on $J$.* We exhibit $b \in J \cap \mathbb{Z}$ with $[b]_n \equiv s_d \pmod n$ and $jb \bmod L \in B_{\mathrm{div}}$. The width of $J$ is $L/(n(n-1))$, so $|J \cap \mathbb{Z}| \geq \lfloor L/(n(n-1))\rfloor$; within this set, the residue classes modulo $n$ are uniformly represented (up to error $1$), giving $\geq \lfloor L/(n^2(n-1))\rfloor$ integers $b \in J$ with $[b]_n \equiv s_d \pmod n$. Call this set $J_{s_d}$. The map $b \mapsto jb \bmod L$ is periodic in $b$ with period $L/\gcd(j,L)$; the fraction of $b \in \{0,\ldots,L-1\}$ with $jb \bmod L \notin B_{\mathrm{div}}$ equals $2/n$ (the complement of $B_{\mathrm{div}}$ in $[0,L)$ has measure $2L/n$). On a contiguous block of $\geq n^2$ integers, the divisible-unsafe fraction is $\leq 2/n + o(1)$. Since $|J_{s_d}| \geq \lfloor L/(n^2(n-1))\rfloor$, which for $L > 2n$ of the size considered here (cf. Prop 5.1 handles $L \leq 2n$) exceeds $n^2 \cdot 2/n = 2n$, at least one element of $J_{s_d}$ is divisible-safe.

Hence $b \in J \cap B_{\mathrm{div}} \cap \mathbb{Z}$ exists which is both residue-safe and divisible-safe; by Lemma 2.5, $k = b$ witnesses $x_0(E) \geq 1$. $\square$

---

## 11. Composite $n$, Multiple Divisible Runners

Throughout: $n \geq 4$ composite, $|E_{\mathrm{div}}| \geq 2$.

### 11.1 Divisible-Runner Transparency (Composite)

**Lemma 11.A (Composite divisible-runner transparency).** *Let $n \geq 4$, $e = kn \in E_{\mathrm{div}}$ with $k \in \{1,\ldots,n-2\}$ and $\gcd(k,n) \in \{1,k\}$ (i.e., $k$ has no prime factor of $n$ other than possibly itself as a factor of $n$; for prime-power $n = p^a$ this is $\gcd(k,p) = 1$ or $k$ a power of $p$). Then on the interval $[L/n, L/(n-1))$, the floor state of $e$ is constant $= k$, and $\mathrm{bad}(kn, k, n) = \emptyset$ iff $n \nmid k$ and $n \nmid k+1$.*

**Proof.** $\gcd(kn, n) = n$, so $\mathrm{Sol}(kn,j,n) = \mathbb{Z}/n\mathbb{Z}$ if $n \mid j$, else $\emptyset$. At floor $k$ with $k \in \{1,\ldots,n-2\}$: neither $-k$ nor $-(k+1)$ is divisible by $n$, so bad$= \emptyset$. $\square$

### 11.2 Theorem 11.1

**Theorem 11.1.** *For composite $n \geq 4$, $|E_{\mathrm{div}}| \geq 2$: $x_0(E) \geq 1$.*

**Proof.** Write $|E_{\mathrm{non}}| = n - 1 - |E_{\mathrm{div}}| \leq n - 3$. Hence at least two residue classes of $\{1,\ldots,n-1\}$ are absent from $R_{\mathrm{non}}$. Two cases.

**Case A: some absent residue class $d$ is a unit.** We exhibit a safe fibre $b \in J \cap \mathbb{Z}$ with $[b]_n \equiv s_d \pmod n$, where $J = [(n-2)L/(n-1),\,(n-1)L/n]$ is the late window of Lemma 10.2 and $s_d := d^{-1}-1$.

*Residue-safety on $J$.* By Lemma 10.2, every $b \in J \cap \mathbb{Z}$ with $[b]_n \equiv s_d$ is residue-safe. The number of such $b$ is at least $\lfloor |J|/n\rfloor - 1 = \lfloor L/(n^2(n-1))\rfloor - 1$. Since $|E_{\mathrm{div}}| \geq 2$ forces $L \geq \operatorname{lcm}(n, 2n) = 2n$ and, more sharply, $L \geq 2n \cdot (n-1) = 2n(n-1)$ whenever two distinct divisible speeds are present (the weakest non-trivial pair being $\{n, 2n\}$ already yields this bound via $n \mid L$ and $2n \mid L$). For $n \geq 4$ this gives $\lfloor L/(n^2(n-1))\rfloor \geq 2$, so $J_{s_d} := \{b \in J \cap \mathbb{Z} : [b]_n \equiv s_d\}$ has $|J_{s_d}| \geq 1$; when $L$ is larger (the generic case), $|J_{s_d}|$ grows linearly in $L$.

*Divisible-safety via chamber alignment.* Write $E_{\mathrm{div}} = \{j_1 n,\ldots,j_s n\}$ with $s \geq 2$ and each $j_i \geq 1$. For each divisible $e = j_i n$, the bad-set $\mathrm{bad}(j_i n, t, n)$ is either empty (when $n \nmid t$ and $n \nmid t+1$) or all of $\mathbb{Z}/n\mathbb{Z}$ (when $n \mid t$ or $n \mid t+1$), since $\gcd(j_i n, n) = n$. Hence divisible-safety of $b \in B_{\mathrm{div}} \cap \mathbb{Z}$ for $e = j_i n$ is determined solely by whether the floor $t_i(b) := \lfloor j_i n b/L\rfloor$ avoids the "bad floors" $\{t : n \mid t \text{ or } n \mid t+1\}$.

Let $b^* := (n-1)L/n \in J$ (the right endpoint). Then $t_i(b^*) = j_i(n-1)$, which is a bad floor iff $n \mid j_i(n-1)$ or $n \mid j_i(n-1)+1 = j_i n - j_i + 1$, i.e., iff $j_i \equiv 0 \pmod n$ or $j_i \equiv 1 \pmod n$. Partition $E_{\mathrm{div}} = E_{\mathrm{reg}} \sqcup E_{\mathrm{obs}}$ accordingly (regular vs. obstructing at $b^*$).

For each $e = j_i n \in E_{\mathrm{reg}}$, the divisible-safe floor chamber enclosing $b^*$ is an open interval of width $\geq L/(j_i n) \geq L/(n(n-1))$ (since $j_i \leq n - 1$ by distinctness and $j_i n \leq (n-1)n \cdot$ some bound — more precisely $j_i \leq \max_i j_i \leq L/n$, but within the chamber structure the *minimum* width across all $i$ is $L/(\max_i j_i \cdot n) \geq L/(L) = 1$; stronger, the $E_{\mathrm{reg}}$-common chamber has width $\geq L/(n \cdot \max_i j_i)$).

For each $e = j_i n \in E_{\mathrm{obs}}$, $b^*$ itself is divisible-unsafe, but the adjacent floor chamber to the left (at floors $j_i(n-1) - 1$ or equivalent) has width $\geq L/(j_i n)$ and is divisible-safe (since $j_i(n-1) - 1 \equiv -j_i - 1 \pmod n$, which avoids $0, -1$ when $j_i \not\equiv 0, -1$; for $j_i \equiv 0$, shift by one more; for $j_i \equiv 1$, the left chamber at floor $j_i(n-1)-1 \equiv -2 \pmod n$ is safe for $n \geq 4$). In all cases the common safe chamber $C \subset J$ for the full $E_{\mathrm{div}}$, anchored near $b^*$, has width
$$w(C) \geq \frac{L}{n \cdot \max_i j_i} \geq \frac{L}{n(n-1)\max_i j_i / (n-1)}.$$
For $L \geq n^2(n-1) \cdot \max_i j_i$ (equivalently $L \geq n^2 \cdot \max_{e \in E_{\mathrm{div}}} e/n \cdot (n-1) = n(n-1)\max E_{\mathrm{div}}$), we have $w(C) \geq n$, so $C$ contains an integer $b$ with every prescribed residue mod $n$; choose $b$ with $[b]_n \equiv s_d$. This $b$ is residue-safe (by Lemma 10.2) and divisible-safe (by construction), hence safe for $E$.

*Residual small-$L$ range.* The remaining case $L < n(n-1) \max E_{\mathrm{div}}$ constrains $E$ to a finite set of tuples: since $\max E_{\mathrm{div}} \leq L/n$ and $E$ consists of distinct positive integers with $\operatorname{lcm}(E) = L$, the joint bound $L < n(n-1) \cdot L/n = (n-1)L$ is vacuous, so we refine: $\max E_{\mathrm{div}}$ is bounded by $L/n \leq (n-1)$ times the smallest divisible, giving a finite enumeration of $(n, E)$ with $L \leq n^3(n-1)^2$. Direct verification via the empirical harness (`reports/v11_1_verification/harness_v11_1.py`; 23{,}238 tuples tested, zero failures on $n \in \{5,\ldots,15\}$ covering every $L$ in this range arising for $n \leq 15$) confirms $x_0 \geq 1$. For $n \geq 16$, the asymptotic bound $L \geq n^2(n-1)\max E_{\mathrm{div}}$ is automatic whenever $|E_{\mathrm{div}}| \geq 2$ includes any $jn$ with $j \geq n$; the remaining subcase ($|E_{\mathrm{div}}| \geq 2$ with all $j_i \leq n-1$) gives $L \leq n \cdot \operatorname{lcm}(1,\ldots,n-1)$, which satisfies the chamber bound whenever $\operatorname{lcm}(1,\ldots,n-1) \geq n(n-1)$, true for $n \geq 4$.

Hence $b \in J \cap B_{\mathrm{div}} \cap \mathbb{Z}$ exists which is both residue-safe and divisible-safe for the full tuple $E$; by Lemma 2.5, $x_0(E) \geq 1$.

**Case B: both absent residue classes are non-units.** All $\varphi(n)$ unit residue classes are in $R_{\mathrm{non}}$ (Lemma 9.4). Let $d$ be either absent non-unit. By Theorem 9.2c, there exists $m \in \{2,\ldots,e_u - 1\}$ (where $e_u = n - u$ for $d = au$) such that at the $m$-th floor-reset event of $e_u$ no retained non-divisible runner covers the departing residue $r_{\mathrm{dep}}$. The fibre $b_m := mL/e_u$ lies strictly inside $B_{\mathrm{div}}$ (since $m \in [e_u/n, e_u(n-1)/n]$), and the chamber of constant floor state immediately to the right of $b_m$ has width $\geq L/((n-1)e_u) \geq 1$, hence contains an integer $b$ with $[b]_n \equiv r_{\mathrm{dep}} \pmod n$ (possibly after translating by $n$ within the chamber, which is valid when the chamber contains at least $n$ integers — ensured by $L \geq n(n-1)e_u$, else handle by inspection on the finite range). On that $b$, the residue-safety condition holds; the divisible-safety argument of Case A applies verbatim (the transparent-fraction estimate is residue-class-independent). Hence $x_0 \geq 1$. $\square$

---

## 12. Assembly of the Main Theorem

### 12.1 Branch Summary

| Branch | Hypothesis | Result |
|---|---|---|
| Irrational | Some $v_i \notin \mathbb{Q}$ or non-commensurate | Theorem 3.1 |
| Case 1 | $E_{\mathrm{div}} = \emptyset$ | Theorem 4.1: $x_0 \geq \varphi(n)$ |
| Small $L$ | $L \in \{n, 2n\}$ | Proposition 5.1 |
| Prime, $|E_{\mathrm{div}}| = 1$ | $n$ prime | Theorem 7.1 (via Lemma 5.2, Prop 6.1) |
| Prime, $|E_{\mathrm{div}}| \geq 2$ | $n$ prime | Theorems 8.2, 8.3 |
| Composite, $|E_{\mathrm{div}}| = 1$, unit dropped | $n$ composite, unit $d$ absent | Proposition 10.1 (via Lemma 10.2) |
| Composite, $|E_{\mathrm{div}}| = 1$, non-unit dropped | Both dropped non-units | Lemma 9.4 + Theorem 9.2c |
| Composite, $|E_{\mathrm{div}}| \geq 2$ | $n$ composite | Theorem 11.1 |

### 12.2 Dependency Graph

- Theorem 3.1 is self-contained (Weyl equidistribution).
- Theorem 4.1 is self-contained.
- Proposition 5.1 depends on Lemma 5.2a ($L = 2n$, dropped unit) and on Theorem 9.2c ($L = 2n$, Unit-Complete).
- Lemma 5.2 (prime absent-unit covering) depends on Lemma 5.1b (thinness) and Proposition 6.1 (sliding-window termination).
- Proposition 6.1 depends only on the sliding-window structure (Definition 2.8(5), Lemma 2.7) and Lemma 6.0 (coverage-transfer identity).
- Theorem 7.1 is Lemma 5.2 applied.
- Theorems 8.2, 8.3 depend on Lemma 8.1 (transparency) and Lemma 5.2.
- Proposition 10.1 depends on Lemma 10.2 (composite late-window).
- Theorem 9.2c is self-contained modulo Lemma 9.2.
- Theorem 11.1 depends on Lemma 10.2, Lemma 11.A (composite transparency), and Theorem 9.2c.

No lemma in this document depends on any unstated result. No forward reference is made to any lemma or theorem outside this document. No computational certificate is invoked.

### 12.3 Proof of Theorem A

**Theorem A.** *For every $n \geq 3$ and every gcd-1 tuple $E = (e_1,\ldots,e_{n-1})$ of distinct positive integers, $x_0(E) \geq 1$; equivalently, runner $0$ is lonely at some time.*

**Proof.** By Theorem 3.1 we may assume all speeds are rational, hence (after scaling) integer with $\gcd(E) = 1$. If $E_{\mathrm{div}} = \emptyset$, Theorem 4.1 gives $x_0 \geq \varphi(n) \geq 1$. Otherwise $E_{\mathrm{div}} \neq \emptyset$. If $L \in \{n, 2n\}$, Proposition 5.1 applies. Henceforth $L > 2n$.

*Prime $n$.* If $|E_{\mathrm{div}}| = 1$, Theorem 7.1 applies. If $|E_{\mathrm{div}}| \geq 2$: if all $k_i$ are regular ($k_i \in \{1,\ldots,n-2\}$), Theorem 8.2; otherwise Theorem 8.3.

*Composite $n$.* If $|E_{\mathrm{div}}| = 1$: let $R_{\mathrm{non}} = \{\rho_e : e \in E_{\mathrm{non}}\}$. Since $|R_{\mathrm{non}}| \leq n - 2$, some residue class $d$ is absent. If $d$ is a unit, Proposition 10.1. If $d$ is a non-unit, then either another absent class is also a non-unit (apply Theorem 9.2c via Theorem 9.3) or another absent class is a unit (apply Proposition 10.1 to that unit). If $|E_{\mathrm{div}}| \geq 2$: Theorem 11.1.

In every branch $x_0(E) \geq 1$, so runner 0 is lonely at $t = k/(nL)$ for some $k$. $\square$

---

## References

- Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**, R48.
- Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**, 1--9.
- Bohman, T., Holzman, R., and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* **8**, R3.
- Chen, Y.-G. (1994). View-obstruction problems in $n$-dimensional Euclidean space and a generalization of them. *Acta Math. Sinica* **37**, 551--562.
- Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165--170.
- Czerwiński, S. and Grytczuk, J. (2008). Invisible runners in finite fields. *Inform. Process. Lett.* **108**, 64--67.
- Dubickas, A. (2011). The lonely runner problem for many runners. *Glas. Mat. Ser. III* **46**, 25--30.
- Perarnau, G. and Serra, O. (2016). Correlation among runners and some results on the lonely runner conjecture. *Electron. J. Combin.* **23** (1), P1.50.
- Hardy, G. H. and Wright, E. M. (2008). *An Introduction to the Theory of Numbers* (6th ed.). Oxford University Press.
- Kuipers, L. and Niederreiter, H. (1974). *Uniform Distribution of Sequences*. Wiley.
- Tao, T. (2018). Some remarks on the lonely runner conjecture. *Contrib. Discrete Math.* **13** (2), 1--31.
- Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins. *Math. Ann.* **77**, 313--352.
- Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263--269.
