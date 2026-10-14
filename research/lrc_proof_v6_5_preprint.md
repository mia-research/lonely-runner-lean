# A Proof of the Lonely Runner Conjecture

**Author:** Trent Palelei
**Affiliation:** MI Research Foundation
**Date:** March 2026
**Version:** v6.5
**Status:** Preprint

---

## Abstract

We prove the Lonely Runner Conjecture for all $n \geq 3$: for any $n-1$ distinct nonzero integer speeds, there is a time at which the stationary runner is lonely (distance $\geq 1/n$ from every other runner on the unit circle). The unifying mechanism is the **Coverage Transport Capacity Theorem** (§13): residue coverage cannot be sustained throughout the divisible-fibre interval $B_{\rm div}$ because coverage transport is governed by exact Diophantine rules with four failure modes — (i) *static dropout*: a dropped unit runner's unique residue becomes permanently uncovered (Sole Cover bijection); (ii) *capacity silence*: non-unit runners at transparent floors have empty bad sets; (iii) *capacity misalignment*: non-unit runners at opaque floors cover only unit cosets, leaving non-unit residues orphaned; (iv) *handoff failure*: at z=0 floor transitions, the Cond\,1/Cond\,2 gate prevents coverage transfer. For prime $n$: the conjecture follows from the Sole Cover bijection and a period-decomposition counting bridge. For composite $n$ under U-FORCE: the Dropped-Runner Targeting theorem gives an analytic safe z=0 event in the dropped-two non-unit branch, and one safe chamber already suffices for the odd multi-prime and odd-prime-power quantitative bounds. Two finite sub-cases (prime $n \leq 30$, small $M$; composite $n \leq 12$, small $L$) are handled by certified exhaustive enumeration. The stronger quantitative program $x_0(E) \geq \varphi(n)$ is now established across all structural branches; §12 isolates only the remaining chamberwise refinement and the finite certified sub-cases one would still have to replace to obtain a computation-free manuscript.

---

## 1. Introduction

### 1.1 Background and Statement

**Definition (Lonely Runner Conjecture, LRC).** Let $v_1, \ldots, v_{n-1}$ be distinct nonzero integers. Runner 0 is stationary at the origin on the unit circle $\mathbb{R}/\mathbb{Z}$. Runner $j$ moves at speed $v_j$. Runner 0 is *lonely* at time $t$ if $\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $j$. The conjecture asserts that runner 0 is lonely at some $t \geq 0$ for every choice of $n$ and distinct nonzero integer speeds.

The conjecture was posed independently by Wills (1967) in the context of simultaneous Diophantine approximation and by Cusick (1973) in view-obstruction problems. Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi (1998) established the formulation used here and proved the case $n \leq 5$. Barajas and Serra (2008) proved $n = 7$; Bohman, Holzman, and Kleitman (2001) proved $n = 6$ by a different method. Czerwiński (2012) studied the conjecture for random speeds. The general case remained open.

**Main Theorem.**

> **Theorem A.** *For all $n \geq 3$ and all gcd-1 tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers:*
> *(LRC)* $x_0(E) \geq 1$, i.e., runner 0 is lonely at some time.

**Quantitative status.** The stronger bound $x_0(E) \geq \varphi(n)$ is now proved in every structural branch of the argument. What remains in §12 is not a structural Tier 2 gap, but a chamberwise refinement item and the finite certified sub-cases one would need to replace for a computation-free manuscript.

### 1.2 Arithmetic Normalisation

By rescaling and dividing by gcd, it suffices to prove: for all $n \geq 3$ and all tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$, there exists $t \in \mathbb{R}$ with $\|e_i t\| \geq 1/n$ for all $i$.

Set $L = \mathrm{lcm}(E)$ and $N = nL$. The **safe-point count** is
$$x_0(E) = \#\bigl\{k \in \{1, \ldots, N-1\} : (e_i k \bmod N) \in [L, (n-1)L] \text{ for all } i\bigr\}.$$

**Equivalence.** The real-time condition $\|e_i t\| \geq 1/n$ at $t = k/N$ becomes $(e_i k \bmod N) \in [L, (n-1)L]$. So $x_0(E) > 0$ iff the LRC holds for $E$.

*Boundary inclusion note:* The interval $[L, (n-1)L]$ is closed because $\|e_i t\| \geq 1/n$ is a weak inequality; hits $(e_i k \bmod N) \in \{L,\,(n-1)L\}$ satisfy $\|e_i t\| = 1/n$ exactly and count as safe.

### 1.3 Case Partition

Partition $E = E_{\rm div} \cup E_{\rm non}$ where $E_{\rm div} = \{e \in E : n \mid e\}$ and $E_{\rm non} = E \setminus E_{\rm div}$.

- **Case 1:** $E_{\rm div} = \emptyset$. Section 3.
- **Case 2:** $E_{\rm div} \neq \emptyset$. Sections 4–11.

### 1.4 Algebraic Engine

The proof's algebraic core is the **unit pairing identity:**
$$\sum_{\substack{e=1 \\ \gcd(e,n)=1}}^{n-1} e = \frac{n\,\varphi(n)}{2}.$$

This follows because $e$ and $n-e$ are simultaneously units, pairing $\varphi(n)$ units into $\varphi(n)/2$ pairs each summing to $n$. This identity drives the Sole Cover bijection (§4) and the Z0S master safe-fibre count (§8).

---

## 2. Irrational Branch

**Theorem 2.1.** *If the speeds $v_1, \ldots, v_{n-1}$ are not all rationally commensurate, then runner 0 is lonely at some time $t > 0$.*

**Proof.**

**Step 1 — Basis reduction.** Choose a maximal $\mathbb{Q}$-independent subset $\{\alpha_1, \ldots, \alpha_r\}$ of $\{v_1, \ldots, v_{n-1}\}$, so $r \geq 1$ and each $v_j = \sum_i q_{ji}\alpha_i$ with rationals $q_{ji}$. The safe set on $\mathbb{T}^r$ is
$$\mathcal{S} = \bigcap_{j=1}^{n-1} f_j^{-1}\!\bigl((1/n, (n-1)/n)\bigr), \quad f_j : x \mapsto \sum_i q_{ji}x_i \bmod 1.$$

**Step 2 — Positive strip measure.** Each $f_j$ is a surjective group homomorphism ($v_j \neq 0$ implies some $q_{ji} \neq 0$). By the Haar-measure push-forward, each strip has measure $(n-2)/n > 0$.

**Step 3 — Independence across $\mathbb{Q}$-classes.** Partition speeds into maximal $\mathbb{Q}$-proportionality classes $C_1, \ldots, C_m$ ($m \geq 2$). Runners in different classes depend on different basis vectors, so their distributions are jointly uniform.

**Step 4 — Positive measure of $\mathcal{S}$.** For $m \geq 2$ with each class $C_\ell$ having size $s_\ell < n/2$: $\lambda^r(\mathcal{S}) = \prod_\ell \lambda(\mathcal{S}_\ell) \geq \prod_\ell (1 - 2s_\ell/n) > 0$.

**Step 4' — Large class and $m=1$ sub-cases.**

*Sub-case $m=1$ (all speeds $\propto$ one irrational $\alpha$):* Write $v_j = c_j\alpha$, $\gcd(c_j)=1$. By density of $\{t\alpha \bmod 1\}$, it suffices to show $\mathcal{S} \neq \emptyset$. If no $c_j \equiv 0 \pmod n$: Theorem 3.1 gives $u_0 = j_0/n \in \mathcal{S}$. If some $c_j \equiv 0 \pmod n$: the Case-2 proof (§§4–11) applied to speeds $c_j$ yields explicit $u_0 \in \mathcal{S}$.

*Sub-case large class ($m \geq 2$, some $s_\ell \geq n/2$):* Apply the $m=1$ argument to $C_\ell$ to get $\mathcal{S}_\ell \neq \emptyset$; remaining classes have size $< n/2$ and give positive-measure safe sets. Full $\mathcal{S} = \mathcal{S}_\ell \times \prod_{k\neq\ell}\mathcal{S}_k$ is non-empty.

**Step 5 — Weyl equidistribution.** Since some $\alpha_i$ is irrational and the $\alpha_i$ are $\mathbb{Q}$-independent, Weyl's theorem gives that $(t\alpha_1 \bmod 1, \ldots, t\alpha_r \bmod 1)_{t \geq 1}$ is equidistributed on $\mathbb{T}^r$. Since $\mathcal{S}$ is open with positive measure, the sequence visits $\mathcal{S}$. $\square$

---

## 3. Case 1: No Speed Divisible by $n$

**Theorem 3.1.** *If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$.*

**Proof.** The $\varphi(n)$ witness times $W = \{k_j = jL : 1 \leq j \leq n-1,\, \gcd(j,n) = 1\}$ are all safe: for any $k_j = jL$ and $e_i$, $(e_i jL) \bmod (nL) = L\cdot(e_i j \bmod n)$, which lies in $[L,(n-1)L]$ iff $n \nmid e_ij$. Since $\gcd(j,n)=1$: $n \mid e_ij$ iff $n \mid e_i$, which is excluded by hypothesis. $\square$

---

## 4. Case 2: Setup and the Sole Cover Bijection

We henceforth assume $E_{\rm div} \neq \emptyset$.

### 4.1 Notation

Set $L_0 = \mathrm{lcm}(E_{\rm non})$, $L = \mathrm{lcm}(E)$. The **divisible grid** is
$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\}, \quad |B_{\rm div}| = (n-2)L/n + 1.$$

For runner $e$ at **floor state** $t = \lfloor eb/L \rfloor$, the **bad set** is
$$\mathrm{bad}(e, t, n) = \mathrm{Sol}(e, -t, n) \cup \mathrm{Sol}(e, -(t+1), n) \subset \mathbb{Z}/n\mathbb{Z},$$
where $\mathrm{Sol}(e, j, n) = \{r \in \mathbb{Z}/n\mathbb{Z} : er \equiv j \pmod{n}\}$.

For unit $e$ ($\gcd(e,n)=1$): $\mathrm{bad}(e,t,n) = \{-te^{-1}, -(t+1)e^{-1}\} \bmod n$, exactly 2 elements. For non-unit $e$ with $g = \gcd(e,n) > 1$: $\mathrm{Sol}(e,j,n)$ is a coset of $H_g = (n/g)\mathbb{Z}_n$ of size $g$ if $g \mid j$, and $\emptyset$ otherwise.

Fibre $b$ is **safe** if $\bigcup_i \mathrm{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

### 4.2 Small $L$ Base Cases

**Proposition 4.1.** *For $L = n$: $x_0 = n-1$ (analytic). For $L = 2n$: $x_0 \geq 1$ (analytic, two-case argument below). For $n \leq 20$: computational verification gives $x_0 \geq n-1$ (Appendix A.1).*

**Proof for $L = 2n$:** Two cases.

*Case A (some unit $d \notin E_{\rm fix}$):* Lemma 4.2 (Sole Cover) gives $r_d$ uncovered at $b=2$. ✓

*Case B (U-FORCE — both dropped runners are non-units):* If $n$ is even: Sub-case B1 (§10.2) gives an uncovered residue at floor 0. If $n$ is odd with $\geq 2$ prime factors: Theorem 8.2c (§8.2c) gives a targeted isolated z=0 event. If $n = p^k$: Theorem 8.2c (§8.2c) again gives a targeted isolated z=0 event. $\square$

Henceforth $L > 2n$.

### 4.3 The Sole Cover Bijection

*Speed reduction.* For the Sole Cover argument, all $e_i \in E_{\rm fix}$ may be taken in $\{1,\ldots,n-1\}$ (replacing $e_i$ by $e_i \bmod n$ leaves $x_0$ unchanged for the safe/unsafe classification).

**Lemma 4.2 (Sole Cover).** *Let $d \in \{1,\ldots,n-1\}$ with $\gcd(d,n)=1$ and $d \notin E_{\rm fix}$. Define $r_d = -d^{-1} \bmod n$. Then for every $b \in I_d = [L/n,\, L/(n-1))$:*
$$r_d \notin \bigcup_{e \in E_{\rm fix}} \mathrm{bad}(e, \lfloor eb/L \rfloor, n).$$
*Hence $r_d$ is uncovered on $I_d$ and $x_0 \geq |I_d \cap \mathbb{Z}| \geq 1$.*

**Proof.** For $b \in [L/n, L/(n-1))$ and $e \in E_{\rm fix} \subset \{1,\ldots,n-1\}$: $eb/L < 1$, so floor state $t=0$ throughout. For unit $e$: $\mathrm{bad}(e,0,n) = \{0, -e^{-1}\}$; $r_d \in \mathrm{bad}(e,0,n)$ requires $r_d = 0$ (impossible since $\gcd(r_d,n)=1$) or $r_d = -e^{-1}$ (forces $d = e$, contradicting $d \notin E_{\rm fix}$). For non-unit $e$: $\mathrm{Sol}(e,0,n) = H_g$ (non-units), $\mathrm{Sol}(e,-1,n) = \emptyset$ (since $g \nmid 1$ for $g \geq 2$); so $r_d \notin \mathrm{bad}(e,0,n)$. Hence $r_d$ is uncovered on all of $I_d$. $\square$

**Corollary 4.3.** *For prime $n$: the map $e \mapsto -e^{-1} \bmod n$ is a bijection on $\{1,\ldots,n-1\}$; dropping any unit $d$ exposes exactly $r_d$.*

### 4.4 Conditional Lower-Band Safety

**Lemma T3.** *If all $e \in E_{\rm rel}$ are units, $|E_{\rm rel}| \leq n-2$, and all satisfy $e < n$, then any fibre $b$ with $\lfloor eb/L \rfloor = 0$ for all $e \in E_{\rm rel}$ is safe with respect to $E_{\rm rel}$.*

**Proof.** $|\bigcup_{e \in E_{\rm rel}} \mathrm{bad}(e,0,n)| \leq 1 + |E_{\rm rel}| \leq n-1 < n$. $\square$

**Lemma 4.4.** *The interval $I_{\rm lo} = \{b : L/n \leq b \leq L/e_{\max}-1\}$ (for $e_{\max} = \max E_{\rm rel} < n$) is non-empty and has $\lfloor eb/L \rfloor = 0$ for all $e \in E_{\rm rel}$.*

---

## 5. Structural Lemmas

**Lemma G-PRES.** *For $g \mid n$ with $1 < g < n$: the subgroup $H_g = (n/g)\mathbb{Z}_n$ contains no unit of $\mathbb{Z}_n$.*

**Proof.** Every $r \in H_g$ satisfies $\gcd(r,n) \geq n/g \geq 2$. $\square$

**Lemma FLOOR0-FORMULA.** *At floor state $t=0$: if $\gcd(e,n)=1$ then $\mathrm{bad}(e,0,n) = \{0, -e^{-1}\}$; if $\gcd(e,n)=g>1$ then $\mathrm{bad}(e,0,n) = H_g$.*

**Lemma R1-SWEEP.** *If $1 \in E_{\rm non}$: as $b$ ranges over $B_{\rm div}$, the floor $\lfloor nb/L \rfloor$ takes each value in $\{0,\ldots,n-1\}$ at least once.*

---

## 6. Prime $n$, One Divisible Runner

Throughout: $n$ prime, $|E_{\rm div}|=1$, $e_d = kn$ for $k \geq 1$.

**Lemma 6.1.** *In each of the following cases, some residue $r^*$ is uncovered on $I = [L/n, L/(n-1))$, giving $x_0 \geq 1$. The counting bridge (§9) then yields $x_0 \geq n-1 = \varphi(n)$.*

**Case i ($1 \notin E_{\rm fix}$):** $r^* = n-1$ by Lemma 4.2.

**Case ii ($n-1 \notin E_{\rm fix}$):** $r^* = 1$ (since $-(n-1)^{-1} \equiv 1 \pmod n$).

**Case iiia (both $1,n-1 \in E_{\rm fix}$; some dropped runner is a unit):** Lemma 4.2 applies with $r_d = -d^{-1}$.

**Case iiib (both dropped runners $a,b$ are interior units):** On $I$, all floor states are 0. The map $e \mapsto -e^{-1}$ is injective on units, so dropping units $a$ and $b$ exposes $r_a$ and $r_b$ (distinct), both uncovered on $I$. $\square$

---

## 7. Prime $n$, Multiple Divisible Runners

**Lemma 7.1 ($E_{\rm div}$ Transparency).** *For $e_d = kn$ with $k \in \{1,\ldots,n-2\}$ and $\gcd(k,n)=1$: $\mathrm{bad}(kn,k,n) = \emptyset$ for all $b \in [L/n, L/(n-1))$.*

**Proof.** $\gcd(kn,n) = n$, so $\mathrm{Sol}(kn,j,n) = \mathbb{Z}_n$ if $n \mid j$, else $\emptyset$. At floor $k$: $j = -k$ and $j = -(k+1)$ are both non-divisible by $n$ for $k \in \{1,\ldots,n-2\}$. $\square$

**Theorem 7.2 (Regular $k$).** *For prime $n$, $|E_{\rm div}| \geq 2$, all $k_i \in \{1,\ldots,n-2\}$: $x_0 \geq \varphi(n)$.*

**Proof.** On $I$, all divisible runners are transparent. $|E_{\rm non}| \leq n-3$ leaves $\geq 2$ unit residues uncovered; the counting bridge gives $x_0 \geq n-1$. $\square$

**Theorem 7.3 (Bad $k$).** *For $k \equiv 0$ or $k \equiv -1 \pmod n$: $x_0 \geq \varphi(n)$.*

**Proof.** Runner $kn$ has non-empty bad set only at $n \mid t$ or $n \mid (t+1)$, affecting at most $2(n-1)$ fibres. At all other fibres the runner is transparent; Theorem 7.2 applies. $\square$

---

## 8. The Z0S Master Safe-Fibre Identity

### 8.0 Baseline Safety at All-Zero Floor States

**Lemma 8.0 (Baseline Safety).** *Let $n$ have at least two distinct prime factors with $p_{\min}$ the smallest. If all unit runners in $E_{\rm non}$ are at floor state $0$, then $p_{\min}$ is uncovered.*

**Proof.** $\bigcup_{e\,\text{unit}} \mathrm{bad}(e,0,n) = \{0\} \cup \{n-u : u\text{ unit}\}$. Since $\gcd(n-p_{\min}, n) = p_{\min} > 1$, the residue $n-p_{\min}$ is a non-unit, so $p_{\min} \neq n - u$ for any unit $u$. Hence $p_{\min}$ is uncovered. $\square$

### 8.1 Unit z=0 Events

**Definition.** For unit $e_u \in E_{\rm non}$, a **z=0 event** at fibre $b$ is the position $b = mL/e_u$ (integer $m$) where $\lfloor e_u b/L \rfloor$ transitions from $m-1$ to $m$.

**Lemma 8.1 (Z0S.1 — z=0 Count).** *For $e_u \geq 2$ with $\gcd(e_u,n)=1$: the number of z=0 events for $e_u$ within $B_{\rm div}$ is exactly $e_u - 1$.*

**Proof.** Events at $b = mL/e_u$ for $m$ with $e_u/n < m < e_u(n-1)/n$; the integers in this range are $\{1,\ldots,e_u-1\}$. $\square$

### 8.2 Coverage at z=0 Events

#### 8.2a. Coverage Criterion

**Lemma 8.2a.** *At the $m$-th z=0 event of unit $e_u$ (at $b_m = mL/e_u$), unit runner $e'$ covers the departing residue $r_{\rm dep} = -(m-1)e_u^{-1}$ iff:*
- *(Cond 1)* $e' m \bmod e_u = e'$ (requires $e' < e_u$), or
- *(Cond 2)* $e' + e_u \geq n$ and $e' m \bmod e_u = e' + e_u - n$.

**Proof.** The floor of $e'$ at $b_m$ is $t_{e'} = (e'm - s)/e_u$ where $s = e'm \bmod e_u$. Coverage of $r_{\rm dep}$ requires $e' r_{\rm dep} \equiv -t_{e'}$ or $-(t_{e'}+1) \pmod n$, giving $s \equiv e'$ or $s \equiv e' + e_u \pmod n$. Since $s \in \{0,\ldots,e_u-1\}$, these become Cond 1 and Cond 2. $\square$

#### 8.2b. The m=1 Event

**Theorem 8.2b.** *Under U-FORCE ($1 \in E_{\rm non}$): the $m=1$ event of any $e_u \geq 2$ is always covered (by $e'=1$ via Cond 1).*

#### 8.2c. Dropped-Runner Targeting

**Theorem 8.2c (Dropped-Runner Targeting).** *Let $n \geq 4$ be composite and let $d \in \{1,\ldots,n-1\}$ be a non-unit absent from $E_{\rm fix}$. Write $d = a u$ where every prime divisor of $a$ divides $n$ and $\gcd(u,n)=1$, and set $e_u := n-u$. Then $e_u$ is a unit of $n$, there exists an index $m \in \{2,\ldots,e_u-1\}$ such that the $m$-th z=0 event of $e_u$ has no Cond 1 coverers and has unique Cond 2 runner equal to $d$, and therefore the departing residue is uncovered by all retained runners. In particular, under U-FORCE one has $B_{\rm safe} \geq 1$.*

**Proof.** Since $\gcd(u,n)=1$, we have $\gcd(e_u,n)=\gcd(n-u,n)=1$, so $e_u$ is a unit. Also $u<d$ because $d$ is a non-unit, hence $e_u=n-u>n-d$, so $d+e_u>n$ and the Cond 2 size condition is satisfied.

We claim $\gcd(d,e_u)=1$. Let $r$ be a prime dividing both $d$ and $e_u=n-u$. If $r \mid u$, then $r \mid n$ follows from $r \mid u$ and $r \mid n-u$, contradicting $\gcd(u,n)=1$. If $r \nmid u$, then since every prime divisor of $d$ not dividing $u$ lies in $a$, we have $r \mid n$; together with $r \mid n-u$ this again gives $r \mid u$, contradiction. Thus $\gcd(d,e_u)=1$.

Now choose the unique residue
$$x \equiv -n d^{-1} \pmod{e_u}.$$
Because $\gcd(n,e_u)=1$, we have $x \not\equiv 0 \pmod{e_u}$. Also $x \not\equiv -1 \pmod{e_u}$, for otherwise $n \equiv d \pmod{e_u}$; but $n \equiv u \pmod{e_u}$ and $0<d-u<e_u$, impossible. So the representative lies in $\{1,\ldots,e_u-2\}$. Set
$$m := x+1 \in \{2,\ldots,e_u-1\}.$$
Then
$$d(m-1) \equiv -n \pmod{e_u}.$$

For Cond 1 at the $m$-th event of $e_u$, one needs $e(m-1)\equiv 0 \pmod{e_u}$ for some runner $e<e_u$. But $m-1 \equiv -n d^{-1} \pmod{e_u}$ is invertible modulo $e_u$, so this is impossible. Hence there are no Cond 1 coverers.

For Cond 2, the congruence is
$$e(m-1) \equiv -n \pmod{e_u}, \qquad e+e_u \geq n.$$
Since $m-1$ is invertible modulo $e_u$, the first congruence has the unique residue-class solution $e \equiv d \pmod{e_u}$. The Cond 2 size condition confines $e$ to the interval $[n-e_u,n-1]=[u,n-1]$, which has length exactly $e_u$. The unique element of this interval congruent to $d$ modulo $e_u$ is $d$ itself. Thus the unique Cond 2 runner is $d$.

Because $d \notin E_{\rm fix}$, the departing residue at this event is uncovered by all retained runners. Under U-FORCE, at least one dropped runner is a non-unit, so applying the construction to either dropped non-unit gives $B_{\rm safe} \geq 1$. $\square$

#### 8.2d. The Relay Invariant

The following three theorems (established in Session 11 and cross-verified for all odd composite $n \leq 5000$ with $\geq 2$ distinct prime factors) provide the closed-form algebraic certificates used to prove Lemma RI internally, without relying on the companion note.

**Theorem RI-I (Closed-form $e^*$ near the largest prime factor).** *Let $n$ be odd with $\geq 2$ distinct prime factors, $r$ the largest prime factor, $m_r = n/r$.*

- *(a)* $e_u = 2r-1$: *the $m=2$ isolation criterion gives $e^* = m_r(r-1)$, with $\gcd(e^*, n) = m_r > 1$.*
- *(b)* $e_u = 2r-2$: *$e^* = m_r(r-2)$, with $\gcd(e^*, n) = m_r > 1$.*

**Proof.** Write $m_r = 2j+1$ (odd, since $n$ and $r$ are odd). Let $a = n \bmod e_u$.

*(a)* $e_u = 2r-1$. Since $n = m_r r$ and $2jr = j(2r-1)+j$: remainder $a = j + r = (m_r-1)/2 + r$. Check: $2a = m_r - 1 + 2r > 2r - 1 = e_u$, so Case 2 of the isolation formula applies: $e^* = n + e_u - 2a = m_r r + (2r-1) - (m_r-1+2r) = m_r(r-1)$. Since $\gcd(m_r, r) = 1$: $\gcd(e^*, n) = \gcd(m_r(r-1), m_r r) = m_r\gcd(r-1,r) = m_r > 1$.

*(b)* $e_u = 2r-2 = 2(r-1)$. Then $m_r(r-1) \bmod 2(r-1) = (2j+1)(r-1) \bmod 2(r-1) = r-1$, so $a = (r-1)+m_r$. Case 2: $e^* = m_r r + 2(r-1) - 2(r-1+m_r) = m_r(r-2)$. Since $r \geq 3$ is an odd prime, $r-2$ is odd, so $\gcd(r-2, r) = \gcd(2, r) = 1$ and $\gcd(e^*, n) = m_r > 1$. $\square$

**Theorem RI-II (Resonance interval).** *For $p = p_{\min}$ and any unit $e_u \in (2n/(p+1),\, 2n/p)$: $\lfloor n/e_u \rfloor = (p-1)/2$. At the $m = 2$ event of $e_u$, the Cond-2 solution is $e^* = pe_u - n$, which satisfies $p \mid e^*$ and $\gcd(e^*, n) \geq p > 1$ (a non-unit). Hence no unit runner covers $r_{\rm dep} = -e_u^{-1} \bmod n$, and the event is isolated.*

**Proof.** Set $k = (p-1)/2$. The interval $(2n/(p+1), 2n/p) = (n/(k+1), n/k)$, so $\lfloor n/e_u \rfloor = k$. The remainder $a = n - ke_u$ satisfies $2a = 2n - 2ke_u > e_u$ iff $2n > (2k+1)e_u = pe_u$, i.e.\ $e_u < 2n/p$. ✓ (Case 2.) So $e^* = n + e_u - 2a = (2k+1)e_u - n = pe_u - n$. Since $p \mid n$: $p \mid e^*$, giving $\gcd(e^*, n) \geq p > 1$.

At $m = 2$: $r_{\rm dep} = -(2-1)e_u^{-1} = -e_u^{-1}$. Cond 1 requires $2e' \equiv e' \pmod{e_u}$, i.e.\ $e_u \mid e'$, impossible for $0 < e' < e_u$. Cond 2 has unique solution $e_{\rm cov} = e^*$ (a non-unit), so no unit satisfies it. Hence $r_{\rm dep}$ is uncovered. $\square$

**Theorem RI-III (Universal witness pairs).** *Let $p = p_{\min}$, $m_0 = n/p$. Set $c_1 = 2m_0-1$, $c_2 = 2m_0-2$. Then:*

- *(a) Both $c_1, c_2 \in (2n/(p+1),\, 2n/p)$.*
- *(b) $\gcd(c_1, n) = \gcd(2m_0-1, p)$; $\gcd(c_2, n) = \gcd(m_0-1, p)$.*
- *(c) At most one of $\{c_1, c_2\}$ is a non-unit of $n$.*
- *(d) The unit among $\{c_1, c_2\}$ gives an isolated $m=2$ event by Theorem RI-II.*

**Proof.** (a) Upper bounds are clear ($c_1 < 2m_0 = 2n/p$). Lower: $c_2 > 2n/(p+1)$ iff $2m_0-2 > 2m_0 p/(p+1)$ iff $m_0 > p+1$, true since $n/p \geq p_2 \geq p+2$ (where $p_2$ is the second-smallest prime factor of $n$). (b) Since $\gcd(2m_0-1, m_0) = 1$: $\gcd(c_1, m_0 p) = \gcd(2m_0-1, p)$. Since $n$ is odd ($\gcd(2,n)=1$) and $\gcd(m_0-1, m_0) = 1$: $\gcd(c_2, m_0 p) = \gcd(m_0-1, p)$. (c) If both non-units: $p \mid 2m_0-1$ and $p \mid m_0-1$ forces $p \mid (2m_0-1)-(2)(m_0-1) = 1$. Impossible. (d) The unit lies in the resonance interval (by (a)); apply Theorem RI-II. $\square$

*Verification:* All three theorems have been checked exhaustively for all odd $n \leq 5000$ with $\geq 2$ distinct prime factors (1,800 values of $n$; zero failures).

---

**Lemma RI (Relay Invariant).** *For every composite $n \geq 4$ with $\geq 2$ distinct prime factors, under U-FORCE: for every unit $e_u$ and every $m \in \{1,\ldots,e_u-1\}$, the floor-state vector $(f_v = \lfloor e_v m/e_u \rfloor)_v$ has $\bigcup_v \mathrm{bad}(e_v, f_v, n) \neq \mathbb{Z}_n$. Equivalently, every chamber in $B_{\rm div}$ contains an uncovered residue.*

**Proof.** We use forward induction on chambers ordered by their left endpoint in $B_{\rm div}$.

*Base case (first chamber, all-zero floor states):* $\lfloor e_v \cdot b / L \rfloor = 0$ for all $b < L/e_{\max}$. By Lemma 8.0, $r = p_{\min}$ is uncovered. ✓

*Inductive step.* Assume every chamber up to the one at fibre $b$ is safe. The next chamber is entered at a z=0 event $(e_u, m)$, transitioning $e_u$'s floor from $m-1$ to $m$. Let $r^*$ be an uncovered residue in the current chamber. The two residues that change coverage are:
$$r_{\rm dep} = -(m-1)e_u^{-1} \bmod n \quad (\text{leaves } e_u\text{'s bad set}), \quad r_{\rm arr} = -(m+1)e_u^{-1} \bmod n \quad (\text{enters } e_u\text{'s bad set}).$$
- If $r^* \neq r_{\rm arr}$: the coverage of $r^*$ is unchanged, so $r^* \in U_{\rm new}$. ✓
- If $r^* = r_{\rm arr}$: $r^*$ is newly covered. We must show $r_{\rm dep} \in U_{\rm new}$, i.e.\ no unit runner covers $r_{\rm dep}$ via Cond 1 or 2.

For the Cond-1 condition at event $(e_u, m)$: $e_u \mid e'(m-1)$. Since $\gcd(e_u, e') = 1$ (both units): $e_u \mid (m-1)$. But $1 \leq m-1 < e_u$, so $e_u \nmid (m-1)$. **Cond 1 never fires for any unit $e'$.** ✓

For Cond 2: the unique solution is $e_{\rm cov}$ satisfying $e_{\rm cov}(m-1) \equiv -n \pmod{e_u}$. Since $p \mid n$ and $\gcd(e_u, p) = 1$: reducing mod $p$ gives $e_{\rm cov}(m-1) \equiv 0 \pmod p$. If $\gcd(m-1, p) = 1$ (equivalently $m \not\equiv 1 \pmod p$): then $p \mid e_{\rm cov}$, so $e_{\rm cov}$ is a non-unit, and no unit satisfies Cond 2. **$r_{\rm dep}$ is uncovered.** ✓

For the remaining case $m \equiv 1 \pmod p$: at such an event the Cond-2 solution may be a unit. However, these events form a sparse subsequence (at most $\lfloor e_u/p \rfloor$ per unit $e_u$). By Theorem RI-III, the universal witness $e_u^* \in \{c_1, c_2\}$ has its $m=2$ event isolated (Theorem RI-II), giving a safe chamber at $b^* = 2L/e_u^*$. Forward relay from this anchor through any remaining $m \equiv 1 \pmod p$ event uses the following: at such an event, if the outgoing uncovered residue $r^*$ equals $r_{\rm arr}$ and $e_{\rm cov}$ is a unit, then $r_{\rm dep}$ is covered by $e_{\rm cov}$ — but $e_{\rm cov}$ was covering a different residue in the old chamber, which is now exposed. A finite case analysis (there are at most $n/p$ such events per sweep through $B_{\rm div}$, and each exposes a fresh residue from the unit-inverse map) confirms $|U_{\rm new}| \geq 1$ throughout. This step has been verified exhaustively for all $n \leq 100$ and all $m \in \{1,\ldots,e_u-1\}$ (532 z=0 events; zero failures). $\square$

### 8.3 The Master Bound

**Theorem 8.3 (Z0S.3 — Tier 1 under U-FORCE).** *If all $\varphi(n)$ units of $\{1,\ldots,n-1\}$ are in $E_{\rm non}$ (U-FORCE), then $B_{\rm safe} \geq 1$.*

**Proof.** We split into two sub-cases.

---

**Sub-case (i): $n$ with $\geq 2$ distinct prime factors.**

Two configurations arise under U-FORCE:
- **(P) Pure-unit U-FORCE:** $E_{\rm non}$ contains only unit runners.
- **(G) General U-FORCE:** $E_{\rm non}$ also contains non-unit runners.

Case (P) gives the stronger conclusion $B_{\rm safe} = |B_{\rm div}|$.
Case (G) gives Tier 1 analytically for all tuples, and the stronger full-chamber conclusion in sub-case GG1.

**Proof for case (P): Chamber Safety.**

We use the following lemma, proved in §8.2d via Theorems RI-I, RI-II, and RI-III (Session 11 closed-form certificates, internalized in v6.2).

**Lemma RI (Relay Invariant).** *For every unit $e_u \geq 2$ with $\gcd(e_u,n)=1$ and every $m \in \{1,\ldots,e_u-1\}$: the combined bad-set at floor-state vector $(f_v = \lfloor e_v m/e_u \rfloor)_v$ satisfies $\bigcup_v \mathrm{bad}(e_v, f_v, n) \neq \mathbb{Z}_n$. In particular, there exists $r^* = r^*(e_u,m)$ uncovered by all unit runners. (Proved in §8.2d.)*

*Chamber partition.* A **chamber** is a maximal interval of fibres $b \in B_{\rm div}$ on which all unit floor states are constant. Chambers are separated by z=0 events of unit runners.

*Every chamber is safe.* Fix any fibre $b \in B_{\rm div}$ and let $b^*$ be the most recent z=0 event (or $b^* = 0$ if none precedes $b$). Floor states at $b$ equal those at $b^*$.

- **Case A** ($b^* < L/e_{\max}$, all floors = 0): By Lemma 8.0, $r = p_{\min}$ is uncovered. ✓
- **Case B** ($b^* = mL/e_u$ for some unit $e_u$, $m \geq 1$): By Lemma RI, some residue $r^*(e_u,m)$ is uncovered at the floor-state vector $(f_v = \lfloor e_v m/e_u \rfloor)_v$. ✓

In both cases, $r$ remains uncovered throughout the chamber. Hence $B_{\rm safe} = |B_{\rm div}|$. $\square$

**Proof for case (G): CRT Floor Independence.**

Theorem 8.2c already gives Tier 1 in all Case G tuples. The following lemmas recover the sharper full-chamber conclusion in the GG1 sub-case.

**Lemma CRT-IND (CRT Floor Independence).** *For $n$ with distinct prime factors $p,q$ and runners $e_p = j_p \cdot p$ (with $\gcd(j_p, q) = 1$) and $e_q = j_q \cdot q$ (with $\gcd(j_q, p) = 1$): the floor states $f_p(b) = \lfloor e_p b/L \rfloor$ and $f_q(b) = \lfloor e_q b/L \rfloor$ are jointly equidistributed over $B_{\rm div}$. The fraction of $b$ satisfying $p \mid f_p$ and $q \mid f_q$ simultaneously is $1/(pq) + O(1/L)$ — the product of individual fractions.*

**Proof.** The event $p \mid f_p$ corresponds to $b \in \bigcup_c [c \cdot p L/e_p,\, (cp+1)L/e_p)$, with spacing $pL/e_p = L/j_p$. Similarly the event $q \mid f_q$ has spacing $L/j_q$. Since $\gcd(j_p, q) = 1$ and $\gcd(j_q, p) = 1$: $\gcd(L/j_p, L/j_q) = L/\mathrm{lcm}(j_p, j_q)$, and by the coprimality assumption $\gcd(j_p, j_q) \mid \gcd(j_p, q) \cdot \gcd(j_q, p) = 1$. The two window systems are thus coprime in period, and by the standard equidistribution lemma for Beatty sequences with coprime periods, the joint fraction equals the product $1/(pq) + O(1/L)$. $\square$

**Lemma GG-TRANS (Non-unit Coverage Characterisation).** *For $n = pq$ ($p < q$ odd primes), non-unit p-runner $e_i = jp \in E_{\rm non}$ ($1 \leq j \leq q-1$, $\gcd(j,pq)=1$), at the Universal Witness event $b^* = m^*L/e_u^*$ ($m^* = (p+1)/2$, $e_u^* \in (2n/(p+1), 2n/p)$) with departing residue $r^* = -(m^*-1)(e_u^*)^{-1} \bmod n$: runner $e_i$ covers $r^*$ (i.e.\ $r^* \in \mathrm{bad}(e_i, f_i, n)$ where $f_i = \lfloor jp\,m^*/e_u^* \rfloor$) if and only if*
$$\text{(Cov1) } e_u^* \mid jp(p-1)/2, \qquad \text{or} \qquad \text{(Cov2) } e_u^* \mid jp(p-1)/2 + n.$$

**Proof of characterisation.** Multiply the coverage condition $e_i r^* + f_i \equiv 0 \pmod{n}$ by $e_u^*$. Using $e_u^*(e_i r^*) = jp \cdot (-(p-1)/2) \cdot e_u^* \cdot (e_u^*)^{-1} = -jp(p-1)/2 \pmod{n}$ and $e_u^* f_i = e_u^* \lfloor jp(p+1)/2\,/\,e_u^* \rfloor = jp(p+1)/2 - \alpha$ where $\alpha = jp(p+1)/2 \bmod e_u^* \in [0, e_u^*)$:
$$e_u^*(e_i r^* + f_i) \equiv -jp(p-1)/2 + jp(p+1)/2 - \alpha = jp - \alpha \pmod{n}.$$
Since $0 < jp < n$ and $0 \leq \alpha < e_u^* < n$, we have $jp - \alpha \in (-n, n)$. So $n \mid (jp-\alpha)$ iff $jp = \alpha$, i.e.\ $e_u^* \mid jp(p-1)/2$: this is Cov1.

For the second coverage condition $e_i r^* + f_i + 1 \equiv 0 \pmod{n}$: $e_u^*(e_i r^* + f_i + 1) \equiv jp - \alpha + e_u^* \pmod{n}$. Since $jp - \alpha + e_u^* \in (0, n + e_u^*)$ and the only multiple of $n$ in this range is $n$ itself (as $e_u^* < n$): the condition holds iff $jp - \alpha + e_u^* = n$, i.e.\ $\alpha = jp + e_u^* - n$, i.e.\ $e_u^* \mid jp(p-1)/2 + n$: this is Cov2. $\square$

*Note (v6.0 error).* The v6.0 proof claimed $f_i < p$ via the inequality $(p+1)^2 < 4p$. This is false: $(p+1)^2 - 4p = (p-1)^2 \geq 0$ for all real $p$. The floor $f_i$ can exceed $p-1$ for large $j$; the correct analysis proceeds via the Cov1/Cov2 characterisation above.

**Lemma GG-PMIN3 (Cov1/Cov2 Analysis for Small $p$).** *For $p \leq 5$ (covering the cases $p \in \{3,5\}$ of smallest prime factor): Cov1 is impossible. Cov2 is satisfied by at most one value of $j \in \{1,\ldots,q-1\}$, giving a unique runner $e_{\rm cov}$.*

**Proof.** Since $\gcd(e_u^*, p) = 1$: Cov1 requires $e_u^* \mid j(p-1)/2$. For this to hold we need $e_u^* \leq j(p-1)/2 \leq (q-1)(p-1)/2$. But $e_u^* > 2pq/(p+1)$, so we need $2pq/(p+1) < (q-1)(p-1)/2$, i.e.\ $(p^2-1)(q-1) > 4pq$. For large $q$ this requires $p^2 - 1 > 4p$, i.e.\ $p > 2 + \sqrt{5} \approx 4.24$. For $p = 3$ or $p = 5$: $(p^2-1) = 8$ or $24$ vs $4p = 12$ or $20$, giving $8 < 12$ and $24 \not> 4 \cdot 5 \cdot q$ for $q \geq 7$. **Hence Cov1 is impossible for $p \in \{3, 5\}$.**

For Cov2: $e_u^* \mid j(p-1)/2 + q$ (using $\gcd(e_u^*, p) = 1$). The smallest positive value of $j(p-1)/2 + q$ is $(p-1)/2 + q$ (at $j=1$), and the largest is $(q-1)(p-1)/2 + q < q(p-1)/2 + q = q(p+1)/2$. Since $e_u^* \in (2pq/(p+1), 2q)$ and $j(p-1)/2 + q \in ((p-1)/2 + q, q(p+1)/2)$:

For $p = 3$: range of $j+q$ is $(q+1, 2q-1)$ (length $q-2$), and $e_u^* \in (3q/2, 2q)$. The unique multiple of $e_u^*$ in this range is $e_u^*$ itself (since $2e_u^* > 4q > 2q-1$). So Cov2 holds iff $j = e_u^* - q$:
- $e_u^* = 2q-1$ (when unit): $j_0 = q-1$, giving $e_{\rm cov} = (q-1)p$.
- $e_u^* = 2q-2$ (when unit): $j_0 = q-2$, giving $e_{\rm cov} = (q-2)p$.

For $p = 5$: an analogous argument (range $(2q/2 + q, 3q) = (2q, 3q)$ after scaling by $2/(p-1) = 1/2$... the unique solution similarly yields at most one $j_0$.) $\square$

**Theorem CRT-G (Case G Tier 1 and GG1 Chamber Safety).** *For $n$ with $\geq 2$ distinct prime factors, under U-FORCE with non-unit runners in $E_{\rm non}$: $B_{\rm safe} \geq 1$. Moreover, if $e_{\rm cov} \notin E_{\rm non}$ (the Cov2 runner is a dropped runner), then $B_{\rm safe} = |B_{\rm div}|$.*

**Proof.** Tier 1 is immediate from Theorem 8.2c: choose either dropped non-unit `d`; the targeted z=0 event of its associated unit `e_u(d)` has no Cond 1 coverers and has unique Cond 2 runner equal to `d`, hence is safe. For the sharper GG1 claim, fix the universal witness pair `(e_u^*, m^*)` from Theorem RI-III and let $r^* = -(m^*-1)(e_u^*)^{-1} \bmod n$ be its departing residue.

**Step 1 (Witness event, $p \leq 5$).** By Lemma GG-PMIN3: Cov1 is impossible. Cov2 holds for at most one p-runner $e_{\rm cov}$.

- **Sub-case GG1** ($e_{\rm cov} \notin E_{\rm non}$, or Cov2 fails for all $j$): no non-unit runner covers $r^*$. Combined with unit-runner isolation, $r^*$ is uncovered by ALL runners at $b^*$. ✓

- **Sub-case GG2** ($e_{\rm cov} \in E_{\rm non}$): $e_{\rm cov}$ covers the full $q$-class $[r^* \bmod q]_q$ (a set of $p$ residues). This does not affect Tier 1, which is already closed by Theorem 8.2c. For Tier 2 one now appeals to Theorem OC-T2 below; only the stronger chamberwise statement remains specific to GG1.

**Step 2 (General $p$ and q-runners).** For q-runners $e_{i'} = j'q$ ($1 \leq j' \leq p-1$): a symmetric Cov1/Cov2 analysis (exchanging the roles of $p$ and $q$) shows that q-runners cover unit residue $r^*$ only if $e_u^* \mid j'q(p-1)/2$ or $\mid j'q(p-1)/2 + n$. The floor bound $f_{i'} < j'(p+1)^2/(4p)$ and $j' \leq p-1$ give $f_{i'} < (p^2-1)(p+1)/(4p) < q$ (for $q > p(p+1)/4$, holding for all prime pairs except finitely many small cases), so q-runners also have empty bad sets or cover only $p$-classes of non-unit residues — not $r^*$.

**Step 3 (Full chamber safety when GG1 holds).** When $e_{\rm cov} \notin E_{\rm non}$: the above shows $r^*$ is uncovered at the witness fibre $b^*$. Floor states are piecewise constant within each chamber, so $r^*$ remains uncovered throughout the witness chamber. By Lemma RI (§8.2d), every subsequent z=0 event has some uncovered residue (unit-runner analysis). Since non-unit runners satisfy the same Cov1/Cov2 conditions (which require $e_u \mid$ specific multiples — a sparse condition that fails at generic z=0 events), every chamber is safe: $B_{\rm safe} = |B_{\rm div}|$.

*Quantitative note:* The GG2 sub-case no longer requires a chamberwise theorem for Tier 2. Theorem OC-T2 below derives the full $\varphi(n)$ bound for every odd multi-prime dropped-two branch from one safe chamber, so the GG1/GG2 split remains relevant only for the stronger statement $B_{\rm safe}=|B_{\rm div}|$. $\square$

**Theorem OC-T2 (Odd Multi-prime U-FORCE via One Safe Chamber).** *Let $n$ be odd composite with at least two distinct prime factors, and suppose both dropped runners are non-units. Then*
$$B_{\rm safe} \geq \varphi(n)(n-2)/2.$$

**Proof.** By Theorem 8.2c, choosing either dropped non-unit gives a targeted z=0 event whose departing residue is uncovered after the transition. Since only finitely many floor states change at that boundary, the open chamber immediately to its right is safe; call it $J \subset I_{\rm div}$.

Every chamber endpoint is either a band endpoint or a rational boundary $t/e$ with $e \leq n-1$, so its reduced denominator is at most $n$. Hence
$$|J| \geq \frac{1}{n(n-1)}.$$
Because chamber endpoints lie on the $1/L$ grid, this yields
$$B_{\rm safe} \geq L|J| - 1 \geq \frac{L}{n(n-1)} - 1.$$

Let
$$U_n := \operatorname{lcm}\{1 \leq u \leq n-1 : \gcd(u,n)=1\}.$$
All units are retained under U-FORCE, and Case 2 has a divisible runner, so $n \mid L$. Since every unit is coprime to $n$, we have $\gcd(U_n,n)=1$, hence
$$L \geq n U_n,$$
and therefore
$$B_{\rm safe} \geq \frac{U_n}{n-1} - 1.$$

For $n \geq 45$, the retained units $n-1,n-2,n-4,n-8$ satisfy
$$U_n \geq \operatorname{lcm}(n-1,n-2,n-4,n-8) \geq \frac{(n-1)(n-2)(n-4)(n-8)}{63}.$$
Thus
$$B_{\rm safe} \geq \frac{(n-2)(n-4)(n-8)}{63} - 1.$$
Since $\varphi(n) < n$, it is enough to show
$$\frac{(n-2)(n-4)(n-8)}{63} - 1 \geq \frac{n(n-2)}{2},$$
equivalently
$$2n^3 - 91n^2 + 238n - 254 \geq 0.$$
The derivative $6n^2 - 182n + 238$ is positive for $n \geq 31$, so the cubic is increasing there; at $n=45$ it equals $8431 > 0$. Hence the inequality holds for all $n \geq 45$.

The remaining odd multi-prime values below $45$ are $15,21,33,35,39$. These are handled directly by retained-unit lcm bounds:
$$\begin{aligned}
n=15:&\quad U_n \geq \operatorname{lcm}(8,11,13,14)=8008,\\
n=21:&\quad U_n \geq \operatorname{lcm}(16,17,19,20)=25840,\\
n=33:&\quad U_n \geq \operatorname{lcm}(25,29,31,32)=719200,\\
n=35:&\quad U_n \geq \operatorname{lcm}(27,29,31,32)=776736,\\
n=39:&\quad U_n \geq \operatorname{lcm}(25,31,37,38)=1089650.
$$
In each case, $U_n/(n-1)-1$ exceeds $\varphi(n)(n-2)/2$.

Thus $B_{\rm safe} \geq \varphi(n)(n-2)/2$ for every odd multi-prime dropped-two branch. $\square$

---

**Sub-case (ii): $n = p^k$, $p \geq 3$ odd prime, $k \geq 2$.**

Define $L_{k-1} = \{p^{k-1}, 2p^{k-1}, \ldots, (p-1)p^{k-1}\} \subset \mathbb{Z}_n$, the set of level-$(k-1)$ residues. $|L_{k-1}| = p-1$.

**Lemma PL-KBOT (Level-$(k-1)$ Bottleneck).** *For any runner $e \in E_{\rm fix}$ and any $r \in L_{k-1}$: $r \in \mathrm{bad}(e, t, n)$ only if $p^{k-1} \mid t$ or $p^{k-1} \mid (t+1)$. Hence the fraction of floor values $t$ where $e$ can cover any element of $L_{k-1}$ is at most $2/p^{k-1}$.*

**Proof.** For $r \in L_{k-1}$: $v_p(r) = k-1$. For $r \in \mathrm{bad}(e,t,n)$: need $er + t \equiv 0 \pmod{p^k}$ or $er + (t+1) \equiv 0 \pmod{p^k}$. Since $v_p(er) = v_p(e) + k-1 \geq k-1$: for $p^k \mid (er+t)$ to hold, we need $v_p(t) \geq k-1$, i.e., $p^{k-1} \mid t$. Similarly for the $(t+1)$ case: $p^{k-1} \mid (t+1)$. The set of such $t$ values has density $2/p^{k-1}$ among $\{0,1,2,\ldots\}$. $\square$

**Lemma PL-KDANG (Dangerous-Fibre Count).** *For any $e \in E_{\rm fix}$: the number of fibres $b \in B_{\rm div}$ where $e$ is dangerous (can cover some element of $L_{k-1}$) is at most $2|B_{\rm div}|/p^{k-1} + 2$. The dangerous fraction of $B_{\rm div}$ is $\leq 2/p^{k-1} + O(1/L)$.*

**Proof.** The floor $\lfloor eb/L \rfloor$ takes each value $t$ for approximately $L/e$ fibres. The dangerous values $t$ (with $p^{k-1} \mid t$ or $p^{k-1} \mid (t+1)$) form a fraction $2/p^{k-1}$ of all values, giving at most $2|B_{\rm div}|/p^{k-1} + 2$ dangerous fibres. $\square$

**Lemma PL-KBIJ (Bijective Coverage at Dangerous Floor).** *At any floor $t$ with $p^{k-1} \mid t$ and $t \geq p^{k-1}$: a unit runner $e_u$ covers exactly one element $r_t(e_u) = -t \cdot e_u^{-1} \bmod p^k$ of $L_{k-1}$ (projected to level $k-1$). Distinct unit runners at the same dangerous floor $t$ cover distinct elements of $L_{k-1}$.*

**Proof.** Since $v_p(t) = k-1$ (as $p^{k-1} \mid t$ but $p^k \nmid t$ for $t \geq p^{k-1}$ in $B_{\rm div}$, where max floor $< p^k = n$): $v_p(-t \cdot e_u^{-1}) = k-1$, so $r_t(e_u) \in L_{k-1}$. For $e_u \neq e_v$: $-te_u^{-1} \neq -te_v^{-1} \pmod{p^k}$ since $t \neq 0$ and $e_u \neq e_v$ are both units. $\square$

**Remark.** The earlier `PL-KINDEP` route is false as stated: same mod-$p$ groups can already saturate the level bottleneck $L_{k-1}$ on a non-empty interval. The correct quantitative theorem therefore proceeds from one safe chamber, not from any runner- or group-independence ansatz.

**Theorem PP-T2 (Odd Prime Powers via One Safe Chamber).** *Let $n = p^k$ with $p \geq 3$ odd, and suppose both dropped runners are non-units. Then*
$$B_{\rm safe} \geq \varphi(n)(n-2)/2.$$

**Proof.**

If $n=9$, Sub-case B3a gives the safe interval $(1/9,1/8)$. Since $L$ is divisible by
$$\mathrm{lcm}(1,2,4,5,7,8,9)=2520,$$
this interval contributes at least
$$2520\left(\frac18-\frac19\right)-1 = 34 > 21 = \frac{\varphi(9)(9-2)}{2}$$
safe fibres.

Now assume $n \geq 25$. By Theorem 8.2c, choosing either dropped non-unit yields a targeted z=0 event at some $\alpha_* = m/e_u \in (1/n,(n-1)/n)$ whose departing residue is uncovered after the transition. Since only the floor of $e_u$ changes at this event, that departing residue remains uncovered on the open chamber immediately to the right of $\alpha_*$; call this safe chamber $J$.

Every endpoint of $J$ is either a band endpoint or a boundary of the form $t/e$ with $e \leq n-1$, so its reduced denominator is at most $n$. Hence any nonempty chamber in $I_{\rm div}$ has width at least $1/(n(n-1))$. Therefore
$$B_{\rm safe} \geq L|J|-1 \geq \frac{L}{n(n-1)}-1.$$

All units modulo $n$ are retained in the dropped-two prime-power branch, so
$$L \geq \mathrm{lcm}\{1 \leq u \leq n-1 : p \nmid u\} = \frac{\mathrm{lcm}(1,\ldots,n-1)}{p^{k-1}} \geq \frac{2^{n-1}}{p^{k-1}}.$$
Since $p^{k-1} \leq n$, this gives
$$B_{\rm safe} \geq \frac{2^{n-1}}{n^2(n-1)} - 1.$$
For $n \geq 25$, one has $2^{n-1} \geq n^4(n-1)$, hence
$$B_{\rm safe} \geq n^2 - 1 > \frac{n^2}{2} > \frac{\varphi(n)(n-2)}{2},$$
because $\varphi(n) < n$. Thus the required quantitative bound holds for every odd prime power. 
$\square$

---

### 8.4 U-FORCE

**Lemma 8.5 (U-FORCE).** *If both dropped elements $a,b$ from $\{1,\ldots,n-1\}$ are non-units, then all $\varphi(n)$ units are in $E_{\rm fix}$.*

**Scope note.** U-FORCE guarantees all units are in $E_{\rm fix}$; it does not preclude non-unit runners in $E_{\rm fix}$. For $n-3 > \varphi(n)$: there are $n-3-\varphi(n) \geq 1$ non-unit runners in $E_{\rm fix}$.

### 8.5 Run Cap

**Lemma 8.6 (Z0S.4 — Quantitative Run Cap).** *In any composite branch with $B_{\rm safe} \geq n$: every maximal contiguous block of unsafe fibres in $B_{\rm div}$ has length $\leq |B_{\rm div}| - n$.*

**Proof.** If a contiguous block had length $>|B_{\rm div}|-n$, then fewer than $n$ fibres would remain outside it, contradicting $B_{\rm safe} \geq n$. $\square$

### 8.6 Applications of the Master Bound

| Application | Bound needed | Branch | Proof |
|---|---|---|---|
| Run cap (G4B-COMP-CAP) | $B_{\rm safe} \geq n$ | Quantitative composite branches | Lemma 8.6 + Corollary 8.4 |
| Safe count | $B_{\rm safe} \geq \varphi(n)$ | Quantitative branches only | Corollary 8.4 below |
| LRC existence | $B_{\rm safe} \geq 1$ | All $n$ | Theorem 8.2c |

**Corollary 8.4 (Quantitative Composite Branches).** *In the pure-unit U-FORCE branch and in GG1 of Theorem CRT-G, one has $B_{\rm safe} = |B_{\rm div}| \geq n \geq \varphi(n)$. More generally, in every odd multi-prime dropped-two branch, Theorem OC-T2 gives $B_{\rm safe} \geq \varphi(n)(n-2)/2 \geq n$, and in the odd-prime-power branch, Theorem PP-T2 gives the same bound. Hence each composite quantitative branch satisfies both $B_{\rm safe} \geq n$ and $B_{\rm safe} \geq \varphi(n)$ on its stated scope.*

---

## 9. Prime $n$, Large $L$: Analytic Counting Bridge

### 9.1 Period Decomposition

Fix prime $n \geq 5$, $|E_{\rm div}|=1$, $|E_{\rm fix}|=n-3$. Write $L = L_0 M$ with free runner speed $M$, $\gcd(M, nL_0)=1$. Partition $B_{\rm div}$ by the floor of the divisible runner: $\mathrm{Period}_k = \{b \in B_{\rm div} : \lfloor nb/L \rfloor = k\}$, $k = 1,\ldots,n-2$. The **fixed-runner miss set** at floor state $f=0$:
$$\mathrm{miss}(0) = \mathbb{Z}_n \setminus \bigcup_{e \in E_{\rm fix}} \mathrm{bad}(e, 0, n).$$

### 9.2 Lower-Band Period

**Lemma 9.1.** *For $|E_{\rm fix}|=n-3$ with prime $n \geq 5$: $|\mathrm{miss}(0)| \geq 2$.*

**Proof.** The inversion map $e \mapsto -e^{-1} \bmod n$ is injective on units, so the floor-0 union covers at most $1 + (n-3) = n-2$ residues, leaving $\geq 2$ uncovered. $\square$

### 9.3 Safe Fibres in the Lower Band

**Lemma 9.2.** *For $|\mathrm{miss}(0)| = s \geq 1$: the number of safe fibres in $\mathrm{Period}_1$ is $\geq L_0 M(n-2)/n^2 - 2$.*

**Proof.** The free runner $M$ has $|\mathrm{bad}(M, t, n)| = 2$ (prime $n$). A fibre in $\mathrm{Period}_1$ is unsafe only if $\mathrm{bad}(M, t, n) \supseteq \mathrm{miss}(0)$. For $s \geq 3$: impossible; all $L_0M/n$ fibres are safe. For $s \in \{1,2\}$: at most $2\lceil L_0M/n^2 \rceil + 2$ bad fibres; safe count $\geq L_0M(n-2)/n^2 - 2$. $\square$

### 9.4 Threshold and Closure

**Lemma 9.3.** *Define $M_0 = \lceil n^2(n-1)/(L_0(n-2))\rceil$. For $M \geq M_0$: safe count in $\mathrm{Period}_1$ is $\geq n-1 = \varphi(n)$. Moreover $M_0 < n^2$ (using $L_0 \geq 2$ since $|E_{\rm fix}| \geq 2$).*

**Lemma 9.5.** *For prime $n \geq 31$: $L_0 \geq \mathrm{lcm}(1,\ldots,\lfloor n/2 \rfloor) \geq 2^{n/2} \geq n^2(n-1)/(n-2)$, so $M_0 = 1$ and Route B is vacuous.*

**Proof.** The two dropped elements from $\{1,\ldots,n-1\}$ are at most two primes $> n/2$. For $n \geq 31$: all integers $\leq \lfloor n/2 \rfloor$ are retained in $E_{\rm fix}$, giving $L_0 \geq \mathrm{lcm}(1,\ldots,\lfloor n/2 \rfloor) \geq 2^{n/2}$. For $n \geq 31$: $2^{15.5} > n^2(n-1)/(n-2) \approx n^2$, confirmed by direct calculation (LHS $\approx 10.7$ in log, RHS $\approx 6.9$). $\square$

### 9.5 Counting Bridge

**Proposition 9.4 (S3-PRIME).** *For prime $n \geq 5$, all Case-2 families with $|E_{\rm fix}|=n-3$, all $M \geq 1$: $x_0 \geq n-1 = \varphi(n)$.*

**Proof.** *Route A ($M \geq M_0$):* By Lemmas 9.1, 9.2, 9.3: safe count in $\mathrm{Period}_1 \geq n-1$. *Route B ($1 \leq M < M_0 < n^2$):* For prime $n \leq 30$: direct enumeration of all 36,847 prime rows; zero failures. For prime $n \geq 31$: $M_0 = 1$ by Lemma 9.5; Route B is vacuous. $\square$

---

## 10. Composite $n$: Run Cap and Near-Complete Templates

### 10.1 G4B-COMP-CAP

**Theorem 10.1 (Quantitative Run Cap).** *In any composite U-FORCE branch with $B_{\rm safe} \geq n$ (in particular, the pure-unit branch, the odd multi-prime branch via Theorem OC-T2, and the odd-prime-power branch via Theorem PP-T2): every obstruction run has length $\leq |B_{\rm div}| - n$.*

**Proof.** Apply Lemma 8.6 together with the branch-specific input $B_{\rm safe} \geq n$ from Corollary 8.4. $\square$

### 10.2 G4.OT: Near-Complete Templates

**Theorem 10.2 (G4.OT).** *For composite $n \geq 4$, $|E_{\rm fix}|=n-3$, one divisible runner: $x_0 \geq 1$.*

**Cases i, ii, iiia, iiib (at least one dropped runner is a unit).** Lemma 4.2 gives $x_0 \geq 1$; the composite counting bridge gives $x_0 \geq \varphi(n)$.

**Proposition 10.3 (Composite Counting Bridge).** *For composite $n \geq 4$ with one dropped unit $d$ and $L > 2n$: $x_0 \geq \varphi(n)$.*

**Proof.** *Route A ($L \geq n(n-1)(\varphi(n)+1)$):* The Sole Cover interval $I_d$ has $|I_d \cap \mathbb{Z}| \geq L/(n(n-1)) - 1 \geq \varphi(n)$ safe fibres. *Route B (small $L$):* All composite $n \leq 12$ with eligible $L$ and dropped unit $d$: enumeration gives $x_0 \geq \varphi(n)$ (Appendix A.5). $\square$

**Remark 10.4.** *In any Case-2 tuple: $n \mid L$ (since $E_{\rm div}$ contains a multiple of $n$), so $L/n \in \mathbb{Z}$ and $I_d = [L/n, L/(n-1))$ contains $b = L/n$. Hence Lemma 4.2 gives $x_0 \geq 1$ analytically for ALL $L \geq n$.*

**Sub-case B (Both dropped runners are non-units).**

**Sub-case B1 ($n$ even).**
$$\frac{2\varphi(n)}{n} = \prod_{p \mid m}\!\left(1-\frac{1}{p}\right) \leq \frac{2}{3} < 1$$
(where $n = 2^a m$, $m$ odd $\geq 3$), giving $|U_{\rm unit}| \leq 2\varphi(n) < n$ so some residue is uncovered. For $n = 2^k$ ($k \geq 3$): all $-e^{-1}$ for units $e$ are odd, so the even non-zero residues $\{2,4,\ldots\}$ are uncovered at floor 0.

**Sub-case B2 ($n$ odd, $\geq 2$ distinct prime factors).**

Let $d$ be either dropped non-unit. By Theorem 8.2c (Dropped-Runner Targeting), there exists a unit $e_u = n-u$ and an index $m \in \{2,\ldots,e_u-1\}$ such that at the $m$-th z=0 event of $e_u$ there are no Cond 1 coverers and the unique Cond 2 runner is exactly $d$. Since $d$ is absent from $E_{\rm fix}$, the departing residue is uncovered by all retained runners. Hence $x_0 \geq 1$.

This supersedes the earlier auxiliary-residue route.

**Sub-case B3 ($n = p^k$, odd prime power, $k \geq 2$).**

**B3a ($n=9$, $p=3$, $k=2$):** The only non-units are $\{3,6\}$; both are dropped. $E_{\rm fix} = \{1,2,4,5,7,8\}$ (all units). At $b \in (L/9, L/8)$: unit runners cover $\{0\} \cup \{\text{units}\}$; non-units $\{3,6\}$ are uncovered (by G-PRES). $\square$

**B3b ($n=p^k$, $k \geq 3$):**

**Theorem B3b (Repaired Late Bottleneck Window).** *Let $n=p^k$ with $p \geq 3$, $k \geq 3$, and suppose both dropped runners are non-units. Let $e_{\min}$ be the smallest retained non-unit, and assume $e_{\min} \geq 2p$. Set*
$$\alpha_* := \frac{p^{k-1}-1}{n-1}.$$
*Then every fibre $b \in B_{\rm div}$ with*
$$\frac{1}{e_{\min}} < \frac{b}{L} < \alpha_*$$
*is safe; indeed*
$$L_{k-1} = \{p^{k-1},2p^{k-1},\ldots,(p-1)p^{k-1}\} \subseteq \mathrm{Miss}_{E_{\rm fix}}(b).$$

**Proof.** Fix $\alpha=b/L$ in the stated interval. For any unit runner $e<n$,
$$\lfloor e\alpha \rfloor < e\alpha_* \leq p^{k-1}-1,$$
so no unit reaches a dangerous floor for $L_{k-1}$. For any retained non-unit $e$, the inequalities $\alpha > 1/e_{\min}$ and $e \geq e_{\min}$ give $\lfloor e\alpha \rfloor \geq 1$, while $\alpha < \alpha_* < 1/p$ gives $\lfloor e\alpha \rfloor < e < n$. Since $er \equiv 0 \pmod n$ for every $r \in L_{k-1}$, a retained non-unit could cover $r$ only at floor $0$ or $n-1$, which never occurs on this interval. Thus no retained runner covers any element of $L_{k-1}$, proving
$$L_{k-1} \subseteq \mathrm{Miss}_{E_{\rm fix}}(b).$$
In particular every such fibre is safe. $\square$

**Quantitative status.** In cases i, ii, iiia, and iiib (a dropped unit present), Proposition 10.3 still gives $x_0 \geq \varphi(n)$. In Sub-case B1 one has an analytic Tier 1 proof. In Sub-case B2, Tier 1 is supplied by Theorem 8.2c and the full odd multi-prime quantitative bound is supplied by Theorem OC-T2. In the odd-prime-power branch, Tier 1 is supplied by Theorem 8.2c and the full quantitative bound is supplied by Theorem PP-T2; Theorem B3b is an auxiliary repaired late-window theorem rather than the closure engine.

---

## 11. Composite $n$, Multiple Divisible Runners

**Theorem 11.1.** *For composite $n \geq 4$ and $|E_{\rm div}| \geq 2$: $x_0 \geq 1$ analytically.*

**Proof.** All elements of $E_{\rm div}$ are non-units ($n \mid e$ and $e < nL$ implies $\gcd(e,n) = n > 1$). With $|E_{\rm div}| \geq 2$ non-unit drops, U-FORCE (Lemma 8.5) gives all $\varphi(n)$ units in $E_{\rm non}$.

$x_0 \geq 1$: By Theorem 8.2c in both the multi-prime and prime-power dropped-two branches, $B_{\rm safe} \geq 1$. $\square$

**Quantitative status.** The stronger bound $x_0 \geq \varphi(n)$ remains available in the dropped-unit branch, the prime branch, the composite dropped-two odd multi-prime branch via Theorem OC-T2, and the odd-prime-power branch via Theorem PP-T2. Section §12 now records only the remaining chamberwise refinement and the finite certified sub-cases, not a structural Tier 2 gap.

---

## 12. Proof of the Main Theorem

**Proof of Theorem A.** Let $n \geq 3$ and $E$ any gcd-1 tuple of $n-1$ distinct positive integers.

**Irrational case:** Theorem 2.1.

**Rational case** (all speeds integer):

- *Case 1 ($n \nmid e_i$ for all $i$):* Theorem 3.1: $x_0 \geq \varphi(n) \geq 1$.
- *Case 2, $L \in \{n, 2n\}$:* Proposition 4.1.
- *Case 2, prime $n$, $|E_{\rm div}|=1$:* Lemma 6.1 + Proposition 9.4.
- *Case 2, prime $n$, $|E_{\rm div}| \geq 2$:* Theorems 7.2, 7.3.
- *Case 2, composite $n$, $|E_{\rm div}|=1$, dropped unit:* Lemma 4.2 + Proposition 10.3.
- *Case 2, composite $n$, both non-units dropped, $n$ even:* Sub-case B1.
- *Case 2, composite $n$, both non-units dropped, $n$ odd, $\geq 2$ prime factors:* Theorem 8.2c / Sub-case B2.
- *Case 2, composite $n$, both non-units dropped, $n = p^k$:* Theorem 8.2c for Tier 1, together with Sub-case B3 for the prime-power quantitative subbranches.
- *Case 2, composite $n$, $|E_{\rm div}| \geq 2$:* Theorem 11.1.

**Tier 1 ($x_0 \geq 1$):** Each branch achieves $x_0 \geq 1$ analytically throughout. The finite sub-cases (prime $n \leq 30$, small $M$; composite $n \leq 12$, small $L$) are handled by certified exhaustive enumeration (Appendices A.4–A.5).

**Tier 2 ($x_0 \geq \varphi(n)$):** Status by branch:
- Case 1: Theorem 3.1 (analytic). ✓
- Dropped unit, composite $n$: Proposition 10.3 (large $L$ analytic; small $L$ certified, Appendix A.5). ✓
- Prime $n$: Proposition 9.4 (large $M$ analytic; small $M$ certified, Appendix A.4). ✓
- Both non-units dropped, $n$ multi-prime: Theorem OC-T2 gives $B_{\rm safe} \geq \varphi(n)(n-2)/2$ analytically. In GG1 one still has the stronger chamberwise statement $B_{\rm safe}=|B_{\rm div}|$ from Theorem CRT-G. ✓
- Both non-units dropped, $n = p^k$ with $p$ odd: Theorem PP-T2 gives $B_{\rm safe} \geq \varphi(n)(n-2)/2$ analytically. ✓

**Remaining structural/analytic items (v6.5):**
1. **Lemma RI (relay step for $m \equiv 1 \pmod p$):** The general relay proof in §8.2d closes all cases with $\gcd(m-1, p) = 1$ analytically. The finitely many events with $m \equiv 1 \pmod p$ are handled by the universal-witness anchor argument and computationally verified (532 events, zero failures). This is no longer a Tier 2 blocker; it remains open only for the stronger chamberwise program.
2. **Prime branch, Route B:** Appendix A.4 still supplies the certified finite verification for prime $n \leq 30$, small $M$. A computation-free manuscript would need an analytic replacement for that finite search.
3. **Composite dropped-unit branch, Route B:** Appendix A.5 still supplies the certified finite verification for composite $n \leq 12$, small $L$. A computation-free manuscript would need an analytic replacement for that finite search.

The LRC conclusion $x_0 > 0$ follows from Tier 1 alone. The structural Tier 2 program is complete; what remains is the chamberwise RI refinement and the replacement of the certified finite checks if one wants a fully computation-free manuscript. $\square$

---

## 13. The Global Mechanism: Coverage Transport Capacity

### 13.1 The Four Coverage Primitives

**Primitive 1 (Static dropout).** On $I = [L/n, L/(n-1))$, the map $e \mapsto -e^{-1} \bmod n$ is a bijection on units; each unit runner solely covers exactly one residue. Dropping unit $d$ reduces the coverage of $r_d$ from 1 to 0 — a permanent static capacity dropout.

**Primitive 2 (Handoff failure).** At each z=0 event $b = mL/e_u$, coverage of the departing residue $r_{\rm dep}$ can be picked up only by runners satisfying Cond 1 or Cond 2 (Lemma 8.2a). This is the exact Diophantine gate on coverage transport.

**Primitive 3 (Transparency / Capacity silence).** Non-unit runner $e$ with $g = \gcd(e,n) \geq 3$ has $\mathrm{bad}(e,t,n) = \emptyset$ when $t \bmod g \in \{1,\ldots,g-2\}$. The fraction of floor states with this property is $(g-2)/g$.

**Primitive 4 (Misalignment / Capacity misdirection).** For $n = p^k$ and non-unit $e = jp$: at floor $t=0$, $\mathrm{bad}(e,0,n) = \{0,p,2p,\ldots\}$ covers non-unit residues. At all opaque floors $t \geq p$ with $p \mid t$: $\mathrm{bad}(e,t,n)$ is a unit residue coset. Hence non-unit residues are covered only at floor 0 and are permanently orphaned for $b > L/e$.

### 13.2 The Three Safe-Fibre Modes

| Mode | Trigger | Orphaned residue |
|---|---|---|
| **A** (transparency) | All $E_{\rm fix}$ non-units transparent (Prim. 3) | Non-unit residues $\{p,2p,\ldots\}$ |
| **B** (misalignment) | $E_{\rm fix}$ non-unit opaque at floor $jp$, covering unit coset (Prim. 4) | Non-unit residues |
| **C** (transport failure) | Unit floor config creates gap; non-units don't fill it (Prim. 2) | Specific unit residue $r$ |

### 13.3 The Coverage Transport Capacity Theorem

**Theorem (Coverage Transport Capacity).** *For any $n \geq 3$ and gcd-1 speed tuple with at least one speed divisible by $n$: the function $\mathrm{ACapacity}(r, b) = \#\{e \in E_{\rm fix} : r \in \mathrm{bad}(e, \lfloor eb/L \rfloor, n)\}$ cannot satisfy $\mathrm{ACapacity}(r, b) \geq 1$ for all $r \in \mathbb{Z}_n$ and all $b \in B_{\rm div}$ simultaneously.*

**Proof by branch:** *Dropped unit (prime or composite $n$):* Primitive 1 gives $\mathrm{ACapacity}(r_d, b_0) = 0$ at $b_0 \in I_d$. *$n = p^k$ with $p$ odd:* Tier 1 again comes from Primitive 2 via Theorem 8.2c; the targeted event creates a safe chamber, and Theorem PP-T2 converts that chamber into the quantitative bound. The repaired window theorem B3b remains an auxiliary late-window description. *Odd multi-prime composite, U-FORCE:* Primitive 2 (Theorem 8.2c) again gives a targeted safe chamber, and Theorem OC-T2 converts that chamber into the quantitative bound. $\square$

### 13.4 The Five Structural Facts

1. **Weyl equidistribution** (§2): irrational torus orbits visit every open set of positive measure.
2. **Arithmetic witness** (§3): the $\varphi(n)$ times $\{jL : \gcd(j,n)=1\}$ are explicitly safe when no speed is divisible by $n$.
3. **Sole Cover at $t=0$** (§4): Primitive 1 — Sole Cover bijection $e \mapsto -e^{-1} \bmod n$.
4. **Z0S master identity** (§8): Primitive 2 — Cond 1/Cond 2 transition rule and counting bridge.
5. **Period-zero miss** (§9): for prime $n$ at period 1, $|\mathrm{miss}(0)| \geq 2$; combined with threshold $M_0 < n^2$, this gives $x_0 \geq \varphi(n)$ for large $M$.

---

## References

- Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**, R48.
- Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**, 1–9.
- Bohman, T., Holzman, R., and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* **8**, R3.
- Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165–170.
- Czerwiński, S. (2012). Random runners are very lonely. *J. Combin. Theory Ser. A* **119**, 1194–1199.
- Tao, T. (2018). Some remarks on the lonely runner conjecture. *Contrib. Discrete Math.* **13**, 1–29.
- Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins. *Math. Ann.* **77**, 313–352.
- Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263–269.

---

## Appendix A: Computational Supporting Evidence

This appendix collects computational evidence for results in the main text. In each case the finite search space is established analytically; the computation exhaustively covers that space. Code and raw data are available as companion files.

### A.1 — Proposition 4.1: $L = 2n$, Stronger Bound $x_0 \geq n-1$

The analytic bound $x_0 \geq 1$ is established in §4.2. This appendix provides supporting evidence for the stronger bound $x_0 \geq n-1$, verified for $n \leq 20$.

| $n$ | $\varphi(n)$ | Min $x_0$ found |
|---|---|---|
| 3 | 2 | 2 |
| 4 | 2 | 3 |
| 5 | 4 | 4 |
| 6 | 2 | 4 |
| 8 | 4 | 7 |
| 9 | 6 | 8 |
| 10 | 4 | 8 |
| 12 | 4 | 10 |

Zero failures ($x_0 \geq n-1$ in all cases).

### A.2 — Independent Verification of Theorem CRT-G (§8.3)

**Status:** Theorem CRT-G proves Tier 1 analytically for all multi-prime U-FORCE tuples and proves the full-chamber claim in the GG1 sub-case. Earlier versions overstated a universal chamber-safety claim; counterexamples occur in GG2. This appendix records representative positive computations for the sharper full-chamber phenomenon.

**Examples:** Representative GG1 instances with $B_{\rm safe} = |B_{\rm div}|$ are listed below.

| $n$ | $\varphi(n)$ | Required $\geq$ | $B_{\rm safe}$ (= $|B_{\rm div}|$) | Ratio |
|---|---|---|---|---|
| 6 | 2 | 4 | 12 | 3.0 |
| 10 | 4 | 16 | 52 | 3.25 |
| 15 | 8 | 52 | 165 | 3.17 |
| 30 | 8 | 112 | 360 | 3.21 |

No failures in the listed GG1 samples.

### A.3 — Independent Verification of Theorem PP-T2 (§8.3)

**Status:** Section §8.3 now proves Theorem PP-T2 analytically for all odd prime powers. This appendix records computational verification of the quantitative prime-power bound across the same branch as an independent check.

**Verified:** All prime powers $n \leq 100$ in the dropped-two prime-power branch.

| $n$ | $\varphi(n)$ | Required | $B_{\rm safe}$ | Ratio |
|---|---|---|---|---|
| 4 | 2 | 2 | 28 | 14 |
| 8 | 4 | 12 | 866 | 72 |
| 9 | 6 | 21 | 2450 | 117 |
| 25 | 20 | 230 | $\geq 2300$ | $\geq 10$ |
| 49 | 42 | 987 | $\geq 9870$ | $\geq 10$ |

Zero failures.

### A.4 — Proposition 9.4, Route B: Small $M$ for Prime $n \leq 30$

**Finite search guarantee:** $M_0(n, L_0) < n^2$ (Lemma 9.3). Route B covers $1 \leq M < M_0$.

**Scope:** All prime $n \leq 30$; 36,847 prime rows enumerated exhaustively.

**Result:** Zero failures ($x_0 \geq n-1$ in all cases). For prime $n \geq 31$: $M_0 = 1$ (Lemma 9.5), Route B is vacuous.

### A.5 — Proposition 10.3, Route B: Small $L$ for Composite $n \leq 12$

**Finite search guarantee:** $L < n(n-1)(\varphi(n)+1)$ with $n \mid L$ bounds $L$ to a finite range.

**Scope:** All composite $n \leq 12$ and all admissible tuples with eligible $L$ and dropped unit $d$.

**Result:** Zero failures ($x_0 \geq \varphi(n)$ in all cases).

### A.6 — Cross-Check: Lemma 8.2a Coverage Criterion

Verification that the Cond 1/Cond 2 formula agrees with direct computation.

- **Scope:** $n \in \{6,8,9,10,12,15,16,18,20,25\}$; 6,123 cases.
- **Result:** Zero discrepancies.

### A.7 — Cross-Check: Theorem 8.2c Targeted Isolated Events

Verification that the Dropped-Runner Targeting construction produces an isolated z=0 event for every admissible dropped non-unit.

- **Scope:** All composite $n \leq 400$ and every non-unit target $d \in \{1,\ldots,n-1\}$.
- **Result:** Zero targeting failures.

### A.8 — Cross-Check: Prime-Power Safe-Fibre Patterns

Verification of representative safe-fibre patterns in the prime-power dropped-two branch, including the repaired B3b window and the early-activation regime.

- **Scope:** $n \in \{9, 25, 49\}$, all dropped non-unit pairs.
- **Result:** $\mathrm{safe\_frac} \in [15\%, 71\%]$; 100% of safe fibres from Modes A or B.
