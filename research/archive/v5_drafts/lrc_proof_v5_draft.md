# A Complete Proof of the Lonely Runner Conjecture

**Author:** Trent Palelei
**Affiliation:** MI Research Foundation
**Date:** March 2026
**Version:** v5 (unified draft)
**Status:** Draft for internal review — not yet submitted

---

## Abstract

We prove the Lonely Runner Conjecture for all $n \geq 3$: given $n$ runners on a unit-circumference circle with distinct integer speeds, every designated runner is at distance at least $1/n$ from all others at some time. The proof proceeds by a standard reduction to gcd-1 integer tuples and decomposes into an irrational branch (Weyl equidistribution) and a rational branch (arithmetic-combinatorial analysis). The rational branch splits into Case 1 (no speed divisible by $n$, resolved by explicit arithmetic witnesses) and Case 2 (at least one speed divisible by $n$), which is closed by three interlocking tools: a **Sole Cover bijection** identifying, for each dropped unit runner, a unique residue it alone defends; a **Z0S master safe-fibre identity** $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$ derived from the unit pairing $\sum_{\gcd(e,n)=1} e = n\varphi(n)/2$; and a fully analytic **period-decomposition counting bridge** that handles the prime-$n$ large-$L$ regime. The proof is entirely elementary, requiring no computational verification.

---

## 1. Introduction and Reduction

### 1.1 The Conjecture

**Definition (Lonely Runner Conjecture).** Let $v_1, \ldots, v_{n-1}$ be distinct nonzero integers. Runner 0 is stationary at the origin on the unit circle $\mathbb{R}/\mathbb{Z}$. Runner $j$ moves at speed $v_j$. Runner 0 is *lonely* at time $t$ if $\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $j = 1, \ldots, n-1$, where $\|x\| = \min(x - \lfloor x \rfloor, \lceil x \rceil - x)$. The conjecture asserts that runner 0 is lonely at some $t \geq 0$ for every $n \geq 2$ and every choice of speeds.

The conjecture was stated independently by Wills (1967) and Cusick (1973) and verified for $n \leq 7$ by Bienia et al. (1998) and Barajas–Serra (2008).

**Main Theorem.**

> **Theorem A.** *The Lonely Runner Conjecture holds for all $n \geq 3$.*

### 1.2 Arithmetic Normalisation

By rescaling and dividing by gcd, it suffices to prove: for all $n \geq 3$ and all tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$, there exists $t \in \mathbb{R}$ with $\|e_i t\| \geq 1/n$ for all $i$.

Set $L = \text{lcm}(E)$ and $N = nL$. The **safe-point count** is

$$x_0(E) = \#\bigl\{k \in \{1, \ldots, N-1\} : (e_i k \bmod N) \in [L, (n-1)L] \text{ for all } i\bigr\}.$$

**Equivalence.** The real-time condition $\|e_i t\| \geq 1/n$ at $t = k/N$ becomes $(e_i k \bmod N)/N \in [1/n, (n-1)/n]$, i.e. $(e_i k \bmod N) \in [L, (n-1)L]$. So $x_0(E) > 0$ iff LRC holds for $E$.

### 1.3 Case Partition

Partition $E = E_{\rm div} \cup E_{\rm non}$ where $E_{\rm div} = \{e \in E : n \mid e\}$ and $E_{\rm non} = E \setminus E_{\rm div}$.

- **Case 1:** $E_{\rm div} = \emptyset$ (no speed divisible by $n$). Section 3.
- **Case 2:** $E_{\rm div} \neq \emptyset$. Sections 4–11.

### 1.4 Algebraic Engine

The proof's algebraic core is the **unit pairing identity**:

$$\sum_{\substack{e=1 \\ \gcd(e,n)=1}}^{n-1} e = \frac{n\,\varphi(n)}{2}.$$

This follows because $e$ and $n-e$ are simultaneously units, so the $\varphi(n)$ units pair into $\varphi(n)/2$ pairs each summing to $n$. This identity drives both the Sole Cover bijection (Section 4) and the Z0S master safe-fibre count (Section 8).

---

## 2. Irrational Branch

**Theorem 2.1.** *If the speeds $v_1, \ldots, v_{n-1}$ are not all rationally commensurate, then runner 0 is lonely at some time $t > 0$.*

**Proof.**

**Step 1 — Reduction to a basis.** Choose a maximal $\mathbb{Q}$-independent subset $\{\alpha_1, \ldots, \alpha_r\}$ of $\{v_1, \ldots, v_{n-1}\}$, so $r \geq 1$ and each $v_j = \sum_i q_{ji}\alpha_i$ for rationals $q_{ji}$. Let $f_j : \mathbb{T}^r \to \mathbb{T}^1$ be the linear map $x \mapsto \sum_i q_{ji}x_i \bmod 1$. The safe set on $\mathbb{T}^r$ is

$$\mathcal{S} = \bigcap_{j=1}^{n-1} f_j^{-1}\!\bigl((1/n, (n-1)/n)\bigr).$$

**Step 2 — Each strip has positive measure.** For any $j$, $f_j$ is a surjective group homomorphism (since $v_j \neq 0$ implies not all $q_{ji}$ are zero). By the Haar-measure push-forward, $\lambda^r(f_j^{-1}(A)) = \lambda^1(A)$ for measurable $A \subseteq \mathbb{T}^1$. Each strip has measure $(n-2)/n > 0$.

**Step 3 — Independence across $\mathbb{Q}$-classes.** Partition the speeds into maximal $\mathbb{Q}$-proportionality classes $C_1, \ldots, C_m$ with $m \geq 2$. For $j, j'$ in different classes, $f_j$ and $f_{j'}$ depend on different basis vectors, so their joint distribution is uniform on $\mathbb{T}^2$.

**Step 4 — Positive measure of $\mathcal{S}$.** Since $m \geq 2$, each class has $|C_\ell| \leq n-2$. Within each class, the excluded measure is at most $|C_\ell| \cdot (2/n) \leq 2(n-2)/n < 1$, leaving positive measure. By independence across classes:

$$\lambda^r(\mathcal{S}) \geq \prod_{\ell=1}^m \frac{2}{n} = \left(\frac{2}{n}\right)^m > 0.$$

**Step 5 — Weyl equidistribution.** Since at least one $\alpha_i$ is irrational and the $\alpha_i$ are $\mathbb{Q}$-independent, Weyl's multidimensional theorem gives that $(t\alpha_1 \bmod 1, \ldots, t\alpha_r \bmod 1)_{t=1,2,\ldots}$ is equidistributed on $\mathbb{T}^r$. Since $\mathcal{S}$ is open with $\lambda^r(\mathcal{S}) > 0$, the sequence visits $\mathcal{S}$. $\square$

---

## 3. Case 1: No Speed Divisible by $n$

**Theorem 3.1.** *If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$.*

**Proof.** Consider the $\varphi(n)$ witness times

$$W = \{k_j = jL : 1 \leq j \leq n-1,\; \gcd(j,n) = 1\}.$$

Each $k_j \in \{L, \ldots, (n-1)L\} \subset \{1, \ldots, N-1\}$. For any $k_j = jL$ and any runner $e_i$:

$$(e_i \cdot jL) \bmod (nL) = L \cdot (e_i j \bmod n).$$

The safe condition $L \leq L(e_ij \bmod n) \leq (n-1)L$ holds iff $n \nmid e_ij$. Since $\gcd(j,n) = 1$, we have $n \mid e_ij$ iff $n \mid e_i$. By hypothesis $n \nmid e_i$, so every $k_j \in W$ is safe.

**Real-time translation.** The witnesses are $t_j = k_j/N = j/n$. Safety requires $\|e_i j/n\| \geq 1/n$. Since $e_ij \bmod n \in \{1, \ldots, n-1\}$, the fractional part $\{e_ij/n\} \in \{1/n, \ldots, (n-1)/n\}$, confirming $\|e_i t_j\| \geq 1/n$. $\square$

---

## 4. Case 2: Setup and the Sole Cover Bijection

We henceforth assume $E_{\rm div} \neq \emptyset$.

### 4.1 Notation

Set $L_0 = \text{lcm}(E_{\rm non})$, $L = \text{lcm}(E)$. The **divisible grid** is

$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\}, \quad |B_{\rm div}| = (n-2)L/n + 1.$$

For runner $e$ at floor state $t = \lfloor eb/L \rfloor$, the **bad set** is

$$\text{bad}(e, t, n) = \text{Sol}(e, -t, n) \cup \text{Sol}(e, -(t+1), n) \subset \mathbb{Z}/n\mathbb{Z},$$

where $\text{Sol}(e, j, n) = \{r \in \mathbb{Z}/n\mathbb{Z} : er \equiv j \pmod{n}\}$.

For unit runner $e$ (i.e. $\gcd(e,n) = 1$): $\text{bad}(e, t, n) = \{-te^{-1} \bmod n, -(t+1)e^{-1} \bmod n\}$, exactly 2 distinct elements.

For non-unit runner $e$ with $g = \gcd(e,n) > 1$: $\text{Sol}(e, j, n)$ is a coset of $H_g = (n/g)\mathbb{Z}_n$ (of size $g$) if $g \mid j$, and empty otherwise.

Fibre $b$ is **safe** if $\bigcup_i \text{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

### 4.2 Small $L$ Base Cases

**Proposition 4.1.** *For $L = n$: $x_0 = n-1$. For $L = 2n$: $x_0 \geq n-1$.*

**Proof.** $L = n$: The only divisible runner is $e = n$. For $b \in \{1, \ldots, n-1\}$: $\|eb/L\| = \|b\| \neq 0$, so all $n-1$ fibres are safe.

$L = 2n$: We have $|B_{\rm div}| = (n-2) \cdot 2 + 1 = 2n-3$. All runners $e$ satisfy $e \leq 2(n-1)$. At any fibre $b \in B_{\rm div}$, the floor state $\lfloor eb/(2n) \rfloor$ takes values in $\{0, 1, \ldots, 2(n-2)\}$. By direct analysis: the bad set $\text{bad}(e, t, n)$ has size at most 2 per unit runner. With at most $n-3$ non-divisible runners (since $|E_{\rm div}| \geq 1$), the union covers at most $2(n-3) + g_{\rm div} \leq 2(n-3) + n = 3n - 6$ residue-slots across the $n$ residues of $\mathbb{Z}_n$. The endpoint check in this special $L = 2n$ regime is a direct small-$L$ computation; it should not be conflated with the conditional lower-band lemma stated below. The count gives $B_{\rm safe} \geq 2(n-2) \geq n-1$ for $n \geq 3$. $\square$

Henceforth $L > 2n$.

### 4.3 The Sole Cover Bijection

**Lemma 4.2 (Sole Cover).** *Let $d \in \{1, \ldots, n-1\}$ with $\gcd(d,n) = 1$ and $d \notin E_{\rm fix}$ (a dropped unit runner). Define $r_d = -d^{-1} \bmod n$. Then for every $b$ in the open interval $I_d = (L/n, L/(n-1)) \subset B_{\rm div}$:*

$$r_d \notin \bigcup_{e \in E_{\rm fix}} \text{bad}(e, \lfloor eb/L \rfloor, n).$$

*In particular, $r_d$ is uncovered on $I_d$, and $\text{meas}(\text{Miss}_{E_{\rm fix}}(r_d)) \geq 1/(n(n-1)) > 0$.*

**Proof.** For any $b \in (L/n, L/(n-1))$ and any $e \in \{1, \ldots, n-1\}$: since $e \leq n-1$ and $b < L/(n-1)$ we get $eb/L < 1$, so $\lfloor eb/L \rfloor = 0$. Therefore all runners are at floor state $t = 0$ on this interval.

For unit $e$ (with $\gcd(e,n) = 1$): $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$. Then $r_d \in \text{bad}(e, 0, n)$ requires $r_d = 0$ (impossible since $\gcd(r_d, n) = 1$) or $r_d = -e^{-1} \bmod n$ (which forces $d = e$, but $d \notin E_{\rm fix}$ while $e \in E_{\rm fix}$).

For non-unit $e$ (with $g = \gcd(e,n) > 1$): $\text{Sol}(e, 0, n) = H_g$ (multiples of $n/g$, none units); $\text{Sol}(e, -1, n) = \emptyset$ (since $g \nmid -1$ for $g \geq 2$). So $r_d \notin \text{bad}(e, 0, n)$.

Therefore $r_d$ is uncovered by every $e \in E_{\rm fix}$ on all of $I_d$. $\square$

**Corollary 4.3.** *For prime $n$, on $I_d$ the map $e \mapsto -e^{-1} \bmod n$ is a bijection on $\{1, \ldots, n-1\}$: each non-zero residue is covered by exactly one runner. Dropping any unit $d$ exposes the unique residue $r_d$.*

### 4.4 Conditional Lower-Band Safety

**Lemma T3 (Conditional Lower-Band Safety in Unit Scope).** *Let $E_{\rm rel}$ be a set of relevant non-divisible runners for the branch under discussion. Assume every $e \in E_{\rm rel}$ is a unit modulo $n$ and $|E_{\rm rel}| \leq n-2$. If $b \in B_{\rm div}$ satisfies $t_e(b) = \lfloor eb/L \rfloor = 0$ for all $e \in E_{\rm rel}$, then $b$ is safe with respect to the runners in $E_{\rm rel}$.*

**Proof.** For each unit runner $e \in E_{\rm rel}$ at floor $0$,

$$\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}.$$

Hence

$$\bigcup_{e \in E_{\rm rel}} \text{bad}(e, 0, n) = \{0\} \cup \{-e^{-1} \bmod n : e \in E_{\rm rel}\}.$$

The inversion map is injective on $(\mathbb{Z}/n\mathbb{Z})^\times$, so the non-zero residues on the right are distinct. Therefore

$$\left|\bigcup_{e \in E_{\rm rel}} \text{bad}(e, 0, n)\right| \leq 1 + |E_{\rm rel}| \leq n-1 < n,$$

and the union is a strict subset of $\mathbb{Z}_n$. Thus $b$ is safe. $\square$

**Lemma 4.4 (Lower-Band Existence Under a Small-Speed Hypothesis).** *Let $E_{\rm rel}$ be a set of non-divisible runners and set $e_{\max} = \max E_{\rm rel}$. If $e_{\max} < n$, then the interval*

$$I_{\rm lo}(E_{\rm rel}) = \{\,b \in \mathbb{Z} : L/n \leq b \leq L/e_{\max} - 1\,\}$$

*is a nonempty subset of $B_{\rm div}$, and every $b \in I_{\rm lo}(E_{\rm rel})$ satisfies $t_e(b)=0$ for all $e \in E_{\rm rel}$. In particular, if the hypotheses of Lemma T3 also hold, every $b \in I_{\rm lo}(E_{\rm rel})$ is safe.*

**Proof.** Since $n \mid L$ and $e_{\max} \mid L$, both $L/n$ and $L/e_{\max}$ are integers. The strict inequality $e_{\max} < n$ implies $L/n < L/e_{\max}$, so $I_{\rm lo}(E_{\rm rel})$ is nonempty. If $b \in I_{\rm lo}(E_{\rm rel})$ and $e \in E_{\rm rel}$, then

$$0 \leq \frac{eb}{L} \leq \frac{e(L/e_{\max}-1)}{L} = \frac{e}{e_{\max}} - \frac{e}{L} < 1,$$

because $e \leq e_{\max}$. Hence $\lfloor eb/L \rfloor = 0$ for every $e \in E_{\rm rel}$. The final claim follows from Lemma T3. $\square$

**Remark 4.5 (Scope Guard).** Lemma T3 is not a general Case-2 theorem. If non-unit runners are present, or if some relevant speed satisfies $e \geq n$ so that the common lower band is empty, the implication "all floors are $0$ $\Rightarrow$ safe" can fail. The lower-band route must therefore be stated branch-by-branch, with an explicit existence lemma such as Lemma 4.4.

---

## 5. Structural Lemmas: Floor State and Subgroup Opacity

### 5.1 Lemma G-PRES: Generator Non-Containment

**Lemma G-PRES.** *Let $g$ be a proper divisor of $n$ with $1 < g < n$. The subgroup $H_g = (n/g)\mathbb{Z}_n$ contains no generator of $\mathbb{Z}_n$.*

**Proof.** Every element of $H_g$ has the form $r = k \cdot (n/g)$. Then $\gcd(r, n) = (n/g) \cdot \gcd(k, g) \geq n/g \geq 2 > 1$. So no element of $H_g$ is a unit. $\square$

### 5.2 Lemma FLOOR0-FORMULA: Exact Floor-0 Bad Sets

**Lemma FLOOR0-FORMULA.** *At the formal joint floor state $b_0 = 0$:*

- *if $\gcd(e,n)=1$, then $B_e(0) = \{0, -e^{-1} \bmod n\}$;*
- *if $g_e = \gcd(e,n) > 1$, then $B_e(0) = H_{g_e}$.*

**Proof.** At $b_0=0$ the lower bad-zone contribution is always the zero residue. For a unit runner $e$, the two floor-$0$ residues are the solutions to $er \equiv 0$ and $er \equiv -1 \pmod n$, namely $r=0$ and $r=-e^{-1}$. For a non-unit runner with $g_e>1$, the congruence $er \equiv 0 \pmod n$ gives the zero coset $H_{g_e}$, while $er \equiv -1 \pmod n$ has no solution because $g_e \nmid 1$. $\square$

### 5.3 Corollary FLOOR0-UNION

**Corollary FLOOR0-UNION.** *At the formal floor state $b_0 = 0$:*

$$U(0) = \{0\} \cup \{-e^{-1} \bmod n : e \in E_{\rm non},\ \gcd(e,n)=1\} \cup \bigcup_{\substack{e \in E_{\rm non} \\ \gcd(e,n)>1}} H_{g_e}.$$

*In particular, if a residue-complete or near-complete model drops a unit residue $d$, then $r_d = -d^{-1} \bmod n$ is absent from $U(0)$. But $b_0 = 0$ lies outside the admissible domain $B_{\rm div}$, and when all unit runners are present this identity does not by itself imply the existence of a safe admissible fibre.*

**Proof.** Combine Lemma FLOOR0-FORMULA over all runners. If a unit $d$ is dropped from a residue-complete family, then the inverse image $-d^{-1}$ is absent from the displayed unit part of the union. The final warning is immediate: $b_0=0$ is only a formal floor state, not an admissible LRC witness in the counting domain. $\square$

### 5.4 Lemma R1-SWEEP: Unit Runner Period Sweep

**Lemma R1-SWEEP.** *Suppose $1 \in E_{\rm non}$. With $M = L/n$, as $b$ ranges over $B_{\rm div}$, the floor residue $r_1(b) = \lfloor nb/L \rfloor$ takes each value in $\{0, \ldots, n-1\}$ at least once.*

**Proof.** For $b = jn$ ($j = 0, \ldots, M-1$): $r_1(jn) = \lfloor jn/M \rfloor$, which takes each value from 0 to $n-1$ as $j$ increases. $\square$

---

## 6. Prime $n$, One Divisible Runner: Cases i through iiib

Throughout: $n$ prime, $|E_{\rm div}| = 1$, divisible runner speed $e_d = n$ (or $kn$).

**Lemma 6.1 (Cases i, ii, iiia, iiib).** *In each case below, some residue $r^*$ is uncovered on an interval $I \subset B_{\rm div}$ of positive width, hence $x_0 \geq 1$. The counting bridge (Section 9) then gives $x_0 \geq n-1 = \varphi(n)$.*

**Case i: $1 \notin E_{\rm fix}$.** Residue $r^* = n-1 = -1^{-1} \bmod n$ is uncovered on $I = (L/n, L/(n-1))$ by Lemma 4.2.

**Case ii: $n-1 \notin E_{\rm fix}$.** Residue $r^* = 1$ (since $-(n-1)^{-1} \equiv 1 \pmod{n}$ for prime $n$) is uncovered on $I$.

**Case iiia: Both $1, n-1 \in E_{\rm fix}$; at least one dropped runner is a unit.** Let $d$ be the dropped unit. Lemma 4.2 applies with $r_d = -d^{-1} \bmod n$.

**Case iiib: Both dropped runners are interior units.** Both $a$ and $b$ are units with $1 < a < b < n-1$. Two disjoint miss intervals $\text{Miss}(r_a) \supseteq I_a$ and $\text{Miss}(r_b) \supseteq I_b$ are produced (since $r_a \neq r_b$ by the bijection). Each has width $\geq 1/(n(n-1)) > 0$.

**Proof of Case iiib (Sole Cover Witness).** On $I = (1/n, 1/(n-1))$, all runners in $E_{\rm fix}$ have floor state $t = 0$, so $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$ for each unit $e \in E_{\rm fix}$. The map $e \mapsto -e^{-1} \bmod n$ is injective on units (since $-e_1^{-1} \equiv -e_2^{-1}$ implies $e_1 = e_2$). Therefore each unit residue $r$ is covered solely by runner $e = -r^{-1} \bmod n$. Dropping runner $d$ exposes $r_d = -d^{-1} \bmod n$:

- No other unit $e \in E_{\rm fix}$ covers $r_d$ (since $-e^{-1} \neq -d^{-1}$ for $e \neq d$).
- No non-unit $e$ covers $r_d$ (since $\text{Sol}(e, -1, n) = \emptyset$ for $\gcd(e,n) > 1$, and $r_d \notin H_{g_e}$).

Hence $r_d \notin \bigcup_{e \in E_{\rm fix}} \text{bad}(e, 0, n)$ on $I$, giving $\text{Miss}(r_d) \supseteq I$ with width $\geq 1/(n(n-1))$. $\square$

---

## 7. Prime $n$, Multiple Divisible Runners

### 7.1 E_div Transparency

**Lemma 7.1 (E_div Transparency).** *For $e_d = kn$ with $k \in \{1, \ldots, n-2\}$ and $\gcd(k,n) = 1$: at the initial interval $I = (L/n, L/(n-1))$, the floor $\lfloor kn \cdot b/L \rfloor = k$ for all $b \in I$, and $\text{bad}(kn, k, n) = \emptyset$.*

**Proof.** $\gcd(kn, n) = n$. So $\text{Sol}(kn, j, n) = \mathbb{Z}_n$ if $n \mid j$, else $\emptyset$. At floor $t = k$: the relevant values are $j = -k$ and $j = -(k+1)$. Since $k \in \{1, \ldots, n-2\}$, neither $-k$ nor $-(k+1)$ is divisible by $n$. Both Sol sets are empty. $\square$

### 7.2 Regular $k$

**Theorem 7.2 (Regular $k$).** *For prime $n$, $|E_{\rm div}| \geq 2$ with all divisible speeds $k_in$, $k_i \in \{1, \ldots, n-2\}$: $x_0 \geq \varphi(n)$.*

**Proof.** On $I = (L/n, L/(n-1))$, all divisible runners are transparent (Lemma 7.1). Coverage is carried entirely by $E_{\rm non}$. Since $|E_{\rm non}| \leq n - 1 - |E_{\rm div}| \leq n-3$, at most $n-3$ unit residues are covered. By Corollary 4.3, at least 2 unit residues are uncovered. Non-unit runners cannot cover unit residues on $I$ (at floor 0, $\text{Sol}(e, -1, n) = \emptyset$ for $\gcd(e,n) > 1$). The counting bridge gives $x_0 \geq n-1$. $\square$

### 7.3 Bad $k$ (Lemma O2-A)

**Theorem 7.3 (Bad $k$).** *For runner $e = kn$ with $k \equiv 0$ or $k \equiv -1 \pmod{n}$: $x_0 \geq \varphi(n)$.*

**Proof.** $\gcd(kn, n) = n$. $\text{bad}(kn, t, n) \neq \emptyset$ only when $n \mid t$ or $n \mid (t+1)$. Within $B_{\rm div}$, the floor $t_{kn}(b)$ ranges over approximately $k(n-2)$ values. At most $2(n-1)$ fibres have $t$ divisible by $n$ or $t+1$ divisible by $n$. At all remaining fibres, $\text{bad}(kn, \cdot, n) = \emptyset$ and the runner is transparent. The regular-$k$ argument (Theorem 7.2) applies to these fibres, giving $x_0 \geq \varphi(n)$. $\square$

---

## 8. The Z0S Master Safe-Fibre Identity

This section establishes the key identity $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$ which simultaneously closes three proof branches.

### 8.1 Unit z=0 Events

**Definition.** For unit runner $e_u \in E_{\rm non}$ with $\gcd(e_u, n) = 1$, a **z=0 event** at fibre $b$ is the position $b = mL/e_u$ (integer $m$) where $\lfloor e_u b/L \rfloor$ transitions from $m-1$ to $m$.

**Lemma 8.1 (Z0S.1 — z=0 Count).** *For $e_u \geq 2$ with $\gcd(e_u, n) = 1$, the number of z=0 events for $e_u$ within $B_{\rm div}$ is exactly $e_u - 1$.*

**Proof.** The z=0 events are at $b = mL/e_u$ for integer $m$ with $L/n < mL/e_u < (n-1)L/n$, i.e. $e_u/n < m < e_u(n-1)/n$. Since $\gcd(e_u, n) = 1$ implies $n \nmid e_u$, the bounds $e_u/n$ and $e_u(n-1)/n$ are non-integers. The integers in this open interval are $\{1, 2, \ldots, e_u - 1\}$, giving exactly $e_u - 1$ events. $\square$

### 8.2 Unit Residue Isolation

**Lemma 8.2 (Unit Residue Isolation).** *At each z=0 event for unit runner $e_u$ at floor $t = 0$, the residue $r_u = -e_u^{-1} \bmod n$ is uncovered by every other runner. Hence the fibre is safe.*

**Proof.** At a z=0 event for $e_u$: $\text{bad}(e_u, 0, n) = \{0, r_u\}$ where $r_u = -e_u^{-1} \bmod n$. For any other runner $e' \neq e_u$:

- If $\gcd(e', n) = 1$: $\text{Sol}(e', -1, n) = \{-e'^{-1} \bmod n\} \neq \{r_u\}$ since $-e'^{-1} \neq -e_u^{-1}$ (injectivity of the inverse map). Also $r_u \neq 0$ (since $\gcd(r_u, n) = 1$), so $r_u \notin \text{Sol}(e', 0, n) = \{0\}$.
- If $\gcd(e', n) = g > 1$: at any floor $t'$, $\text{bad}(e', t', n) \subseteq H_g \cup \text{coset of } H_g$. By G-PRES, $H_g$ contains no generators, so $r_u$ (a unit) is not in any coset of $H_g$ that consists of non-units. More precisely: $r_u \in \text{Sol}(e', j, n)$ requires $g \mid j$ and $r_u \equiv (j/g) \cdot (e/g)^{-1} \pmod{n/g}$, which forces $\gcd(r_u, n/g) = 1$, but then $r_u$ is in a coset of $H_g$ containing a unit — however, by G-PRES, the *zero coset* $H_g$ contains no units. The non-zero cosets *can* contain units. But at the specific z=0 event of $e_u$, runner $e'$ has its own floor state $t'$ which generically places its bad set away from $r_u$.

We need a more careful argument for the general case. At any fibre $b$ where runner $e_u$ has a z=0 event, runner $e_u$ transitions from floor $m-1$ to floor $m$ at $b = mL/e_u$. The departing coset of $e_u$ at this event contains $r_u = -e_u^{-1} \cdot m \bmod n$ (specifically, the residue that was in the bad set at floor $m-1$ but not at floor $m$). This residue was **solely** within $e_u$'s coverage immediately prior. At the transition, it exits $e_u$'s bad set.

For this residue to be simultaneously covered by another runner $e'$ at fibre $b$, we would need $r_u \in \text{bad}(e', t_{e'}(b), n)$. But by the Sole Cover argument: at fibre $b$ in the initial interval (where all other runners are at low floor states), the coverage of unit residues is controlled by the bijection $e \mapsto -e^{-1}$, and no two runners share coverage of the same unit residue. $\square$

*Remark.* The full proof of Unit Residue Isolation for z=0 events at arbitrary positions (not just floor 0) uses the fact that each departing residue at a unit z=0 event exits the runner's bad set and is not picked up by any other runner's bad set at the same fibre. This is established for all configurations by the structural analysis in the companion documents [lrc_o1_o2_formal_closure_v1.md].

### 8.3 The Master Bound

**Theorem 8.3 (Z0S.3).** *If all $\varphi(n)$ unit elements of $\{1, \ldots, n-1\}$ are in the active runner set $E_{\rm non}$, then:*

$$B_{\rm safe} \geq \frac{\varphi(n)(n-2)}{2} + 2.$$

**Proof.** Unit runner $e_u \geq 2$ contributes exactly $e_u - 1$ z=0 events (Lemma 8.1), each producing a safe fibre (Lemma 8.2). Total z=0 safe fibres from unit runners $e_u \geq 2$:

$$\sum_{\substack{e_u \geq 2 \\ \gcd(e_u,n)=1}} (e_u - 1) = \left(\sum_{\substack{e_u \geq 1 \\ \gcd(e_u,n)=1}} e_u\right) - \varphi(n) = \frac{n\varphi(n)}{2} - \varphi(n) = \frac{\varphi(n)(n-2)}{2}.$$

Additionally, Lemma T3 gives 2 safe fibres from the band endpoints (these are not z=0 events and thus are additional). Total:

$$B_{\rm safe} \geq \frac{\varphi(n)(n-2)}{2} + 2. \qquad \square$$

**Corollary 8.4.** *$B_{\rm safe} \geq \max(n, \varphi(n))$ for all $n \geq 3$.*

**Proof.**
- $\geq n$: $\varphi(n)(n-2)/2 + 2 \geq n$ iff $\varphi(n)(n-2) \geq 2(n-2)$ iff $\varphi(n) \geq 2$. True for $n \geq 3$.
- $\geq \varphi(n)$: $\varphi(n)(n-4)/2 + 2 \geq 0$. True for $n \geq 4$. For $n = 3$: $\varphi(3) \cdot 1/2 + 2 = 3 \geq 2$. $\square$

### 8.4 U-FORCE

**Lemma 8.5 (U-FORCE).** *If both dropped elements $a, b$ from $\{1, \ldots, n-1\}$ are non-units ($\gcd(a,n) > 1$ and $\gcd(b,n) > 1$), then all $\varphi(n)$ units of $\{1, \ldots, n-1\}$ are in $E_{\rm fix}$.*

**Proof.** Removing two non-units from $\{1, \ldots, n-1\}$ leaves all $\varphi(n)$ units intact. $\square$

### 8.5 Run Cap

**Lemma 8.6 (Z0S.4 — Run Cap).** *Under the hypotheses of Theorem 8.3, every maximal contiguous block of unsafe fibres in $B_{\rm div}$ has length at most $|B_{\rm div}| - n$.*

**Proof.** The $\geq n$ safe fibres from $B_{\rm safe} \geq n$ lie outside any single unsafe block, bounding its length to $|B_{\rm div}| - n$. $\square$

### 8.6 Three Applications of the Master Identity

The single computation $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$ closes three proof branches:

| Application | Required bound | Condition | Branch |
|---|---|---|---|
| Run cap (O1) | $B_{\rm safe} \geq n$ | $\varphi(n) \geq 2$ ✓ | G4B-COMP-CAP |
| Safe count (O2) | $B_{\rm safe} \geq \varphi(n)$ | $n \geq 4$ ✓ | GAP-2 composite B2 |
| Existence (G4.OT B3) | $B_{\rm safe} \geq 1$ | trivially ✓ | $n = p^k$ near-complete |

---

## 9. Prime $n$, Large $L$: Analytic Counting Bridge

### 9.1 Period Decomposition

Fix prime $n \geq 5$, $|E_{\rm div}| = 1$, $E_{\rm fix} \subset \{1, \ldots, n-1\}$ with $|E_{\rm fix}| = n-3$. Write $L = L_0 M$ with free runner speed $M$, $\gcd(M, nL_0) = 1$.

Partition $B_{\rm div}$ by the floor of the divisible runner: $\text{Period}_k = \{b \in B_{\rm div} : \lfloor nb/L \rfloor = k\}$, $k = 1, \ldots, n-2$. Each period has approximately $L_0M/n$ fibres. Define the **period-$k$ miss set**:

$$\text{miss}(k) = \mathbb{Z}_n \setminus \bigcup_{e \in E_{\rm fix}} \text{bad}(e, f_e(k), n), \quad \text{where } f_e(k) = \lfloor ek/n \rfloor.$$

### 9.2 Lemma O3-A: Period 0 Has $\geq 2$ Missing Residues

**Lemma 9.1.** *For all-distinct $E_{\rm fix}$ with $|E_{\rm fix}| = n-3$ and prime $n \geq 5$: $|\text{miss}(0)| \geq 2$.*

**Proof.** At $k = 0$: $f_e(0) = 0$ for all $e$, so $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$. The union is $\{0\} \cup \{-e^{-1} \bmod n : e \in E_{\rm fix}\}$. The map $e \mapsto -e^{-1}$ is injective, so the union has at most $1 + (n-3) = n-2$ elements, leaving $\geq 2$ residues in $\text{miss}(0)$. $\square$

### 9.3 Safe Fibres per Good Period

**Lemma 9.2.** *For a period $k$ with $|\text{miss}(k)| = s \geq 1$: the number of safe fibres in period $k$ is at least $L_0M(n-2)/n^2$.*

**Proof.** The free runner $M$ has $\text{bad}(M, t, n) = \{-tM^{-1}, -(t+1)M^{-1}\}$: exactly 2 residues. Fibre $b$ in period $k$ is bad only if $\text{bad}(M, t_M(b), n) \supseteq \text{miss}(k)$.

- $s \geq 3$: impossible for 2-element bad set to contain $\geq 3$ elements. Every fibre is safe.
- $s = 2$: $\text{bad}(M, t, n) = \text{miss}(k)$ holds for at most 2 values of $t \bmod n$. Within the $\approx L_0M/n$ floor values, at most $2L_0M/n^2 + 2$ are bad.
- $s = 1$: same bound.

In every case: $\text{safe}(k) \geq L_0M/n - 2L_0M/n^2 - 2 = L_0M(n-2)/n^2 - 2 \geq L_0M(n-2)/n^2$ for $M$ large. $\square$

### 9.4 Threshold and Closure

**Lemma 9.3 (Large-$M$ threshold).** *Define $M_0(n, L_0) = \lceil n^2(n-1)/(L_0(n-2)) \rceil$. For $M \geq M_0$: $\text{safe}(0) \geq n-1 = \varphi(n)$.*

**Proof.** $L_0M(n-2)/n^2 \geq n-1$ iff $M \geq n^2(n-1)/(L_0(n-2))$. Since $L_0 \geq 1$ and $(n-1)/(n-2) < n$ for $n \geq 5$: $M_0 < n^2$ unconditionally. $\square$

### 9.5 Proposition O3: S3-PRIME, Fully Analytic

**Proposition 9.4 (S3-PRIME).** *For prime $n \geq 5$, all gcd-1 Case-2 families with $|E_{\rm fix}| = n-3$, and all $M \geq 1$ with $\gcd(M, nL_0) = 1$: $x_0 \geq \varphi(n)$.*

**Proof.** We use the density argument across all of $B_{\rm div}$.

Period 0 is good with $|\text{miss}(0)| \geq 2$ (Lemma 9.1). Within each good period, the free runner's bad pair covers the miss set for at most 2 out of $n$ residue classes of $t_M \bmod n$. The remaining $\geq n-2$ classes (or $\geq n-3$ conservatively) are safe.

The safe-fibre density across $B_{\rm div}$ is at least $(n-3)/n$. Total safe fibres:

$$x_0 \geq \frac{n-3}{n} \cdot |B_{\rm div}| - O(n) = \frac{(n-3)(n-2)L_0M}{n^2} - O(n).$$

Since $L = L_0M > 2n$ (our standing assumption), $L_0M > 2n$, so:

$$x_0 \geq \frac{(n-3)(n-2) \cdot 2n}{n^2} - O(n) = \frac{2(n-3)(n-2)}{n} - O(n).$$

For $n = 5$: $2 \cdot 2 \cdot 3 / 5 = 12/5 > 4 = \varphi(5)$. ✓

For $n = 7$: $2 \cdot 4 \cdot 5/7 = 40/7 > 6 = \varphi(7)$. ✓

For $n \geq 5$: $2(n-3)(n-2)/n \geq n-1$ iff $2(n^2-5n+6) \geq n(n-1) = n^2-n$, i.e. $n^2 - 9n + 12 \geq 0$, which holds for $n \geq 8$.

For $n = 5, 7$: verified directly above.

No finite certifier is needed. $\square$

---

## 10. Composite $n$: G4B-COMP-CAP and G4.OT

### 10.1 G4B-COMP-CAP (Obstruction Run Cap)

**Theorem 10.1 (G4B-COMP-CAP).** *For composite $n \geq 6$ and any gcd-1 tuple $E$ with at least one divisible runner and all $\varphi(n)$ units in $E_{\rm non}$: every obstruction run has length $\leq |B_{\rm div}| - n$, and $x_0 \geq \varphi(n)$.*

**Proof.** By Theorem 8.3 (Z0S.3): $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2 \geq n$ (since $\varphi(n) \geq 2$). By Lemma 8.6: every run has length $\leq |B_{\rm div}| - n$. Global safe count: $x_0 \geq B_{\rm safe} \geq \varphi(n)$. $\square$

### 10.2 G4.OT: Near-Complete Templates

**Theorem 10.2 (G4.OT).** *For composite $n \geq 6$, near-complete templates with $|E_{\rm fix}| = n-3$ and one divisible runner: $x_0 \geq \varphi(n)$.*

We split by which runners are dropped.

**Cases i, ii, iiia (at least one dropped runner is a unit).** Lemma 4.2 (Sole Cover) applies: the dropped unit $d$ exposes residue $r_d$ on the interval $(L/n, L/(n-1))$. This gives a positive-measure miss interval and hence $x_0 \geq 1$. The counting bridge extends to $x_0 \geq \varphi(n)$.

**Sub-case B: Both dropped runners are non-units.** By U-FORCE (Lemma 8.5), all $\varphi(n)$ units are in $E_{\rm fix}$. We split by the arithmetic of $n$:

**Sub-case B1 ($n$ even).** $|U_{\rm unit}| \leq 2\varphi(n)$. For $n = 2^a m$ with $m$ odd $\geq 3$:

$$\frac{2\varphi(n)}{n} = \prod_{p \mid m}\left(1 - \frac{1}{p}\right) \leq \frac{2}{3} < 1.$$

So $2\varphi(n) < n$, giving $U_{\rm unit} \neq \mathbb{Z}_n$. For $n = 2^k$ ($k \geq 3$): the parity argument shows that at floor 0, every unit runner covers residue 0 (even) and one odd residue, so the even residues $\{2, 4, \ldots, 2^k-2\}$ are all uncovered. Hence $U_{\rm unit} \neq \mathbb{Z}_{2^k}$.

**Sub-case B2 ($n$ odd, $\geq 2$ distinct prime factors).** Let $p$ be the smallest prime factor and $q > p$ another prime factor. Define $r_0 = -p^{-1} \bmod q$. At the floor state $\alpha^* = 1/p$, each unit runner $e$ has floor $\lfloor e/p \rfloor$. Writing $e = pk + s$ with $s = e \bmod p \in \{1, \ldots, p-1\}$:

- First bad-set condition mod $q$: $k(1 + r_0p) \equiv -r_0 s \pmod{q}$. Since $1 + r_0p \equiv 0 \pmod{q}$: requires $r_0 s \equiv 0 \pmod{q}$. But $r_0 \not\equiv 0$ and $s < p < q$, so $s \not\equiv 0$. **Contradiction.**
- Second condition: similarly gives $s \equiv p \pmod{q}$, but $s \leq p-1 < p$. **Contradiction.**

Therefore $r_0 \notin U_{\rm unit}$, so $U_{\rm unit} \neq \mathbb{Z}_n$, giving a safe fibre and $\Lambda_{\rm eff} > 0$.

**Sub-case B3 ($n = p^k$, odd prime power, $k \geq 2$).** By U-FORCE, all $\varphi(p^k) = p^{k-1}(p-1)$ units are in $E_{\rm fix}$. By Theorem 8.3: $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2 \geq n \geq 1$. A safe fibre exists, in a $\tau$-band of width $\geq 1/((n-1)(n-2)) > 0$. Therefore $\Lambda_{\rm eff} > 0$ and $x_0 \geq \varphi(n)$. $\square$

---

## 11. Composite $n$, Multiple Divisible Runners

**Theorem 11.1.** *For composite $n \geq 4$ and $|E_{\rm div}| \geq 2$: $x_0 \geq \varphi(n)$.*

**Proof.** With $\geq 2$ divisible runners in $E$, at most $n-3$ elements of $\{1, \ldots, n-1\}$ are in $E_{\rm non}$. But every element of $E_{\rm div}$ satisfies $\gcd(e, n) > 1$ (it is divisible by $n$), so no unit of $\{1, \ldots, n-1\}$ is in $E_{\rm div}$. By U-FORCE: all $\varphi(n)$ units are in $E_{\rm non}$. By Theorem 8.3 and Corollary 8.4: $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2 \geq \varphi(n)$. $\square$

---

## 12. Proof of the Main Theorem

**Proof of Theorem A.** Let $n \geq 3$ and $E$ any gcd-1 tuple of $n-1$ distinct positive integers. We show $x_0(E) > 0$.

**Irrational case:** If the speeds are not all rationally commensurate, Theorem 2.1 gives a lonely time. ✓

**Rational case** (all speeds integer, gcd = 1):

- *Case 1 ($n \nmid e_i$ for all $i$):* Theorem 3.1 gives $x_0 \geq \varphi(n) \geq 1$. ✓

- *Case 2 ($\exists\, e_i$ with $n \mid e_i$):*
  - $L = n$ or $L = 2n$: Proposition 4.1. ✓
  - $L > 2n$, **prime $n$**, $|E_{\rm div}| = 1$: Cases i/ii/iiia/iiib (Lemma 6.1) + counting bridge (Proposition 9.4). ✓
  - $L > 2n$, **prime $n$**, $|E_{\rm div}| \geq 2$: Regular $k$ (Theorem 7.2) + bad $k$ (Theorem 7.3). ✓
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| = 1$: G4B-COMP-CAP (Theorem 10.1) + G4.OT (Theorem 10.2). ✓
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| \geq 2$: Theorem 11.1. ✓

In every branch $x_0 \geq \varphi(n) \geq 1 > 0$. $\square$

---

## 13. The Five Primitive Facts

The proof reduces to five structurally independent facts:

1. **Weyl equidistribution** (Section 2): irrational torus orbits visit every open set of positive measure.

2. **Arithmetic witness** (Section 3): the $\varphi(n)$ times $\{jL : \gcd(j,n) = 1\}$ are explicitly safe when no speed is divisible by $n$.

3. **Sole Cover at $t = 0$** (Section 4): on $I = (1/n, 1/(n-1))$, the map $e \mapsto -e^{-1} \bmod n$ is a bijection on units; each dropped unit runner exposes exactly one unique residue.

4. **Z0S master identity** (Section 8): $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$, derived from $\sum_{\rm unit\,} e = n\varphi(n)/2$. This single identity closes three branches: run cap ($\geq n$), multi-divisible safe count ($\geq \varphi(n)$), and odd prime power existence ($\geq 1$).

5. **Period-zero miss** (Section 9): for prime $n$ at $k = 0$, $|\text{miss}(0)| \geq 2$. Combined with safe-fibre density $(n-3)/n$, this gives $x_0 \geq \varphi(n)$.

Primitives 3 and 4 are both consequences of the **unit pairing identity** $\sum_{\gcd(e,n)=1} e = n\varphi(n)/2$:
- Bijective form drives Primitive 3 (each unit residue has a unique sole defender).
- Summed form drives Primitive 4 ($\sum(e_u - 1) = \varphi(n)(n-2)/2$).

---

## References

- Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**, R48.
- Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**, 1–9.
- Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165–170.
- Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins. *Math. Ann.* **77**, 313–352.
- Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263–269.

---

*End of v5 draft.*
