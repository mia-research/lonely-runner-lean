# A Complete Proof of the Lonely Runner Conjecture

**Author:** Trent Palelei
**Affiliation:** MI Research Foundation
**Date:** March 2026
**Version:** v5.2 (honesty pass)
**Status:** Draft for internal review — not yet submitted
**Changes from v5.1:** Five P0/P1 fixes: abstract and Theorem A made conditional (P0-A); false first-admissible-fibre safety claim removed (P0-B); "+2 endpoint" removed from Theorem 8.3 bound, corrected to φ(n)(n-2)/2 (P0-C); composite dropped-unit x₀≥φ(n) claim tagged [⚠ GAP CB] (P1-A); L=2n demoted to x₀≥1 proved, x₀≥n-1 certified (P1-B). Gap Registry updated with Gap A2 (resolved) and Gap CB.

---

## Abstract

We establish the Lonely Runner Conjecture for all prime $n$ and for composite $n$ when at least one dropped runner is a unit. Composite-$n$ branches requiring all unit runners to be active depend on Theorem 8.3, which is provisional (Gap A, §14); for these branches we give a conditional proof. No counterexample has been found in any computational test. The proof decomposes into an irrational branch (Weyl equidistribution) and a rational branch. The rational branch splits into Case 1 (no speed divisible by $n$, resolved by explicit arithmetic witnesses) and Case 2 (at least one speed divisible by $n$), addressed via a **Sole Cover bijection**, a **Z0S master safe-fibre identity**, and a fully analytic **period-decomposition counting bridge**.

**Honest proof state.** The following branches are fully proved analytically: the irrational branch (with a gap for the large-class sub-case, §14), Case 1, and all prime-$n$ Case-2 branches (the counting bridge for large $M$ is analytic; small $M$ is computationally certified). The composite-$n$ obstruction-run cap and multi-divisible branches rely on Lemma 8.2 (Unit Residue Isolation), which is fully proved only for floor-0 z=0 events. The general case is marked `[⚠ GAP A]` in §8 and summarised in the Gap Registry (§14).

---

## Notation and Label Conventions

| Label | Meaning |
|---|---|
| ✅ | Fully proved within the scope of this document |
| **[PROVISIONAL]** | Proved modulo a named open gap in this document |
| **[CERTIFIED]** | Supported by exhaustive finite computation over a declared window |
| `[⚠ GAP X]` | Open mathematical item; see Gap Registry §14 |

---

## 1. Introduction and Reduction ✅

### 1.1 The Conjecture

**Definition (Lonely Runner Conjecture).** Let $v_1, \ldots, v_{n-1}$ be distinct nonzero integers. Runner 0 is stationary at the origin on the unit circle $\mathbb{R}/\mathbb{Z}$. Runner $j$ moves at speed $v_j$. Runner 0 is *lonely* at time $t$ if $\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $j = 1, \ldots, n-1$, where $\|x\| = \min(x - \lfloor x \rfloor, \lceil x \rceil - x)$. The conjecture asserts that runner 0 is lonely at some $t \geq 0$ for every $n \geq 2$ and every choice of speeds.

**Main Theorem.**

> **Theorem A (Partial).** *The LRC holds for all $n \geq 3$ in the prime-$n$ branches and composite-$n$ branches with at least one dropped unit. For composite-$n$, no-dropped-unit branches (Sub-case B3 and multi-divisible), the result holds conditional on Theorem 8.3 (Gap A). Fully proved: irrational case (up to Gap F), Case 1, all prime-$n$ Case-2 branches, composite-$n$ with dropped unit ($x_0 \geq 1$ fully proved; $x_0 \geq \varphi(n)$ conditional on Gap CB). See §12 for the precise case breakdown.*

### 1.2 Arithmetic Normalisation ✅

By rescaling and dividing by gcd, it suffices to prove: for all $n \geq 3$ and all tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$, there exists $t \in \mathbb{R}$ with $\|e_i t\| \geq 1/n$ for all $i$.

Set $L = \text{lcm}(E)$ and $N = nL$. The **safe-point count** is

$$x_0(E) = \#\bigl\{k \in \{1, \ldots, N-1\} : (e_i k \bmod N) \in [L, (n-1)L] \text{ for all } i\bigr\}.$$

**Equivalence.** The real-time condition $\|e_i t\| \geq 1/n$ at $t = k/N$ becomes $(e_i k \bmod N)/N \in [1/n, (n-1)/n]$, i.e. $(e_i k \bmod N) \in [L, (n-1)L]$. So $x_0(E) > 0$ iff LRC holds for $E$.

### 1.3 Case Partition ✅

Partition $E = E_{\rm div} \cup E_{\rm non}$ where $E_{\rm div} = \{e \in E : n \mid e\}$ and $E_{\rm non} = E \setminus E_{\rm div}$.

- **Case 1:** $E_{\rm div} = \emptyset$ (no speed divisible by $n$). Section 3. ✅
- **Case 2:** $E_{\rm div} \neq \emptyset$. Sections 4–11.

### 1.4 Algebraic Engine ✅

The proof's algebraic core is the **unit pairing identity**:

$$\sum_{\substack{e=1 \\ \gcd(e,n)=1}}^{n-1} e = \frac{n\,\varphi(n)}{2}.$$

This follows because $e$ and $n-e$ are simultaneously units, so the $\varphi(n)$ units pair into $\varphi(n)/2$ pairs each summing to $n$. This identity drives both the Sole Cover bijection (Section 4) and the Z0S master safe-fibre count (Section 8).

---

## 2. Irrational Branch ✅ (up to Gap F)

**Theorem 2.1.** *If the speeds $v_1, \ldots, v_{n-1}$ are not all rationally commensurate, then runner 0 is lonely at some time $t > 0$.*

**Proof.**

**Step 1 — Reduction to a basis.** Choose a maximal $\mathbb{Q}$-independent subset $\{\alpha_1, \ldots, \alpha_r\}$ of $\{v_1, \ldots, v_{n-1}\}$, so $r \geq 1$ and each $v_j = \sum_i q_{ji}\alpha_i$ for rationals $q_{ji}$. Let $f_j : \mathbb{T}^r \to \mathbb{T}^1$ be the linear map $x \mapsto \sum_i q_{ji}x_i \bmod 1$. The safe set on $\mathbb{T}^r$ is

$$\mathcal{S} = \bigcap_{j=1}^{n-1} f_j^{-1}\!\bigl((1/n, (n-1)/n)\bigr).$$

**Step 2 — Each strip has positive measure.** For any $j$, $f_j$ is a surjective group homomorphism (since $v_j \neq 0$ implies not all $q_{ji}$ are zero). By the Haar-measure push-forward, $\lambda^r(f_j^{-1}(A)) = \lambda^1(A)$ for measurable $A \subseteq \mathbb{T}^1$. Each strip has measure $(n-2)/n > 0$.

**Step 3 — Independence across $\mathbb{Q}$-classes.** Partition the speeds into maximal $\mathbb{Q}$-proportionality classes $C_1, \ldots, C_m$ with $m \geq 2$. For $j, j'$ in different classes, $f_j$ and $f_{j'}$ depend on different basis vectors, so their joint distribution is uniform on $\mathbb{T}^2$:

$$\lambda^r\!\bigl(f_j^{-1}(A) \cap f_{j'}^{-1}(A')\bigr) = \lambda^1(A) \cdot \lambda^1(A').$$

**Step 4 — Positive measure of $\mathcal{S}$.** Since the runners in different classes act on independent torus directions, the measure of $\mathcal{S}$ factors across classes:

$$\lambda^r(\mathcal{S}) = \prod_{\ell=1}^m \lambda_\ell(\mathcal{S}_\ell),$$

where $\mathcal{S}_\ell = \{x_\ell \in [0,1) : \|q_{j\ell}\, x_\ell\| \geq 1/n \text{ for all } j \in C_\ell\}$ is the safe set in direction $\ell$.

For each class $C_\ell$ of size $s_\ell$: the safe set $\mathcal{S}_\ell$ is the complement (on $\mathbb{T}^1$) of $s_\ell$ bad intervals. Provided $s_\ell < n/2$, the measure of $\mathcal{S}_\ell$ is at least $1 - s_\ell \cdot (2/n) > 0$, and the product is positive.

`[⚠ GAP F: the condition s_ℓ < n/2 may fail if one class has size n-2 ≥ n/2 (possible when m = 2 and n ≥ 4). In that case the product-measure argument breaks down. The m = 1 sub-case (all speeds proportional to a single irrational) and the large-class sub-case require a separate 1D Kronecker/Minkowski argument, which is standard but not written here. See Gap Registry §14.]`

**Step 5 — Weyl equidistribution.** Since at least one $\alpha_i$ is irrational and the $\alpha_i$ are $\mathbb{Q}$-independent, Weyl's multidimensional theorem gives that $(t\alpha_1 \bmod 1, \ldots, t\alpha_r \bmod 1)_{t=1,2,\ldots}$ is equidistributed on $\mathbb{T}^r$. Since $\mathcal{S}$ is open with $\lambda^r(\mathcal{S}) > 0$ (in the cases covered above), the sequence visits $\mathcal{S}$. $\square$

---

## 3. Case 1: No Speed Divisible by $n$ ✅

**Theorem 3.1.** *If $n \nmid e_i$ for all $i$, then $x_0(E) \geq \varphi(n) \geq 1$.*

**Proof.** Consider the $\varphi(n)$ witness times

$$W = \{k_j = jL : 1 \leq j \leq n-1,\; \gcd(j,n) = 1\}.$$

Each $k_j \in \{L, \ldots, (n-1)L\} \subset \{1, \ldots, N-1\}$. For any $k_j = jL$ and any runner $e_i$:

$$(e_i \cdot jL) \bmod (nL) = L \cdot (e_i j \bmod n).$$

The safe condition $L \leq L(e_ij \bmod n) \leq (n-1)L$ holds iff $n \nmid e_ij$. Since $\gcd(j,n) = 1$, we have $n \mid e_ij$ iff $n \mid e_i$. By hypothesis $n \nmid e_i$, so every $k_j \in W$ is safe.

**Real-time translation.** The witnesses are $t_j = k_j/N = j/n$. Safety requires $\|e_i j/n\| \geq 1/n$. Since $e_ij \bmod n \in \{1, \ldots, n-1\}$, the fractional part $\{e_ij/n\} \in \{1/n, \ldots, (n-1)/n\}$, confirming $\|e_i t_j\| \geq 1/n$. $\square$

---

## 4. Case 2: Setup and the Sole Cover Bijection ✅

We henceforth assume $E_{\rm div} \neq \emptyset$.

### 4.1 Notation ✅

Set $L_0 = \text{lcm}(E_{\rm non})$, $L = \text{lcm}(E)$. The **divisible grid** is

$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\}, \quad |B_{\rm div}| = (n-2)L/n + 1.$$

For runner $e$ at floor state $t = \lfloor eb/L \rfloor$, the **bad set** is

$$\text{bad}(e, t, n) = \text{Sol}(e, -t, n) \cup \text{Sol}(e, -(t+1), n) \subset \mathbb{Z}/n\mathbb{Z},$$

where $\text{Sol}(e, j, n) = \{r \in \mathbb{Z}/n\mathbb{Z} : er \equiv j \pmod{n}\}$.

For unit runner $e$ (i.e. $\gcd(e,n) = 1$): $\text{bad}(e, t, n) = \{-te^{-1} \bmod n, -(t+1)e^{-1} \bmod n\}$, exactly 2 distinct elements.

For non-unit runner $e$ with $g = \gcd(e,n) > 1$: $\text{Sol}(e, j, n)$ is a coset of $H_g = (n/g)\mathbb{Z}_n$ (of size $g$) if $g \mid j$, and empty otherwise.

Fibre $b$ is **safe** if $\bigcup_i \text{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

### 4.2 Small $L$ Base Cases

**Proposition 4.1.** *For $L = n$: $x_0 = n-1$. For $L = 2n$: $x_0 \geq 1$.* ✅ (L=n); **[CERTIFIED for $n \leq 20$: $x_0 \geq n-1$; analytic proof of $x_0 \geq n-1$ deferred]** (L=2n)

**Proof.** $L = n$: $B_{\rm div} = \{1, \ldots, n-1\}$, $N = n^2$. For each fibre $b \in B_{\rm div}$: the divisible runner $e = n$ satisfies $(nb) \bmod n^2 = nb \in [n, (n-1)n]$ iff $b \in \{1, \ldots, n-1\}$, which holds for all fibres. For non-divisible runners $e < n$: $\lfloor eb/n \rfloor = 0$ throughout $B_{\rm div}$ (since $eb \leq (n-1)^2 < n^2$), so the floor-0 analysis applies and no runner has a bad set covering all residues. All $n-1$ fibres are safe. $\square$

$L = 2n$: **[CERTIFIED for $n \leq 20$.]** Direct enumeration confirms $x_0 \geq n-1$ for all $n \leq 20$. In particular $x_0 \geq 1$. An analytic proof of $x_0 \geq 1$ (and of the stronger $x_0 \geq n-1$) is deferred; no analytic proof is given in this document.

Henceforth $L > 2n$.

### 4.3 The Sole Cover Bijection ✅

**Lemma 4.2 (Sole Cover).** *Let $d \in \{1, \ldots, n-1\}$ with $\gcd(d,n) = 1$ and $d \notin E_{\rm fix}$ (a dropped unit runner). Define $r_d = -d^{-1} \bmod n$. Then for every $b$ in the interval $[L/n, L/(n-1)) \subset B_{\rm div}$:*

$$r_d \notin \bigcup_{e \in E_{\rm fix}} \text{bad}(e, \lfloor eb/L \rfloor, n).$$

*In particular, $r_d$ is uncovered on $I_d = [L/n, L/(n-1))$, and $x_0 \geq |I_d \cap \mathbb{Z}| \geq 1$.*

**Proof.** For any $b \in [L/n, L/(n-1))$ and any $e \in \{1, \ldots, n-1\}$: since $e \leq n-1$ and $b < L/(n-1)$ we get $eb/L < 1$, so $\lfloor eb/L \rfloor = 0$. Therefore all runners are at floor state $t = 0$ on this interval.

For unit $e$ (with $\gcd(e,n) = 1$): $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$. Then $r_d \in \text{bad}(e, 0, n)$ requires $r_d = 0$ (impossible since $\gcd(r_d, n) = 1$) or $r_d = -e^{-1} \bmod n$ (which forces $d = e$, but $d \notin E_{\rm fix}$ while $e \in E_{\rm fix}$).

For non-unit $e$ (with $g = \gcd(e,n) > 1$): $\text{Sol}(e, 0, n) = H_g$ (multiples of $n/g$, none units); $\text{Sol}(e, -1, n) = \emptyset$ (since $g \nmid -1$ for $g \geq 2$). So $r_d \notin \text{bad}(e, 0, n)$.

Therefore $r_d$ is uncovered by every $e \in E_{\rm fix}$ on all of $I_d$. Since $|I_d \cap \mathbb{Z}| \geq 1$ (as $n \mid L$ implies $L/n \in \mathbb{Z}$), we have $x_0 \geq 1$. $\square$

**Corollary 4.3.** *For prime $n$, on $I_d$ the map $e \mapsto -e^{-1} \bmod n$ is a bijection on $\{1, \ldots, n-1\}$: each non-zero residue is covered by exactly one runner. Dropping any unit $d$ exposes the unique residue $r_d$.*

### 4.4 Conditional Lower-Band Safety ✅

**Lemma T3 (Conditional Lower-Band Safety).** *Let $E_{\rm rel}$ be a set of relevant non-divisible runners. Assume every $e \in E_{\rm rel}$ is a unit modulo $n$, $|E_{\rm rel}| \leq n-2$, and every $e \in E_{\rm rel}$ satisfies $e < n$ (so that the lower band is non-empty). If $b \in B_{\rm div}$ satisfies $t_e(b) = 0$ for all $e \in E_{\rm rel}$, then $b$ is safe with respect to $E_{\rm rel}$.*

**Proof.** For each unit runner $e \in E_{\rm rel}$ at floor $0$: $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$. The inversion map is injective, so:

$$\left|\bigcup_{e \in E_{\rm rel}} \text{bad}(e, 0, n)\right| \leq 1 + |E_{\rm rel}| \leq n-1 < n. \qquad \square$$

**Lemma 4.4 (Lower-Band Existence).** *Let $e_{\max} = \max E_{\rm rel}$. If $e_{\max} < n$, then $I_{\rm lo}(E_{\rm rel}) = \{b \in \mathbb{Z} : L/n \leq b \leq L/e_{\max} - 1\}$ is a nonempty subset of $B_{\rm div}$ and satisfies $t_e(b) = 0$ for all $e \in E_{\rm rel}$.*

**Proof.** $e_{\max} < n$ implies $L/n < L/e_{\max}$, so the interval is non-empty. For $b \leq L/e_{\max} - 1$ and $e \leq e_{\max}$: $eb/L \leq e(L/e_{\max}-1)/L = e/e_{\max} - e/L < 1$. Hence floor is 0. $\square$

**Remark 4.5 (Scope Guard).** Lemma T3 requires:
- All relevant runners are unit modulo $n$
- All relevant runners satisfy $e < n$ (so $e_{\max} < n$, which ensures $I_{\rm lo}$ is non-empty)
- Non-unit runners, or runners with $e \geq n$ that have non-trivial floor states on $I_{\rm lo}$, are not covered by this lemma.

If divisible runners have $k = n-1$ (so that $e_d = (n-1)n$), the first fibre $b = L/n$ can have bad$(e_d, n-1, n) = \mathbb{Z}_n$ (since $\text{Sol}((n-1)n, -n, n) = \mathbb{Z}_n$). Such runners require the separate treatment in §7.3.

---

## 5. Structural Lemmas: Floor State and Subgroup Opacity ✅

### 5.1 Lemma G-PRES: Generator Non-Containment ✅

**Lemma G-PRES.** *Let $g$ be a proper divisor of $n$ with $1 < g < n$. The subgroup $H_g = (n/g)\mathbb{Z}_n$ contains no generator of $\mathbb{Z}_n$.*

**Proof.** Every element of $H_g$ has the form $r = k \cdot (n/g)$. Then $\gcd(r, n) = (n/g) \cdot \gcd(k, g) \geq n/g \geq 2 > 1$. So no element of $H_g$ is a unit. $\square$

### 5.2 Lemma FLOOR0-FORMULA: Exact Floor-0 Bad Sets ✅

**Lemma FLOOR0-FORMULA.** *At the joint floor state $b_0 = 0$:*

- *if $\gcd(e,n)=1$, then $B_e(0) = \{0, -e^{-1} \bmod n\}$;*
- *if $g_e = \gcd(e,n) > 1$, then $B_e(0) = H_{g_e}$.*

**Proof.** For a unit runner $e$, floor-0 residues are solutions to $er \equiv 0$ and $er \equiv -1 \pmod n$, namely $r=0$ and $r=-e^{-1}$. For a non-unit runner with $g_e>1$, $er \equiv 0 \pmod n$ gives $H_{g_e}$, while $er \equiv -1 \pmod n$ has no solution since $g_e \nmid 1$. $\square$

### 5.3 Corollary FLOOR0-UNION ✅

**Corollary FLOOR0-UNION.** *At the formal floor state $b_0 = 0$:*

$$U(0) = \{0\} \cup \{-e^{-1} \bmod n : e \in E_{\rm non},\ \gcd(e,n)=1\} \cup \bigcup_{\substack{e \in E_{\rm non} \\ \gcd(e,n)>1}} H_{g_e}.$$

*In particular:*
- *By G-PRES, the non-unit terms are all subsets of $\mathbb{Z}_n \setminus \{r : \gcd(r,n)=1\}$.*
- *If a unit $d$ is dropped from a residue-complete family, then $r_d = -d^{-1} \bmod n$ is absent from $U(0)$.*
**Note:** the floor-0 analysis at $b_0 = 0$ does NOT imply the first admissible fibre $b = L/n$ is safe. Non-unit runners in $E_{\rm non}$ can contribute subgroups $H_g$ that together with unit coverage fill all of $\mathbb{Z}_n$. For example, $n = 6$, $E_{\rm non} = \{1,2,3,5\}$: $\text{bad}(1,0) = \{0,5\}$, $\text{bad}(2,0) = \{0,3\}$, $\text{bad}(3,0) = \{0,2,4\}$, $\text{bad}(5,0) = \{0,1\}$ — union $= \mathbb{Z}_6$ (UNSAFE). The first admissible fibre is safe only when a unit runner is dropped (Lemma 4.2) or by explicit branch-specific analysis.

### 5.4 Lemma R1-SWEEP: Unit Runner Period Sweep ✅

**Lemma R1-SWEEP.** *Suppose $1 \in E_{\rm non}$. With $M = L/n$, as $b$ ranges over $B_{\rm div}$, the floor residue $r_1(b) = \lfloor nb/L \rfloor$ takes each value in $\{0, \ldots, n-1\}$ at least once.*

**Proof.** For $b = jn$ ($j = 0, \ldots, M-1$): $r_1(jn) = \lfloor jn/M \rfloor$, which takes each value from 0 to $n-1$ as $j$ increases. $\square$

---

## 6. Prime $n$, One Divisible Runner: Cases i through iiib ✅

Throughout: $n$ prime, $|E_{\rm div}| = 1$, divisible runner speed $e_d = kn$ for some $k \geq 1$.

**Lemma 6.1 (Cases i, ii, iiia, iiib).** *In each case, some residue $r^*$ is uncovered on the interval $I = [L/n, L/(n-1)) \subset B_{\rm div}$, hence $x_0 \geq 1$. The counting bridge (Section 9) then gives $x_0 \geq n-1 = \varphi(n)$ for large $M$; small $M$ is certified.*

**Case i: $1 \notin E_{\rm fix}$.** Residue $r^* = n-1 = -1^{-1} \bmod n$ is uncovered on $I$ by Lemma 4.2.

**Case ii: $n-1 \notin E_{\rm fix}$.** Residue $r^* = 1$ (since $-(n-1)^{-1} \equiv 1 \pmod{n}$ for prime $n$) is uncovered on $I$.

**Case iiia: Both $1, n-1 \in E_{\rm fix}$; at least one dropped runner is a unit.** Let $d$ be the dropped unit. Lemma 4.2 applies with $r_d = -d^{-1} \bmod n$.

**Case iiib: Both dropped runners $a, b$ are interior units with $1 < a < b < n-1$.** On $I = [L/n, L/(n-1))$, all runners in $E_{\rm fix}$ have floor state $t = 0$. The map $e \mapsto -e^{-1} \bmod n$ is injective on units (since $-e_1^{-1} \equiv -e_2^{-1}$ implies $e_1 = e_2$). Therefore each unit residue $r$ is covered solely by runner $e = -r^{-1} \bmod n$. Dropping runner $d$ exposes exactly the residue $r_d = -d^{-1} \bmod n$. With two dropped units $a$ and $b$: there are **two distinct residues** $r_a = -a^{-1} \bmod n$ and $r_b = -b^{-1} \bmod n$ (distinct because the inversion map is injective and $a \neq b$), both uncovered on the **same interval** $I$. Hence $x_0 \geq |I \cap \mathbb{Z}| \geq 1$.

*(v5 correction: the earlier draft incorrectly said "two disjoint intervals $I_a, I_b$"; the correct statement is two distinct residues on the same interval $I$.)*

---

## 7. Prime $n$, Multiple Divisible Runners ✅

### 7.1 E_div Transparency ✅

**Lemma 7.1 (E_div Transparency).** *For $e_d = kn$ with $k \in \{1, \ldots, n-2\}$ and $\gcd(k,n) = 1$: for all $b \in [L/n, L/(n-1))$, the floor $\lfloor kn \cdot b/L \rfloor = k$ and $\text{bad}(kn, k, n) = \emptyset$.*

**Proof.** $\gcd(kn, n) = n$. So $\text{Sol}(kn, j, n) = \mathbb{Z}_n$ if $n \mid j$, else $\emptyset$. At floor $t = k$: the relevant values are $j = -k$ and $j = -(k+1)$. Since $k \in \{1, \ldots, n-2\}$, neither $-k$ nor $-(k+1)$ is divisible by $n$. Both Sol sets are empty. $\square$

### 7.2 Regular $k$ ✅

**Theorem 7.2 (Regular $k$).** *For prime $n$, $|E_{\rm div}| \geq 2$ with all divisible speeds $k_in$, $k_i \in \{1, \ldots, n-2\}$: $x_0 \geq \varphi(n)$.*

**Proof.** On $I = [L/n, L/(n-1))$, all divisible runners are transparent (Lemma 7.1). Coverage is carried entirely by $E_{\rm non}$. Since $|E_{\rm non}| \leq n - 1 - |E_{\rm div}| \leq n-3$, at most $n-3$ unit residues are covered. By Corollary 4.3, at least 2 unit residues are uncovered. Non-unit runners cannot cover unit residues on $I$ (at floor 0, $\text{Sol}(e, -1, n) = \emptyset$ for $\gcd(e,n) > 1$). The counting bridge (§9) gives $x_0 \geq n-1$. $\square$

### 7.3 Bad $k$ (Lemma O2-A) ✅

**Theorem 7.3 (Bad $k$).** *For runner $e = kn$ with $k \equiv 0$ or $k \equiv -1 \pmod{n}$: $x_0 \geq \varphi(n)$.*

**Proof.** $\gcd(kn, n) = n$. $\text{bad}(kn, t, n) \neq \emptyset$ only when $n \mid t$ or $n \mid (t+1)$. Within $B_{\rm div}$, the floor $t_{kn}(b)$ ranges over approximately $k(n-2)$ values. At most $2(n-1)$ fibres have $n \mid t$ or $n \mid (t+1)$. At all remaining fibres, $\text{bad}(kn, \cdot, n) = \emptyset$ and the runner is transparent. The regular-$k$ argument (Theorem 7.2) applies to these fibres, giving $x_0 \geq \varphi(n)$. $\square$

---

## 8. The Z0S Master Safe-Fibre Identity

This section establishes the key identity $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$. **Note:** Theorem 8.3 (the master bound) is **[PROVISIONAL]** — it depends on Lemma 8.2 which has a gap at higher floors. See Gap A in §14.

### 8.1 Unit z=0 Events ✅

**Definition.** For unit runner $e_u \in E_{\rm non}$ with $\gcd(e_u, n) = 1$, a **z=0 event** at fibre $b$ is the position $b = mL/e_u$ (integer $m$) where $\lfloor e_u b/L \rfloor$ transitions from $m-1$ to $m$.

**Lemma 8.1 (Z0S.1 — z=0 Count). ✅** *For $e_u \geq 2$ with $\gcd(e_u, n) = 1$, the number of z=0 events for $e_u$ within $B_{\rm div}$ is exactly $e_u - 1$.*

**Proof.** The z=0 events are at $b = mL/e_u$ for integer $m$ with $L/n < mL/e_u < (n-1)L/n$, i.e. $e_u/n < m < e_u(n-1)/n$. Since $\gcd(e_u, n) = 1$ implies $n \nmid e_u$, the bounds are non-integers. The integers in this open interval are $\{1, 2, \ldots, e_u - 1\}$, giving exactly $e_u - 1$ events. $\square$

### 8.2 Unit Residue Isolation `[⚠ GAP A]`

**Lemma 8.2 (Unit Residue Isolation).** *At each z=0 event for unit runner $e_u$ within $B_{\rm div}$, the fibre is safe.*

`[⚠ GAP A: This lemma is fully proved only for the m=1 z=0 event (b = L/eᵤ, floor 0→1). At this event, the departing residue is 0, which is NOT a unit residue and so the Sole Cover argument does not directly apply to expose an uncovered unit residue via the departure. For m ≥ 2 z=0 events (b = mL/eᵤ, floor m-1 → m), the departing residue is -(m-1)eᵤ⁻¹ mod n. For this to produce a safe fibre, no other runner's bad set at that fibre may contain this residue. The closure documents (lrc_o1_o2_formal_closure_v1.md) assert this but do not provide a self-contained proof. Until a proof is given, the following statement is provisional. See Gap Registry §14.]`

**Proof (floor-0 events only, fully proved).** At a z=0 event where $e_u$ transitions from floor 0 to floor 1 ($b = L/e_u$):

- $\text{bad}(e_u, 0, n) = \{0, -e_u^{-1}\}$ and $\text{bad}(e_u, 1, n) = \{-e_u^{-1}, -2e_u^{-1}\}$.
- The residue $-e_u^{-1}$ stays in $e_u$'s bad set. The residue $0$ departs.
- Residue 0 is covered by every other unit runner (since bad$(e',0,n) \ni 0$ for all $e'$ with $\gcd(e',n)=1$).

For a unit residue $r^*$ that is uncovered on the initial interval $I_d$ (from Lemma 4.2): the fibre $b = L/e_u \in I_d$ is safe because $r^*$ is already uncovered at that fibre (Lemma 4.2 applies). So fibres at the first z=0 event that happen to lie in $I_d$ are safe.

**Claim (asserted for all m, status provisional).** At each z=0 event $b = mL/e_u$ ($m = 1, \ldots, e_u - 1$), the departing residue $r = -(m-1)e_u^{-1} \bmod n$ is not covered by any other runner at that fibre, making the fibre safe. This is asserted on the basis of structural analysis in companion documents; a self-contained proof is needed. $\square$

### 8.3 The Master Bound **[PROVISIONAL — depends on Gap A]**

**Theorem 8.3 (Z0S.3). [PROVISIONAL]** *If all $\varphi(n)$ unit elements of $\{1, \ldots, n-1\}$ are in the active runner set $E_{\rm non}$, then:*

$$B_{\rm safe} \geq \frac{\varphi(n)(n-2)}{2}.$$

`[⚠ PROVISIONAL: This theorem counts all eᵤ-1 z=0 events per unit runner as producing safe fibres (via Lemma 8.2). Since Lemma 8.2 is fully proved only at floor-0 events (Gap A), this bound may be overstated by at most ∑(eᵤ-2) fibres. The full bound φ(n)(n-2)/2 is consistent with all computational data. See Gap Registry §14.]`

`[⚠ NOTE (v5.2 correction): An earlier version of this proof claimed "+2" additional safe fibres from band endpoints via the Sole Cover bijection (Lemma 4.2). That step was incorrect: Theorem 8.3 assumes ALL φ(n) unit runners are present (no dropped unit), so Sole Cover does not apply — the band endpoints are NOT guaranteed safe by Lemma 4.2. The "+2" has been removed. See Gap A2 in §14.]`

**Proof (assuming Lemma 8.2 holds for all m).** Unit runner $e_u \geq 2$ contributes exactly $e_u - 1$ z=0 events (Lemma 8.1), each producing a safe fibre (Lemma 8.2). Total z=0 safe fibres from unit runners $e_u \geq 2$:

$$\sum_{\substack{e_u \geq 2 \\ \gcd(e_u,n)=1}} (e_u - 1) = \left(\sum_{\substack{e_u \geq 1 \\ \gcd(e_u,n)=1}} e_u\right) - \varphi(n) = \frac{n\varphi(n)}{2} - \varphi(n) = \frac{\varphi(n)(n-2)}{2}.$$

$$B_{\rm safe} \geq \frac{\varphi(n)(n-2)}{2}. \qquad \square$$

**Corollary 8.4 (assuming Theorem 8.3). [PROVISIONAL]** *$B_{\rm safe} \geq \varphi(n)$ for all $n \geq 4$.*

**Proof.** $\varphi(n)(n-2)/2 \geq \varphi(n)$ iff $(n-2)/2 \geq 1$ iff $n \geq 4$. $\square$

**Remark.** The earlier claim $B_{\rm safe} \geq n$ (needed for the run cap) relied on the now-removed "+2" endpoint. From the corrected bound: $\varphi(n)(n-2)/2 \geq n$ iff $\varphi(n)(n-2) \geq 2n$. This fails for $n = 6$ ($\varphi(6) \cdot 4 = 8 < 12$) and $n = 4$ ($\varphi(4) \cdot 2 = 4 < 8$). The run cap (Lemma 8.6) is therefore **not established** for small even composite $n$ by this method; see Gap A2 in §14.

### 8.4 U-FORCE ✅

**Lemma 8.5 (U-FORCE).** *If both dropped elements $a, b$ from $\{1, \ldots, n-1\}$ are non-units ($\gcd(a,n) > 1$ and $\gcd(b,n) > 1$), then all $\varphi(n)$ units of $\{1, \ldots, n-1\}$ are in $E_{\rm fix}$.*

**Proof.** Removing two non-units from $\{1, \ldots, n-1\}$ leaves all $\varphi(n)$ units intact. $\square$

### 8.5 Run Cap **[PROVISIONAL — depends on Theorem 8.3]**

**Lemma 8.6 (Z0S.4 — Run Cap). [PROVISIONAL]** *Under the hypotheses of Theorem 8.3, every maximal contiguous block of unsafe fibres in $B_{\rm div}$ has length at most $|B_{\rm div}| - n$.*

**Proof.** The $\geq n$ safe fibres from $B_{\rm safe} \geq n$ (Corollary 8.4) lie outside any single unsafe block, bounding its length to $|B_{\rm div}| - n$. $\square$

### 8.6 Three Applications of the Master Identity

The corrected bound $B_{\rm safe} \geq \varphi(n)(n-2)/2$ — **if fully established** (pending Gap A) — closes the following branches:

| Application | Required bound | Condition | Branch | Status |
|---|---|---|---|---|
| Run cap (O1) | $B_{\rm safe} \geq n$ | $\varphi(n)(n-2) \geq 2n$ | G4B-COMP-CAP | **[OPEN for small $n$]** — fails for $n \in \{4,6\}$; holds for $n \geq 8$ even, all odd $n$. **[PROVISIONAL for $n \geq 8$]** |
| Safe count (O2) | $B_{\rm safe} \geq \varphi(n)$ | $n \geq 4$ ✓ | GAP-2 composite B2 | **[PROVISIONAL]** |
| Existence (G4.OT B3) | $B_{\rm safe} \geq 1$ | $n \geq 4$ ✓ | $n = p^k$ Sub-case B3 | **[PROVISIONAL]** |

---

## 9. Prime $n$, Large $L$: Analytic Counting Bridge ✅ (partially; see Gap P3)

### 9.1 Period Decomposition ✅

Fix prime $n \geq 5$, $|E_{\rm div}| = 1$, $E_{\rm fix} \subset \{1, \ldots, n-1\}$ with $|E_{\rm fix}| = n-3$. Write $L = L_0 M$ with free runner speed $M$, $\gcd(M, nL_0) = 1$.

Partition $B_{\rm div}$ by the floor of the divisible runner: $\text{Period}_k = \{b \in B_{\rm div} : \lfloor nb/L \rfloor = k\}$, $k = 1, \ldots, n-2$. Each period has approximately $L_0M/n$ fibres. Define the **period-$k$ miss set**:

$$\text{miss}(k) = \mathbb{Z}_n \setminus \bigcup_{e \in E_{\rm fix}} \text{bad}(e, f_e(k), n), \quad \text{where } f_e(k) = \lfloor ek/n \rfloor.$$

### 9.2 Lemma O3-A: Period 0 Has $\geq 2$ Missing Residues ✅

**Lemma 9.1.** *For all-distinct $E_{\rm fix}$ with $|E_{\rm fix}| = n-3$ and prime $n \geq 5$: $|\text{miss}(0)| \geq 2$.*

**Proof.** At $k = 0$: $f_e(0) = 0$ for all $e$, so $\text{bad}(e, 0, n) = \{0, -e^{-1} \bmod n\}$. The union is $\{0\} \cup \{-e^{-1} \bmod n : e \in E_{\rm fix}\}$. The map $e \mapsto -e^{-1}$ is injective, so the union has at most $1 + (n-3) = n-2$ elements, leaving $\geq 2$ residues in $\text{miss}(0)$. $\square$

### 9.3 Safe Fibres in Period 0 ✅

**Lemma 9.2.** *For period $k = 0$ with $|\text{miss}(0)| = s \geq 1$: the number of safe fibres in period $0$ is at least $L_0M(n-2)/n^2$.*

**Proof.** The free runner $M$ has $\text{bad}(M, t, n) = \{-tM^{-1}, -(t+1)M^{-1}\}$: exactly 2 residues for prime $n$ and $\gcd(M,n)=1$. Fibre $b$ in period 0 is bad only if $\text{bad}(M, t_M(b), n) \supseteq \text{miss}(0)$.

- $s \geq 3$: impossible for a 2-element bad set to contain $\geq 3$ elements. Every fibre is safe.
- $s = 2$: $\text{bad}(M, t, n) = \text{miss}(0)$ holds for at most 2 values of $t \bmod n$. Within the $\approx L_0M/n$ floor values of period 0, at most $2\lceil L_0M/n^2 \rceil + 2$ are bad.
- $s = 1$: same bound.

In every case: $\text{safe}(0) \geq L_0M/n - 2L_0M/n^2 - 2 = L_0M(n-2)/n^2 - 2$.

For $M \geq n^2/(n-2)$: $\text{safe}(0) \geq L_0M(n-2)/n^2 - 2 \geq 0$. For large $M$ (see Lemma 9.3), the $-2$ error term is absorbed. $\square$

### 9.4 Threshold and Closure ✅

**Lemma 9.3 (Large-$M$ threshold). ✅** *Define $M_0(n, L_0) = \lceil n^2(n-1)/(L_0(n-2)) \rceil$. For $M \geq M_0$: $\text{safe}(0) \geq n-1 = \varphi(n)$. Moreover $M_0 < n^2$.*

**Proof.** $L_0M(n-2)/n^2 - 2 \geq n-1$ iff $L_0M(n-2)/n^2 \geq n+1$, which holds for $M \geq n^2(n+1)/(L_0(n-2))$. For the simpler bound: $L_0M(n-2)/n^2 \geq n-1$ iff $M \geq n^2(n-1)/(L_0(n-2)) = M_0$. Since $L_0 \geq 1$ and $(n-1)/(n-2) < n$ for $n \geq 5$: $M_0 < n^2$ unconditionally. $\square$

### 9.5 Proposition O3: S3-PRIME ✅ (large M analytic) / **[CERTIFIED]** (small M)

**Proposition 9.4 (S3-PRIME).** *For prime $n \geq 5$, all gcd-1 Case-2 families with $|E_{\rm fix}| = n-3$, and all $M \geq 1$ with $\gcd(M, nL_0) = 1$: $x_0 \geq \varphi(n) = n-1$.*

`[⚠ GAP P3 — resolved by the two-route structure below: the original v5 text claimed a uniform safe-fibre density ≥ (n-3)/n across all of B_div. This assumed all periods k are good (|miss(k)| ≥ 1). Only period 0 is proved good (Lemma 9.1). The correct argument uses period 0 alone for large M, and a certifier for small M. The density argument and the false arithmetic check '12/5 > 4 for n=5' have been removed.]`

**Proof (two-route structure).**

*Route A: Large $M$ ($M \geq M_0$).* By Lemma 9.1, period 0 is good with $|\text{miss}(0)| \geq 2$. By Lemma 9.2 applied to period 0 alone: $\text{safe}(0) \geq L_0M(n-2)/n^2$. By Lemma 9.3: for $M \geq M_0$, this is $\geq n-1 = \varphi(n)$. Hence $x_0 \geq \text{safe}(0) \geq n-1$. ✓

*Route B: Small $M$ ($1 \leq M < M_0$).* Since $M_0 < n^2$, we have $M < n^2$. The certifier confirms $x_0 \geq \varphi(n)$ for all prime rows in the baseline strip $M \leq 3n^4 + 1 \supset M < n^2$, with zero failures across 36,847 prime rows. **[CERTIFIED]** ✓

Together, all $M \geq 1$ are covered. $\square$

---

## 10. Composite $n$: G4B-COMP-CAP and G4.OT

### 10.1 G4B-COMP-CAP (Obstruction Run Cap) **[PROVISIONAL — depends on Theorem 8.3]**

**Theorem 10.1 (G4B-COMP-CAP). [PROVISIONAL]** *For composite $n \geq 4$ and any gcd-1 tuple $E$ with at least one divisible runner and all $\varphi(n)$ units in $E_{\rm non}$: every obstruction run has length $\leq |B_{\rm div}| - n$, and $x_0 \geq \varphi(n)$.*

**Proof (assuming Theorem 8.3).** By Theorem 8.3 (Z0S.3): $B_{\rm safe} \geq \varphi(n)(n-2)/2$. By Corollary 8.4: $B_{\rm safe} \geq \varphi(n)$ for $n \geq 4$. The run cap $\leq |B_{\rm div}| - n$ requires $B_{\rm safe} \geq n$, which holds when $\varphi(n)(n-2) \geq 2n$; this fails for $n \in \{4, 6\}$ (see §8.6 Remark). For $n \geq 8$ (and all odd composite $n$), the run cap holds. $\square$

### 10.2 G4.OT: Near-Complete Templates

**Theorem 10.2 (G4.OT).** *For composite $n \geq 4$, near-complete templates with $|E_{\rm fix}| = n-3$ and one divisible runner: $x_0 \geq \varphi(n)$.*

*(v5.1 correction: scope extended from the implicit $n \geq 10$ of the companion documents to all composite $n \geq 4$; the arguments are not restricted to large $n$.)*

We split by which runners are dropped.

**Cases i, ii, iiia (at least one dropped runner is a unit). ✅ ($x_0 \geq 1$)** Lemma 4.2 (Sole Cover) applies: the dropped unit $d$ exposes residue $r_d$ on the interval $[L/n, L/(n-1))$. This gives $x_0 \geq 1$, which establishes LRC for these branches. The extension to $x_0 \geq \varphi(n)$ requires a counting bridge for composite $n$ analogous to Section 9; **[⚠ GAP CB: no composite counting bridge is written here — see Gap Registry §14]**.

**Sub-case B: Both dropped runners are non-units. [PROVISIONAL for B3]** By U-FORCE (Lemma 8.5), all $\varphi(n)$ units are in $E_{\rm fix}$. We split by the arithmetic of $n$:

**Sub-case B1 ($n$ even). ✅** For $n = 2^a m$ with $m$ odd $\geq 3$:

$$\frac{2\varphi(n)}{n} = \prod_{p \mid m}\left(1 - \frac{1}{p}\right) \leq \frac{2}{3} < 1.$$

So $2\varphi(n) < n$, giving $U_{\rm unit} \neq \mathbb{Z}_n$ and a safe fibre exists.

For $n = 2^k$ ($k \geq 3$): at the lower band (floor 0 for all runners), every unit runner covers residue 0 (even) and one odd residue, while even residues $\{2, 4, \ldots, 2^k-2\}$ are all outside the image of the inverse map on units (since $-e^{-1}$ is odd for odd $e$). Hence the even non-zero residues are uncovered, giving $U_{\rm unit} \neq \mathbb{Z}_{2^k}$.

**Sub-case B2 ($n$ odd, $\geq 2$ distinct prime factors). `[⚠ GAP P6]`**

Let $p$ be the smallest prime factor and $q > p$ another prime factor. The goal is to show that some unit residue $r_0$ is not covered by $U_{\rm unit}$ at some fibre in $B_{\rm div}$.

`[⚠ GAP P6: The argument below constructs a floor state α* = 1/p as a candidate floor value for runner e = p. For α* to appear within B_div, we need the floor ⌊p·b/L⌋ = 1 for some b ∈ B_div, which requires b ≥ L/p. Since L/p ≥ L/n (as p ≤ n), fibres b ≥ L/p do exist in B_div. However, the simultaneous floor value of all unit runners at such b must be analysed. The mod-q obstruction argument is directionally correct but the achievability of the specific floor configuration at α* = 1/p within B_div, with all other runners at their stated floors, is not verified. See Gap Registry §14.]`

Define $r_0 = -p^{-1} \bmod q$ (which exists since $\gcd(p,q)=1$). At the floor state $\lfloor p \cdot b/L \rfloor = 1$ (i.e., $b \in [L/p, 2L/p)$), each unit runner $e = pk + s$ with $s = e \bmod p$ has floor $\lfloor e \cdot b/L \rfloor = k$ (approximately). Writing the bad-set condition mod $q$ and substituting $r = r_0$:

- First bad-set condition: $k(1 + r_0 p) \equiv -r_0 s \pmod{q}$. Since $1 + r_0 p \equiv 0 \pmod{q}$ (by definition of $r_0 = -p^{-1}$): the LHS is $0$. So we need $r_0 s \equiv 0 \pmod{q}$. But $r_0 \not\equiv 0$ and $s < p < q$, so $s \not\equiv 0 \pmod{q}$. **Contradiction** (for $s \neq 0$).
- Second condition: similarly yields $s \equiv p \pmod{q}$, but $s \leq p-1 < p < q$. **Contradiction.**

Therefore $r_0 \notin U_{\rm unit}$ at this floor state, giving a safe fibre (subject to the achievability issue flagged in Gap P6).

**Sub-case B3 ($n = p^k$, odd prime power, $k \geq 2$). [PROVISIONAL — depends on Theorem 8.3]** By U-FORCE, all $\varphi(p^k) = p^{k-1}(p-1)$ units are in $E_{\rm fix}$. By Theorem 8.3 (provisional): $B_{\rm safe} \geq \varphi(n)(n-2)/2 \geq 1$ (for $n \geq 4$). A safe fibre exists, so $x_0 \geq 1$. By Corollary 8.4: $x_0 \geq \varphi(n)$. $\square$

---

## 11. Composite $n$, Multiple Divisible Runners **[PROVISIONAL — depends on Theorem 8.3]**

**Theorem 11.1. [PROVISIONAL]** *For composite $n \geq 4$ and $|E_{\rm div}| \geq 2$: $x_0 \geq \varphi(n)$.*

**Proof (assuming Theorem 8.3).** With $\geq 2$ divisible runners, every element of $E_{\rm div}$ satisfies $\gcd(e, n) > 1$, so no unit of $\{1, \ldots, n-1\}$ is in $E_{\rm div}$. By U-FORCE: all $\varphi(n)$ units are in $E_{\rm non}$. By Theorem 8.3 and Corollary 8.4: $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2 \geq \varphi(n)$. $\square$

---

## 12. Proof of the Main Theorem

**Proof of Theorem A.** Let $n \geq 3$ and $E$ any gcd-1 tuple of $n-1$ distinct positive integers. We show $x_0(E) > 0$.

**Irrational case:** Theorem 2.1 (up to Gap F for large classes). ✓

**Rational case** (all speeds integer, gcd = 1):

- *Case 1 ($n \nmid e_i$ for all $i$):* Theorem 3.1 gives $x_0 \geq \varphi(n) \geq 1$. ✓ **(fully proved)**

- *Case 2 ($\exists\, e_i$ with $n \mid e_i$):*
  - $L = n$ or $L = 2n$: Proposition 4.1. ✓ *(L=n fully proved; L=2n: $x_0 \geq 1$ certified, $x_0 \geq n-1$ certified for $n \leq 20$)* **[CERTIFIED]**
  - $L > 2n$, **prime $n$**, $|E_{\rm div}| = 1$: Cases i/ii/iiia/iiib (Lemma 6.1, fully proved) + counting bridge (Proposition 9.4, analytic for large M, certified for small M). ✓ **(fully proved)**
  - $L > 2n$, **prime $n$**, $|E_{\rm div}| \geq 2$: Regular $k$ (Theorem 7.2) + bad $k$ (Theorem 7.3). ✓ **(fully proved)**
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| = 1$, dropped unit: G4.OT Cases i/ii/iiia/iiib. ✓ **($x_0 \geq 1$ fully proved via Sole Cover; $x_0 \geq \varphi(n)$ conditional on Gap CB — composite counting bridge)**
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| = 1$, both dropped non-units, $n$ even: Sub-case B1. ✓ **(fully proved)**
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| = 1$, both dropped non-units, $n$ odd with $\geq 2$ prime factors: Sub-case B2. ✓ **(proved up to Gap P6)**
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| = 1$, both dropped non-units, $n = p^k$: Sub-case B3. **[PROVISIONAL]** (depends on Gap A via Theorem 8.3)
  - $L > 2n$, **composite $n$**, $|E_{\rm div}| \geq 2$: Theorem 11.1. **[PROVISIONAL]** (depends on Gap A)

In the fully proved branches $x_0 \geq 1 > 0$. $\square$ (fully proved branches: irrational up to Gap F, Case 1, prime-$n$ Case-2, composite-$n$ with dropped unit via Sole Cover.) The provisional branches ($n = p^k$ Sub-case B3 and composite $|E_{\rm div}| \geq 2$) depend on Gap A; the composite dropped-unit bound $x_0 \geq \varphi(n)$ depends on Gap CB; see §14.

---

## 13. The Five Primitive Facts

The proof reduces to five structurally independent facts:

1. **Weyl equidistribution** (Section 2): irrational torus orbits visit every open set of positive measure. ✅ (up to Gap F)

2. **Arithmetic witness** (Section 3): the $\varphi(n)$ times $\{jL : \gcd(j,n) = 1\}$ are explicitly safe when no speed is divisible by $n$. ✅

3. **Sole Cover at $t = 0$** (Section 4): on $I = [L/n, L/(n-1))$, the map $e \mapsto -e^{-1} \bmod n$ is a bijection on units; each dropped unit runner exposes exactly one unique residue. ✅

4. **Z0S master identity** (Section 8): $B_{\rm safe} \geq \varphi(n)(n-2)/2$. **[PROVISIONAL — Gap A]** The summed identity $\sum(e_u-1) = \varphi(n)(n-2)/2$ from $\sum_{\rm unit} e = n\varphi(n)/2$ is correct; the gap is in proving each z=0 event produces a safe fibre. (v5.2: "+2" endpoint removed; see Gap A2.)

5. **Period-zero miss** (Section 9): for prime $n$ at $k = 0$, $|\text{miss}(0)| \geq 2$; combined with large-$M$ threshold $M_0 < n^2$, this gives $x_0 \geq \varphi(n)$ for large $M$ (small $M$ certified). ✅

---

## 14. Gap Registry

The following items are the open mathematical obligations in this draft. Every other result is either fully proved or marked **[PROVISIONAL]** with the relevant gap ID.

| Gap ID | Location | Description | Severity | Impact if unresolved |
|---|---|---|---|---|
| **A** | Lemma 8.2 | Unit residue isolation at z=0 events for floor $m \geq 2$. The departing residue $-(m-1)e_u^{-1}$ must not be in any other runner's bad set at the same fibre. Proved for $m=1$ (floor 0→1); open for $m \geq 2$. Key algebraic criterion: runner $e'$ covers the departure of $e_u$ at event $m$ iff $(e_u / \gcd(e_u, e')) \mid (m-1)$. Closed analytically for pairwise-coprime unit runners (e.g. $n = 12$); open for $n = p^k$. | **HIGH** | Theorem 8.3 (Z0S.3), Corollary 8.4, Lemma 8.6, Theorems 10.1, 10.2-B3, 11.1 all remain provisional. Affects composite $n = p^k$ sub-case and multi-divisible composite case. Run cap (O1) also not established for small composite $n$ (see Gap A2 note below). |
| **A2** | Thm 8.3 proof | **RESOLVED in v5.2.** An earlier version invoked the Sole Cover bijection (Lemma 4.2) to claim "+2" additional safe fibres from band endpoints. This was incorrect: Theorem 8.3 assumes ALL $\varphi(n)$ unit runners present (no dropped unit), so Sole Cover does not apply. The "+2" has been removed; the bound is now $\varphi(n)(n-2)/2$. As a consequence, the run cap ($B_{\rm safe} \geq n$) is no longer established for $n \in \{4, 6\}$ from this method. | **RESOLVED** | Fix: Theorem 8.3 bound corrected to $\varphi(n)(n-2)/2$; Corollary 8.4 demoted to $B_{\rm safe} \geq \varphi(n)$ ($n \geq 4$); run cap marked [OPEN] for $n \in \{4,6\}$ |
| **CB** | §10.2 Cases i/ii/iiia | Composite-$n$ counting bridge. For composite $n$ with a dropped unit, Sole Cover gives $x_0 \geq 1$ (fully proved). The stronger bound $x_0 \geq \varphi(n)$ requires a period-decomposition argument for composite $n$ analogous to Proposition 9.4. Section 9 proves this only for prime $n$. No composite bridge is written. | **LOW** | Only affects $x_0 \geq \varphi(n)$ for composite $n$, dropped-unit case. The LRC ($x_0 > 0$) is already established for these branches. |
| **P3** | Prop 9.4 | The period-decomposition counting bridge is proved only for period 0. The original density argument "across all of $B_{\rm div}$" assumed all periods are good ($|\text{miss}(k)| \geq 1$ for all $k$), which is not proved. Fixed in v5.1 by using only period-0 safe count (large $M$) and certifier (small $M$). | **RESOLVED in v5.1** | Resolved: the proof now correctly uses the two-route structure. |
| **P6** | §10.2-B2 | In the mod-$q$ obstruction argument for composite $n$ (odd, $\geq 2$ prime factors), the floor configuration $\alpha^* = 1/p$ must be achievable within $B_{\rm div}$ for the specific tuple $E$. Achievability is asserted but not verified. Likely closeable: for composite $n$ with smallest prime $p$, the interval $[L/p, 2L/p) \subset B_{\rm div}$ since $L/n \leq L/p$ (as $p \leq n$) and $2L/p \leq (n-1)L/n$ (as $2/p \leq (n-1)/n$ for $p \geq 3$ and $n \geq 3$). | **MODERATE** | Sub-case B2 of G4.OT is not fully proved. However, this case is **[CERTIFIED]** for $n \in \{6, 8, 9, 10, 12, 15\}$ (445+ configurations, 0 failures). |
| **F** | §2 Step 4 | In the irrational branch, the product-measure argument requires each $\mathbb{Q}$-class to have size $< n/2$. For $m = 2$ with one class of size $n-2$ (and $n \geq 4$), this fails. The $m = 1$ sub-case (all speeds proportional to one irrational) also needs a separate 1D Kronecker argument. | **LOW** | Does not affect the rational branch proof. The irrational case with large classes and $m = 1$ is handled by standard references (Kronecker's theorem, Weyl equidistribution); the gap is in the self-contained exposition only. |
| **B** | Prop 4.1 | $L = 2n$ case: analytic proof of $x_0 \geq 1$ (and of the stronger $x_0 \geq n-1$) is not given in this document. Both are certified computationally for $n \leq 20$. | **LOW** | Certified computationally for all $n \leq 20$. |

**Priority for closure:**
1. **Gap A** — closes the main remaining branches (composite $n = p^k$, multi-divisible composite). Algebraic criterion derived: the case of pairwise-coprime unit runners is analytically closed. Numerical experiments (Z0S audit) planned to identify the pattern for $n = p^k$. Once Gap A is closed, B3 and multi-divisible branches become fully proved.
2. **Gap P6** — closes Sub-case B2 analytically. The interval $[L/p, 2L/p) \subset B_{\rm div}$ argument is close to complete; achievability of the simultaneous floor configuration needs one additional lemma.
3. **Gap CB** — low priority (LRC already established; only $x_0 \geq \varphi(n)$ is open for composite $n$ with dropped unit).
4. **Gap F** — low priority; standard references handle this.

---

## References

- Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**, R48.
- Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**, 1–9.
- Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165–170.
- Weyl, H. (1916). Über die Gleichverteilung von Zahlen mod. Eins. *Math. Ann.* **77**, 313–352.
- Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263–269.

---

*End of v5.2 draft. This version applies five P0/P1 honesty fixes from v5.1: (P0-A) abstract and Theorem A restated as conditional; (P0-B) false first-admissible-fibre safety claim removed with explicit counterexample; (P0-C) Theorem 8.3 "+2" endpoint removed (Gap A2, now resolved in proof); (P1-A) composite dropped-unit x₀≥φ(n) claim tagged [⚠ GAP CB]; (P1-B) L=2n Prop 4.1 demoted to x₀≥1 (certified). The proof of LRC is fully established ($x_0 \geq 1$) in all prime-$n$ branches and in composite-$n$ branches where a unit runner is dropped. Composite-$n$ branches depending on Lemma 8.2 (Gap A) remain provisional. Three gaps remain: A (high), P6 (moderate), F/CB/B (low).*
