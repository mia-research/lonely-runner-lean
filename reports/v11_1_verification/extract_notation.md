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

