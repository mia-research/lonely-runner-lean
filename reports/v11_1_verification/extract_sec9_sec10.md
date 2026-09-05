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

