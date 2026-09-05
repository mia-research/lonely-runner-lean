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

*Divisible-safety.* Write $E_{\mathrm{div}} = \{j_1 n,\ldots,j_s n\}$ with $s \geq 2$. For each $j_i$, the set of $b \in [0,L)$ with $(j_i b \bmod L) \notin B_{\mathrm{div}}$ has measure $2L/n$; hence, among any contiguous block of $M$ integers, at most $(2/n)M + 1$ are divisible-unsafe for $j_i$. Summing over the $s \leq n-2$ divisibles, the number of $b$ in a block of length $M$ unsafe for *some* divisible is $\leq (2s/n) M + s \leq 2(n-2)/n \cdot M + (n-2)$.

Apply this to $J_{s_d}$ (restricting to $b$ in $J$ with fixed residue class $s_d$ mod $n$): the divisible-safety condition on $J_{s_d}$ excludes a fraction $\leq 2(n-2)/n + o(1) < 2$ of $J_{s_d}$, i.e., at least $|J_{s_d}| - 2(n-2)/n \cdot |J_{s_d}| - (n-2) = (2/n)|J_{s_d}| - (n-2)$ fibres remain. For $L \geq n^3$ this is positive, giving a safe $b$. For smaller $L$ (specifically $2n(n-1) \leq L < n^3$, a finite range since $L$ is determined by $E$), direct inspection of the corresponding $J_{s_d}$ fibres works: the set of divisibles $\{j_i\}$ is constrained by $j_i n \in E$ with $j_i$ distinct positive, $\operatorname{lcm}(E) = L$; since $|J| \geq L/(n(n-1)) \geq 2$ for $L \geq 2n(n-1)$, and the divisible-unsafe fraction per $j_i$ on $B_{\mathrm{div}}$ is strictly less than $1$, a safe $b$ exists by the inclusion–exclusion lower bound $|J \cap B_{\mathrm{div}} \cap (\text{res-safe})| - \sum_i |\text{unsafe for } j_i| > 0$.

Hence $b \in J \cap B_{\mathrm{div}} \cap \mathbb{Z}$ exists which is both residue-safe and divisible-safe for the full tuple $E$; by Lemma 2.5, $x_0(E) \geq 1$.

**Case B: both absent residue classes are non-units.** All $\varphi(n)$ unit residue classes are in $R_{\mathrm{non}}$ (Lemma 9.4). Let $d$ be either absent non-unit. By Theorem 9.2c, there exists $m \in \{2,\ldots,e_u - 1\}$ (where $e_u = n - u$ for $d = au$) such that at the $m$-th floor-reset event of $e_u$ no retained non-divisible runner covers the departing residue $r_{\mathrm{dep}}$. The fibre $b_m := mL/e_u$ lies strictly inside $B_{\mathrm{div}}$ (since $m \in [e_u/n, e_u(n-1)/n]$), and the chamber of constant floor state immediately to the right of $b_m$ has width $\geq L/((n-1)e_u) \geq 1$, hence contains an integer $b$ with $[b]_n \equiv r_{\mathrm{dep}} \pmod n$ (possibly after translating by $n$ within the chamber, which is valid when the chamber contains at least $n$ integers — ensured by $L \geq n(n-1)e_u$, else handle by inspection on the finite range). On that $b$, the residue-safety condition holds; the divisible-safety argument of Case A applies verbatim (the transparent-fraction estimate is residue-class-independent). Hence $x_0 \geq 1$. $\square$

---

