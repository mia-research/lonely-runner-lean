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
