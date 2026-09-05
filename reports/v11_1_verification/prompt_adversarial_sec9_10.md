# Adversarial proof review — §§9–10 of lrc_proof_v11_1.md

You are a hostile referee. Find every flaw. Do not grant benefit of the doubt, but do not invent problems.

## Setup (notation assumed)

LRC reduction: integer speeds $E = (e_1,\ldots,e_{n-1})$, $\gcd = 1$, $L = \operatorname{lcm}(E)$, $N = nL$. Partition $E = E_{\mathrm{non}} \sqcup E_{\mathrm{div}}$ (divisible = multiples of $n$). $R_{\mathrm{non}} = \{\rho_e : e \in E_{\mathrm{non}}\}$ where $e = nq_e + \rho_e$, $\rho_e \in \{1,\ldots,n-1\}$. $B_{\mathrm{div}} := [L/n,(n-1)L/n] \cap \mathbb{Z}$. $x_0(E) \ge 1$ iff some $k \in B_{\mathrm{div}}$ is both residue-safe (no $e \in E_{\mathrm{non}}$ puts $[k]_n$ in its bad set) and divisible-safe (for $e = jn$, $jk \bmod L \in B_{\mathrm{div}}$).

## Target sections

### §9.1 Floor-Reset

For unit $e_u$, $m$-th floor-reset at $b_m := mL/e_u$ where $\lfloor e_u b/L\rfloor$ goes $m-1 \to m$.

**Lemma 9.1.** #floor-reset events in $B_{\mathrm{div}}$ is $e_u - 1$.

### §9.2 Coverage criterion

**Lemma 9.2.** *Let $f = nq_f + u \in E_{\mathrm{non}}$ unit ($\gcd(u,n)=1$), $m$-th floor-reset of $f$ at $b_m = mL/f$. Departing residue $r_{\mathrm{dep}} := -(m-1)u^{-1} \bmod n$. For $e = nq_e + s \in E_{\mathrm{non}}$ ($s \in \{1,\ldots,n-1\}$), define $\sigma := em \bmod f \in \{0,\ldots,f-1\}$. Then $e$ covers $r_{\mathrm{dep}}$ at $b_m$ iff*

- *(CG1) $\sigma \equiv s \pmod n$, or*
- *(CG2) $\sigma \equiv s + u \pmod n$.*

Proof: $em = ft_e + \sigma$ so $t_e = \lfloor em/f\rfloor$. Coverage needs $s r_{\mathrm{dep}} \equiv -t_e$ or $-(t_e+1) \pmod n$. $r_{\mathrm{dep}} = -(m-1)u^{-1}$, $f \equiv u \pmod n$, so $u t_e \equiv sm - \sigma \pmod n$. Combining gives $\sigma \equiv s$ and $\sigma \equiv s+u$.

### §9.3 Dropped-Runner Targeting (key lemma)

**Theorem 9.2c.** *$n \ge 4$ composite, $d \in \{1,\ldots,n-1\}$ non-unit absent from $R_{\mathrm{non}}$. Write $d = au$ where every prime divisor of $a$ divides $n$ and $\gcd(u,n)=1$. Set $e_u := n-u$. Then $e_u$ unit, and $\exists m \in \{2,\ldots,e_u-1\}$ s.t. at $m$-th floor-reset of $e_u$ no runner covers the departing residue. Hence $x_0(E) \ge 1$.*

Proof sketch: $\gcd(e_u,n) = \gcd(n-u,n) = \gcd(u,n) = 1$, so $e_u$ unit. $u < d$ (non-unit $d \Rightarrow a \ge 2$), so $e_u = n-u > n-d$, $d + e_u > n$.

**Coprimality $\gcd(d, e_u) = 1$:** prime $r \mid d, e_u$. If $r \mid u$: $r \mid (n-u)+u = n$, contradicts $\gcd(u,n)=1$. Else $r \mid a \mid n$, $r \mid n-u$ gives $r \mid u$, contradiction.

**Choice of $m$:** $x \equiv -n d^{-1} \pmod{e_u}$, $x \in \{1,\ldots,e_u-2\}$. Ruling out $x \equiv 0$: $n \equiv 0 \bmod e_u$ impossible ($\gcd(n,e_u)=1$, $e_u>1$). Ruling out $x \equiv -1$: $n \equiv d \bmod e_u$, but $n \equiv u \bmod e_u$ and $0 < d - u < e_u$.

Set $m := x+1$. Then $d(m-1) \equiv -n \pmod{e_u}$.

**CG1 fails:** would need $e'(m-1) \equiv 0 \pmod{e_u}$; $m-1 = x$ is invertible mod $e_u$; so $e' \equiv 0 \bmod{e_u}$, impossible.

**CG2 has unique solution $d$:** $e(m-1) \equiv -n \pmod{e_u}$ with $e+e_u \ge n$, i.e., $e \ge u$. $m-1$ invertible $\Rightarrow$ unique residue class. $e$ confined to $[u, n-1]$, length $e_u$, contains one rep per residue mod $e_u$. Since $d \in [u,n-1]$, unique solution is $e = d$.

Since $d \notin E_{\mathrm{non}}$, no retained runner covers $r_{\mathrm{dep}}$. $\square$

### §10 Composite, $|E_{\mathrm{div}}|=1$, dropped unit

**Proposition 10.1.** *$n \ge 4$ composite, $|E_{\mathrm{div}}|=1$, unit $d \notin R_{\mathrm{non}}$. Then $x_0 \ge 1$.*

**Lemma 10.2 (Late-window).** $n \ge 4$ composite, unit $d \notin R_{\mathrm{non}}$, $s_d := d^{-1} - 1 \bmod n$. Define $J := [(n-2)L/(n-1), (n-1)L/n]$. Then $s_d$ uncovered by every $e \in E_{\mathrm{non}}$ at every $b \in J \cap \mathbb{Z}$.

Proof:
- **Floor on $J$:** $e(n-2)/(n-1) \le eb/L \le e(n-1)/n$ for $b \in J$. For $e \in \{1,\ldots,n-1\}$: $e(n-2)/(n-1) \ge e - 1$ (iff $e(n-2) \ge (e-1)(n-1)$ iff $n \ge e+1$, holds for $e \le n-1$). Upper: $e(n-1)/n < e$. So $\lfloor eb/L\rfloor = e-1$. For general $e = nq_e + \rho_e$: floor $\equiv \rho_e - 1 \pmod n$.
- **Unit runners ($\gcd(\rho_e,n)=1$):** at floor $\rho_e - 1 \pmod n$, $\mathrm{bad} = \{-(\rho_e-1)\rho_e^{-1}, -\rho_e \rho_e^{-1}\} = \{\rho_e^{-1}-1, -1\} = \{\rho_e^{-1}-1, n-1\}$. Map $\rho \mapsto \rho^{-1}-1$ injective on $U_n$. $d \notin R_{\mathrm{non}} \Rightarrow s_d = d^{-1}-1 \notin \{\rho^{-1}-1: \rho \in R_{\mathrm{non}}\cap U_n\}$. $s_d \ne n-1$ since $s_d = n-1 \Rightarrow d^{-1} \equiv 0$, impossible.
- **Non-unit runners ($g := \gcd(\rho_e,n) > 1$):** at floor $\rho_e - 1 \pmod n$, $\mathrm{Sol}(\rho_e,-(\rho_e-1),n) = \emptyset$ (since $g\mid\rho_e$, $g\nmid \rho_e-1$); $\mathrm{Sol}(\rho_e,-\rho_e,n) = H_g - 1$ where $H_g = (n/g)\mathbb{Z}/n\mathbb{Z}$. $s_d \in H_g - 1 \iff d^{-1} \in H_g$. But $d^{-1} \in U_n$, can't be nonzero multiple of $n/g > 1$. So $s_d \notin H_g - 1$.

**Proof of Prop 10.1:** $e_d = jn$ unique divisible ($j \ge 1$). Divisible-safety of $b \in B_{\mathrm{div}}$ is $(jb \bmod L) \in B_{\mathrm{div}}$. Seek $b \in J \cap B_{\mathrm{div}} \cap \mathbb{Z}$ both residue-safe and divisible-safe.

Residue-safety on $J$: Lemma 10.2 ⇒ every $b \in J \cap \mathbb{Z}$ with $[b]_n \equiv s_d$ is residue-safe. Counting: $|J|/n(n-1) \cdot (1/n)$ approximately; for $L \ge n^2(n-1)$, $|J_{s_d}| \ge \lfloor L/(n^2(n-1))\rfloor$.

Divisible-safety: $b \mapsto jb \bmod L$ has complement of $B_{\mathrm{div}}$ of measure $2L/n$. Unsafe fraction $\le 2/n + o(1)$. $|J_{s_d}|$ exceeds $2n$ for $L$ large enough, so safe $b$ exists.

## Specific adversarial questions

1. **Theorem 9.2c "unique solution" step.** The proof confines $e$ to $[u, n-1]$, calling this "an interval of length $e_u$ containing exactly one representative of each class modulo $e_u$." Is this correct when $e_u \ge n$? (It shouldn't be, since $u \ge 1$ and $n-1 \le e_u + u - 1 < 2e_u$ assuming $u \le e_u$.) Also: **are all $e \in E_{\mathrm{non}}$ of actual speed** confined to $[u, n-1]$? The variable $e$ in CG2 is ambiguous: does it mean the actual speed $nq_e + s$ or the residue $s$? The proof-sketch conflates them. Verify this carefully.

2. **Theorem 9.2c existence of $e = d$ in $E_{\mathrm{non}}$.** Theorem concludes "since $d \notin E_{\mathrm{non}}$, no retained runner covers $r_{\mathrm{dep}}$." But the proof established $e = d$ is the UNIQUE residue-class solution to CG2 in $[u, n-1]$. The actual retained speeds $e \in E_{\mathrm{non}}$ might have speed $e = nq_e + d$ for some $q_e \ge 1$ — i.e., a speed whose *residue class* is $d$. Doesn't the problem statement say $d \notin R_{\mathrm{non}}$? If so, no retained runner has residue $d$ mod $n$. But does the CG2 argument require excluding residues, or actual speeds? Clarify.

3. **Proposition 10.1 divisible-safety counting.** The proof uses "unsafe fraction $\le 2/n + o(1)$" and concludes $|J_{s_d}|$ exceeds $2n$ for "$L$ large enough." What is the precise threshold? Is the "for smaller $L$ apply Prop 5.1" escape hatch rigorous, or is there a range $2n < L < L_0$ where neither Prop 5.1 nor the counting argument covers the case?

4. **Lemma 10.2 non-unit floor.** For $e = nq_e + \rho_e$ with $\gcd(\rho_e, n) = g > 1$, the proof asserts the floor state at $b \in J$ is $\equiv \rho_e - 1 \pmod n$. Is this computation correct when $\rho_e \ge 2$? The bounds $e(n-2)/(n-1) \le eb/L \le e(n-1)/n$ give the floor's integer value, not its residue mod $n$. Verify.

5. **Lemma 10.2 interval non-emptiness.** $J$ has width $L/(n(n-1))$. When is $J \cap \mathbb{Z}$ nonempty? When $L \ge n(n-1)$. Is this ensured by the hypotheses of Prop 10.1?

Output format:
```
VERDICT: ACCEPT | ACCEPT-WITH-MINORS | REJECT
SCORE (0–100):
CONFIDENCE:
TOP-3 ISSUES: (lemma, flaw, severity)
OTHER NOTES:
```
