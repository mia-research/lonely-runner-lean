# Proof-section second-opinion request

You are providing a second opinion on §5 of a proof of the Lonely Runner Conjecture, specifically the **Absent-Unit Covering Lemma** (Lemma 5.2) and its base-fibre dependencies (Lemmas 5.1a, 5.1b, 5.2a). Do not trust the primary proof; check each step critically.

## Output format
```
VERDICT: ACCEPT | ACCEPT-WITH-MINORS | REJECT
CONFIDENCE: 0.0–1.0
ISSUES:
 - (severity) ...
NOTES:
 - ...
```

## Setup

LRC reduces (after irrational reduction and integer scaling with $\gcd(E)=1$) to: for $E = (e_1,\dots,e_{n-1})$ distinct positive integers with $\gcd(E)=1$, show $x_0(E) \ge 1$, where $x_0$ counts $k \in \{1,\dots,N-1\}$ (with $N = nL$, $L = \operatorname{lcm}(E)$) satisfying $(e_i k \bmod N) \in [L, (n-1)L]$ for all $i$.

Partition $E = E_{\mathrm{non}} \sqcup E_{\mathrm{div}}$ (non-divisible vs. divisible by $n$). For $e = nq_e + \rho_e \in E_{\mathrm{non}}$, $\rho_e \in \{1,\dots,n-1\}$; $R_{\mathrm{non}} := \{\rho_e : e \in E_{\mathrm{non}}\}$.

$B_{\mathrm{div}} := \{b \in \mathbb{Z} : L/n \le b \le (n-1)L/n\}$. For $b \in B_{\mathrm{div}}$ and $e$: $\mathrm{bad}(e,t,n) = \{r : er \equiv -t \text{ or } -(t+1) \pmod n\}$ where $t = \lfloor eb/L \rfloor$. Safe-point condition: $[b]_n \notin \mathrm{bad}(e, \lfloor eb/L\rfloor, n)$ for all $e \in E_{\mathrm{non}}$, plus divisible-safety.

Base fibre: $b_0 := L/n$ (integer, since $n|L$). At $b_0$: $\lfloor eb_0/L \rfloor = q_e$.

## Lemmas to check

**Lemma 5.1a (Exact base-fibre coverage).** *Let $d$ be a unit with $d \notin R_{\mathrm{non}}$ and $r_d := -d^{-1} \bmod n$. Then $e = nq+\rho \in E_{\mathrm{non}}$ covers $r_d$ at $b_0$ iff $\rho \equiv qd$ or $\rho \equiv (q+1)d \pmod n$.*

Proof: $e$ covers $r_d$ iff $\rho r_d + q \equiv 0$ or $\rho r_d + q+1 \equiv 0 \pmod n$. With $r_d = -d^{-1}$: multiply by $-d$ gives $\rho \equiv qd$ or $\rho \equiv (q+1)d$.

**Lemma 5.1b (Base-fibre thinness, prime $n$).** *Prime $n$, $|E_{\mathrm{div}}| \ge 1$, $b_0$ fully covered $\Rightarrow$ some residue has multiplicity exactly 1.*

Proof: prime $n \Rightarrow \gcd(\rho_e,n)=1$ so $|\mathrm{bad}(e,q_e,n)| = 2$. Incidence $I_0 = 2|E_{\mathrm{non}}| \le 2(n-2)$. Full coverage of $n$ residues with all multiplicities $\ge 2$ needs $I_0 \ge 2n$, contradiction.

**Lemma 5.2a (Floor-0 sub-case).** *Prime $n$, every $e \in E_{\mathrm{non}}$ has $e < n$ (so $q_e = 0$). Missing unit $d \notin R_{\mathrm{non}}$ $\Rightarrow r_d$ uncovered at $b_0$.*

Proof: at $b_0$ each $e$ has floor $0$: $\mathrm{bad}(e,0,n) = \{0, -\rho_e^{-1}\}$. $r_d = -d^{-1} \ne 0$ and $d \notin R_{\mathrm{non}}$ $\Rightarrow r_d \ne -\rho_e^{-1}$ for all $e$. So $r_d$ uncovered.

**Lemma 5.2 (Absent-unit covering, prime $n$).** *Prime $n$, $|E_{\mathrm{div}}|=1$, some unit $d \notin R_{\mathrm{non}}$ $\Rightarrow x_0(E) \ge 1$.*

Proof: if $b_0$ not fully covered, some residue uncovered there. Else $b_0$ fully covered; Lemma 5.1b gives a thin residue $r^*$ with sole cover $e^*$. The sliding-window termination argument (Prop 6.1, not shown here) produces some $b^{**} \in B_{\mathrm{div}}$, $b^{**} > b_0$, at which $r^*$ is uncovered. Hence $x_0 \ge 1$.

## Specific checks

1. **Lemma 5.1a algebra**: verify the multiplication step $-d \cdot (\rho r_d + c) \equiv 0 \pmod n$ really gives $\rho \equiv c d \pmod n$. (It should: $\rho r_d = \rho \cdot (-d^{-1})$, so multiplying by $-d$ gives $\rho$.)

2. **Lemma 5.1b incidence**: is the bound $|E_{\mathrm{non}}| \le n-2$ correct? The tuple has $n-1$ runners total; $|E_{\mathrm{div}}| \ge 1$ implies $|E_{\mathrm{non}}| \le n-2$. Yes.

3. **Lemma 5.2a zero-residue check**: is it legitimate that $r_d \ne 0$? $r_d = -d^{-1}$, $d$ is a unit, so $d^{-1}$ is nonzero, so $r_d \ne 0$. Yes.

4. **Lemma 5.2 dependency**: the proof punts to Prop 6.1 for the "sliding-window termination" step. That is reviewed separately. Modulo that, is the §5.2 argument complete?

5. **Are there any unhandled cases**? For instance, what if $b_0$ is fully covered AND no residue is thin at $b_0$? (Lemma 5.1b rules this out.) What if $|E_{\mathrm{div}}| = 0$ (Case 1, handled elsewhere)? What if no unit is absent (handled by Unit-Complete, §9)?

Report per format above. Focus on genuine mathematical gaps, not prose polish.
