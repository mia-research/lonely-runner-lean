# Proof-section verification request

You are reviewing a self-contained excerpt from a proof of the Lonely Runner Conjecture (LRC). The excerpt covers the **sliding-window termination** argument (§6), which supplies the main lemma used in the prime-$n$ branch (§§5.3 and 7) and is structurally echoed in the composite-$n$ transparency lemma (§11.1).

## Your task
Perform a rigorous verification. For each lemma/proposition, assess:
1. **Correctness**: does the proof actually establish the stated claim?
2. **Gaps**: are there hidden hypotheses, missing cases, or unjustified steps?
3. **Dependencies**: does it silently rely on facts not supplied by the notation section?

Report in this format:
```
VERDICT: ACCEPT | ACCEPT-WITH-MINORS | REJECT
CONFIDENCE: 0.0–1.0
ISSUES:
 - (severity: low|med|high) ...
NOTES:
 - ...
```

## Notation setup (§§2.4–2.7)

```
# NOTATION EXTRACT
# (§§2.4–2.7 of lrc_proof_v11_1.md)
```

Key definitions used below:
- $E = E_{\mathrm{non}} \sqcup E_{\mathrm{div}}$ where $E_{\mathrm{non}} = \{e : n \nmid e\}$.
- For $e = nq_e + \rho_e$, $\rho_e \in \{1,\dots,n-1\}$.
- $B_{\mathrm{div}} := \{b \in \mathbb{Z} : L/n \le b \le (n-1)L/n\}$.
- $\mathrm{bad}(e,t,n) := \mathrm{Sol}(e,-t,n) \cup \mathrm{Sol}(e,-(t+1),n)$ where $\mathrm{Sol}(e,j,n) = \{r : er \equiv j \pmod n\}$.
- For unit $e$: $\mathrm{bad}(e,t,n) = \{-t\rho_e^{-1}, -(t+1)\rho_e^{-1}\} \bmod n$ (sliding window).
- $a_{\mathrm{low}}(e,t) := -t\rho_e^{-1}$ (OLD LOW, departing residue at reset $t \to t+1$).
- $a_{\mathrm{high}}(e,t) := -(t+1)\rho_e^{-1}$ (NEW HIGH, arriving residue).
- $b_m := mL/e$ is the $m$-th floor-reset fibre of $e$.
- Coincident reset of $e,f$ at $b$: $\lfloor eb/L\rfloor$ and $\lfloor fb/L\rfloor$ both transition at $b$; equivalently $e \mid fm$.
- A residue $r^*$ is *thin at* $b$ if covered by exactly one $e \in E_{\mathrm{non}}$ (its *sole cover*).

## Target sections (§§5.3, 6, 11.1)

### §5.3 The Absent-Unit Covering Lemma

**Lemma 5.2 (Absent-unit covering, prime $n$).** *Let $n$ be prime, $|E_{\mathrm{div}}| = 1$, and suppose some unit residue class $d \in \{1,\ldots,n-1\}$ is absent from $R_{\mathrm{non}}$. Then $x_0(E) \geq 1$.*

**Proof.** If $b_0 := L/n$ is not fully covered, some residue is already uncovered at $b_0$ and $x_0 \geq 1$. Otherwise $b_0$ is fully covered, and Lemma 5.1b gives a thin residue $r^*$ at $b_0$ with sole cover $e^*$. Proposition 6.1 produces a fibre $b^{**} \in B_{\mathrm{div}}$ with $b^{**} > b_0$ at which $r^*$ is uncovered. By Lemma 2.5, $x_0 \geq 1$. $\square$

(Lemma 5.1b: prime $n$, $b_0$ fully covered $\Rightarrow$ some residue has multiplicity exactly 1. Proof: total incidence $= 2|E_{\mathrm{non}}| \leq 2(n-2) < 2n$, so if all multiplicities $\geq 2$, incidence $\geq 2n$, contradiction.)

### §6 Sliding-Window Termination for Prime $n$

**§6.2 (Chain construction).** Let $r^*$ be thin at $b_0$ with sole cover $e^{(0)} := e^*$ and residue $\rho_0 := \rho_{e^*}$. Define stage-0 drop index $m^{(0)}$: smallest $m$ such that $r^* = a_{\mathrm{low}}(e^{(0)}, m-1)$. Then $b^{(0)} := m^{(0)}L/e^{(0)}$.

Inductive step. Given $e^{(k)}$ (unit), $\rho_k$, $m^{(k)}$, $b^{(k)}$, with $r^*$ sole cover on $(b^{(k-1)}, b^{(k)})$ and about to depart $e^{(k)}$ at $b^{(k)}$:

(a) **No valid transfer.** No $f \in E_{\mathrm{non}}$ has $\rho_f = n - \rho_k$ AND $e^{(k)} \mid f m^{(k)}$. Terminate: $b^{**} := b^{(k)}$.

(b) **Coverage transfer via coincident reset.** Some $e^{(k+1)}$ with $\rho_{k+1} = n - \rho_k$ satisfies $e^{(k)} \mid e^{(k+1)} m^{(k)}$. Set $j^{(k)} := e^{(k+1)} m^{(k)} / e^{(k)}$.

**Lemma 6.0 (Coverage-transfer identity).** Under (b), $a_{\mathrm{high}}(e^{(k+1)}, j^{(k)}) = r^*$.

**Proof.** $a_{\mathrm{high}}(e^{(k+1)}, j^{(k)}) = -(j^{(k)}+1)\rho_{k+1}^{-1}$. Since $\rho_{k+1} = n-\rho_k$, $\rho_{k+1}^{-1} \equiv -\rho_k^{-1} \pmod n$, so arriving residue $= (j^{(k)}+1)\rho_k^{-1}$. Now $j^{(k)} = e^{(k+1)} m^{(k)} / e^{(k)}$, so mod $n$:
$$j^{(k)} \equiv \rho_{k+1} m^{(k)} \rho_k^{-1} \equiv -\rho_k m^{(k)} \rho_k^{-1} \equiv -m^{(k)} \pmod n.$$
Hence arriving residue $\equiv (-m^{(k)}+1)\rho_k^{-1} = -(m^{(k)}-1)\rho_k^{-1} = r^*$ since $r^* = a_{\mathrm{low}}(e^{(k)}, m^{(k)}-1)$. $\square$

In case (b), $e^{(k+1)}$ newly covers $r^*$ as its arriving residue; by thinness, $e^{(k+1)}$ is the new sole cover. $r^*$ becomes the departing residue of $e^{(k+1)}$ at reset $j^{(k)}+2$. Set $m^{(k+1)} := j^{(k)}+2$.

**Proposition 6.1 (Sliding-Window Termination).** *Let $n$ be prime, $|E_{\mathrm{non}}| = n-2$, $d \notin R_{\mathrm{non}}$. If $b_0$ is fully covered, the chain terminates in case (a), exposing $r^*$ as uncovered at some $b^{**} \in B_{\mathrm{div}}$, $b^{**} > b_0$.*

**Proof.** $b^{(k+1)} = m^{(k+1)}L/e^{(k+1)} = (j^{(k)}+2)L/e^{(k+1)} = (j^{(k)}+2)/j^{(k)} \cdot b^{(k)} > b^{(k)}$ since $j^{(k)} \ge 1$. The strictly increasing sequence $b^{(0)} < b^{(1)} < \cdots$ is in finite $B_{\mathrm{div}} \subset (0,L)$, so terminates. Termination only in case (a), producing $b^{**}$. $\square$

### §11.1 Divisible-Runner Transparency (Composite)

**Lemma 11.A.** *Let $n \ge 4$, $e = kn \in E_{\mathrm{div}}$ with $k \in \{1,\ldots,n-2\}$. On $[L/n, L/(n-1))$, the floor state of $e$ is constant $= k$, and $\mathrm{bad}(kn,k,n) = \emptyset$ iff $n \nmid k$ and $n \nmid k+1$.*

**Proof.** $\gcd(kn,n) = n$, so $\mathrm{Sol}(kn,j,n) = \mathbb{Z}/n\mathbb{Z}$ if $n \mid j$, else $\emptyset$. At floor $k$ with $k \in \{1,\ldots,n-2\}$: neither $-k$ nor $-(k+1)$ is divisible by $n$, so $\mathrm{bad} = \emptyset$. $\square$

## Specific questions to address

1. **Lemma 6.0 algebra**: verify the identity $\rho_{k+1}^{-1} \equiv -\rho_k^{-1} \pmod n$ when $\rho_{k+1} = n - \rho_k$ and both are units. Does the proof's closing step $-(m^{(k)}-1)\rho_k^{-1} = r^*$ require that $r^*$ is *exactly* the OLD LOW (not just lies in the bad set) at stage $k$? Check the inductive maintenance.

2. **Thinness preservation**: step (b) asserts "by thinness, $e^{(k+1)}$ is the new sole cover of $r^*$." Is this actually forced, or only that $e^{(k+1)}$ becomes *a* cover? (If multiple runners simultaneously add $r^*$ to their bad sets at the same fibre, is the chain still well-defined?)

3. **Termination count**: the chain lives in $B_{\mathrm{div}}$. Is there a tighter a priori bound on chain length, or is "$b^{(k)}$ strictly increasing in a finite set" sufficient?

4. **Prime hypothesis usage**: where exactly does primality of $n$ enter? (Presumably at Lemma 5.1b incidence count and at inversion $\rho^{-1}$.) Does anything else break if $n$ is composite?

5. **Lemma 11.A scope**: the statement says transparency holds on $[L/n, L/(n-1))$. Is this interval always nonempty as an integer set when $|E_{\mathrm{div}}| \ge 2$?

End of excerpt. Report per format above.
