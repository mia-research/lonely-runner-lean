# Candidate proof attempt: Conjecture 5.2-SR-H (CORRECTED, EXISTENTIAL form)

## Statement

> **Conjecture 5.2-SR-H (corrected, existential).**
> Let $(n, G, A, p)$ be an LRC-shape input (i.e., $|G| + |A| = n - 1$) with standing hypothesis $n \nmid w'$ for all $w' \in W_2$ (the lifted W₂ part). Define $W_1 := \{w \in G \cup pA : n \nmid w\}$. Assume $|W_2| \ge 1$ (SR-failure). Then *there exists* a Z₂-good $c \in \{1, \ldots, n-1\}$ and $k \in \{0, \ldots, n-1\}$ with $\|w(nk + c)/n^2\| \ge 1/n$ for all $w \in W_1$.

## Structural lemmas (proved, empirically verified 34/34 cases)

### L1 (coprime case).

*Let $\gcd(w, n) = 1$, $c \in \{1, \ldots, n-1\}$, $c \not\equiv 0 \pmod n$. Then $\mathrm{bad}_k(w, c) = \{k_1, k_2\}$ where $k_2 - k_1 \equiv -w^{-1} \pmod n$, depending on $c$ via $\beta := \lfloor wc/n \rfloor \pmod n$:*
$$k_1 = -\beta w^{-1} \bmod n, \quad k_2 = -(\beta+1) w^{-1} \bmod n.$$

### L2 (non-coprime case).

*Let $\gcd(w, n) = d > 1$, $n \nmid w$, $n = d n_1$, $w = d w_1$ with $\gcd(w_1, n_1) = 1$. For any $c \in \{1, \ldots, n-1\}$:*
- *If $w_1 c \bmod n \in R_d := \{0, 1, \ldots, n_1 - 1\} \cup \{n - n_1 + 1, \ldots, n - 1\}$ (size $2n_1 - 1$), bad-k is a coset of $\langle n_1 \rangle$ of size $d$.*
- *If $w_1 c \bmod n \in \{n_1, n_1 + 1, \ldots, n - n_1\}$ (size $n - 2n_1 + 1$), bad-k is empty.*

### Auxiliary: edge consequence of L2.

*For $w$ with $\gcd(w, n) = d > 1$: bad-k coset is empty iff $|wc \bmod^* nd| \ge n$.*

In particular, **boundary case**: $wc \bmod nd = n_1 \cdot d = n$ gives $|wc| = n$, NOT $< n$, hence bad-k empty.

## Strategy

**Step 1.** Decompose $W_1 = W_1^{\mathrm{cop}} \cup W_1^{(>1)}$ (coprime vs. non-coprime to $n$).

**Step 2.** For each $w \in W_1^{(>1)}$, find the set of $c$ for which bad-k is empty:
$$C_{\mathrm{kill}}(w) := \{c \in \{1, \ldots, n-1\} : w_1 c \bmod n \in \{n_1, \ldots, n - n_1\}\}.$$

**Step 3.** Choose $c \in \bigcap_{w \in W_1^{(>1)}} C_{\mathrm{kill}}(w)$ (if nonempty) AND $c$ Z₂-good. This kills all non-coprime contributions.

**Step 4.** Then $K(c) = \bigcup_{w \in W_1^{\mathrm{cop}}} \{k_1(w, c), k_2(w, c)\}$, with $|K(c)| \le 2|W_1^{\mathrm{cop}}|$.

**Step 5.** Find $c$ in this intersection such that $|K(c)| < n$.

## Issues with this strategy

(I1) The intersection $\bigcap_{w \in W_1^{(>1)}} C_{\mathrm{kill}}(w)$ might be EMPTY for some inputs, in which case some non-coprime $w$ MUST contribute bad-k.

(I2) Even if non-empty, the bound $|K(c)| \le 2|W_1^{\mathrm{cop}}| \le 2(n-2)$ can still exceed $n$.

(I3) Z₂-good restriction further narrows admissible $c$.

## Refinement attempt

### Attempt A: Counting + averaging over all Z₂-good $c$

Let $\mathcal{C} := \{c \in \{1, \ldots, n-1\} : c \text{ is Z₂-good}\}$.

$$\sum_{c \in \mathcal{C}} |K(c)| \le \sum_{c \in \mathcal{C}} \sum_{w \in W_1} |\mathrm{bad}_k(w, c)| = \sum_{w \in W_1} \sum_{c \in \mathcal{C}} |\mathrm{bad}_k(w, c)|.$$

For coprime $w$: $|\mathrm{bad}_k(w, c)| = 2$ always (for $c \in \{1, \ldots, n-1\}$, $\gcd(c, n)$ arbitrary). Sum $= 2|\mathcal{C}|$.

For non-coprime $w$ ($\gcd = d > 1$): $|\mathrm{bad}_k(w, c)| \in \{0, d\}$. The contribution per $w$ is $d \cdot |\{c \in \mathcal{C} : w_1 c \bmod n \in R_d \setminus \{0\}\}|$.

Without restriction to Z₂-good, summing $c \in \{1, \ldots, n-1\}$:
$$\sum_{c=1}^{n-1} |\mathrm{bad}_k(w, c)| = d \cdot |\{c \in \{1, \ldots, n-1\} : w_1 c \bmod n \in R_d \setminus \{0\}\}|.$$

For $\gcd(w_1, n) = 1$: $w_1 c \bmod n$ permutes residues, so the count is $|R_d \setminus \{0\}| = 2(n_1 - 1)$ if $0 \notin R_d$... actually $0 \in R_d$ but $w_1 c \equiv 0 \pmod n$ requires $n | c$, impossible. So count = $|R_d| = 2n_1 - 1$ over $c \in \{0, 1, ..., n-1\}$, less $c = 0$: $2n_1 - 1$ if $0 \in R_d$, $2n_1 - 1 - 1 = 2n_1 - 2$ if not. We have $0 \in R_d$, so count = $|R_d| - 1 = 2n_1 - 2$.

Actually wait the issue is more subtle. For $c$ s.t. $w_1 c \equiv 0 \pmod n$: $c \equiv 0 \pmod n$ (since $\gcd(w_1, n) = 1$). But $c \in \{1, ..., n-1\}$, so no such $c$. Hence $0 \notin \{w_1 c \bmod n : c \in \{1, ..., n-1\}\}$.

Therefore over $c \in \{1, ..., n-1\}$: $w_1 c \bmod n \in \{1, ..., n-1\}$ permuting. Count of $c$ with $w_1 c \in R_d \setminus \{0\}$ = $|R_d \cap \{1, ..., n-1\}| = 2n_1 - 2$.

So $\sum_{c=1}^{n-1} |\mathrm{bad}_k(w, c)| = d \cdot (2n_1 - 2) = 2(n - d)$ for $w$ with $\gcd(w, n) = d$ and $\gcd(w_1, n) = 1$.

For $\gcd(w_1, n) > 1$: complicated.

**Total over all $c \in \{1, \ldots, n-1\}$ (not Z₂-restricted yet):**
$$\sum_{c=1}^{n-1} |K(c)| \le 2(n-1) |W_1^{\mathrm{cop}}| + \sum_{d > 1, w} 2(n - d).$$

Avg over $n - 1$ values of $c$:
$$\overline{|K(c)|} \le 2 |W_1^{\mathrm{cop}}| + \frac{2 \sum_{d > 1, w} (n - d)}{n - 1}.$$

For $|K(c)| < n$ at some $c$: need average $< n$. Crude bound: $|W_1^{\mathrm{cop}}| \le n - 2$, so $2|W_1^{\mathrm{cop}}| \le 2n - 4$.

This averaging is too weak. We need:
(i) Restrict to Z₂-good $c$ (reduces $\mathcal{C}$ but the bound becomes more favorable per-$c$).
(ii) Use overlapping of bad pairs to get a sub-additive bound.

### Attempt B: Use overlap structure

Observation: for fixed coprime $w$, bad-k is a pair with gap $-w^{-1}$. As $c$ varies, the pair "rotates" through the cycle $\{j w^{-1} \bmod n : j = 0, 1, ..., n-1\}$ at consecutive positions.

For two coprime $w_1, w_2 \in W_1^{\mathrm{cop}}$ with gaps $g_1 = -w_1^{-1}, g_2 = -w_2^{-1}$: their bad pairs may overlap or not depending on $c$.

If $g_1 = g_2$: pairs are translates by the same amount, may overlap exactly (if same $\beta$) or not.

If $g_1 \neq g_2$: different rotational structures.

Hmm, this needs more thought.

### Attempt C: Direct argument for $|W_1| \le n - 2$

**Claim.** For any LRC-shape input with $|W_1| \le n - 2$ in SR-failure regime, there exists a Z₂-good $c$ and $k \in \{0, \ldots, n-1\}$ with $k \notin \mathrm{bad}_k(w, c)$ for all $w \in W_1$.

**Proof attempt.**

(STEP 1) For each $w \in W_1$, define
$$D_w := |\bigcup_{c \in \mathcal{C}} \mathrm{bad}_k(w, c)| \subseteq \{0, \ldots, n-1\}.$$

For coprime $w$: bad-k pair has gap $w^{-1}$. As $c$ varies, the pair takes various positions in the rotational orbit. Total elements visited = at most $n$ (but usually fewer if $|\mathcal{C}|$ is small).

(STEP 2) Use $|W_1| \le n - 2$ to argue $|\bigcup_w D_w| < n$.

[INCOMPLETE — needs structural argument]

---

## Strategic questions for DeepSeek (--task math --thinking)

1. **For prime $n$:** Given $|W_1| \le n - 2$ all coprime, prove there is a c (unit OR non-unit) admitting good $k$. Pure counting fails (sum of bad pairs could exceed $n$). What's the structural fix?

2. **For composite $n$:** How to combine the non-coprime bad-coset "killing" mechanism with the coprime bad-pair count?

3. **Counterexample insight:** In the 4 unit-c counterexample cases, the witness is non-unit Z₂-good $c$. What property of these cases forces non-unit $c$? Can we characterize them?

4. **Alternative approach:** Instead of choosing $c$ first, choose $k$ first. For each $k$, characterize which $c$'s are good. Find $c$ that is good for at least one $k$ AND Z₂-good.

5. **Connection to PCL / GPCL:** The classical PCL gives a witness when all of $W$ is coprime to $n$. Here we have $W_1$ possibly containing non-coprime elements (when $n$ composite). What's the right generalization?
