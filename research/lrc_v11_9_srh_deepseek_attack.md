# Conjecture 5.2-SR-H — analytical attack

## Setup (terse)

- $n \ge 3$ integer; $W = G \cup pA$ with $|W| = n - 1$ (LRC-shape, $\gcd(p, L_G) = 1$).
- $W_1 = \{w \in W : n \nmid w\}$, $W_2 = \{w/n : w \in W,\ n \mid w\}$. SR-failure: $|W_2| \ge 1$, so $|W_1| \le n - 2$.
- Standing hypothesis: $n \nmid w'$ for every $w' \in W_2$.
- Goal: prove $\exists$ Z₂-good $c \in \{1, \ldots, n-1\}$ (i.e., $w'c \not\equiv 0 \pmod{n}$ for all $w' \in W_2$) AND $k \in \{0, \ldots, n-1\}$ with $\|w(nk+c)/n^2\| \ge 1/n$ for all $w \in W_1$.

## Verified structural lemmas (34/34 empirical)

**L1 (coprime case).** $\gcd(w, n) = 1$, $c \in \{1, \ldots, n-1\}$:
$$\mathrm{bad}_k(w, c) = \{-\beta w^{-1},\ -(\beta + 1) w^{-1}\} \bmod n,\quad \beta := \lfloor wc/n \rfloor \bmod n.$$
Pair gap is $w^{-1}$ (independent of $c$).

**L2 (non-coprime).** $\gcd(w, n) = d > 1$, $n \nmid w$; $n = dn_1$, $w = dw_1$:
- If $w_1 c \bmod n \in R_d := \{0, 1, \ldots, n_1 - 1\} \cup \{n - n_1 + 1, \ldots, n-1\}$: $|\mathrm{bad}_k(w, c)| = d$, a coset of $\langle n_1 \rangle$.
- Else ($w_1 c \bmod n \in \{n_1, \ldots, n - n_1\}$): $\mathrm{bad}_k(w, c) = \emptyset$ (boundary vanishing).

## Empirical scope

Across all 75 L_residual cases at $n \in \{4, 5, 6, 7, 8\}$:
- SR closes 20 (SR hypothesis $n \nmid w$ holds → $t = s/n$ for any $s \in (\mathbb{Z}/n)^\times$).
- SR2 closes the remaining 55 on lattice $1/n^2$ (some $(k, c)$ exists).
- $0$ cases require lattice finer than $1/n^2$ (SR2 hypothesis $n^2 \nmid w$ holds for all w throughout the search range).

## Sub-result: c = 1, all W₁ small (PROVED this session)

**Theorem.** *If $W_1 \subseteq \{1, \ldots, n-1\}$ (all small, all coprime to $n$, all distinct), then at $c = 1$:*
$$\Big|\bigcup_{w \in W_1} \mathrm{bad}_k(w, 1)\Big| \le |W_1| + 1 \le n - 1.$$

*Proof.* For $w \in W_1$ with $w < n$: $\beta = \lfloor w \cdot 1 / n \rfloor = 0$. So $\mathrm{bad}_k(w, 1) = \{0, -w^{-1} \bmod n\}$. All pairs share $0$. Distinct $w$ have distinct $w^{-1} \bmod n$, so $-w^{-1}$ are distinct. Hence $|\bigcup| = 1 + |W_1|$.

Since $|W_1| \le n - 2$ (SR-failure), $|\bigcup| \le n - 1 < n$. $\square$

## What's STILL needed for full SR-H

The above sub-result handles the case where ALL $W_1$ elements are coprime to $n$ AND less than $n$. The remaining sub-cases:

**Sub-case (i): $W_1$ all coprime, some $w \ge n$.**
At $c = 1$, $\beta(w) = \lfloor w/n \rfloor > 0$, so bad-pair doesn't contain $0$. The "shared $0$" mechanism is partial.

Empirical observation: pairs for $w_1, w_2$ with $w_1 \equiv w_2 \pmod n$ and $\beta_2 = \beta_1 + 1$ share one element ($-(\beta_1 + 1) w^{-1}$). This gives a residue-class overlap mechanism.

**Sub-case (ii): $W_1$ contains non-coprime elements.**
L2 distinguishes "boundary vanishing" $c$ vs "coset" $c$. Need to pick $c$ that kills enough non-coprime contributions while keeping coprime contributions overlapping.

**Sub-case (iii): $W_1$ has 2n-symmetric pair (rare counterexample).**
At $c = n/2$ (if $n$ even and $c$ Z₂-good), Lemma A collapses the symmetric pair to a single bad-pair. Counterexample $n=4, W_1 = \{1, 7\}$.

## Strategic questions

1. **For sub-case (i):** Given $W_1$ all coprime, residue classes $r = w \bmod n$ partition $W_1$ into $\{W_1^{(r)} : r \in R\}$ with $|W_1^{(r)}| = m_r$. At $c = 1$, bad-k for residue $r$ is $\{-q \cdot r^{-1} : q \in Q_r \cup (Q_r + 1)\}$, where $Q_r = \{\lfloor w/n \rfloor : w \in W_1^{(r)}\}$. Is there a clean bound on $|\bigcup_r \mathrm{bad}_k(W_1^{(r)}, 1)|$ in terms of $|W_1|$ and $|R|$?

2. **For sub-case (ii):** Can we ALWAYS find a $c$ such that EVERY non-coprime $w \in W_1^{(>1)}$ has boundary vanishing? Or is this too strong? If too strong, what fraction can be killed?

3. **For sub-case (iii):** Is there a clean characterization of when $W_1$ has a 2n-symmetric pair? (Conjecture: only at small $n$.) If so, can we extend Lemma A to cover all such cases?

4. **General:** Is there a SINGLE $c$ (possibly non-unit) that works under all sub-cases? Or do we genuinely need a case-by-case argument?

5. **Alternative formulation:** Is SR-H equivalent to some well-known additive combinatorics statement (Erdős–Ginzburg–Ziv, Davenport constant, etc.)?

Please attempt to close one or more sub-cases analytically, OR identify the natural obstacle and recommend the most promising next step.
