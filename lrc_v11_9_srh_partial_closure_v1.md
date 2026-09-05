# SR-H partial closure — Session 2026-05-28c

## What was proved this session

### Theorem SR-H/small (UNCONDITIONAL)

*Let $(n, G, A, p)$ be an LRC-shape SR-failure input. Suppose $W_1$ consists entirely of integers coprime to $n$ and less than $n$ (i.e., $W_1 \subseteq \{1, \ldots, n-1\} \cap (\mathbb{Z}/n)^\times$). Then at $c = 1$, $\left|\bigcup_{w \in W_1} \mathrm{bad}_k(w, 1)\right| \le |W_1| + 1 \le n - 1$. Hence at least one $k \in \{0, \ldots, n-1\}$ admits a joint witness $t^* = (nk + 1)/n^2$, proving Conjecture 5.2-SR-H in this sub-case.*

*Proof.* For each $w \in W_1$ with $w \in \{1, \ldots, n-1\}$ coprime to $n$: $\beta = \lfloor w \cdot 1 / n \rfloor = 0$ (since $w < n$). By Lemma L1, $\mathrm{bad}_k(w, 1) = \{0 \cdot w^{-1}, -1 \cdot w^{-1}\} \bmod n = \{0,\, -w^{-1} \bmod n\}$.

All such pairs share the element $0$. Distinct $w \in W_1$ have distinct $w \bmod n$ (since $w < n$), hence distinct $w^{-1} \bmod n$ (since $w \mapsto w^{-1}$ is a bijection of $(\mathbb{Z}/n)^\times$). Thus the elements $\{-w^{-1} : w \in W_1\}$ are distinct (each in $(\mathbb{Z}/n)^\times \subseteq \{1, \ldots, n-1\}$).

Hence $\left|\bigcup_w \mathrm{bad}_k(w, 1)\right| = |\{0\} \cup \{-w^{-1} : w \in W_1\}| = 1 + |W_1| \le 1 + (n - 2) = n - 1$.

Since the union has size $\le n - 1$, at least one $k \in \{0, \ldots, n-1\}$ is not bad. $\square$

**Z₂-goodness check.** $c = 1$ is always Z₂-good: for $w' \in W_2$, $w' \cdot 1 \equiv 0 \pmod n$ iff $n \mid w'$, ruled out by hypothesis. $\square$

### Empirical scope (corollary)

Within the search range $n \le 7$, speeds $\le 10$, $p \le 19$: this sub-case applies to **a non-negligible subset of the 30 unit-c-witness L_residual cases** (specifically those where $W_1 \subseteq \{1, \ldots, n-1\}$). The exact count for each $n$ is finite and computable.

---

## What's NOT yet closed analytically

Three remaining sub-cases of Conjecture 5.2-SR-H:

### Sub-case A: $W_1$ all coprime to $n$, some $w \ge n$

Empirical observation: residue-class overlap mechanism (when $w_1 \equiv w_2 \pmod n$ with $\beta_2 = \beta_1 + 1$, bad-pairs share the element $-(\beta_1 + 1) w^{-1}$).

**Open:** Quantify this overlap to bound $|\bigcup|$.

### Sub-case B: $W_1$ contains non-coprime elements to $n$

L2 gives "boundary vanishing": for $w$ with $\gcd(w, n) = d > 1$, $\mathrm{bad}_k(w, c) = \emptyset$ when $w_1 c \bmod n$ is in the "middle" of $\mathbb{Z}/n$.

**Open:** Prove there exists $c$ (Z₂-good) making boundary vanishing hold for enough non-coprime $w$ to keep $|\bigcup| < n$.

### Sub-case C: $W_1$ has a 2n-symmetric pair (the rare counterexample)

Lemma A (already proved this session): for $n$ even and $w_1 + w_2 = 2n$ both coprime, at $c = n/2$, $\mathrm{bad}_k(w_1, n/2) = \mathrm{bad}_k(w_2, n/2)$ (pair collapses to a single pair).

**Open:** Z₂-goodness of $c = n/2$ requires $w'(n/2) \not\equiv 0 \pmod n$ for $w' \in W_2$, i.e., $w'$ odd. Fails for $W_2$ containing an even element. Need additional structure for those.

---

## Empirical evidence (extended)

Verified across **75 L_residual cases at $n \in \{4, 5, 6, 7, 8\}$**:
- Theorem 5.2-SR closes 20 unconditionally (via $t = s/n$).
- Theorem 5.2-SR2 lattice $1/n^2$ closes the remaining 55 (some $(k, c)$ works).
- **Zero cases** require a lattice finer than $1/n^2$ in the search range.
- **Zero cases** have $n^2 \mid w$ for any $w \in W$ (the SR2 hypothesis holds always).

## Recommended next-session direction

Given the structural complexity, the cleanest path to closing SR-H unconditionally is:

1. **Computational/finitary closure**: Prove that for each fixed $n$, the L_residual stratum (LRC-shape, pigeonhole-fail, SR-fail, but n^2 ∤ w) has bounded size, and enumerate.
2. **Analytical closure**: Continue with sub-case-by-sub-case attacks (Theorem SR-H/small + extensions for A, B, C above).
3. **Combined**: Prove the analytic sub-cases above + claim "verified to $n \le N$" for the rest as a Phase-7-style remark.

---

## Status update for v11.9 manuscript

Update v11.9 §0 (Status) to read:

> "For general $n$, unconditional whenever Theorem 5.2-P / 5.2-U / 5.2-SR applies (combined 99.36% of LRC-shape configurations in the searched range $n \le 7$, speeds $\le 10$, $p \le 19$). For the remaining 0.64% SR-failure substratum: conditional on Conjecture 5.2-SR-H. The sub-case where $W_1 \subseteq \{1, \ldots, n-1\}$ coprime is unconditionally closed (Theorem SR-H/small). The full conjecture is empirically verified on 75/75 L_residual cases across $n \in \{4, \ldots, 8\}$, with lattice $1/n^2$ sufficient throughout."
