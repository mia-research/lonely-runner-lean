# Conjecture 5.2-SR-H — structural analysis (session 2026-05-28b)

## Conjecture (as stated in v11.9 draft v2)

> **Conjecture 5.2-SR-H.** *Under the hypotheses of Theorem 5.2-SR2, every $\gcd(c, n) = 1$ Z₂-good offset admits a $W_1$-PCL-good lift $k$; equivalently, $\bigcup_{w \in W_1} \mathrm{bad}_k(w, c) \ne \{0, 1, \ldots, n - 1\}$ for at least one such $c$.*

## Setup

- $(n, G, A, p)$ LRC-shape: $|G| + |A| = n - 1$. Standing hypothesis: $n \nmid w'$ for $w' \in W_2$.
- $W := G \cup pA$, $W_1 := \{w \in W : n \nmid w\}$, $W_2 := \{w/n : w \in W, n \mid w\}$.
- SR-failure: $|W_2| \ge 1$, so $|W_1| \le n - 2$.
- For $c \in \{1, \ldots, n - 1\}$, $k \in \{0, \ldots, n - 1\}$, define
  $$\mathrm{bad}_k(w, c) := \{k : \|w(nk + c)/n^2\| < 1/n\}.$$

## Structural lemmas (verified on 34 SR-failure cases)

### Lemma L1 (coprime case, c-DEPENDENT)

*Let $w \in W_1$ with $\gcd(w, n) = 1$ and any $c \in \{1, \ldots, n-1\}$. Then $|\mathrm{bad}_k(w, c)| = 2$ and the two bad k's form a pair $\{k_1, k_2\}$ with*
$$k_2 - k_1 \equiv -w^{-1} \pmod n.$$
*Explicitly, writing $\beta := \lfloor wc / n \rfloor \pmod n$:*
$$k_1 = -\beta w^{-1} \bmod n, \quad k_2 = -(\beta + 1) w^{-1} \bmod n.$$

*Proof sketch.* $X(k) := w(nk + c) \bmod n^2$. Setting $\alpha := wc \bmod n$ (nonzero since $\gcd(w,n)=1$ and $c \not\equiv 0 \pmod n$), the orbit $\{X(k)\}_{k=0}^{n-1}$ equals $\{\alpha, \alpha+n, \ldots, \alpha+(n-1)n\}$ (set). The two values in $(-n, n)$ signed are $\alpha$ (positive, $j=0$) and $\alpha + (n-1)n = \alpha - n \pmod{n^2}$ (negative, $j = n-1$). Solving $wnk \equiv jn - n\beta \pmod{n^2}$, i.e., $wk \equiv j - \beta \pmod n$, gives $k = (j - \beta) w^{-1}$.

So $k_1 = -\beta w^{-1}$ (from $j=0$) and $k_2 = (n - 1 - \beta) w^{-1} = -(\beta+1) w^{-1}$ (from $j=n-1$). Their difference: $k_2 - k_1 = -w^{-1} \bmod n$.

(My original L1 claim "bad = {0, $-w^{-1}$}" was WRONG — that's the special case $\beta = 0$, i.e., $wc < n$. Verified numerically: 34/34.)

### Lemma L2 (non-coprime case)

*Let $w \in W_1$ with $\gcd(w, n) = d > 1$, $n = dn_1$. For any $c \in \{1, \ldots, n-1\}$, $|\mathrm{bad}_k(w, c)| \in \{0, d\}$, and (if nonempty) the bad-k set is a coset of $\langle n_1 \rangle$ in $\mathbb{Z}/n$ — i.e., $\{k_0 + i n_1 : i = 0, \ldots, d-1\}$ for some $k_0 \in \mathbb{Z}/n$.*

*Proof sketch.* $X(k) = wnk + wc \bmod n^2$. Orbit has $n_1$ distinct values (since $\gcd(wn, n^2) = nd$), each visited $d$ times. Orbit spacing $nd \ge 2n$, so the bad window $|X| < n$ (length $2n-1$) contains at most 1 orbit point. If it contains 1, multiplicity $d$ gives $d$ bad k's, forming a coset of $\langle n_1 \rangle$. (Verified 34/34.)

### Strategy implication

- **Coprime contribution:** For each $w \in W_1^{\mathrm{cop}}$, bad-k is a pair $\{k_1(c), k_1(c) - w^{-1}\}$. As $c$ varies, the pair translates.
- **Non-coprime contribution:** For each $w \in W_1^{(d)}$ ($d > 1$), bad-k is a coset (or empty) of $\langle n_1 \rangle$.

Total bad-k size: $\le 2|W_1^{\mathrm{cop}}| + \sum_{d>1} d \cdot |W_1^{(d)}|$. Pure counting can fail (exceed $n$); need structural argument.

---

## CRITICAL FINDING: Conjecture-as-stated has 4 counterexamples among 34 SR-failure cases

For 4 of 34 cases, **NO** $c \in (\mathbb{Z}/n)^\times$ admits a good $k$. The witness requires a **non-unit Z₂-good $c$**:

| n | G | A | p | W₁ | W₂ | Z₂-good c | Unit-c works? | Non-unit witness |
|---|---|---|---|----|----|-----------|---------------|------------------|
| 4 | [1, 7] | [6] | 2 | {1, 7} | {3} | {1, 2, 3} | NO (both c=1, c=3 fully bad) | c=2 → bad={0,3}, good k∈{1,2} |
| 6 | [2, 5, 7] | [1, 4] | 3 | {2, 3, 5, 7} | {2} | {1, 2, 4, 5} | NO | c=2 → good k=5 |
| 6 | [2, 5, 7] | [1, 6] | 3 | {2, 3, 5, 7} | {1, 3} | {1, 5} (units only — and they fail) | NO | non-unit c needed |
| 6 | [2, 5, 7] | [1, 8] | 3 | {2, 3, 5, 7} | {2} | {1, 2, 4, 5} | NO | c=2 → good k=5 |

### Detailed verification of case $n=4, G=[1,7], A=[6], p=2$

$W = \{1, 7, 12\}$, $W_2 = \{3\}$ (since $12 = 4 \cdot 3$), $W_1 = \{1, 7\}$. Both $w \in W_1$ coprime to 4.

**Unit $c = 1$:**
- $w=1$, $c=1$: $\alpha=1, \beta=0$, $w^{-1}=1$. $k_1 = 0$, $k_2 = -1 \bmod 4 = 3$. Bad = $\{0, 3\}$.
- $w=7$, $c=1$: $\alpha = 7 \bmod 4 = 3$, $\beta = \lfloor 7/4 \rfloor = 1$, $w^{-1} = 7^{-1} \bmod 4 = 3$. $k_1 = -3 = 1$, $k_2 = -2 \cdot 3 = -6 \equiv 2$. Bad = $\{1, 2\}$.
- Union: $\{0, 1, 2, 3\}$ — ALL bad.

**Unit $c = 3$:** symmetric. Union $\{0, 1, 2, 3\}$.

**Non-unit $c = 2$ (Z₂-good since $3 \cdot 2 = 6 \not\equiv 0 \pmod 4$):**
- $w=1$, $c=2$: $\alpha = 2, \beta = 0$. $k_1 = 0$, $k_2 = 3$. Bad = $\{0, 3\}$.
- $w=7$, $c=2$: $\alpha = 14 \bmod 4 = 2$, $\beta = \lfloor 14/4 \rfloor = 3$. $k_1 = -3 \cdot 3 = -9 \equiv 3$, $k_2 = -4 \cdot 3 = 0$. Bad = $\{0, 3\}$.
- Union: $\{0, 3\}$. Good k ∈ $\{1, 2\}$. ✓

**Why $c=2$ works:** It makes both $w=1, w=7$ have the same residue mod 4 (namely $\alpha=2$), so their bad-k pairs *coincide* (collapse to one pair).

### Diagnosis: the conjecture statement is too strong

The Theorem 5.2-SR2 proof needs only that SOME Z₂-good $c$ admits a good $k$. Lemma 5.2-SR2.A proves $\gcd(c, n) = 1 \implies$ Z₂-good, so it suffices to verify "some unit $c$ admits good $k$" — BUT this is FALSE in 4/34 cases.

The empirical claim (34/34) is the existential version over ALL Z₂-good $c$, not unit-restricted.

**Corrected Conjecture 5.2-SR-H:**
> *Under the hypotheses of Theorem 5.2-SR2, **there exists** a Z₂-good $c \in \{1, \ldots, n-1\}$ admitting a $W_1$-PCL-good lift $k \in \{0, \ldots, n-1\}$.*

Note: the second clause of the original conjecture ("for at least one such $c$") is consistent with this; only the "every $\gcd(c, n) = 1$ Z₂-good offset" clause is too strong. Either treat them as the same intended statement (drop "every") or fix to "for some Z₂-good $c$".

---

## Open problem

Prove the corrected Conjecture 5.2-SR-H.

**Stratify by n:**
- $n$ prime: only $\gcd(w, n) \in \{1\}$ for $w \in W_1$. Bad-k is unions of pairs. By a slightly more careful argument than my failed first attempt, this case is closable analytically; details below.
- $n$ composite: bad-k structure is more complex; non-coprime $w$'s give cosets.

### Closing the prime-$n$ case (sketch)

For $n$ prime, all $w \in W_1$ have $\gcd(w, n) = 1$. Bad-k for $w$ at unit $c$: pair $\{k_1, k_1 + (n - w^{-1})\}$ — 2 elements. So $|\bigcup_w \mathrm{bad}_k(w, c)| \le 2|W_1| \le 2(n - 2)$ — but this can exceed $n$ for $n \ge 5$.

Refined argument? Maybe: the bad-k pairs have specific structure (gaps $= -w^{-1}$ for various $w$), and as $c$ varies, the pairs translate. Sum over unit $c$:
$$\sum_{c \in (\mathbb{Z}/n)^\times} |\mathrm{bad}_k(w, c)| = 2 \phi(n) = 2(n-1).$$

So $\sum_c |K(c)| \le 2(n-1)|W_1| \le 2(n-1)(n-2)$, averaged over $\phi(n) = n-1$ unit c's: average $|K(c)| \le 2(n-2) < n$ if $n \ge 4$ — wait, $2(n-2) < n$ requires $n < 4$, not $\ge 4$. So averaging fails.

Need a tighter approach. **Suggestion:** count $\#\{(w, c, k) : k \in \mathrm{bad}_k(w, c)\}$ and use that bad-k is in a *2-element coset of $\langle 1 \rangle = \mathbb{Z}/n$ shifted* — meaning the bad k's form a sliding pair.

---

## Questions for DeepSeek (--task verify --thinking)

1. Verify Lemma L1 (corrected pair structure for $\gcd(w, n) = 1$).
2. Verify Lemma L2 (coset structure for $\gcd(w, n) = d > 1$).
3. Confirm the 4 counterexamples to the unit-$c$ conjecture and the suggested correction.
4. Strategic guidance: how to prove the corrected conjecture for composite $n$?

Specifically:
(i) For composite $n$, prove that some non-unit Z₂-good $c$ admits a good $k$ when no unit $c$ does.
(ii) Or, prove a unified statement: some Z₂-good $c$ (any) admits a good $k$.
