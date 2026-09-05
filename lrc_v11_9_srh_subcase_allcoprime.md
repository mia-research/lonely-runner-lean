# Sub-case: $W_1$ all coprime to $n$

**Restriction**: All $w \in W_1$ satisfy $\gcd(w, n) = 1$. Note this includes:
- Every $n$ prime (no other gcd possible for $w \in W_1$).
- Many composite-$n$ inputs where the non-unit speeds are confined to $W_2$ or do not appear.

## Statement (Sub-Lemma SR-H/cop)

*Under the standing hypotheses, suppose every $w \in W_1$ has $\gcd(w, n) = 1$. Then there exist a Z₂-good $c \in \{1, \ldots, n-1\}$ and $k \in \{0, \ldots, n-1\}$ with $k \notin \mathrm{bad}_k(w, c)$ for all $w \in W_1$.*

## Attack idea

By L1, $\mathrm{bad}_k(w, c) = \{k_1(w, c), k_1(w, c) - w^{-1} \bmod n\}$ where $k_1 = -\beta(w, c) w^{-1}$ with $\beta(w, c) = \lfloor wc/n \rfloor \bmod n$.

**Key observation:** The MAP $c \mapsto k_1(w, c)$ for fixed coprime $w$ is "almost" linear in $c$:
- For $w, c < n$: $\beta(w, c) = \lfloor wc/n \rfloor \in \{0, 1, \ldots, w-1\}$.
- For $w \geq n$: $\beta$ takes more values mod $n$.

In particular, the bad pair $\{k_1, k_2\}$ moves through different positions as $c$ varies. The union over $c$ of all bad pairs covers (at most) the full cycle $\{j w^{-1} : j = 0, \ldots, n-1\}$.

## Refinement: Pair structure summed over c

For coprime $w$, define $T_w := \{\beta(w, c) : c \in \{1, \ldots, n-1\}\} \subseteq \mathbb{Z}/n$. The bad pair set is $\{(-\beta w^{-1}, -(\beta+1) w^{-1}) : \beta \in T_w\}$.

Adjacent pairs in the cycle. As $\beta$ varies, the pair sweeps the cycle.

## Specific structure: $w = 1$

For $w = 1$, $\beta(1, c) = \lfloor c/n \rfloor = 0$ for $c \in \{1, \ldots, n-1\}$. So bad pair always = $\{0, -1\} = \{0, n-1\}$, INDEPENDENT of $c$.

**Consequence:** If $1 \in W_1$ (or any $w \equiv 1 \pmod n$ with $w < n$), then $0$ and $n-1$ are bad for every $c$.

(Note: this corresponds to runners that are "essentially trivial" — period exactly $n$ in the appropriate scale.)

## Counterexample case dissected: $n=4, W_1 = \{1, 7\}$

$w = 1$: $\beta = 0$ always, bad pair $\{0, 3\}$.
$w = 7 \equiv 3 \pmod 4$. $w^{-1} \bmod 4 = 3$. Bad pair: $\{-\beta \cdot 3, -(\beta+1) \cdot 3\} \pmod 4$.

For $c = 1$: $wc = 7$, $\beta = 1$. Bad: $\{-3, -6 \bmod 4\} = \{1, 2\}$.
For $c = 2$: $wc = 14$, $\beta = 3$. Bad: $\{-9 \bmod 4, -12 \bmod 4\} = \{3, 0\}$.
For $c = 3$: $wc = 21$, $\beta = 5 \equiv 1 \pmod 4$. Bad: $\{-3, -6 \bmod 4\} = \{1, 2\}$.

Bad pair for $w = 1$ always $\{0, 3\}$. Bad pair for $w = 7$: $\{1, 2\}$ or $\{0, 3\}$.

For $c \in \{1, 3\}$ (units): $\{0, 3\} \cup \{1, 2\}$ = ALL of $\{0, 1, 2, 3\}$.
For $c = 2$ (non-unit, Z₂-good): $\{0, 3\} \cup \{0, 3\}$ = $\{0, 3\}$. Good $k \in \{1, 2\}$.

**Insight:** $c = 2$ "synchronizes" both $w$'s to the same bad pair, due to the symmetry $w_2 \equiv -w_1 \pmod{2n}$.

Generalization?

## General attack: alignment via non-unit c

When $|W_1| = n - 2$ and pairs cover everything for unit $c$, we may need non-unit $c$ to **align** $w$'s into pair-collisions.

**Hypothesis A:** For any LRC-shape SR-failure input with $|W_1| \le n - 2$ all coprime, some $c \in \{1, \ldots, n-1\}$ (Z₂-good) yields $|K(c)| \le |W_1| + 1$ OR achieves pair-collision sufficient to make $|K(c)| < n$.

Need: structural lemma showing such $c$ exists.

---

## Open question

Prove Hypothesis A, or find a counterexample to it within the LRC-shape SR-failure stratum.
