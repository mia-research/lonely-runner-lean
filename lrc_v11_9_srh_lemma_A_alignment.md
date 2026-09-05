# Lemma A: Coprime-Pair Alignment at $c = n/2$

## Statement

**Lemma A (Alignment of symmetric coprime pairs).**
*Let $n \ge 4$ be **even**, and let $w_a, w_b$ be two integers with $\gcd(w_a, n) = \gcd(w_b, n) = 1$ and $w_a + w_b \equiv 0 \pmod{2n}$. Then at $c = n/2$:*
$$\mathrm{bad}_k(w_a, n/2) = \mathrm{bad}_k(w_b, n/2).$$

## Proof

Setting $c := n/2$. Both $w_a$ and $w_b$ are odd (coprime to even $n$ forces odd).

**Compute $\alpha, \beta, w^{-1}$ for each:**

For $w$ odd, $wc = w(n/2)$, so:
- $\alpha := wc \bmod n = (n/2) \cdot (w \bmod 2) = n/2$.
- $\beta := \lfloor wc/n \rfloor \bmod n = \lfloor w/2 \rfloor \bmod n = (w-1)/2 \bmod n$ (since $w$ is odd).

So $\beta_a = (w_a - 1)/2 \bmod n$ and $\beta_b = (w_b - 1)/2 \bmod n$.

**Use $w_a + w_b = 2n$:** $w_b = 2n - w_a$, so
$$\beta_b = (2n - w_a - 1)/2 = n - 1 - (w_a - 1)/2 = n - 1 - \beta_a \pmod n.$$

**Compute $w_b^{-1}$:** $w_b \equiv -w_a \pmod n$, so $w_b^{-1} \equiv -w_a^{-1} \pmod n$.

**Apply Lemma L1 (corrected pair formula):**
$$\mathrm{bad}_k(w, c) = \{-\beta w^{-1}, \; -(\beta + 1) w^{-1}\} \pmod n.$$

For $w_b$:
$$k_1^{(b)} = -\beta_b \cdot w_b^{-1} = -(n - 1 - \beta_a)(-w_a^{-1}) = (n - 1 - \beta_a) w_a^{-1} \equiv -(1 + \beta_a) w_a^{-1} \equiv k_2^{(a)} \pmod n.$$

$$k_2^{(b)} = -(\beta_b + 1) \cdot w_b^{-1} = -(n - \beta_a)(-w_a^{-1}) = (n - \beta_a) w_a^{-1} \equiv -\beta_a w_a^{-1} \equiv k_1^{(a)} \pmod n.$$

So $\{k_1^{(b)}, k_2^{(b)}\} = \{k_2^{(a)}, k_1^{(a)}\}$ = $\mathrm{bad}_k(w_a, n/2)$. $\square$

## Numerical verification

**Case $n = 4$, $w_a = 1$, $w_b = 7$**: $w_a + w_b = 8 = 2n$. ✓ At $c = 2$:
- $\beta_a = 0$, $w_a^{-1} = 1$. Bad pair = $\{0, -1 \bmod 4\} = \{0, 3\}$.
- $\beta_b = 3$, $w_b^{-1} = 3$. Bad pair = $\{-9 \bmod 4, -12 \bmod 4\} = \{3, 0\}$.

**Identical.** ✓

**Case $n = 6$, $w_a = 5$, $w_b = 7$**: $w_a + w_b = 12 = 2n$. ✓ At $c = 3$:
- $\beta_a = 2$, $w_a^{-1} = 5$. Bad pair = $\{-10 \bmod 6, -15 \bmod 6\} = \{2, 3\}$.
- $\beta_b = 3$, $w_b^{-1} = 1$. Bad pair = $\{-3 \bmod 6, -4 \bmod 6\} = \{3, 2\}$.

**Identical.** ✓

## Application to counterexample case 1 (n=4, $G=[1,7]$)

$W_1 = \{1, 7\}$, both coprime, $1 + 7 = 2n$.

At $c = n/2 = 2$ (Z₂-good since $W_2 = \{3\}$ and $3 \cdot 2 = 6 \not\equiv 0 \pmod 4$):

By Lemma A, $\mathrm{bad}_k(1, 2) = \mathrm{bad}_k(7, 2) = \{0, 3\}$.

Union: $\{0, 3\}$, $|K(2)| = 2 < 4 = n$. Good $k \in \{1, 2\}$. ✓

## Generalization to all "symmetric coprime pair + $c = n/2$ Z₂-good" cases

**Theorem A1 (provisional).** *Let $n \ge 4$ even, LRC-shape SR-failure input with $|W_1^{(>1)}| = 0$ (all of $W_1$ coprime to $n$) and $c^* := n/2$ Z₂-good. If $W_1$ can be paired up as $W_1 = \{w_{a_1}, w_{b_1}, \ldots, w_{a_m}, w_{b_m}\}$ with $w_{a_i} + w_{b_i} = 2n$ for each $i$, then at $c = n/2$, $|K(n/2)| \le |W_1|/2 \cdot 2 = |W_1|$.*

If $|W_1| < n$: $K(n/2)$ does not cover everything. Since SR-failure requires $|W_1| \le n - 2 < n$, this gives a witness.

**Verifies counterexample 1.** Open: does this work more generally?

## Limitations

- **Even $n$ only**: Lemma A uses $c = n/2$. For odd $n$, no such $c$.
- **Z₂-good restriction**: $c = n/2$ needs $w' (n/2) \not\equiv 0 \pmod n$ for $w' \in W_2$, i.e., $w'$ odd. If $W_2$ contains an even element, this fails. (Counterexamples 2, 4 at $n = 6$: $W_2 = \{2\}, \{4\}$, both even, so $c = 3 = n/2$ NOT Z₂-good.)
- **Non-coprime $W_1$ elements**: Lemma A applies only to coprime pairs. Non-coprime $W_1$ elements need separate treatment (Lemma L2 / boundary vanishing).
- **Asymmetric $W_1^{\text{cop}}$**: If $W_1$'s coprime part has no symmetric pair at $2n$, Lemma A doesn't apply.

## Status

- Lemma A: proved.
- Application to counterexample 1: complete (with Theorem A1 sketch).
- Counterexamples 2, 3, 4: counterexample 3 closeable via Lemma A at $c = 3$. Counterexamples 2 and 4 need additional structure (boundary vanishing of non-coprime $w$'s at non-unit $c \ne n/2$).
- General theorem: still open.
