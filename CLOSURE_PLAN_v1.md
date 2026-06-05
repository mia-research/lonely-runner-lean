# Plan: Unconditional all-$n$ closure of Conjecture 5.2-H

**Date:** 2026-05-27 (Phase 8 planning)
**Status:** Plan only. Each step has a 1-2 paragraph proof sketch. Verification
of analytical steps is required before drafting full proofs.

## Goal

Close Conjecture 5.2-H **unconditionally for all $n$**, removing the
"conditional on Conjecture 5.2-H" caveat from Theorems 10.1, 11.1, 12.1 in
v11.7.

## Strategy

Two complementary paths, both pursued in parallel.

- **Path 1** (primary): Strengthen Lemma 7b.1 — derive a lower bound on
  $|\mathcal{B}|$ that holds in the **overlapping-band regime**, using
  Cauchy-Schwarz + the autocorrelation structure of LRC good cell sets.
- **Path 2** (backup): Bound the residual list. Show that pigeonhole failure
  is only possible when $L_G$ lies in a bounded range depending on $(n, p,
  v_{\max})$, then verify each $(L_G, L_A, p, n)$ tuple by direct enumeration.

Path 1 closes the "generic" residual (most of the 88); Path 2 cleans up the
small-$L_G$ residual where Path 1's autocorrelation bound is weakest.

## Path 1 — Strengthen Lemma 7b.1 (Cauchy-Schwarz + autocorrelation)

### Step 1.1: Cauchy-Schwarz framework for $|\mathcal{B}|$

**Setup.** Define
$$X_\beta \;:=\; \bigl|\{\alpha_0 \in \mathcal{I}_G : \beta \in B_{\alpha_0}\}\bigr|, \qquad \beta \in [0, n L_A).$$
Then $|\mathcal{B}| = |\{\beta : X_\beta \ge 1\}|$, and by Cauchy-Schwarz,
$$|\mathcal{B}| \;\ge\; \frac{\bigl(\sum_\beta X_\beta\bigr)^2}{\sum_\beta X_\beta^2}.$$

**Proof sketch.** $X_\beta = \sum_\alpha \mathbf{1}_\alpha(\beta)$, so
$\sum_\beta X_\beta = \sum_\alpha |B_\alpha|$. Each band $B_\alpha$ has size
$r := \lceil L_A p / L_G \rceil$ (the projection of an interval of width
$L_A p$ in $m''$-space at resolution $L_G$, with at most one extra cell
from boundary). Hence $\sum_\beta X_\beta \ge |\mathcal{I}_G| \cdot r$
(equality when no band ever projects to $r+1$ cells; we use the lower
estimate throughout). For the second moment,
$\sum_\beta X_\beta^2 = \sum_{(\alpha, \alpha')} |B_\alpha \cap B_{\alpha'}|$,
which decomposes as diagonal ($|\mathcal{I}_G| \cdot r$) plus off-diagonal
pairwise intersections (the autocorrelation sum). Cauchy-Schwarz then gives
the displayed inequality. The bound is sharp when bands are pairwise disjoint
(reduces to Lemma 7b.1).

### Step 1.2: Autocorrelation bound for two bands

**Claim.** For any two distinct $\alpha_0, \alpha_0' \in [0, n L_G)$ with
shift difference $d := |\alpha_0 p - \alpha_0' p| \bmod n L_G$,
$$|B_{\alpha_0} \cap B_{\alpha_0'}| \;\le\; \max\!\left(\left\lceil \frac{L_A p - d \cdot L_A}{L_G}\right\rceil,\; 0\right).$$

**Proof sketch.** In $m''$-space, the bands are intervals of width $L_A p$ at
starts $s_\alpha = \alpha p L_A$ and $s_{\alpha'} = \alpha' p L_A$, with
$|s_\alpha - s_{\alpha'}| = d L_A$ in absolute units. The intervals overlap
in $m''$-space iff $d L_A < L_A p$, i.e., $d < p$, with overlap width
$L_A p - d L_A$. Projecting to $\beta$-space at resolution $L_G$, the overlap
has at most $\lceil (L_A p - d L_A)/L_G \rceil$ cells, vanishing for $d \ge p$.

### Step 1.3: Autocorrelation sum for LRC good cell sets

**Claim.** For the LRC good cell set $\mathcal{I}_G$,
$$\sum_{\alpha_0, \alpha_0' \in \mathcal{I}_G,\, \alpha_0 \ne \alpha_0'} \mathbf{1}_{d(\alpha_0, \alpha_0') < p}
\;\le\; |\mathcal{I}_G| \cdot 2 (p-1) \cdot \frac{|\mathcal{I}_G|}{n L_G},$$
where $d(\alpha_0, \alpha_0') := |(\alpha_0 - \alpha_0') p \bmod n L_G|$.

**Proof sketch.** For each $\alpha_0 \in \mathcal{I}_G$, the count of
$\alpha_0' \in \mathcal{I}_G$ with $d(\alpha_0, \alpha_0') < p$ is exactly
the count of $\alpha_0' \in \mathcal{I}_G$ such that $\alpha_0' \equiv \alpha_0
+ k p^{-1} \pmod{n L_G}$ for some $k \in \{-(p-1), \ldots, -1, 1, \ldots, p-1\}$
(using $\gcd(p, n L_G) = \gcd(p, n)$ — when this is 1, $p$ is invertible mod
$n L_G$). For each of the $2(p-1)$ values of $k$, the residue class
$\alpha_0 + k p^{-1} \bmod n L_G$ intersects $\mathcal{I}_G$ in an expected
$|\mathcal{I}_G|/(n L_G)$ elements (uniform-distribution assumption — to be
verified for $\mathcal{I}_G$ as an LRC good cell set). Summing over $\alpha_0$
gives the displayed bound; rigorous proof requires showing $\mathcal{I}_G$ is
"sufficiently uniform" in residue classes mod $n L_G$, which can be argued
via Weyl-type equidistribution applied to the good cell indicator function.

**Caveat.** The uniform-distribution assumption is heuristic. A rigorous
version requires either (i) bounding the discrepancy of $\mathcal{I}_G$
mod $p^{-1}$ shifts, or (ii) showing the bound in expectation suffices for
a probabilistic argument. The empirical evidence from Phase 6c (correlation
ratio ≈ 1 for L_residual) supports the uniform-distribution model in practice.

### Step 1.4: Combined bound on $\sum X^2$

**Claim.** Under the autocorrelation bound of Step 1.3,
$$\sum_\beta X_\beta^2 \;\le\; |\mathcal{I}_G| \cdot r + \frac{|\mathcal{I}_G|^2}{n L_G} \cdot 2(p-1) \cdot r.$$

**Proof sketch.** Diagonal term $\sum_\alpha |B_\alpha|^2 \le |\mathcal{I}_G| \cdot r^2$ (each band has at most $r$ cells). But the $r^2$ over-counts; actually $\sum_\beta X_\beta^2 \ge \sum_\beta X_\beta$ trivially (sum of integers $\ge$ sum of $\mathbf{1}$). The off-diagonal contribution is bounded by Step 1.2 applied to each pair: each pair contributes $\le r$, and there are at most $|\mathcal{I}_G|^2 / (n L_G) \cdot 2(p-1)$ such pairs (Step 1.3). So
$\sum_\beta X_\beta^2 \le |\mathcal{I}_G| \cdot r + |\mathcal{I}_G|^2 \cdot 2(p-1) \cdot r / (n L_G)$.

### Step 1.5: Lower bound on $|\mathcal{B}|$

**Theorem (Path 1 main).** For LRC-shape inputs with $\gcd(p, n L_G) = 1$,
$$|\mathcal{B}| \;\ge\; \frac{(|\mathcal{I}_G| r)^2}{|\mathcal{I}_G| r + 2(p-1) r |\mathcal{I}_G|^2 / (n L_G)} \;=\; \frac{|\mathcal{I}_G| r}{1 + 2(p-1) |\mathcal{I}_G|/(n L_G)}.$$

**Proof sketch.** Substitute Steps 1.1, 1.4 (assuming Step 1.3's
autocorrelation bound). Simplifying the denominator: $1 + 2(p-1) |\mathcal{I}_G|/(n L_G) = 1 + 2(p-1) \mu(G)$.

For $\mu(G) \le 1/(2(p-1))$ (sparse good cells): denominator $\le 2$, so $|\mathcal{B}| \ge |\mathcal{I}_G| r / 2$.
For $\mu(G) \ge 1/(2(p-1))$ (dense good cells): denominator $\le 1 + 2(p-1) \cdot 1 = 2p - 1$, so $|\mathcal{B}| \ge |\mathcal{I}_G| r / (2p - 1)$.

Either way: $|\mathcal{B}| \ge |\mathcal{I}_G| r / (2p)$. Concretely,
$$|\mathcal{B}| \;\ge\; \frac{|\mathcal{I}_G| L_A p}{2p \cdot L_G} \;=\; \frac{|\mathcal{I}_G| L_A}{2 L_G}.$$
Using Lemma 4.1 lower bound on $|\mathcal{I}_G|$:
$|\mathcal{B}| \ge L_A / ((n-1) v_{\max})$.

### Step 1.6: Pigeonhole under Step 1.5

**Theorem (Path 1 pigeonhole).** For LRC-shape inputs with $\gcd(p, n L_G) = 1$
and the autocorrelation bound (Step 1.3) holding,
$$\frac{1}{v_{\max}} + \frac{2}{u_{\max}} \;>\; n(n-1) \;\implies\; \text{pigeonhole holds}.$$

**Proof sketch.** Substitute Step 1.5 + Lemma 4.1:
$|\mathcal{B}| + |\mathcal{I}_A| \ge L_A/((n-1) v_{\max}) + 2 L_A/((n-1) u_{\max}) = L_A/(n-1) \cdot (1/v_{\max} + 2/u_{\max})$.
This exceeds $n L_A$ iff $1/v_{\max} + 2/u_{\max} > n(n-1)$.

### Step 1.7: Comparison with Theorem 5.2-U

Theorem 5.2-U (disjoint bands): $p/v_{\max} + 1/u_{\max} > n(n-1)/2$.
Path 1 (with overlap, Cauchy-Schwarz factor 2): $1/v_{\max} + 2/u_{\max} > n(n-1)$.

Path 1 is WEAKER than Theorem 5.2-U by a factor of 2 in the pigeonhole
condition. This is the cost of allowing overlapping bands. For Hard Case
$p < n L_G$: Theorem 5.2-U applies when $p \ge v_{\max} n(n-1)/2$;
Path 1 applies when $v_{\max} \le 2/(n(n-1))$ — vacuous unless $v_{\max} = 1$
(degenerate).

**Conclusion**: Path 1 with $\sum X^2$ trivial Cauchy-Schwarz is INSUFFICIENT.
A finer estimate is required.

### Step 1.8: Refinement — better autocorrelation bound

The bound in Step 1.3 is loose by a factor of $p$ (the $2(p-1)$ factor). A
sharper bound for **LRC-shape** good cells: most pairs $(\alpha_0, \alpha_0')$
with shift difference $< p$ have shift difference EXACTLY $\le p / k$ for
$k \in \{1, 2, ..., p-1\}$ — only $O(1)$ pairs per $\alpha_0$ achieve each
specific shift difference (by uniformity of $\mathcal{I}_G$ mod $L_G$).

**Refined claim**: For LRC-shape with $\gcd(p, n) = 1$,
$$\sum_{d < p,\, d \ne 0} (\text{pairs with shift diff } d) \;\le\; O(p \log p) \cdot |\mathcal{I}_G|^2 / (n L_G).$$

Substituting: $|\mathcal{B}| \ge |\mathcal{I}_G| r / (1 + O(\log p) \mu(G))$.

This is still bounded by $O(1)$ factor improvement; doesn't close the
$v_{\max} n(n-1)/2$ gap.

**Honest assessment**: Cauchy-Schwarz alone cannot close the conjecture. A
more sophisticated tool (Plancherel/Weyl-type identity, or structural use of
LRC good cell topology) is needed.

## Path 2 — Bound the residual list

### Step 2.1: $L_A$ bound from LRC-shape

**Lemma.** For LRC-shape DI: $L_A = u_1 \le (n-1) v_{\max} / p$.
For LRC-shape ModDI: $L_A = \text{lcm}(u_j)$ with each $u_j \le (n-1) v_{\max}/p$ for at least one slow position; by DI constraint analogue, $L_A \le ((n-1) v_{\max}/p)^{k_A}$.

**Proof sketch.** Direct from the DI/ModDI definition: $V = p u_1$ (DI) or $V = p u_j$ (ModDI) for the "promoted" fast speed, with $V \in ((n-1) v_{\min}, (n-1) v_{\max}]$. Hence $u_1 = V/p \le (n-1) v_{\max} / p$. For ModDI, $L_A = \text{lcm}$ of $k_A$ fast speeds, each bounded similarly.

### Step 2.2: $L_G$ upper bound for residual

**Lemma.** If pigeonhole fails for an LRC-shape input, then
$$L_G \;\le\; \frac{n(n-1) v_{\max} L_A}{2} \;\le\; \frac{n(n-1)^2 v_{\max}^2}{2 p}.$$

**Proof sketch.** Combining Lemma 4.1 bounds ($|\mathcal{I}_G| \ge 2 L_G/((n-1) v_{\max})$, $|\mathcal{I}_A| \ge 2 L_A/((n-1) u_{\max})$) with the trivial $|\mathcal{B}| \ge |\mathcal{I}_G|$ and the pigeonhole-failure assumption $|\mathcal{B}| + |\mathcal{I}_A| \le n L_A$:
$2 L_G/((n-1) v_{\max}) + 2 L_A/((n-1) u_{\max}) \le n L_A$
$\Rightarrow 2 L_G/((n-1) v_{\max}) \le n L_A$ (since the second term is non-negative)
$\Rightarrow L_G \le n(n-1) v_{\max} L_A / 2$.
Using Step 2.1's $L_A \le (n-1) v_{\max}/p$: $L_G \le n(n-1)^2 v_{\max}^2 / (2p)$.

### Step 2.3: Combined bound on $(L_G, v_{\max})$ for residual

**Theorem.** A pigeonhole-failure LRC-shape input has
$$v_{\max} \;\le\; L_G \;\le\; \frac{n(n-1)^2 v_{\max}^2}{2p}.$$
In particular, $L_G / v_{\max}^2 \le n(n-1)^2 / (2p)$, which for fixed $(n, p)$
is bounded.

**Proof sketch.** The lower bound $L_G \ge v_{\max}$ holds since $v_{\max} \mid L_G$
(LCM of integers includes the max). The upper bound is Step 2.2. Combined:
$L_G \le n(n-1)^2 v_{\max}^2 / (2p)$, which implies $v_{\max} \ge \sqrt{2p L_G / (n(n-1)^2)}$ —
a lower bound on $v_{\max}$ in terms of $L_G$.

### Step 2.4: Chebyshev lower bound on $L_G$ from gcd structure

**Lemma.** For LRC-shape DI with $k_G = n - 2$ slow speeds and $\gcd$ of
slow speeds equal to some divisor $g$, the lcm satisfies
$L_G \ge g \cdot \text{lcm}(\{v_i/g\})$ where $\{v_i/g\}$ are coprime.

By Chebyshev's theorem $\text{lcm}(1, ..., m) \ge e^{(0.92) m}$ for $m \ge 7$;
for $\{v_i/g\}$ a set of $n-2$ coprime positive integers all $\ge 1$, the lcm
is at least the smallest such set's lcm. Worst case: $\{v_i/g\} = \{1, 2, ..., n-2\}$
giving $L_G/g \ge e^{0.92(n-2)}$. So
$$L_G \;\ge\; g \cdot e^{0.92 (n-2)}.$$

### Step 2.5: Residual is empty for large $n$ (DI case)

**Theorem (Path 2 main, DI version).** For LRC-shape DI inputs with bounded
$v_{\max}$, pigeonhole holds unconditionally for $n \ge N_0(p, v_{\max})$
where $N_0$ is determined by
$$e^{0.92(N_0 - 2)} \cdot \min(v_i) \;>\; \frac{N_0 (N_0 - 1)^2 v_{\max}^2}{2 p}.$$

**Proof sketch.** Substituting Chebyshev (Step 2.4) into Step 2.2's upper
bound: if $L_G \ge g \cdot e^{0.92(n-2)}$ exceeds $n(n-1)^2 v_{\max}^2 / (2p)$,
pigeonhole holds. The crossover $N_0$ is determined by setting these equal;
explicitly for $g = 1, v_{\max} = 10, p = 2$: $e^{0.92(N_0 - 2)} > 50 N_0^3$,
giving $N_0 \approx 25$ (numerically).

**Concretely**: For $v_{\max} \le 10, p \ge 2$: pigeonhole holds for $n \ge 25$.

### Step 2.6: Direct enumeration for small $n$

**Theorem (Path 2 closure for small $n$).** For each pair $(n, p)$ with
$3 \le n \le 25$ and $p \in \{2, 3, 5, 7\}$ (the relevant residual primes),
the residual LRC-shape inputs form a FINITE list. Each can be directly
verified using a harness that enumerates $(G_{\text{speeds}}, A_{\text{speeds}})$
combinations and checks $N_{\text{joint}} \ge 1$.

**Proof sketch.** For each $(n, p)$, $L_G$ is bounded by $n(n-1)^2 v_{\max}^2 / (2p)$
where $v_{\max} \le L_G$ (so $v_{\max} \le \sqrt{n(n-1)^2 L_G / (2p)}$).
Hence $L_G \le n(n-1)^2 L_G / (2p) \cdot 1$ … this is a circular but bounded
constraint. In practice, $L_G$ is bounded by a constant (depending only on
$n, p$) once $v_{\max}$ is constrained. The set of $(v_i, u_j, p)$ tuples with
$L_G \le M(n, p)$ is finite.

Concretely, the residual list for $n \le 10$ is the 88 cases enumerated in
Phase 7c; for $11 \le n \le 25$, the analogous enumeration is a finite
extension (computational effort: $\sim 10^6 - 10^7$ tuples per $(n, p)$,
feasible in hours).

### Step 2.7: Combined Path 2 closure

For each $n$:
- If $n \ge N_0(p, v_{\max})$ (where $v_{\max}$ is determined by input):
  pigeonhole holds by Step 2.5.
- Otherwise: input is in the finite residual list (Step 2.6), verified
  directly.

Hence Conjecture 5.2-H holds for all $n$.

## Synthesis — combined Path 1 + Path 2

### When Path 1 applies (large $|\mathcal{I}_G|$)

Theorem 5.2-U (disjoint bands, Phase 7b) covers $p \ge v_{\max} n(n-1)/2$.
Path 1 with overlap (Step 1.6) is WEAKER and doesn't extend significantly.

### When Path 2 applies (small $|\mathcal{I}_G|$)

For LRC-shape with $v_{\max}$ bounded and $n$ large: $L_G \ge e^{0.92(n-2)}$
(Step 2.4) eventually exceeds the residual upper bound. Pigeonhole holds for
$n \ge N_0(v_{\max})$.

For $n < N_0$ or $v_{\max}$ unbounded: residual list is finite (Step 2.6);
verify each.

### Gap analysis

The "gap" where neither path applies cleanly is the regime:
- $p < v_{\max} n(n-1)/2$ (Theorem 5.2-U doesn't apply)
- $v_{\max}$ large but specific arithmetic structure forces $L_G$ small
  (Step 2.5 doesn't bite)

This gap can in principle be enumerated case-by-case. The 88 currently
known residuals all fall in this gap; verifying them empirically suffices
for $n \le 10$.

For $n \ge 11$: extend Phase 7's mining to larger $n$. By Chebyshev (Step 2.4)
+ a careful $v_{\max}$ analysis, eventually $L_G$ exceeds all relevant
thresholds, making residual empty.

**Estimated $N_0$**: For $v_{\max} \le 20$ and $p \le 19$: $N_0 \approx 30$.

## Risk assessment

| Step | Risk | Mitigation |
|---|---|---|
| Step 1.3 (autocorrelation uniformity) | HIGH — heuristic; requires equidistribution-type result | Derive rigorous bound via Weyl/discrepancy theory or accept as conjecture; Path 2 doesn't require this |
| Step 1.6 (Path 1 main) | MEDIUM — bound is weaker than Theorem 5.2-U, may not close anything new | Path 1 mainly useful for theoretical clarity; Path 2 is the workhorse |
| Step 2.4 (Chebyshev for $L_G$) | LOW — standard PNT-type result | Standard, well-known |
| Step 2.5 (residual empty for $n \ge N_0$) | **CRITICAL GAP** (DeepSeek-flagged) — requires $v_{\max}$ to be bounded by some function of input | Path 2 alone doesn't close for unbounded $v_{\max}$; see Step 2.8 below |
| Step 2.6 (enumeration for $n \le 25$) | LOW — computational, finite | $10^7$ tuples per $(n, p)$ is feasible |
| Step 2.8 (unbounded $v_{\max}$) | OPEN — needs refinement | See proposed approach below |

### Step 2.8: Refined Path 2 for unbounded $v_{\max}$ (CRITICAL — closes the gap)

**Issue (DeepSeek-flagged)**: Step 2.5 assumes $v_{\max}$ is bounded. For LRC-shape
DI inputs with arbitrarily large $v_{\max}$, the Chebyshev bound on $L_G$ no
longer dominates.

**Key observation**: For LRC-shape DI ($k_A = 1$), the good cell measure
$\mu(A) = (n-2)/n$ EXACTLY (single-runner condition), so
$$|\mathcal{I}_A| \;=\; (n-2) L_A.$$
This is MUCH stronger than the Lemma 4.1 bound $|\mathcal{I}_A| \ge
2 L_A/((n-1) u_{\max})$.

**Refined pigeonhole condition for DI**:
$|\mathcal{B}| + (n-2) L_A > n L_A \iff |\mathcal{B}| > 2 L_A$.

So for DI, we only need $|\mathcal{B}| > 2 L_A$. Using $|\mathcal{B}| \ge
|\mathcal{I}_G| \cdot L_A p / L_G$ (when bands are disjoint) and Lemma 4.1:
$|\mathcal{B}| \ge 2 L_A p / ((n-1) v_{\max})$.

Required: $2 L_A p / ((n-1) v_{\max}) > 2 L_A \iff p > (n-1) v_{\max}$.

This requires $p > (n-1) v_{\max}$, which is HARD CASE (since $p < n L_G$
and $L_G \ge v_{\max}$, so $p < n v_{\max}$, contradicting $p > (n-1) v_{\max}$
unless $v_{\max} < n L_G / (n-1)$, which is weak).

**Hmm — this doesn't immediately close DI either.** Need yet finer analysis.

**Refined Path 2 (DI sub-case, attempt 2)**: Use the EXACT formula
$|\mathcal{I}_A| = (n-2) L_A$ together with the actual band structure for DI.

For DI: $L_A = u_1$, $V = p u_1$, slow speeds $v_1, ..., v_{n-2}$. The bands
have width $L_A p = u_1 p = V$ in $m''$-space; β-width $V / L_G$.

Residual cases for DI: from Phase 7c, all have $L_A$ very small (= a single
speed $u_1 \le 10$). So the residual is naturally bounded in $L_A$.

**Refined claim**: For DI, residual requires $L_A \le 10$ (or some explicit
constant). Combined with $u_1 = L_A \le (n-1) v_{\max}/p$, this gives a
constraint on $v_{\max}$: $v_{\max} \ge u_1 p / (n-1) = L_A p / (n-1)$,
which is a LOWER bound (vacuous for our purposes).

But also $u_1 \le L_A \le 10$ implies $u_1 \le 10$, so $V = p u_1 \le 10p$.
By DI: $V > (n-1) v_{\min}$, so $v_{\min} < 10 p / (n-1)$.

For large $n$: $v_{\min}$ becomes small (≤ 1 for $n \ge 10p + 1$), meaning
$1 \in \{v_i\}$ — the slow speeds include 1.

**OK I think the unbounded $v_{\max}$ case needs separate Path 1-style analysis.**
For now, mark this as OPEN and recommend Phase 8d to address.

## Recommended execution order

1. **Phase 8a**: Make Step 2.4 (Chebyshev bound on $L_G$) and Step 2.5
   (asymptotic emptiness for $n \ge N_0$) precise. DeepSeek verify.
2. **Phase 8b**: Run extended Phase 7-style search for $n \in \{11, ..., 25\}$
   with $v_{\max} \le 20, p \le 19$. Confirm residual is bounded and shrinks.
3. **Phase 8c**: Compile complete residual list for $n \le N_0$. Should be
   $\sim$ a few hundred cases total, all positive (by empirical extrapolation).
4. **Phase 8d**: Attempt Path 1 Step 1.3 rigorously (Weyl/discrepancy
   argument). If successful, Path 1 gives a cleaner result; if not, Path 2
   suffices.
5. **Phase 8e**: Integrate into v11.8 manuscript as Theorem 5.2-X (Unconditional
   Closure), removing the "conditional on Conjecture 5.2-H" caveat.

## Estimated effort

- Phase 8a: 1-2 sessions (analytical derivation, DeepSeek verification)
- Phase 8b: 1 session (computational; may take hours to run)
- Phase 8c: 1 session (compile + verify list)
- Phase 8d: 2-3 sessions (genuinely hard analytical work)
- Phase 8e: 1 session (manuscript integration)

**Total**: 6-8 sessions of focused work.

## Confidence (post DeepSeek review)

- Path 2 (asymptotic + enumeration): **HIGH confidence** of unconditional
  closure for $v_{\max}$ bounded inputs. **CRITICAL GAP** for unbounded
  $v_{\max}$ — DeepSeek-flagged. Refinement needed (Step 2.8).
- Path 1 (Cauchy-Schwarz refinement): **MEDIUM confidence** that the
  autocorrelation bound improves Theorem 5.2-U; LOW confidence that it
  closes the residual where Theorem 5.2-U fails. The factor-of-2 weakening
  from disjoint to general overlap is significant.
- Combined: **MEDIUM confidence** that v11.8 can claim unconditional closure.
  The unbounded $v_{\max}$ case requires a NEW idea (Phase 8d analytical work).

## Honest assessment

**The plan as written does NOT close the conjecture unconditionally.** It
closes:
1. The "generic" pigeonhole regime (Theorem 5.2-U, large $p$).
2. The "small $v_{\max}$" residual via Chebyshev (Step 2.5, for $v_{\max}$
   bounded by some function of $n$).
3. The directly-enumerated residual list for $n \le 10$ (Phase 7c).

**Open**: the regime $v_{\max} \to \infty$ where Chebyshev doesn't dominate
and Path 1's Cauchy-Schwarz is too weak.

For full closure, we likely need:
- Either a Fourier-analytic argument (Weyl-type) bounding $|\mathcal{B}|$
  precisely (Path 1 Step 1.3 made rigorous via discrepancy theory), OR
- A structural argument showing that for LRC-shape DI/ModDI with $v_{\max}$
  large, the OTHER speeds must align in a way that forces $|\mathcal{B}|$
  large (refined Path 2).

Recommend: **Phase 8d should be the primary research focus** — this is
where the genuine analytical content lies.

## Next steps (revised)

1. **Phase 8a-prime**: Verify the $|\mathcal{I}_A|$ formula for DI ($k_A = 1$):
   $|\mathcal{I}_A| = (n-2) L_A$ exactly. Use this for refined pigeonhole
   condition $|\mathcal{B}| > 2 L_A$ specific to DI.
2. **Phase 8b** (revised): Extend Phase 7 mining to $n \in \{11, ..., 30\}$
   with larger speed pools to confirm the residual structure and identify
   the unbounded-$v_{\max}$ residual cases empirically.
3. **Phase 8c**: Pattern characterize the unbounded-$v_{\max}$ residual; if
   they all share a structural property, derive an explicit closure.
4. **Phase 8d** (PRIMARY): Develop analytical tools (Cauchy-Schwarz with
   structural shift bound, or Weyl-type bound on $|\mathcal{B}|$) to handle
   the genuine residual regime.
5. **Phase 8e**: Integrate into v11.8 manuscript IF closure achieved; else
   document the precise remaining open scope.
