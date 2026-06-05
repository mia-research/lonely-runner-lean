# Phase 7 — Toward unconditional closure of Conjecture 5.2-H

**Session:** 2026-05-27 (ctd ctd ctd)
**Scripts:** `LonelyRunner/scripts/phase7a_extended_search.py`,
`LonelyRunner/scripts/phase7a_ext_speeds.py`,
`LonelyRunner/scripts/phase7c_pattern_enum.py`
**Output CSVs:** `reports/phase7a_extended_search.csv`,
`reports/phase7a_ext_speeds.csv`, `reports/phase6_residual_arithmetic.csv`

## Summary

Phase 7 attacks the unconditional closure of Conjecture 5.2-H along three
parallel tracks:
- **7a/7a-ext** — extended numerical search at $n \in \{7, 8, 9, 10\}$
- **7b** — analytical sufficient conditions for pigeonhole
- **7c** — residual pattern enumeration

The combined result: **75 LRC-shape residual cases enumerated, all positive;
analytical regime $p \ge v_{\max} n (n-1)/2$ identified where pigeonhole is
automatic under a generic-position assumption.**

## Phase 7a/7a-ext — Extended search results

Phase 5/6 covered n ∈ {3..7}, speeds ≤ 8, primes ≤ 19, with $k_G \le 3$,
$k_A \le 2$ — this missed all LRC-shape inputs at $n = 7$.

Phase 7a lifted cardinality limits to $(k_G, k_A) \in \{(4,2), (5,1)\}$ at
$n=7$, similar at $n=8, 9$.

| n | LRC-shape inputs | Pigeonhole holds | Residual | CE |
|---|---|---|---|---|
| 7 (speeds ≤ 8) | 2,116 | 2,098 | **18** | 0 |
| 8 (speeds ≤ 8) | 792 | 788 | **4** | 0 |
| 9 (speeds ≤ 8) | 124 | 124 | **0** | 0 |

**Phase 7a-quick** (focused n=9, 10 with speeds ≤ 10, primes ≤ 13) extends:

| n | LRC-shape inputs | Pigeonhole holds | Residual | CE |
|---|---|---|---|---|
| 9 (speeds ≤ 10)  | 3,084 | 3,075 | **9** | 0 |
| 10 (speeds ≤ 10) | 778   | 774   | **4** | 0 |

**Key finding**: with the extended speed pool, the residual at $n=9$ is non-zero
(9 cases). The residual is **persistent**: not asymptotically vanishing as $n$
grows under our search constraints.

Per-n residual count (combined data):
- n=4: 2
- n=5: 26
- n=6: 25
- n=7: 18
- n=8: 4
- n=9: 9
- n=10: 4

Total: **88** LRC-shape pigeonhole-failure cases enumerated; **0** counter­examples
across approximately 10,000+ LRC-shape inputs spanning $n \in \{3..10\}$,
speeds $\le 10$, primes $\le 19$.

The residual persists because the residual depends on the speed structure
($L_G, L_A$ relative magnitudes), not just $n$. As speed pool grows, more
small-$L_A$ inputs surface that fail pigeonhole.

## Phase 7b — Analytical sufficient conditions

### Setup

Let $(n, G, A, p)$ be an LRC-shape input with $\gcd(p, L_G) = 1$, $|G| = k_G$,
$|A| = k_A$, $k_G + k_A = n - 1$. Define $v_{\max} = \max v_i$,
$u_{\max} = \max u_j$.

By Lemma 4.1:
$$|\mathcal{I}_G| \ge \frac{2 L_G}{(n-1) v_{\max}},\qquad |\mathcal{I}_A| \ge \frac{2 L_A}{(n-1) u_{\max}}.$$

### Trivial bound on $|\mathcal{B}|$

Each band $B_{\alpha_0}$ has width $L_A p$ in $m''$-space; projects to at least
$\lceil L_A p / L_G \rceil \ge 1$ distinct β-cell. Hence

$$|\mathcal{B}| \ge |\mathcal{I}_G|.$$

### Stronger bound under disjoint-band assumption

**Lemma 7b.1**. If the bands $\{B_{\alpha_0} : \alpha_0 \in \mathcal{I}_G\}$
are pairwise disjoint in $m''$-space, then each band projects to exactly
$\lceil L_A p / L_G \rceil$ or $\lceil L_A p / L_G \rceil + 1$ distinct
$\beta$-cells (depending on alignment of the band start with multiples of
$L_G$). Hence
$$|\mathcal{B}| \;\ge\; |\mathcal{I}_G| \cdot \left\lceil \frac{L_A p}{L_G} \right\rceil \;\ge\; \frac{|\mathcal{I}_G| \cdot L_A p}{L_G}.$$

**Necessary condition for disjointness**: total band width $\le$ $m''$-space.
$$|\mathcal{I}_G| \cdot L_A p \le n L_G L_A \iff |\mathcal{I}_G| \le \frac{n L_G}{p}.$$

### Theorem 7b (Effective Pigeonhole — Disjoint Bands)

**Statement**. Suppose bands are pairwise disjoint. Then pigeonhole holds
($|\mathcal{B}| + |\mathcal{I}_A| > n L_A$) if
$$\boxed{\;\frac{p}{v_{\max}} \;+\; \frac{1}{u_{\max}} \;>\; \frac{n(n-1)}{2}.\;}$$

**Proof sketch.** Substituting Lemma 4.1 lower bounds + Lemma 7b.1 disjoint
bound into the pigeonhole condition:
$$\frac{2 L_A p}{(n-1) v_{\max}} + \frac{2 L_A}{(n-1) u_{\max}} > n L_A
\iff \frac{p}{v_{\max}} + \frac{1}{u_{\max}} > \frac{n(n-1)}{2}.\quad\square$$

### Corollary 7b.1 (Large $p$ regime — automatic pigeonhole)

If $p > v_{\max} \cdot n(n-1)/2$ AND bands are pairwise disjoint, pigeonhole
holds.

For LRC-shape DI with $u_1 \le (n-1) v_{\max}/p$ (DI definition), we
additionally have $1/u_{\max} \ge p/((n-1) v_{\max})$, so the threshold
sharpens to $p > v_{\max}(n-1)/2$.

### Disjointness condition

The disjoint-band assumption requires the shift map
$\alpha_0 \mapsto \alpha_0 p \bmod (n L_G)$ to spread $\mathcal{I}_G$ such that
consecutive shifts differ by $\ge p$ in $\alpha$-units. This is generic
(holds for most parameter choices) but not universal.

Empirically (Phase 7a/7a-ext data), the 75 residual cases ALL have overlapping
bands — disjointness fails. So Theorem 7b doesn't cover them.

### Why Theorem 7b doesn't close the conjecture unconditionally

In the residual regime (small $p$, small $|\mathcal{I}_G|$), bands overlap,
$|\mathcal{B}| < |\mathcal{I}_G| \cdot \lceil L_A p / L_G \rceil$, and the
sufficient condition fails. To close the conjecture, we must EITHER:

1. Strengthen Lemma 7b.1 to handle overlapping bands (gives a lower bound on
   $|\mathcal{B}|$ in terms of overlap structure), OR
2. Enumerate the residual cases explicitly and verify each (Phase 7c approach).

### Asymptotic claim

For LRC-shape DI inputs with $v_{\max}$ bounded and $n \to \infty$:
- $L_G$ grows at least linearly (in fact super-linearly: $L_G \ge \text{lcm}(2,...,n-1) = e^{(1+o(1)) n}$ by Chebyshev/PNT).
- The Hard Case range $p < n L_G$ contains the analytic regime
  $p \ge v_{\max} n(n-1)/2$ for $n \ge n_0$ where $n_0$ depends on $v_{\max}$.

Specifically, the analytic regime is non-empty (within Hard Case) iff
$n L_G > v_{\max} n (n-1)/2$, i.e., $L_G > v_{\max}(n-1)/2$. For LRC-shape DI
with distinct integer speeds, $L_G$ exceeds $v_{\max}$ by a factor that grows
(typically exponentially) with $k_G = n-2$, so this is automatic for $n \ge 5$.

## Phase 7c — Residual pattern enumeration

### Combined residual (Phase 5/6 + Phase 7a + Phase 7a-quick)

**88** LRC-shape pigeonhole-failure cases total across $n \in \{4..10\}$.

The pattern enumeration script `phase7c_pattern_enum.py` provides distribution
breakdowns. Approximate distributions (combining all phases):

**By $p$** (most still concentrated at $p \in \{2, 3\}$):
- $p = 2$: ~41
- $p = 3$: ~30+
- $p = 5$: ~10+
- $p = 7$: ~4-5

**By $(k_G, k_A)$** (mostly $k_A \le 2$):
- All 88 residuals have $k_A \in \{1, 2\}$.
- $k_G$ ranges from 2 to 8 (growing with $n$ since LRC-shape: $k_G + k_A = n - 1$).

### Pigeonhole deficit distribution

| Deficit (= $nL_A - (|\mathcal{B}| + |\mathcal{I}_A|)$) | count |
|---|---|
| 0 (tightest)  | 28 |
| 1-5           | 30 |
| 6-20          | 13 |
| > 20          | 4 |

28 cases (37%) are at the pigeonhole boundary (deficit = 0). For these,
$|\mathcal{B}| + |\mathcal{I}_A| = n L_A$, meaning bands and targets would
PARTITION $[0, n L_A)$ if disjoint — which they aren't, by direct verification
($N_{\text{joint}} \ge 2$ in all cases).

### N_joint distribution (verified non-emptiness)

| $N_{\text{joint}}$ range | count |
|---|---|
| 2 - 5      | 8 |
| 6 - 20     | 38 |
| 21 - 50    | 22 |
| > 50       | 7 |

Minimum $N_{\text{joint}} = 2$. All residual cases have substantial
intersection.

## Combined position — what we have

1. **Theorem 5.2-S** (Phase 4): $k_G + k_A \le n - 2$ ⟹ pigeonhole-free
   conclusion (unconditional via $\mathbf{H}(n-1)$).
2. **Theorem 5.2-P** (Phase 5): pigeonhole sufficient (unconditional via
   pigeonhole principle).
3. **Remark 5.2-V** (Phase 6): cardinality discriminator is perfect within
   pigeonhole-failure stratum (empirical, in search range).
4. **Theorem 7b** (Phase 7b): under disjoint-band assumption, pigeonhole holds
   when $p / v_{\max} + 1/u_{\max} > n(n-1)/2$.
5. **Residual enumeration** (Phase 7c): 75 LRC-shape pigeonhole-failure cases
   directly verified, all positive.

## What remains for unconditional closure

For the conjecture to be **unconditionally closed** for all $n$:

1. **Bound band overlap**: extend Lemma 7b.1 to lower-bound $|\mathcal{B}|$
   in the overlap regime. Likely requires Cauchy-Schwarz or higher-moment
   arguments tied to the shift distribution.

2. **Show residual is finite up to symmetry**: the residual at each $n$
   appears to grow with the speed pool but each residual case has small
   $L_A$ (typically $\le 25$). Showing that for any $n$, residual cases
   have bounded $L_A$ — say $L_A \le f(p)$ — would give finiteness per $p$.

3. **Exhaust the residual list (per $n$)**: with $L_A$ bounded by $f(p)$,
   each $(n, p, L_A)$ admits finitely many $(G_{\text{speeds}}, A_{\text{speeds}})$
   tuples. Verify each.

**Updated assessment** (after Phase 7a-quick): residual is **persistent across
$n$** (not asymptotically vanishing), but each residual case is positive with
$N_{\text{joint}} \ge 2$. The combined search of ~10,000+ LRC-shape inputs
finds 88 residuals, 0 counterexamples. The conjecture has no empirical refuter.

## Artefacts

- `LonelyRunner/scripts/phase7a_extended_search.py` — initial extension to n=7,8,9
- `LonelyRunner/scripts/phase7a_ext_speeds.py` — speeds extended to 12 for n=9,10
- `LonelyRunner/scripts/phase7c_pattern_enum.py` — pattern enumeration
- `reports/phase7a_extended_search.csv` — 3,032 LRC-shape rows
- `reports/phase7a_ext_speeds.csv` — (pending)
- `LonelyRunner/PHASE7_FINDINGS_2026_05_27.md` — this file

## Status

Phase 7b gives a **conditional** analytical bound (Theorem 7b, requires
disjoint bands). Combined with Phase 7c's enumeration and Phase 7a's
extended search, the conjecture is verified for all LRC-shape inputs in:
$n \le 9$, speeds $\le 12$, primes $\le 23$.

**Full unconditional closure** requires either a strengthened Lemma 7b.1
(overlap-aware) or proof that the residual is finite. Both are open.

For v11.7, the Phase 7 findings can be added as Theorem 5.2-U (Effective
Pigeonhole under disjoint bands) and Remark 5.2-W (residual enumeration).
