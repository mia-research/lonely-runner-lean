# Phase 4 — Empirical mining for Conjecture 5.2-H separating invariant

**Session:** 2026-05-27
**Script:** `LonelyRunner/scripts/phase4_invariant_mining.py`
**Output CSV:** `reports/phase4_invariants.csv` (38,664 rows)

## Setup

For each hard-regime input $(n, G_{\text{speeds}}, A_{\text{speeds}}, p)$ with
- $n \in \{3, 4, 5, 6, 7\}$, $|G_{\text{speeds}}| \le 3$, $|A_{\text{speeds}}| \le 2$,
- $p$ prime $\le 19$, $\gcd(p, L_G) = 1$, $p < n L_G$,
- $\mu(G), \mu(A) > 0$,
- $M := n L_G L_A p \le 5{,}000{,}000$,

we computed:
- $N_{\text{joint}}$: number of joint-good fine cells in $[0, M)$
- $|\mathcal{I}_G|, |\mathcal{I}_A|$, $\mu_G, \mu_A$
- $\gcd(p, n L_G), \gcd(p, n), \gcd(p, L_A)$
- shift-set sizes
- band-union count, target count, expected joint count
- DI / ModDI classification

## Headline finding

**The separating invariant is $k_G + k_A$:**

| Stratum | Inputs | Counterexamples ($N_{\text{joint}} = 0$) |
|---|---|---|
| $k_G + k_A \le n - 2$ | 16,924 | **0** |
| $k_G + k_A = n - 1$ | 8,388 | **0** |
| $k_G + k_A \ge n$ | 13,352 | **681** |

Every one of the 681 abstract counterexamples (from
`LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md`) has $k_G + k_A \ge n$.

## Two consequences for the manuscript

### Theorem 5.2-S (Cardinality Sublemma) — provable

For $k_G + k_A \le n - 2$ at threshold $1/n$: by Lemma 2.1 (Fundamental
Identity), the joint condition is LRC for the combined speed set
$W = \{v_i\} \cup \{p u_j\}$, which has $|W| = k_G + k_A \le n - 2$ distinct
positive integers. By $\mathbf{H}(n-1)$, a strict witness at threshold
$1/(n-1) > 1/n$ exists, satisfying the conjecture's conclusion.

**Distinctness of $W$:** $v_i \ne p u_j$ because $\gcd(p, L_G) = 1$ implies
$p \nmid v_i$ (since $v_i \mid L_G$), but $p \mid p u_j$.

This sublemma is **now in v11.7** as Theorem 5.2-S, with Corollary 5.2-S'
narrowing the open scope of Conjecture 5.2-H to exactly
$k_G + k_A = n - 1$ (the LRC-shape edge case).

### Logical-equivalence observation at $k_G + k_A = n - 1$

At the LRC-shape edge case ($k_G + k_A = n - 1$), Conjecture 5.2-H's joint
condition is LRC for $n - 1$ runners at threshold $1/n$ — exactly the LRC
statement at $n$ for the combined speed set $W$. **So Conjecture 5.2-H at
this scope is logically equivalent (via Lemma 2.1) to the LRC inductive
step at $n$** for the §§10–11 speed structure ($V = pq$, $p$ prime, $\gcd(p, L_G) = 1$).

This matches Option E from `LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md`:
Theorem 5.2 doesn't add logical content beyond §§10.1/11.1 themselves at
the LRC-shape edge case — its role is to separate the analytic content
(fine-cell counting in the easy regime) from the structural content (gcd
setup, §§10–11 reductions).

## What was NOT found

No structural invariant other than $k_G + k_A$ cleanly separates the
counterexamples from the conjecture-satisfying inputs. Specifically:
- $\mu_G, \mu_A, |\mathcal{I}_G|, |\mathcal{I}_A|$ — ranges overlap.
- $\gcd(p, n L_G), \gcd(p, n)$ — both classes span $\{1, 2, 3, 5\}$.
- Shift-set sizes, band-union counts — ranges overlap.

The cardinality is therefore the *unique* clean invariant in this study.

## Limitations

- The script caps $|G_{\text{speeds}}| \le 3$ and $|A_{\text{speeds}}| \le 2$,
  so the data does NOT include the full LRC-shape coverage for $n \ge 6$
  (DI for $n = 7$ needs $|G_{\text{speeds}}| = 5$). The $k_G + k_A = n - 1$
  stratum is only fully populated for $n \le 5$.
- The 5,517 LRC-realisable inputs in the data are a subset of the 20,403
  inputs validated in Phase 1.

## What this means for closing the analytic gap

Theorem 5.2-S extends the *unconditional* scope of v11.7's proof, but
the §§10.1/11.1 invocations of Theorem 5.2 are at $k_G + k_A = n - 1$,
where Conjecture 5.2-H is required. The conjecture at this scope is
equivalent to the LRC inductive step at $n$ itself.

**Genuinely closing the conjecture requires either:**
1. A new analytic technique that proves the LRC inductive step for the
   $V = pq$ hard regime (this *is* the LRC problem in disguise), or
2. A direct LRC-internal compositional argument leveraging the $V = pq$
   structure without reducing to a separate Theorem 5.2 intermediate
   (Option E).

Neither was found in this session. The empirical mining tightened the
conjecture's stated scope (Theorem 5.2-S + Corollary 5.2-S') but did not
resolve the analytic content at the edge case.
