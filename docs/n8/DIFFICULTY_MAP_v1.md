# The difficulty-weighted map — replacing the withdrawn count-weighting

`CATEGORIES_v1`'s weighting was withdrawn because instance counts in a box measure neither progress
nor remaining work. This is the replacement: the same partition, weighted by **`R`**, the least clear
point `≥ 1`. `R = 1` means the profile clears at the first instant — no cascade, nothing to prove.

## The table

40,000 random speed sets from `[1,300)`, `R` computed exactly by endpoint enumeration.

| `k` | instances | `R = 1` | `R > 1.25` | `R > 1.5` | `R > 2` | max `R` |
|---|---|---|---|---|---|---|
| 0 | 977 | 45.8% | 1.43% | 0.00% | **0.00%** | 1.3009 |
| 1 | 96 | 26.0% | 4.17% | 0.00% | **0.00%** | 1.3673 |
| 2 | 344 | 33.4% | 3.78% | 0.00% | **0.00%** | 1.5000 |
| 3 | 847 | 30.8% | 7.67% | 0.71% | **0.00%** | 1.8617 |
| 4 | 2,006 | 28.6% | 13.66% | 2.99% | 0.15% | 2.9412 |
| 5 | 7,419 | 37.8% | 20.37% | 7.02% | 1.25% | 3.6957 |
| 6 | 28,311 | 60.7% | 17.10% | 6.88% | 1.25% | 5.0611 |

**Where the hard instances are** (`R > 2`, i.e. a real cascade): `k = 4` holds 0.7%, `k = 5` holds
20.7%, **`k = 6` holds 78.6%**. `k ≤ 3` holds **none**. Hardest found: `R = 5.0611` at `k = 6`,
speeds `[39, 97, 131, 169, 204, 232, 291]`.

## Two things the count-weighting could not say

**1. The proved categories are exactly the cascade-free ones.** `k = 0, 1, 2` produced no instance
with `R > 2` in 40,000 samples. Branch A and `TwoWalker` close precisely the region where the cascade
never starts, and stop where it does. That is a statement about what those proofs are *for*, which a
percentage of instances cannot express.

**2. `k = 3` is open but shows no depth.** 847 instances, max `R = 1.8617`, **zero above 2**. By
difficulty it belongs with the proved region; by structure it is listed with the frontier. That makes
it the natural next target — extending `TwoWalker` from `k ≤ 2` to `k = 3` attacks a region that
empirically has no cascade, rather than `k = 6`, which has 78.6% of all depth.

This lead was invisible under instance-counting, where `k = 3` was 0.04% and indistinguishable from
the rest of the "99.95% open".

## Scope

`[EMPIRICAL]`: 40,000 random speed sets from `[1,300)`, `R` exact. Random sampling does **not** reach
band 1 — every deep case on file (`R ≈ 11.6–11.97`) is far above the `5.06` maximum here, and all of
those have non-integer readings, consistent with the table's tail sitting at high `k`. So the table
ranks the categories; it does not bound them.

`R` is the right axis because it is the framework's own difficulty measure (Theorem 11.1) and because
`R = 1` is exactly "nothing to prove". Instance counts rank nothing.

## Deposit

`experiments/n8/difficulty_map_v1.py`, `experiments/n8/difficulty_by_k_v1.py`.
