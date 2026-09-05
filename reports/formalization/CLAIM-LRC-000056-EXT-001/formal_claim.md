# Formalized Claim: CLAIM-LRC-000056-EXT-001

## Claim Type
Empirical exactness claim (three structural isolation laws for arithmetic sequences in the 000056 corpus).

## Domain
Dataset: `/Users/trentpalelei/Downloads/lrc_validation_large_1759239075705.csv`
SHA-256: `99b30d585e6378f834d3357efef71ec14852fee04e01ecbb52e86a5d52c00139`
Scope: Arithmetic family only; 55,000 rows; n ∈ {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}.
Columns used: `family, n, phi_n, delta, isolation_count, first_isolation`.
Derived from: INV-PHI-MATCH-001 Finding 6 (2026-02-28), phi_match_investigation_cycle005.md.

## Formal Proposition

Let `A` = all rows where `family = arithmetic` (55,000 rows).

### Law 1 — First Isolation Exactness

Define `fi(r)` = `first_isolation` for row `r ∈ A`, `n(r)` = column `n`, `delta(r)` = column `delta`.

**Claim:** For every row `r ∈ A`, `fi(r) = 1 / (n(r) · delta(r))` exactly.

Verification (over all 55,000 rows):
- Mean relative error = `|fi(r) − 1/(n·delta)| / (1/(n·delta))`: **2.92e-14**
- Max relative error: **5.12e-13**
- Rows with relative error > 1e-9: **0**
- Interpretation: All errors are at machine floating-point precision; the formula is exact.

### Law 2 — Isolation Count Lower Bound

Define `iso(r)` = `isolation_count` for row `r ∈ A`, `phi(r)` = `phi_n`.

**Claim:** For every row `r ∈ A`, `iso(r) ≥ phi(r)`.

Verification:
- Rows with iso < phi_n: **0 / 55,000**
- Interpretation: Zero violations; the lower bound holds without exception.

### Law 3 — Isolation Count Mode

Define `mode(iso | n)` = the most frequent value of `isolation_count` among all rows in `A` with that `n`.

**Claim:** `mode(iso | n) = 3 · phi_n` for n ∈ {5, 6, 7, 8, 9, 10, 12, 15} (8 of 11 tested values).

| n  | phi_n | 3·phi_n | observed mode | law holds? |
|----|-------|---------|---------------|-----------|
| 5  | 4     | 12      | 12            | ✓         |
| 6  | 2     | 6       | 6             | ✓         |
| 7  | 6     | 18      | 18            | ✓         |
| 8  | 4     | 12      | 12            | ✓         |
| 9  | 6     | 18      | 18            | ✓         |
| 10 | 4     | 12      | 12            | ✓         |
| 11 | 10    | 30      | 32            | ✗         |
| 12 | 4     | 12      | 12            | ✓         |
| 13 | 12    | 36      | 40            | ✗         |
| 14 | 6     | 18      | 20            | ✗         |
| 15 | 8     | 24      | 24            | ✓         |

Exceptions (n=11, 13, 14): observed mode exceeds 3·phi_n in each case. No simpler closed-form
formula is currently proposed for these three n values. Note: n=11 and n=13 are prime; n=14=2×7.

## Falsification Rule

This claim is falsified (given the same source file, verified by SHA-256) if:
1. Any arithmetic row has `|first_isolation − 1/(n·delta)| / (1/(n·delta)) > 1e-9`.
2. Any arithmetic row has `isolation_count < phi_n`.
3. The observed mode of `isolation_count` for any of {5, 6, 7, 8, 9, 10, 12, 15} deviates
   from `3·phi_n` when computed over all arithmetic rows with that n.

Law 3 is **not** falsified by deviations at n ∈ {11, 13, 14}, which are documented as known
exceptions with observed modes 32, 40, and 20 respectively.
