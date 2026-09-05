# G4.OPEN SL-1.B Track Note (v2)
Date: 2026-03-04
Scope: Near-complete one-divisible Case-2, Case-iiib branch (composite n).

## 0. Goal
Close the remaining Case-iiib blocker in G4.OPEN by proving:
- `exists r*` with positive miss interval in alpha-space,
- with explicit lower bound and denominator control,
- then lift to an interior integer `b`-interval witness.

## 1. Locked setup
Let
- `I_div = [1/n, (n-1)/n]`,
- `Cov_e(r) = union_{t: r in bad_set(e,t,n)} [t/e,(t+1)/e) intersect I_div`,
- `Miss(r) = I_div \ union_{e in E_fix} Cov_e(r)`,
- `m(r) = meas(Miss(r))`.

Case-iiib means:
- `1, n-1 in E_fix`,
- `|E_fix| = n-3`,
- `U_fix(tau=0) = Z_n`.

## 2. Theorem-grade status split

### 2.1 Proved pieces

**SL1-P1 (Rational endpoint lemma): PROVED**
All `Cov_e(r)` endpoints are of form `t/e` with `e<=e_max`; therefore every `Miss(r)` endpoint is rational with denominator `<=e_max<=n`.

**SL1-P2 (Equivalent witness formulation): PROVED**
`exists b in B_div` with `U_fix(tau(b)) != Z_n` iff `exists r` with `Miss(r) != empty`.

### 2.2 Open analytic piece

**SL1-O1 (Uniform miss lower bound): OPEN**
Need analytic proof of
`exists r* : m(r*) >= 1/(e_max*(e_max-1))`
for all Case-iiib templates in scope.

### 2.3 Empirical support (extended)

A reproducible probe was run for composite `n in [10,30]` over all Case-iiib templates.

Results:
- Templates checked: `694`
- Bound violations `m(r*) < 1/(e_max*(e_max-1))`: `0`
- Denominator violations `den(alpha_endpoints) > n`: `0`
- Zero integer witness at `M=1`: `0`

Extremal row:
- `n=14`, dropped `(6,10)`, `best_r=4`,
- `m(best_r)=8/91`, bound `=1/156`, ratio `=13.714285...`.

Smallest integer witness row (M=1):
- `n=10`, dropped `(4,8)`, `max_b_count_m1=240`.

Artifacts:
- `/tmp/lrc_sl1b_extended_probe_v1.py`
- `/tmp/lrc_sl1b_extended_probe_rows_v1.csv`
- `/tmp/lrc_sl1b_extended_probe_summary_v1.md`

## 3. Immediate theorem path

1. Prove SL1-O1 (uniform lower bound) via Farey-gap control on active-window endpoints.
2. Use denominator control to select rational `alpha*` in a miss interval.
3. Lift `alpha*` to integer `b` witness at any `M>=1` (already empirically strong at `M=1`).
4. Conclude Case-iiib `=> Lambda_eff > 0` and close G4.OPEN in this scope.

## 4. Current classification

- `SL1-P1`: PROVED
- `SL1-P2`: PROVED
- `SL1-O1`: OPEN
- `G4.OPEN (Case-iiib)`: OPEN-PROGRESS (single sub-lemma blocker)
