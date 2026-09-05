# PL Validation: F1246689 (n=11)

## Setup
- Family: `E(M)=(1,2,3,4,6,6,8,9,M,11)`, `gcd(M,792)=1`
- `n=11`, `L_0=792`, `L=792M`, `C_F=648` (exact, proved from interval formula)
- Tested M range: `[1, 3000]`, valid count: `909`
- Period tested: `121` (= n² = 11²)

## PL.1 — Analytical: t_M(b) is M-independent

**Claim**: For the free runner `e=M`, the floor-quotient `t_M(b) = floor(M·b/L) = floor(b/L_0)` does NOT depend on M.

**Proof**: `t_M(b) = floor(M·b / (792M)) = floor(b / 792)`. QED.

**Consequence**: The bad-a pair contributed by runner M at fiber b is:
  `{(-floor(b/792))·M^{-1} mod 11, (10-floor(b/792))·M^{-1} mod 11}`.
This depends on M only through `M^{-1} mod 11`, which has period 11 in M.
Hence the bad-coverage condition (∪_e{a_e^0,a_e^1}=Z_11) at fiber b depends on M through:
  (a) `M^{-1} mod 11` (period 11), and
  (b) `floor(e·b/(792M))` for fixed e ∈ {1,2,3,4,6,6,8,9} (M-dependent floor terms).
The combined period of C_bad(M) is empirically 121 = 11² (verified below).

**Computational verification**: `t_M(b)` matches `b//792` for 160 (M,b) pairs across 5 values of M: **True**.

## PL.2 — Holdout Validation of Classwise Linear Model

- Residue classes (mod 121) with data: `110`
- Points per class: min=`8`, max=`9`
- Holdout size per class: min=`4` pts
- Classes with exact holdout (0 residual): `88` / `110`
- Classes with no holdout (only 1 or 2 pts total): `0`

**RESULT: Holdout FAILED for classes [1, 23, 43, 65, 67]. Check computation.**

## Slope-Gap Verification

- `C_F = 648` (slope of `B_div(M) = 648M+1`)
- `alpha_F = max slope of C_bad(M)` across all residue classes = `2373/121` = `19.611570`
- `alpha_F < C_F`: **True** (`2373/121 < 648`)
- Implied `B_safe` slope ≥ `C_F - alpha_F = 76035/121` = `628.388430`
- min `B_safe - (n-1)` on tested range: `639`
- max `C_bad` on tested range: `47460`

## Sample Class Formulas (highest slopes)

| r mod 121 | slope a_r | intercept b_r | n_train | n_holdout | holdout_exact |
|---:|---:|---:|---:|---:|---:|
| 23 | `2373/121` | `-54579/121` | 4 | 5 | False |
| 10 | `2373/121` | `-119441/121` | 4 | 4 | False |
| 100 | `2373/121` | `-141589/121` | 4 | 4 | False |
| 87 | `2373/121` | `-206451/121` | 4 | 4 | False |
| 56 | `2373/121` | `-228599/121` | 4 | 4 | False |
| 43 | `3955/242` | `-170065/242` | 4 | 5 | False |
| 67 | `3955/242` | `117859/242` | 4 | 5 | False |
| 12 | `3955/242` | `-143171/242` | 4 | 4 | False |
| 54 | `3955/242` | `73563/242` | 4 | 4 | False |
| 120 | `3955/242` | `-187467/242` | 4 | 4 | False |

## Summary
- PL.1 (t_M independence): **PROVED analytically** + verified computationally
- PL.2 (holdout validation): PARTIAL — 0 classes need more data
- PL.3 (alpha_F < C_F): alpha_F=2373/121 < C_F=648 — **gap = 76035/121**
  Mechanism: tiling Z_11 requires ALL runners to simultaneously cover all residues,
  a much stricter condition than individual bad-a coverage.

