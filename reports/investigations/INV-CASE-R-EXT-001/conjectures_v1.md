# INV-CASE-R-EXT-001: Mechanistic Conjecture Testing

## Conjecture M1: min containment margin ≥ 1/(11·p₂)

The tightest possible margin is set by the second-slowest runner p₂.

- Tested (successes): 1000
- Violations (margin < 1/(11·p₂)): **0**
- Min ratio (margin / bound): 9.7778
- Mean ratio: 217.1144

## Conjecture M2: L ≤ ⌊p₁₀/p₁⌋ − 10

- Violations (L > ⌊p₁₀/p₁⌋ − 10): **30**
  [9, 59, 63, 70, 76, 78, 83, 97, 114, 119]: L=4, bound=3, type=A
  [4, 9, 17, 21, 22, 23, 24, 37, 39, 42]: L=2, bound=0, type=A
  [5, 20, 21, 26, 33, 43, 48, 52, 53, 54]: L=3, bound=0, type=A
  [8, 49, 51, 56, 61, 62, 65, 74, 76, 84]: L=5, bound=0, type=A
  [1, 3, 4, 6, 7, 8, 9, 10, 11, 12]: L=7, bound=2, type=A

## Conjecture M3: Step L2 buffer ≥ 0 for all configs

- Violations (buffer < 0): **278**
- Near-violations (0 ≤ buffer < 1): 52

Top violations:
  [4, 494, 567, 572, 997, 1072, 1288, 1573, 1597, 1914]: buf=-4.000000, type=A
  [4, 89, 169, 1108, 2361, 2365, 2409, 2758, 3137, 3357]: buf=-86.157303, type=A
  [1, 37, 66, 107, 108, 126, 285, 291, 302, 375]: buf=-4.318182, type=A
  [4, 45, 118, 163, 175, 178, 207, 210, 273, 298]: buf=-13.866667, type=A
  [6, 50, 67, 75, 95, 129, 159, 167, 241, 304]: buf=-2.686567, type=A

Closest to 0: ([1, 130, 169, 183, 350, 356, 363, 422, 424, 432], 0.03581267217630854, 'A')

## Theorem 10.12 Verification: Pacemaker Configs (ratio = 11)

For each p1=1, p10=11, missing speed m: check that ILE witness = (11j*+1)/121.

| Missing m | j* | Theorem t* | ILE witness | Match |
|---|---|---|---|---|
| 2 | 5 | 56/121 = 0.462810 | 56/121 | ✓ |
| 3 | 7 | 78/121 = 0.644628 | 17/55 | ✗ (got 17/55) |
| 4 | 8 | 89/121 = 0.735537 | 23/99 | ✗ (got 23/99) |
| 5 | 2 | 23/121 = 0.190083 | 23/121 | ✓ |
| 6 | 9 | 100/121 = 0.826446 | 12/77 | ✗ (got 12/77) |
| 7 | 3 | 34/121 = 0.280992 | 3/22 | ✗ (got 3/22) |
| 8 | 4 | 45/121 = 0.371901 | 4/33 | ✗ (got 4/33) |
| 9 | 6 | 67/121 = 0.553719 | 6/55 | ✗ (got 6/55) |
| 10 | 1 | 12/121 = 0.099174 | 12/121 | ✓ |
