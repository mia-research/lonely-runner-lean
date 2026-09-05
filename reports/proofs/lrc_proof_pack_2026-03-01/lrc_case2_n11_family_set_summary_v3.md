# n=11 Family Set (v3)

Goal outputs: explicit `B_div(F,M)` formulas, exact periodic-linear `N_s(F,M)` forms, and `alpha_F` vs `C_F`.

## Family Definitions

- **F1**: `E(M)=(1^8,M,11), 11∤M`
- **F12**: `E(M)=(1^7,M,11,22), gcd(M,22)=1`
- **F1246689**: `E(M)=(1,2,3,4,6,6,8,9,M,11), gcd(M,792)=1`

## Alpha vs C Table

| family | tested M | B_div formula exact | C_F | C_bad fit (period) | alpha_F range | max C_bad | min(B_safe-(n-1)) |
|---|---:|---:|---:|---:|---|---:|---:|
| F1 | 440 | 1 | 9 | 1 (121) | [0,0] | 0 | 0 |

### F1
- `B_div(M)=9M+1` exact on tested M: `1`
- `C_bad(M)` periodic-linear fit success: `1` with period `121` and `110` residue classes
- `C_bad` slope range: `[0, 0]`
- Top signature fits (slots [1,M]): `8/8`
- Sample `C_bad` class formulas:
  - r=1: `C_bad=0*M + 0` (points=4)
  - r=2: `C_bad=0*M + 0` (points=4)
  - r=3: `C_bad=0*M + 0` (points=4)

| F12 | 220 | 1 | 16 | 1 (121) | [0,0] | 0 | 8 |

### F12
- `B_div(M)=16M+2` exact on tested M: `1`
- `C_bad(M)` periodic-linear fit success: `1` with period `121` and `110` residue classes
- `C_bad` slope range: `[0, 0]`
- Top signature fits (slots [1,M]): `8/8`
- Sample `C_bad` class formulas:
  - r=1: `C_bad=0*M + 0` (points=2)
  - r=2: `C_bad=0*M + 0` (points=2)
  - r=3: `C_bad=0*M + 0` (points=2)

| F1246689 | 152 | 1 | 648 | 1 (121) | [0, 2373/121] | 7910 | 639 |

### F1246689
- `B_div(M)=648M+1` exact on tested M: `1`
- `C_bad(M)` periodic-linear fit success: `1` with period `121` and `42` residue classes
- `C_bad` slope range: `[0, 2373/121]`
- Top signature fits (slots [1,M]): `8/8`
- Sample `C_bad` class formulas:
  - r=1: `C_bad=3779/242*M + -3779/242` (points=2)
  - r=3: `C_bad=0*M + 0` (points=2)
  - r=4: `C_bad=0*M + 0` (points=2)

