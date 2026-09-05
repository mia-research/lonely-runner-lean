# LRC `n=all` Shared-Object Dictionary (v1)
**Date:** 2026-03-07  
**Purpose:** rewrite the remaining branches in one common language so the synthesis review can test whether they are local and global faces of the same object.

## 1) Shared objects

### Alpha-state geometry
- `alpha = b/L in I_div`
- `tau(alpha) = (floor(e alpha))_{e in E_fix}`
- `U_fix(tau)` = fixed-side covered residues
- `R_fix(tau) = Z_n \ U_fix(tau)`

### Fiber obstruction geometry
- `B_e(b)` = bad-a set contributed by runner `e`
- `U(b) = union_e B_e(b)`
- `D(b) = n - |U(b)|`
- `O = {b : D(b)=0}`

### Dangerous-set occupancy
- `D_e subset Z_N` dangerous lattice sets
- `x_r` multiplicity histogram
- `S_k` overlap moments
- `x0 = N + sum (-1)^k S_k`

### Coset geometry
- for `g = gcd(e,n) > 1`, runner `e` covers only subgroup cosets of size `g`
- transition objects: `Leave_e`, `Enter_e`
- essentiality question: does vacating a coset expose a residue?

### Period-summed geometry
- `t_div` = divisible-runner period index
- canonical lower/top bands are only part of the total period range
- outside-band safe mass is the summed safe count over interior `t_div` periods

## 2) Branch rewrites

| Frontier branch | Native language in pack | Shared-object rewrite | Controlled quantity |
|---|---|---|---|
| `G4B-COMP-CAP` | obstruction runs, event paths, NZ0 exits | fiber obstruction geometry + coset geometry on the alpha-state graph | `max_obstr_run(C)` / safe-event density |
| `MULTI-DIV` | miss windows, affine `S(F,M)`, delayed Miss | period-summed geometry + occupancy deficit on fibers | total surviving safe fibers or direct `x0` |
| `COMPOSITE-N` | non-unit regime, subgroup opacity, essentiality | coset geometry + alpha-state transitions | exposed departing residue / miss interval |
| `S3-GENERAL` | structural inequality, complementarity, occupancy | dangerous-set occupancy over the full lattice | `x0 > 0` or `x0 >= phi(n)` |
| Xi residual / outside-band branch | `S_out`, widened `I_mid`, period anatomy | period-summed geometry | `sum_k safe_fibers(t_div=k)` |

## 3) Same phenomenon at four resolutions
The current pack appears to describe one obstruction-instability phenomenon at four resolutions:

1. **Local event resolution**
   - a runner transition causes a residue to leave coverage.
   - object: `Leave_e(b_exit)`.

2. **Component resolution**
   - obstruction cannot persist for too long on one `B_div` component.
   - object: `O cap C`.

3. **Period resolution**
   - safe mass accumulates across divisible-runner periods outside canonical bands.
   - object: `safe_fibers(t_div=k)`.

4. **Global occupancy resolution**
   - full dangerous-set union cannot saturate the lattice.
   - object: `x0 = N + sum (-1)^k S_k`.

The synthesis question is whether these are equivalent shadows of one theorem.

## 4) Proposed translation rules

### Rule T1: local exit -> component cap
If every relevant run exit exposes at least one uncovered residue, then obstruction components must have bounded length.

Native branches affected:
- `G4B-COMP-CAP`
- `COMPOSITE-N`

### Rule T2: component cap -> period-safe mass
If obstruction cannot occupy too much of each component, then summed safe mass over periods is positive.

Native branches affected:
- composite `S3`
- some multidiv regimes

### Rule T3: period-safe mass -> occupancy positivity
If summed safe mass across periods is positive with explicit lower bound, then `x0 > 0` or `x0 >= phi(n)`.

Native branches affected:
- Xi residual / outside-band route
- multidiv affine route
- `S3-GENERAL`

### Rule T4: coset essentiality -> local exit exposure
If non-unit runners are subgroup-limited and vacating a coset forces exposure, then pure non-unit exits are safe-producing events.

Native branches affected:
- `G4B-COMP-CAP`
- `COMPOSITE-N`
- E2/E3/E4 program

## 5) Branch-by-branch controlled quantities

### `G4B-COMP-CAP`
Use:
- `D(b)`,
- `O`,
- maximal run exits,
- `Leave_e(b_exit)`,
- component size `|C|`.

What must be proved:
- a theorem converting exit-local exposure into `|O cap C| <= |C| - n`.

### `MULTI-DIV`
Use:
- `B_div`,
- `A_b`,
- `t_div`,
- direct `x0` rather than only `B_safe` where needed.

What must be proved:
- a period/global counting theorem that survives families where safe mass lies outside canonical bands.

### `COMPOSITE-N`
Use:
- non-unit subgroup cosets,
- delayed witness intervals,
- width transfer through `M3`.

What must be proved:
- non-unit exposure is template-free and quantitatively strong enough to feed global counting.

### `S3-GENERAL`
Use:
- dangerous sets `D_e`,
- moments `S_k`,
- multiplicities `x_r`.

What must be proved:
- universal positivity of the occupancy deficit, or another theorem known to imply it.

## 6) Synthesis signal
The strongest signal from this translation pass is:

> `G4B-COMP-CAP` and `COMPOSITE-N` live naturally in local exposure / coset geometry, while `MULTI-DIV` and `S3-GENERAL` live naturally in global occupancy / period-summed positivity.

So the frontier already compresses significantly, even before deciding whether one final theorem links both halves.
