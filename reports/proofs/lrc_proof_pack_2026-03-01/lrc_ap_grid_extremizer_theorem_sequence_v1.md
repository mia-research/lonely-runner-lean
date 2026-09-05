# LRC AP-Grid Extremizer Theorem Sequence (v1)

## Purpose
Provide a formal sequence that matches your conceptual path:

1. `Definition` (AP-grid + grand return frame)
2. `Extremizer Lemma` (AP-core maximizes forbidden coverage)
3. `Defect Monotonicity` (adding holes/defects cannot increase worst congestion)
4. `Main Theorem` (rational `n=all` follows)

Notation is aligned with current scripts/results (`D_e`, `S_t`, `x_q`, `N=nL`).

---

## 1. Definitions
### Definition 1 (Normalized rational frame)
Fix runner `i`. Set relative rational speeds `w_j = v_j - v_i` for `j=1..m` with `m=n-1`.
Clear denominators and divide by gcd to obtain integers `e_1,...,e_m` with `gcd(e_1,...,e_m)=1`.
Set:
- `L = lcm(e_1,...,e_m)`
- `N = nL`
- lattice times `s_k = k/N`, `k in Z_N`.

### Definition 2 (Dangerous sets)
For each `e`:

`D_e = { k in Z_N : {e s_k} < 1/n or {e s_k} > (n-1)/n }`.

Safe count:

`x_0 = N - |U_e D_e|`.

### Definition 3 (AP-grid class)
A speed set is AP-grid if all normalized integer speeds lie in one arithmetic lattice:

`E subset d*Z_{>0}` for some step `d`.

After gcd-normalization, AP-grid is simply an integer set `E subset Z_{>0}` (possibly with holes).

### Definition 4 (AP-core)
For fixed `n`, define

`A_n = {1,2,...,n-1}`.

This is the no-hole core against which AP-grid defect sets are compared.

---

## 2. Exact Identities (proved)
Define multiplicity histogram `x_q` (`q=0..m`) and overlap moments

`S_t = sum_{|I|=t} |cap_{e in I} D_e| = sum_{q=t}^m C(q,t)x_q`.

Then inclusion-exclusion gives exactly:

`x_0 = N + sum_{t=1}^{m} (-1)^t S_t`.

So LRC-SINGLE is equivalent to `x_0>0`.

---

## 3. Extremizer Program (formal statement)
### Lemma E (AP-core extremizer, target)
For every gcd-1 integer tuple `E={e_1,...,e_m}` of size `m=n-1`:

`|U_{e in E} D_e| <= |U_{a in A_n} D_a|`.

Equivalent form:

`x_0(E) >= x_0(A_n)`.

Interpretation:
- AP-core is maximal forbidden congestion (worst case).
- Any non-core arrangement has at least as many safe points.

Status: **open** (this is the key new lemma matching your conceptual claim).

---

## 4. Defect Monotonicity Program
Let `E = A_n + defects` in AP-grid coordinates (holes/shifts/duplicates under normalization constraints).

### Lemma D (Defect monotonicity, target)
Each admissible defect operation does not increase forbidden union size:

`F(E) := |U_{e in E} D_e|`, and for each primitive defect move `E -> E'`:

`F(E') <= F(E)` whenever `E` moves away from AP-core symmetry.

Sufficient route:
1. Classify primitive moves (hole insertion, index spread, residue-class split).
2. Show each move weakly decreases high multiplicity mass (`x_m, x_{m-1}, ...`).
3. Deduce non-increase of `F`.

Status: **open**, but this is the mathematically precise version of your fragility argument.

---

## 5. Main Theorem (conditional, clean)
### Theorem T (Rational `n=all` from AP-core extremizer)
Assume Lemma E (or Lemma D implying Lemma E). Then for every `n>=3`, every rational speed set, and every runner `i`, there exists a time when runner `i` is isolated at threshold `1/n`.

#### Proof
By normalization, reduce to integer tuple `E` and dangerous sets on `Z_N`.
By Lemma E:

`x_0(E) >= x_0(A_n)`.

`x_0(A_n)>0` (AP-core has known safe witnesses).
Hence `x_0(E)>0`, so a safe time exists. QED.

---

## 6. How this bypasses full `S_t` tower
Without Lemma E, one may need higher moments `S_5,S_6,...`.
With Lemma E/D proved, full high-order enumeration is unnecessary:
- evaluate only AP-core positivity once,
- compare all others via monotonicity/extremizer inequality.

This is exactly the compression you asked for.

---

## 7. Alignment with computed evidence
From current runs:
- exact formulas for low-order overlaps are validated;
- S4 moment forcing proves all scanned tuples in bounded grids;
- no counterexamples found in extended checks.

These support (but do not yet prove) Lemma E/D.

---

## 8. Immediate proof tasks
1. Define a finite generating set of AP-grid defect moves.
2. For each move, prove non-increase of `F(E)` or monotone improvement of `x_0`.
3. Conclude Lemma D -> Lemma E -> Theorem T.
