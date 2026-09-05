# Defect Moves and Explicit Lemma-D Inequalities (v2)

## 1. Finite Defect-Move Basis
Let `m=n-1`, and let `E=(e_1<...<e_m)` be a strict normalized AP-grid tuple (`gcd(E)=1`).
Define defects:

`d_j = e_j - j`, `j=1..m`.

Because `e_{j+1}-e_j>=1`, we have `d_1<=...<=d_m` and `d_j>=0`.

Define primitive suffix-hole move `H_p` (`p=1..m`):

`H_p(E) = (e_1,...,e_{p-1}, e_p+1, ..., e_m+1)`.

Define inverse (when admissible) `R_p = H_p^{-1}`:

`R_p(E) = (e_1,...,e_{p-1}, e_p-1, ..., e_m-1)`.

Admissibility of `R_p` is exactly `d_p>0` (equivalently strictness/positivity preserved).

### Lemma G (Generation by finite moves)
Let `d_0=0` and `eta_p = d_p - d_{p-1} >= 0`.
Then

`E = H_1^{eta_1} H_2^{eta_2} ... H_m^{eta_m}(A_n)`,

where `A_n=(1,2,...,m)` is the AP-core.

So `{H_p}_{p=1}^m` is a finite generating set for all strict AP-grid defect tuples.

---

## 2. Explicit Inequalities for Lemma D
Let

`f(E) = |U_{e in E} D_e|/N`  (forbidden density),
`sigma(E) = 1 - f(E)`  (safe density).

Also let normalized moments

`s_t(E) = S_t(E)/N`, so `sigma(E)=1+sum_{t=1}^m (-1)^t s_t(E)`.

### Move-by-move inequality family (target obligations)
For each primitive move `H_p`:

- **(D1-p)** `f(H_p(E)) <= f(E)`
- equivalent **(D1p')** `sigma(H_p(E)) >= sigma(E)`
- equivalent moment form **(D1p'')**
  `sum_{t=1}^m (-1)^t ( s_t(H_p(E)) - s_t(E) ) >= 0`.

If `(D1-p)` holds for all `p` and all `E`, then by Lemma G:

`f(E) <= f(A_n)` for all `E`, i.e. AP-core extremizer, and rational `n=all` follows.

---

## 3. Audit Status of the Naive Local Form
Exact sampled audit (`n=5..8`, strict tuples, exact lattice counting):

- file: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_defect_move_audit_summary_v1.md`
- rows: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_defect_move_audit_rows_v1.csv`

Observed pass rates for `(D1-p)`:
- `n=5`: 52.29%
- `n=6`: 46.83%
- `n=7`: 57.22%
- `n=8`: 54.52%

So **naive single-step monotonicity `(D1-p)` is false in general**.

---

## 4. Corrected Lemma-D Form (path version)
Because local monotonicity fails, the defensible move-based target is:

### Lemma D-path (target)
For every defect tuple `E`, there exists a finite sequence of admissible moves

`A_n = E_0 -> E_1 -> ... -> E_r = E`

such that cumulative drift satisfies

`sum_{k=0}^{r-1} ( f(E_{k+1}) - f(E_k) ) <= 0`.

Equivalent:

`f(E) <= f(A_n)`.

This is exactly the AP-extremizer statement, but now expressed in finite move language without requiring each edge to be monotone.

---

## 5. Practical next inequality layer
To make Lemma D-path provable, use a structured potential `Phi` (not raw `f`) with edge inequalities:

- **(P1-p)** `Phi(H_p(E)) <= Phi(E)` for all admissible edges,
- **(P2)** `f(E) <= f(A_n) + C*(Phi(E)-Phi(A_n))` with `C>=0`.

Then `Phi`-monotonicity yields AP extremizer.

Candidate `Phi` choices:
- weighted high-multiplicity tails,
- weighted moment polynomial (dual-certificate form),
- residue-class dispersion functional.

This is the formal move-inequality framework aligned with current notation and scripts.
