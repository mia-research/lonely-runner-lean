# Lemma E Case-2 Work Note (v2)

## Case-2 setting
Normalized integer tuple `E=(e_1,...,e_{n-1})`, `gcd(E)=1`, with at least one component divisible by `n`.

Goal:

`x0(E) >= phi(n)`.

(Strict `>` is false in general: `n=3`, `E=(1,3)` gives equality.)

---

## Exact decomposition
Write `k = aL + b`, with `a in {0,...,n-1}`, `b in {0,...,L-1}`, `L=lcm(E)`, `N=nL`.

Split speeds:
- `E_div = {e in E : e ≡ 0 (mod n)}`
- `E_non = E \ E_div`

Define
- `B_div = { b : all divisible-speed constraints pass at b }`
- `A_b = { a : all non-divisible constraints pass at k=aL+b }`.

Then exactly:

`x0(E) = sum_{b in B_div} |A_b|`.

Also define

`B_safe = { b in B_div : |A_b| > 0 }`.

Hence

`x0(E) >= |B_safe|`.

---

## New candidate lemma (from exhaustive evidence)
### Candidate C2-Bsafe
For all Case-2 tuples:

`|B_safe| >= n-1`.

If true, then immediately:

`x0(E) >= |B_safe| >= n-1 >= phi(n)`.

So C2-Bsafe would close Case 2 and therefore complete Lemma E.

---

## Evidence produced
Exhaustive scans (case-2 tuples only) in current proof pack:
- `n=3` with `max_e=12`
- `n=4` with `max_e=9`
- `n=5` with `max_e=7`
- `n=6` with `max_e=8`
- `n=7` with `max_e=7`

Results summary (`lrc_case2_bsafe_summary_v1.md`):
- `min B_safe = n-1` in every tested `n`
- zero violations of `B_safe >= n-1`
- zero violations of `x0 >= phi(n)`

Min examples align with low-structure tuples containing many `1`s and one `n`.

---

## Proof roadmap to promote C2-Bsafe
1. Characterize `B_div` via interval-congruence constraints in `b` only.
2. For each admissible `b`, analyze bad-`a` residue sets from each non-divisible speed.
3. Prove at least `n-1` values of `b` have nonempty `A_b` (i.e., are in `B_safe`).
4. Conclude `x0 >= phi(n)` from `x0 >= |B_safe|`.

This avoids high-order global moment expansions and keeps Case 2 in the AP-grid/defect framework.

---

## Artifacts
- Script: `lrc_case2_bsafe_scan_v1.py`
- Rows: `lrc_case2_bsafe_rows_v1.csv`
- Summary: `lrc_case2_bsafe_summary_v1.md`
