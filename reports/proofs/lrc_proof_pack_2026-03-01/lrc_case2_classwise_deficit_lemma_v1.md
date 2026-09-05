# Case-2 Classwise CRT Deficit Lemma (v1)

## Goal
Recast Case-2 closure directly in aggregate deficit form:

`x0(E) = sum_{b in B_div} delta_b`, where `delta_b = n - cover(b)`.

This avoids anchor-only and lower-band-only arguments.

---

## Definitions (signature class form)
For a fixed Case-2 tuple `E` at size `n`:
- `B_div` = divisible-feasible fibers.
- Signature classes `s` partition `B_div`, with occupancy `N_s`.
- For class `s` and residue `a in Z_n`, define branch multiplicity `q_s(a)`.
- Define class coverage and deficit:
  - `cover_s = #{a : q_s(a) > 0}`,
  - `delta_s = n - cover_s`.

Then exactly:

`x0(E) = sum_s N_s * delta_s`.

---

## Lemma CD.1 (Case-2 branch multiplicity cap)
For every Case-2 class `s` and every `a in Z_n`:

`q_s(a) <= n-2`.

### Proof sketch
In Case-2, at least one speed is divisible by `n`, so `|E_non| <= n-2`.
At fixed `a`, each non-divisible speed contributes at most one active branch hit:
- if `gcd(e,n)=1`, two branches exist globally but correspond to distinct `a` values, so at a fixed `a` at most one branch can hit;
- if `gcd(e,n)>1`, at most one of the two congruence branches is solvable (residues differ by 1), so again at most one hit.
Summing over `E_non` gives `q_s(a) <= |E_non| <= n-2`.

---

## Lemma CD.2 (Exact classwise coverage polynomial)
Define `V_t(s) := sum_{a in Z_n} C(q_s(a), t)`.
Then for Case-2 classes:

`cover_s = sum_{t=1}^{n-2} (-1)^{t+1} V_t(s)`.

Hence

`delta_s = n - sum_{t=1}^{n-2} (-1)^{t+1} V_t(s)`.

### Reason
Pointwise identity for integers `q>=0`:
`1_{q>0} = sum_{t=1}^{m} (-1)^{t+1} C(q,t)` whenever `m>=q`.
Using CD.1, `q_s(a)<=n-2`, so `m=n-2` is exact for every `a`.

---

## Lemma CD.3 (Odd-truncation deficit lower bounds)
For odd `k <= n-2`, define

`UB_k(s) := sum_{t=1}^{k} (-1)^{t+1} V_t(s)`.

By Bonferroni, `cover_s <= UB_k(s)`, so

`delta_s >= max(0, n - UB_k(s))`.

Summing over classes:

`x0(E) >= LB_k(E) := sum_s N_s * max(0, n - UB_k(s))`.

This is a direct classwise CRT deficit lower bound from feasible signature occupancy.

---

## Empirical adjudication (checker v2)
Artifact: `lrc_case2_classwise_deficit_checker_v2.py`.

### Exhaustive (`n=3..6`, full Case-2 grids)
- `LB_3` passes for `n=3,4,5`, fails for some `n=6` tuples.
- `LB_5` has zero violations of `LB_5 >= n-1` and `LB_5 >= phi(n)`.
- `LB_N` (largest odd `<= n-1`) is exact in all tested rows (`x0 - LB_N = 0`).

### Random stress (`n=7..12`, Case-2, `L<=2500`)
- `LB_3` shows failures.
- `LB_5` shows zero violations in sampled sets.
- `LB_N` remains exact on sampled rows.

---

## Current theorem-critical target
The remaining universal inequality can now be stated in this classwise deficit form:

`LB_5(E) = sum_s N_s * max(0, n - UB_5(s)) >= n-1`  for all Case-2 tuples `E`.

If proved, it implies:

`x0(E) >= LB_5(E) >= n-1 >= phi(n)`.

This is a stronger and cleaner closure target than the failed `C2-main(C)` tail route.

---

## Files
- rows: `lrc_case2_classwise_deficit_rows_v2.csv`
- summary: `lrc_case2_classwise_deficit_summary_v2.md`
- checker: `lrc_case2_classwise_deficit_checker_v2.py`
