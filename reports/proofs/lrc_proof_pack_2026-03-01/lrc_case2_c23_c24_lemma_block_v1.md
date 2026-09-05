# Case-2 Lemmas C2.3/C2.4 (v1)

## Setting
Case 2: at least one speed is divisible by `n`.
Use the standard split:
- `E = E_div ⊔ E_non`,
- `x0 = sum_{b in B_div} |A_b|`,
- `B_safe = {b in B_div : |A_b|>0}`,
- `C_bad = |B_div \ B_safe|`.

For fixed `b in B_div`, define pointwise bad multiplicities on the `a`-fiber:

`q_a(b) = #{e in E_non : (a,b) is bad for e}`, `a=0,...,n-1`.

Define bad-fiber moments:
- `I_b = sum_a q_a(b)`
- `P_b = sum_a C(q_a(b),2)`
- `T_b = sum_a C(q_a(b),3)`.

Aggregate over bad fibers (`A_b=0`):
- `I_bad = sum_{bad b} I_b`
- `P_bad = sum_{bad b} P_b`
- `T_bad = sum_{bad b} T_b`.

---

## Lemma C2.3 (per-fiber obstruction inequalities)
If `A_b=0` then every `a` is covered by at least one bad speed, so `q_a(b) >= 1` for all `a`.
Hence:

1. `n <= I_b`.

2. Let `m=|E_non|`. Since for integers `q in [1,m]`:

`q - (2/m) C(q,2) >= 1`,

we get

`n <= I_b - (2/m) P_b`.

3. Since for every integer `q>=1`:

`q - C(q,2) + C(q,3) >= 1`,

we get

`n <= I_b - P_b + T_b`.

Proof of (3) pointwise identity:

`q - C(q,2) + C(q,3) = q - q(q-1)/2 + q(q-1)(q-2)/6`.

For integer `q>=1`, values are:
`q=1 -> 1`, `q=2 -> 1`, `q=3 -> 1`, and increase for `q>=4`.
So each term is at least 1.

---

## Lemma C2.4 (bad-fiber counting)
Summing C2.3 over bad fibers:

- `n C_bad <= I_bad`
- `n C_bad <= I_bad - (2/m)P_bad`
- `n C_bad <= I_bad - P_bad + T_bad`.

Therefore:

`B_safe = B_div - C_bad >= B_div - (I_bad - P_bad + T_bad)/n`.

So a sufficient condition for the Case-2 target `B_safe >= n-1` is:

`I_bad - P_bad + T_bad <= n(B_div-(n-1))`.   (C2-main(C))

Then immediately:

`x0 >= B_safe >= n-1 >= phi(n)`.

---

## Empirical status (exhaustive bounded Case-2 grids in proof pack)
Using `n=3..7` grids already in the current proof pack:
- all C2.3 inequalities hold with zero violations,
- all C2.4 counting inequalities hold with zero violations,
- C2-main(C) holds on all tested tuples,
- target `x0>=phi(n)` holds on all tested tuples,
- equality appears at `n=3` (`(1,3)`, `(3,1)`).

Artifacts:
- checker: `lrc_case2_c23_c24_checker_v2.py`
- rows: `lrc_case2_c23_c24_rows_v2.csv`
- summary: `lrc_case2_c23_c24_summary_v2.md`

---

## Remaining proof step
Promote C2-main(C) from exhaustive evidence to universal theorem:

`I_bad - P_bad + T_bad <= n(B_div-(n-1))` for all Case-2 tuples.

This is now the concrete final inequality for Case 2 in this branch.
