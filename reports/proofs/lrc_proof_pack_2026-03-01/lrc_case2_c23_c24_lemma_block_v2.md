# Case-2 Lemmas C2.3/C2.4 (v2)

## Case-2 target
For gcd-1 tuples with some `e_r ≡ 0 (mod n)`, prove:

`x0(E) >= phi(n)`.

Using the standard split (`k=aL+b`):

`x0(E) = sum_{b in B_div} |A_b|`,
`B_safe = {b in B_div : |A_b|>0}`,
so `x0 >= |B_safe|`.

A sufficient closure is `|B_safe| >= n-1`.

---

## Fiber moments and bad-fiber counts
For fixed admissible fiber `b in B_div`, define

`q_a(b) = #{e in E_non : (a,b) is bad for e}`, `a=0,...,n-1`.

For bad fibers (`A_b=0`) define:
- `C_bad = #{bad fibers}`
- `I_bad = sum_{bad b} sum_a q_a(b)`
- `P_bad = sum_{bad b} sum_a C(q_a(b),2)`
- `T_bad = sum_{bad b} sum_a C(q_a(b),3)`.

---

## Lemma C2.3 (pointwise bad-fiber obstruction)
If `A_b=0`, then `q_a(b) >= 1` for all `a`.
For integers `q>=1`:

`q - C(q,2) + C(q,3) >= 1`.

Summing over `a` in a bad fiber gives:

`n <= I_b - P_b + T_b`.

Summing over bad fibers:

`n C_bad <= I_bad - P_bad + T_bad`.   (C2.3-ipt)

---

## Lemma C2.4 (counting consequence)
From `B_safe = B_div - C_bad` and C2.3-ipt:

`B_safe >= B_div - (I_bad - P_bad + T_bad)/n`.

Hence the following is a sufficient Case-2 closure condition:

`I_bad - P_bad + T_bad <= n(B_div-(n-1))`.   (C2-main(C))

Then:

`B_safe >= n-1`, so `x0 >= B_safe >= n-1 >= phi(n)`.

---

## Current status
This reduces Case 2 to one concrete universal inequality: **C2-main(C)**.

Evidence now in proof pack:
1. Exhaustive bounded Case-2 grids (`n=3..7`): zero violations of C2-main(C).
2. Additional random stress (`n=8,9,10` with thousands of tuples each under L-cap): zero violations found.

Equality clause remains required:
- `n=3`, `(1,3)` and `(3,1)` achieve `x0=phi(3)=2`.

---

## Remaining task
Prove C2-main(C) universally (all `n`, all Case-2 tuples), not just bounded grids/stress tests.

Artifacts:
- `lrc_case2_c23_c24_checker_v2.py`
- `lrc_case2_c23_c24_summary_v2.md`
- `lrc_case2_c2mainC_stress_v1.py`
- `lrc_case2_c2mainC_stress_summary_v1.md`
