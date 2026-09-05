# Case-2 Tail Hierarchy + Optimal Majorant Program (v1)

## Purpose
Formalize the repaired Case-2 pathway after the C2-main(C) construction audit:

1. exact odd-order tail identity,
2. exact remainder decomposition,
3. optimal-majorant LP/dual program for selecting low-order aggregate forms.

---

## Setup
On bad fibers (`A_b=0`), let `q_a(b) >= 1` be bad-speed multiplicity at residue `a in Z_n`.
Define bad-fiber moments

`M_t := sum_{bad b} sum_{a in Z_n} C(q_a(b), t)`, `t>=1`.

Then:
- `M_1 = I_bad`
- `M_2 = P_bad`
- `M_3 = T_bad`
- etc.

For odd order `k=2r+1`, define polynomial weight

`g_k(q) := sum_{t=1..k} (-1)^{t+1} C(q,t)`.

Aggregate:

`L_k := sum_{bad b} sum_a g_k(q_a(b)) = sum_{t=1..k} (-1)^{t+1} M_t`.

---

## Lemma TH.1 (Tail hierarchy identity)
For all integers `q>=1` and odd `k>=1`:

`g_k(q) - 1 = C(q-1, k)`.

### Proof
Use the standard alternating binomial partial-sum identity:

`sum_{t=0..k} (-1)^t C(q,t) = (-1)^k C(q-1,k)`.

Therefore

`g_k(q) = sum_{t=1..k} (-1)^{t+1} C(q,t)
       = 1 - sum_{t=0..k} (-1)^t C(q,t)
       = 1 + C(q-1,k)`

(since `k` is odd). Hence `g_k(q)-1=C(q-1,k)`. ∎

---

## Corollary TH.2 (Exact remainder decomposition)
For odd `k=2r+1`:

`L_k = n C_bad + R_k`,

where

`R_k := sum_{bad b} sum_a C(q_a(b)-1, k)`.

So every odd-order aggregate is exactly `n*C_bad` plus a nonnegative tail remainder.

Special cases:
- `k=3`: `L_3 = I_bad - P_bad + T_bad = n C_bad + sum C(q-1,3)`
- `k=5`: `L_5 = I_bad - P_bad + T_bad - Q4_bad + Q5_bad = n C_bad + sum C(q-1,5)`

---

## Interpretation for C2-main(C)
C2-main(C) is the `k=3` member:

`L_3 <= n(B_div-(n-1))`.

By TH.2, this is equivalent to demanding

`R_3 <= n(B_safe-(n-1))`.

So the failure mode is now explicit: high multiplicity tail `C(q-1,3)` can exceed slack.

---

## Counterexample diagnostic (carried forward)
Tuple:

`n=12`, `E=(12,10,5,4,7,3,6,1,8,3,11)`.

Computed:
- `x0=9386`, `phi(12)=4` (LRC-side goal strongly true)
- `L_3 = 99062`
- `n(B_div-(n-1)) = 92280`

So `k=3` fails.

But:
- `L_5 = 86198 <= 92280` (passes).

Thus failure is a cubic-tail issue, not framework invalidity.

---

## Optimal Majorant Program (LP/dual form)
For a fixed multiplicity cap `m` (Case-2: `m<=n-2`) and truncation `T`, choose

`p(q)=sum_{t=1..T} c_t C(q,t)`

as a majorant of `1_{q>0}` on `q=1..m` by solving:

`min z`

subject to
- `p(q) >= 1` for `q=1..m`,
- `p(q)-1 <= z` for `q=1..m`,
- `z>=0`.

This is a finite LP; our implementation solved it via vertex enumeration.

Interpretation:
- objective minimizes worst overshoot over multiplicity levels,
- active constraints at optimum serve as a finite dual witness pattern.

Candidate aggregate inequality induced by `p`:

`L_p := sum_{bad b} sum_a p(q_a(b)) <= n(B_div-(n-1))`.

If true universally, Case-2 closes.

---

## Computed coefficients (examples)
From `lrc_case2_optimal_majorant_lp_v1.py`:

For `m=10` (relevant to the `n=12` counterexample):
- `T=3`: `p(q)=C(q,1) - 0.45*C(q,2) + 0.1*C(q,3)`
- `T=5`: `p(q)=C(q,1) - 0.8392857143*C(q,2) + 0.5833333333*C(q,3) - 0.2976190476*C(q,4) + 0.08503401361*C(q,5)`

On the counterexample:
- `L_3` (fixed cubic) = `99062` (fails)
- `L_5` (fixed odd-5) = `86198` (passes)
- `L_{p,T=3}` = `59569.1` (passes)
- `L_{p,T=5}` = `49925.64` (passes)

So LP majorants identify much lower-overshoot aggregate forms.

---

## Practical theorem route from here
1. Prove TH.1/TH.2 (now explicit and short).
2. Choose a universal majorant family `p_n` (fixed symbolic coefficients or constrained LP-derived template).
3. Prove universal bound

`sum_{bad b} sum_a p_n(q_a(b)) <= n(B_div-(n-1))`

via CRT/signature counting.
4. Conclude `B_safe>=n-1` and thus Case-2 closure.

This preserves the original architecture while replacing a brittle cubic majorant by a controlled tail-majorant method.

---

## Artifacts
- LP script: `lrc_case2_optimal_majorant_lp_v1.py`
- LP coeffs: `lrc_case2_optimal_majorant_coeffs_v1.csv`
- forcing table: `lrc_case2_optimal_majorant_summary_v1.md`
- detailed rows: `lrc_case2_optimal_majorant_results_v1.csv`
