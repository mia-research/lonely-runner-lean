# Lemma M2-drop (Candidate) v1
Date: 2026-03-04
Status: OPEN-PROGRESS (strong empirical support)

## 1. Scope
Near-complete one-divisible Case-2, Case-iiib branch:
- `n` composite, `n >= 10`
- `E_fix = {1,...,n-1} \ {a,b}` with `|E_fix|=n-3`
- `1, n-1 in E_fix`
- `U_fix(tau=0)=Z_n`
- `I_div=[1/n,(n-1)/n]`

Define for `r in Z_n`:
- `Cov_e(r) = union_{t: r in bad_set(e,t,n)} ([t/e,(t+1)/e) intersect I_div)`
- `Miss(r) = I_div \ union_{e in E_fix} Cov_e(r)`

Define dropped-runner residue support:
- `Cover(e) = union_{t=0}^{e-1} bad_set(e,t,n)`
- `Cover_drop = Cover(a) union Cover(b)`

## 2. Statement (M2-drop)
There exists a residue `r* in Cover_drop` such that
`Miss(r*) != empty`.

Equivalent fiber form:
There exists `r* in Cover_drop` and `b in B_div` with `r* notin U_fix(b)`.

## 3. Why this matters
`M2-drop` => `M2` (existence of uncovered residue), and with already-locked endpoint/Farey control:
- positive miss measure lower bound follows,
- integer witness follows by counting bridge,
- Case-iiib branch closes in the `Lambda_eff>0` chain.

## 4. Current evidence envelope
Extended probe (composite `n=10..40`):
- Case-iiib templates checked: `1719`
- `M2` failures (`exists r with Miss(r)=empty for all r`): `0`
- `M2-drop` failures (`exists r in Cover_drop with Miss(r)>0`): `0`
- best miss boundary-touch: `0`

Empirical status: no counterexample found in tested scope.

## 5. Proof gap
Remaining analytic burden is a universal existence argument for an uncovered residue in dropped support (`Cover_drop`) without template-wise enumeration.

A likely route is transition-graph contradiction:
assume `Miss(r)=empty` for all `r in Cover_drop`, propagate through state transitions, and derive impossible full-coverage persistence under missing-runner deletion.
