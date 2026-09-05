# C2-main(C) Construction Audit (v1)

## Scope
This audit checks whether the original C2-main(C) setup was mathematically sound as a construction, independent of empirical pass/fail.

Target examined:

`C2-main(C): I_bad - P_bad + T_bad <= n(B_div-(n-1))`.

---

## 1) Was the derivation itself valid?

Yes, **as a sufficient condition**.

From bad-fiber definition (`A_b=0`), each residue has `q_a(b) >= 1`.
Using

`q - C(q,2) + C(q,3) >= 1` for all integers `q>=1`,

summing over residues/fibers gives

`n C_bad <= I_bad - P_bad + T_bad`.

Combined with `B_safe = B_div - C_bad`, C2-main(C) is a valid sufficient route to `B_safe >= n-1`.

So the construction was not logically wrong; it was a coarse majorant.

---

## 2) What hidden assumption was embedded?

C2-main(C) implicitly assumes the cubic majorant is not too loose on bad fibers.
The exact looseness is explicit:

Define per-residue cubic weight

`g3(q)=q-C(q,2)+C(q,3)`.

Then

`g3(q)-1 = C(q-1,3)`  (exact identity).

Hence

`I_bad-P_bad+T_bad = n C_bad + sum_{bad b} sum_a C(q_a(b)-1,3)`.

So C2-main(C) is equivalent to requiring the tail term

`R3 := sum C(q-1,3)`

to satisfy

`R3 <= n(B_safe-(n-1))`.

This tail-control requirement was present implicitly, but not stated.

---

## 3) Why did the n=12 tuple fail?

Counterexample tuple:

`n=12`, `E=(12,10,5,4,7,3,6,1,8,3,11)`.

Observed:

- `n C_bad = 47028`
- `R3 = sum C(q-1,3) = 52034`
- so `I_bad-P_bad+T_bad = 99062`.

Budget RHS:

`n(B_div-(n-1)) = 92280`.

Equivalent slack form:

`n(B_safe-(n-1)) = 45252`.

Failure is exactly

`R3(=52034) > 45252`.

So the mechanism is high-multiplicity tail mass (`q>=6`) on bad fibers; not a definitional bug.

---

## 4) Important construction-level insight (opportunity)

The same pattern continues for higher odd truncations:

`g5(q)=q-C2+C3-C4+C5`, and

`g5(q)-1 = C(q-1,5)` (exact).

Thus higher odd-order aggregates are not ad hoc patches; they are a systematic tail-control hierarchy.

General form (odd order `2r+1`):

`g_{2r+1}(q)-1 = C(q-1,2r+1)`.

So each upgraded inequality corresponds to controlling a strictly higher combinatorial tail moment of bad-fiber multiplicity.

---

## 5) Audit verdict

- **Construction correctness:** valid sufficient framework.
- **Reason for breakdown:** unstated/failed tail-control condition, now explicit.
- **Interpretation:** this is a structural learning event, not an inconvenience.
- **Right next move:** design/prove a universal tail bound in this hierarchy (rather than treating C2-main(C) as the final universal form).

