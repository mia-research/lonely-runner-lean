# `(9,1)` Branch Shell Reduction
## Reducing the last global entrance branch to one inequality sublemma — 2026-04-23

---

## Purpose

After the inner-asymmetry lemma, the remaining global promotion step became:

1. prove every fixed point has lead/tail pair in
   `{(5,5),(6,2),(8,2),(9,1)}`
2. prove the `(9,1)` branch is exactly `E`.

This note carries the second item most of the way.

It shows:

> once a fixed point is known to have lead/tail pair `(9,1)` and inner
> symmetry, its shell pairing already has the exact `E` shape.

So the only missing ingredient is one clean inequality sublemma guaranteeing
that the excess-`9` layer does not outrun the inner multiplicities.

---

## Inner-symmetric count form

By the inner-asymmetry lemma, every `(9,1)` fixed point is exactly
inner-symmetric:

`c1=c8, c2=c7, c3=c6, c4=c5`.

So its digit-frequency vector has the form

`[z, A, B, C, D, D, C, B, A, z+q]`

with:

- `z = c0 >= 1`
- `q = c9-c0 >= 0`
- `A,B,C,D >= 0`.

The branch claim `n in E` is equivalent to proving:

- `A=B=D = k+q`
- `C = d+q`

for some `k>=1`, `d>=0`,

because then the count vector is exactly

`E(z,k,q,d) = [z, k+q, k+q, q+d, k+q, k+q, q+d, k+q, k+q, z+q]`.

---

## Shell pairing from the outside

Assume the basic shell inequalities

- `A >= q`
- `B >= q`
- `C >= q`
- `D > q`.

Then the sorted digit string

`9^(z+q) 8^A 7^B 6^C 5^D 4^D 3^C 2^B 1^A 0^z`

pairs from the outside exactly as follows:

1. `z` outer pairs `9-0`, giving `9^z`
2. the excess `q` copies of `9` pair with `1`, giving `8^q`
3. the remaining `A-q` copies of `8` pair with `1`, giving `7^(A-q)`
4. the remaining `q` copies of `8` pair with `2`, giving `6^q`
5. the remaining `B-q` copies of `7` pair with `2`, giving `5^(B-q)`
6. the remaining `q` copies of `7` pair with `3`, giving `4^q`
7. the remaining `C-q` copies of `6` pair with `3`, giving `3^(C-q)`
8. the remaining `q` copies of `6` pair with `4`, giving `2^q`
9. the remaining `D-q` copies of `5` pair with `4`, giving `1^(D-q)`.

So the induced gap profile is exactly

`g = (9^z, 8^q, 7^(A-q), 6^q, 5^(B-q), 4^q, 3^(C-q), 2^q, 1^(D-q), 0^u)`

for the appropriate trailing-zero count `u`.

This is already the `E` support pattern.

---

## Self-consistency forces the `E` equalities

Now feed that gap profile back through the borrow normal form.

Write:

- `p = q`
- `b = A-q`
- `c = B-q`
- `d = C-q`
- `t = D-q`.

Then the generic tail-`1` count reconstruction gives:

- digit `1`: `p+t = q + (D-q) = D`
- digit `2`: `b+p = (A-q) + q = A`
- digit `3`: `p+d = q + (C-q) = C`
- digit `4`: `c+p = (B-q) + q = B`

and symmetrically on the upper half:

- digit `5`: `B`
- digit `6`: `C`
- digit `7`: `A`
- digit `8`: `D`.

So any self-consistent `(9,1)` profile satisfying the shell inequalities must
reproduce the count vector

`[z, D, A, C, B, B, C, A, D, z+q]`.

But the original fixed point had count vector

`[z, A, B, C, D, D, C, B, A, z+q]`.

Equating these forces:

- `A = D`
- `B = A`
- hence `A = B = D`.

Set

- `k = A-q = B-q = D-q >= 1`
- `d = C-q >= 0`.

Then the count vector is exactly

`E(z,k,q,d)`.

So:

> subject only to the shell inequalities above, every `(9,1)` fixed point is
> automatically an `E`-family point.

---

## Reduction corollary

The remaining theorem work on the `(9,1)` branch is therefore not a full
classification problem anymore.

It has collapsed to one sublemma:

> prove that a `(9,1)` fixed point always satisfies
> `A >= q`, `B >= q`, `C >= q`, and `D > q`.

Once that is shown, the branch is closed:

- shell pairing gives the exact `E` gap pattern,
- self-consistency forces the `E` equalities,
- so `(9,1)` implies `E`.

---

## Computational support

Runner:

- `scripts/kaprekar_e_branch_shell_reduction.py`

Machine output:

- `analysis/base10/e_branch_shell_reduction_2026-04-23.json`

Checked local theorem window:

- all `26,350` canonical base-10 fixed points with lead/tail pair `(9,1)`

Results:

- shell inequality failures: `0`
- induced-gap formula failures: `0`
- `E`-fit failures: `0`

So on the full local `(9,1)` branch, the reduction described in this note is
exact.
