# Inner Asymmetry Lemma
## Outer-gap / tail-gap control of the nonclassical symmetry split — 2026-04-23

---

## Purpose

The global promotion step is no longer blocked by missing family-internal laws.
What remains is the entrance theorem:

> prove that every base-10 fixed point enters the `P/C/E/O` reduction grammar.

This note isolates one exact structural simplification:

> the entire inner-frequency asymmetry of a fixed point is controlled only by
> the outer gap `alpha = g_1` and the last positive gap `beta = g_m`.

In particular, the classical `6174` chain is the only branch carrying genuine
inner asymmetry. The `495`, `975`, and `864` branches are all exactly
inner-symmetric.

That reduces the global entrance problem to the inner-symmetric branch.

---

## Setup

Let `g = (g_1, ..., g_h)` be the nonincreasing gap profile of a nontrivial
fixed point, with trailing-zero count `r`, positive length `m = h-r`, and
positive tail

`beta = g_m`.

Write

`alpha = g_1`.

Let `N_v` be the multiplicity of the positive gap value `v` among
`g_1, ..., g_m`.

By the borrow normal form, the decimal digits of the fixed point are

### Even

`g_1 ... g_{m-1} (g_m-1) 9^{2r} (9-g_m) (9-g_{m-1}) ... (10-g_1)`

### Odd

`g_1 ... g_{m-1} (g_m-1) 9^{2r+1} (9-g_m) (9-g_{m-1}) ... (10-g_1)`.

The central `9`-block does not affect the counts of digits `1` through `8`, so
the inner-frequency asymmetry is independent of `r` and of parity.

---

## Exact count formula

Fix `x in {1,2,3,4}` and write `c_x` for the digit count of `x` in the fixed
point.

For `x in {1,...,8}`, the count of `x` is:

`c_x = N_x - 1[beta=x] + 1[beta=x+1] + N_{9-x} - 1[alpha=9-x] + 1[alpha=10-x]`.

Reason:

- every positive gap `x` contributes one left digit `x`,
- except the pivot `beta`, which is replaced by `beta-1`,
- every non-outer positive gap `9-x` contributes one right digit `x`,
- and the outer gap contributes `10-alpha` rather than `9-alpha`.

Applying the same formula to `9-x` and subtracting gives:

`c_x - c_{9-x}`

`= 1[alpha=x] - 1[alpha=x+1] - 1[alpha=9-x] + 1[alpha=10-x]`

`  - 1[beta=x] + 1[beta=x+1] + 1[beta=9-x] - 1[beta=10-x]`.

So the full inner asymmetry vector

`A(g) = (c_1-c_8, c_2-c_7, c_3-c_6, c_4-c_5)`

depends only on `(alpha, beta)`.

---

## The four decisive specializations

The current theorem stack already identifies four primitive lead/tail types:

1. `P`: `(alpha,beta) = (5,5)`
2. `C`: `(alpha,beta) = (6,2)`
3. `O`: `(alpha,beta) = (8,2)`
4. `E`: `(alpha,beta) = (9,1)`

Substituting these pairs into the exact formula gives:

### 1. `P`: `(5,5)`

`A(g) = (0,0,0,0)`.

So the full `495` ladder is exactly inner-symmetric.

### 2. `C`: `(6,2)`

`A(g) = (1,-1,-1,1)`.

This is exactly the classical `6174` asymmetry:

- `c1 = c8 + 1`
- `c2 = c7 - 1`
- `c3 = c6 - 1`
- `c4 = c5 + 1`.

### 3. `O`: `(8,2)`

`A(g) = (0,0,0,0)`.

So the entire `864 / +14` branch is exactly inner-symmetric.

### 4. `E`: `(9,1)`

`A(g) = (0,0,0,0)`.

So the paired / odd-lift branch is also exactly inner-symmetric.

---

## Theorem

For any self-consistent fixed-point gap profile whose lead/tail pair is one of

- `(5,5)`
- `(6,2)`
- `(8,2)`
- `(9,1)`

the inner asymmetry vector is forced to be:

- `(0,0,0,0)` in the `P`, `O`, and `E` cases
- `(1,-1,-1,1)` in the `C` case.

Equivalently:

> inside the current grammar, the classical `6174` chain is the unique branch
> carrying genuine inner-frequency asymmetry.

---

## Consequence for the entrance theorem

This lemma does not finish the global promotion step by itself, but it sharpens
it substantially.

The remaining problem is no longer:

> prove every fixed point enters `P/C/E/O`

in one undifferentiated sweep.

It becomes:

1. prove that every base-10 fixed point has lead/tail pair in
   `{(5,5),(6,2),(8,2),(9,1)}`
2. prove the `(9,1)` branch is exactly `E`

because the other three branches are already symbolically closed:

- `(5,5)` -> `P`
- `(6,2)` -> `C`
- `(8,2)` -> `O`.

So the genuinely global entrance problem is now concentrated in one
inner-symmetric branch rather than in the whole grammar at once.

---

## Computational support

Runner:

- `scripts/kaprekar_inner_asymmetry_check.py`

Machine output:

- `analysis/base10/inner_asymmetry_check_2026-04-23.json`

Checked local theorem window:

- `26,664` canonical base-10 fixed points through `d<=150`

Results:

- observed lead/tail pairs:
  - `(5,5)`: `50`
  - `(6,2)`: `74`
  - `(8,2)`: `190`
  - `(9,1)`: `26,350`
- asymmetry mismatches against the exact formula: `0`

So in the current theorem window, every fixed point already sits on one of the
four lead/tail branches above, and the exact asymmetry law matches perfectly.
