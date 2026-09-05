# Lemma E Case-2 Work Note (v3)

## Goal (corrected)
Case-2 means at least one speed is divisible by `n`.
Target remains:

`x0(E) >= phi(n)`.

(Strict `>` is false: `n=3`, `E=(1,3)` gives equality.)

---

## Setup
Let `E=(e_1,...,e_{n-1})`, `gcd(E)=1`, `L=lcm(E)`, `N=nL`, `q=L/n`.
Write `k=aL+b` with `a in {0,...,n-1}`, `b in {0,...,L-1}`.

Split speeds:
- `E_div = {e in E: e ≡ 0 (mod n)} = {n f_1,...,n f_s}`
- `E_non = E \ E_div`.

Define:
- `B_div = {b : all divisible-speed constraints pass}`
- `A_b = {a : k=aL+b passes all non-divisible constraints}`.

Exact identity:

`x0(E) = sum_{b in B_div} |A_b|`.

---

## New explicit lower bound for `|B_div|`

### Proposition C2.1 (single divisible speed count, exact)
For one divisible speed `e=nf`, define

`S_f = {b mod L : q <= (f b mod L) <= (n-1)q}`.

Then with `d=gcd(f,L)`,

`|S_f| = d * ( floor((n-1)q/d) - ceil(q/d) + 1 )`.

Reason: `f b mod L` visits exactly multiples of `d`, each with multiplicity `d`.

### Corollary C2.2 (explicit intersection lower bound)
For `E_div={nf_1,...,nf_s}`:

`|B_div| = |⋂_i S_{f_i}| >= max(0, sum_i |S_{f_i}| - (s-1)L)`.

(standard first-order Bonferroni on `S`-sets).

### Corollary C2.3 (anchor lower bound)
For anchors `b_j = j q` (`j=1,...,n-1`),
`b_j in B_div` iff `n ∤ f_i j` for all `i`.
So

`|B_div| >= |J|`, where `J={j in {1,...,n-1}: forall i, n ∤ f_i j}`.

Equivalent divisor form:
with `d_i = n / gcd(n,f_i)`,
`j in J` iff `d_i ∤ j` for all `i`.

Hence explicit bound:

`|B_div| >= max(0, n-1 - sum_i floor((n-1)/d_i))`.

In bounded exhaustive scans (`n=3..7` grids already used in Case-2 files),
`min |B_div| = n-1`, and this new explicit LB also attains `n-1` minima.

---

## Uniform lower bound on `|A_b|`

### Proposition C2.4 (uniform fiber bound)
For fixed `b` and one non-divisible speed `e`, let `g=gcd(e,n)`.
Among `a=0,...,n-1`, the number of bad `a` for this speed is at most `2g`.

Therefore:

`|A_b| >= n - 2 * sum_{e in E_non} gcd(e,n)`  for every `b`.

Proof sketch: `a -> { e(aL+b)/(nL) }` is an arithmetic progression on the circle
with spacing `g/n`; each dangerous arc has length `1/n`, so each arc catches at
most one orbit point per cycle, giving at most `2g` bad lifts.

---

## What this does and does not close
The two requested explicit pieces are now in place:
1. explicit `|B_div|` lower bound (C2.2 + C2.3),
2. uniform `|A_b|` lower bound (C2.4).

But C2.4 is often zero on hard tuples (e.g. many low non-divisible speeds), so
`x0 >= |B_div| * (uniform A_b LB)` does not close Case 2 generally.

This is confirmed by the new checker:
- product bound proves all case-2 tuples for `n=3`,
- but only partial coverage for `n=4..7`.

So the remaining step is not `|B_div|`; it is a **non-uniform fiber mass lemma**
(replace global `min_b |A_b|` by a lower bound on aggregate `sum_{b in B_div} |A_b|`,
or prove `|B_safe|>=n-1` directly).

---

## New artifacts
- Script: `/tmp/lrc_case2_c2main_bounds_v1.py`
- Rows: `/tmp/lrc_case2_c2main_bounds_rows_v1.csv`
- Summary: `/tmp/lrc_case2_c2main_bounds_summary_v1.md`

