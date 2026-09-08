# n = 8, UNIT-COMPLETE, the TWIN case: a complete proof

**Status.** `[PROVED]`. Every admissible `(rho0, rho', q', m)` admits a safe fibre,
hence an integer `b`, hence a loneliness witness. No counterexample exists in this
leaf.

**Scope.** `n = 8`; `E_non` unit-complete with `R_non = {1,3,5,7} u {rho0}`,
`rho0 in {2,4,6}`; `|E_non| = 6`, `|E_div| = 1`; the five base speeds are
representative (`e = rho_e`); the twin is `e' = 8q' + rho'` with `q' >= 1`,
`rho' in R_non`; `E_div = {8m}`, `m >= 1`. So

    E = {1, 3, 5, 7, rho0} u {e'} u {8m},   e' = 8q' + rho',  q' >= 1,  m >= 1.

All seven elements are automatically distinct (`e' >= 9 > 7 >= rho0`, `8m >= 8 > 7`,
`8 does not divide e'`) and `gcd(E) = 1` because `1 in E`. There is no upper bound on
`q'` or `m`; the proof covers the whole infinite family.

**Non-representative base speeds are out of scope** and are handled separately.

**Arithmetic.** Every number in this document and in every script is an exact
`Fraction` or `int`. No floating point enters any decision. Floats appear only in
parenthetical decimal renderings.

---

## 0. What is proved

> **Theorem (Twin case).** For every `rho0 in {2,4,6}`, every `rho' in {1,3,5,7,rho0}`,
> every `q' >= 1` and every `m >= 1`, the set
>
>     Safe = { x in [0,1) : union over e in E of bad(e, floor(e x))  !=  Z/8 }
>
> contains a non-empty half-open interval whose endpoints lie in `(1/L)Z`. By
> INTEGRALITY it therefore contains a point `x = b/L` with `b` an integer in `[0,L)`,
> and `b` is a safe fibre.

The proof is a finite case analysis: six cases indexed by `(rho0, rho')`, each closed
by one of three lemmas, with an explicitly enumerated residual of **179 cells**, every
one of which carries an exhibited witness `x` (Table 3).

---

## 1. Reduction to windows

Write `U(x) = Z/8 minus ( union over e in {1,3,5,7,rho0} of bad(e, floor(e x)) )` for
the uncovered set of the five base runners. Because the base speeds are
representative, `U` depends only on `floor(x), floor(3x), floor(5x), floor(7x),
floor(rho0 x)`, so it is constant on each half-open cell of the partition of `[0,1)`
by the points `j/e`, `e in {1,3,5,7,rho0}`. Table 1 lists those cells exactly.

For the remaining two runners:

* the twin contributes `bad(e', floor(e' x))`. Since
  `bad(e,t) = { r : e r + t = 0 or 7 (mod 8) }` depends on `e` only through `e mod 8`,
  this equals `bad(rho', floor(e' x))`, a set depending only on
  `j := floor(e' x) mod 8`;
* `8m` contributes `Z/8` when `x in B_m` and the empty set otherwise, where

      B_m = { x : ||m x|| < 1/8 }.

  In `killed` form this is exactly the half-open set
  `B_m = union over j of [ (8j-1)/(8m), (8j+1)/(8m) )`, since
  `floor(8m x) mod 8 in {0,7}` iff `{m x} in [0,1/8) u [7/8,1)`. Its components have
  length `1/(4m)`; consecutive components are separated by gaps
  `[ (8j+1)/(8m), (8j+7)/(8m) )` of length `3/(4m)`.

**Window criterion.** Let `W = [alpha, beta)` be an interval and `V` a non-empty
subset of `Z/8` with `V contained in U(x)` for every `x in W`. Put

    J = J(rho', V) = { j in Z/8 : V contained in bad(rho', j) },
    A(c, J)       = { x in [0,1) : floor(c x) mod 8 in J }
                  = union of [t/c, (t+1)/c) over t in [0,c) with t mod 8 in J.

Then every `x in W \ ( A(e', J) u B_m )` is safe.

*Proof.* Let `x` be such a point. Since `floor(e' x) mod 8 is not in J`, we have
`V not contained in bad(rho', floor(e' x))`, so some `r in V` escapes the twin. That
`r` lies in `U(x)`, so it escapes all five base runners. And `x not in B_m`, so the
runner `8m` kills nothing at `x`. Hence `r` is uncovered by every `e in E`. `[]`

The criterion is a **sufficient** condition, deliberately: taking `V` smaller than the
full `U` enlarges `J` and only makes the criterion harder, but it lets one window
serve a whole interval on which `U` varies. The identity version (using the exact `U`
on every cell) is implemented in `twin3_window.py` and was checked against the
brute-force cell decomposition of the full seven-runner set on 1440 tuples with zero
mismatches.

**Integrality of the endpoints.** Every endpoint appearing below is one of
`alpha, beta` (denominators `1,3,4,5,6,7`, all dividing `L` because
`1,3,5,7,rho0 in E` and `4 | 8m | L`), `t/c` with `c = e' | L`, or `(8j+-1)/(8m)` with
`8m | L`. All lie in `(1/L)Z`. `W`, `A` and `B_m` are all finite unions of half-open intervals
`[.,.)`, and removing a half-open `[a,b)` from a half-open `[u,v)` leaves
`[u, a) u [b, v)`, again half-open. So `W \ (A u B_m)` is a finite union of intervals
`[u, v)` with `u, v in (1/L)Z`, and whenever it is non-empty its left endpoint `u = b/L`
is itself a witness with `b` an integer. No rounding term is ever needed.

---

## 2. Lemma 1 (shape of `J`)

> **Lemma 1.** For every `rho' in {1,...,7}` and every non-empty `V` contained in `Z/8`,
> the set `J(rho', V)` is empty, a singleton, or a pair of **cyclically adjacent**
> residues. In particular `|J| <= 2` always.

*Proof.* Write `bad(e,t) = { r : e r = -t or -t-1 (mod 8) }`.

**(a) `rho'` odd.** Then `rho'^2 = 1 (mod 8)`, so `rho'` is its own inverse and
`bad(rho', j) = { -j rho', -(j+1) rho' }`, a pair whose two elements differ by `rho'`.
If `V = {a}` then `a in bad(rho', j)` iff `j = -a rho'` or `j = -a rho' - 1`: two
cyclically adjacent values, `|J| = 2`. If `V = {a,b}` with `a != b`, then
`V contained in bad` forces `V = bad(rho', j)`, hence `b - a = +- rho'`; the two signs
cannot both hold because that would give `2 rho' = 0 (mod 8)`, impossible for odd
`rho'`. So `|J| <= 1`. If `|V| >= 3` then `J` is empty.

**(b) `rho' in {2,6}`,** i.e. `gcd(rho',8) = 2`. Exactly one of `-j, -j-1` is even; call
it `c_j`. Then `bad(rho', j) = { r : rho' r = c_j (mod 8) }`, which is a coset of
`{0,4}` of size 2, determined by `c_j`. The map `j -> c_j` is

    j  = 0 1 2 3 4 5 6 7
    c_j= 0 6 6 4 4 2 2 0

so each even value has exactly two preimages and they are cyclically adjacent
(`0 <- {7,0}`, `6 <- {1,2}`, `4 <- {3,4}`, `2 <- {5,6}`). Hence `J` is either empty or
one of those four adjacent pairs.

**(c) `rho' = 4`.** `4r in {0,4}`, so `bad(4,j)` is the evens when `c_j = 0`
(`j in {7,0}`), the odds when `c_j = 4` (`j in {3,4}`), and empty when `c_j in {2,6}`.
Both preimage sets are cyclically adjacent pairs. `[]`

Verified by exhaustion over all `7 x 255` pairs `(rho', V)` in `twin3_jshape.py`:
1667 empty, 32 singleton, 86 adjacent pair, **0 violations**.

---

## 3. Lemma 2 (geometry of `A` and `B_m`)

Let `kappa = |J| in {0,1,2}` with `J` a cyclic block (Lemma 1). Then:

* **Components of `A(c,J)`** are maximal runs of consecutive integers `t in [0,c)` with
  `t mod 8 in J`. Since `J` is a cyclic block of size `kappa <= 2`, such a run has at
  most `kappa` terms, so every component has length **at most `kappa/c <= 2/c`**.
* **Gaps.** Writing `J = {j0, ..., j0+kappa-1}` cyclically, for every integer
  `t = j0 + kappa (mod 8)` the `8 - kappa` integers `t, t+1, ..., t + 7 - kappa` have
  residues `j0+kappa, ..., j0+7`, none in `J`. Hence

      [ t/c , (t + 8 - kappa)/c )  is disjoint from A(c,J),   length (8-kappa)/c >= 6/c.

  Consecutive components of `A` are therefore separated by a positive gap, so **any
  interval contained in `A` lies inside a single component**, and has length `<= 2/c`.
* **`B_m`**: components of length `1/(4m)`, separated by gaps of length `3/(4m)`. Any
  interval contained in `B_m` has length `<= 1/(4m)`.
* **Closed form.** With `e' = 8q' + rho'` and `s = #{ j in J : j < rho' }`,

      |A(e', J)| = ( kappa q' + s ) / ( 8 q' + rho' ) ,       |B_m| = 1/4 exactly.

  (Verified against direct computation for all `rho' in [1,7]`, `q' in [1,40)` and
  seven representative `J`, in `twin3_quarterbound.py`.)

---

## 4. Lemma 3 (the gap lemma)

> **Lemma 3.** Let `W = [alpha, beta)` be contained in `[0,1)`, `ell = beta - alpha`,
> `J` a cyclic block with `kappa = |J| in {1,2}`, `c >= 1`, `m >= 1`. If
>
>     ell >= 15/c      and      ell >= 7/(4m),
>
> then `W` is **not** contained in `A(c,J) u B_m`.

*Proof.* Suppose `W` is contained in `A u B_m`.

**(i) A long `A`-free interval inside `W`.** By Lemma 2 the interval
`I_t = [ t/c, (t + 8 - kappa)/c )` misses `A` whenever `t = j0 + kappa (mod 8)`. We need
such a `t` with `alpha <= t/c` and `(t + 8 - kappa)/c <= beta`, i.e.
`t in [ alpha c, beta c - (8-kappa) ]`. That real interval has length
`ell c - (8 - kappa) >= 15 - (8 - kappa) = 7 + kappa >= 8`, and any real interval of
length `>= 8` contains 8 consecutive integers, hence one in every residue class mod 8.
The chosen `t` satisfies `t >= alpha c >= 0` and `t + 8 - kappa <= beta c <= c`, so
`I_t` is a genuine subinterval of `W`, of length `(8-kappa)/c >= 6/c`, disjoint from
`A`. Since `W` is contained in `A u B_m`, we get `I_t` contained in `B_m`, and Lemma 2
forces

     (8 - kappa)/c <= 1/(4m)     hence     c >= 4m(8 - kappa) >= 24 m.          (1)

**(ii) A long `B_m`-free interval inside `W`.** The interval
`G_j = [ (8j+1)/(8m), (8j+7)/(8m) )` misses `B_m` and has length `3/(4m)`. We need `j`
with `alpha <= (8j+1)/(8m)` and `(8j+7)/(8m) <= beta`, i.e.
`j in [ alpha m - 1/8, beta m - 7/8 ]`, a real interval of length
`ell m - 3/4 >= 7/4 - 3/4 = 1`, which contains an integer. That `j` satisfies
`j >= alpha m - 1/8 >= -1/8`, so `j >= 0`, and `8j + 7 <= 8 beta m <= 8m`, so
`G_j` is contained in `[0,1)`. Since `W` is contained in `A u B_m`, `G_j` is contained
in `A`, and Lemma 2 forces

     3/(4m) <= kappa/c <= 2/c     hence     3c <= 8m.                           (2)

**(iii)** Combining (1) and (2): `24 m <= c <= 8m/3`, so `72 m <= 8 m`, so `m <= 0`.
Contradiction. `[]`

Set

    C1 = ceil(15 / ell)        (c >= C1 gives the first hypothesis)
    M1 = ceil(7 / (4 ell))     (m >= M1 gives the second)

so Lemma 3 settles every `(c,m)` with `c >= C1` **and** `m >= M1`.

---

## 5. Lemmas 4 and 5 (the two residual strips)

> **Lemma 4 (small `e'`).** Fix `c`. Let `mu(c)` be the largest length of a component
> of `W \ A(c,J)`. If `4 m mu(c) > 1` then `W \ (A u B_m)` is non-empty.

*Proof.* That component `I` is disjoint from `A` and has `|I| > 1/(4m)`, so by Lemma 2
it is not contained in `B_m`. Any point of `I \ B_m` works. `[]`

> **Lemma 5 (small `m`).** Fix `m`. Let `lam(m)` be the largest length of a component
> of `W \ B_m`. If `c lam(m) > kappa` then `W \ (A u B_m)` is non-empty.

*Proof.* That component `I` is disjoint from `B_m` and has `|I| > kappa/c`, so by
Lemma 2 it is not contained in `A`. `[]`

**Residual.** A pair `(c,m)` survives all three lemmas only if

    ( c < C1  and  m <= floor( 1 / (4 mu(c)) ) )   or   ( m < M1  and  c <= floor( kappa / lam(m) ) ),

a finite set, because `mu(c) > 0` and `lam(m) > 0` in every case below (verified, and
the code raises if either vanishes). Tables 2 and 3 list `mu`, `lam`, the resulting
residual, and an explicit witness for every residual cell.

---

## 6. The six cases

`c = e' = 8q' + rho'` runs over the arithmetic progression `rho' + 8Z` with `c >= 8 + rho'`.

| case | `rho0` | `rho'` | window `W` | `ell` | `V` | `J` | `kappa` | closed by |
|---|---|---|---|---|---|---|---|---|
| A | 2 | 1,3,5,7 | `[0, 1/7)` | `1/7` | `{2,6}` | empty | 0 | `J` empty; `m <= 1` |
| B | 2 | 2 | `[0, 1/5)` | `1/5` | `{6}` | `{3,4}` | 2 | Lemmas 3,4,5 + 27 cells |
| C | 4 | 1,7,4 | `[2/7, 2/5)` | `4/35` | `{1,4}` | empty | 0 | `J` empty; `m <= 2` |
| D | 4 | 3,5 | `[2/7, 2/5)` | `4/35` | `{1,4}` | `{4}` / `{3}` | 1 | Lemmas 3,4,5 + 63 / 56 cells |
| E | 6 | 1,3,5,7 | `[0, 1/7)` | `1/7` | `{2,6}` | empty | 0 | `J` empty; `m <= 1` |
| F | 6 | 6 | `[1/6, 1/5)` | `1/30` | `{4,6}` | empty | 0 | `J` empty; `m <= 7` |

Every `(rho0, rho')` pair occurs in exactly one row, so the six cases are exhaustive:
`3 x 5 = 15` pairs, distributed `4 + 1 + 3 + 2 + 4 + 1`.

The `V` column is legitimate in each row by Table 1:

* A, E: `U = {2,6}` throughout `[0,1/7)`.
* B: `U = {2,6}` on `[0,1/7)` and `U = {6}` on `[1/7,1/5)`, so `6 in U` throughout `[0,1/5)`.
* C, D: `U = {1,4}` throughout `[2/7,2/5)`.
* F: `U = {4,6}` throughout `[1/6,1/5)`.

The `J` column follows from Lemma 1's description; it is also printed, window by window, by
`twin3_jtable.py`.

### 6.1 Cases A, C, E, F (`J` empty)

Here the twin can never kill `W`, so `x in W \ B_m` is safe for every `e'`. By Lemma 2
any interval contained in `B_m` has length `<= 1/(4m)`, so

    W contained in B_m   implies   ell <= 1/(4m)   implies   m <= 1/(4 ell).

* A, E: `ell = 1/7`, so `m <= 7/4`, i.e. `m = 1`. And `W \ B_1 = [1/8, 1/7)`, non-empty.
* C: `ell = 4/35`, so `m <= 35/16`, i.e. `m in {1,2}`. `B_1` and `B_2` are both disjoint
  from `[2/7,2/5)` (`B_2 = [0,1/16) u [7/16,9/16) u [15/16,1)` and `2/5 < 7/16`), so
  `W \ B_m = W`.
* F: `ell = 1/30`, so `m <= 15/2`, i.e. `m <= 7`; `W \ B_m` is non-empty for each.

Table 3 tabulates `W \ B_m` up to `ceil(1/(4 ell))`, which is one value of `m` past the
bound in each row: `m <= 2` for A and E (bound `m = 1`), `m <= 3` for C (bound `m = 2`),
`m <= 8` for F (bound `m = 7`). The extra row is harmless and is left in as a margin
check.

These four cases are therefore closed for **all** `q' >= 1` and **all** `m >= 1`.

### 6.2 Case B (`rho0 = 2`, `rho' = 2`)

`ell = 1/5`, `kappa = 2`, so `C1 = ceil(75) = 75` and `M1 = ceil(35/4) = 9`. Lemma 3
closes every `(e', m)` with `e' >= 75` and `m >= 9`; since `e' = 2 (mod 8)` this means
`e' >= 82`. The residual computed from Lemmas 4 and 5 is 27 cells, all with witnesses
(Table 3). Largest residual `e'` is 74; largest residual `m` is 8.

### 6.3 Case D (`rho0 = 4`, `rho' in {3,5}`)

This is the case the brief flags as hard, and it is where `V` must be `{1,4}` rather
than `{4}`.

By Lemma 1(a), for `V = {1,4}` and odd `rho'`, `J` is non-empty only if
`4 - 1 = +-rho' (mod 8)`, i.e. `rho' in {3,5}`; and then `|J| = 1`:

* `rho' = 3`: `4 - 1 = 3 = rho'`, so `j = -4 rho' = -12 = 4`, giving `J = {4}`.
* `rho' = 5`: `1 - 4 = -3 = 5 = rho'`, so `j = -1 rho' = -5 = 3`, giving `J = {3}`.

For `rho' in {1,7,4}` no `j` works and `J` is empty -- that is case C. So the brief's
prediction is exactly right: **only `rho' in {3,5}` can kill both residues on
`[2/7,2/5)`, and it pins `floor(e' x) mod 8` to a single value**, giving `kappa = 1`
and hence `A`-components of length `1/e'` and `A`-gaps of length `7/e'`.

`ell = 4/35`, `kappa = 1`, so `C1 = ceil(525/4) = 132` and `M1 = ceil(245/16) = 16`.
Lemma 3 closes every `(e', m)` with `e' >= 132` and `m >= 16`. The residual is 63 cells
for `rho' = 3` and 56 for `rho' = 5`, all with witnesses (Table 3).

**A wider window would not do.** The obvious alternative is `W = [1/4, 3/7)` with
`V = {4}` (length `5/28`, `J = {3,4}`, `kappa = 2`), which gives smaller `C1 = 84` and
`M1 = 10`. It fails at exactly one residual cell, `(e', m) = (11, 4)`, i.e.
`E = {1,3,4,5,7,11,32}` -- the tuple named in the brief's warning. On that window the
residue `4` really is killed on all of `[1/4,3/7)`. The fine window recovers it: at
`x = 2/7` the residue `1` survives, and

    E = {1,3,4,5,7,11,32},  L = 36960,  x = 2/7,  b = 10560,  r = 1,  k = b + rL = 47520,
    min over e in E of || e k / (8L) || = 1/8   exactly.

On the fine window the cell `(e',m) = (11,4)` is not even residual: `J = {4}` gives
`A(11,{4}) = [4/11, 5/11)`, so `W \ A = [2/7, 4/11)` and

    mu(11) = 4/11 - 2/7 = 6/77,     1/(4 mu(11)) = 77/24 = 3.208...,

so Lemma 4 settles every `m >= 4`, `m = 4` included. The surviving interval `[2/7, 4/11)`
is exactly the interval on which the brief reports that residue `1` survives.

This is the concrete reason the case must be run on `V = {1,4}`, and it is the same
error the brief warns against.

---

## 7. Mirror symmetry

For `x` with `e x` not an integer, `floor(e(1-x)) = e - 1 - floor(e x)`, and

    bad(e, e-1-t) = { -s-1 : s in bad(e,t) } = sigma( bad(e,t) ),   sigma(r) = -1-r.

*Proof.* `r in bad(e, e-1-t)` iff `e r = t+1-e` or `t-e`, iff `e(r+1) = t+1` or `t`.
Put `s = -(r+1)`; then `e(r+1) = -e s`, and the condition reads `e s = -t-1` or `-t`,
i.e. `s in bad(e,t)`. `[]`

`sigma` is the involution `0<->7, 1<->6, 2<->5, 3<->4`. `B_m` is invariant under
`x -> 1-x`, and `A(e', J)` maps to `A(e', rho' - 1 - J)`. Hence the whole configuration
is mirror-symmetric, and the mirror windows (`[6/7,1)` for A/E, `[4/5,1)` for B,
`[3/5,5/7)` for C/D, `[4/5,5/6)` for F) carry no information beyond their partners.
Table 1 exhibits the symmetry directly: e.g. for `rho0 = 4`, `[1/4,2/7) -> {4}` mirrors
`[5/7,3/4) -> {3} = sigma({4})`, and `[2/7,2/5) -> {1,4}` mirrors
`[3/5,5/7) -> {3,6} = sigma({1,4})`.

---

## 8. Two corrections to the suggested route

**(1) "The twin's kill set has measure at most 1/4" is false.** By the closed form of
Lemma 2, `|A(e',J)| = (kappa q' + s)/(8 q' + rho')` with `s = #{ j in J : j < rho' }`,
and this exceeds `1/4` exactly when `4 s > rho'`. Among the `(rho0, rho', V)` triples
that actually occur here, the maximum over `q' = 1..2000` is

    |A(13, {1,2})| = 4/13 = 0.30769...  >  1/4,      at rho0 = 2, rho' = 5, q' = 1, V = {6}.

The true twin kill set `K = union over V of ( W_V intersect A(e', J_V) )` also breaks
`1/4`: its maximum over `q' = 1..300` is `86/315 = 0.2730...` at
`(rho0, rho') = (2,2)`, `q' = 2`, `e' = 18`. So step 1 of the suggested route does not
close as stated. `[VERIFIED-scope]` -- exact, `q'` ranges as given,
`twin3_quarterbound.py`.

**(2) The union bound is negative for `rho0 = 4`, as expected, but the margin for
`rho0 = 2` is thin and unproved.** Exact values of `|S| - max|K| - 1/4` over
`q' = 1..300`:

| `rho0` | `rho'` | `max |K|` | `|S| - max|K| - 1/4` |
|---|---|---|---|
| 2 | 1 | `96/595` | `+517/2380` |
| 2 | 3 | `8/35` | `+3/20` |
| 2 | 5 | `72/455` | `+401/1820` |
| 2 | 7 | `164/1085` | `+141/620` |
| 2 | 2 | `86/315` | `+19/180` |
| 4 | 1 | `43/490` | `+19/980` |
| 4 | 3 | `12/77` | `-15/308` |
| 4 | 5 | `3/26` | `-3/364` |
| 4 | 7 | `67/658` | `+1/188` |
| 4 | 4 | `1/10` | `+1/140` |
| 6 | 1 | `5/21` | `+31/84` |
| 6 | 3 | `24/77` | `+13/44` |
| 6 | 5 | `97/273` | `+275/1092` |
| 6 | 7 | `4/15` | `+143/420` |
| 6 | 6 | `4/15` | `+143/420` |

The `rho0 = 4` rows are negative, confirming that measure alone cannot close that case.
The positive rows are a bounded computation over `q' <= 300`, not a proof for all `q'`.
**The proof above uses no measure bound at all**, so neither issue affects it.

---

## 9. Controls

The lemmas are only useful if true, so each was tested on the region where it claims to
apply (`twin3_audit.py`): **39 968 instances, 0 violations**.

| control | region tested | instances | violations |
|---|---|---|---|
| Lemma 3 | `c >= C1`, `m >= M1`, 40 x 40 grid per case | -- | 0 |
| Lemma 4 | `c < C1`, `4 m mu(c) > 1` | -- | 0 |
| Lemma 5 | `m < M1`, `c lam(m) > kappa` | -- | 0 |
| window identity vs brute force | 1440 full seven-runner tuples | 1440 | 0 |
| Lemma 1 by exhaustion | all `7 x 255` pairs `(rho', V)` | 1785 | 0 |
| Table 1, independent recomputation | pure integer enumeration over `b in [0, L_base)`, `L_base = 210, 420, 210`; no `Fraction`, no interval algebra | 840 fibres | 0 |
| residual witnesses vs full `E` | all 179 cells, uncovered set of all 7 runners | 179 | 0 |
| BRIDGE end-to-end | all 179 cells: `b = xL`, `k = b + rL`, `min_e ||ek/(8L)|| >= 1/8` | 179 | 0 |

Independent sweeps of the exact safe measure of the full seven-runner set, all 15
`(rho0, rho')` pairs:

| sweep | range | tuples | empty safe sets |
|---|---|---|---|
| `twin3_sweep2.py` | `q' <= 60`, `m <= 60` | 54 000 | 0 |
| `twin3_stress.py` | `q', m` each in `1..12 u 280..300` (mixes a very fine `A` with a very coarse `B_m` and vice versa, straddling the `C1`/`M1` thresholds) | 16 335 | 0 |

Smallest safe measure seen in either sweep: `53/924 = 0.05736...` at
`E = {1,3,4,5,7,11,24}` (`rho0 = 4`, `rho' = 3`, `q' = 1`, `m = 3`).
`[VERIFIED-scope]` -- exact, ranges as given. These are controls, not the proof; the
proof is unbounded in `q'` and `m`, and it asserts non-emptiness only, not any measure
lower bound.

---

## 10. Scripts

All under `experiments/n8/`, all exact `Fraction`/`int`:

| file | role |
|---|---|
| `twin3_core.py` | `bad`, interval algebra, `A(c,K)`, `B_m`, `J(rho',V)` |
| `twin3_window.py` | window engine + identity check against brute force |
| `twin3_jtable.py` | the `(rho0, rho', window) -> J` table |
| `twin3_jshape.py` | Lemma 1 by exhaustion |
| `twin3_table1_independent.py` | Table 1 recomputed by integer enumeration in `b`-coordinates |
| `twin3_decide.py` | the case machine: `C1`, `M1`, residual enumeration, direct check |
| `twin3_certificate.py` | residual witnesses + full seven-runner audit (`twin3_certificate.out`) |
| `twin3_bridge_check.py` | end-to-end BRIDGE control on every witness |
| `twin3_audit.py` | controls on Lemmas 3, 4, 5 in their own regions |
| `twin3_quarterbound.py` | the `1/4` premise and the union-bound margins |
| `twin3_sweep.py`, `twin3_sweep2.py`, `twin3_stress.py` | independent sweeps of the full seven-runner safe measure |
| `twin3_report_tables.py` | emits Tables 1-3 (`twin3_tables.md`) |

Reproduce: `python3 twin3_decide.py && python3 twin3_audit.py && python3 twin3_bridge_check.py`.

---

## 11. What is not settled here

* Non-representative base speeds (some base `e != rho_e`). Out of scope by assumption;
  the window criterion of Section 1 still applies, but Table 1 changes, so the case
  table must be recomputed.
* `|E_non| = 6` with two classes carrying two speeds each, or `|E_div| >= 2`. Different
  leaves.
* Nothing here proves a positive lower bound on the safe measure; the theorem is
  non-emptiness only.

---

## Table 1 - base-five uncovered sets

**rho0 = 2**  (breakpoint denominators divide lcm(1,3,5,7,2))

| window | length | U (uncovered by {1,3,5,7,rho0}) |
|---|---|---|
| [0, 1/7) | 1/7 | [2, 6] |
| [1/7, 1/5) | 2/35 | [6] |
| [1/5, 2/7) | 3/35 | empty |
| [2/7, 2/5) | 4/35 | [1] |
| [2/5, 3/5) | 1/5 | empty |
| [3/5, 5/7) | 4/35 | [6] |
| [5/7, 4/5) | 3/35 | empty |
| [4/5, 6/7) | 2/35 | [1] |
| [6/7, 1) | 1/7 | [1, 5] |

**rho0 = 4**  (breakpoint denominators divide lcm(1,3,5,7,4))

| window | length | U (uncovered by {1,3,5,7,rho0}) |
|---|---|---|
| [0, 1/4) | 1/4 | empty |
| [1/4, 2/7) | 1/28 | [4] |
| [2/7, 2/5) | 4/35 | [1, 4] |
| [2/5, 3/7) | 1/35 | [4] |
| [3/7, 4/7) | 1/7 | empty |
| [4/7, 3/5) | 1/35 | [3] |
| [3/5, 5/7) | 4/35 | [3, 6] |
| [5/7, 3/4) | 1/28 | [3] |
| [3/4, 1) | 1/4 | empty |

**rho0 = 6**  (breakpoint denominators divide lcm(1,3,5,7,6))

| window | length | U (uncovered by {1,3,5,7,rho0}) |
|---|---|---|
| [0, 1/7) | 1/7 | [2, 6] |
| [1/7, 1/6) | 1/42 | [6] |
| [1/6, 1/5) | 1/30 | [4, 6] |
| [1/5, 3/7) | 8/35 | [4] |
| [3/7, 4/7) | 1/7 | empty |
| [4/7, 4/5) | 8/35 | [3] |
| [4/5, 5/6) | 1/30 | [1, 3] |
| [5/6, 6/7) | 1/42 | [1] |
| [6/7, 1) | 1/7 | [1, 5] |


## Table 2 - mu(c) and lam(m)

**[B] rho0=2, rho'=2**  W=[0,1/5), ell=1/5, J=[3, 4], kappa=2, C1=75, M1=9

| c = e' | mu(c) | Lemma B settles m > | residual m |
|---|---|---|---|
| 10 | 1/5 | 5/4 | 1..1 |
| 18 | 1/6 | 3/2 | 1..1 |
| 26 | 3/26 | 13/6 | 1..2 |
| 34 | 3/34 | 17/6 | 1..2 |
| 42 | 17/210 | 105/34 | 1..3 |
| 50 | 1/10 | 5/2 | 1..2 |
| 58 | 3/29 | 29/12 | 1..2 |
| 66 | 1/11 | 11/4 | 1..2 |
| 74 | 3/37 | 37/12 | 1..3 |

| m | lam(m) | Lemma C settles c > | residual c |
|---|---|---|---|
| 1 | 3/40 | 80/3 | [10, 18, 26] |
| 2 | 11/80 | 160/11 | [10] |
| 3 | 19/120 | 240/19 | [10] |
| 4 | 27/160 | 320/27 | [10] |
| 5 | 3/20 | 40/3 | [10] |
| 6 | 1/8 | 16 | [10] |
| 7 | 3/28 | 56/3 | [10, 18] |
| 8 | 3/32 | 64/3 | [10, 18] |

**[D] rho0=4, rho'=3**  W=[2/7,2/5), ell=4/35, J=[4], kappa=1, C1=132, M1=16

| c = e' | mu(c) | Lemma B settles m > | residual m |
|---|---|---|---|
| 11 | 6/77 | 77/24 | 1..3 |
| 19 | 4/35 | 35/16 | 1..2 |
| 27 | 4/35 | 35/16 | 1..2 |
| 35 | 2/35 | 35/8 | 1..4 |
| 43 | 21/215 | 215/84 | 1..2 |
| 51 | 38/357 | 357/152 | 1..2 |
| 59 | 22/413 | 413/88 | 1..4 |
| 67 | 29/335 | 335/116 | 1..2 |
| 75 | 46/525 | 525/184 | 1..2 |
| 83 | 30/581 | 581/120 | 1..4 |
| 91 | 1/13 | 13/4 | 1..3 |
| 99 | 7/99 | 99/28 | 1..3 |
| 107 | 29/535 | 535/116 | 1..4 |
| 115 | 7/115 | 115/28 | 1..4 |
| 123 | 7/123 | 123/28 | 1..4 |
| 131 | 7/131 | 131/28 | 1..4 |

| m | lam(m) | Lemma C settles c > | residual c |
|---|---|---|---|
| 1 | 4/35 | 35/4 | none |
| 2 | 4/35 | 35/4 | none |
| 3 | 1/40 | 40 | [11, 19, 27, 35] |
| 4 | 4/35 | 35/4 | none |
| 5 | 5/56 | 56/5 | [11] |
| 6 | 11/240 | 240/11 | [11, 19] |
| 7 | 27/280 | 280/27 | none |
| 8 | 33/448 | 448/33 | [11] |
| 9 | 19/360 | 360/19 | [11] |
| 10 | 3/40 | 40/3 | [11] |
| 11 | 41/616 | 616/41 | [11] |
| 12 | 9/160 | 160/9 | [11] |
| 13 | 3/52 | 52/3 | [11] |
| 14 | 3/56 | 56/3 | [11] |
| 15 | 1/20 | 20 | [11, 19] |

**[D] rho0=4, rho'=5**  W=[2/7,2/5), ell=4/35, J=[3], kappa=1, C1=132, M1=16

| c = e' | mu(c) | Lemma B settles m > | residual m |
|---|---|---|---|
| 13 | 6/65 | 65/24 | 1..2 |
| 21 | 4/35 | 35/16 | 1..2 |
| 29 | 19/203 | 203/76 | 1..2 |
| 37 | 14/185 | 185/56 | 1..3 |
| 45 | 4/35 | 35/16 | 1..2 |
| 53 | 27/371 | 371/108 | 1..3 |
| 61 | 22/305 | 305/88 | 1..3 |
| 69 | 7/69 | 69/28 | 1..2 |
| 77 | 5/77 | 77/20 | 1..3 |
| 85 | 6/85 | 85/24 | 1..3 |
| 93 | 7/93 | 93/28 | 1..3 |
| 101 | 43/707 | 707/172 | 1..4 |
| 109 | 7/109 | 109/28 | 1..3 |
| 117 | 7/117 | 117/28 | 1..4 |
| 125 | 7/125 | 125/28 | 1..4 |

| m | lam(m) | Lemma C settles c > | residual c |
|---|---|---|---|
| 1 | 4/35 | 35/4 | none |
| 2 | 4/35 | 35/4 | none |
| 3 | 1/40 | 40 | [13, 21, 29, 37] |
| 4 | 4/35 | 35/4 | none |
| 5 | 5/56 | 56/5 | none |
| 6 | 11/240 | 240/11 | [13, 21] |
| 7 | 27/280 | 280/27 | none |
| 8 | 33/448 | 448/33 | [13] |
| 9 | 19/360 | 360/19 | [13] |
| 10 | 3/40 | 40/3 | [13] |
| 11 | 41/616 | 616/41 | [13] |
| 12 | 9/160 | 160/9 | [13] |
| 13 | 3/52 | 52/3 | [13] |
| 14 | 3/56 | 56/3 | [13] |
| 15 | 1/20 | 20 | [13] |


## Table 3 - residual cells with witnesses

**[A] rho0=2, rho'=1**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[A] rho0=2, rho'=3**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[A] rho0=2, rho'=5**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[A] rho0=2, rho'=7**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[B] rho0=2, rho'=2**
residual cells: 27

| e' | q' | m | witness x | E | uncovered by all 7 |
|---|---|---|---|---|---|
| 10 | 1 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 10) | [2, 6] |
| 10 | 1 | 2 | 1/16 | (1, 2, 3, 5, 7, 10, 16) | [2, 6] |
| 10 | 1 | 3 | 1/24 | (1, 2, 3, 5, 7, 10, 24) | [2, 6] |
| 10 | 1 | 4 | 1/32 | (1, 2, 3, 5, 7, 10, 32) | [2, 6] |
| 10 | 1 | 5 | 1/40 | (1, 2, 3, 5, 7, 10, 40) | [2, 6] |
| 10 | 1 | 6 | 1/48 | (1, 2, 3, 5, 7, 10, 48) | [2, 6] |
| 10 | 1 | 7 | 1/56 | (1, 2, 3, 5, 7, 10, 56) | [2, 6] |
| 10 | 1 | 8 | 1/64 | (1, 2, 3, 5, 7, 10, 64) | [2, 6] |
| 18 | 2 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 18) | [2, 6] |
| 18 | 2 | 7 | 1/56 | (1, 2, 3, 5, 7, 18, 56) | [2, 6] |
| 18 | 2 | 8 | 1/64 | (1, 2, 3, 5, 7, 18, 64) | [2, 6] |
| 26 | 3 | 1 | 5/26 | (1, 2, 3, 5, 7, 8, 26) | [6] |
| 26 | 3 | 2 | 1/16 | (1, 2, 3, 5, 7, 16, 26) | [2, 6] |
| 34 | 4 | 1 | 5/34 | (1, 2, 3, 5, 7, 8, 34) | [6] |
| 34 | 4 | 2 | 1/16 | (1, 2, 3, 5, 7, 16, 34) | [2, 6] |
| 42 | 5 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 42) | [2, 6] |
| 42 | 5 | 2 | 1/16 | (1, 2, 3, 5, 7, 16, 42) | [2, 6] |
| 42 | 5 | 3 | 1/24 | (1, 2, 3, 5, 7, 24, 42) | [2, 6] |
| 50 | 6 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 50) | [2, 6] |
| 50 | 6 | 2 | 1/10 | (1, 2, 3, 5, 7, 16, 50) | [2, 6] |
| 58 | 7 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 58) | [2, 6] |
| 58 | 7 | 2 | 5/58 | (1, 2, 3, 5, 7, 16, 58) | [2, 6] |
| 66 | 8 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 66) | [2, 6] |
| 66 | 8 | 2 | 5/66 | (1, 2, 3, 5, 7, 16, 66) | [2, 6] |
| 74 | 9 | 1 | 1/8 | (1, 2, 3, 5, 7, 8, 74) | [2, 6] |
| 74 | 9 | 2 | 5/74 | (1, 2, 3, 5, 7, 16, 74) | [2, 6] |
| 74 | 9 | 3 | 5/74 | (1, 2, 3, 5, 7, 24, 74) | [2, 6] |

**[C] rho0=4, rho'=1**
J is empty, so the twin never kills W; W subset B_m forces m <= 3.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [2/7, 2/5) | 2/7 |
| 2 | [2/7, 2/5) | 2/7 |
| 3 | [2/7, 7/24) u [3/8, 2/5) | 2/7 |

**[C] rho0=4, rho'=7**
J is empty, so the twin never kills W; W subset B_m forces m <= 3.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [2/7, 2/5) | 2/7 |
| 2 | [2/7, 2/5) | 2/7 |
| 3 | [2/7, 7/24) u [3/8, 2/5) | 2/7 |

**[C] rho0=4, rho'=4**
J is empty, so the twin never kills W; W subset B_m forces m <= 3.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [2/7, 2/5) | 2/7 |
| 2 | [2/7, 2/5) | 2/7 |
| 3 | [2/7, 7/24) u [3/8, 2/5) | 2/7 |

**[D] rho0=4, rho'=3**
residual cells: 63

| e' | q' | m | witness x | E | uncovered by all 7 |
|---|---|---|---|---|---|
| 11 | 1 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 11) | [1] |
| 11 | 1 | 2 | 2/7 | (1, 3, 4, 5, 7, 11, 16) | [1] |
| 11 | 1 | 3 | 2/7 | (1, 3, 4, 5, 7, 11, 24) | [1] |
| 11 | 1 | 5 | 2/7 | (1, 3, 4, 5, 7, 11, 40) | [1] |
| 11 | 1 | 6 | 2/7 | (1, 3, 4, 5, 7, 11, 48) | [1] |
| 11 | 1 | 8 | 2/7 | (1, 3, 4, 5, 7, 11, 64) | [1] |
| 11 | 1 | 9 | 2/7 | (1, 3, 4, 5, 7, 11, 72) | [1] |
| 11 | 1 | 10 | 2/7 | (1, 3, 4, 5, 7, 11, 80) | [1] |
| 11 | 1 | 11 | 2/7 | (1, 3, 4, 5, 7, 11, 88) | [1] |
| 11 | 1 | 12 | 2/7 | (1, 3, 4, 5, 7, 11, 96) | [1] |
| 11 | 1 | 13 | 2/7 | (1, 3, 4, 5, 7, 11, 104) | [1] |
| 11 | 1 | 14 | 33/112 | (1, 3, 4, 5, 7, 11, 112) | [1] |
| 11 | 1 | 15 | 2/7 | (1, 3, 4, 5, 7, 11, 120) | [1] |
| 19 | 2 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 19) | [4] |
| 19 | 2 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 19) | [4] |
| 19 | 2 | 3 | 2/7 | (1, 3, 4, 5, 7, 19, 24) | [4] |
| 19 | 2 | 6 | 2/7 | (1, 3, 4, 5, 7, 19, 48) | [4] |
| 19 | 2 | 15 | 2/7 | (1, 3, 4, 5, 7, 19, 120) | [4] |
| 27 | 3 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 27) | [1, 4] |
| 27 | 3 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 27) | [1, 4] |
| 27 | 3 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 27) | [1, 4] |
| 35 | 4 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 35) | [1, 4] |
| 35 | 4 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 35) | [1, 4] |
| 35 | 4 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 35) | [1, 4] |
| 35 | 4 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 35) | [1, 4] |
| 43 | 5 | 1 | 13/43 | (1, 3, 4, 5, 7, 8, 43) | [4] |
| 43 | 5 | 2 | 13/43 | (1, 3, 4, 5, 7, 16, 43) | [4] |
| 51 | 6 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 51) | [1, 4] |
| 51 | 6 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 51) | [1, 4] |
| 59 | 7 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 59) | [1, 4] |
| 59 | 7 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 59) | [1, 4] |
| 59 | 7 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 59) | [1, 4] |
| 59 | 7 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 59) | [1, 4] |
| 67 | 8 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 67) | [1] |
| 67 | 8 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 67) | [1] |
| 75 | 9 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 75) | [4] |
| 75 | 9 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 75) | [4] |
| 83 | 10 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 83) | [1, 4] |
| 83 | 10 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 83) | [1, 4] |
| 83 | 10 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 83) | [1, 4] |
| 83 | 10 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 83) | [1, 4] |
| 91 | 11 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 91) | [1, 4] |
| 91 | 11 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 91) | [1, 4] |
| 91 | 11 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 91) | [1, 4] |
| 99 | 12 | 1 | 29/99 | (1, 3, 4, 5, 7, 8, 99) | [4] |
| 99 | 12 | 2 | 29/99 | (1, 3, 4, 5, 7, 16, 99) | [4] |
| 99 | 12 | 3 | 3/8 | (1, 3, 4, 5, 7, 24, 99) | [4] |
| 107 | 13 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 107) | [1, 4] |
| 107 | 13 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 107) | [1, 4] |
| 107 | 13 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 107) | [1, 4] |
| 107 | 13 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 107) | [1, 4] |
| 115 | 14 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 115) | [1, 4] |
| 115 | 14 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 115) | [1, 4] |
| 115 | 14 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 115) | [1, 4] |
| 115 | 14 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 115) | [1, 4] |
| 123 | 15 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 123) | [1] |
| 123 | 15 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 123) | [1] |
| 123 | 15 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 123) | [1] |
| 123 | 15 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 123) | [1] |
| 131 | 16 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 131) | [4] |
| 131 | 16 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 131) | [4] |
| 131 | 16 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 131) | [4] |
| 131 | 16 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 131) | [4] |

**[D] rho0=4, rho'=5**
residual cells: 56

| e' | q' | m | witness x | E | uncovered by all 7 |
|---|---|---|---|---|---|
| 13 | 1 | 1 | 4/13 | (1, 3, 4, 5, 7, 8, 13) | [1] |
| 13 | 1 | 2 | 4/13 | (1, 3, 4, 5, 7, 13, 16) | [1] |
| 13 | 1 | 3 | 3/8 | (1, 3, 4, 5, 7, 13, 24) | [1] |
| 13 | 1 | 6 | 4/13 | (1, 3, 4, 5, 7, 13, 48) | [1] |
| 13 | 1 | 8 | 4/13 | (1, 3, 4, 5, 7, 13, 64) | [1] |
| 13 | 1 | 9 | 4/13 | (1, 3, 4, 5, 7, 13, 72) | [1] |
| 13 | 1 | 10 | 5/16 | (1, 3, 4, 5, 7, 13, 80) | [1] |
| 13 | 1 | 11 | 4/13 | (1, 3, 4, 5, 7, 13, 88) | [1] |
| 13 | 1 | 12 | 4/13 | (1, 3, 4, 5, 7, 13, 96) | [1] |
| 13 | 1 | 13 | 33/104 | (1, 3, 4, 5, 7, 13, 104) | [1] |
| 13 | 1 | 14 | 4/13 | (1, 3, 4, 5, 7, 13, 112) | [1] |
| 13 | 1 | 15 | 4/13 | (1, 3, 4, 5, 7, 13, 120) | [1] |
| 21 | 2 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 21) | [1, 4] |
| 21 | 2 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 21) | [1, 4] |
| 21 | 2 | 3 | 2/7 | (1, 3, 4, 5, 7, 21, 24) | [1, 4] |
| 21 | 2 | 6 | 2/7 | (1, 3, 4, 5, 7, 21, 48) | [1, 4] |
| 29 | 3 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 29) | [1, 4] |
| 29 | 3 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 29) | [1, 4] |
| 29 | 3 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 29) | [1, 4] |
| 37 | 4 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 37) | [4] |
| 37 | 4 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 37) | [4] |
| 37 | 4 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 37) | [4] |
| 45 | 5 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 45) | [1] |
| 45 | 5 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 45) | [1] |
| 53 | 6 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 53) | [1, 4] |
| 53 | 6 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 53) | [1, 4] |
| 53 | 6 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 53) | [1, 4] |
| 61 | 7 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 61) | [1, 4] |
| 61 | 7 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 61) | [1, 4] |
| 61 | 7 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 61) | [1, 4] |
| 69 | 8 | 1 | 20/69 | (1, 3, 4, 5, 7, 8, 69) | [1] |
| 69 | 8 | 2 | 20/69 | (1, 3, 4, 5, 7, 16, 69) | [1] |
| 77 | 9 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 77) | [1, 4] |
| 77 | 9 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 77) | [1, 4] |
| 77 | 9 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 77) | [1, 4] |
| 85 | 10 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 85) | [1, 4] |
| 85 | 10 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 85) | [1, 4] |
| 85 | 10 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 85) | [1, 4] |
| 93 | 11 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 93) | [4] |
| 93 | 11 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 93) | [4] |
| 93 | 11 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 93) | [4] |
| 101 | 12 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 101) | [1] |
| 101 | 12 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 101) | [1] |
| 101 | 12 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 101) | [1] |
| 101 | 12 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 101) | [1] |
| 109 | 13 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 109) | [1, 4] |
| 109 | 13 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 109) | [1, 4] |
| 109 | 13 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 109) | [1, 4] |
| 117 | 14 | 1 | 2/7 | (1, 3, 4, 5, 7, 8, 117) | [1, 4] |
| 117 | 14 | 2 | 2/7 | (1, 3, 4, 5, 7, 16, 117) | [1, 4] |
| 117 | 14 | 3 | 2/7 | (1, 3, 4, 5, 7, 24, 117) | [1, 4] |
| 117 | 14 | 4 | 2/7 | (1, 3, 4, 5, 7, 32, 117) | [1, 4] |
| 125 | 15 | 1 | 36/125 | (1, 3, 4, 5, 7, 8, 125) | [1] |
| 125 | 15 | 2 | 36/125 | (1, 3, 4, 5, 7, 16, 125) | [1] |
| 125 | 15 | 3 | 36/125 | (1, 3, 4, 5, 7, 24, 125) | [1] |
| 125 | 15 | 4 | 36/125 | (1, 3, 4, 5, 7, 32, 125) | [1] |

**[E] rho0=6, rho'=1**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[E] rho0=6, rho'=3**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[E] rho0=6, rho'=5**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[E] rho0=6, rho'=7**
J is empty, so the twin never kills W; W subset B_m forces m <= 2.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/8, 1/7) | 1/8 |
| 2 | [1/16, 1/7) | 1/16 |

**[F] rho0=6, rho'=6**
J is empty, so the twin never kills W; W subset B_m forces m <= 8.

| m | W minus B_m | witness x |
|---|---|---|
| 1 | [1/6, 1/5) | 1/6 |
| 2 | [1/6, 1/5) | 1/6 |
| 3 | [1/6, 1/5) | 1/6 |
| 4 | [1/6, 1/5) | 1/6 |
| 5 | [1/6, 7/40) | 1/6 |
| 6 | [3/16, 1/5) | 3/16 |
| 7 | [1/6, 1/5) | 1/6 |
| 8 | [1/6, 1/5) | 1/6 |


Total residual cells: 179
