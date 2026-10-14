# `f(8,p) ≥ 6` is FALSE as stated — three counterexamples, and what survives (v2: range extended to 700)

2026-09-07. Task: prove `f(8,p) ≥ 6` uniformly. It does not hold uniformly. Three odd
primes admit a 5-dilate cover, and one of them admits a 4-dilate cover. Witnesses are
exhibited and verified below. Script: `experiments/n8/f_lower_bound_v1.py`.

`h = ⌊(p−1)/8⌋`, `A = {s : |s|_p ≤ h}`, `M[w] = w⁻¹A`, `f(8,p) = ` least `x` with `x`
dilates covering `Z/p`.

## 1. The counterexamples  `[PROVED — explicit witnesses, independently re-verified]`

| `p` | `h` | covering set `W` | `f(8,p) ≤` |
|---|---|---|---|
| 11 | 1 | `{1,2,3,4,5}` | **5** |
| 17 | 2 | `{1,3,4,5}` | **4** |
| 19 | 2 | `{1,3,4,5,6}` | **5** |

Each was checked by re-deriving, for every `r ∈ Z/p`, that some `w ∈ W` has `|rw|_p ≤ h`:
**zero uncovered residues** in all three cases. At `p = 11`, `M[w] = {0, ±w⁻¹}`, and
`{±w⁻¹ : w = 1,…,5}` is exactly the ten non-zero residues — a perfect partition,
`5 × 2h = 10 = p−1`. At `p = 17`, `4 × 2h = 16 = p−1`, again perfect. At `p = 19`,
`5 × 2h = 20 ≥ 18` with overlap.

So the exceptions are where the non-zero residues admit an exact or near-exact partition
into symmetric arithmetic progressions. They are structural, not near-misses.

## 2. What is provable, and it is only the small cases

**Proposition 1 (counting).** *If `10h + 1 < p` then no five dilates cover `Z/p`.*
Every `M[w]` contains `0`, so `|⋃_{i=1}^{5} M[w_i]| ≤ 5(2h+1) − 4 = 10h + 1`. ∎

This decides `p ≤ 9` (`h = 0`, `A = {0}`), `p = 13` (`11 < 13`) and `p = 23` (`21 < 23`).

**Proposition 2 (counting is vacuous from `p = 29` on).** For `p ≥ 31`,
`h ≥ (p−7)/8`, so `10h + 1 ≥ (10p − 62)/8 ≥ p` exactly when `p ≥ 31`; and `p = 29` has
`h = 3`, `10h+1 = 31 ≥ 29`. ∎

**So for every prime `p ≥ 29` the counting bound permits a 5-cover, and none exists.**
That is the cleanest statement of the phenomenon recorded elsewhere as the "1.75 slack":
the obstruction is structural at every prime that matters, and no counting argument of
this shape can reach it.

## 3. The repaired claim

`[VERIFIED-scope]` **`f(8,p) ≥ 6` for every prime `23 ≤ p ≤ 700`**, decided exactly by
depth-5 branch-and-bound (branching on the lowest uncovered residue is complete; scale
invariance fixes `w = 1` in the set; `M[−w] = M[w]`). Among all odd primes `≤ 700` the
only exceptions are `11, 17, 19` — and the range `[301,700]` (63 primes) is clean. Scope: `n = 8`, this arc, primes to 700. Not a theorem
for any `p ≥ 29`.

Rosenfeld's `S` starts at 31, so the exceptions do not touch the `n = 8` application. What
they do settle is a constraint on any proof: **a correct proof must use a lower bound on
`p`.** Any argument that is purely algebraic in `w₁,…,w₅` and blind to the size of `p`
would prove the false statement, so it is wrong.

## 4. Why LRC for 6 runners does not close it

Uncovered `r` means `‖(r/p)·w_i‖ > h/p` for all `i`. Since `h/p < 1/8 < 1/6`, the level we
need is **slacker** than LRC for 6 runners provides — and LRC(6) is proved, and
machine-verified in this project. The obstruction is the grid: we need `t = r/p`, not an
arbitrary real.

Take `t₀` with `min_i ‖t₀ w_i‖ ≥ 1/6`. For `t = t₀ + δ`, `‖t w_i‖ ≥ 1/6 − |δ|w_i`, which
stays above `1/8` while `|δ| < 1/(24 max_i w_i)`. With `w_i ≤ (p−1)/2` that is
`|δ| < 1/(12p)`: an interval of length `1/(6p)`, shorter than the grid spacing `1/p` by a
factor of 6. The transfer therefore fails by a **bounded factor**, not by an order of
magnitude, and closing that factor is the whole content.

## 5. Reformulation for the next attempt

Put `u_i = w_i⁻¹`. Then `M[w_i] = {0, ±u_i, ±2u_i, …, ±h u_i}` — a **symmetric arithmetic
progression** — and as `w` runs over `(Z/p)*` so does `u`. Hence

> `f(8,p) ≥ 6` ⟺ no five symmetric APs `{0, ±u, …, ±hu}` of `h` steps each way cover `Z/p`.

That is a covering-by-APs question rather than a dilates-of-an-arc one, and each `B_i` has
its gap structure controlled by the three-distance theorem (`≈ u_i/2` clusters at period
`≈ p/u_i`). The `p = 11` and `p = 17` counterexamples are exactly the perfect partitions of
`Z/p ∖ {0}` into such APs, which is where a proof must place its lower bound on `p`.

## 6. Ledger

`f(8,p) ≥ 6` is **not proved for any `p ≥ 29`**. Decided cells: **2 of 135, unchanged.**
`P_UNIFORMITY_v1.md` §3 recorded `f(8,p) ∈ {6,7}` at the 27 primes of `S` as EMPIRICAL and
noted `f(8,p) ≥ 6` was unproved; that grade stands, with the range now extended and the
statement now known to be **false below 23**.
