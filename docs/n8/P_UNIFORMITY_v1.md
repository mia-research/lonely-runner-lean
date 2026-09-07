# Which parts of the `p = 163` sector argument are formulas in `p`

2026-09-07. Goal: an **analytic** proof of `n = 8`. Deciding 135 cells by cheaper search is
the same replication trap in cheaper clothes, so this run measured the argument's inputs
across all 27 primes of `S` in order to find which are *formulas* and which are genuinely
`p`-specific. Script `experiments/n8/p_uniformity_v1.py`; companion
`CAP_TABLE_UNIFORM_v1.md`.

**Reproduction check.** The script is written independently of `max_union_v1.py`,
`collapse_z163_v1.py` and `x5_two_odd_v1.py`. At `p = 163` it returns
`U_min = 122, 86, 58, 34, 12`, `f(8,163) = 7`, `max|D| = 27`, `#odd = 324` — all four match
the values recorded in `project_n8_rosenfeld_2026_09_07` §2 exactly.

Notation: `h = ⌊(p−1)/8⌋`, arc `A = {|s| ≤ h}`, `|A| = 2h+1`, `M[w] = w⁻¹A`.
`U_min(x) = p − max_{|W|=x} |⋃_{w∈W} M[w]|`. `f(8,p) = min x` with `U_min(x) = 0`.
`maxD(p) = ` max over pairs of odd speeds of the number of classes the pair *fully* covers.

## 1. What is now a formula

**`U_min(x)` is always even.**  `[PROVED, all odd p]`  `A = −A`, so each `M[w]` is
symmetric under `r ↦ −r`, hence so is any union and so is its complement. Every `M[w]`
contains `0`, so the complement omits `0`. A negation-symmetric subset of `Z/p` (`p` odd)
avoiding `0` is a disjoint union of pairs `{r, −r}`, so its size is even. ∎
Confirmed: every one of the 135 computed values is even.

**`U_min(1) = p − (2h+1)`.**  `[PROVED]`  `|M[w]| = |A|` since `w` acts bijectively. ∎

**`U_min(2) = p − 2(2h+1) + m(p)`**, where
`m(p) = min_{w ≠ ±1} |A ∩ w⁻¹A|`.  `[PROVED, both directions]`

*Proof.* For any pair, `|M[w₁] ∪ M[w₂]| = 2|A| − |M[w₁] ∩ M[w₂]|`, and multiplying by `w₁`
gives `|M[w₁] ∩ M[w₂]| = |A ∩ (w₂w₁⁻¹)⁻¹A| ≥ m(p)`, so every union is `≤ 2|A| − m(p)`.
Conversely `W = {1, w*}` for a minimising `w*` attains it. ∎

Verified `27/27` primes — a check of the arithmetic, not evidence for the law.

**This reduces the `x = 2` sector's cardinality input to a lattice-point count.**
`|A ∩ w⁻¹A| = #{r : |r| ≤ h and |rw|_p ≤ h}` is the number of points of the lattice
`L_w = {(a,b) ∈ Z² : b ≡ wa (mod p)}`, of determinant `p`, inside the box `[−h,h]²` of area
`(2h+1)²`. Measured: `m(p) = 1` for `p ≤ 53`, `3` for `59 ≤ p ≤ 109`, `5` for `p ≥ 113`.
Minkowski forces a non-zero point (hence `m ≥ 3`) once `(2h+1)² ≥ 4p`, i.e. `p ≳ 64`; the
measured `m` is at or above that guarantee at every prime, and `m(59) = 3` already exceeds it.

**`maxD(p) = ⌊(p+3)/6⌋`.**  `[EMPIRICAL, 27/27]`  No proof. Partial mechanism from
`CAP_TABLE_UNIFORM_v1.md` §3: an odd speed `v` covers two targets of a class iff both
`t₁ ≡ −qv⁻¹` and `t₁ − v⁻¹` lie in `{0,1,2,3} (mod 8)`, which happens for **3** of the 8
values of `q` when `v⁻¹ ≡ ±1 (mod 8)` and for **1** of 8 otherwise. What is not derived is
how the two speeds' `q`-values co-vary as `r` runs over the classes.

## 2. The route this measurement closes off

The `x = 5` and `x = 4` decisions use `|D| ≥ U_min(x)` as a **necessary filter** before an
exact coverability search. If `maxD(p) < U_min(5)` the filter alone would decide the sector,
with no search — an analytic argument with finitely many exceptional primes.

**It does not, at any prime of `S`.** `U_min(5) − maxD` is negative at all 27, and widens
roughly linearly:

| `p` | 31 | 53 | 83 | 113 | 137 | 163 |
|---|---|---|---|---|---|---|
| `U_min(5)` | 4 | 4 | 4 | 6 | 8 | 12 |
| `maxD` | 5 | 9 | 14 | 19 | 23 | 27 |
| difference | −1 | −5 | −10 | −13 | −15 | −15 |

`maxD ≈ p/6` grows about 2.3× faster than `U_min(5) ≈ p/14`. So the filter is not merely
insufficient at `p = 163` — it gets worse with `p`, and the sector method as constituted
needs its exhaustive coverability search **at every prime**. `[EMPIRICAL, all 27 primes of S;
scope: this sector argument and this filter, not covering arguments in general.]`

The forced-overlap bound `U_min(x) ≥ p − x(2h+1) + (x−1)m(p)` is valid for all `x` but is
**vacuous from `x = 5` upward** at every prime measured, non-trivial at `x ≤ 4`, and tight at
`x ≤ 2`. So it cannot rescue the filter either.

## 3. One uniform statement worth keeping

`f(8,p) ∈ {6,7}` at all 27 primes, against a density bound `⌈p/(2h+1)⌉` of 4 or 5. Since the
gcd condition forces `x ≤ 5`, **coarse speeds alone never cover, at any prime of `S`** — the
`p = 163` observation that the truth exceeds the counting bound is not special to 163.
`CLAIM_GRADES_v1` item 6 graded that EMPIRICAL and scoped to "the primes measured"; the
measured set is now all 27. Still EMPIRICAL — `f(8,p) ≥ 6` is not proved for any `p`.

## 4. Ledger

**Decided cells: 2 of 135, unchanged.** Nothing here decides a sector. What changed is that
three inputs the sector argument re-established per prime are now theorems for all odd `p`
(`CAP_TABLE_UNIFORM_v1.md`), `U_min(1)` and `U_min(2)` have closed forms, and the
filter-only route is measured shut across `S`. The open sectors at `p = 163` remain
`x ∈ {1,2,3}`, and 26 primes remain untouched.
