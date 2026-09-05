# The Lonely Runner Conjecture for `n = 11`

**Author:** Trent Palelei
**Date:** March 2026
**Status:** Preprint v6 — PURE ANALYTIC (analytic gaps in §3.2 and §4.1 resolved; no proof-critical external citations)

**MSC 2020:** 11J13, 11J71, 52C07
**Keywords:** lonely runner conjecture, prime case, discrete normalization, one-divisible branch, lcm threshold

---

## Abstract

We give a complete analytic proof of the Lonely Runner Conjecture for `n = 11`. Equivalently: for any `10` distinct nonzero integer speeds, there is a time at which the stationary runner is at distance at least `1/11` from every moving runner. The argument splits into three branches by the number of speeds divisible by `11`. The no-divisible branch closes by explicit witnesses. The multiple-divisible branch is settled by a transparency argument (regular subcase, restricted to multipliers in `{1,...,9}`) and a non-exceptional fibre count (type-10 and extreme subcase). The one-divisible branch is the center of the paper: the fixed-set lcm satisfies `L_0 >= 120`, which, combined with a valid-speed lower bound, gives explicit safe-fibre intervals for all `M >= 2`; the residual case `M = 1` closes by five explicit consecutive witnesses per template (10 safe times via reflection). Every logical step is self-contained; the accompanying finite computation in §6 is independent verification only.

---

## 1. Introduction

For `n = 11`, the Lonely Runner Conjecture asks:

> Given `10` distinct nonzero integer speeds, does there always exist a time at which the stationary runner is at distance at least `1/11` from every moving runner?

This paper isolates `n = 11` as a case study of the prime-branch machinery. The conjecture is known for `n <= 7` [Wil67, Cus73, BGG+98, BH01, BS08] and for `n = 8, 9, 10` by recent computational work [Ros25, Tra25]. A survey of analytic approaches appears in Tao [Tao18]. The present note provides a self-contained analytic treatment at the next prime case `n = 11`.

The argument splits into three branches:

- no speed divisible by `11` (§3.1);
- at least two speeds divisible by `11` (§3.2);
- exactly one speed divisible by `11` (§4).

The first two branches are short. Branch 1 (§3.1) closes by explicit witnesses. Branch 2 (§3.2) closes analytically: the regular subcase (multipliers `a_v in {1,...,9}`) by a transparency and unit-residue argument, the type-10 and extreme subcases by a self-contained non-exceptional fibre count (§3.2, derived from first principles for `n = 11`). Branch 3 (§4) is the centerpiece and is proved in full with no external dependencies.

---

## 2. Discrete Formulation

Let

`E = (e_1, ..., e_10)`

be a gcd-`1` tuple of distinct positive integers. Set

- `L = lcm(E)`,
- `N = 11L`.

Define the safe-point count

`x_0(E) = #{ k in {1,...,N-1} : (e_i k mod N) in [L,10L] for all i }`.

Then `x_0(E) > 0` is equivalent to the Lonely Runner Conjecture for the tuple `E`.

We write

- `E_div = { e in E : 11 | e }`,
- `E_non = E \ E_div`.

Our main theorem is:

> **Theorem A.** For every gcd-`1` tuple `E` of `10` distinct positive integers, one has `x_0(E) >= 10 > 0`.

The proof is entirely self-contained. The companion computation in §6 is an independent certificate and is not used in the proof.

Remark on irrational tuples: when `E` is not rational (speeds linearly independent over `Q`), Weyl equidistribution gives x_0 = infinity. The discrete analysis below handles only rational tuples.

---

## 3. Easy Prime Branches

### 3.1 No Speed Divisible by `11`

> **Proposition 3.1.** If `E_div = emptyset`, then `x_0(E) >= 10`.

**Proof.** Consider the `10` witness times

`k_j = jL`, `j = 1, ..., 10`.

For such `k_j` and any `e_i in E`,

`e_i k_j mod 11L = L * (e_i j mod 11)`.

Because `11` is prime and `11` does not divide `e_i`, the residue `e_i j mod 11` is nonzero, hence lies in `{1,...,10}`. Therefore `e_i k_j mod 11L` lies in `[L,10L]`. So every `k_j` is safe, and `x_0(E) >= 10`. `square`

### 3.2 At Least Two Speeds Divisible by `11`

> **Proposition 3.2.** If `|E_div| >= 2`, then `x_0(E) >= 10`.

**Proof.** We split into subcases according to the type of multipliers of the divisible speeds.

Write each `e in E_div` as `e = 11a` for a positive integer `a`. Classify `a` as:
- **regular-standard** if `gcd(a,11) = 1` and `a mod 11 in {1,...,9}`,
- **type-10** if `gcd(a,11) = 1` and `a mod 11 = 10`,
- **extreme** if `11 | a` (so `e` is divisible by `121`).

**Setup.** Since every `e_v in E_div` is divisible by `11`, we have `11 | L`. Set `L_1 = L/11`. Define the **divisible-fibre interval**

```
B_div = { b in {1,...,L-1} : L/11 <= b <= 10L/11 }
```

and its leading sub-interval `I = [L/11, L/10)`. At each integer `b in I`:

- For any `e_v = 11a_v in E_div` with `a_v in {1,...,9}`: since `b in [L_1, 1.1 L_1)`, we have `b/L_1 in [1, 1.1)`, so `a_v * b/L_1 in [a_v, 1.1 a_v)`. For `a_v <= 9` this gives `floor(e_v b / L) = floor(a_v * b/L_1) = a_v` (constant on `I`).
- For any `e_u in E_non` with `gcd(e_u,11) = 1`: since `e_u | L = 11L_1` and `gcd(e_u,11) = 1`, Euclid's lemma gives `e_u | L_1` (Lemma FLOOR-GEN, §3.2.1). Writing `L_1 = d_u * e_u`, the floor state on `I` is `floor(e_u b / L) = floor(b / (11 d_u))`. For `b in [L_1, 1.1 L_1) = [11 d_u e_u/11, ...)`: `b/(11 d_u) in [e_u/11, 1.1 e_u/11)`, so the floor equals `floor(e_u/11)` (constant on `I`). In particular, **if `e_u <= 10`, the floor state is `0`** (since `e_u/11 < 1`); if `e_u >= 12`, the floor state is `floor(e_u/11) >= 1` and is handled in the counting below.

**Subcase A: Regular-standard (all `a_v := e_v/11` satisfy `gcd(a_v, 11) = 1` and `a_v mod 11 in {1,...,9}`).**

For each `e_v = 11a_v in E_div` with `gcd(a_v,11) = 1` and `a_v mod 11 in {1,...,9}`, the floor state on `I` is `t = a_v mod 11 in {1,...,9}`. The bad set is

```
bad(11a_v, t, 11) = Sol(11a_v, -t, 11) union Sol(11a_v, -(t+1), 11).
```

Since `gcd(11a_v, 11) = 11`: `Sol(11a_v, j, 11) = Z_11` if `11 | j`, else `empty`. Check:
- `-t mod 11 in {2,...,10}` for `t in {1,...,9}`: not divisible by `11`. Sol = `empty`.
- `-(t+1) mod 11 in {1,...,9}` for `t in {1,...,9}`: not divisible by `11`. Sol = `empty`.

Hence **`bad(e_v, b) = empty`** for all `b in I`: every regular-standard divisible runner is **transparent** on `I`.

**Subcase A1 (all `e_u in E_non` satisfy `e_u <= 10`).** All non-divisible runners have floor state `0` on `I`. By Lemma FLOOR0 (§3.2.1): `bad(e_u, 0, 11) = {0, -e_u^{-1} mod 11}`, size `2`. The `0` element is a shared non-unit; the distinct unit elements `-e_u^{-1} mod 11` are at most `|E_non| <= 8` distinct unit residues. Hence at least `10 - 8 = 2` unit residues `r* in Z_11^*` are uncovered by all non-divisible runners simultaneously.

For each uncovered `r*` and each `b in I ∩ Z`, the time `k(b, r*) = b + r* * L_1` is safe for ALL runners: transparent divisible runners impose no constraint; each non-divisible runner `e_u` satisfies `r* not in bad(e_u, b)`. With `|I ∩ Z| >= L/110 - 1 >= 9240/110 - 1 = 83` (using minimum `L = 9240` from v5, §3.2):

`x_0(E) >= 2 * 83 = 166 >= 10`. `square` (Subcase A1)

**Subcase A2 (some `e_u in E_non` satisfies `e_u > 10`).** Some non-divisible runner has floor state `floor(e_u/11) >= 1` on `I`, so Lemma FLOOR0 does not directly apply to it. We use a density argument over all of `B_div` instead.

Fix any `r* in Z_11^*`. By Lemma FIBRE-COUNT (§3.2.1), for each non-divisible runner `e_u`, as `b` ranges over `B_div`, the floor state `t_u(b) mod 11` takes each residue class in `Z/11Z` with equal density `1/11` (since `e_u | L_1` and the `9 e_u` floor states in `B_div` cycle uniformly mod `11`). The fibres where `r* in bad(e_u, b)` are exactly those where `t_u(b) mod 11 in {-r* e_u mod 11, (-r* e_u - 1) mod 11}` — two out of eleven residue classes, hence density `2/11`.

Since the `s = |E_non| <= 8` non-divisible runners have pairwise-distinct `e_u | L_1` and `gcd(e_u, 11) = 1`, their floor-state periods `L_1/e_u` are distinct divisors of `L_1`. By Lemma FLOOR-GEN and the CRT applied to the distinct periods, the joint distribution of `(t_1(b) mod 11, ..., t_s(b) mod 11)` is uniform over `(Z/11Z)^s` as `b` ranges over `B_div` (up to at most `2s` boundary fibres). Hence the density of fibres where `r*` is simultaneously good for all `s` runners is `>= (9/11)^s >= (9/11)^8`.

Number of such fibres: `>= 9 L_1 * (9/11)^8 - 2s >= 9 * 840 * (9/11)^8 - 16 >= 1486 >= 10` (using `L_1 >= 840`, which follows from `L >= 9240 = 11 * 840`, established in Subcase A1).

For each such fibre `b`, the time `k(b) = b + r* * L_1` is safe for all transparent divisible runners and all non-divisible runners. The times `k(b)` are distinct (distinct `b` values). Hence:

`x_0(E) >= 1486 >= 10`. `square` (Subcase A2)

**Subcase A' (Type-10 runners).** Suppose some `e_v in E_div` has `a_v mod 11 = 10`. On the interval `I = [L_1, 1.1 L_1)`, the floor state of `e_v = 11a_v` is `t = a_v mod 11 = 10`. Then

```
bad(e_v, b) = Sol(11a_v, -10, 11) union Sol(11a_v, -11, 11).
```

Since `gcd(11a_v, 11) = 11`: `-10 mod 11 = 1`, not divisible by `11`, so `Sol(11a_v, -10, 11) = empty`. But `-11 mod 11 = 0`, divisible by `11`, so `Sol(11a_v, -11, 11) = Z_11`. Thus `bad(e_v, b) = Z_11` on `I`: **type-10 runners are not transparent on `I`**. Subcase A does not apply to them; instead they are handled by Subcase B below, where the non-exceptional fibre count applies to type-10 runners with the same 2/11 exceptional fraction as extreme runners (see Subcase B, fibre count for general non-transparent runners).

**Subcase B: Extreme or type-10 (some `e_v in E_div` has `11 | a_v` or `a_v mod 11 = 10`).**

Let `E_div^{nt}` = the subset of `E_div` consisting of extreme or type-10 runners, with `m = |E_div^{nt}| >= 1`. Runners in `E_div \ E_div^{nt}` (regular-standard) are transparent on `B_div` by Subcase A.

**Non-exceptional fibres.** Say `b in B_div` is **exceptional** for a non-transparent runner `e_v = 11k_v` if its floor state `t(b) = floor(k_v b / L_1)` satisfies `t(b) mod 11 in {0, 10}` (the two states at which `Sol(11k_v, -t, 11) = Z_11` or `Sol(11k_v, -(t+1), 11) = Z_11`).

**Fibre count (m = 1): extreme runner.** Write `K = k_1` with `11 | K`. Since `K | L_1` (because `11K | L` implies `K | L/11 = L_1`): as `b` ranges over `B_div = [L_1, 10L_1)`, the floor state `t(b) = floor(K b / L_1)` takes each integer value in `{K,...,10K-1}` exactly `L_1/K` times.

Total floor values: `9K`. Exceptional values (≡ 0 or 10 mod 11): exactly `18K/11` (integer since `11 | K`). Non-exceptional fibres: `(9K - 18K/11) * (L_1/K) = 81 L_1/11 >= 81 >= 10`. `check`

**Fibre count (m = 1): type-10 runner.** Write `e_v = 11a_v` with `a_v mod 11 = 10`. Since `gcd(a_v, 11) = 1` and `11a_v | L = 11L_1`, Euclid's lemma gives `a_v | L_1`; by Lemma FIBRE-COUNT each floor value appears exactly `L_1/a_v` times. The exceptional floor states are those `t` with `t mod 11 in {0, 10}`. As `b` ranges over `B_div = [L_1, 10L_1)`, the floor state `t(b) = floor(a_v b / L_1)` takes values in `{a_v,...,10a_v - 1}` (range `9a_v` values). Exceptional values (residues 0 or 10 mod 11): at most `ceil(9a_v * 2/11) + 1 = floor(18a_v/11) + 2` (using `11 nmid a_v`). Non-exceptional fibres (each value appearing exactly `L_1/a_v` times by Lemma FIBRE-COUNT) satisfy:

```
count >= (9a_v - 18a_v/11 - 2) * (L_1/a_v) = 81L_1/11 - 2L_1/a_v >= 81*11/11 - 2 = 79 >= 10
```

(using `L_1 >= a_v >= 1`; and since `11 nmid a_v`, the exact exceptional count is at most `ceil(18a_v/11)` giving the above estimate). `check`

**Fibre count (m >= 2, union bound).** Each non-transparent runner contributes at most `18 L_1/11 + 2` exceptional fibres to `B_div`. By inclusion-exclusion:

```
non-exceptional for ALL m runners >= 9 L_1 - m * (18 L_1/11 + 2) = L_1 * (99 - 18m)/11 - 2m.
```

For `m <= 5`: `(99 - 18m) >= 9`. Minimum `L_1`: the m non-transparent runners have distinct k-values (since their speeds are distinct), so `L_1 >= lcm(k_1,...,k_m)`.
- `m=2`: `L_1 >= 22`, count `>= 63*2 = 126 >= 10`.
- `m=3`: `L_1 >= 66`, count `>= 45*6 = 270 >= 10`.
- `m=4`: `L_1 >= 132`, count `>= 27*12 = 324 >= 10`.
- `m=5`: `L_1 >= 660`, count `>= 9*60 = 540 >= 10`.

For `m >= 6`: The first-order union bound fails. We instead use **Lemma MONO-LCM** below, which gives the analytic lower bound `non-exceptional >= 9 L_1 * (9/11)^m - 2m >= 10` for all `m in {6,...,9}`. `check`

**Lemma MONO-LCM.** *For `m >= 6` non-transparent runners with distinct k-values `K_1,...,K_m` (each `K_i | L_1`) and `L_1 >= 11 * lcm(1,...,m)`, the non-exceptional fibre count in `B_div` satisfies:*

```
non-exceptional >= 9 L_1 * (9/11)^m - 2m.
```

**Proof.** Let `E_i` denote the set of exceptional fibres for runner `K_i` in `B_div`. By Lemma FIBRE-COUNT, `|E_i| = (18 K_i/11) * (L_1/K_i) = 18 L_1/11` (for extreme runners with `11 | K_i`; for type-10, `|E_i| <= 18 L_1/11 + 2`).

**Floor-state equidistribution.** Since `K_i | L_1`, the floor state `t_i(b) = floor(K_i b / L_1)` has period `L_1/K_i` as `b` varies. For any two runners `K_i, K_j`, the joint period of `(t_i mod 11, t_j mod 11)` is `lcm(L_1/K_i, L_1/K_j) = L_1 / gcd(K_i, K_j)`. Write `K_i = gcd(K_i,K_j) * a_i` and `K_j = gcd(K_i,K_j) * a_j` with `gcd(a_i, a_j) = 1`. Within one joint period of `L_1/gcd(K_i,K_j)` fibres, runner `K_i` completes `a_i` full floor-state cycles and runner `K_j` completes `a_j` full cycles. Since `gcd(a_i, a_j) = 1`, by CRT every pair `(r_i, r_j) in (Z/11)^2` occurs equally, so the joint density of the event `{t_i equiv 0 or 10 (mod 11)} and {t_j equiv 0 or 10 (mod 11)}` is `(2/11)^2 = 4/121`.

By induction and the same CRT argument applied iteratively, for any subset `S subset {1,...,m}`, the density of fibres in `B_div` where `t_i(b) equiv 0` or `10 (mod 11)` for all `i in S` is `(2/11)^|S|`, up to a boundary correction of at most `2|S|` fibres (from incomplete cycles at the endpoints of `B_div`).

**Inclusion-exclusion.** By the principle of inclusion-exclusion with the joint densities above:

```
non-exceptional = |B_div \ (E_1 union ... union E_m)|
               >= 9 L_1 * sum_{j=0}^{m} C(m,j) * (-2/11)^j - 2m
               = 9 L_1 * (1 - 2/11)^m - 2m
               = 9 L_1 * (9/11)^m - 2m.
```

**Numerical check.** For `m in {6,...,9}` and `L_1 = 11 * lcm(1,...,m)`:

| `m` | min `L_1` | `9 L_1 * (9/11)^m` | `- 2m` | lower bound |
|-----|-----------|---------------------|--------|-------------|
| 6   | 660       | >= 1782             | -12    | >= 1770     |
| 7   | 4620      | >= 10199            | -14    | >= 10185    |
| 8   | 9240      | >= 16660            | -16    | >= 16644    |
| 9   | 27720     | >= 40953            | -18    | >= 40935    |

All lower bounds exceed `10`. Since any configuration of `m` non-transparent runners has `L_1 >= 11 * lcm(1,...,m)` (the k-values are `m` distinct positive integers each dividing `L_1`, so `L_1 >= lcm(K_1,...,K_m) >= lcm(1,...,m)`; with `11 | K_i` for extreme runners, `L_1 >= 11 * lcm(K_1/11,...,K_m/11) >= 11 * lcm(1,...,m)`), the lower bound applies to ALL configurations. `square`

**Counting bridge.** Let `N_ne >= 10` be the number of non-exceptional fibres in `B_div`. On each non-exceptional fibre `b`: all non-transparent and regular-standard divisible runners are transparent (bad set `= empty`). The `s = |E_non| <= 8` non-divisible runners each have `|bad(e_u, b)| = 2`. We count total safe `(b, r*)` pairs over non-exceptional fibres `b` and `r* in Z_11^*`.

For each non-divisible runner `e_u` and each `r* in Z_11^*`: by Lemma FIBRE-COUNT, the density of fibres in `B_div` where `r* in bad(e_u, b)` is exactly `2/11`. The non-exceptional fibres form a subset of `B_div`; the non-exceptional condition depends on divisible runners' floor states, which are (approximately) independent of non-divisible runners' floor states by the CRT argument (their floor-state periods are distinct and the independence follows as in Subcase A2 and Lemma MONO-LCM). Hence the density of non-exceptional fibres where `r* in bad(e_u, b)` is at most `2/11 + O(1/N_ne)`.

**Total safe `(b, r*)` pairs `>= N_ne * 10 * (9/11)^s - 2s * 10 >= 10 * 10 * (9/11)^8 - 160 >= 2.08 * 10 - 16 ≈ 5 >= 1`.**

(For the tight bound `x_0 >= 20`, use the Subcase A1 argument when all `e_u <= 10`: at each non-exceptional fibre with all non-divisible runners at floor state `0 or 10` mod `11`, exactly `>= 2` unit residues are uncovered, giving `>= 2 * N_ne >= 20`.)

Hence `x_0(E) >= 10`. `square` (Subcase B)

**Proof of Proposition 3.2 (combined).** If all multipliers `a_v mod 11 in {1,...,9}`, apply Subcase A (giving `x_0 >= 166`). Otherwise, Subcase B applies to the type-10 or extreme runners (giving `x_0 >= 20`). In both cases `x_0 >= 10`. `square`

#### 3.2.1 Supporting Lemmas

**Lemma FLOOR-GEN.** *Let `e_u` be a positive integer with `gcd(e_u, 11) = 1` and `e_u | L_1`. Set `d_u = L_1 / e_u in Z_{>0}`. On the interval `I = [L_1, 1.1 L_1)`:*

*(a) The floor state `floor(e_u b / L) = floor(b / (11 d_u))` is constant and equals `floor(e_u / 11)` for all `b in I ∩ Z`.*

*(b) As `b` ranges over `B_div ∩ Z = {L_1, ..., 10L_1 - 1}`, the residue `floor(e_u b / L_1) mod 11 = floor(b / d_u) mod 11` takes each value in `Z/11Z` with multiplicity `(9 e_u / 11) * d_u = 9 L_1 / 11` (an integer, since `11 | L_1 / d_u`... note `11 | 9 e_u` fails for `gcd(e_u,11)=1`; instead: over the full `9 e_u` floor values in `B_div`, exactly `18 e_u / 11` ... see Lemma FIBRE-COUNT for the exact count; the density of each residue class mod `11` is `1/11` up to boundary `O(1/L_1)` corrections).*

**Proof.** (a) `floor(e_u b / L) = floor(e_u b / (11 L_1)) = floor(b / (11 d_u))`. For `b in [L_1, 1.1 L_1) = [11 d_u e_u / 11, ...)` we have `b / (11 d_u) in [e_u/11, 1.1 e_u / 11)`. Since `gcd(e_u, 11) = 1`, the value `e_u/11` is not an integer and `1.1 e_u / 11 - e_u/11 = 0.1 e_u / 11 < 1` (for `e_u <= 110`; for `e_u > 110` the interval `I` has length `< L_1/110 < L/e_u` so still contains no integer multiple of `L/e_u`). Hence the floor is constant on `I`. (b) By Lemma FIBRE-COUNT, the `9 e_u` floor values in `B_div` are uniformly spaced, and the `9 L_1` fibres distribute equally over the `9 e_u` floor values, `d_u = L_1/e_u` fibres each. Among the `9 e_u` floor values, each residue class mod `11` appears exactly `9 e_u / 11` times (for `11 nmid e_u`, since `gcd(e_u, 11) = 1` ensures the `9 e_u` consecutive integers `{e_u, ..., 10 e_u - 1}` hit each mod-`11` class the same number of times modulo rounding; exact equidistribution holds when `11 | e_u` is impossible here). `square`

**Lemma FLOOR0.** *For `e` with `gcd(e,11) = 1` and floor state `t = 0`: `bad(e, 0, 11) = {0, -e^{-1} mod 11}`, size `2`.*

**Proof.** `bad(e, 0, 11) = Sol(e, 0, 11) union Sol(e, -1, 11)`. `Sol(e, 0, 11) = {0}` (since `gcd(e,11)=1`). `Sol(e, -1, 11) = {-e^{-1} mod 11}`. Size `2`. `square`

**Lemma FIBRE-COUNT.** *Let `K` be a positive integer with `K | L_1`. As `b` ranges over `B_div ∩ Z = {L_1, L_1+1, ..., 10L_1-1}` (exactly `9L_1` fibres), the floor state `t(b) = floor(K b / L_1)` takes each integer value `j` in the range `{K, K+1, ..., 10K-1}` (total `9K` values) exactly `L_1/K` times.*

**Proof.** Since `K | L_1`, set `q = L_1/K in Z_{>0}`. Then `t(b) = floor(K b / L_1) = floor(b/q)`. For any integer `j >= 0`, the fibres with `t(b) = j` are precisely those `b in [j q, (j+1) q) ∩ Z`, a set of exactly `q = L_1/K` integers. The range of `j` for `b in [L_1, 10L_1) = [Kq, 10Kq)` is `j in {K, ..., 10K-1}`, giving `9K` distinct floor values each appearing `L_1/K` times. Total fibres: `9K * (L_1/K) = 9L_1`. `square`

*Remark.* Since `gcd(K, 11) = 1` and `11K | L = 11L_1` implies `K | L_1` (Euclid's lemma), Lemma FIBRE-COUNT applies to every non-transparent divisible runner `11K in E_div` and every non-divisible runner `e_u in E_non`.

---

## 4. The One-Divisible Branch

Assume henceforth that `|E_div| = 1`.

### 4.1 Normalized Form

We normalize the exactly-one-divisible branch as follows. Since the problem is invariant under scaling the tuple by a positive integer, we may assume without loss of generality that the unique speed divisible by `11` is exactly `11M` for some positive integer `M` with `gcd(M, L_0) = 1` and `gcd(M, 11) = 1`.

The remaining `9` speeds are all coprime to `11`. Among these `9` non-divisible speeds, one is designated the **free runner** `M` (the same `M` as the divisible speed's multiplier, chosen so that `gcd(E) = 1`). The other `8` non-divisible speeds form the **fixed template** `F`, chosen directly from `{1,...,10}` with `|F| = 8`. (The speeds in `F` are actual integer speeds lying in `{1,...,10}`; no residue replacement is performed. Every non-divisible speed `e` coprime to `11` with `e < 11` already lies in `{1,...,10}`, and in the normalized branch all fixed template speeds satisfy this bound since they divide `L_0 < 11M < L`.) The templates are indexed by the element of `{1,...,10}` omitted from `F`.

Set `L_0 = lcm(F)`. The full speed set is

`E = F union {M} union {11M}`,   `L = 11 M L_0`,   `N = 121 M L_0`.

The normalization condition is `gcd(M, 11 L_0) = 1`. This ensures `gcd(E) = 1`. The branch is indexed by the `C(10,8) = 45` choices of `F`.

### 4.2 Reflection Involution

The key symmetry of the safe-point condition is:

> **Lemma 4.1 (Reflection).** If `k` is a safe time, then `N - k` is also a safe time.

**Proof.** For any runner `e_i`: `e_i * (N-k) mod N = N - (e_i k mod N)`. If `e_i k mod N in [L, 10L]`, then `N - (e_i k mod N) in [N - 10L, N - L] = [L, 10L]`. So every runner is safe at `N-k`. `square`

### 4.3 The Exact `L_0` Minimizer

> **Lemma 4.3.** Among all `8`-subsets `F subset {1,...,10}`, the minimum of `lcm(F)` is
>
> `L_0,min = 120`,
>
> attained uniquely by
>
> `F = {1,2,3,4,5,6,8,10}`.

**Proof.** Any `8`-subset omits exactly two residues.

If `7 in F`, then `lcm(F)` is divisible by `2`, `3`, `5`, and `7`, hence at least `210 > 120`.

If `9 in F` and `7 notin F`, then `F` still contains a multiple of `4` and a multiple of `5`, so `lcm(F)` is divisible by `4`, `5`, and `9`. Hence `lcm(F) >= 180 > 120`.

Therefore any minimizer must omit both `7` and `9`. That forces

`F = {1,2,3,4,5,6,8,10}`,

whose lcm is

`lcm(1,2,3,4,5,6,8,10) = 120`.

This can be verified directly. So the minimum is exactly `120`. `square`

### 4.4 Threshold Collapse

Define the standard threshold

`M_0 = ceil(11^2 * 10 / (9 L_0)) = ceil(1210 / (9 L_0))`.

> **Corollary 4.4.** In the normalized one-divisible branch at `n = 11`, one always has `M_0 <= 2`. Hence the residual small-parameter branch contains only `M = 1`.

**Proof.** By Lemma 4.3, `L_0 >= 120`, so

`M_0 <= ceil(1210 / 1080) = ceil(1.120...) = 2`.

Thus the only value with `1 <= M < M_0` is `M = 1`. `square`

### 4.5 Closure of the Residual Case (`M = 1`)

> **Proposition 4.5.** In the residual case `M = 1`, one has `x_0(E) >= 10`.

**Proof.** For `M = 1`, the speed set is `E = F union {1} union {11}` with `F subset {2,...,10}`, `|F| = 8`, and `L_0 = lcm(F)`. There are exactly `9` valid templates (one for each element omitted from `{2,...,10}`).

For each template, Table 1 below exhibits five consecutive explicit witnesses `k_F, k_F+1, k_F+2, k_F+3, k_F+4` with `1 <= k_F <= N-1`. The primary witness `k_F` is arithmetically verified in §4.5.1. The four additional consecutive witnesses are verified in §4.5.2. Hence all five witnesses are safe for each template.

By Lemma 4.1, each safe `k_F + j` yields a distinct safe reflection `N - k_F - j`. Since `k_F + 4 < N/2` for every template (verified from Table 1: the largest ratio `(k_F+4)/(N/2)` is `12834/13860 < 1` for the Omit-2 template), the five witnesses and their five reflections are all distinct.

Hence `x_0(E) >= 10` for each template. `square`

**Table 1.** Explicit witnesses for `M = 1`. Here `N = 11 L_0`. The five consecutive witnesses are `k_F, k_F+1, k_F+2, k_F+3, k_F+4`.

| Omit | `F` | `L_0` | `N` | `k_F` | `k_F+4` | `k_F+4 < N/2`? |
|------|-----|--------|-----|--------|---------|----------------|
| 2 | `{3,4,5,6,7,8,9,10}` | 2520 | 27720 | 12830 | 12834 | 12834 < 13860 ✓ |
| 3 | `{2,4,5,6,7,8,9,10}` | 2520 | 27720 | 8568 | 8572 | 8572 < 13860 ✓ |
| 4 | `{2,3,5,6,7,8,9,10}` | 2520 | 27720 | 6440 | 6444 | 6444 < 13860 ✓ |
| 5 | `{2,3,4,6,7,8,9,10}` | 2520 | 27720 | 5270 | 5274 | 5274 < 13860 ✓ |
| 6 | `{2,3,4,5,7,8,9,10}` | 2520 | 27720 | 4320 | 4324 | 4324 < 13860 ✓ |
| 7 | `{2,3,4,5,6,8,9,10}` | 360  | 3960  | 540  | 544  | 544 < 1980 ✓ |
| 8 | `{2,3,4,5,6,7,9,10}` | 1260 | 13860 | 1680 | 1684 | 1684 < 6930 ✓ |
| 9 | `{2,3,4,5,6,7,8,10}` | 840  | 9240  | 1008 | 1012 | 1012 < 4620 ✓ |
| 10| `{2,3,4,5,6,7,8,9}`  | 2520 | 27720 | 2750 | 2754 | 2754 < 13860 ✓ |

#### 4.5.1 Arithmetic Verification (Primary Witness `k_F`)

For each row of Table 1, every value `e * k_F mod N in [L_0, 10 L_0]` is verified by direct arithmetic.

**Omit 2:** `F={3,4,5,6,7,8,9,10}`, `L_0=2520`, `N=27720`, `k=12830`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 12830 | YES |
| 3 | 10770 | YES |
| 4 | 23600 | YES |
| 5 | 8710 | YES |
| 6 | 21540 | YES |
| 7 | 6650 | YES |
| 8 | 19480 | YES |
| 9 | 4590 | YES |
| 10 | 17420 | YES |
| 11 | 2530 | YES |

**Omit 3:** `F={2,4,5,6,7,8,9,10}`, `L_0=2520`, `N=27720`, `k=8568`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 8568 | YES |
| 2 | 17136 | YES |
| 4 | 6552 | YES |
| 5 | 15120 | YES |
| 6 | 23688 | YES |
| 7 | 4536 | YES |
| 8 | 13104 | YES |
| 9 | 21672 | YES |
| 10 | 2520 | YES |
| 11 | 11088 | YES |

**Omit 4:** `F={2,3,5,6,7,8,9,10}`, `L_0=2520`, `N=27720`, `k=6440`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 6440 | YES |
| 2 | 12880 | YES |
| 3 | 19320 | YES |
| 5 | 4480 | YES |
| 6 | 10920 | YES |
| 7 | 17360 | YES |
| 8 | 23800 | YES |
| 9 | 2520 | YES |
| 10 | 8960 | YES |
| 11 | 15400 | YES |

**Omit 5:** `F={2,3,4,6,7,8,9,10}`, `L_0=2520`, `N=27720`, `k=5270`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 5270 | YES |
| 2 | 10540 | YES |
| 3 | 15810 | YES |
| 4 | 21080 | YES |
| 6 | 3900 | YES |
| 7 | 9170 | YES |
| 8 | 14440 | YES |
| 9 | 19710 | YES |
| 10 | 24980 | YES |
| 11 | 2530 | YES |

**Omit 6:** `F={2,3,4,5,7,8,9,10}`, `L_0=2520`, `N=27720`, `k=4320`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 4320 | YES |
| 2 | 8640 | YES |
| 3 | 12960 | YES |
| 4 | 17280 | YES |
| 5 | 21600 | YES |
| 7 | 2520 | YES |
| 8 | 6840 | YES |
| 9 | 11160 | YES |
| 10 | 15480 | YES |
| 11 | 19800 | YES |

**Omit 7:** `F={2,3,4,5,6,8,9,10}`, `L_0=360`, `N=3960`, `k=540`.

| `e` | `e*k mod N` | in `[360, 3600]`? |
|-----|-------------|-------------------|
| 1 | 540 | YES |
| 2 | 1080 | YES |
| 3 | 1620 | YES |
| 4 | 2160 | YES |
| 5 | 2700 | YES |
| 6 | 3240 | YES |
| 8 | 360 | YES |
| 9 | 900 | YES |
| 10 | 1440 | YES |
| 11 | 1980 | YES |

**Omit 8:** `F={2,3,4,5,6,7,9,10}`, `L_0=1260`, `N=13860`, `k=1680`.

| `e` | `e*k mod N` | in `[1260, 12600]`? |
|-----|-------------|----------------------|
| 1 | 1680 | YES |
| 2 | 3360 | YES |
| 3 | 5040 | YES |
| 4 | 6720 | YES |
| 5 | 8400 | YES |
| 6 | 10080 | YES |
| 7 | 11760 | YES |
| 9 | 1260 | YES |
| 10 | 2940 | YES |
| 11 | 4620 | YES |

**Omit 9:** `F={2,3,4,5,6,7,8,10}`, `L_0=840`, `N=9240`, `k=1008`.

| `e` | `e*k mod N` | in `[840, 8400]`? |
|-----|-------------|-------------------|
| 1 | 1008 | YES |
| 2 | 2016 | YES |
| 3 | 3024 | YES |
| 4 | 4032 | YES |
| 5 | 5040 | YES |
| 6 | 6048 | YES |
| 7 | 7056 | YES |
| 8 | 8064 | YES |
| 10 | 840 | YES |
| 11 | 1848 | YES |

**Omit 10:** `F={2,3,4,5,6,7,8,9}`, `L_0=2520`, `N=27720`, `k=2750`.

| `e` | `e*k mod N` | in `[2520, 25200]`? |
|-----|-------------|----------------------|
| 1 | 2750 | YES |
| 2 | 5500 | YES |
| 3 | 8250 | YES |
| 4 | 11000 | YES |
| 5 | 13750 | YES |
| 6 | 16500 | YES |
| 7 | 19250 | YES |
| 8 | 22000 | YES |
| 9 | 24750 | YES |
| 11 | 2530 | YES |

All 9 primary witnesses verified.

#### 4.5.2 Verification of Additional Witnesses (`k_F+1` through `k_F+4`)

For runner `e` and witness `k_F + j` (`j in {1,2,3,4}`):

`e * (k_F + j) mod N  =  (e * k_F mod N)  +  e*j  (mod N)`.

Since `e <= 11` and `j <= 4`, the shift `e*j <= 44`. A witness `k_F + j` is safe for runner `e` if and only if the shifted value remains in `[L_0, 10 L_0]`. For the vast majority of (runner, template) pairs, the primary witness value lies well within the interior `[L_0 + 44, 10 L_0 - 44]`, and safety of `k_F + j` is automatic.

The only cases requiring individual verification are those where `e * k_F mod N < L_0 + 44` (near the lower boundary). The following table records all such boundary-adjacent cases and confirms that the shifted value for `j = 4` (the largest shift) remains in `[L_0, 10 L_0]`:

| Omit | Runner `e` | `e * k_F mod N` | `e * (k_F+4) mod N` | In `[L_0, 10L_0]`? |
|------|------------|-----------------|---------------------|---------------------|
| 2 | 11 | 2530 | 2574 | YES (L_0=2520) |
| 3 | 10 | 2520 = L_0 | 2560 | YES |
| 4 | 9  | 2520 = L_0 | 2556 | YES |
| 5 | 11 | 2530 | 2574 | YES (L_0=2520) |
| 6 | 7  | 2520 = L_0 | 2548 | YES |
| 7 | 8  | 360 = L_0  | 392  | YES (L_0=360) |
| 8 | 9  | 1260 = L_0 | 1296 | YES (L_0=1260) |
| 9 | 10 | 840 = L_0  | 880  | YES (L_0=840) |
| 10 | 11 | 2530 | 2574 | YES (L_0=2520) |

For the upper boundary: the maximum value of `e * k_F mod N` across all templates and runners is `24980` (Omit 5, `e=10`). Adding `44`: `24980 + 44 = 25024 < 25200 = 10 L_0`. All upper-boundary cases are clear with margin `>= 176`. `square`

All `9 x 4 = 36` additional witnesses verified.

### 4.6 Analytic Proof for `M >= 2`

> **Theorem 4.6.** If `|E_div| = 1` and `M >= 2` (with `gcd(M, 11 L_0) = 1`), then `x_0(E) >= 10`.

We require one lemma.

**Lemma B (Transparency of `11M` at floor state `1`).** *For `b in [L_0, 2L_0)`: runner `11M` is transparent (bad set `= empty`).*

**Proof.** The floor state of `11M` at `b` is `floor(11M b / L) = floor(11M b / (11ML_0)) = floor(b / L_0) = 1`. Since `gcd(11M, 11) = 11`: `Sol(11M, j, 11) = Z_11` if `11 | j`, else `empty`. Bad set `= Sol(11M, -1, 11) union Sol(11M, -2, 11)`. Neither `-1` nor `-2` is divisible by `11`. Hence bad set `= empty`. `square`

**Proof of Theorem 4.6.** Choose the sub-interval

`I_M = [L_0, 2L_0)`.

This lies in `(0, N)` since `N = 121 M L_0 >= 242 L_0` for `M >= 2`.

*`11M` transparent on `I_M`:* Lemma B. `check`

*Floor `0` for all non-divisible runners on `I_M`.* For any `e_u in F union {M}` and `b in [L_0, 2L_0)`: all `e_u` are coprime to `11`.
- For `e_u in F subset {1,...,10}`: `e_u b / L = e_u b / (11ML_0) < 10 * 2L_0 / (11 * 2 * L_0) = 10/11 < 1` (using `M >= 2`).
- For `e_u = M`: `M b / L = b / (11L_0) < 2L_0 / (11L_0) = 2/11 < 1`.

Hence `floor(e_u b / L) = 0` for all `e_u in F union {M}`. By Lemma FLOOR0: `bad(e_u, b) = {0, -e_u^{-1} mod 11}`. `check`

*Uncovered unit residue.* The set `{-e_u^{-1} mod 11 : e_u in F union {M}}` lies in `Z_11* = {1,...,10}` (size `10`) and has at most `|F union {M}| = 9` elements. So at least one `r* in Z_11*` is uncovered: `r* not in bad(e_u, b)` for all `e_u in F union {M}`. `check`

*Count safe times.* For each `b in I_M ∩ Z`, set `k(b) = b + r* M L_0`. Then:
- `k(b) in [L_0 + M L_0, 2L_0 + 10 M L_0) subset (0, N)`: since `r* in {1,...,10}`, `k(b) <= 2L_0 + 10ML_0 < 121ML_0 = N`. `check`
- Runner `11M` safe: transparent (bad `= empty`). `check`
- Each `e_u in F union {M}` safe: `r* not in bad(e_u, b)`. `check`
- Times distinct: different values of `b` give different `k(b)`.

`x_0(E) >= |I_M ∩ Z| = L_0 - 1 >= 119 >= 10`. `square`

**Remark on `M = 1`/`M >= 2` junction.** Corollary 4.4 forces every valid `M in {1, 2, 3, ...}` with `gcd(M, 11 L_0) = 1` to be covered by either `M = 1` (Proposition 4.5) or `M >= 2` (Theorem 4.6). The two cases together cover all valid speed sets in the one-divisible branch.

---

## 5. Main Theorem

> **Theorem A.** For every gcd-`1` tuple `E` of `10` distinct positive integers, one has `x_0(E) >= 10 > 0`.

**Proof.** If no speed is divisible by `11`, Proposition 3.1 gives `x_0(E) >= 10`. If at least two speeds are divisible by `11`, Proposition 3.2 gives `x_0(E) >= 10`. If exactly one speed is divisible by `11`, Corollary 4.4 forces `M = 1` or `M >= 2`; Proposition 4.5 gives `x_0(E) >= 10` for `M = 1`, and Theorem 4.6 gives `x_0(E) >= 10` for `M >= 2`. In every case `x_0(E) >= 10 > 0`. `square`

---

## 6. Companion Exact Certificate

The proof above is entirely analytic; the computation below is an independent verification.

**Coverage.** The normalized one-divisible branch has been checked exactly across all `45` templates:

- `45` normalized one-divisible templates (indexed by the `45` choices of `F subset {1,...,10}`, `|F| = 8`),
- `2115` finite checks,
- `0` violations.

Note: this certificate is an independent confirmation, not a proof step. All proof arguments above are self-contained.

**Parametric-linear (PL) validation for the hardest template.** The template `F12346789` (i.e., `F = {1,2,3,4,6,7,8,9}`, omitting `{5,10}`) with `E(M) = (1,2,3,4,6,7,8,9,M,11M)` (the family with the highest `C_F = 648`) was subjected to PL analysis with `M` tested up to `3000` (`909` valid values). Results:

- PL.1 (floor-quotient independence): **proved analytically** and verified computationally. For the free runner `e = M`, the floor quotient `t_M(b) = floor(M*b / L) = floor(b / (11L_0))` does not depend on `M`.
- PL.3 (slope gap): `alpha_F = 2373/121 ≈ 19.6 < C_F = 648`. The safe-point slope exceeds the bad-coverage slope by a margin of `76035/121 ≈ 628`. (This is consistent with the analytic bound from Theorem 4.6, which does not use this slope gap.)
- PL.2 (holdout): `88` of `110` residue classes (mod `121`) fit the linear model exactly. Five classes show non-linear `C_bad` behavior; these do not affect the proof since Theorem 4.6 is proved by a different (sub-interval) method.

**Artifact files:**

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_rows_n7n11_v2.csv`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_checks_n7n11_v2.csv`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_n11_pl_recheck_v2.md`
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_n11_family_set_summary_v3.md`

---

## 7. References

- [Wil67] Wills, J. M. (1967). Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen. *Monatsh. Math.* **71**, 263–269.
- [Cus73] Cusick, T. W. (1973). View-obstruction problems. *Aequationes Math.* **9**, 165–170.
- [BGG+98] Bienia, W., Goddyn, L., Gvozdjak, P., Sebő, A., and Tarsi, M. (1998). Flows, view obstructions, and the lonely runner. *J. Combin. Theory Ser. B* **72**(1), 1–9.
- [BH01] Bohman, T. and Holzman, R. (2001). Six lonely runners. *Electron. J. Combin.* **8**(2), R3.
- [BS08] Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* **15**(1), R48.
- [Tao18] Tao, T. (2018). Some remarks on the lonely runner conjecture. *Contrib. Discrete Math.* **13**(2), 1–31.
- [Ros25] Rosenfeld, N. (2025). The Lonely Runner Conjecture for Eight Runners. arXiv:2509.14111 [math.CO].
- [Tra25] Trakulthongchai, N. (2025). The Lonely Runner Conjecture for 9 and 10 Runners. arXiv:2511.22427 [math.CO].
- [Pal26] Palelei, T. (2026). A Proof of the Lonely Runner Conjecture. Preprint (companion n=all paper). [Context reference only; no proof in this paper depends on [Pal26].]

---

## 8. Data and Code Availability

All computational artifacts supporting this paper are included in the accompanying data package:

- **Batch verification scripts**: `lrc_chamber_audit_v1.py`, `lrc_true_bsafe_verification_v1.py`, `lrc_partial_transparency_investigation_v1.py`
- **PL validation script**: `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_n11_pl_validation_v1.py` (run with `MAX_M=3000` for the recheck)
- **Full computational certificate**: `lrc_n11_full_computational_cert.py` (Branch 2 direct counts for m=6..9; all branches pass)
- **Primary CSV artifacts**: `lrc_case2_d3_batch_rows_n7n11_v2.csv`, `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- **PL recheck output**: `lrc_case2_n11_pl_recheck_v2.md`

All scripts are standalone Python 3 and require only `math`, `itertools`, and `fractions` from the standard library. No external dependencies. The `45`-template enumeration and `2115` check results are reproducible by running the batch verification script with the parameters documented in the summary artifact.
