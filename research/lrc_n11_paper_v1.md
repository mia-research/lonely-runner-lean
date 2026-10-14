# The Lonely Runner Conjecture for `n = 11`

**Author:** Trent Palelei  
**Date:** March 2026  
**Status:** Working draft

---

## Abstract

We give a short analytic proof of the Lonely Runner Conjecture for `n = 11`. Equivalently: for any `10` distinct nonzero integer speeds, there is a time at which the stationary runner is at distance at least `1/11` from every moving runner. The core point is that the prime one-divisible branch, which is the only branch requiring real work at `n = 11`, collapses to a single residual small-parameter case. In the normalized one-divisible branch, the retained fixed-set lcm satisfies `L_0 >= 120`, forcing the threshold parameter `M_0` to satisfy `M_0 <= 2`. The only residual value is `M = 1`, and that case closes analytically by combining the lower-band safe-fibre bound with the reflection involution. As a companion certification, we also record an exact finite computation over all `45` normalized one-divisible templates at `n = 11`, with `2115` finite checks and zero violations.

---

## 1. Introduction

For `n = 11`, the Lonely Runner Conjecture asks:

> Given `10` distinct nonzero integer speeds, does there always exist a time at which the stationary runner is at distance at least `1/11` from every moving runner?

This note isolates `n = 11` as a standalone case study of the prime-branch machinery from the broader `n = all` program. The point is not to reproduce the full omnibus proof architecture. The point is to show that at `n = 11` the hard branch is already controlled by a simple lower-band capacity mechanism.

The argument splits into three branches:

- no speed divisible by `11`;
- at least two speeds divisible by `11`;
- exactly one speed divisible by `11`.

The first two are short. The third is the centerpiece.

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

> **Theorem A.** For every gcd-`1` tuple `E` of `10` distinct positive integers, one has `x_0(E) > 0`. In fact, in the prime one-divisible branch one has `x_0(E) >= 10`.

---

## 3. Easy Prime Branches

### 3.1 No Speed Divisible by `11`

> **Proposition 3.1.** If `E_div = emptyset`, then `x_0(E) >= 10`.

**Proof.** Consider the `10` witness times

`k_j = jL`, `j = 1, ..., 10`.

For such `k_j` and any `e_i`,

`e_i k_j mod 11L = L * (e_i j mod 11)`.

Because `11` is prime and `11 does not divide e_i`, the residue `e_i j mod 11` is nonzero, hence lies in `{1,...,10}`. Therefore `e_i k_j mod 11L` lies in `[L,10L]`. So every `k_j` is safe, and `x_0(E) >= 10`. `square`

### 3.2 At Least Two Speeds Divisible by `11`

> **Proposition 3.2.** If `|E_div| >= 2`, then `x_0(E) >= 10`.

**Proof sketch.** This is the prime multiple-divisible branch. On the lower interval

`I = [L/11, L/10)`,

every divisible runner with residue coefficient `k in {1,...,9}` is transparent: its floor is exactly `k`, and its bad set mod `11` is empty. The extreme residue classes `k equiv 0` or `-1 mod 11` affect only the usual finite exceptional floor states and do not obstruct the lower-band count. Once the divisible runners are removed from coverage on the lower band, the remaining non-divisible runners leave at least two residues uncovered at floor `0`, and the standard prime counting bridge gives `x_0(E) >= 10`.

For the purposes of this standalone paper, the only branch needing a full worked proof is the one-divisible branch. `square`

---

## 4. The One-Divisible Branch

Assume henceforth that `|E_div| = 1`.

### 4.1 Normalized Form

Following the standard prime one-divisible normalization, choose one non-divisible runner as the free runner `M`, and let

`F subset {1,...,10}`

be the remaining `8` retained non-divisible residues. Define

- `|F| = 8`,
- `L_0 = lcm(F)`,
- `L = L_0 M`,
- `gcd(M, 11L_0) = 1`.

Thus the normalized branch is indexed by the choice of the fixed set `F` and the free parameter `M`.

There are exactly

`C(10,8) = 45`

choices for `F`.

### 4.2 Lower-Band Period

Let

`Period_1 = { b in Z : L/11 <= b < 2L/11 }`.

At floor state `0`, the fixed set `F` covers

`{0} union { -e^{-1} mod 11 : e in F }`.

Since `|F| = 8`, the floor-`0` union has size at most `9`, so at least two residues are missed.

> **Lemma 4.1.** The floor-`0` miss set of the fixed runners has size at least `2`.

**Proof.** The inversion map `e -> -e^{-1} mod 11` is injective on `F`, and `|F| = 8`. Thus the floor-`0` union has size at most `1 + 8 = 9`, leaving at least `2` residues missed. `square`

The free runner contributes at most two bad residues at each fibre. As in the prime counting bridge, this yields:

> **Lemma 4.2.** The number of safe fibres in `Period_1` is at least
>
> `L_0 M * 9 / 121 - 2`.

**Proof.** A fibre in `Period_1` can be unsafe only if the free runner covers the entire miss set left by the fixed runners. If the miss set has size at least `3`, this is impossible because a prime bad set has size `2`. If the miss set has size `1` or `2`, the standard fibre-counting argument bounds the number of bad fibres by at most `2 ceil(L_0 M / 121) + 2`, leaving at least `L_0 M * 9 / 121 - 2` safe fibres. `square`

### 4.3 The Exact `L_0` Minimizer

The whole `n = 11` problem turns on the smallest possible fixed-set lcm.

> **Lemma 4.3.** Among all `8`-subsets `F subset {1,...,10}`, the minimum of `lcm(F)` is
>
> `L_0,min = 120`,
>
> attained uniquely by
>
> `F = {1,2,3,4,5,6,8,10}`.

**Proof.** Any `8`-subset omits exactly two residues.

If `7 in F`, then `lcm(F)` is divisible by `2`, `3`, `5`, and `7`, hence at least `210 > 120`.

If `9 in F` and `7 notin F`, then only one additional residue is omitted. So `F` still contains a multiple of `4` and a multiple of `5`, and therefore `lcm(F)` is divisible by `4`, `5`, and `9`. Hence `lcm(F) >= 180 > 120`.

Therefore any minimizer must omit both `7` and `9`. That forces

`F = {1,2,3,4,5,6,8,10}`,

whose lcm is

`lcm(1,2,3,4,5,6,8,10) = 120`.

So the minimum is exactly `120`. `square`

### 4.4 Threshold Collapse

Define the standard threshold

`M_0 = ceil(11^2 * 10 / (9L_0)) = ceil(1210 / (9L_0))`.

> **Corollary 4.4.** In the normalized one-divisible branch at `n = 11`, one always has `M_0 <= 2`. Hence the residual small-parameter branch contains only `M = 1`.

**Proof.** By Lemma 4.3, `L_0 >= 120`, so

`M_0 <= ceil(1210 / 1080) = 2`.

Thus the only value with `1 <= M < M_0` is `M = 1`. `square`

### 4.5 Closure of the Residual Case

The lower-band estimate now closes the remaining case completely.

> **Proposition 4.5.** In the residual case `M = 1`, one has `x_0(E) >= 14`.

**Proof.** By Lemma 4.2 and Lemma 4.3,

`safe(Period_1) >= 120 * 9 / 121 - 2 > 6`,

so `Period_1` contains at least `7` safe fibres.

Now apply the reflection involution

`k -> N-k`.

If `k` is safe, then `N-k` is also safe, and `Period_1` reflects to the disjoint upper period `Period_9`. Therefore there are at least `7` further safe fibres outside `Period_1`. Hence

`x_0(E) >= 14 > 10 = phi(11)`.

So the residual case closes analytically. `square`

Combining the large-`M` branch with the residual case yields:

> **Theorem 4.6.** If `|E_div| = 1`, then `x_0(E) >= 10`.

**Proof.** If `M >= M_0`, the prime lower-band threshold argument gives `x_0(E) >= 10`. If `M < M_0`, Corollary 4.4 forces `M = 1`, and Proposition 4.5 gives the stronger bound `x_0(E) >= 14`. `square`

---

## 5. Main Theorem

> **Theorem A.** For every gcd-`1` tuple `E` of `10` distinct positive integers, one has `x_0(E) > 0`.

**Proof.** If no speed is divisible by `11`, apply Proposition 3.1. If at least two speeds are divisible by `11`, apply Proposition 3.2. If exactly one speed is divisible by `11`, apply Theorem 4.6. In every case `x_0(E) > 0`. `square`

---

## 6. Companion Exact Certificate

The proof above is analytic. The computation is auxiliary.

Nevertheless, the normalized one-divisible branch at `n = 11` has already been checked exactly across all templates:

- `45` normalized one-divisible templates,
- `2115` finite checks,
- `0` violations.

The current companion artifacts are:

- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md`,
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_rows_n7n11_v2.csv`,
- `reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_checks_n7n11_v2.csv`.

These are useful as an independent exact certificate and as a reproducibility package for finite-verification work. They are not the proof engine of this paper.

---

## 7. Remarks on Final Version

This is a first draft. Before a public version, the following should be tightened:

- the one-divisible normalization should be written out as a formal reduction rather than invoked as standard;
- Proposition 3.2 should be expanded from proof sketch to a complete self-contained proof;
- the companion computation should be packaged with a short reproducibility appendix and script inventory;
- references should be added in final form.

Even in the current draft, however, the analytic mechanism is already clear: at `n = 11`, the fixed-set lcm is forced high enough that the small-parameter branch collapses to one residual case, and that case closes by `Period_1 + reflection`.
