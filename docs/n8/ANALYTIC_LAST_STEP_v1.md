# Making the last step analytical: what reduces, what does not, and where the wall is

The last step is **band 2 unreachability**: for every profile, `[1,7] ∪ [9,15]` contains a clear
point, hence `R < 16`, hence Existence. Four attacks, reported in the order tried.

---

## 1. The chain reduction — **it does make the question finite and decidable**

Write `u_i = 1/s_i`. Comb `i`'s bad intervals are `[(8k−1)u_i, (8k+1)u_i]`. A union of intervals
covers a region **iff they chain**: ordered by left endpoint, each next starts before the previous
ends. Every such condition,

```
        (8k_j − 1)·u_{i_j}  ≤  (8k_{j−1} + 1)·u_{i_{j−1}} ,
```

is **linear in `u`**, as are the ordering `1 > u_2 > … > u_7` and `u_7 < 1/7` (from `S > 7`).

> **Band 2 is reachable ⟺ some chain's linear system is feasible.**

So the question is a finite union of LP feasibility problems — decidable, with a Farkas certificate
available for each infeasible case. That is a genuine change in kind from an unbounded search over
`t`. The cost is the number of chains, and §4 says why that is not small.

## 2. The candidate-point shortcut — **fails, and instructively**

A necessary condition, far smaller than the full covering: band 2 requires every candidate
`R_k = (8k+1)/S` in `[1,15]` to be non-clear. Setting `v_i = s_i/S` (so `v_7 = 1`, clear there by
construction), this asks the five remaining `v_i ∈ (1/8,1)` to kill ~14 points.

**A single `v ≈ 0.981` kills all of them.** A reading just below `S` sits just inside every band edge
that `S` touches. The condition is trivially satisfiable and carries no information. Recorded because
it looked like the natural reduction and is not.

## 3. The reach lemma, and a refinement that uses the comb count

**Reach lemma.** *If `x` lies in a bad interval of comb `s` at level `m`, then `s·x > 8m−1`, so that
interval's right endpoint is `(8m+1)/s < x·(8m+1)/(8m−1) ≤ 9x/7`.* Each covering step multiplies the
reach by at most `9/7` — the same constant as the dilation bound (v11 Theorem 6.25), because the
covering chain *is* the cascade.

**Refinement.** Comb `i` has exactly **one** interval at each level `m`. With six combs, at most `6`
steps can be at `m = 1` (multiplier `9/7` each), at most `6` more at `m = 2` (`17/15`), and so on.
Spending the cheapest levels first bounds the reach after `6M` steps by
`∏_{m≤M} ((8m+1)/(8m−1))^6`, and inverting gives a **sharper lower bound on the number of steps**
than `log R / log(9/7)`:

```
     case        depth      R      naive ≥    refined ≥
   23-move         23   10.3125       10          13
   28-move         28   10.2607       10          13
   27 banded       27   10.5814       10          14
   R = 11.93       28   11.9271       10          15
   R = 11.96       27   11.9648       10          15
```

Valid on every case, and sharper by 3–5 steps. `[EMPIRICAL — verified]`; the per-step half is
`[PROVED]` (`DilationBound.dilation_lt_nine_sevenths`), the level-counting half is not formalised.

## 4. Why this does not close it — a route eliminated

The refined bound says what band 2 would cost:

```
    reaching R = 15 : ≥ 18 steps        reaching R = 17 : ≥ 20 steps
```

**So band 2 requires depth ≥ 20 — and cases of depth 28 exist.** Therefore:

> **No ceiling on the cascade's depth can exclude band 2.** A depth ceiling would have to be below
> 20, and 28 is exhibited.

That closes off "bound the move count, and band 2 follows" as a route, which is worth knowing
because it is the route the step law appears to offer. The reach product also **diverges** —
`∏_{m≤M}((8m+1)/(8m−1))^6` grows without bound — so it never forbids reaching any `R`. It bounds
steps from below; it does not bound `R` at all.

## 5. Where the wall actually is

What survives is §1: the question is finite and decidable, and infeasibility of every chain would be
a proof. The obstruction is the **number of chains**. The reach lemma says a chain covering `[1,15]`
needs ≥ 18 steps; with six combs and levels up to ~15 that is on the order of `90^18` sequences
before pruning. LP pruning at every partial chain is what the search does, and it is not obviously
enough.

**What a proof needs is an interlocking obstruction** — a reason six arithmetic-progression-of-
intervals families cannot mesh — not a counting one. Counting has given `1.5×` at every level it was
tried (6 combs × density `1/4` over 12 units against 12 needed), and the one structural fact pointing
the right way remains v11 Theorem 11.3: the best coverer, the AP, fails by exactly eight points
protected by the unit group, and is simultaneously the *worst* case for `R`.

## 6. Status

| | |
|---|---|
| band 2 reachability is a finite union of LPs | **yes** — §1, and decidable |
| the candidate-point necessary condition | **useless** — one `v` kills all |
| per-step reach ≤ `9x/7` | `[PROVED]` |
| refined depth lower bound using six combs | `[VERIFIED]` on all cases, not formalised |
| a depth ceiling could exclude band 2 | **no** — band 2 needs ≥ 20, depth 28 exists |
| band 2 excluded | **no** |

```bash
python3 experiments/n8/necessary_v1.py    # the shortcut that fails
python3 experiments/n8/reach_bound_v1.py  # the reach lemma and its refinement
python3 experiments/n8/lp_cover_v2.py     # the LP-pruned chain search
```
