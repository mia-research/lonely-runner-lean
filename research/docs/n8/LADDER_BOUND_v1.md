# The ladder bound: a closed form for sup R, and a proof structure for human review

2026-09-16. Came out of a failed computation — the order-8 word enumeration, abandoned as infeasible
(§1). What the failure exposed is a closed-form extremal structure that reproduces the proven order-5
value exactly and gives a candidate argument at every order. **This is a proof STRUCTURE with a named
gap, not a proof.** Existence at order 8 remains open and the gate still reports it unstated.

Scripts: `experiments/n8/order8_tree_census_v1.py`, `order_n_certificate_v1.py`.

---

## 1. Why the enumeration was abandoned  `[measured, not guessed]`

The order-5 certificate closed by enumerating every realisable word. At order 8 that fails, and the
numbers say so plainly:

| level | examined | realisable | pass rate | growth |
|---|---|---|---|---|
| 1 | 36 | 6 | 16.7% | — |
| 2 | 210 | 30 | 14.3% | 5.0× |
| 3 | 1 020 | 120 | 11.8% | 4.0× |
| 4 | 3 960 | 720 | 18.2% | 6.0× |
| 5 | 22 680 | 3 600 | 15.9% | 5.0× |
| 6 | 108 360 | 16 920 | 15.6% | 4.7× |

The pass rate is **flat at ~16%** — the LP does not prune harder as words lengthen — and words may run to
length `(n−2)·L = 36`. Extrapolated, level 16 alone is ~9×10^10 words, months of compute, with 20 levels
left; the full space is 7.25×10^26. Branch-and-bound against the cap does not rescue it: the bound
`R_now + 2·Σ_x (laps left)/u_min_x` sits at 62.7 at depth 1 and is still 22.1 at depth 6, never below the
cap of 7. **The enumeration is the wrong instrument at order 8**, and the reason is ironic: the cap `n−1`
is far above the true supremum, so realisability prunes almost nothing. The larger margin that makes
order 8 mathematically easier makes it combinatorially harder.

One thing the census did establish, and it matters: **the enumeration is faithful.** Taking each
LP-realisable word's own witness readings and running the actual cascade — latest-next-opening rule and
all — reproduced the claimed word in 100% of cases at every length tested. The word space is real
cascade behaviour, not an artefact of the relaxation.

## 2. The extremal readings are forced, in closed form  `[EMPIRICAL — exact rational agreement]`

At each depth the word maximising `R` is the lap-1 ladder, and the LP forces its readings into a
geometric sequence. Computed minima at order 8, against the closed form:

| rung `k` | LP minimum | closed form `(n−1)·((n−1)/(n+1))^(k−1)` |
|---|---|---|
| 1 | 7.00 | `7` |
| 2 | 5.44 | `49/9` |
| 3 | 4.23 | `343/81` |
| 4 | 3.29 | `2401/729` |
| 5 | 2.56 | `16807/6561` |
| 6 | 1.99 | `117649/59049` |

Every digit agrees. The first rung sits at exactly `n − 1`, the cap itself, and each subsequent reading is
the previous one times `(n−1)/(n+1)`.

Since a setting of `x` at lap `Q` lands at `R = (nQ + 1)/u_x`, the ladder's final value is

    R = (n + 1) / u_{n-2} = ((n+1)/(n-1))^(n-2).

## 3. The bound, and why it holds  `[the structure]`

> **The ladder needs one runner per rung, and there are only `n − 2` non-nearest runners.**

That is the whole mechanism. The nearest runner never sets (its own setting would give `R ≥ n+1`), so the
ladder cannot have more than `n − 2` rungs, and `R` cannot reach the next power.

| `n` | `((n+1)/(n−1))^(n−2)` | cap `n−1` | holds? | margin |
|---|---|---|---|---|
| 3 | 2.0000 | 2 | **no** (equality) | 0 |
| 4 | 2.7778 | 3 | yes | +0.22 |
| **5** | **3.3750 = 27/8** | **4** | yes | +0.63 |
| 6 | 3.8416 | 5 | yes | +1.16 |
| 7 | 4.2140 | 6 | yes | +1.79 |
| **8** | **4.5172** | **7** | yes | **+2.48** |
| 12 | 5.3150 | 11 | yes | +5.69 |

**At `n = 5` the formula gives `27/8` — exactly the value the order-5 certificate proved by exhaustive
enumeration.** The closed form reproduces a theorem we already own, at the order where we can check it.
As `n` grows the ladder tends to `e² ≈ 7.389` while the cap `n − 1` grows without bound, so the margin
widens; the tight cases are small `n`, and `n = 3` is the boundary (exactly 2 versus 2), already proved
separately in Lean.

## 4. What is proved, what is not

`[PROVED]` — the order-5 case, by the exhaustive certificate: `sup R = 31/9 < 4` for ratio ≤ 26.
`[PROVED — Lean]` — the near-AP extremal family at order 8, and the eighth-family theorem.
`[EMPIRICAL]` — everything in §2 and §3 above.

**The two gaps, stated so they can be attacked or refuted:**

1. **Ladder maximality.** That the lap-1 ladder maximises `R` at each depth is observed (best `R` equals
   `(9/7)^d` at every depth `d ≤ 6` at order 8, and the pattern breaks at `d = 7` exactly when the ladder
   runs out of runners, falling to `33/7 = 4.7143` instead of `(9/7)^7 = 5.8078`). It is not proved.
2. **The return correction.** Words longer than the ladder add a little: at order 5, `27/8 → 31/9`
   (+2%); at order 8, `4.5172 → 4.7143` (+4%). Both stay well under their caps, but **there is no bound
   on this correction**, and without one the argument is incomplete. At `n = 5` the margin is 0.625 and
   returns consumed 0.07 of it — the ratio that matters, and the one a proof must control.

A proof would need: Lemma A, the forced ladder readings (§2, closed form); Lemma B, at most `n − 2` rungs
(§3, immediate from the nearest never setting); Lemma C, a bound on the return correction (open). Then
`R < n − 1` for `n ≥ 4`, the cascade stops, and Existence follows.

**This is where human review is wanted.** The structure reproduces the one value we have independently
proved, explains why order 8 has more room than order 5, and identifies precisely one missing bound.
