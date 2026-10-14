# The grid-neighbourhood certificate

2026-09-11. Scripts `experiments/n8/ok_transition_v2.py`, `ok_gridcert_v1.py`,
`ok_localisation_v1.py`. Exact `Fraction`. Supersedes `GRID_TRACKING_v1.md` §4, whose
uniform window was the weak form of this.

Owner's construction: take the AP/grid, where global isolation is exact, as a base; perturb
one speed and map where the cover moves.

---

## 1. What the transition map showed  `[PROVED + VERIFIED exact]`

At `t = 1/8` the AP sits with runner 1 at `‖1/8‖ = 1/8` and runner 7 at `‖7/8‖ = 1/8` — both
**on** the bound — while runners 2..6 are at `1/4, 3/8, 1/2, 3/8, 1/4`, with slack. So
**only the residue-1 and residue-7 runners bind.** Consequences, both measured exactly:

- **Perturbing a non-binding runner does not move the witness.** Sweeping runner 2 over
  `v = 1.1, 1.2, …, 2.9` (cleared to integer tuples), `t = 1/8` remains a witness at **every**
  value — while `|Ḡ|` jumps from `0` at `v = 2` to `≈ 1/30`. The tight instance is an isolated
  zero of `|Ḡ|` in speed space; any perturbation opens loneliness to positive measure.
- **The opening law.** Perturbing the residue-1 runner to `w` opens `[1/(8w), 1/8]`, of length
  `(w−1)/(8w)`; perturbing the residue-7 runner to `w` opens `(7−w)/(8w)`. Predicted against
  measured: **10/10 exact in each direction**.
- Perturbing the binding runner the *wrong* way (`w < 1`) destroys `t = 1/8` outright, since
  runner 1 then demands `t ≥ 1/(8w) > 1/8` while runner 7 demands `t ≤ 1/8`.

## 2. The certificate  `[PROVED]`

Generalising the opening law to all runners at once. At `t = a/8 + ε`, `a ∈ (ℤ/8)*`, put
`r_j = e_j a mod 8`. Runner `j` needs `‖r_j/8 + e_j ε‖ ≥ 1/8`, and the admissible interval
containing `ε = 0` is `[(1−r_j)/(8e_j), (7−r_j)/(8e_j)]`. Therefore

> **`L(a) = max_j (1−r_j)/(8e_j)`,  `U(a) = min_j (7−r_j)/(8e_j)`.**
> **If `L(a) ≤ U(a)`, every `ε ∈ [L(a), U(a)]` gives a witness `t = a/8 + ε`.**

A max and a min of seven explicit rationals. The **wrapped** form lets runner `j` take
interval index `k_j ∈ [−K,K]`, shifting its interval by `k_j/e_j`.

**Why it encodes the known obstruction:** a multiple of 8 has `r = 0`, forcing
`L ≥ 1/(8e) > 0`; a residue-7 runner pins `U = 0`. Their coexistence makes `L > U` — the
Unit-Complete clash, now with a number attached. Separately and exactly
(`GRID_TRACKING_v1` §2): the first-order direction fails **iff** the tuple is Unit-Complete,
31 788/31 788 over the complete enumeration.

## 3. Controls  `[PASS]`

| control | result |
|---|---|
| must fire **degenerately** (`L = U = 0`) on all three tight instances | fires, `L = U = 0`, all three |
| every fired certificate must be a real witness, checked independently at `L`, `U` and the midpoint | 2784 fired, **0** non-witnesses |
| Case 1 must be 100% (the grid point is the witness) | 11 439/11 439 |

## 4. Coverage, exhaustive over `[1..18]`  `[VERIFIED — exhaustive in box]`

| | principal (`K=0`) | `K = 1` | `K = 2` |
|---|---|---|---|
| Case 1 (11 439) | **100.00%** | — | — |
| Case 2 (20 349) | 61.79% | **99.94%** | **100.00%** |
| Residual (6250) | 51.86% | **99.79%** | **100.00%** |

Exactly **13** Case-2 tuples escape `K = 1`, all of them in the residual, and every one is
covered at `K = 2`: `(1,3,5,6,7,8,18)`, `(1,3,5,7,8,11,18)`, `(1,5,6,7,8,11,13)`,
`(3,7,10,11,14,16,18)` and nine others. `E*` fires already at `K = 1` — **the extremum is not
the hard case for this certificate**, which is the reverse of every other route tried.

For scale: the uniform-window version of the same idea reached 14.05% on Case 2, and the
small-denominator lemma reached 69.29%.

## 5. The localisation conjecture is false  `[REFUTED — exhaustive]`

`K = 1` means `|ε| ≲ 1/e_max`, which invites: *every witness lies within `1/e_max` of a grid
point*. Let `ρ(E)` be the exact distance from the nearest grid point to `Ḡ(E)`. Over the
complete `[1..18]` Case 2, **194 tuples have `ρ·e_max ≥ 1`**, the max being `18/11 = 1.636` at
`(1,3,5,7,8,11,18)`. Sampled at larger boxes the statistic **grows**: `2.125` at `[1..40]`,
`2.946` at `[1..120]`, `9.625` at `[1..600]`. Since `max ρ` itself shrinks (`1/10 → 9/512`),
the implied scaling is nearer `ρ ~ C/√e_max` than `C/e_max` — recorded as an observation, not
a law: those rows are sampled with falling sample sizes, which biases a maximum downward.

## 6. A bug of mine, fixed, with the affected numbers re-verified  `[recorded]`

The `k = 0` blocked arc `(−1/(8e), 1/(8e))` **wraps**; clipping it to `[0, ·)` left `{0}` as a
spurious isolated good point, and `t = 0` is never good. Fixed. Re-run under the fix: Case 1
still 0 failures, and `GRID_TRACKING_v1`'s exhaustive `max ρ = 1/10` at `(1,2,3,5,6,7,8)` is
**unchanged**. This is the second boundary/endpoint bug this session; both were caught by a
control, neither reached a published number.

## 7. Ledger

`[PROVED]` §2 the certificate and the wrapped form; §1's opening laws, verified 10/10 each.
`[VERIFIED — exact]` §1's runner-2 sweep; §3 all three controls.
`[VERIFIED — exhaustive in box]` §4's coverage table and the list of 13 escapees, complete
enumeration of `[1..18]`.
`[REFUTED — exhaustive]` §5, `ρ·e_max < 1`, 194 counterexamples in the box.
`[EMPIRICAL — sampled, downward-biased]` §5's growth rows and the `1/√e_max` reading.
`[recorded]` §6.

`n = 8` is **not proved**: coverage is exhaustive in a box, not a theorem about all tuples, and
`K` is not bounded a priori. What is new is a cheap sufficient condition that is *sharp at the
tight instances*, covers the residual at `K = 1` to 99.79%, and for which the extremum is easy.
