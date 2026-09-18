# Door 4, opened: the flank search modulo `b`

2026-09-18. Lean: `LRC/Cascade/Flanks.lean`, three new theorems, all axiom-clean, build 2443 jobs.
Artefacts: `experiments/n8/door4_v1/`. Door 4 is `ExistenceAt8_flank` — see `ATTACK_SURFACE_v1`.

---

## 1. The modulus drops from `n·b` to `b`  `[PROVED]`

`clear_at_int_flank_iff_emod` works modulo `n·b`. Split `a = n·q + s` with `0 ≤ s < n`. Then
`a(nk+1) = n(ak + q) + s`, so the residue modulo `n·b` is `n·((ak+q) mod b) + s`, and:

    Flanks.clear_at_int_flank_iff_emod_b :
      clear at flank b, opening k  ↔  b − s ≤ n·((a·k + q) mod b) ≤ (n−1)·b − s

Checked against the direct form before formalising: **200,000 cases, 0 disagreements**.

**Two things this makes visible that the `n·b` form hides.**

- The condition on `k` is an **arithmetic progression `a·k + q` modulo `b`, landing in a fixed
  interval** — one progression per runner. At `n = 8` the interval has length exactly `3b/4`: the
  middle three quarters.
- **The flank contributes no constraint.** For `a = b` the progression is constant at `q = ⌊b/8⌋`,
  which is exactly the interval's **left edge** — verified 20,000/20,000. So at order 8 there are
  **six** real conditions, not seven.

So door 4 over whole numbers is: *six arithmetic progressions mod `b`, each required to land in its
own interval of relative length `3/4`, must have a common `k`.*

Heuristic density `(3/4)^6 = 0.1780`. Observed at flank `b = max ds`: **median 0.1831**, 10th
percentile 0.1364, minimum 0.0476 over 3,000 sets, and **zero** sets where that flank had no lonely
opening. The conditions behave close to independently, which is why the union bound — `6 × 1/4 = 1.5`
— is the wrong instrument: it adds the failure probabilities where the truth is nearer a product.

## 2. The `k = 0` layer collapses to one flank  `[PROVED]`

    Flanks.inWay_at_first_opening_of_lt : 0 < m → m < b → inWay n m (flankOpening n b 0)
    Flanks.eq_min_of_lonely_first_opening : a lonely first opening forces b = min ds

Flank `b`'s opening `k = 0` is `1/(n·b)`, where a runner at difference `m < b` reads `m/(n·b) < 1/n`
and is in the way. So **only the nearest flank can be free at `k = 0`**, where the condition is
`clear_at_bound_of_ratio`.

This was found as a measured coincidence and then explained: over 20,000 primitive sets, "some flank
works at `k = 0`" and "the *minimum* flank works at `k = 0`" hold on **exactly** the same 11,167 sets.

## 3. How deep the search goes

| | coverage |
|---|---|
| `k = 0` (now a single flank) | 0.552 |
| `k ≤ 2` | 0.938 |
| `k ≤ 8` | 0.999 |

Tight sets `{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}`: all settled at **`k = 0`**, at
flank `b = 1`, where the condition collapses to *no difference divisible by 8*. **The tight
configurations are not the hard ones for door 4.** The named hard arrangements need `k = 6` and
`k = 4`.

**`k` is not bounded**, and a layered proof by cases on `k` therefore cannot terminate:
`bounded_k_attack_v1` reaches `k = 369` at spread ≈ 14,125. The layers above are coverage, not a
proof strategy.

## 4. What door 4 now needs

Stated in the framework's objects, with no trajectory in it:

> Let `b = max ds`. For each `a ∈ ds` write `a = 8q_a + s_a` with `0 ≤ s_a < 8`. Show there is
> `k ∈ [0, b)` with `(a·k + q_a) mod b ∈ [(b − s_a)/8, (7b − s_a)/8]` for every `a`.

Six non-trivial conditions, each of relative length `3/4`. The union bound is vacuous at `1.5`;
measurement says the true density is near the product `0.178`. **The gap between those two numbers is
the whole problem**, and closing it means showing the six progressions cannot conspire — which is a
statement about `a·k mod b` for six values of `a`, not about the cascade.

Known obstruction, recorded so it is not rediscovered: the interval does not factor under CRT, so
splitting `b` into prime parts does not split the condition.
