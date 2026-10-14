# A closed form for `α` — and the criterion it does, and does not, give

2026-09-10. Follows `ALPHA_v1.md`. Script `experiments/n8/ok_alpha_closed_v1.py`.
Exact `Fraction`; no float on any decision path.

---

## 1. The closed form  `[PROVED — exact, 0 mismatches / 200]`

Let `φ(Y) = |{y ∈ [0,Y] : ‖y‖ < 1/8}|`. Then `|A_x ∩ [0,s]| = φ(xs)/x` and
`φ(Y) = ⌊Y⌋/4 + φ({Y})`, so with `ψ(θ) := φ(θ) − θ/4`,

    |A_x ∩ [0,s]| = s/4 + ψ({x s})/x,

        ψ(θ) =  3θ/4        on [0, 1/8]
                1/8 − θ/4   on [1/8, 7/8]        range exactly [−3/32, 3/32].
                3(θ−1)/4    on [7/8, 1]

Summing over the components `(u_i, v_i)` of `G = G(H)`:

> **`α_x = 1/4 + S_x /(x·|G|)`,   `S_x = Σ_i [ ψ({x v_i}) − ψ({x u_i}) ]`.**

Elementary, exact, and **endpoint-only** — it needs nothing about `G` but its component
endpoints. Verified against direct interval computation for `x = 1..200`: **0 mismatches**.
Reproduces the named values: `α_7 = 18/41`, `α_13 = 505/1066`, `α_4 = 25/41`,
`α_22 = 296/451`, and `α_x = 0` exactly for `x ∈ {3,16,20,28,32}` (there `S_x = −x|G|/4`).

## 2. The decay bound  `[PROVED — 0 violations / 500, ~90% tight]`

`|ψ| ≤ 3/32`, so `|S_x| ≤ 3N/16` with `N` the number of components of `G`. Hence

> **`|α_x − 1/4| ≤ 3N/(16 x |G|) = C/x`,  `C := 3N/(16|G|)`.**

`α_x → 1/4` at rate `O(N/x)`: **large off-grid speeds are asymptotically generic.** The
bound is dilation invariant (`N` scales with `λ`, `x` with `λ`). For the grid
`{2,6,8,10,14}` (`|G| = 41/560`, `N = 8`): `C = 840/41 ≈ 20.4878`. Over `x = 1..500`, zero
violations, and the worst case reaches `18.5244` — **90% of the bound, so there is no
square-root cancellation to harvest.**

## 3. The criterion, and its honest reach  `[PROVED; and it fires nowhere useful]`

`Σ_v α_v < 1` forces `|G(H ∪ O)| ≥ |G|(1 − Σα_v) > 0`. With the bound:

> **If `r/4 + C·Σ_{v∈O} 1/v < 1` then `G(H ∪ O) ≠ ∅`** (`r = |O|`).

Its consequence is a genuine finiteness statement — for the grid above,
survival `< 1/10` requires `1/x + 1/y > 41/2100`, hence `min(x,y) < 103`; survival `< 1/4`
requires `min(x,y) < 164`.

**But it fires on 0 of 509 Case-2 tuples in `[1..18]`.** `C` is too large in the
small-speed regime, which is exactly where the extremum lives (`E*` has `1/7 + 1/13 =
20/91`, two orders above the threshold). The bound bites only on **large** off-grid speeds,
and those are the easy ones.

## 4. A circularity caught, and discarded  `[the important part]`

The same script also scored a variant: "`Σ` of the **true** `α_v` `< 1`". It settled
**509 / 509**. That figure is **worthless and is not counted**.

For `r = 1`, `α_v < 1` says `A_v` fails to cover `G(H)` — which *is* the statement
`|G(T)| > 0`. It recomputes the conclusion under another name, so it returns 100% for any
true theorem and would return 100% if the conjecture were replaced by any other true one.
It is a **forced** statistic. The script now labels that branch `CIRCULAR-do-not-count` and
prints only the a-priori row.

This is the failure mode that a 100% result should always trigger a check for: the
criterion has to be decidable **without** evaluating the thing it is predicting.

## 5. Ledger

`[PROVED — exact]` §1 closed form (0/200 mismatches) and the `α_x = 0` characterisation
`S_x = −x|G|/4`; §2 the bound (0/500 violations) and its near-tightness; §3 the criterion
and the finiteness consequence.
`[REFUTED — circular]` §4, the exact-`α` variant; 509/509 is forced and is retracted.

`n = 8` is **not proved.** What §1–§2 add is that `α` — the statistic that *reads* the
deficit — is now in closed form and its deviation from generic is `O(N/x)`, provably and
near-tightly. What §3 concedes is that the resulting a-priori criterion is powerless in the
small-speed regime, so the closed form is at present a **structural** gain and not a
witness-producing one. The obstruction is explicit and quantitative: `C = 3N/(16|G|)`, with
no cancellation available to shrink it.
