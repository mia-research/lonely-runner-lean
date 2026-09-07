# `r = 1` attacked; the witness-denominator route opened and closed; one correction

2026-09-07. Continues `HALVING_AND_TIGHT_WITNESS_v1.md`. Artifacts:
`experiments/n8/{r_ge_2_cover_v1, witness_denominator_v1, witness_denominator_v2,
D_unbounded_and_largespeed_v1, witness_structure_v1}.py`.

## 0. Correction to `HALVING_AND_TIGHT_WITNESS_v1.md` §2

**Theorem P's `x = 1` case is not new.** It is the pre-jump reduction of Bienia,
Goddyn, Gvozdjak, Sebő and Tarsi 1998 — statement (2) in that paper, transcribed in
this project's own memory as `bienia_n4_proof.md`:

> "**(2) Pre-jump reduction.** Let `v ∈ ℕ^k`, `k ≥ 3`. If `gcd(v_1,…,v_{k−1})` does
> not divide `v_k`, then there exists a time when `R` is distant iff there exists a
> time when `R \ {k}` is distant."

That is exactly the `x = 1` branch, and `x = 1` supplies **54 802 of the 71 826** sets
Theorem P settles at speeds `≤ 32` — 76% of it. The genuine extension is the deletion
of **two or three** runners at once (`x = 2, 3`: 16 766 + 258 sets, 24%). The theorem
stands as proved; the novelty claim does not. This is the project's own source-first
rule: the argument was in the corpus and was not read first.

## 1. `r = 1`: attacked, and the natural route is dead  `[PROVED that the route fails]`

Recall the reduction: *no tight instance contains a multiple of `n`* ⟺ *every tight
instance has witness denominator exactly `n`*, i.e. `r = 1` where `q = nr`.

The decidable necessary condition. With `w_v = v p mod q` and
`Block(w) = {c ∈ ℤ/q : |c·w|_q ≤ r}`, tightness forces the seven sets `Block(w_v)` to
**cover `ℤ/q`** — otherwise the missed `c` gives `t = c/q` with every runner strictly
beyond `1/8`. So if the minimum number of band residues whose `Block`s cover `ℤ/8r`
exceeded 7, `r ≥ 2` would be impossible.

Computed exactly (iterative-deepening branch and bound on bitmasks, no greedy answer
reported): **the minimum cover is 3 for every `r` from 1 to 12.** Three residues
`r, 3r, 4r` always suffice, because `|c·(jr)|_{8r} = r·|jc|_8` collapses the problem to
`ℤ/8`. Seven speeds are far more than needed.

**So this necessary condition cannot exclude `r ≥ 2`.** The route is closed for a
stated reason, not by a null: the condition is satisfiable, and the reason is that
multiples of `r` degenerate the covering to `ℤ/8`.

*What survives.* The three-set cover uses only multiples of `r`; if **all** `w_v` were
multiples of `r` then `r | v` for every `v`, so `r | gcd(T) = 1`. Hence `r ≥ 2` forces
at least one speed off every prime dividing `q` — a real constraint, and the only
piece of leverage this analysis leaves.

## 2. The empirical base for `r = 1`, widened  `[EMPIRICAL — exhaustive, ranges stated]`

| `n` | speed bound | tight instances | witness `r` values | containing a multiple of `n` |
|---|---|---|---|---|
| 5 | 70 | 2 | `{1}` | 0 |
| 6 | 50 | 2 | `{1}` | 0 |
| 7 | 34 | 1 | `{1}` | 0 |
| 8 | 22 | 3 | `{1}` | 0 |

Every witness of every tight instance found has `r = 1`, and the witness set is exactly
`{k/n : gcd(k,n) = 1}` in all eight.

## 3. A second proved reduction: the large-speed lemma  `[PROVED from LRC(7)]`

> If some `v ∈ T` satisfies `v ≥ 28·max(T \ {v})`, then `M(T) ≥ 1/8`.

*Proof.* LRC(7) on the other six gives `t₀` with `‖v_i t₀‖ ≥ 1/7`. On
`J = [t₀ − δ, t₀ + δ]`, `δ = (1/7 − 1/8)/m = 1/(56m)` with `m = max(T\{v})`, all six
stay `≥ 1/8`. `|J| = 1/(28m) ≥ 1/v` is a full period of `v`, and every period of `v`
contains a sub-interval of length `3/(4v)` on which `‖vt‖ ≥ 1/8`. ∎

## 4. The witness-denominator route — opened, measured, closed

Define `D(T) = min{q ≥ 2 : ∃a, gcd(a,q)=1, ‖v·a/q‖ ≥ 1/8 ∀v ∈ T}`.

**Why it was worth opening.** `‖v·a/q‖ ≥ 1/8` depends only on `v mod q`. So if
`D(T) ≤ Q₀` on the residual case, LRC(8) there becomes a statement about residue
vectors mod `lcm(2..Q₀)` — finitely many cases, **a proof rather than a search over
speeds**. And unlike the earlier 2-adic run, boundedness is *not* forced: density of
the rationals gives only `D ≲ c·max(T)`, i.e. growth.

**Control fires.** At threshold `1/7` the three tight instances (`M = 1/8 < 1/7`)
return `D = None`, as they must.

**Exhaustive measurement over the residual case** — every set, not a sample:

| speed bound | 16 | 20 | 24 | 28 | 32 | 36 |
|---|---|---|---|---|---|---|
| residual sets | 2 561 | 12 673 | 76 902 | 239 556 | 710 038 | 1 845 768 |
| **max `D`** | 23 | 23 | 28 | 28 | 28 | 28 |

A flat plateau at 28 across four consecutive bounds and 1.85 million sets. That reads
like a bound. **It is not.**

**`D` is unbounded, by construction and in one line.** If `q | v` for some `v ∈ T`
then `‖v·a/q‖ = 0` for every `a`, so level `q` is dead outright. Taking a single speed
`v = lcm(2,…,Q)` kills every level `q ≤ Q` at once, so `D(T) > Q`. Measured on
`T = {L, L+1, L+2, L+3, L+5, L+7, L+11}`, `L = lcm(2..Q)`, `gcd(T) = 1`:

| `Q` | 18 | 24 | 30 | 36 | 44 | 52 |
|---|---|---|---|---|---|---|
| `D(T)` | 23 | 25 | 32 | 41 | 47 | 53 |

`D` grows. Since `lcm(2..Q) = e^{(1+o(1))Q}`, forcing `D > Q` costs
`max(T) ≥ lcm(2..Q)^{1/7}`, so `D = Θ(log max T)` — unbounded, but only
logarithmically, which is why the plateau at speeds `≤ 36` is real and misleading at
the same time. **The finite-residue-check route is closed.**

*Also worth recording:* the three exhaustive minimisers of `M` over the residual case
(`M = 2/15`) all have `D = 15`. The sets hardest by `M` are not the sets hardest by
`D`; the two difficulty measures are not the same order.

## 5. Where this leaves the programme

Settled analytically so far, none of it assuming LRC(8):

| case | tool | status |
|---|---|---|
| missing a ladder level `q ≤ 7` | `t = 1/q` | one line |
| no multiple of 8 | `t = 1/8` | one line; contains every known tight instance |
| `gcd` of six speeds `≥ 2` | Bienia (2) | known |
| two or three speeds deleted | Theorem P `x = 2,3` | this project |
| one speed `≥ 28×` the rest | large-speed lemma | this project |
| **everything else** | — | **open** |

Together the reductions cover about a tenth of the residual case at speeds `≤ 32`.

**What to look at next, and why.** Two independent routes have now landed on the same
object. From the Rosenfeld side, `COLLAPSE_Z163_v2.md` §2 built a **2-adic cap table**
and a sector decomposition on `x = #{v ∈ T : 8 | v}`. From this side, the ladder makes
`8 | v` the defining feature of the residual case, and the tight instances are exactly
those without it. Barajas–Serra's `n = 7` proof — which this project owns, formally
verified and axiom-clean — is a **prime-filtering argument on the `7`-adic valuation**.
`n = 8 = 2³` is the prime-power case, and its natural analogue is filtering on the
**2-adic valuation**, which is precisely what both routes have independently built.
That convergence, not another reduction lemma, is the thing to follow.

`r = 1` remains open and is *not* the recommended next target: it presupposes LRC(8)
and would not prove it.
