# The small-denominator witness — 69.29% of Case 2 closes in one line

2026-09-11. Script `experiments/n8/ok_collapse_law_v1.py`. Exact `Fraction`, no float on any
decision path. All controls fired; one control caught an error of mine before it reached a
result (§2).

Provenance: **GECT Verification Log (11 Sep 2026)**, §1 (the collapse law) and §7.1
(`N(V,n) = Σ_{d|n, d ∤ v} φ(d)`, verified there on 42 000 speed sets, zero mismatches). The
contribution here is dropping one restriction in §7.1 and measuring what that reaches.

---

## 1. The statement  `[PROVED]`

> **Lemma.** Let `E` be the speed set and `d ≤ n` a positive integer with `d ∤ e` for every
> `e ∈ E`. Then for any `a` with `gcd(a,d) = 1`, `t = a/d` is a witness: `‖e t‖ ≥ 1/n` for
> every `e ∈ E`.
>
> **Proof.** `e a / d` has denominator `d` in lowest terms, since `d ∤ e` and `gcd(a,d)=1`.
> So `‖e a / d‖` is a nonzero multiple of `1/d`, hence `≥ 1/d ≥ 1/n`. ∎

Counting the `a` gives the witness total

    N*(V, n)  =  Σ_{d ≤ n,  d ∤ v for all v ∈ V}  φ(d),

which is §7.1's `N(V,n)` **with `d | n` weakened to `d ≤ n`**. The divisibility hypothesis is
what the proof uses; `d | n` is never needed.

## 2. The correction that a control caught  `[recorded]`

I first read §4's gap-sum argument ("`n` gaps summing to 1 each `≥ 1/n` force the exact
`n`-grid") as giving *complete mod `m ≤ 8` ⟹ witness*. Control B tested it: **3977 failures
in 4000**. Completeness is irrelevant — the operative condition is non-divisibility, which
is what §7.1 already says. §4's gap-sum is a statement about *global* isolation of `n`
runners; LRC asks only that the stationary runner be far from the rest, so the grid is not
forced. Recorded because the wrong reading was mine and the control is what stopped it.

## 3. What it reaches  `[VERIFIED — exhaustive over [1..18]]`

At `n = 8` the `d | n` form admits `d ∈ {2,4,8}`; the `d ≤ n` form adds `d ∈ {3,5,6,7}` with
`φ = 2,4,2,6`. Every one of those extra `d` can hold when a speed *is* a multiple of 8 — so
unlike `N`, the strengthened count reaches into Case 2.

Exhaustive over the 31 788 primitive 7-tuples in `[1..18]`; 20 349 are Case 2 (some speed a
multiple of 8):

| | Case-2 tuples closed | share |
|---|---|---|
| `N(V,8) > 0` (the `d\|n` form) | **0** | 0.00% |
| `N*(V,8) > 0` (the `d ≤ n` form) | **14 099** | **69.29%** |
| remaining | 6 250 | 30.71% |

**Controls.** `N(V,8) > 0 ⟺ no speed is a multiple of 8` — 0 disagreements in 4000 random
tuples, confirming the `d | n` form is exactly Case 1. `N*(E,8) > 0 ⟹ an actual witness at
that `d` — **0 failures in 5869 (tuple, `d`) pairs**, witnesses verified by exact evaluation
of `‖e a/d‖`, not by the lemma.

**Novelty check.** `grep` over `docs/n8/` and `reports/` finds no witness at any denominator
below 8; Case 1 is recorded in four places uniformly as "`t = 1/8`, one line"
(`EXACT_CRITERION_v2.md:63`, `STATUS_n8_ANALYTIC_v1.md:45`, `U_REFORMULATION_v1.md:24`,
`U_REFORMULATION_v2.md:32`). The `d < 8` cases were not in the project.

## 4. The residual, characterised exactly  `[PROVED — 0 disagreements over all 20 349]`

> A Case-2 tuple is **not** closed by the lemma **iff its speed set hits every `d ∈ {2,…,8}`**
> — i.e. contains a multiple of each.

Checked against `N*(E,8) = 0` over all 20 349 Case-2 tuples: 0 disagreements. This is a
strong constraint on seven speeds — it forces multiples of 5, 7 and 8 plus the 2-3 structure
— which is why the residual is only 30.71%.

`E* = (2,6,7,8,10,13,14)` is in the residual, as it must be: `2→2`, `6→3,6`, `8→4,8`,
`10→5`, `7,14→7`. All three tight instances are Case 1 and are closed by `d = 8`.

## 5. What this does not do

It does not prove `n = 8`. The residual 30.71% contains the extremum and is exactly the
region where no `d ≤ 8` is free, so every witness there has denominator `> 8` and the
condition is no longer divisibility but the finer band condition
`e a mod m ∈ [m/8, 7m/8]`. Measured for `E*`: **first witness at `m = 15`, `a ∈ {4,11}`**
(smallest `m`; search to 400).

It also does not make `u(E) < 1` easier — the lemma certifies specific tuples, it does not
bound the covering measure.

## 6. A null on a hypothesis of mine, not of the source  `[PROVED — counterexample]`

I asked whether "a witness exists at level `m`" is a function of the completeness profile
`m ↦ k(E,m)` alone — an extrapolation from §1, not something §1 claims. **False.** Over 4368
5-subsets of `[1..16]` with profiles taken to `M = 24`: 2063 distinct profiles, 1951 of them
carrying two or more distinct witness sets. Witness pair:

`E = (2,3,4,5,6)` has `W > 0` at `m ∈ {7,8,9,10,11,12,13,14}`; `E' = (1,2,3,4,6)` has
`W > 0` at `m ∈ {5,7,8,12,13,14,15,16}`; identical profiles, first difference at `m = 5`.

§1's actual claim — that `k` at `t = a/m` is a function of `m` alone — is untouched and was
used throughout.

## 7. Ledger

`[PROVED]` §1 the lemma and the count `N*`; §4 the characterisation of the residual
(0 disagreements over the complete Case-2 enumeration).
`[VERIFIED — exhaustive in box]` §3, 69.29% of Case 2 over `[1..18]`, with both controls
(4000 tuples for the `d|n` equivalence, 5869 pairs for witness realisation, 0 failures).
`[RECORDED — my error, control-caught]` §2.
`[PROVED — counterexample]` §6, the profile hypothesis, which was mine and not the source's.
`[SCOPE]` the coverage percentage is box-dependent (`[1..18]`); the lemma and the residual
characterisation are not — both are unconditional in the speeds.

`n = 8` is **not proved.** The frontier is now the 30.71% whose speed sets hit every `d ≤ 8`.
