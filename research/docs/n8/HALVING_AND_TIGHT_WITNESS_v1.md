# A halving theorem for n=8, and the tight-instance question reduced to one rational

2026-09-07. Continues `TIGHT_INSTANCES_v1.md` and `RESIDUAL_GAP_v1.md`. Artifacts:
`experiments/n8/{halving_theorem_v1, halving_coverage_v1, witness_structure_v1,
tight_no_multiple_of_n_v1, tight_with_coarse_v1, coarse_gap_v1}.py`.

Two things are established here. §2 is a theorem that proves LRC(8) outright on a
class of speed sets, using only LRC(4)–LRC(7) — never LRC(8). §3 converts the
question "does a tight instance contain a multiple of 8" into a statement about a
single rational number, and proves the two equivalent.

## 1. The frame this sits in  `[PROVED]`

For `q ∈ {2,…,8}` and `gcd(a,q)=1`, `‖v·a/q‖ = |va mod q|/q ≥ 1/q` when `q ∤ v`.
Hence:

- some `q ≤ 7` divides no speed → `t = 1/q` gives `M(T) ≥ 1/q > 1/8`. **Settled.**
- `8` divides no speed → `t = 1/8` gives `M(T) ≥ 1/8`. **Settled**, tightly.

So **LRC(8) is equivalent to: every 7-set holding a multiple of 5, of 6, of 7 and of
8 has `M(T) ≥ 1/8`.** Everything below attacks that residual class. Nothing below
assumes LRC(8).

## 2. Theorem P (halving)  `[PROVED — from LRC(4)…LRC(7) only]`

> **Theorem P.** Let `T` be 7 distinct positive integers. Choose `m ≥ 2`, put
> `D = {v ∈ T : m | v}`, `X = T \ D`, `x = |X|`, and `g = gcd(D)`. Suppose `D ≠ ∅`
> and `1 ≤ x ≤ 6`. Write `h_u = gcd(u,g)` and `g_u = g/h_u`. If
>
>     Σ_{u ∈ X}  h_u · ( ⌊ g_u / 4 ⌋ + 1 )  <  g,
>
> then `M(T) > 1/8`.

*Proof.* Suppose `M(T) ≤ 1/8`, i.e. the closed bad sets `Ū_v = {t : ‖vt‖ ≤ 1/8}`
cover the circle. `Ū_D` is invariant under `t ↦ t + 1/g`, because `g | v` for every
`v ∈ D`. So for each `j`, `S¹ = Ū_D ∪ (Ū_X + j/g)`, and intersecting over
`j = 0,…,g−1`,

    S¹ = Ū_D ∪ ⋂_j (Ū_X + j/g).

Fix `t` and `u ∈ X`. As `j` runs over `ℤ/g`, `ju/g mod 1` takes each of the `g_u`
values `k/g_u` exactly `h_u` times. A closed arc of length `1/4` holds at most
`⌊g_u/4⌋ + 1` points of a `1/g_u`-spaced grid, so `u` accounts for at most
`h_u(⌊g_u/4⌋+1)` of the `g` shifts. By hypothesis the whole of `X` accounts for
fewer than `g`, so some shift `j` is missed and `t ∉ ⋂_j(Ū_X + j/g)`. That holds for
every `t`, so the intersection is empty and `Ū_D = S¹`.

Write `D = g·D'`. Substituting `t = s/g` turns `Ū_D = S¹` into `M(D') ≤ 1/8`. But
`D'` is a set of `7−x` distinct positive integers, so LRC(`8−x`) gives
`M(D') ≥ 1/(8−x) > 1/8`. Contradiction. ∎

`8−x ∈ {2,…,7}`, and LRC(3)–LRC(7) are exactly the cases this project has formally
verified in Lean, axiom-clean. **The theorem borrows nothing it does not own.**

**Special case worth naming.** `m = 2` with exactly one odd speed: `g` is even,
`h_u = 1`, `⌊g/4⌋+1 < g` for every `g ≥ 2`. So *a 7-set with exactly one odd speed
satisfies `M(T) > 1/8`* — the six even speeds, halved, would otherwise contradict
LRC(7).

### Verification  `[artifact: halving_theorem_v1.py]`

- **Forward.** Every `T` with speeds `≤ 22`, `gcd = 1`, meeting the hypothesis:
  **8 605 sets, 0 violations** of `M(T) ≥ 1/(8−x)` — checked in exact rational
  arithmetic.
- **Control, and it fires.** The three known tight instances (`M = 1/8`) must *fail*
  the hypothesis for every `m ≤ 256`, or the theorem would be false. All three fail
  it. This is the check that would have exposed a wrong lemma, and it was run.

### How much it settles  `[EMPIRICAL — exhaustive over the stated bounds]`

| speed bound | residual sets | settled by Theorem P |
|---|---|---|
| 20 | 12 673 | 919 (7.25%) |
| 24 | 76 902 | 6 581 (8.56%) |
| 28 | 239 556 | 22 708 (9.48%) |
| 32 | 710 038 | 71 826 (10.12%) |

**About a tenth, rising slowly.** A tenth is a tenth: Theorem P is a genuine piece
of an analytic LRC(8), and it is not close to the whole of one.

## 3. The tight-instance question, reduced  `[PROVED]`

Let `T` be tight at `n` (`M(T) = 1/n`, `|T| = n−1`, `gcd = 1`) and `t*` a witness.

**(i) An extremal pair exists.** There are `a, b ∈ T` with `frac(a t*) = 1/n` and
`frac(b t*) = (n−1)/n`. *Else every active constraint at `t*` has the same sign of
slope and `g(t) = min_v ‖vt‖` exceeds `1/n` immediately to one side, contradicting
`M(T) = 1/n`.*

**(ii) The denominator divides `a+b`.** `a t* ≡ 1/n` and `b t* ≡ −1/n (mod 1)` give
`(a+b)t* ∈ ℤ`. Writing `t* = p/q` in lowest terms, `q | a+b`; in particular
`q ≤ 2·max(T)`.

**(iii) `n | q`, and `r := q/n` divides both `a` and `b`.** From `ap/q − 1/n ∈ ℤ`:
`q | nap`, and `gcd(p,q) = 1` gives `q | na`; reducing mod `n` gives `n | q`. Then
`nr | na` gives `r | a`, and with `a = r a₁`: `a₁ p ≡ 1 (mod n)`. Likewise `r | b`
and `b₁ p ≡ −1 (mod n)`.

**(iv) A multiple of `n` forces `r ≥ 2`.** Suppose `n | d`, `d = n d₁`. Then
`d p mod nr = n·(d₁ p mod r)`, so `‖d t*‖ = (1/r)·min(s, r−s)` with `s = d₁p mod r`.
If `r = 1` then `s = 0` and `‖d t*‖ = 0 < 1/n` — `t*` is not a witness. So `r ≥ 2`,
`q ≥ 2n`, and `r ∤ d₁`.

> **Corollary (the reduction).** *"No tight instance contains a multiple of `n`"* is
> **equivalent** to *"every tight instance has witness denominator exactly `n`"*.
> (⇐ is (iv); ⇒ is the observation that if `n ∤ v` for all `v` then every `k/n` with
> `gcd(k,n)=1` is a witness, and a witness with `r ≥ 2` would have to coexist with
> those.)

All four statements are asserted mechanically on every tight instance enumerated at
`n = 3,…,8` — ten instances, every witness of every one — and pass
(`witness_structure_v1.py`). In all ten, `r = 1`: the witness set is exactly
`{k/n : gcd(k,n) = 1}`.

## 4. Evidence for `r = 1`  `[EMPIRICAL — exhaustive, scope stated]`

- **Across `n`.** Tight instances enumerated exhaustively at `n = 3,4,5,6,7,8`
  (speed bounds 30, 30, 30, 28, 26, 22): ten instances, **none** containing a
  multiple of `n`, **all** with witness denominator `n`.
- **At `n = 8`, directly.** All 7-sets with speeds `≤ 44` holding multiples of 5, 6,
  7 and 8, `gcd = 1`: **8 165 718 sets, zero tight**. Two stages, so no decision
  rests on floating point — a float sweep keeping every set whose largest uncovered
  gap is `< 10⁻⁹` (a tight set has gap exactly 0; float error is `~10⁻¹⁵`, so the
  filter cannot discard one), then exact rational re-decision of the survivors.
  **Stage 1 returned zero survivors**, so the residual case at `V ≤ 44` is not
  merely non-tight — every set in it has a good gap of measurable size.
- **Quantified.** Exhaustively over speeds `≤ 32` (710 038 residual sets),
  `min M = 2/15`, attained at `{1,3,4,5,7,11,24}`, `{1,4,5,6,7,11,16}` and
  `{2,6,7,8,10,13,14}`. Against `1/8`, a gap of `1/120`.

**One-sided.** These are searches for a tight residual set. They can only
over-report; a tight instance with speeds above 44 would not have been seen.

## 5. What is owed

1. **Prove `r = 1`.** That is now the whole of the sub-goal, stated as an arithmetic
   fact about one rational. What is in hand towards it: `q | a+b`, `n | q`, `r | a`,
   `r | b`, `a₁p ≡ 1` and `b₁p ≡ −1 (mod n)`, and — if a multiple of `n` is present —
   `r ∤ d₁` and `q ≥ 2n`. What is missing: a reason the band condition
   `|vp mod± nr| ≥ r` cannot hold for all seven speeds when `r ≥ 2`.
2. **Push Theorem P past 10%.** Its loss is the worst-case grid count
   `⌊g_u/4⌋+1`; the `x` shift-sets are dilated intervals in `ℤ/g`, and four such can
   tile `ℤ/g` exactly, so `x ≤ 3` is close to the limit of *this* counting. A
   different invariant is needed, not a sharper count.
3. Note that (1) and (2) are different targets: (2) advances LRC(8) itself; (1) is a
   structural fact about tight instances that presupposes LRC(8) and does not by
   itself prove it. Both were asked for; they should not be merged.
