# Halving, continued — a width invariant for Theorem P: proved, independent, and small

2026-09-07. Continues `HALVING_AND_TIGHT_WITNESS_v1.md`, whose §5.2 owed:

> *"Its loss is the worst-case grid count `⌊g_u/4⌋+1` … **A different invariant is needed,
> not a sharper count.**"*

This supplies a different invariant — **width** in place of count. It is proved, it is
genuinely independent of Theorem P, and it is **not the unlock**. Artifacts:
`experiments/n8/{halving_width_v1, halving_width_v2}.py`.

## 1. Theorem P″  `[PROVED — from LRC(3)…LRC(7) only]`

> Let `T` be 7 distinct positive integers, `D ⊆ T` non-empty, `g = gcd(D)`,
> `X = T \ D`, `1 ≤ |X| ≤ 6`. Let
>
>     λ(X) := the largest connected component of { t : ‖u t‖ ≥ 1/8 for all u ∈ X }.
>
> If `1/g < λ(X)` then `M(T) > 1/8`.

*Proof.* Theorem P's skeleton, with its final step replaced. `Ū_v = {t : ‖vt‖ ≤ 1/8}` is
invariant under `t ↦ t + 1/g` for every `v ∈ D`, so if `M(T) ≤ 1/8` then
`S¹ = Ū_D ∪ ⋂_j (Ū_X + j/g)`. If `1/g < λ(X)`, every coset `t + (1/g)ℤ` meets the widest
lonely component of `X`, so some shift `j` has `t − j/g ∉ Ū_X`; that holds for every `t`,
so the intersection is empty and `Ū_D = S¹`. Substituting `t = s/g` gives `M(D/g) ≤ 1/8`,
contradicting LRC(`8−x`) `≥ 1/(8−x) > 1/8`. ∎

Note `D` ranges over **all** non-empty proper subsets, not only `{v : m | v}` — the
invariance needs only `g | v` for `v ∈ D`. (This is not a generalisation in effect: for
any `D`, the larger set `{v ∈ T : g | v}` has the same `g` and a smaller `X`, so the
`m`-form already reaches the optimum. Recorded so it is not re-tried.)

## 2. What was tried first and is weaker — recorded so it is not repeated

`halving_width_v1.py` derived the width from LRC(`x+1`) plus a perturbation
(`TOP_GAP_v1.md` Lemma 2), giving `λ(X) ≥ (7−x)/(4(x+1)·max X)` and hence the clean
condition `g(7−x) > 4(x+1)max(X)`. **Measured: 79 of 12 673 residual sets at `B = 20`,
every one of them already settled by Theorem P. Net gain zero.** The constant is the
loss; §1 removes it by computing `λ` exactly with the Boundary Set Method.

## 3. Controls and forward check

- **Control.** The three tight instances (`M = 1/8`) must fail P″ or the theorem is false.
  All three fail it, at `B = 20` and `B = 24`.
- **Forward.** Every set where P″ fires must have `M(T) > 1/8`, decided in exact rational
  arithmetic: **0 violations** of 76 902 at `B = 24`.
- **Implementation check.** This file's independent reimplementation of Theorem P returns
  919/12 673 at `B = 20` and 6 581/76 902 at `B = 24` — matching `v1` §2's table exactly,
  so the comparison below is between like and like.

## 4. How much it adds  `[EMPIRICAL — exhaustive over the stated bounds]`

| bound `B` | residual sets | Theorem P | P″ | either | **P″ adds** |
|---|---|---|---|---|---|
| 20 | 12 673 | 919 (7.25%) | 118 (0.93%) | 958 (7.56%) | **39 (+0.31 pp)** |
| 24 | 76 902 | 6 581 (8.56%) | 826 (1.07%) | 7 120 (9.26%) | **539 (+0.70 pp)** |

P″ is weaker than P overall and still settles sets P misses — the two are independent, not
nested. The increment is **growing** (`+0.31 → +0.70 pp`) where P's own increments are
decelerating (`v1` §2: `+1.31, +0.92, +0.64`). Concretely, P ∪ P″ reaches 9.26% at `B = 24`
where P alone needs `B = 28` for 9.48%: **it buys about one step of `B`, not an order.**

## 5. Why it fires so rarely, quantitatively

`λ(X)` measured exactly over sampled `X ⊆ [1,20]`:

| `\|X\|` | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| median `λ` | 0.0500 | 0.0484 | 0.0441 | 0.0417 | 0.0349 |
| `g` needed | > 20 | > 21 | > 23 | > 24 | > 29 |

But `g = gcd(D) ≤ min(D) ≤ B`. At `B = 20` the requirement sits exactly at the top of the
available range, which is why P″ fires on under 1%. It fires only when the `D`-speeds share
a large factor **and** the `X`-speeds are small — a **large-ratio** regime. That is
precisely the regime Theorem P's counting cannot reach, and it is why P″ adds sets despite
being weaker overall.

## 6. Verdict on the owed item

`v1` §5.2 asked for a different invariant rather than a sharper count. Width **is** a
different invariant, it is proved from what we own, and it is complementary in the
large-ratio direction — but at `+0.31` to `+0.70` percentage points it does not change the
character of `v1`'s finding. **"About a tenth, rising slowly" still stands**: P ∪ P″ is
9.26% at `B = 24`. The owed item is answered in the negative for this candidate, and the
class of invariant that would change the picture remains unidentified.

## 7. Ledger

Decided cells: 2 of 135 (unchanged; nothing here touches the Rosenfeld sector count).
`n = 8` is not proved. Added: Theorem P″, proved, controlled, and measured. Owed and
carried forward unchanged from `v1` §5: prove `r = 1`; the `≤ 34` tight sweep; whether
`inf{M(T) : T ∈ R} > 1/8`.
