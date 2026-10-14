# The scale self-similarity lemma — what it is, and what it is not

> ## ⛔ IT DOES NOT CLOSE THE MIDDLE
>
> **The outstanding statement is unchanged:** close the middle of the trichotomy,
> `1 ≤ M ≤ c−2`. This document does not close it and does not reduce it.
>
> v2 of this note claimed the middle reduces to *"some lift of a sub-solution clears `B`"*, graded
> that `[OPEN]`, and called it "the whole of what is owed". **That statement is `[REFUTED]`**, by
> a minimal witness:
>
> ```
>   D = {1, 8, 14, 15, 17, 23, 27}      A = {8},  B = {1, 14, 15, 17, 23, 27}
>   only resonant flank e = 8, f = 1;  only sub-solution a = 1 mod 8
>   all eight lifts 1, 9, 17, 25, 33, 41, 49, 57  FAIL to clear B
>   yet D is lonely, at flanks 14, 15, 17, 23 and 27
> ```
>
> A reduction to a false statement is not a reduction. **v2 moved the target**, and the
> replacement obligation was wrong as well as different.
>
> **And the descent is not an induction — it is another sufficient rule.** "It closes 868 of 900"
> is a coverage figure, the same shape as `SHADOW_COUNT_v2.md`'s bounds and v1's H1. Third costume,
> same trap. Any resumption that measures how often the descent fires is repeating it.

*Version 3, 2026-09-22. Supersedes v2 (which claimed a reduction) and v1 (which recorded a refuted
guess, H1). Artefacts `experiments/nN/descent_v7.py`, `descent_v8.py`. **What survives is §1 and
nothing else.***

---

## 1. The lemma

> **Lemma (exact scale self-similarity).** Let `e = n·f` be a flank divisible by `n`, and let
> `d = n·m'` be a disparity divisible by `n`. Then for every opening numerator `a`,
>
> ```
>     d is clear at the flank e with numerator a    ⟺    m' is clear at the flank f with numerator a.
> ```
>
> The numerator is the **same**; nothing is rescaled.

*Proof.* `d·a = n·m'·a` and `n·e = n²f`, so `d·a mod n·e = n·(m'·a mod n f)`. The band at flank `e`
is `[e, (n−1)e] = [n f, (n−1)n f]`, and `n·(m'·a mod n f)` lies in it exactly when
`m'·a mod n f ∈ [f, (n−1)f]`, which is the band at flank `f`. ∎

`[PROVED — elementary]`, and checked at orders `n = 3,4,5,6,7,8,9,11,12`, 17,000 triples each,
**0 mismatches**.

**This is stronger than §12.** §12 says a resonant disparity's condition "is a band condition at
modulus `e`", which is true and vague. The lemma says the resonant disparities at a resonant flank
pose the **identical problem one scale down, with the same `a`** — which is what an induction needs
and what the looser statement does not supply.

---

## 2. What the lemma does and does not give

**Gives.** A correct, elementary, general-`n` identity that sharpens §12 of the manuscript. §12 says
a resonant disparity's condition "is a band condition at modulus `e`" — true and vague. The lemma
says the resonant disparities at a resonant flank pose the **identical problem one scale down with
the same numerator**. It is a component available to any future argument, and it is the only durable
output of this line of work.

**Does not give.** Any route. Steps built on it — descend through `A`, lift, check `B` — fail on
sets that are lonely through `B`, per the witness above. The lemma constrains the resonant part and
says nothing about the non-resonant part, which is precisely the obstruction §12 already named.

## 3. The record of this line

| attempt | status |
|---|---|
| **H1** — *`A/n` not ratio-easy ⟹ some flank in `B` clear* | `[REFUTED]` — 5 violations in 24,000 |
| **Step 3** — *some lift of a sub-solution clears `B`* | `[REFUTED]` — witness above |
| **The Lemma** | `[PROVED]` — elementary, general `n`, 0 mismatches at orders 3–12 |

Nothing here reaches the manuscript except the Lemma, and it reaches it as a sharpening of §12, not
as progress on Existence.
