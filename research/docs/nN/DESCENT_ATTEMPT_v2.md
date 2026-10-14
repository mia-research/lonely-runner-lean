# The scale recursion on the middle of the trichotomy — the exact lemma, and what it leaves

*Version 2, 2026-09-22. Supersedes `DESCENT_ATTEMPT_v1.md`, which recorded a refuted guess (H1)
arrived at by pattern-matching on five exceptions and by reaching for CRT because a modulus
factored. That was the wrong move: CRT is the reflex answer to a factoring modulus, not a reason.
This version is the algebra. Artefacts `experiments/nN/descent_v7.py`, `descent_v8.py`.*

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

## 2. The induction it licenses

Let `A = {d : n ∣ d}`, `B = {d : n ∤ d}`, and suppose `A ≠ ∅` (the middle, and the right-hand closed
end). Then `A/n` is a disparity set whose entries are `n` times smaller.

1. **Descend.** By induction on the entries, some flank `f ∈ A/n` has a clear opening `a` for `A/n`.
2. **Lift the flank.** Put `e = n·f ∈ A`. By the Lemma, **every** disparity of `A` is clear at flank
   `e` with that same `a`.
3. **What remains.** The conditions from `A` constrain `a` only modulo `n·f` (checked: the resonant
   condition is constant on `a mod n f`, 0 counterexamples in 4,560). So `a` has `n` lifts modulo
   `n·e = n²f`, and the obligation is that **some lift clears `B`**.

The recursion terminates because the entries shrink by a factor `n` at each step. Steps 1 and 2 are
proved. **Step 3 is the whole of what is owed.**

---

## 3. Status of step 3

`[OPEN]`. Not proved, and not always true of the descent as structured: a set can have no resonant
flank whose sub-solutions lift to clear `B`, while still being lonely through a flank in `B`.

Measured, 900 random middle sets per range, order 8: the descent through a resonant flank closes all
but 32, 24, 7, 6, 1 respectively at ranges 28, 45, 70, 110, 170; mean surviving lifts of the `n = 8`
about 1.7–2.0. `[EMPIRICAL — bound to this sampling and these ranges.]` **Counts, not shares, and
not progress.** The failures are not characterised, and characterising them is the next move if this
is resumed.

One observation worth recording because it is the reverse of the counting attack's behaviour: the
failure count **falls** with range here (32 → 1), where the covering bounds of `SHADOW_COUNT_v2.md`
**rose** with range. That is a difference in kind between the two directions, not a measure of
either's success.

**A trap to name.** Step 3 is a question about `n` lifts and at most `n − 2` members of `B`. Attacking
it by counting how many lifts `B` can block is covering again, at a smaller scale — the same move
that `SHADOW_COUNT_v2.md` records as a closed route. Step 3 wants a reason a lift survives, not a
bound on how many do not.

---

## 4. What v1 got wrong

v1's H1 — *if `A/n` is not ratio-easy, some flank in `B` is clear* — was induced from five
exceptions and refuted at 5 violations in 24,000. It was a guess about which flank to take, made
without the algebra above. The algebra says the flank to take is in `A`, not `B`, and says exactly
what taking it buys.
