# Witness normalisation, and two refutations

Continues `SEARCH_AS_RULE_v2.md`. **17 theorems, axiom-clean, zero `sorry`.**
Artefacts: `experiments/n8/ReachRule_v1.lean` (11), `GapRule_v1.lean` (3), `ArithForm_v1.lean` (2),
plus `branchB_witness_v1/v2.py`, `branchB_rule_v1.py`, `branchB_threshold_v1.py`,
`witness_normal_v1.py`.

---

## 1. The theorem

`ReachRule.witness_normalised` — **`[PROVED]`**, Lean, axiom-clean. Stated for an abstract family of
intervals: if covering fails, a witness exists whose form is known in advance — the start, or the
right endpoint `(n·m+1)/s` of an interval, with `s` from a given finite set.

Read on the Lonely Runner bad sets, where reading `s` at level `m` owns
`((n·m−1)/s, (n·m+1)/s)`:

> **If a lonely point exists, one exists of the form `t = A/(n·s)` with `s` a speed, `A ≡ 1 (mod n)`,
> and `s ≤ A ≤ (n−1)s`.**

The lonely point never needs to be an arbitrary real, or even an arbitrary rational: **its
denominator is `n` times one of the speeds and its numerator is `≡ 1 (mod n)`.** This sharpens the
statement of the conjecture, and it holds at every order.

**Grades, kept apart.** The Lean theorem is the abstract interval statement — `[PROVED]`. Its
instantiation to the LRC bad sets is mechanical (the endpoint form is how the intervals are defined)
but is **not** formalised; it is `[VERIFIED-INSTANCE]`: checked against the exact interval sweep at
orders `n = 4..9`, exhaustive over `(n−1)`-subsets of `[1,16]` and 3,000 random profiles from
`[1,400]` per order — **0 mismatches in every arm, 39,066 exhaustive + 18,000 random profiles.**
Orders `n ≤ 7`, where LRC is proved, test the *reduction* rather than the conjecture; those arms are
clean too.

## 2. Two refutations

Both conjectures were mine, both were natural, both are dead. Recorded because the reasons are
reusable.

**Refuted — "choose `s = s*`, the reading divisible by 8."** 18,809 counterexamples out of 244,790
exhaustive Branch B profiles (readings from `[2,30]`), smallest `S = (1,2,3,4,5,7,8)`.

The motivation was that `s*`'s own constraint self-neutralises: `s*·A/(8s*) = A/8` and `‖A/8‖ = 1/8`
exactly. True — but `(s·A) mod 8s = s` for **every** reading `s` when `A ≡ 1 (mod 8)`, so that
argument never singled out `s*` at all. The matched control confirms it: readings **not** divisible
by 8 fail at 10.90%, the same order of magnitude.

**Refuted — "choose `s` = the largest reading."** 794 counterexamples in the same arm (0.324%), and
failures persist at `s_max = 41, 48, 56, 80` under 300k-per-value sampling. No clean threshold
emerged, so it was not pursued. `min|W(S, s_max)|` does climb about linearly — 2, 4, 5, 12, 40, 204
at `s_max = 64, 100, 128, 200, 512, 2048` — so the failures concentrate at small `s_max`, but
sampling cannot bound where they stop and no claim is made that they do.

## 3. What stands

Allowing **any** reading to supply the witness: **0 failures in all 244,790 Branch B profiles.**
Two regularities, both measured and both unexplained:

- **At least two readings always supply a witness** — never one, never zero. Distribution over the
  six eligible readings: `{2: 61, 3: 1,879, 4: 21,557, 5: 97,893, 6: 123,400}`. The reading `s = 1`
  never works in Branch B, which is forced: it would give `t = 1/8`, and `8 | s*` kills it.
- The supplying reading is **never the smallest**; its rank in the sorted profile runs 1–5.

Scope: readings from `[2,30]`, `n = 8`, integer readings. Not a bound, not a proof.

## 4. Where this leaves Existence

**Has done.** Existence at order 8 for integer readings is now a statement about **two integers**:
for every profile `S`, does there exist `s ∈ S` and `A ≡ 1 (mod 8)` with `s ≤ A ≤ 7s` such that
`s'A mod 8s ∈ [s, 7s]` for every `s' ∈ S`. No reals, no intervals, no measure. Branch A (no reading
divisible by 8) is proved; Branch B is exactly this statement.

**Has not.** The generic counting attack on Branch B does not close, and the reason is exact and
worth recording rather than rediscovering: each reading kills about `1/4` of the candidate `A`, and
seven readings give `7/4 > 1`. The union bound fails by the same margin as the classical measure
obstruction — total bad measure `7 × 3/2 = 10.5` against an interval of length `6`. **Any argument
that ignores overlap between readings will fail here, at any order, by construction.** That is worth
knowing in advance.

**So the next attack has to be about overlap.** One concrete line that is not generic counting:
Hunter–Kounias gives `|⋃Aᵢ| ≤ Σ|Aᵢ| − max_{spanning tree} Σ|Aᵢ ∩ Aⱼ|`, a valid upper bound on the
covered measure. Forcing a gap needs that tree sum above `4.5` over six edges — average pairwise
overlap above `0.75` against a generic value near `0.375`. Untried, and it would need pairs with
structurally large overlap rather than generic ones. Recorded as the live lead, not as a plan known
to work.
