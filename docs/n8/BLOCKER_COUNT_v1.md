# Who can block a candidate — one claim proved, one refuted

Assessment of a proposed three-part structural analysis of the Branch B candidate set. Part A is
proved and formalised; part C was already proved (the gap rule); **part B is false**, and the reason
is a domain mismatch worth recording.

Artefacts: `experiments/n8/BlockerCount_v1.lean` (3 theorems, axiom-clean),
`blocker_density_v1.py`, `pigeonhole_split_v1.py`.

---

## A — proved, and now a theorem

At a candidate `A/sₖ` with `A ≡ 1 (mod 8)`, reading `sᵢ` is *in the way* when `(sᵢ·A) mod 8sₖ` lies
within `sₖ` of `0`.

**`BlockerCount.self_residue`** `(sₖ·A) mod 8sₖ = sₖ` exactly — on the boundary.
**`BlockerCount.self_never_blocks`** hence a reading never blocks its own candidates.
**`BlockerCount.unit_never_blocks`** and the unit reading `1` never blocks any candidate, since
`A mod 8sₖ = A ∈ [sₖ, 7sₖ]`.

Both checked to `sₖ < 400`, 0 cases. **So the blocker count at any candidate is at most `n − 3`**
— five of the seven readings at order 8, not six.

## B — refuted

The proposal was that `slot_gcd`/`even_offset_caged` excludes **even** readings from blocking at
spine candidates, cutting blockers to the odd readings only. It does not.

Over 3,000 profiles, even readings perform **49.7%** of all blocking — essentially half. Cleanest
counterexample: `sᵢ = 4` blocks `u = 9/5`, because `4 · 9/5 = 7.2` and `dist(7.2, 8ℤ) = 0.8 < 1`.

**Why, precisely — and it is not a defect in the cage.** `even_offset_caged` is a statement about
**grid instants**. A candidate `(8m+1)/sₖ` is a grid instant only when `sₖ ∣ (8m+1)`, which is
generally false. The step `sᵢ(8m+1) ≡ sᵢ (mod 8)` is true, but the blocking condition lives
**mod `8sₖ`**, and reducing mod `8` discards exactly the information that decides it. The cage's
hypothesis is not met at these points. Transfer fails for a stateable reason: wrong modulus, wrong
domain.

## What A buys, measured honestly

Removing the two non-blockers moves the mean blockers per candidate from `7/4 = 1.75` to a measured
**1.1867** (per-reading blocking density `0.2370`, against the heuristic `0.25`). Counting needs
below `1`, so it still does not close — but the deficit narrows from `0.75` to `0.19`.

That makes the first moment a genuine **sufficient condition**: if a profile's total blocking pairs
is less than its total candidates, some candidate has zero blockers, and that candidate is a witness.
Exhaustive Branch B, readings `[2,30]`, 244,790 profiles:

| | count | share |
|---|---|---|
| settled by pigeonhole alone | 4,491 | **1.83%** |
| not settled, witness exists anyway | 240,299 | 98.17% |
| not settled, no witness | **0** | — |

**1.83% is small and is stated as small.** The pooled mean of `1.19` conceals that most individual
profiles sit above `1`. The criterion is sound and provable; it is not a route to the branch.

Also measured: **24.81%** of all candidates have zero blockers. Witnesses are abundant generically;
the difficulty is entirely in the profiles where they are scarce.

## Owed

These 3 theorems are not in `MANUSCRIPT_v12`, which was promoted before they existed. A **v13 is
owed** carrying them plus the refutation of B as a closed route. Not done here to avoid churning a
version for three declarations; recorded so it is not lost.
