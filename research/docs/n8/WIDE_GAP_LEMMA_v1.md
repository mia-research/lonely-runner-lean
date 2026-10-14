# The wide-gap lemma — two adjacent wide gaps name a Branch A runner

2026-09-13. n = 8, individual isolation, threshold 1/8. Speeds distinct reals, sorted
`v_1 < … < v_8`. **Speed gaps** `g_k = v_{k+1} − v_k` for `k = 1,…,7`; **spread**
`S = v_8 − v_1 = Σ_k g_k`. For runner `i`, `d_min(i)` is its nearest speed difference and
`d_max(i)` its farthest.

**Branch A** is the case `d_max(i) ≤ 7·d_min(i)`, already proved in `PROOF_CANDIDATE_v3`
Step 7 (35,467 / 35,467) — the runner's moment is named without search.

Call a speed gap **wide** when `g_k ≥ S/7`, that is, at or above the average of the seven.

*(Word collision, flagged: `OWNER_PROCEDURE_v1` §4 uses "spikes" for the features of
`TRANSIT_MAP_v1` §2, a different object. "Wide gap" is used here to avoid it.)*

---

## 1. The lemma  `[PROVED]`

> **Lemma.** If two **adjacent** speed gaps `g_k` and `g_{k+1}` are both wide, then the runner
> between them, `r_{k+1}`, satisfies Branch A.

*Proof.* Runner `r_{k+1}` is interior, and its two adjacent gaps are exactly `g_k` and `g_{k+1}`,
so by sortedness `d_min(k+1) = min(g_k, g_{k+1}) ≥ S/7`, hence `7·d_min(k+1) ≥ S`.

Every other runner lies in `[v_1, v_8]`, so `d_max(k+1) = max(v_{k+1} − v_1, v_8 − v_{k+1}) ≤ S`.

Therefore `d_max(k+1) ≤ S ≤ 7·d_min(k+1)`, which is Branch A. ∎

Three lines, no hypothesis beyond sortedness, and it holds for arbitrary distinct reals.

**It is a positive statement.** It does not say a configuration is difficult; it **names a runner
whose moment the construction already returns**, from the gap sequence alone, without computing
any reading.

## 2. The two end runners  `[PROVED]`

> **Lemma (ends).** If `g_1` is wide then `r_1` satisfies Branch A; if `g_7` is wide then `r_8`
> does.

*Proof.* `r_1` has a single adjacent gap, so `d_min(1) = g_1`, and `d_max(1) = v_8 − v_1 = S`
exactly. Wide means `g_1 ≥ S/7`, so `7·d_min(1) ≥ S = d_max(1)`. The argument for `r_8` is the
same with `g_7`. ∎

The end runners need only **one** wide gap, not two, because their farthest distance is the whole
spread and their nearest is a single gap.

## 3. What the gap sequence must look like when Branch A fails everywhere  `[PROVED]`

Contraposing §1 and §2 together:

> **Corollary.** If Branch A fails for every one of the eight runners, then
>
> 1. `g_1` and `g_7` are **not** wide;
> 2. no two adjacent gaps are both wide;
>
> so the wide gaps occupy pairwise non-adjacent positions inside `{2,3,4,5,6}` — and there are
> therefore **at most three** of them.

*Proof.* (1) is §2 contraposed, (2) is §1 contraposed. A pairwise non-adjacent subset of
`{2,…,6}` has at most three elements, the largest being `{2,4,6}`. ∎

At least one gap is always wide, since seven gaps averaging `S/7` cannot all be below it. So in
such a configuration the count of wide gaps is **1, 2 or 3**, never 0 and never more.

## 4. Verification  `[VERIFIED — exhaustive]`

Every 8-subset of `{0,…,16}` — 24,310 configurations, exact integer arithmetic:

| | |
|---|---|
| adjacent pairs of wide gaps found | 22,578 |
| cases where the runner between them is **not** in Branch A | **0** |
| configurations where Branch A fails for every runner | 586 |
| of those, any wide gap at position 1 or 7 | **0** |
| of those, any two wide gaps adjacent | **0** |
| of those, the count of wide gaps | 1 in 191, 2 in 325, 3 in 70 |
| of those, positions occupied | 2, 3, 4, 5, 6 only |

The corollary's bound of three is attained.

## 5. Status and scope

`[PROVED]` §1, §2, §3, for arbitrary distinct real speeds. Nothing is cited; the proofs use only
sortedness, `d_max(i) ≤ S`, and the definition of Branch A.

`[VERIFIED — exhaustive]` §4, all 24,310 8-subsets of `{0,…,16}`.

**What it does.** It converts a property of the seven speed gaps — two adjacent ones at or above
average — into a named Branch A runner, checkable before any reading is formed. And it constrains
the gap sequence of any configuration in which Branch A reaches nobody.

**What it does not do.** It says nothing about the runners it does not name. Branch A covers a
runner, not a configuration, and LRC(8) requires every runner's moment. Over random
8-sets, the share of **runners** in neither Branch A nor an unblocked integer reading is 56% at
span 50 and 70% at span 5000 — so naming one runner per configuration leaves the bulk of the
obligation untouched. This lemma names runners; it does not reduce that share.

**n = 8 is not proved here.**

---

Origin: the adjacency pattern was first seen in a sweep of configurations where Branch A reaches
no runner (548 of 548 had no two adjacent wide gaps). The proof above is direct from Branch A's
definition and does not depend on that sweep.
