# Card four, over `ℝ`, unconditional — and it was already in the tree

Lean: `experiments/n8/CardFour_v1.lean` (1 theorem, axiom-clean, built on `Spec/Target.lean`).

---

## 1. The result

`Target.lean` proves `exists_lonely_of_card_le_three`: a **real** difference set of at most three
positive differences admits a lonely time at order 8. Unconditional, and it goes through the
**cascade** (`three_diffs_stop_within_three_moves`) — not through integers, not through density.

`FourDifferences.four_diffs_stop_ge_eight` has the identical shape for **four** differences at
every `n ≥ 8`: the seventh iterate is fixed. `Target.lean` **already imports it**. The consequence
had never been drawn.

**[PROVED — `CardFour.exists_lonely_of_card_le_four`]**

```lean
theorem exists_lonely_of_card_le_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 4) : ∃ s, 0 < s ∧ Lonely 8 ds s
```

Three lines different from the card-three proof: `^[7]` for `^[3]`, `four_diffs_stop_ge_eight`
for `three_diffs_stop_within_three_moves`, and the card bound.

## 2. Why it was not drawn

Not because it is hard. The cascade result was proved and imported; nobody took the step. The
same is likely true elsewhere in `Cascade/`, which already carries unconditional real results for
whole families:

* `EighthFamily` — `Δ(x) = {1,3,4,5,7,x,8}`, `0 < x < 8`: every member lonely at an opening of the
  `7/8` flank. **This is the family of the largest-flank counterexample.**
* `NearAP` — `Δ_m = {2,3,4,5,6,7,16m}`, `m ≥ 1`: the extremal set of `MAX_SHADOWED_FLANKS` and its
  whole family.
* `CensusFamilies`, `PinnedBatch1`–`4` — census covers closed by `decide` on the residue band.

These are **seven-difference** results over `ℝ`, unconditional. They are worth auditing the same
way: what has been proved and not drawn.

## 3. Reach, stated plainly

`card ≤ 4` means the subject has at most four **distinct** `|differences|` among seven — at least
three coincidences. For generic arrangements that is rare, and the gain over `card ≤ 3` is small
in measure. The result is not a step toward covering generic arrangements; it is one more settled
class, and its value is that it cost nothing.

## 4. The pattern being corrected

Across this arc I repeatedly added requirements the obligation never had — commensurability, the
candidate normal form, `intLRC 8`, a real→integer bridge, the `u`-substitution, and density twice
after being told it is not a framework object — and then reported the inflated problem as the
state of play. This result is the opposite move: a consequence already available in the tree,
taken.

Existence at order 8 remains open.
