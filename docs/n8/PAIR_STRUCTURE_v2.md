# Two inverted PATTERNS — corrected, and the owed proof discharged

Supersedes `PAIR_STRUCTURE_v1.md`. Two changes: a correction to how the structure was described, and
the counting statement that v1 listed as owed is now proved.

## Correction: patterns, not pairs

v1 described the AP's four isolation events as "two inverted **pairs**" — `{1,7}` and `{3,5}` as
pairs of points. **That is the wrong object.** They are two inverted **patterns**:

* the **`+1` pattern** — every `x` with `s·x ≡ 1 (mod 8)` for some reading `s` (right endpoints);
* the **`−1` pattern** — every `x` with `s·x ≡ −1 (mod 8)` (left endpoints),

each an inverted image of the other under time reversal `x ↦ 8 − x`.

**The four events are the four points where the two patterns coincide.** Nothing pairs up: each of
the four points sits on **both** patterns at once, and the two patterns attribute it to **reflected
readings**:

```
    x = 1    +1 endpoint of reading 1      −1 endpoint of reading 7
    x = 3    +1 endpoint of reading 3      −1 endpoint of reading 5
    x = 5    +1 endpoint of reading 5      −1 endpoint of reading 3
    x = 7    +1 endpoint of reading 7      −1 endpoint of reading 1
```

**`TwoPatterns.unit_on_both`** (Lean, axiom-clean): for odd `u`, `u·u ≡ 1 (mod 8)` and
`u·(8−u) ≡ 7 (mod 8)`. So the coincidence is forced by the Klein identity `u² ≡ 1` — the same
`klein_self_inverse` that runs through the guard structure. **`TwoPatterns.reflected_reading`**
states the second congruence as the time reversal of the first.

**There are four events because there are four units mod 8** — one coincidence per unit. Checked:
within `[1,7]`, over every rational of denominator `≤ 12`, the two patterns coincide at exactly those
four points and nowhere else.

This also explains why the pair structure is invisible at the AP. The unit action merges the four
into one orbit (`spine_all_or_nothing`); the pattern structure is what survives further down.

## The owed proof, discharged

v1 recorded `blocked(α') = blocked(8−α')` as `[VERIFIED — exact]` and owed a `Finset.card` argument.

**`TwoPatterns.blocked_reflect`** (Lean, axiom-clean): with
`blockedSet(α', b) = {v ∈ [0,8b) : v ≡ α' (mod 8), min(v, 8b−v) < b}`,

> `|blockedSet(α', b)| = |blockedSet(8−α', b)|` for `1 ≤ α' ≤ 7`, `b > 0`.

Proved by an **involution**, not a computation: `v ↦ 8b − v` permutes `[0,8b)`, carries the class
`α'` to the class `8−α'`, and leaves `min(v, 8b−v)` unchanged — so it preserves blocking. The only
care needed is `v = 0`, which is excluded because `α' ≥ 1`.

Cross-checked against direct enumeration for `b < 400`, all four classes: 0 exceptions.

**This is `{1,7}` agreeing internally and `{3,5}` agreeing internally — now a theorem.**

## Unchanged from v1, and still verified only

The *split* law — that `{1,7}` and `{3,5}` differ by exactly one lattice point per class when
`β ≡ 2,3,6,7 (mod 8)`, with the favoured pair flipping under `β ↦ β+4` — remains
`[VERIFIED — exact]`: the count formula matches direct enumeration for `β < 300`, and the law holds
with 0 exceptions for `9 ≤ β ≤ 600`. That half is a statement about floors of `(β − α')/8` and is
**not** proved.

So of the two halves of v1's measured law, the **symmetric** half is now proved by an involution, and
the **antisymmetric** half — the split itself — is still owed.
