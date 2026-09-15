# What the failures of "a sharer's own flank is free" say

2026-09-15. Follows `FLANK_NEAR_EXTREMES_v2.md` §3, where the hypothesis *"a runner that is an exact slot-sharer of some flank has its
own flank free"* failed 24,656 times at order 8. The owner asked what the failures say it should be. Scripts in `experiments/n8/`
(outputs `.out`), exact integer arithmetic over every 8-subset of `[1, 20]` and every runner: `sharer_failures_v1.py`,
`sharer_even_slot_v1.py`, `sharer_exceptions_v1.py`.

## 1. The owner's AP picture at a flank

The AP is scale-free: at its gap, whatever the gap, its isolation is absolute (φ law, §5 of v8.2). In the flank coordinates the gap
is set by a runner and the subject together:
- at every opening of the flank `e`, the pair (subject, `e`) sits exactly one eighth apart, the AP spacing at their gap;
- by Theorem 6.2(d), at the first isolation instant some runner is the subject's track neighbour at exactly one eighth, and
  that runner is a flank;
- every other runner is read by its ratio `d_j/d_e`, i.e. where the relocation has put it in that pair's AP;
- the ordering of speeds is bookkeeping for finding those ratios.

`lonely_iff_exists_flank` (Lean) is this statement: isolation happens at an opening of some pair's own AP.

## 2. The rule the failures give  `[VERIFIED — exhaustive in range, 382,738 sharer pairs]`

Take a sharer pair: runner `s` with `d_s = 8m·d_e`. Read every other runner at the sharer's own flank by its ratio `d_j/d_s`.

| sharer flank | an even-slot runner (ratio denominator 2 or 4) | none |
|---|---|---|
| `m = 1`, shadowed | 23,630 | **8** |
| `m = 1`, free | 247,582 | 27,624 |
| `m = 2`, shadowed | 1,176 | **6** |
| `m = 2`, free | 50,798 | 23,732 |

**The 14 exceptions** (`sharer_exceptions_v1.out`) all have `s = 16`. Each is shadowed only by **five or six runners**, every one
with ratio denominator 8 or 16 to the sharer. Combined:

> **A sharer's own flank is shadowed only if some runner sits at a symmetric point of the sharer's AP (ratio denominator 2: the
> antipode; 4: the quarter points), or five or more runners sit at its fine slots (denominators 8, 16).**

No sharer pair in the range breaks it. It is a necessary condition only: most sharer flanks with an even-slot runner are still
free (247,582 against 23,630 at `m = 1`).

## 3. Why the symmetric points matter  `[DERIVED — flank lemma]`

At the sharer's `k`-th opening a runner with ratio `ρ = p/c` (reduced) sits at `ρ·(k + 1/8)` laps. By the flank lemma it is in the way on
a set of residues `k mod c`:
- **`c = 2`, the antipode:** its position repeats every second opening. It is in the way at half the openings (`p` odd: one of
  the two residues).
- **`c = 4`, a quarter point:** it repeats every fourth opening and is in the way at a quarter of them, in a pattern that
  complements the antipode's.
- **`c = 8` or `16`, a fine slot:** it moves through every position, one quarter of the residues at most, and its blocked
  residues overlap those of other fine-slot runners.

So a symmetric-point runner takes a large, well-placed share of the sharer's openings. Without one, holding every opening in the
way takes nearly all the runners, which is what the 14 exceptions show.

## 4. What it gives, and what is still to do

- **For T4:** the first free-flank rule found by reading failures rather than discarding them. A sharer's own flank can be
  shadowed only through runners at the sharer AP's symmetric points, or through a near-complete set of fine-slot runners. At
  order 8 there are six other runners, so the second route is very narrow.
- **To prove, not only verify:** the residue shares of §3 give the necessary condition by the exact count of `T4_FLANKS_v3` §3(b),
  within the owner's pending ruling on counting. The "five or more" in the exception clause needs the exact overlap structure of
  fine-slot residues; that is the next computation.
- **To test beyond the range:** `[1, 20]` makes `m ≤ 2`, and puts all ratios over denominators dividing 16.
