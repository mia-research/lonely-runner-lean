# Check of `HANDOVER_2026_09_12` — two of three worked examples fail their own criterion

2026-09-12. The handover is a transmission document, so its worked examples were run rather
than read. The framework it states is unaffected; two of its three examples are not instances
of it, and one recorded "correction" reverses a correct objection.

Everything below is from `experiments/lrc_adjoin_vs_translate_v1.py`, which reports `n = |V|`
before any verdict and runs two independent implementations (residue criterion, and exact
brute force over signed difference-of-differences candidate times) and asserts they agree.

---

## 1. The claim

`HANDOVER_2026_09_12.md:18-19`:

> "**A grid is an AP with elements missing.** Not "an AP with periodic deletion". Any set whose
> reduced residues form a complete system mod `n`. `(2,6,7,8,10,13,14)` is a grid because it
> sits inside the AP `1..14`. So is `(2,4,6,104)`. So is `(8, 807, 1083, 1239, 1454, 1931,
> 2491)`."

`HANDOVER_2026_09_12.md:48` (§2, row 1), recording an error and its correction:

> "Insisted a "grid" must be an AP under periodic deletion, so `(2,6,7,8,10,13,14)` could not
> be one; then that "subset of an AP" is vacuous | **It is a grid, and it does achieve global
> isolation — verified by brute force after the owner demanded it.**"

## 2. What the artifact returns  `[VERIFIED — two implementations, agreeing]`

| set | `n` | residues | complete | global isolation | max-min-gap vs `1/n` |
|---|---|---|---|---|---|
| `(2,6,7,8,10,13,14)` | 7 | `[0,1,4,4,5,5,6]` mod 7 | **no** | **False** | `3/28` < `1/7` |
| same, `0` adjoined | 8 | `[0,0,2,2,5,6,6,7]` mod 8 | **no** | **False** | `23/208` < `1/8` |
| `(2,4,6,104)` | 4 | `[0,1,2,3]` mod 4 | **yes** | **True** | `1/4` = `1/4`, `t = 1/8` |
| `(8,807,1083,1239,1454,1931,2491)` | 7 | `[0,1,4,4,5,5,6]` mod 7 | **no** | **False** | `39/322` < `1/7` |
| same, `0` adjoined | 8 | `[0,0,3,3,3,6,7,7]` mod 8 | **no** | **False** | `508501/4810121` < `1/8` |

**One of the three examples is a grid.** The first and third are not, on either runner count,
and neither achieves global isolation. The first and third share the residue pattern
`[0,1,4,4,5,5,6]` mod 7, so they fail as the same shape.

This is not a new result in the series. `WHICH_GRIDS_ISOLATE_v1.md:40-41` already states it for
the first example:

> "`π = (0,0,2,2,5,6,6,7)` — the residue pattern of `E* = (0,2,6,7,8,10,13,14)` — **cannot be
> rescued by any deviation.** Four random `q` vectors, all fail."

## 3. The two definitions in `:18-19` are not the same criterion

- "an AP with elements missing" / "sits inside the AP `1..14`" — satisfied by
  `(2,6,7,8,10,13,14)`, and satisfied **by every finite integer set** (take common difference
  1). Vacuous as a criterion.
- "reduced residues form a complete system mod `n`" — the operative criterion, proved
  equivalent to global isolation in `WHICH_GRIDS_ISOLATE_v1` §1 and `FRAME_FREE_RESTATEMENT_v1`
  §1. **Not** satisfied by `(2,6,7,8,10,13,14)`.

`:18-19` presents them as one notion. The set satisfies the first and fails the second, which
is why the example does not carry the point it is used for.

**The objection recorded as an error at `:48` was correct on the point of vacuity.** "Subset of
an AP" *is* vacuous; the complete-residue-system criterion is not. The handover's own next
sentence says so ("The right notion is *complete residue system*, which is neither vacuous nor
periodic-deletion") — it then attaches that right notion to an example that fails it.

## 4. A reading under which the examples are "grids" — and what it does not give

`(2,6,7,8,10,13,14)` reduced is `(0,4,5,6,8,11,12)`, whose residues **mod 14** are
`0,4,5,6,8,11,12` — seven **distinct** points of the ambient 14-lattice. That is true, matches
"the modulus belongs to the AP" (`:21`), and is a non-trivial property.

It does not give global isolation. At `t = p/14` the seven runners sit on distinct 14-grid
points with cyclic gaps `4,1,1,2,3,1,2` in fourteenths, so the minimum gap is `1/14 < 1/7`.
Distinct points on the ambient lattice is a **weaker** property than equally spaced, and only
the latter is isolation.

## 5. What is unaffected

- Grid ⟺ complete residue system ⟺ global isolation at `φ(n)` times. `[PROVED]`, untouched.
- Spread is invisible to global isolation (it lives in `q`). `[PROVED]`, untouched — and
  `WHICH_GRIDS_ISOLATE_v1` §2's positive examples `(4,21,25,27,31,38,48,50)` etc. are correct.
- `(2,4,6,104)` as four runners, and the translation-versus-adjoining distinction
  ([[feedback_count_the_runners_given_2026_09_12]]).
- Every other section of the handover. Only `:18-19` and `:48` are at issue.

## 6. An error of mine, en route

My first pass computed max-min-gap over candidate times `t = k/(n·d)` for **unsigned** pairwise
differences `d`, and returned `9/88` for the eight-runner case where the correct value is
`23/208`. That is exactly the trap recorded in
[[feedback_count_the_runners_given_2026_09_12]] — the min-gap is concave on each cyclic-order
cell, so its maximum can sit strictly inside one, and unsigned candidates miss it. The verdict
happened to be unchanged; the figure was wrong. Every number in §2 above is from the artifact,
not from that pass.

## 7. Status

`[VERIFIED — two implementations, agreeing]` §2's table.
`[DEFECT]` `HANDOVER_2026_09_12:19` — two of three examples are not grids.
`[DEFECT]` `HANDOVER_2026_09_12:48` — "it does achieve global isolation" is false for
`(2,6,7,8,10,13,14)`; and the objection recorded there as an error was right about vacuity.
`[UNAFFECTED]` the framework, and §3–§7 of the handover.

**n = 8 is not proved; nothing here bears on it.**
