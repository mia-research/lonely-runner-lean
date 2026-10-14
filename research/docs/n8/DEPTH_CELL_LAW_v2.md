# Correction to `DEPTH_CELL_LAW_v1` §1: the 28-move case is real

Supersedes `DEPTH_CELL_LAW_v1` §1 and §1.1 only. §2–§5 of that file (the cell census, the width law,
the dilation mechanism) are unaffected and stand.

## What happened

`DEPTH_CELL_LAW_v1` §1 announced that the 28-move case "does not exist" and that I had fabricated
it. **That announcement was itself wrong.** Two errors in sequence:

1. The arrangement reached me as `(27,70,…,393)` with an ellipsis, and I filled in the middle terms
   myself (`133,190,243,297,340`). That reconstruction has maximum depth 5. **This error was real.**
2. On finding my reconstruction shallow, I declared the case fabricated — **without checking
   `MANUSCRIPT_v10.md`, which records the full arrangement on disk.** It is at v10 lines 767, 798
   and 1024.

The second is the worse error: the source was on disk, and CLAUDE.md §5 says read the source first.
I violated that rule *inside a correction*, which is where care should be highest.

## The verified fact

```
  (27, 70, 107, 137, 159, 188, 344, 393),  subject 393
  d_min = 49,  S = 7.469,  depth 28,  t* = 49/1872
```

Reproduced independently just now; matches v10's record exactly, including `t*`.

## Consequences

* **The record is 28, verified.** My band-directed best is **27**, so it does **not** beat the
  record. `DEPTH_CELL_LAW_v1` §1.1 claimed it did; that claim is withdrawn.
* `DEEP_CONSTRUCTION_v1` §6 — *"the record was not beaten — best constructed 27, on file 23 and
  28"* — was **correct as originally written** and is reinstated.
* Nothing in the cell-width law depended on the mislabel. The 96-cell census used the shallow set
  under a wrong name; its cells are still valid data (a depth-5 case contributes cells like any
  other), and re-labelling does not change the fit.

## A note worth keeping

Both deep cases have nearly the same spread:

```
  23-move: d_min = 30, S = 7.467
  28-move: d_min = 49, S = 7.469
```

`S ≈ 7.47` in both — consistent with the band enrichment already measured, and a datum for the
profile analysis in progress.

## The lesson, stated plainly

A correction is not exempt from the source-first rule. I had `MANUSCRIPT_v10.md` on disk, it
contained the arrangement, and I did not grep it before announcing that the case was invented.
