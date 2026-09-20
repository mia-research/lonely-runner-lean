# L3 upgraded — the reading is sound and complete

2026-09-15. Replaces the `[PROVED — arithmetic; verified]` grade of `LEMMAS_v1` L3, whose text
pointed at a proof — *"the chain construction is the proof"* — rather than giving one. The content
is provable; what follows is the argument.

**What L3 should say.** The original reads *"its first boundary point is the first instant all
seven others stand clear"*, which conflates the candidate list with the answer. The statement that
is true and provable is that the procedure is **sound** and **complete**: what it returns is an
isolation instant, it returns the earliest one, and it returns nothing only when there is nothing
in the range.

---

## Setting

Runner `i` has differences `d_1, …, d_7 > 0`; write `m = min_j d_j`. Runner `j` stands clear of
`i` at `t` when `‖d_j t‖ ≥ 1/8`, so its clear set is

    C_j  =  { t > 0 : ‖d_j t‖ ≥ 1/8 }  =  ⋃_{k ≥ 0}  [ (8k+1)/(8 d_j),  (8k+7)/(8 d_j) ]

and the instants at which `i` is isolated are `I = ⋂_j C_j`. The left endpoints
`(8k+1)/(8 d_j)` are the **openings**, the right endpoints `(8k+7)/(8 d_j)` the **closings**.

## (a) `I` is closed, and starts no earlier than `1/(8m)`  `[PROVED]`

Each `C_j` is a locally finite union of closed intervals, hence closed; `I` is an intersection of
closed sets, hence closed. And for `t < 1/(8m)` we have `m t < 1/8`, so `‖m t‖ = m t < 1/8` and the
runner at difference `m` is not clear. Hence `I ⊆ [1/(8m), ∞)`. ∎

## (b) On a bounded range the first instant exists  `[PROVED]`

By (a), `I ∩ (0, T] = I ∩ [1/(8m), T]` — a closed subset of a compact interval, hence compact. A
nonempty compact subset of `ℝ` has a least element. So if the range holds an isolation instant at
all, it holds an earliest one. ∎

## (c) The first instant is an opening  `[PROVED]`

Let `t* = min ( I ∩ [1/(8m), T] )`.

If `t* = 1/(8m)` then `t* = (8·0 + 1)/(8m)`, an opening, and we are done.

Otherwise take `t_n ↑ t*` with `t_n < t*`. Each `t_n ∉ I`, so each fails some `j`; since there are
seven indices, one index `j` fails for infinitely many, giving a sequence `t_n ↑ t*` with
`t_n ∉ C_j`. But `t* ∈ C_j`, so `t*` lies in some component
`[(8k+1)/(8 d_j), (8k+7)/(8 d_j)]` of `C_j`, and it is a limit from the left of points outside
`C_j`. Only the **left** endpoint of a component has that property — an interior point and a right
endpoint both have a whole left-neighbourhood inside `C_j`. Hence
`t* = (8k+1)/(8 d_j)`. ∎

So the closings can be dropped from the candidate list: they never supply the minimum.
`[VERIFIED — 3,200/3,200 runner-instances]` the openings-only enumeration and the full endpoint
enumeration return the same instant in every case.

## (d) The procedure is sound and complete  `[PROVED]`

Let

    K(T)  =  { (8k+1)/(8 d_j)  :  1 ≤ j ≤ 7,  k ≥ 0 }  ∩  [1/(8m), T] .

`K(T)` is finite — for each `j` there are at most `T·d_j + 1` admissible `k`. The procedure
enumerates `K(T)` in increasing order and returns the first member at which all seven stand clear.

- **Sound.** What it returns lies in `I` by construction.
- **Complete.** If `I ∩ (0,T] ≠ ∅` then by (b) it has a least element `t*`, and by (c)
  `t* ∈ K(T)`. Every member of `K(T) ∩ I` is `≥ t*`, so the first one found *is* `t*`.
- **Honest on failure.** If no member of `K(T)` lies in `I`, then `I ∩ (0,T] = ∅` — again by (c),
  since a nonempty intersection would put its minimum in `K(T)`. ∎

`[VERIFIED — 3,200/3,200]` against the full endpoint search; and the first instant is an opening in
3,200 of 3,200.

## (e) The boundary separation is necessary, not stylistic  `[PROVED — by example]`

`I` can have empty interior. For the AP's end runner, `d = (1,2,3,4,5,6,7)`,

    I ∩ [1/8, 7/8]  =  { 1/8, 3/8, 5/8, 7/8 }        exactly — four isolated points.

So an implementation that evaluates cell midpoints, or merges touching closed zones, reports the
AP's own end runners as never isolated. The separate evaluation of boundary points is forced by
the extremal case, not chosen for tidiness. (This is the trap recorded at `OWNER_PROCEDURE_v1` §1
and `PROOF_CANDIDATE_v3` §5.)

---

## Grade

`[PROVED]` (a), (b), (c), (d), (e) — for arbitrary positive real differences, no integrality, no
commensurability, nothing cited.

**Not proved, and not claimed:** that `I` is nonempty. That is C1, and it is LRC(8) for runner `i`.

**So the "within any searched range" qualifier is not a hedge.** It is forced: the procedure cannot
be unconditional precisely because nonemptiness is the open core. L3 says the reading never lies
and never misses; it does not say the search terminates. Those are different statements and only
the first is a lemma.

## What this changes in `LEMMAS_v1`

| | |
|---|---|
| L3's grade | was `[PROVED]` on a pointer; now `[PROVED]` on the argument above |
| L3's statement | *"its first boundary point is the first instant all seven stand clear"* → soundness and completeness of the procedure, with closings droppable |
| L3's relation to C1 | now explicit: L3 is conditional on the range holding an instant, and that condition **is** C1 |

`[VERIFIED — 3,200/3,200]` the procedure against the full endpoint search; the opening property;
and the AP end runner's four isolated points.
