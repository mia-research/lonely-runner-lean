# Integer readings block 8-periodically — the problem halves

Reasoning Branch B forward. The minimiser's gap structure revealed a periodicity that cuts the
integer case in half and reduces the target region from `[1,15]` to `[1,7]`.

---

## 1. The observation

The Branch-B minimiser `[3,4,5,7,11,24]` has uncovered set

```
   [1, 7] :  (9/7, 31/24)   (41/11, 15/4)   (17/4, 47/11)   (161/24, 47/7)
   [9,15] :  (65/7,223/24)  (129/11, 47/4)  (49/4,135/11)   (353/24,103/7)
```

Every gap in the second region is a gap in the first **shifted by exactly 8**: `9/7 + 8 = 65/7`,
`31/24 + 8 = 223/24`, and so on for all four.

## 2. The reason, proved

For an **integer** reading `s`,

```
      s·(R+8) − s·R  =  8s   ≡ 0  (mod 8)
```

so `R` and `R+8` are congruent in the blocking condition and block together. Explicitly, a witness
`M` that `s` is in the way at `R` transfers to `M + s` at `R + 8`:

> **`Guard.block_periodic`** and **`Guard.block_shift`** — `[PROVED]`, axioms `[propext, Quot.sound]`
> only, no choice.

## 3. What it buys

Three consequences, for integer readings:

* **`[9,15]` is a translate of `[1,7]`.** The uncovered sets are shifted copies, so
  `joint uncovered = 2 × uncovered([1,7])` — confirmed on the minimiser, `53/462 = 2 × 53/924`.
* **The clear set is 8-periodic.** It is non-empty in `[1,15]` iff it is non-empty in `[1,7]`.
* Hence **`R ≤ 7` whenever a clear instant exists at all** — for integer readings, the bound is `7`,
  not `16`, and the whole band-2 question collapses into a length-6 region.

So Branch B's target simplifies to:

> for an integer profile containing a multiple of `8`, is `uncovered([1,7]) > 0`?

Half the computation, half the region, and the search reaches roughly twice as far for the same
effort.

## 4. Why a multiple of 8 is the right hypothesis

A reading `s = 8b` has bad set `((m − 1/8)/b, (m + 1/8)/b)` — a comb of period `1/b` centred on the
multiples of `1/b`. At `b = 1` that is a neighbourhood of **every integer**, width `1/4`. So a
multiple of `8` is exactly what blocks the eight odd integers that Branch A relies on, and Branch B
asks whether buying that costs coverage elsewhere.

The measured answer so far is yes, with a floor: over 1,917,719 integer profiles with readings `≤ 40`
containing a multiple of `8`, the minimum joint uncovered is `53/462`, attained at `[3,4,5,7,11,24]`.

## 5. Status

| | |
|---|---|
| blocking is 8-periodic for integer readings | **`[PROVED]`** `block_periodic`, `block_shift` |
| `[9,15]` gaps are `[1,7]` gaps shifted by 8 | **`[VERIFIED — exact]`** on the minimiser |
| for integer readings, `R ≤ 7` if any clear instant exists | follows from the above |
| Branch B for readings ≤ 40 | **`[VERIFIED — exhaustive]`**, floor `53/462` |
| Branch B in general | open; the search now reaches twice as far per unit effort |

```bash
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
python3 experiments/n8/branchB_v1.py   # the mirrored gap structure
```
