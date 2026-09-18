# The colliding blocks, fully partitioned

**Owner, 2026-09-18:** *"Measured 81.3% ok, but the rest must occur for a reason. It's not like
they change if we run them again."*

Correct, and it was a framing error on my side: `81.3% / 18.7%` is a **deterministic arithmetic
partition**, not a sample with residual noise. Re-running finds the same events. Here is the whole
partition, with nothing left over.

---

## 1. The setup

A cascade scale is `D = c·g/(8N+1)` for some disparity `c·g`. A blocker `a·g` reads

```
    s = d/D = a(8N+1)/c          and blocks when   |s − 8M| < 1 for some M.
```

For a **colliding** blocker, `a = 8b`. Put `r = b(8N+1) mod c`. Then `s = 8·b(8N+1)/c`, and the
block condition is `min(r/c, 1 − r/c) < 1/8`.

## 2. The partition — three cases, and that is all of them

```
  r = 0                EXACT block, s is exactly 8M      4314 events   (81.3%)
  7c/8 < r < c         near block, s just BELOW 8M         731 events   (13.8%)
  0 < r < c/8          near block, s just ABOVE 8M         260 events   ( 4.9%)
                                                      -----------
                                                          5305 events
```

**`r = 0 ⟺ exact block`: 5305 of 5305** (`colliding_mechanism_v2.py`). The criterion is exactly
`c ∣ b(8N+1)`.

## 3. Why only colliding disparities block exactly — `[PROVED]`

If `s = a(8N+1)/c` equals `8M` then `8 ∣ a(8N+1)`, and `8N+1` is odd, so `8 ∣ a`.

> `ExactBlock.exact_block_is_colliding`

Measured: non-colliding disparities block exactly **0 times in 12,152**. That zero is the theorem,
not the sample.

## 4. Why the near blocks need a large host — `[PROVED]`

`r` is an integer with `1 ≤ r ≤ c−1`, and a near block needs `8r < c` or `8(c−r) < c`. Either
forces `c > 8`.

> `ExactBlock.near_block_host_large`, and its contrapositive `small_host_forces_exact`

**So if the host disparity is `≤ 8` in reduced units, every colliding block is exact.** Measured:
zero violations, and the smallest `c` among near blocks is exactly **9**.

## 5. Why the near blocks lean 74:26 to one side

The two near zones have equal width `c/8`, and `r ↔ c−r` makes their integer counts equal, so a
uniform `r` gives 50:50. Observed 731:260.

**Cause: the cascade's readings grow monotonically.** `t` strictly increases, `D = 1/(8t)` strictly
decreases, so every `s = d/D` strictly increases — verified `6278/6278`. A blocker therefore enters
its bad zone `(8M−1, 8M+1)` across the **bottom** edge, and is generically caught at `s ≈ 8M−1`,
which is the "just below `8M`" side. Being on the "just above" side requires having already passed
the coincidence point.

The data locates it precisely: the split is carried by **first sight** of a blocker — 586 below vs
213 above — not by lap transitions (33 vs 47). *My first cut of this was wrong*: I predicted the
asymmetry would show up as the blocker's lap index advancing, and attached the right mechanism to
the wrong bookkeeping. Monotone entry is the cause; it acts on first sight.

## 6. What the partition gives

- **An exact block is a coincidence.** `s = 8M` means `d·t = M`: the blocker is exactly *on* the
  subject. That is the maximal violation, and it is available only to colliding disparities.
- **An exact block forces the next move.** `k = M`, so `t' = (M + 1/8)/d` with nothing to choose.
- **Small hosts admit only exact blocks**, so early in a cascade — where the scales come from small
  disparities — the colliding blocks are all coincidences and all forced.

That is why colliding disparities drive 31.3% of setter events on 19.2% of the pack, and why the
effect is strongest at the smallest size ranks (2.64× at rank 1, falling to 1.38× at rank 6):
small hosts are exactly where the exact-block regime is total.

## 7. What is not claimed

No proof at order 8. This says *how* colliding disparities act, not how far. It does not bound
depth — `NEIGHBOUR_DEFORMATION_v2` §6 measured depth as determined by neither `π` nor `q` — and it
does not close §2.3's open item. Counts in §2 and §5 are from one sampler (speeds `1..89`, 2,500
arrangements, 6,370 colliding subjects); the two `[PROVED]` items in §3 and §4 are not.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/ExactBlock_v1.lean   # 4 thms, [propext, Quot.sound]
python3 experiments/n8/colliding_mechanism_v2.py   # r = 0 <-> exact, 5305/5305; smallest near c = 9
python3 experiments/n8/colliding_mechanism_v3.py   # monotonicity 6278/6278; the 74:26 split
```
