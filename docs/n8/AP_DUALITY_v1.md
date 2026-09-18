# The AP is extremal for covering and trivial for `R` — and the reason is the cage

**Owner's ruling (2026-09-18):** covering arguments built from the framework's own objects are
admitted; §6A protects against accidental import, which this is not. `EXISTENCE_MOVEMENT_v1` §2–§3
are therefore live, and this note builds on them.

---

## 1. The AP's clear set is exactly the odd integers

For the AP — readings `1,2,…,7` — the clear points in `[1,15]`, computed exactly over all band
endpoints:

```
   {1, 3, 5, 7, 9, 11, 13, 15}
```

**Isolated points, measure zero**, and the reason is the cage: `R` odd is a **unit mod 8**, so
`i·R mod 8` permutes `{1,…,7}` as `i` runs over `1..7` and never lands on `0`. The same
`slot_gcd` fact that bars offsets 2, 4, 6 from binding is what protects the AP here.

Checks directly: `R = 7` gives `7,6,5,4,3,2,1`; `R = 9` gives `1,2,3,4,5,6,7`.

## 2. The duality

`EXISTENCE_MOVEMENT_v1` §3 found the AP is the configuration that comes closest to **covering**
`[1,7] ∪ [9,15]` — 99.9982%, uncovered `0.000211`. §1 explains why that residual can never reach
zero *for the AP*: the eight odd integers survive, protected by the unit structure.

So the AP is simultaneously

* **the extremal coverer** — it leaves the least measure clear, and
* **the trivial case for `R`** — its first clear point is `R = 1`, the minimum possible.

Maximising coverage and maximising `R` are *different objectives*, and the AP is optimal for the
first and pessimal for the second. That resolves an apparent tension between
`EXISTENCE_MOVEMENT_v1` §3 and `R_FRONTIER_v1` §4: the `R`-maximisers are **not** the AP but the
irregular profiles at `S ≈ 7.45`.

## 3. Crossing the AP boundary

The one-parameter family `1, 1+u, …, 1+6u` (so `S = 1+6u`, and `u = 1` is the AP), first clear
point in exact arithmetic:

```
       u        S    first clear R
   1.000    7.000       1.000000        the AP — protected
   1.005    7.030       4.980080        <-- jumps immediately
   1.010    7.060       4.960317
   1.050    7.300       4.807692
   1.055    7.330       4.789272
   1.060    7.360       3.396739        <-- drops again
```

The instant `S` exceeds 7, reading 7 passes the threshold, the protected point at `R = 1` is
destroyed, and `R` jumps to ≈ 4.98. But this family stays in **band 0** throughout — it never
reaches the band-1 region where the deep cases live. **Regular (AP-like) spacing is not how you get
a large `R`**; irregular spacing is.

## 4. Where this leaves the covering question

The question from `EXISTENCE_MOVEMENT_v1` §2 — can the six non-minimal combs cover `[1,7] ∪ [9,15]`
entirely — now has a sharper shape:

* the best *coverer* (the AP) fails by exactly eight protected points, and they are protected by a
  **unit-group** fact, not an accident;
* the best *`R`-maximiser* (irregular, `S ≈ 7.45`) reaches `R ≈ 11.97` and leaves band 1's upper half
  and all of band 2 unreached;
* those two optima are different configurations, so a counterexample would have to beat the AP at
  covering *while* being irregular enough to push `R` past 15 — and no search has found a profile
  doing both.

That is a description of the obstruction, not a proof of it.

## 5. Grades

| | |
|---|---|
| the AP's clear set in `[1,15]` is `{1,3,5,7,9,11,13,15}` | `[PROVED]` — exact computation over all band endpoints, plus the unit-group argument |
| the AP is the extremal coverer | `[EMPIRICAL]` — 3,000-restart optimisation |
| the `R`-maximisers are not the AP | `[EMPIRICAL]` + §3's family trace |
| a covering counterexample exists | **not established** |

```bash
python3 experiments/n8/ap_crossing_v2.py   # the AP family trace; the odd-integer clear set
```
