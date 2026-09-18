# What the balance is made of

Follows `AUDIT_LEFTOVERS_v1` §2.1. The criterion is

> **clear at `d_min` ⟺ every disparity satisfies `c ≤ a mod 8c ≤ 7c`**, with `c = d_min/g`

Equivalently, in readings `s = d/d_min`:

> **clear at `d_min` ⟺ no disparity has a reading within `1` of a multiple of `8`.**

So the balance — the **46.5%** that do not clear — is exactly the subjects with at least one reading
near `8, 16, 24, …`. Here is that set decomposed.

---

## 1. The first cut: `S ≤ 7` is never in the balance — `[PROVED]`

Readings start at `1` (the minimum itself), and the first multiple of `8` is `8`. So a failure needs
a reading above `7`:

* `a mod 8c > 7c` with `a < 8c` needs `7c < a < 8c` — reading in `(7,8)`;
* `a mod 8c < c` with `a ≥ c` needs `a ≥ 8c` — reading `≥ 8`.

> `DminClearance.clear_of_reading_le_seven` — a reading in `[1,7]` is already inside the band.

Measured: of 9716 subjects with `S ≤ 7`, **9716 clear. Zero violations.**

**This is Theorem 4.8's constant arriving as a corollary rather than an input.** `S ≤ 7` was a
theorem about the clear band; here it falls out of the residue criterion, because `7` is simply
"one below the first multiple of 8".

## 2. How many disparities fail

```
  failing disparities :  1 → 9615   2 → 4218   3 → 951   4 → 106   5 → 4
```

**Mostly one** — 64.6% of the balance fails on a single disparity, 92.9% on one or two.

**The ceiling is 6, and 6 is attained.** `d_min` itself can never fail: `a = c` gives `c mod 8c = c`,
on the lower boundary, and the threshold counts as clear (`DminClearance.dmin_always_clear`). So at
most 6 of the 7 can fail. The sampled maximum was 5 — but a sample maximum is not a bound, a lesson
this session has now paid for twice (the `M ≤ 7` artifact; a parallel session's "max 3 per slot"
forced by its enumeration cap). Constructed instead:

```
  v = [1, 2, 9, 17, 25, 33, 41, 49]   subject 1
  reduced disparities {1, 8, 16, 24, 32, 40, 48}   c = 1   S = 48
  failing: {8, 16, 24, 32, 40, 48}  — six of seven
```

With `c = 1` the bands collapse to `8 ∣ a`, so any six multiples of 8 plus the minimum does it.

## 3. Which side, and at what reading

```
  reading ≥ 8, residue below c   (just past a multiple of 8) : 13161 events
  reading in (7,8) mod 8         (just short of one)         :  8187 events

  reading of the failing disparity : 7 → 5995,  8 → 7168,  ≥9 → 8185
```

Both modes are live and neither dominates. The reading-7 band — a disparity between `7·d_min` and
`8·d_min` — is the one that cannot be reached by any multiple and is purely a spread effect; it is
where `S ≤ 7` is tight.

## 4. Summary

The balance is:

> subjects with `S > 7` carrying at least one disparity whose reading sits within `1` of a multiple
> of `8`; usually exactly one such disparity, at most six, and six is attainable.

`[PROVED]`: §1's implication, the ceiling of 6, and the criterion itself
(`DminClearance.clear_iff`, `bad_iff`, `clear_of_reading_le_seven`, `dmin_always_clear` — all
axiom-clean, zero `sorry`). `[EMPIRICAL]`: the counts in §2 and §3, from 32,000 subject-instances,
speeds `1..89`.

## 5. What this does not do

It characterises the entry to the cascade, not the cascade. A subject in the balance has depth `≥ 1`
and this says nothing about how deep — `NEIGHBOUR_DEFORMATION_v2` §6 measured depth as determined by
neither `π` nor `q`. It also does not bear on Existence.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/DminClearance_v1.lean
python3 experiments/n8/dmin_balance_v1.py    # S<=7 => clear, 9716/9716; the decomposition
python3 experiments/n8/dmin_balance_v2.py    # constructed 6-failure witness
```
