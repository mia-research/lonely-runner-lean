# The AP is the unique coverer, and `S > 7` breaks it — the obstruction, located

The interlocking obstruction has a shape. It is not "six combs cannot interlock"; it is that
**exactly one profile interlocks, and it is the one excluded by `S > 7`.**

---

## 1. Setup — why uncovered length is the right quantity

`s₁ = 1`'s own bad set is `(7,9) ∪ (15,17) ∪ …`, which lies **outside** `[1,7] ∪ [9,15]`. So a point
of that region not covered by the other six is clear for **all seven** readings. Hence

> **joint uncovered length `> 0`  ⟹  a clear `R ≤ 15`  ⟹  `R < 16`.**

The region also splits: no chain crosses `(7,9)`, so `[1,7]` and `[9,15]` are independent problems on
the same six readings (`TENSION_v1` §1).

## 2. The two regions want opposite readings

Optimising each region alone:

```
   covers [1, 7] : readings [3.04, 4.06, 5.07, 5.82, 6.68, 7.26]   — all large
                   leaves 1.183 uncovered in [9,15]
   covers [9,15] : readings [1.26, 1.37, 1.65, 2.95, 6.16, 7.02]   — mostly small
                   leaves 1.244 uncovered in [1, 7]
```

In 60,000 random profiles, **none** covered both to within `0.01`. The demands are opposed.

## 3. Exactly one profile satisfies both — the AP

```
   readings 2,3,4,5,6,7 :  uncovered [1,7] = 0,  uncovered [9,15] = 0,  joint = 0
```

Complete on both regions, up to measure zero — the residual being the eight protected odd integers
of v11 Theorem 11.3, which have no length. Six hundred restarts of joint optimisation found **nothing
else with joint uncovered `0`.**

## 4. And `S > 7` destroys it, at a linear rate

Raising the largest reading alone, `2,3,4,5,6,7+ε`:

```
      ε        unc [1,7]     unc [9,15]        joint
    1e-6      1.000e-6       2.143e-6      3.143e-6
    1e-4      1.000e-4       2.143e-4      3.143e-4
    1e-2      1.000e-2       2.140e-2      3.138e-2
```

`unc[1,7] ≈ ε`, `unc[9,15] ≈ (15/7)·ε`, **joint ≈ (22/7)·(S − 7)** — linear, with the slope stable
over four decades.

## 5. Searched away from the AP, with no cap on `S`

Minimising joint uncovered subject to `S > 7`, readings free in `(1, HI)`:

```
     HI      min joint uncovered    S at minimum    readings at minimum
      8          2.2889e-5            7.000004      ≈ 2, 3, 4, 5, 6, 7
     10          1.2295e-5            7.000004      ≈ 2, 3, 4, 5, 6, 7
     16          3.3260e-6            7.000001      ≈ 2, 3, 4, 5, 6, 7
     24          6.9430e-5            7.000015      ≈ 2, 3, 4, 5, 6, 7
     40          3.6300e-6            7.000001      ≈ 2, 3, 4, 5, 6, 7
```

**Every search, at every cap, converges on the AP and drives the minimum only by driving `S → 7⁺`.**
And over **194,768** random profiles with `S > 7`, joint uncovered was **never** zero.

## 6. What this says

> The AP is (apparently) the **unique** profile covering `[1,7] ∪ [9,15]`. It has `S = 7`, which by
> Corollary 6.21 clears at `R = 1`. Every profile with `S > 7` leaves positive uncovered length, and
> therefore has `R < 16`.

That is the obstruction, located. It is not a counting fact — counting gives `1.5×` and decides
nothing — and it is not the "two regions want opposite readings" tension on its own, which the AP
resolves. It is that **the resolution is unique and sits exactly on the excluded boundary**.

The mechanism is the one already proved: the AP's covering is complete only up to the eight odd
integers, and those are protected by `R` odd being a **unit mod 8** (v11 Theorem 11.3, the same
`slot_gcd` fact as the cage). Pushing `S` past 7 is precisely what destroys the unit structure —
reading 7 leaves `[1,7]` — and the uncovered length opens linearly.

## 7. Grades, and the size of the claim

| | |
|---|---|
| uncovered `> 0` ⟹ `R < 16` | **`[PROVED — in the text]`**, from the band structure (v11 Theorem 11.2) |
| the regions split and want opposite readings | `[EMPIRICAL]`, 60,000 profiles |
| the AP has joint uncovered `= 0` | **`[PROVED — in the text]`**, v11 Theorem 11.3 |
| the AP is the **unique** such profile | `[EMPIRICAL]` — 600 joint-optimisation restarts, 5 range caps, 194,768 random profiles |
| joint uncovered `≈ (22/7)(S−7)` near the AP | `[EMPIRICAL]`, stable over four decades |
| `S > 7` ⟹ uncovered `> 0` for **every** profile | **`[EMPIRICAL]`, not proved** |

**The last line, if proved, is Existence at order 8.** So it is at least as hard as the conjecture,
and no search establishes it. What has changed is the *shape* of what must be proved: from "six
arithmetic-progression families cannot interlock" to **"the AP is the unique interlocking, and it
sits on the excluded boundary"** — a uniqueness-and-boundary statement about one explicit
configuration, with a measured linear rate away from it.

```bash
python3 experiments/n8/bottleneck_v1.py     # the two regions want opposite readings
python3 experiments/n8/bottleneck_v2.py     # the AP is the joint optimum; perturbation rates
python3 experiments/n8/ap_isolation_v1.py   # raising S alone: linear at (22/7)(S-7)
python3 experiments/n8/ap_isolation_v2.py   # no cap on S; 194,768 profiles, never zero
```
