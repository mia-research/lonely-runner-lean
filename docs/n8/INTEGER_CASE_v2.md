# Existence holds for every integer-reading profile with readings ≤ 40

Supersedes `INTEGER_CASE_v1`, whose Branch B was a target. It is now discharged on that range, with
a quantitative floor.

---

## 1. The result

For a profile whose readings `s_i = d_i/d_min` are **integers** with `s_7 ≤ 40`:

```
   BRANCH A   no reading ≡ 0 (mod 8)
              →  every odd integer of [1,15] is clear          [PROVED, all sizes]
              →  R = 1  <  16

   BRANCH B   some reading ≡ 0 (mod 8)
              →  uncovered length ≥ 53/462                     [EXHAUSTIVE on readings ≤ 40]
              →  a clear interval exists, so R ≤ 15  <  16
```

**Either way `R < 16`, hence the clear set is non-empty, hence the cascade terminates and the
subject is lonely.** So Existence at order 8 holds throughout that class.

## 2. The two branches

**Branch A — proved, for integer profiles of any size.**
`Guard.odd_clear_of_not_dvd`: for integer `s` with `8 ∤ s` and `R` odd, `8 ∤ s·R`. No reading blocks
any odd instant, so all eight of `1,3,…,15` are clear. Axiom-clean, no bound on the readings.

**Branch B — exhaustive, exact, on readings `2..40`.**

```
   profiles containing a multiple of 8 :  1,917,719
   with uncovered length = 0           :  0
   minimum uncovered                   :  53/462 = 0.11471861…   at [3, 4, 5, 7, 11, 24]
```

Every one computed in exact rational arithmetic. The floor `53/462` is not "positive" but **bounded
away from zero**, which is the shape a proof would need.

## 3. Why the split is the right one

A reading divisible by `8` is exactly a **colliding** disparity (v11 §6.15) — it blocks every odd
instant at once, which is why Branch A's hypothesis is precisely "no collisions". So Branch A *is*
`spine_all_or_nothing` read through the covering, and Branch B says a collision, far from helping the
covering, forces a gap of definite size.

This is the third question in this line decided by the unit / non-unit split of `slot_gcd`, after
the cage (v11 Cor 4.14) and the guards (`GUARD_ISOLATION_v1`).

## 4. Scope — stated precisely, because it is narrow

* **Integer readings** means `d_min` divides every disparity. Rational speeds give rational readings,
  not integer ones, so this is a proper sub-class and not the general rational case.
* **Readings `≤ 40`** bounds `S = d_max/d_min ≤ 40`. Branch A has no such bound; Branch B does.
* Nothing here touches irrational profiles, or integer profiles with readings above 40.

What it is: a **complete, exactly verified** closure of a concrete infinite-in-speed but
finite-in-shape class, with one branch proved outright.

## 5. What would extend it

Branch B for all integer readings, not just `≤ 40`. The floor `53/462` at `[3,4,5,7,11,24]` is a
starting point: if the minimum uncovered over profiles containing a multiple of `8` is bounded below
uniformly, Branch B closes for every integer profile, and with Branch A that is Existence for the
entire integer class.

## 6. Status

| | |
|---|---|
| Branch A, any integer profile | **`[PROVED]`** `Guard.odd_clear_of_not_dvd`, axiom-clean |
| Branch B, readings ≤ 40 | **`[VERIFIED — exhaustive, exact]`** 1,917,719 profiles |
| Existence for integer readings ≤ 40 | **established**, by the two branches |
| Branch B in general | open — the natural next target |
| the general (non-integer) case | untouched |

```bash
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
python3 experiments/n8/zeros_wide_v1.py   # the three zeros, none with a multiple of 8
python3 experiments/n8/mult8_v1.py        # 1,917,719 profiles, minimum uncovered 53/462
```
