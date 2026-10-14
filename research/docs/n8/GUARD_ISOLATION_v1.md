# The guards are the isolation pattern — the loop closes

The guard structure of `AP_MECHANISM_v1` and the AP's global-isolation pattern are **the same
object, indexed the same way.** Verified 8 of 8.

---

## 1. The correspondence

The protected points are `R = 8k + p` with `p` a unit mod `8`. The guard of `R` is the reading
`≡ R⁻¹ ≡ p` (Klein). The AP's global isolation occurs at the `φ(8) = 4` grid instants `p/8`, where
the binding pair is at offset `±p` (v11 Corollary 4.15).

> **The reading that guards protected point `R` is the runner that binds at instant `p = R mod 8`.**

```
   protected R :  1    3    5    7    9   11   13   15
   R mod 8     :  1    3    5    7    1    3    5    7
   guard       :  1    3    5    7    1    3    5    7
   = binder at instant p ?   True × 8
```

## 2. Two patterns and two inversions

The binding pairs at the four instants, for subject `1` of the AP:

```
   instant p = 1 :  offsets (1, 7)          p = 7 :  (7, 1)   — the inversion
   instant p = 3 :  offsets (3, 5)          p = 5 :  (5, 3)   — the inversion
```

`1·7 ≡ 1` and `3·5 ≡ 1` in `(ℤ/8)ˣ`, so the four instants are **two patterns and two inversions** —
which is what the AP's global isolation was already recorded to be. The eight protected points pair
the same way: `{1,9} ↔ {7,15}` and `{3,11} ↔ {5,13}`.

## 3. The non-units guard nothing

```
   reading 2 : guards nothing
   reading 4 : guards nothing
   reading 6 : guards nothing
```

The same offsets the cage bars from ever binding (v11 Corollary 4.14, `even_offset_caged`). A reading
guards `R` iff `s·R ≡ 1 (mod 8)`, which needs `s` to be a unit — so guarding and binding are the same
predicate, and both are the unit condition of `slot_gcd`.

## 4. What this makes of the obstruction

Reading the chain in one direction:

```
    slot_gcd  →  only units bind        →  only units guard
              →  the AP's readings 1..7 supply exactly one guard per unit
              →  the AP covers [1,7] ∪ [9,15] up to eight points of measure zero
              →  and S ≡ 7 guards the right endpoint of BOTH regions
              →  so S > 7 un-guards both, opening 22ε/(7+ε) of clear length
```

Every arrow is proved except the uniqueness of the AP as a coverer, which remains searched
(`AP_ISOLATION_v1` §5). The obstruction is therefore not a new mechanism bolted on: it is the cage,
followed through to the covering.

## 5. Formalised

`experiments/n8/Guard_v1.lean` — **5 theorems, zero `sorry`, all axiom-clean**
(`[propext, Classical.choice, Quot.sound]`):

```
   guard_blocks_below   a reading on a lower band edge blocks just below it
   raising_unguards     raising a guard moves it into the clear band
   klein_self_inverse   every unit of ZMod 8 is its own inverse            (decide)
   ap_clear_at_odd      8 ∤ i·R for 1 ≤ i ≤ 7 and R odd — the AP's clear points
   unguarded_width      the un-guarded interval is exactly δ < R·ε/(g+ε)
```

`unguarded_width` reproduces the measured intervals exactly: at `g = 7`, widths `7ε/(7+ε)` and
`15ε/(7+ε)`, joint `22ε/(7+ε)` — matching `ap_mechanism_v1.py` to ten decimal places.

Session total: **34 theorems** across nine files, all axiom-clean.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
python3 experiments/n8/guard_isolation_v1.py   # the 8-of-8 correspondence
```
