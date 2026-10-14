# Searching the zeros exactly: two uniqueness claims withdrawn, and what survives

Following the exact-arithmetic discipline the whole way. Two of my claims fall; the thing the
reduction actually needs survives every test.

---

## 1. The first-order rates are the guard structure — derived

Exact rates of the uncovered-length functional at the AP:

```
      reading 2 : 0  both         reading 3 : 14/3 , 18/3
      reading 4 : 0  both         reading 5 : 18/5 , 14/5
      reading 6 : 0  both         reading 7 : 22/7 , 10/7
```

Zero on the non-units, positive on the units. And the `+` rate at unit `p` is **derived**: `p` guards
`R = p` and `R = p+8`, so raising it opens `(2p+8)/p`. All three match — `14/3`, `18/5`, `22/7`.

## 2. Withdrawn: "the AP is the unique zero"

The zero set is a **cell**, bisected exactly:

```
      reading 2 : zero on (161/81, 175/87)      reading 4 : (195/49, 285/71)
      reading 6 : zero on (435/73, 623/103)
```

with rational faces of band-edge form (`175/87 = (8·22−1)/(8·11−1)`). `REDUCTION_v1` §3 is withdrawn.

## 3. Withdrawn: "the units must be at 3, 5, 7"

Exhaustive over **integer** profiles, readings `2..40`, all 3,838,380 combinations:

```
      [2, 3, 4, 5, 6, 7]     clear {1,3,5,7,9,11,13,15}
      [2, 3, 4, 5, 7, 12]    clear {1,3,5,7,9,11,13,15}
      [4, 5, 6, 7, 11, 13]   clear {1,3,5,7,9,11,13,15}
```

Three zeros, not one. The third has no reading at `3` — it uses `11 ≡ 3 (mod 8)` and `13 ≡ 5` as
guards instead. So `ZERO_REGION_v1` §3's "units are `3,5,7`" is withdrawn too; what matters is that
the profile supplies the guard **residues**, not the guard values.

## 4. What survives — and it is exactly what the reduction needs

**Every zero found has all eight protected points clear.** The reduction never needed uniqueness of
the profile, nor pinned units; it needs the clear set non-empty:

```
   Existence  ⟸  clear set non-empty in [1,15]               [PROVED]
              ⟸  uncovered > 0  OR  uncovered = 0 with a clear point
              ⟸  uncovered > 0                                [PROVED]  positive measure
              ⟸  uncovered = 0  ⟹  some point stays clear     ← THE GAP
```

and the gap is now a statement about the **zeros of a functional**, of which the exact search has
found three (integers to 40) and all three satisfy it with room to spare — eight clear points each.

## 5. A proved sub-case: integer profiles with no reading divisible by 8

> **`Guard.odd_clear_of_not_dvd`** — for integer `s` with `8 ∤ s` and odd `R`, `8 ∤ s·R`.
> `[PROVED]`, axiom-clean.

So an integer profile with no reading `≡ 0 (mod 8)` leaves **every** odd integer of `[1,15]` clear,
giving `R = 1`. **Existence holds outright for that class**, and the integer case reduces to profiles
carrying a reading divisible by `8` — the colliding readings of v11 §6.15, seen from the covering
side.

## 6. Verified formal tally

Every file checked **standalone**, its own theorems axiom-checked:

```
   GridNeighbour 8   SingleLevelGeneral 3   ExactBlock 5   DminClearance 7
   MoveRule 2        DilationBound 2        RBand 1        RCapObligation 2
   Guard 6           NoFinitePoints 2       ResiduePartition 3   TwoWalker 5   Bridge 1
   ------------------------------------------------------------------------
   47 theorems, 47 axiom-clean, zero sorry, zero errors
```

**A counting note, recorded because it is the project's own known defect.** My ad-hoc tally first
reported 48 and one error: line 7 of `DminClearance_v1.lean` is a doc-comment beginning with the word
`theorem`, which the regex counted as a declaration. That is exactly the proxy defect the manuscript's
v9.6 header records — the gate carries a `strip_comments` guard for it and my script did not.
**v11's table saying "DminClearance 7" and "27 in 7 files" was right; my recount was wrong.**

```bash
python3 experiments/n8/exact_local_v1.py       # the six exact rates
python3 experiments/n8/zero_region_v1.py       # the zero cell's rational faces
python3 experiments/n8/integer_profiles_v1.py  # three integer zeros
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
```
