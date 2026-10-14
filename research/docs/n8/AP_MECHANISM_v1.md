# The guard structure: why the AP covers, and why `S > 7` un-covers it

The `(22/7)(S−7)` rate of `AP_ISOLATION_v1` is **derived**, not fitted. The mechanism is the units
mod 8 — the same `slot_gcd` fact as the cage — and it fits the framework's own objects exactly.

---

## 1. Guards

At a clear point `R`, the reading that blocks **just below** it is the one landing exactly on the
lower band edge: `s·R = 8k+1`. Then `s(R−δ) = 8k+1 − sδ` lies strictly between `8k` and `8k+1` for
`0 < δ < 1/s` — in the way.

> **`Guard.guard_blocks_below`** — `[PROVED]`, axiom-clean.

The condition `s·R ≡ 1 (mod 8)` means `s ≡ R⁻¹ (mod 8)`, and since `(ℤ/8)ˣ` is the **Klein
four-group**, `R⁻¹ = R`. So the guard of `R` is the reading `≡ R (mod 8)`. For the AP:

```
      R  =  1,  9    guard  s ≡ 1     — that is s₁ = 1 itself
      R  =  3, 11    guard  s = 3
      R  =  5, 13    guard  s = 5
      R  =  7, 15    guard  s ≡ 7     →  s₇ = S
```

**The eight protected points are guarded in pairs by the four units `1, 3, 5, 7`.** The non-units
`2, 4, 6` guard nothing — the same readings the cage (v11 Corollary 4.14) bars from ever binding.
The AP covers because its readings supply exactly the four guards.

## 2. `S` guards both right endpoints

`R = 7` and `R = 15` are the right endpoints of the two regions, and **both** are guarded by the
reading `≡ 7`, which in the AP is `s₇ = S`. Raising it un-guards both at once
(`Guard.raising_unguards`: `s < s'` and `s·R = 8k+1` give `s'·R > 8k+1`, so the guard has moved into
the clear band).

The uncovered set that opens is then exactly computable:

```
   at R = 7 :   (7+ε)(7−δ) ≥ 8·6+1  ⟺  δ ≤  7ε/(7+ε)     →  [7 − 7ε/(7+ε),  7]
   at R = 15:   (7+ε)(15−δ) ≥ 8·13+1 ⟺  δ ≤ 15ε/(7+ε)    →  [15 − 15ε/(7+ε), 15]
   joint length =  22ε/(7+ε)
```

Verified to **ten decimal places** at `ε = 10⁻², 10⁻³, 10⁻⁴`, and the uncovered set is exactly those
two intervals and nothing else:

```
   ε = 0.001 :  [6.99900014, 7.0]  and  [14.99785745, 15.0]
                lengths 0.0009998572 and 0.0021425511,  predicted identically
                joint 0.0031424082  =  22ε/(7+ε)
```

So the measured `(22/7)(S−7)` is the first-order form of the exact `22ε/(7+ε)`.

## 3. Why this is the shape the corpus predicts

Three independent characterisations land on the same object:

* the **AP is the unique minimal-spread globally isolated arrangement**, and Theorem 4.8's constant
  `7` is its reading profile `{1,…,7}` filling the clear band exactly at both ends;
* the **AP's clear set is the odd integers**, protected because odd `R` is a unit mod `8`
  (v11 Theorem 11.3);
* the **AP is the unique profile covering `[1,7] ∪ [9,15]`** (`AP_ISOLATION_v1`).

And the guard structure explains why all three are the same fact: the guards **are** the units, the
cage bars the non-units, and the AP is the arrangement whose readings are exactly `1,…,7` — one
guard per unit, with zero slack at both ends. That zero slack is what makes `S = 7` the boundary:
the arrangement is tight, so any increase in `S` releases the guard it was holding.

## 4. What is proved and what is not

| | |
|---|---|
| a reading on a lower band edge blocks just below | **`[PROVED]`** `guard_blocks_below`, axiom-clean |
| raising a guard moves it into the clear band | **`[PROVED]`** `raising_unguards`, axiom-clean |
| the guard of `R` is the reading `≡ R (mod 8)` | **`[PROVED — in the text]`**, Klein group |
| the AP's uncovered set at `S = 7+ε` is exactly those two intervals, total `22ε/(7+ε)` | **`[VERIFIED — exact, 10 d.p.]`** |
| the AP is the **unique** coverer | `[EMPIRICAL]` — see `AP_ISOLATION_v1` §5 |
| `S > 7` ⟹ uncovered `> 0` for every profile | **not proved** — this is Existence |

The derivation covers the neighbourhood of the AP completely and exactly. What it does not cover is
profiles far from the AP, where uniqueness is still only searched.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
python3 experiments/n8/ap_mechanism_v1.py    # the guard table and the exact uncovered set
```
