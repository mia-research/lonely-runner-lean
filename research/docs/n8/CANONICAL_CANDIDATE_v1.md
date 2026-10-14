# Where the divisor-closed witness is, and why

Method: the 86% mixed class is a **pointer**, not a verdict. Every profile in it clears, with a
small witness. This locates the witness and proves the mechanism that places it.

Lean: `experiments/n8/CanonicalCandidate_v1.lean` (6 theorems, 0 errors; four need only
`[propext, Quot.sound]`). Scripts: `mixed_witness_v1.py`, `Lm_mechanism_v1.py`,
`collider_step_v1.py`, `branchB_rule_v1.py`.

---

## 1. The witness is at the lower edge of the largest modulus

**[VERIFIED — 36,753 mixed profiles, every one with a witness]** Start at `q = L(b_max)` and
walk up:

| | |
|---|---|
| `L(b_max)` itself clears | **36.5%** |
| median walk | **1** |
| mean walk | 1.7 |
| longest walk seen | 54 (profile `[2,56,120,140,840]`) |
| walk shorter than `lcm` of the non-maximal moduli | **100%** |

So the search is not a search. The largest modulus confines `q` to `[L(b_max), U(b_max)]`, and
the remaining moduli are short-period obstacles that are stepped past almost immediately.

## 2. Exactly which moduli block the canonical candidate — **[PROVED]**

Write `b ∣ m`, reading `s = m/b`, `s = 8u + v` with `0 ≤ v < 8`. Then
`L(m) = u*b + ⌈(v*b-1)/8⌉`, so the residue at `b` depends only on `v`:

**[VERIFIED — 13,499 `(m,b)` pairs, `m < 2000`, no exceptions]**

```
    L(m) clears b   ⟺   v ≠ 0   and   ⌈(v*b-1)/8⌉ ≤ ⌊(7b-1)/8⌋
```

Clear rates by `v = s mod 8`: `0` → **0.00%** (1,901 pairs), `1,2,3,4` → **100%**,
`5` → 91.63%, `6` → 85.11%, `7` → 10.56%.

Proved pieces:

* `one_le_L` — `L(b) ≥ 1` for `b ≥ 2`, so residue `0` is never clear.
* `collider_blocked` — a collider (`8 ∣ s`) pins `L(m)` to residue `0`, hence blocks it.
* `small_v_clear` — `1 ≤ v ≤ 4` clears for **every** `b ≥ 2`, with `0 ≤ R < b`.
* `collider_step` — the minimal step at a collider is exactly `L(b)`, landing on the lower edge.

Ceilings and floors are carried as characterising inequalities, so the arithmetic stays inside
`omega` and no division convention is relied on.

## 3. A collider kills the whole `m`-lattice — **[PROVED]**

`collider_kills_lattice`: if `8 ∣ s = m/b` then `m/8 = u*b`, so **every** integer multiple of
`m/8` has residue `0` at `b` and is blocked.

This is why a whole family of candidates fails at once. **[VERIFIED — 20,000 Branch B
profiles]**, eleven explicit formulas:

| candidate | hit rate |
|---|---|
| `L(m)` | **0.00%** |
| `⌈m/4⌉` | **0.00%** |
| `⌈3m/8⌉` | **0.00%** |
| `L(b_max)` | 25.53% |
| `L(m) + 1` | 28.41% |
| `Σ_b L(b)` | 33.14% |
| `L(b_max) + 1` | 44.11% |
| **`L(m) + L(b*)`, `b*` the largest collider** | **59.84%** |

The three zeros are not three failures — they are one theorem. Every `m`-lattice candidate is
killed by any single collider. **The witness cannot be placed at `m`'s scale; it must be placed
at the collider's.** The best formula found is precisely the one that does that, and the
structure of §2 says why: the collider pins the residue to `0`, and `L(b*)` is exactly the step
that reaches the lower edge.

## 4. What is now owed, stated exactly

`L(m) + L(b*)` reaches 59.84% and not 100% because the step `L(b*)` can carry a **non**-collider
modulus `b` past its upper edge. From §2 the residue there is `R_b = ⌈(v_b·b-1)/8⌉`, so the
step is safe exactly when

```
    R_b + L(b*)  ≤  U(b)      for every non-collider b.
```

That is an explicit, checkable, division-free condition in the framework's own objects, and it
is the next thing to prove or to attack at its worst case. It is not a density estimate and not
a bound to be tuned — it either holds for a profile or names the modulus that breaks it.

## 5. Grades

* **[PROVED]** §2 and §3, six theorems, axiom-clean.
* **[VERIFIED]** the walk statistics (§1), the `(m,b)` law (§2), the eleven formulas (§3).
* **[OPEN]** the condition in §4, and with it the mixed-scale class.

Existence at order 8 remains open.
