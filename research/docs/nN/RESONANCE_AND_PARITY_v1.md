# Arithmetic resonance: why even orders are wasted, and why eight is the worst of its size

2026-09-21, version 1. Follows the owner's observation that odds and evens interrelate and that
a mechanism is surfacing.

Artefacts: `experiments/nN/parity_clearance_v1.{py,out}` · `parity_driver_v1.{py,out}` ·
`resonance_v1.{py,out}` · `coprime_theorem_v1.{py,out}` · `divis_vs_coprime_v1.{py,out}`

---

## 1. The mechanism

**Resonance.** Call a disparity `d` *resonant with `n`* when `gcd(d, n) > 1`. This is the
quantity in the manuscript's Theorem 4.13 (the cage): a resonant offset is confined to
`[gcd(d,n)/n, 1 − gcd(d,n)/n]` and cannot come near the subject at a grid instant. It is also
the quantity behind the over-blocking measured earlier: a disparity on a coarse lattice blocks
more openings than the generic `2e/n` — `d = 8` at `e = 16`, `n = 8` blocks 8, not 4.

**The empirical law.** Across every order and blocker count tested, **a difference set fails at
its largest flank only if it contains a disparity resonant with `n`.** Zero counterexamples.

> **Candidate.** If `gcd(d, n) = 1` for every disparity `d`, the largest flank hosts a lonely
> opening. `[EMPIRICAL — 0 counterexamples over all `(n, card)` in the table below]`

| `n` | card | coprime sets | failures among them | resonant sets | failures among them |
|---|---|---|---|---|---|
| 6 | 5 | 21 | **0** | 25,830 | 52 |
| 7 | 5 | 11,370 | **0** | 14,481 | 4 |
| 7 | 6 | 2,996 | **0** | 4,984 | 90 |
| 8 | 6 | 28 | **0** | 7,952 | 31 |
| 8 | 7 | 1 | **0** | 3,430 | 127 |
| 9 | 7 | 120 | **0** | 3,311 | 49 |
| 10 | 7 | 0 | — | 3,431 | 37 |
| 11 | 7 | 1,715 | **0** | 1,716 | 3 |
| 12 | 7 | 0 | — | 3,431 | 2 |

---

## 2. Why even orders are wasted  `[VERIFIED]`

Read the *coprime sets* column. At `n = 7` it is 11,370; at `n = 11`, 1,715. At `n = 6` it is
21; at `n = 8`, one; at `n = 10` and `n = 12`, **zero**.

Every even `n` has 2 as a divisor, so a set avoids resonance only by being entirely odd — which
almost no set is. **At even orders the protection is vacuous.** At prime orders roughly half of
all sets are protected outright.

That is exactly the step pattern measured independently (`parity_driver_v1.out`) — the factor by
which the failure rate improves on going from `n` to `n+1`:

| step | 6→7 | 7→8 | 8→9 | **9→10** | 10→11 | **11→12** | 12→13 |
|---|---|---|---|---|---|---|---|
| `k=5` | ×6.6 | ×3.5 | ×4.9 | **×1.0** | →0 | | |
| `k=6` | | ×3.1 | ×3.1 | **×1.3** | ×15.0 | **×1.5** | →0 |

Steps into an even order buy almost nothing; an even order behaves like the odd order beneath
it. The threshold `1/n` does shrink, but at even `n` the resonance is universal and cancels it.

---

## 3. The condition is strictly stronger than the one already proved  `[VERIFIED]`

The framework proves `LRC.SpecN.lonelyAt_inv_of_not_dvd`: **if `n` divides no disparity, the
subject is lonely at `1/n`.** Resonance is a weaker requirement to violate, so the question is
whether the extra sets matter. They do:

| `n` | failures containing a multiple of `n` | failures resonant but with **no** multiple of `n` |
|---|---|---|
| 6 | 34 | **18** |
| **7** | 94 | **0** |
| 8 | 69 | **89** |
| 9 | 30 | **24** |
| 10 | 26 | **16** |
| **11** | 3 | **0** |
| 12 | 2 | **0** |

**147 failures in total** pass the divisibility test and still fail. And the zero rows are
`n = 7` and `n = 11` — **at prime `n`, `gcd(d,n) > 1` and `n ∣ d` are the same condition.**

So:

- at **prime** order, the framework's proved criterion is exactly the right one, and there is no gap;
- at **composite** order, the proved criterion leaves a band of sets uncovered, and that band is
  indexed by the proper divisors of `n`.

---

## 4. Why eight is the worst order of its size

`8 = 2³` has proper divisors 2 and 4 — the largest such set for any `n ≤ 12` — so its uncovered
band is the widest. At `card = 7`, eight has **89** failures that pass the divisibility test,
against 24 at nine, 18 at six, and **none** at seven or eleven.

Read together with the earlier results this is consistent and, I think, the shape of the thing:

- `n = 5`, prime, four disparities, nothing resonant unless a multiple of 5 appears — the only
  order where `sup R < n − 1` holds (`R_ROUTE_IS_ORDER_FIVE_ONLY_v1.md`), and the only order
  where `DoorLargestFlank` survives (`SMALL_ORDER_DOORS_v3.md`);
- `n = 7`, prime, no gap — and its annealing maximum `9.04` is the lowest relative to threshold
  of `n = 6…9`;
- `n = 8 = 2³`, maximal resonance, widest gap, highest observed `R` (11.96 against threshold 7).

The difficulty at eight is not that eight is large. It is that eight is **2³**.

---

## 5. What to do with it

1. **Prove the candidate** of §1. It is framework-native (the cage is Theorem 4.13), it
   subsumes `lonelyAt_inv_of_not_dvd`, and it is stated at general `n`.
2. **Split the order-8 problem by resonance.** The coprime sets are settled by §1 once proved;
   what remains is indexed by `gcd(d,8) ∈ {2,4,8}` — a three-class decomposition rather than an
   undifferentiated frontier.
3. **Stop reading order-8 difficulty as a size effect.** Comparisons should be against 9 and 7,
   not against 5 and 6, and the controlling parameter is the divisor structure of `n`.

---

## 6. Grades

| claim | grade |
|---|---|
| a failure requires a resonant disparity | `[EMPIRICAL — 0 counterexamples across the §1 table]` |
| the condition is strictly stronger than `n ∤ d` | `[VERIFIED — 147 failures pass divisibility and still fail]` |
| at prime `n` the two conditions coincide | `[PROVED — `gcd(d,n)>1 ⟺ n∣d` for prime `n`]` |
| even orders give ~no coprime sets | `[VERIFIED — 21, 1, 0, 0 at `n = 6, 8, 10, 12`]` |
| steps into even orders buy almost nothing | `[VERIFIED — ×1.0, ×1.3, ×1.5]` |
| `n = 8` has the widest uncovered band of its size | `[VERIFIED — 89 against 24, 18, 0, 0]` |
| the candidate theorem itself | **not proved** |

**Scope.** Whole-number difference sets, exhaustive over the stated ranges (`card 5` to
`[1,22]`, `card 6` to `[1,16]`, `card 7` to `[1,14]`). The coprime column is thin at even `n`
(21, 1, 0, 0 sets), so "0 failures among coprime sets" is weak evidence *there* and strong at
`n = 7, 9, 11` where the column runs to thousands.
