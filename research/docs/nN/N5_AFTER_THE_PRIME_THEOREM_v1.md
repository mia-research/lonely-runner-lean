# What the prime-order theorem does for n = 5

2026-09-21, version 1. Answers the owner's question directly. Supersedes the position recorded
in `N5_LEAN_STATUS_v1.md` §4 and `OVERLAP_BOUND_v1.md` §4.

Artefacts: `experiments/nN/n5_after_prime_v1.{py,out}` · `n5_residue_v1.{py,out}` ·
`n5_coverage_v1.{py,out}` · Lean in `LRC/Spec/ResonanceN.lean`, `LRC/Spec/FlankFiniteN.lean`

---

## 1. Five is prime, so the theorem applies

`LRC.Resonance.flankWorks_of_prime` needs `n` prime and `n` dividing neither the flank nor any
disparity. At `n = 5` a subject has at most four disparities, and the hypothesis is just: **no
disparity is a multiple of 5**. That case is now **proved**, for every flank, not only the
largest.

---

## 2. Three axiom-clean theorems now cover two thirds of order five

| | theorem | coverage (card 4, `[1,120]`) |
|---|---|---|
| **P1** | `Resonance.flankWorks_of_prime` — no disparity divisible by 5 | 40.54% |
| **P2** | `FlankFinite.clear_at_last_opening` — `d_max ≤ 4·d_min` | 42.41% |
| **P3** | `FlankFinite.four_clears_small` — `d_max ≤ 15`, by `decide`, **no axioms at all** | — |
| | **union P1 ∪ P2 ∪ P3** | **66.10%** |

Before the prime theorem the proved region was P2 alone, **42.4%**. The residue has fallen from
**57.3%** to **33.9%**.

---

## 3. The residue changed character, and that is the important part

The residue is now exactly: **resonant** (some disparity divisible by 5) **and** wide ratio
(`d_max > 4·d_min`) **and** `d_max > 15`.

Within it, measured over 7,627,637 primitive sets to `[1,120]`:

> **the minimum number of working openings is 2 — never 1, never 0.**

That is a different situation from the one recorded earlier. The obstacle in
`OVERLAP_BOUND_v1.md` was the *tight* family — 57 sets with exactly one working opening, where
any margin argument has no room. Those 57 all have `d_max ≤ 15`, so **P3 discharges every one of
them**. Inside the residue there are 29 tight sets and they too are all `≤ 15`, hence also
covered.

So the remaining class is uniformly comfortable: at least two openings work throughout, and the
edge cases are gone. A margin argument now has somewhere to stand, which it did not before.

---

## 4. Why the prime theorem cannot simply be extended to the residue

Its construction takes `s` with `e·s ≡ 1 (mod 5)` and `j = (e·s − 1)/5`, so `5j + 1 = e·s`. For a
disparity `d = 5m` the factor cancels:

```
    5m·(5j+1)/(5e) = m·(5j+1)/e = m·e·s/e ≡ 0   (mod 1)
```

— the residue is exactly `0`, so a 5-multiple sits **on** the subject at that opening. The
construction does not merely fail to cover the resonant sets; the resonant disparity is precisely
what blocks at the `j` it names. A different opening is needed, and the resonant disparity obeys
a different rule there: `5m` is clear iff `m·(5j+1) mod e ∈ [e/5, 4e/5]` — modulus `e`, not `5e`.

That reduction (a 5-multiple reads at `m` against modulus `e`) is the structure the residue has
and the non-resonant case does not. It has not been exploited.

---

## 5. Position

| claim | grade |
|---|---|
| P1, P2, P3 | `[PROVED — axiom-clean; P3 depends on no axioms]` |
| union covers 66.1% of order five | `[VERIFIED — exhaustive to [1,120]]` |
| residue has ≥ 2 working openings throughout | `[EMPIRICAL — 7,627,637 sets; 0 with fewer]` |
| every tight set has `d_max ≤ 15`, hence is covered by P3 | `[VERIFIED — exhaustive]` |
| order five, largest flank, in general | **not proved** |

**What is left, precisely.** Sets that are resonant, of wide ratio, with `d_max > 15`. Every one
tested has at least two working openings. The tools now available on them are the residue
reduction of §4 and the gap criterion (`exists_lonely_flankOpening_of_gap`), neither yet applied.

**Scope.** Whole-number difference sets of card 4, exhaustive to `[1,120]`; by
`lonely_flank_smul_iff` this covers all rational sets of that shape. Irrational ratios are
untouched.
