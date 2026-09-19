# Are the open frontiers actually open? — an audit, and the categories

Every frontier checked against what is proved on disk, asking of each: is this open because the
mathematics is open, or because something was imported, misphrased, or assumed?

**Result: of the four frontiers, one is closed, one is genuinely open (and reduced), and two
were never frontiers.**

---

## 1. Middle band `8 ≤ b ≤ 27` — **CLOSED**, and it was held open by an imported reason

The `b ≥ 28` threshold came from an order-**7** route, whose margin is `1/7 − 1/8 = 1/56`,
forcing `1/(2b) ≤ 1/56`. But the divisor-closed reduction (`Rescale.divisor_reduces`) leaves
**five** constraints, not six — and five constraints is an order-**6** question, margin
`1/6 − 1/8 = 1/24`. Order 6 is proved in this tree (`intLRC_six`, in-house, axiom-clean).

Keeping integrality of the residue then gives `b ≥ 10`, not 15 (`DivisorOrder6.clear_of_order6`).
The residual `{8,9}` was likewise not hard: for `2 ≤ b ≤ 9` the window is `[1, U(b)]`, so
clearing is pure **non-divisibility** (`ReducedOpen.small_clear_iff`), and `q = 1` clears the
whole range at once (`SmallModuli.clear_one`).

**The band was held open by using order 7 where the surviving constraint count licenses order 6.**
Closed per modulus. Whether one `q` meets all moduli at once is §2, not this.

## 2. Mixed quotient profiles — **GENUINELY OPEN, reduced**; was held open by a hypothesis of mine

`clear_of_order6` is a **per-modulus** theorem. `profile_clear_of_order6` demanded `b ≥ 10` of
*every* modulus, excluding every mixed profile by fiat — a hypothesis the per-modulus theorem
never needed. Removing it (`Derestricted.profile_clear_mixed`) took reach from **13.45%** to
**100.00%** of 8,000 sampled profiles.

What remains is real. The obligation is `ReducedOpen.ReducedWitness`:

> find `q` clearing every modulus `≥ 10`, subject only to `b ∤ q` at each modulus `b ≤ 7`, and
> `b ∤ q` with `b ∤ (q+1)` at each `b ∈ {8,9}`.

The identified obstruction: order-6 supplies a real witness with margin `1/6` at the moduli
`≥ 10`, and rounding it to an integer can land on a forbidden small residue. For `b = 2` a
margin `> 1/4` would be needed to force the parity, and no order-6 bound supplies it. **This is
the only genuinely open mathematical region.**

## 3. Rational readings — **NOT A SEPARATE FRONTIER**

`RATIONAL_FRONTIER_v1.md` establishes, verified on 200,000 seven-element speed sets with 0
mismatches:

> **Integer readings ⟺ the reduced integer speed set contains `1`.
> The rational-reading frontier is exactly: speed sets with no unit speed.**

It is the same mathematics. Of the theorems the work rests on, exactly one mentions the unit and
fails without it — `BlockerCount.unit_never_blocks` — and the cost is that the blocker count
rises from `n − 3` to `n − 2` (a minimum speed `> 1` blocks 21.94% of candidates, measured over
10.5M candidate/speed pairs). Everything else transfers unchanged, including the whole reflection
apparatus.

**A phrasing defect to correct.** `EXISTENCE_MAP_v5` §3 reads "Costs exactly one theorem,
**`unit_never_blocks`**", which reads as though the theorem is owed. It is **proved and
axiom-clean** — `experiments/n8/BlockerCount_v1.lean:40`, witness line 38 of
`v12_new_axioms_v1.out`. The cost is that the rational case cannot *use* it. This has already
misled one automated reader, which recorded the theorem as "absent from disk … still owed".
**`EXISTENCE_MAP_v6` is owed to fix the wording.**

## 4. `R < 16` / `DoorCapped`, and flank shadowing / `DoorFlank` — **NOT FRONTIERS**

`LRC.Spec.doors_agree` (axiom-clean) proves

```
    DoorFlank v k ↔ DoorArrives v k ↔ DoorCapped v k ↔ DoorFAM v k ↔ LonelyForSubject v k
```

per arrangement and per subject. These are **the same obligation in four vocabularies**, not four
regions. Closing any one closes the conjecture; leaving three "open" alongside the one you are
working on double-counts. They are **routes**, and belong in a different list from the profile
classes, which genuinely partition the instances.

## 5. Real / irrational speeds — **not where the difficulty is**

`LonelyRunnerAt8` is already stated over `v : Fin 8 → ℝ`, and the doors are proved equivalent to
it over `ℝ`. `Spec/Target.lean:246–251` records the position in the tree's own words: the real
case is *"mathematically comfortable (margins 1.6× to 3.7× once any ratio is irrational) but
expensive to formalise, since it needs a dense-orbit theorem on the `k`-torus that mathlib does
not carry. It would **not touch the difficulty: that sits entirely in the commensurable case**."*

So this is a **formalisation cost against mathlib**, not an open mathematical frontier. Listing
it beside Branch B overstates what is unknown.

## 6. One claim resting on an artifact that is not there

`class_killer_int` — cited as settling off-lattice free differences — exists in
`experiments/n8/manuscript_map_v9_2.json` and in two script comments, one of which says
"formalised via `class_killer_int`". **There is no such Lean declaration anywhere in the repo.**
It is a manuscript-level result at most; the word "formalised" in that comment is wrong.

---

## The categories, announced

| | category | status |
|---|---|---|
| **1** | **Commensurable, reduced speed set contains `1`** (integer readings) | |
| 1a | — no collider: `8 ∤ s` for every reading | **PROVED, all magnitudes** — `Guard.odd_clear_of_not_dvd`, `spine_all_or_nothing` (`[propext]` only). Every odd unit clears at the first spine instant |
| 1b | — collider present (`8 ∣ s` for some reading): **Branch B** | **OPEN.** The only genuinely open region. Divisor-closed sub-case reduced to `ReducedOpen.ReducedWitness` |
| **2** | **Commensurable, no unit speed** (rational readings) | **The same question.** Machinery transfers entire but for `unit_never_blocks`; blocker count `n−3 → n−2` |
| **3** | **Incommensurable** (real / irrational) | **Not a mathematical frontier.** Margins 1.6×–3.7×; the gap is a mathlib dense-orbit theorem |
| **4** | **The doors** — `DoorCapped` (`R < 16`), `DoorFlank`, `DoorArrives`, `DoorFAM` | **Not regions.** Proved mutually equivalent; these are four routes into 1b/2 |

**What moved.** Four frontiers became: one closed (the middle band, by an imported-reason
removal), one genuinely open and reduced (Branch B and its no-unit twin), one formalisation
cost, and one set of equivalent routes that should never have been counted as regions.

Existence at order 8 remains open, and now names exactly one region.
