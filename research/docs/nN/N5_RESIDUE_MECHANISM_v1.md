# The n = 5 residue: map, rules, mechanism, and how far the proof reaches

2026-09-21, version 1. Follows `N5_RESIDUE_MAP_v1.md`, carried through to the mechanism.

Artefacts: `experiments/nN/n5_map2d_v1.{py,out}` · `n5_residue_bound_v1.{py,out}` ·
`n5_exceptions_v1.{py,out}` · `n5_selfsimilar_v1.{py,out}`

---

## 1. Map

Residue = some **non-flank** disparity divisible by 5, wide ratio, `d_max > 15`. **27.4%** of
order five. Exhaustive over primitive 4-subsets to `[1,80]` (397,091 sets):

| | |
|---|---|
| exactly one non-flank 5-multiple | 81.1% |
| two | 17.9% |
| three | 0.97% |
| minimum working openings | **2** |
| sets with ≤ 2 openings | **82** |

---

## 2. Rules

**Rule 1 — the hard offset.** In the family `(1, 4, 5m, e)` the minimum over `e` sits at
`e = 5m + 2`, i.e. `e ≡ 2 (mod 5)` — the 5-multiple immediately below the flank — and the
minimum count **grows linearly in `m`**: 2, 3, 4, 5, 6, 6, 6, 8, 9, 9, 10, 11, 11, 12, 13, 14, 15
for `m = 3…19`. The hard cases are the **small** ones.

**Rule 2 — the low-opening sets are bounded, and the bound is stable.**

| ≤ T openings | 2 | 3 | 4 | 5 |
|---|---|---|---|---|
| max `d_max` | **33** | **37** | 53 | 54 |
| unchanged from | `[1,40]` | `[1,40]` | `[1,60]` | `[1,60]` |

Checked to `[1,80]`. So the residue splits as: a finite check below 54, and a margin argument
(≥ 6 openings) above it.

**Rule 3 — the exceptions are concentrated.** Sets with **three** inner 5-multiples are
**13.85× over-represented** among the low-opening sets: 13.41% of them, against 0.97% of the
residue.

---

## 3. Mechanism: the residue contains a smaller copy of itself  `[VERIFIED — exact]`

Rule 3 points at the sets whose **every** non-flank disparity is a multiple of 5. There the
factor cancels in all of them at once, and

> **#openings of `(5m₁, 5m₂, 5m₃, e)` = #{ `r ∈ [0,e)` : `mᵢ·r mod e ∈ [e/5, 4e/5]` for all `i` }**

Verified on all 3,846 such sets to `[1,80]`: **0 mismatches**.

The band is *identical* — `[1/5, 4/5]` of the modulus — only the modulus drops from `5e` to `e`,
and `r` is unconstrained where `a` had to be `≡ 1 (mod 5)`. So the residue is **self-similar**:
the same problem, one scale down. That is why the three-multiple sets are the hard core — they
are the residue composed with itself, and the difficulty compounds.

This also explains Rule 1. With `5m` adjacent to `e`, `m·r mod e` advances nearly in step with
`r`, so the reduced band and the outer band lock together instead of averaging out.

---

## 4. Proof route, and exactly where it stops

The reduced problem asks for a **rational** point `r/e` at which three runners `mᵢ` are all at
circle distance `≥ 1/5`. Two proved tools meet here:

* **`intLRC_four`** (axiom-clean in this tree) gives a **real** `t` with distance `≥ 1/4` for
  three speeds;
* **`exists_lonely_flankOpening_of_gap`** (proved, `FlankFiniteN.lean`) converts a lonely window
  wider than `1/e` into a lattice point.

Staying above `1/5` holds on a window of width `2(1/4 − 1/5)/m₃ = 1/(10·m₃)`, so the route
closes when **`e > 10·m₃`**.

What the difference set gives for free is `5·m₃ < e`, i.e. **`e > 5·m₃`**.

> **The route is short by exactly a factor of two.**

| | sets | share |
|---|---|---|
| `e > 10·m₃` — route closes | 504 | 13.1% |
| `5·m₃ < e ≤ 10·m₃` — the gap | 3,342 | 86.9% |

And in that gap the margin is comfortable: minimum **2** openings, only **12** sets with ≤ 3, all
with `d_max ≤ 33` — inside Rule 2's bound.

---

## 5. What would close it

1. **A better floor than `1/4` for three speeds in this regime.** `1/4` is tight only at
   `(1,2,3)`; if the reduced triples `(m₁,m₂,m₃)` arising here admit `≥ 1/4 + 1/20` the factor
   of two disappears. Untested.
2. **A sharper window.** The window `1/(10 m₃)` uses the worst case; the lonely set of three
   runners is a union of intervals and its **largest** interval is what matters.
3. **Finite check plus margin.** Rule 2 bounds the low-opening sets by `d_max ≤ 54`; above that
   there are ≥ 6 openings. `four_clears_small` already covers `d_max ≤ 15` by `decide`; extending
   that check to 54 is mechanical but heavier.

---

## 6. Grades

| claim | grade |
|---|---|
| the self-similar reduction | `[VERIFIED — exact, 0 mismatches on 3,846 sets]` |
| low-opening bounds 33 / 37 / 53 / 54, stable | `[VERIFIED — exhaustive to [1,80]]` |
| three-multiple sets 13.85× enriched among the low | `[VERIFIED — exhaustive]` |
| Rule 1, minimum at `e ≡ 2 (mod 5)`, count linear in `m` | `[EMPIRICAL — the `(1,4,5m,e)` family]` |
| the gap-criterion route closes for `e > 10·m₃` | `[PROVED — `intLRC_four` + `exists_lonely_flankOpening_of_gap`]` |
| it covers 13.1% of the self-similar family | `[VERIFIED]` |
| the residue itself | **not proved** |

**Scope.** Whole-number difference sets of card 4, exhaustive to `[1,80]`. The `intLRC_four`
step imports the analytical line, so any use of §4 in a framework-native argument must be
flagged as such — it is offered here as a route, not as part of the framework's own chain.
