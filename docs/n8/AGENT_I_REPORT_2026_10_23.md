# Agent I report, 2026-10-23: core width lemma and block rules for arbitrary cores

Rules: 5 (no runner stationary: every reading positive, `0 < l`, `0 < t` carried through), 6/7 (counting and covering steps tagged PROVISIONAL in the file headers), 15 (no floats), 16 (new files only), 18 (grades below). Nothing committed, no lakefile or pin touched, `RUNNING_LOG_order8_v1.md` not edited.

Grades: [L] = Lean compiled, axioms exactly `propext, Classical.choice, Quot.sound`. "relative to NativeLRC k" = [L] with that hypothesis explicit. [OBS] = from a script (none used).

## Files created (all new)

In `LonelyRunnerFresh/Fresh/` (compiled with `./check.sh`; scan 0 sorry/native_decide/axiom/admit/unsafe; untagged Prop defs 0):
1. `Fresh/CoreWidthBase.lean`
2. `Fresh/CoreWidthBlocks.lean`
3. `Fresh/CoreWidthNat.lean`

In `LonelyRunnerFresh/bridge/` (NOT in `Fresh/`, so Fresh still imports nothing from the old repo and check.sh's module list is unchanged; compiled by hand, see "Discharge"):
4. `bridge/CoreWidthBridge.lean`
5. `bridge/CoreWidthBridgeSkeleton.lean`
(plus the build artefact `bridge/build/CoreWidthBridge.olean`.)

## Task 1: bridge to the nested statements

Nested form (`LRC/Spec/DoorsN.lean`): `ExistenceAtN n := ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ n - 1 → ∃ s, 0 < s ∧ Lonely n ds s`, with `Lonely n ds s := ∀ d ∈ ds, (n : ℝ)⁻¹ ≤ circDist (d * s)` (`Cascade/Iteration.lean`, namespace `MomentIterationN`), `circDist x = min (fract x) (1 - fract x)`. Positivity of readings and a card bound are the only hypotheses; no ordering. (`lonely_8_real` in `OrderSixEightNativeN.lean` is NOT the order-6 theorem: it is BHK section 8 on 5 speeds with `v 2 ≤ 3 v 0`. The usable ones are below.)

Fresh hypothesis: `CoreWidth.NativeLRC k := ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ k → ∃ t, 0 < t ∧ ∀ d ∈ ds, 1/(k+1) ≤ distInt (d * t)`, tagged `-- STANDING: IMPORTED`. It is exactly `ExistenceAtN (k+1)`.

| k | nested theorem (all `[propext, Classical.choice, Quot.sound]`) | status here |
|---|---|---|
| 1 | trivial | [L] `native_one` from scratch (`t = 1/(2c)`) |
| 2 | `LRC.SpecN.existenceAtN_three` (`OrdersThreeFourN`) | [L] `native_two` from scratch (`t = 1/(a+b)` for `b <= 2a`, else the first `b`-window of width 1/3 reaching `1/(3a)`) |
| 3 | `LRC.SpecN.existenceAtN_four` | bridge only (`nativeLRC_3`) |
| 4 | `LRC.OrderFiveN.existenceAtN_five` (`RealFiveN`) | bridge only |
| 5 | `LRC.OrderSixN.existenceAtN_six` (`RealSixN`) | bridge only |
| 6 | `LRC.OrderSevenNative.existenceAtN_seven` (`OrderSevenNativeN`; also `LRC.OrderSevenN.existenceAtN_seven` in `RealSevenN`) | bridge only |

Discharge without a lakefile edit: `bridge/CoreWidthBridge.lean` imports both trees. Compile by hand:
`LP=$(cd LonelyRunner && lake env printenv LEAN_PATH); LEAN_PATH="<Fresh>/bridge/build:<Fresh>/build:$LP" lean bridge/CoreWidthBridge.lean -o bridge/build/CoreWidthBridge.olean` (then the Skeleton file the same way). Result [L], 12 s: `circDist_eq_distInt`, `nativeLRC_of_existence`, `nativeLRC_3/4/5/6`, `blockRuleNat_one/two/three_discharged` all with standard axioms. Caveat: it loads the nested `.olean` files as they stand on disk (OrderSevenNativeN built 2026-10-19; Order8SkeletonN 2026-09-27); I did not rebuild them or re-run the nested gate.

## Task 2: core width lemma [L]

`CoreWidthBase.lean`:
* `distInt_lipschitz : |distInt x - distInt y| ≤ |x - y|` (was absent from Fresh).
* `core_width (hk : NativeLRC k) (hne : C.Nonempty) (hpos) (hcard : C.card ≤ k) (hc : ∀ d ∈ C, d ≤ c) : ∃ t, 1/(8c) ≤ t - w ∧ ∀ s, |s - t| ≤ w → ∀ d ∈ C, 1/8 ≤ distInt (d * s)` with `w = (1/(k+1) - 1/8)/c`.
* `core_interval`: the same as `∃ l r, 0 < l ∧ r - l = 2w ∧ ∀ s ∈ [l, r], all clear`. The lower end is `>= 1/(8c)` because `1/(k+1) ≤ distInt (d t) ≤ d t ≤ c t`.
* `margin_pos : k ≤ 6 → 0 < 1/(k+1) - 1/8`. No hypothesis `k ≤ 6` is needed by `core_width` itself (empty interval otherwise).
Widths `2w c`: k=6: 1/28; k=5: 1/12; k=4: 3/20 (matches the review table).

## Task 3: block rules [L, relative to NativeLRC]

`CoreWidthBlocks.lean`. Core `C` nonempty, positive, all `<= c`; block `F` with `F.card <= f` (so fewer readings are covered too); conclusion `∃ t > 0, ∀ d ∈ C ∪ F, 1/8 ≤ distInt (d * t)`.

| theorem | hypothesis | core | block | threshold on every `x ∈ F` | derivation |
|---|---|---|---|---|---|
| `block_rule_one` | `NativeLRC 6` | `card <= 6` | `<= 1` | `7 c <= x` | `1/(28c) = 1/(4 (7c))` against `one_clear_in` (new, from `opening_close`, `holds_clear`) |
| `block_rule_two` | `NativeLRC 5` | `card <= 5` | `<= 2` | `12 c <= x` | `1/(12c) = 1/(12c)` against `two_clear_in2` |
| `block_rule_three` | `NativeLRC 4` | `card <= 4` | `<= 3` | `(80/3) c <= x` | `3/(20c) = 4/((80/3)c)` against `three_clear_in_all` |
| `block_rule_three_27` | `NativeLRC 4` | same | same | `27 c <= x` | corollary (`27 > 80/3`) |

Thresholds are exact (equality in the width comparison), as the review predicted: D = 7, 12, 80/3 (so 27).

First isolation and `Lands` (same file): `firstIso_of_lonely` (a positive lonely instant of an arrangement gives `∃ T > 0, FirstIso v k T`, via `exists_dmin`, `exists_fixed_of_lonely`, `bound_le_of_lonely`, `fixed_is_first_isolation`); `lands_of_block`; `block_lands_one/two/three`: for `v` an arrangement, `k` a subject with `disparitySet v k = C ∪ F` and the hypotheses above, `∃ T, 0 < T ∧ FirstIso v k T ∧ ∀ a ∈ disparitySet v k, Lands v k a` (the 7c/12c/(80/3)c thresholds, relative to `NativeLRC 6/5/4`). The first isolation instant exists because the common clear instant is a positive lonely instant; the statements say nothing about WHERE `T` is relative to the core's landing.
Also `distInt_eq_min : distInt x = min (fract x) (1 - fract x)` (the nested `circDist`).

`CoreWidthNat.lean`: `BlockRuleNat f T` is the skeleton's `BlockRule8 f T` with `distInt` for `circDist` (whole-number `C F : Finset ℕ`, `F.card = f`, `C.card + F.card <= 7`, `C.Nonempty`, `T c <= x`). `blockRuleNat_mono` (larger `T` weakens), `blockRuleNat_one : NativeLRC 6 → BlockRuleNat 1 7`, `blockRuleNat_two : NativeLRC 5 → BlockRuleNat 2 12`, `blockRuleNat_three : NativeLRC 4 → BlockRuleNat 3 27`.

## Task 4: comparison with `Order8SkeletonN.lean`

* `BlockRuleNat f T` and the skeleton's `BlockRule8 f T` are the same statement up to `circDist = distInt` (proved in `CoreWidthBridge.circDist_eq_distInt`). `BlockRule8 f T` for sets implies `ArrBlockRule8 f T` for arrangements by taking `C = readingsOf.filter (· ≤ m)`, `F = filter (m < ·)` (disjoint, `C.card + F.card = card <= 7`); I did not formalise that implication, the skeleton's own proof of `lonely8_of_arrangement_holes` does this split by hand.
* f = 1: `BlockRule8 1 9` is already a theorem (`blockRule8_one`); mine gives `T = 7`, so nothing new at `T = 9`.
* f = 2: `BlockRule8 2 9` is already a theorem (`blockRule8_two`); mine needs `T = 12`, weaker than the skeleton's route. Nothing new.
* f = 3: new. `blockRuleNat_three` gives the block of three at `T = 27` for arbitrary cores (so `ArrBlockRule8 3 27` in the sense above). It does NOT give `ArrBlockRule8 3 9`, which stays OWED: ratios between 9 and 27 across a block of three are not covered.
* Skeleton at `T = 27` [L, hand-compiled bridge `CoreWidthBridgeSkeleton.lean`, standard axioms]: `lonely8_of_holes_27 (h3 : BlockRuleNat 3 27) (h : ∀ f, 4 ≤ f → f ≤ 6 → ArrBlockRule8 f 27) (hB : ArrBoundedCovered8 27)` and `lonelyRunnerAt8_of_holes_27 (h4 h5 h6 : ArrBlockRule8 _ 27) (hB : ArrBoundedCovered8 27) : LonelyRunnerAt8`, with `h3` discharged by `blockRuleNat_three_discharged`. So the five named holes at `T = 9` become four at `T = 27`: `ArrBlockRule8 4 27`, `5 27`, `6 27`, `ArrBoundedCovered8 27`.
* Cost on the scale-free side: `ArrBoundedCovered8 T` quantifies over arrangements with NOT `Separated8 T`, i.e. every consecutive reading ratio `< T`. Raising `T` from 9 to 27 enlarges that set (it adds the arrangements whose largest consecutive ratio lies in `[9, 27)`), so `ArrBoundedCovered8 27` implies `ArrBoundedCovered8 9` and is the stronger owed statement. The block holes for f = 4..6 get weaker (hypothesis `27 c <= x` instead of `9 c <= x`). I did not measure how much harder the finite cover becomes; nothing computed about it.

## Not proved / not done
* The `NativeLRC` hypotheses inside `Fresh/` are hypotheses; they are discharged only in the `bridge/` files (outside `Fresh/`, hand-compiled, relying on the nested oleans on disk). `NativeLRC 3..6` is not reproved in Fresh.
* f >= 4: not attempted. With a core of three the width is `1/(4c)`, and the measure argument of `three_clear_in_all` does not extend to four blocked sets (review section 4). No lemma written.
* The review's remark that true constants are about twice the provable ones (so f = 3 near `T = 11`) is [OBS]-only and not touched.
* `ArrBlockRule8 f T` as a statement about `readingsOf`/`Nat.dist` is not proved from `BlockRuleNat f T` in Lean (only argued above); `lonely8_of_holes_27` does the split inline.
* No claim about where the cascade lands inside the core's landing cell; only existence of a first isolation instant and `Lands` at each disparity.
