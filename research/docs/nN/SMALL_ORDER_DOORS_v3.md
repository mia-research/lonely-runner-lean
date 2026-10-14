# The n=8 framework at every order — what generalises, and what does not

2026-09-20, version 3. Supersedes v2 (same session). v1 predated the `n = 5` sweeps; v2 covered
the doors only. v3 covers the **whole** `n = 8` Spec apparatus, ported and checked, and reports
the order-dependent content — which is the part with any content in it.

Owner's instruction: *"Build everything that n=8 has so we know if everything generalises and
if not what, because that will be very important."*

Artefacts:
`LonelyRunner/LRC/Spec/DoorsN.lean` (95 declarations, builds, no `sorry`)
`experiments/n8/doorsN_full_check_v1.lean` / `.out` (105 axiom checks)
`experiments/nN/` — `n5_four_diff_v1`, `n5_movecount_v1`, `n5_control_v1`, `n5_witness_v1`,
`whatfails_v1`, `doorfirstlap_nN_v1`, `doorfirstlap_deep_v1`, `doorfirstlap_ratio_v1`,
`tau_exhaustive_v1`, `flankrank_exhaustive_v1`, `largestflank_v1`, `largestflank_audit_v1`,
`largestflank_rate_v1`, `cx_shape_v1`, `cx_profile_v1`, `n5_largestflank_exhaustive_v1`,
`n5_margin_v1`, `n5_tight_v2` (each with its `.out`)

**RING-FENCE.** `LRC/Construction8/`, `LRC/Spec/Target.lean` and `LRC/Spec/Doors.lean` are
untouched. `DoorsN.lean` is additive, imports `Doors.lean`, and lives in namespace `LRC.SpecN`,
so the cascade gate's check [4] keeps its meaning.

---

## 1. The answer

**Every theorem generalises. Nothing failed to port.** All 93 declaration names of
`Cascade/Arrangement.lean` + `Spec/Target.lean` + `Spec/Doors.lean` have a general-`n`
counterpart; 105 of 105 axiom checks return `[propext, Classical.choice, Quot.sound]`.

The order-dependence is entirely in the **refuted and quantitative** content. That is not a
coincidence: what is proved is structural (facts about the cascade construction, which does not
know `n`), and what is refuted is quantitative (a cap, a rank), and quantities scale with `n`.

> **The single most valuable consequence.** `DoorLargestFlank` is `[REFUTED]` at `n = 8` — and
> at `n = 5` it has **zero failures in 172,352,957 exhaustive primitive difference sets**, with
> a **bounded** tight family. It is a candidate theorem, and the chain it feeds is already
> proved, so it would close order 5 natively. §6.

---

## 2. What was built  `[PROVED]`

`LRC/Spec/DoorsN.lean`, `variable {n : ℕ} [Fact (2 ≤ n)]`, with `Fin 8 → Fin n`,
`(8:ℝ)⁻¹ → (n:ℝ)⁻¹`, `ds.card ≤ 7 → ds.card ≤ n - 1`, `(8:ℤ) → (n:ℤ)`, `1/(8m) → 1/(nm)`:

| layer | n=8 source | ported |
|---|---|---|
| arrangement (`sep`, `LonelyAt`, `diffSet`, gaps, named instants, flank equivalences) | `Cascade/Arrangement.lean`, 34 | all |
| target (`ExistenceAtN`, cascade/flank/congruence forms, `CascadeCapped`, FAM, `LonelyRunnerAtN`) | `Spec/Target.lean`, 26 | all |
| doors (1–5, `doors_agree`, `blockDegree`, both refuted doors) | `Spec/Doors.lean`, 34 | all |

Object-level check (not a token count — a name-by-name `comm` of the declaration lists):
**0 names present at `n = 8` and missing at general `n`.** Two additions, `diffSet_card_le`
and `exists_lonely_of_card_le_four`.

Only three things needed any thought, all mechanical: `others_nonempty` was `by simp` at a
literal `Fin 8` and needs `Fact.out` at variable `n`; `four_diffs_stop_ge_six` lives in
namespace `FourDifferencesSix`; and `sep` is definitionally the conjecture's separation, so the
`rw [← sep_eq]` steps are unnecessary. It compiled otherwise unchanged.

**Why it was free.** Every step of the `n = 8` proofs already supplied `8` as an *argument* to a
lemma stated for a variable `n` — `lonely_iff_run_ends (n := 8)`, `exists_fixed_of_capped (n := 8)`,
`iterate_stable (n := 8)`, `move_eq_self_or_opening (n := 8)`, `lonely_iff_exists_flank (n := 8)`,
`clear_at_int_flank_iff_emod (n := 8)`, `circDist_int_div (n := 8)`. `MomentIterationN` and
`Flanks` were generic throughout. The literal `8` only ever entered at `LRC/Spec`.

---

## 3. Order-dependent item 1 — the excess case  `[PROVED — arithmetic on cited hypotheses]`

`ExistenceAtN` quantifies over any `ds` with `card ≤ n − 1`, but an arrangement cannot produce
every such set: a value `d` occurs as `|v i − v k|` for at most two runners (`v k ± d`), so a
realised set has `2·card ≥ n − 1`, i.e. `card ≥ ⌈(n−1)/2⌉`. The **excess** is `card < ⌈(n−1)/2⌉`.

At `n = 8` the excess is `card ≤ 3`, and `exists_lonely_of_card_le_three` settles it — that is
the manuscript's "the difference-set form is the conjecture plus a case already settled".

The theorem ports (it needs only `4 ≤ n`). **Its role does not.**

| `n` | excess `card ≤` | covering theorem | |
|---|---|---|---|
| 5 | 1 | `two_diffs` (n≥3) | covered |
| 6, 7 | 2 | `two_diffs` (n≥3) | covered |
| 8, 9 | 3 | `three_diffs` (n≥4) | covered |
| 10, 11 | 4 | `four_diffs` (n≥6) | covered |
| **12** | **5** | **none** | **first uncovered** |
| 13+ | ≥5 | none | uncovered |

`stops_slowest_recursion` needs `2^(k−1) ≤ n`, so at `k = 5` it needs `n ≥ 16`. From `n = 12` the
difference-set form is **strictly wider than the conjecture by an unsettled case**, and the
manuscript's remark stops being true.

---

## 4. Order-dependent item 2 — door 5's constant  `[VERIFIED — exhaustive]`

`DoorThreeLargest` says the lonely opening sits at one of the subject's **three** largest
disparities. The `Prop` ports; the constant 3 is `n = 8`'s number.

Best flank rank from the large end, exhaustive over primitive sets
(`flankrank_exhaustive_v1.out`):

| order | range | sets | worst rank | distribution |
|---|---|---|---|---|
| 5 | [1,60] | 455,041 | **1** | {1: 455041} |
| 6 | [1,30] | 139,246 | **2** | {1: 139186, 2: 60} |
| 7 | [1,23] | 100,478 | **2** | {1: 100284, 2: 194} |
| 8 | [1,20] | 77,400 | **3** | {1: 76734, 2: 637, 3: 29} |

Control: the `n = 8` run reproduces rank 3 as the worst, matching the record.

---

## 5. Order-dependent item 3 — `DoorFirstLap`  `[UNDETERMINED at 5, 6, 7 — say so]`

`[REFUTED]` at `n = 8` by `τ = e·t = 2401/1872 > 1` on `{49,205,234,256,286,323,366}`.
**Reproduced exactly** by this harness (`doorfirstlap_nN_v1.out`), 28 moves.

**Random search is not a usable instrument here, at any order.** It fails to find the known
`n = 8` witness across ~160,000 sets per order in three different regimes — wide random
(39,696), by cascade depth (11,931), and in the ratio band just above `n − 1` (59,507). A search
that cannot find the positive it is known to be looking for licenses no null anywhere, so those
runs are void and are **not** reported as evidence that `DoorFirstLap` holds at 5, 6, 7.

What *is* measurable is the quantity whose instability refuted it. Exhaustive max `τ`
(`tau_exhaustive_v1.out`); the `n = 8` row reproduces the record exactly (170,213 sets,
`33/56` at `(2,6,8,9,11,14,15)`, then `17/24` at [1,24]):

| order | max τ, by range | still climbing |
|---|---|---|
| 5 | 22/35 → 77/120 → 121/185 → 33/50 = 0.660 at [1,70] | yes |
| 6 | 19/28 → 25/33 → 125/162 → 25/31 = 0.806 at [1,34] | yes |
| 7 | 15/28 → 33/56 → 116/161 = 0.721 at [1,25] | yes |
| 8 | 33/56 (stable [1,18]–[1,22]) → 17/24 at [1,24] | yes — **and refuted at 1.28** |

The same instability that refuted `n = 8` is present at 5, 6 and 7. `n = 8` also sat flat at
0.589 across three ranges before climbing, so flatness is not evidence of a cap. **Status:
open at 5, 6, 7. No witness exhibited, so not refuted; no cap shown, so not held.**

---

## 6. Order-dependent item 4 — `DoorLargestFlank`, and the prize  `[the main finding]`

`DoorLargestFlank`: the **largest** disparity hosts a lonely opening. `[REFUTED]` at `n = 8` by
`(2,3,5,7,8,13,16)` — reproduced: no lonely opening at flank 16, works at flank 13 lap 1.

### 6.1 The test is sound

Three independent checks (`largestflank_audit_v1.out`, `largestflank_rate_v1.out`):

- **Periodicity.** `flankOpening(e,j) = (j+1/n)/e`; the reading for `d` is `d(j+1/n)/e`, and
  `j ↦ j+e` adds the integer `d`. Period `e`, so searching `j ∈ [0,e)` is complete. Verified.
- **Not truncation.** Every reported failure at `n = 6, 7, 8` still fails with `j` searched to
  `50e`. **0 spurious.** (And under-searching `j` can only *add* failures, so the `n = 5`
  zero-failure result is immune to this direction of error.)
- **Rate matches the record.** Pooled over the four ranges the record used ([1,20], [1,30],
  [1,45], [1,70]), the largest flank works **99.734%** against the record's **99.76%**. The
  higher rates in small-range exhaustive sweeps are a denser population, and the rate falls
  monotonically with range.
- **Integer vs `Fraction`** implementations agree on 3,000 `n = 5` sets, 0 mismatches.

*(An earlier version of the audit reported inflated `n = 8` rates; it had reused the `n = 6`
threshold on 7-element sets. Corrected in `largestflank_rate_v1`.)*

### 6.2 What the counterexamples look like  `[VERIFIED — exhaustive]`

`cx_profile_v1.out`, exhaustive:

| order | failures | `d_min/d_max` max | `1/(n−1)` | failures **inside** `d_max ≤ (n−1)d_min` |
|---|---|---|---|---|
| 6 [1,34] | 62 | 0.18750 | 0.20000 | **0** |
| 7 [1,26] | 219 | 0.15789 | 0.16667 | **0** |
| 8 [1,22] | 1,046 | 0.13636 | 0.14286 | **0** |

**Every counterexample at every order lies strictly outside the ratio condition.** A failure
needs `d_max > (n−1)·d_min` — the exact hypothesis Theorem 4.8 settles.

### 6.3 `n = 5`  `[EMPIRICAL — exhaustive to [1,260], zero counterexamples]`

Integer form used throughout (fast, and equal to the `Fraction` form): the largest flank `e`
hosts a lonely opening iff

```
∃ j ∈ [0, e) :  ∀ d ∈ ds,   d·(n j + 1)  mod  n e   ∈  [e, (n−1)e]
```

Exhaustive over primitive 4-subsets, both regions counted separately so the §6.2 split is a
reported observation and not a filter (`n5_largestflank_exhaustive_v1.out`):

| range | inside ratio condition | outside | failures |
|---|---|---|---|
| [1,120] | 3,235,029 | 4,392,608 | **0** |
| [1,260] | 72,887,168 | 99,465,789 | **0** |

**172,352,957 sets, zero failures.**

### 6.4 And the tight family is BOUNDED — which is why this is proof-shaped

Counting the *working* openings at the largest flank (`n5_margin_v1.out`, `n5_tight_v2.out`):

| order | sets with **0** working | sets with exactly **1** | behaviour as range grows |
|---|---|---|---|
| 5 [1,60] | 0 | 57 | **constant** |
| 5 [1,90] | 0 | 57 | **constant** |
| 5 [1,120] | 0 | 57 | **constant** |
| 5 [1,200] | 0 | **57** | **constant** |
| 6 [1,26] | 55 | 655 | grows |
| 7 [1,22] | 189 | 2,044 | grows |
| 8 [1,18] | 414 | 3,008 | grows |

At `n = 5` the tight sets are **exactly 57, and every one has `d_max ≤ 15`** — the family is
finite and bounded, stable from [1,60] through [1,200]. Everything with `d_max > 15` has **two
or more** working openings. At `n = 6, 7, 8` the tight count grows without bound.

That is the shape of a provable statement: a finite check on `d_max ≤ 15`, and a margin
argument (≥ 2 openings) for the rest. The full 57 are listed in `n5_tight_v2.out`; they begin
`(1,2,3,4) j=3`, `(1,2,3,5) j=1`, `(1,2,3,6) j=1`, and end `(7,9,10,12) j=11`.

### 6.5 Why this would close order 5

The chain is already built and proved at every `n`:

```
DoorLargestFlank  →  DoorThreeLargest  →  LonelyForSubject  →  LonelyRunnerAtN n
   doorThreeLargest_of_doorLargestFlank
                        lonelyForSubject_of_threeLargest
                                               (doorFlank_iff / doors_agree)
```

So `DoorLargestFlank` at `n = 5` **closes order 5 inside the framework** — no `intLRC` import,
no dependence on the `sorry`'d real-speeds reduction, and it sidesteps the termination diagonal
entirely (§7), because it never iterates.

**Real difference sets.** The sweeps cover integer sets, hence by scale-invariance all rational
ones. The irrational case has framework machinery already, generic and applicable at `n = 5`:
`Flanks.off_lattice_of_irrational_ratio` and `Flanks.lonely_opening_of_free_off_lattice`
(hypothesis `4 ≤ n`), which reduce a flank with an off-lattice ratio to a finite lattice check.
Assembling them is work and is not claimed done.

---

## 7. Carried over from v2 — termination

Unchanged and still the other frontier. Closing order `n` natively by iteration needs the
diagonal `k = n − 1` at that `n`; it is closed at 3 and 4 and **open for every `n ≥ 5`**
(`2^(n−2) ≤ n` fails from `n = 5`). At `(k=4, n=5)` the cascade arrives on everything tested
(~530k sets) but the move count is **unbounded** (1,283 at scale 10^10 against a proved 7 for
every set at `n ≥ 6`), so the `n ≥ 6` constant-bound *shape* cannot be the `n = 5` statement —
it must be existential, i.e. `DoorArrives`. Smallest witness exceeding the `n ≥ 6` constant:
`(1,13,15,28)`, 8 moves, fixed point `26/75`, with `d = 15` at exactly `1/5`.

§6 matters partly because it **avoids** this: the largest-flank route has no iteration in it.

---

## 8. Grades

| claim | grade |
|---|---|
| all 93 `n = 8` declarations ported; 105/105 axiom-clean, no `sorry` | `[PROVED — doorsN_full_check_v1.out]` |
| name-by-name parity with the `n = 8` files | `[VERIFIED — comm of declaration lists, 0 missing]` |
| excess case first uncovered at `n = 12` | `[PROVED — arithmetic on cited hypotheses]` |
| door 5's worst rank is 1, 2, 2, 3 at `n = 5,6,7,8` | `[VERIFIED — exhaustive]` |
| `DoorLargestFlank` refuted at 6, 7, 8 | `[VERIFIED — exhaustive; n=8 reproduces the record]` |
| every counterexample has `d_max > (n−1)d_min` | `[VERIFIED — exhaustive, 0 inside at 6, 7, 8]` |
| `DoorLargestFlank` at `n = 5`: no counterexample | `[EMPIRICAL — 172,352,957 exhaustive primitive sets to [1,260]; integer sets only; NOT a proof]` |
| the `n = 5` tight family is 57 sets, all `d_max ≤ 15` | `[VERIFIED — exhaustive to [1,200], stable from [1,60]]` |
| `DoorFirstLap` at 5, 6, 7 | **undetermined** — random search cannot find the known `n = 8` witness, so no null is licensed |
| max `τ` unstable at every order | `[VERIFIED — exhaustive; `n = 8` reproduces 33/56 and 17/24]` |
| termination diagonal open for every `n ≥ 5` | `[PROVED — arithmetic on cited hypotheses]` |

**Scope of the negatives.** "No counterexample at `n = 5`" is bounded to integer (hence
rational) difference sets of card 4, exhaustive to `d_max ≤ 260`, with the opening search proved
complete by periodicity. It is not a proof and does not cover irrational ratios or collapsed
sets of card 1–3 (those are covered by `two_diffs`/`three_diffs` for *existence*, but the
largest-flank property on them has not been swept here).

---

## 9. What to do next

1. **Prove `DoorLargestFlank` at `n = 5`.** Finite check on `d_max ≤ 15` (57 tight sets plus the
   rest of that range), margin argument above it. Closes order 5 natively. Highest value.
2. **Re-measure door 5's constant** per order before any statement uses "three".
3. **Settle `DoorFirstLap` at 5, 6, 7** with a directed construction, not sampling — the `n = 8`
   witness came from an adversarial arrangement, and no sampler has ever found it.
4. **`n = 12`** is where the excess case opens up; the manuscript's remark needs an `n ≤ 11`
   qualifier if it is ever stated at general `n`.
