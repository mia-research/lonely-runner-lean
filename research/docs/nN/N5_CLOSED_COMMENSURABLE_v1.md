# Order five, closed for every commensurable arrangement

2026-09-21, version 1. Supersedes nothing; it is the first closure result at order five in the
framework's own objects.

Artefacts: `LonelyRunner/LRC/Spec/FiveInt.lean` · `experiments/n8/fiveint_axioms_v1.{lean,out}`

**RING-FENCE.** Additive. `Construction8/`, `Spec/Target.lean`, `Spec/Doors.lean` untouched;
`FiveInt.lean` lives in namespace `LRC.FiveInt` and the cascade gate is unaffected.

---

## 1. What is proved  `[PROVED — axiom-clean, no `sorry`, no `native_decide`]`

For every injective `v : Fin 5 → ℤ` and every subject `k`:

| declaration | statement |
|---|---|
| `lonelyAtFive_int` | some `t > 0` has every other runner at circle distance `≥ 1/5` |
| `lonelyForSubject_five_int` | `LRC.SpecN.LonelyForSubject` holds |
| `doors_five_int` | **all four doors** hold — flank, arrives, capped, FAM |
| `cascade_arrives_five_int` | the cascade reaches a fixed point |

and, without integrality of the speeds:

| `lonelyForSubject_five_commensurable` | if the subject's disparities are all integer multiples of one positive real `c`, the subject has a lonely instant |

All axioms `[propext, Classical.choice, Quot.sound]`.

Because `LRC.SpecN.doors_agree` is an **equivalence**, `doors_five_int` is not a weaker
statement than the obligation — it is the obligation, in four wordings. In particular the
framework's Existence statement at order five (*the cascade arrives*) is **discharged** for
these arrangements, rather than left equivalent to an open conjecture as it is at `n = 8`.

---

## 2. Why this route, and what it costs

`DoorLargestFlank` at `n = 5` would close order five **natively**, with no import. It is
unproved, and `docs/nN/OVERLAP_BOUND_v1.md` measures three routes to it shut: counting cannot
work (blocking capacity ≥ 1 for 1,472,573 of 1,473,833 sets); a finite cover by named band
instances cannot work (the required opening index is unbounded from both ends — `k ≤ 30` misses
636 of 455,041, and from the top the worst `r` grows with the range); and the LRC floor for
three speeds reaches 0.03%.

So this file uses `intLRC_five` as a **tool** while the target stays native — the obligation is
`LRC.SpecN.LonelyAt` on an arrangement, not a difference set, with nothing pinned at `0`. That
is what the author's 2026-09-15 ruling permits: *tools are fine, targets and statements are what
must stay native.*

---

## 3. The bridge, and why one was needed

`intLRC_five` is stated for a **strictly monotone** `speeds : Fin 4 → ℕ` with `gcd = 1`. A
subject of a five-runner arrangement presents an **unordered `Finset`** of **at most** four
disparities whose gcd need not be one. Three mismatches, each closed here:

| mismatch | fix |
|---|---|
| fewer than four disparities (`diffSet` collapses when two runners sit symmetrically about the subject) | `padTo` — pad above the maximum; the witness restricts to a subset, and padding cannot lower the gcd below 1 |
| unordered `Finset` vs `StrictMono Fin 4 → ℕ` | `Finset.orderIsoOfFin`, with `oif_strictMono` / `oif_image` / `oif_gcd` transferring monotonicity, range and gcd |
| gcd need not be 1 | divide by `g = S.gcd id` (`Finset.gcd_div_id_eq_one`), and scale the witness `t ↦ t/g` |

Plus: `intLRC` yields some `t`, not a positive one. `t ≠ 0` because `circDist (d·0) = 0 < 1/5`,
and `circDist` is even (`Flanks.circDist_neg`), so `|t|` serves.

This bridge did not previously exist anywhere in the tree — a grep of `Cascade/`, `Spec/` and
`ConstructionN/` for `intLRC` found nothing.

---

## 4. What is NOT proved

**`LonelyRunnerAtN 5` over the reals does not follow from anything here.** The gap is the
reduction from real to whole-number speeds, `Theorem121_Main.theorem121_LRC_real`, which is
**`sorry`** at line 346 — a standard argument (Bienia et al. 1998) stated there without proof.

The incommensurable case is not merely unproved here, it is unreachable by the present route:
`lonelyForSubject_five_commensurable` requires a common `c`, and when some disparity ratio is
irrational no such `c` exists. The framework's own machinery for that case
(`Flanks.lonely_opening_of_free_off_lattice`, `off_lattice_of_irrational_ratio`, both under
`4 ≤ n`) handles **one** free parameter; the general case needs multi-dimensional Kronecker/Weyl
on the torus, which Mathlib does not carry (only the 1-D `AddCircle.denseRange_zsmul_coe_iff`).

Also still unproved, and independent of all this: `FourClears` / `DoorLargestFlank` at `n = 5`
(`OVERLAP_BOUND_v1.md`), and the termination diagonal at every `n ≥ 5`
(`SMALL_ORDER_DOORS_v3.md` §7).

---

## 5. Grades

| claim | grade |
|---|---|
| the four arrangement results at whole-number `v` | `[PROVED — fiveint_axioms_v1.out, axiom-clean]` |
| all four doors at order five, whole-number arrangements | `[PROVED — via `doors_agree`, an equivalence]` |
| the commensurable case | `[PROVED — lonelyForSubject_five_commensurable]` |
| `LonelyRunnerAtN 5` over the reals | **NOT PROVED** — blocked on `theorem121_LRC_real` (`sorry`) |
| the incommensurable case | **NOT PROVED**, and out of reach of this route |
| `DoorLargestFlank` / `FourClears` at `n = 5` | **NOT PROVED** |

**Scope.** "Closed at order five" here means: every arrangement whose disparities from the
subject share a common real measure. That is all whole-number and all rational arrangements,
and no irrational-ratio arrangement.
