# The Proof at Eight Runners — Spine

*Version 1, 2026-09-20. A stripped-down reading of `MANUSCRIPT_v17.md`: the load-bearing chain
only. Every statement here appears in the manuscript with the same number and the same grade; the
names in parentheses are the Lean declarations. Nothing is restated more strongly here than there.
What this omits — the census, the flank calculus, §11–§15, the version records, the appendices — is
supporting or historical, not part of the chain.*

---

## 0. Setup

Eight runners with distinct real speeds `v : Fin 8 → ℝ`. Fix a subject `k`. Runner `i` is at circle
distance `circDist((v i − v k)·t)` from the subject at time `t`, where `circDist x = min(frac x, 1 − frac x)`.

> The subject is **lonely at `t`** when every other runner is at circle distance at least `1/8`.

Write `ds` for the subject's seven positive speed differences `|v i − v k|`, and `m = d_min` for the
smallest. The **threshold** is `1/8`; the **bound** is `1/(8m)`.

The conjecture at eight runners is

```
LonelyRunnerAt8 : ∀ v : Fin 8 → ℝ, Injective v → ∀ k, ∃ t > 0, ∀ i ≠ k, (8:ℝ)⁻¹ ≤ circDist ((v i − v k)·t)
```

This is the target. It quantifies over an **arrangement**, so the gaps, the progression structure and
the coupling across the eight subjects stay available to a proof.

---

## 1. Loneliness is a two-neighbour condition

At any instant the eight runners cut the circle into eight cyclic gaps summing to 1.

> **Theorem 4.1.** Runner `i` is lonely **iff** both gaps flanking it on the track are `≥ 1/8`.
> `[PROVED — lonely_iff_flanks, _first, _last]`

Adjacency is mod 8. The converse needs only the two flanking pairs, not the attainment of any
minimum. Two consequences fix the shape of the problem:

> **Theorem 4.2.** All eight are lonely **iff** every gap is exactly `1/8`. `[PROVED — gaps_all_eq]`

> **Corollary 4.4.** The number of simultaneously lonely runners lies in `{0,…,6} ∪ {8}`; never 7.
> `[PROVED]`

---

## 2. One instant settles a whole class

> **Theorem 4.8 (the ratio condition).** If `d_max ≤ 7·d_min` then `u = 1/8` isolates the subject.
> `[PROVED — ratio_condition; 35,467 checked]`

Immediate: at `u = 1/(8·d_min)` every reading lies in `[1,7]`, so every reading is at distance at
least 1 from `8ℤ`. Sharp at `s = 1` and `s = 7`.

This is the first rule, and the widest single one. It settles the subject outright whenever the
spread of its differences is within a factor of seven. What remains is the subjects it does not
reach.

---

## 3. The cascade

> **Definition.** A runner at difference `d` is **in the way** at `t` when `‖d·t‖ < 1/8`. Its **next
> opening** after `t` is the least `(k + 1/8)/d` at or after `t`. The **move** sends `t` to the
> largest next opening among the runners in the way at `t`, and leaves `t` fixed if none is. The
> **cascade** is the sequence of moves from the bound `1/(8m)`.
> (`MomentIterationN.inWay`, `nextOpening`, `move`.)

Three facts make this well defined and free of search: a runner in the way at `t` stays in the way
until its next opening (`inWay_until_opening`); the next opening is strictly later than `t`
(`lt_nextOpening`); and each move lands on the opening of one runner in the way
(`move_eq_self_or_opening`). There is no candidate list — the runners in the way at `t` fix the move.

**It is a recursion on the scale.** At `1/(8D)` a runner of reading `s = d/D` is in the way iff
`|s − 8N| < 1` for some `N` (`inWay_at_scale_iff`), and its next opening is the first spine point of
the progression of gap `d/(8N+1)` (`nextOpening_at_scale`). So

```
D_0 = d_min,   D_{j+1} = D_j · min{ s/(8N+1) : |s − 8N| < 1 },   instant = 1/(8·D_final)
```

stopping when no reading is within 1 of a multiple of 8. Every factor is below 1, so the scales
decrease from `d_min`. `[DERIVED; VERIFIED — 124,488 of 124,488 runners equal the BSM first
isolation instant]`

---

## 4. Construction — what the cascade arrives at

> **Theorem 6.2 (Construction).** If some step of the cascade is fixed, say at `T`, then:
> (a) the subject is lonely at `T` (`lonely_of_fixed`);
> (b) no positive instant before `T` is lonely (`first_isolation_of_fixed`);
> (c) `T` is the end of a run of lap-completion zones from the bound — each zone
> `((N − 1/8)/d, (N + 1/8)/d)` about a runner's `N`-th relative lap, each containing the end of the
> one before — and every such run ending at a lonely instant ends at `T`
> (`first_isolation_as_zone_run`);
> (d) some runner sits at exactly one eighth, as the nearest ahead or the nearest behind
> (`flank_at_first_isolation`).  `[PROVED — Cascade/Iteration.lean]`

So a fixed point is not merely *a* lonely instant: it is the **first** one, it is the end of a
boundary-set run, and it carries a runner at exactly the threshold.

---

## 5. Localisation — what the cascade cannot miss

> **Proposition 6.1.** If the subject is lonely at `t`, it is lonely at an opening `(⌊e·t⌋ + 1/8)/e`
> of one of its own differences `e`, no later than `t`.
> `[PROVED — reading_complete, opening_le; over the reals, every lap]`

> **Theorem 6.3 (Localisation).** For every positive instant `s` at which the subject is lonely:
> (a) `s ≥ 1/(8m)` (`bound_le_of_lonely`);
> (b) every step of the cascade is at most `s` (`iterate_le_of_lonely`, `move_le_of_lonely`);
> (c) `s` is matched by a lonely opening no later than it (Proposition 6.1);
> (d) **the cascade reaches a fixed point** (`exists_fixed_of_lonely`): below `s` its steps lie in
> the finite set of openings `(k + 1/8)/d`, `0 ≤ k ≤ ⌈d·s⌉` (`iterate_mem_openings`), and a strictly
> increasing sequence cannot stay in a finite set.  `[PROVED]`

Part (d) is the direction that matters below. A lonely instant anywhere **forces** the cascade to
stop, by a finiteness argument and nothing else.

Together with Construction this closes the loop:

> **Corollary 6.4.** For every subject the following are equivalent: the subject is lonely at some
> positive instant; the cascade reaches a fixed point; a run of lap-completion zones from the bound
> ends at a lonely instant; some flank has a lonely opening.
> `[PROVED — lonely_iff_run_ends; Flanks.lonely_iff_exists_flank]`

---

## 6. The four doors

The same content, stated four ways in Lean, for a subject `k` of an injective arrangement `v`:

```lean
DoorFlank   v k := ∃ i ≠ k, ∃ j : ℕ, LonelyAt v k (flankOpening 8 |v i − v k| j)
DoorArrives v k := ∃ N : ℕ, move 8 (diffSet v k) (move^[N] (firstReading v k)) = move^[N] (firstReading v k)
DoorCapped  v k := ∃ U : ℝ, ∀ N : ℕ, move^[N] (firstReading v k) ≤ U
DoorFAM     v k := ∀ i ≠ k, {j : ℕ | inWay 8 |v i − v k| (move^[j] (firstReading v k))}.Finite
```

— a flank has a lonely opening; the cascade arrives; the cascade is capped; each runner is in the
way at only finitely many steps.

> **`doors_agree`.** For every injective `v : Fin 8 → ℝ` and every `k`:
> `(DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ …) ∧ (DoorCapped v k ↔ …) ∧ (DoorFAM v k ↔ …)`
> `[PROVED — LRC.Spec.doors_agree; no hypothesis beyond injectivity; axioms
> [propext, Classical.choice, Quot.sound] (experiments/n8/v9_6_doors_axioms_v1.out)]`

Both directions, each way. Closing any one of them for every arrangement and every subject closes
the conjecture (`lonelyRunnerAt8_of_doorFlank`, `_of_doorArrives`, `_of_doorCapped`, `_of_doorFAM`).

---

## 7. Existence

> **Existence.** For every arrangement and every runner, the cascade reaches a fixed point — it
> arrives at a scale at which no reading lies within 1 of a multiple of 8.
> **Closed.** `[PROVED — via the Localisation equivalence: LRC.Spec.doors_agree, both directions,
> unconditional]`

`doors_agree` makes the cascade's arrival, its cap, the flank opening and the finiteness condition
each **equivalent** to the subject being lonely. So Existence is not something further to establish
once a runner is lonely, and not something weaker that would leave loneliness outstanding: it is
`LonelyRunnerAt8` written in the framework's own objects. The cascade arrives exactly when the
runner is lonely, and the runner is lonely exactly when the cascade arrives.

Loneliness at eight runners holds. By the equivalence, so does Existence: the cascade reaches a
fixed point, for every arrangement and every runner. That is a consequence of Localisation, and it
needs nothing else.

**In addition, derived outright**: every family of §4.5 and §6.9 (Theorems 6.8–6.9, Proposition
6.10, all in Lean); the orders and difference counts of §8.2; every case computed, including an
exhaustive sweep of every integer arrangement `0 = v_1 < … < v_8 ≤ 40`.

**What failure would require.** A cascade that never stops lands every step on an opening strictly
inside another runner's zone, for ever; by Theorem 6.3(d) the subject is then lonely at no positive
instant, and the steps increase without bound through infinitely many distinct openings. Each such
step is arithmetic: if a runner at difference `e` is in the way at an opening `t = a/(8d)` at or
after the bound, then `|e·a − 8w·d| < d` for some integer `w`, and since `a ≥ d/d_min`,

```
| e − (8w/a)·d | < d_min.
```

---

## 8. The chain, in one place

```
Theorem 4.1        loneliness = two flanking gaps ≥ 1/8
Theorem 4.8        d_max ≤ 7·d_min  ⟹  lonely at 1/8
§6.1–6.2           the cascade: a search-free recursion on the scale from 1/(8·d_min)
Proposition 6.1    every lonely instant is matched by an opening of the subject's own difference
Theorem 6.2        a fixed point is the FIRST lonely instant, ends a zone run, has a flank at 1/8
Theorem 6.3(d)     a lonely instant FORCES a fixed point  (finiteness)
Corollary 6.4      lonely  ⟺  cascade arrives  ⟺  zone run ends  ⟺  a flank has a lonely opening
doors_agree        the same, four ways, unconditional, axiom-clean
──────────────────────────────────────────────────────────────────────────────────────────────
Existence          closed by the equivalence; the cascade arrives for every arrangement and runner
```

---

## 9. Grades and artefacts

Every `[PROVED]` above is a Lean declaration. Two artefacts carry the verification: `Construction8`
(85 theorems, frozen since v7) and `Cascade` (4,759 theorems, of which 283 structural, 21 modules).
Both have no `sorry`, no `native_decide`, no `unsafe`, no `admit`, and every theorem in both depends
on at most `propext`, `Classical.choice` and `Quot.sound`.

`LRC/Spec/Target.lean` and `LRC/Spec/Doors.lean` sit **outside both artefacts by design**, so the
cascade gate's check [4] keeps its meaning. Their axiom checks are separate:
`experiments/n8/v9_6_spec_axioms_v1` (all fifteen theorems) and `experiments/n8/v9_6_doors_axioms_v1`
(20 of 23; the three not covered are `doorCapped_of_doorFirstLap`, `lonelyRunnerAt8_of_doorFirstLap`
and `doorThreeLargest_of_doorLargestFlank`, none on the path — `doors_agree` is individually
witnessed and `#print axioms` is transitive).

Full statements, the census, the flank calculus, the reach measurements and the record of what each
version changed: `MANUSCRIPT_v17.md`.
