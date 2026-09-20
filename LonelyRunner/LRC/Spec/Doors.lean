import LonelyRunner.LRC.Spec.Target

/-!
# The doors, on arrangements

The target is `LonelyRunnerAt8`, equivalently `ExistenceOnArrangements` (`Spec/Target.lean`): every
injective `v : Fin 8 → ℝ`, every subject `k`, some `t > 0` at which the subject is lonely.

`Spec/Target.lean` states the doors on a **difference set**.  This module states them on the
**arrangement**, per subject, and proves each one **equivalent** to the obligation for that subject.
Equivalence is the point: none of these is a weaker thing to aim at, and closing any one of them
closes the target.

* `LonelyForSubject v k` — the obligation for one subject.
* `DoorFlank` — some disparity of the subject hosts a lonely opening.
  **This is the obligation of record (amended 2026-09-20).**  It is the only door with no iteration
  in it: a disparity and a lap index, both read off the arrangement, and no bound on when or on how
  many.  `Spec/Target.lean`'s amendment block carries the decision and the reasons.
* `DoorArrives` — the cascade from the subject's first reading reaches a fixed point.
* `DoorCapped` — the cascade's instants are bounded above.
* `DoorFAM` — each other runner is in the subject's way at only finitely many steps.

  The three above are **sufficient routes**, not the obligation: each is stated over the cascade's
  run, so discharging one means bounding how far a run goes — an obligation the conjecture, which
  asks only for *some* instant, does not carry.  Every proof of theirs is intact and unaffected.
* `DoorThreeLargest` — the flank of `DoorFlank` can be taken among the subject's three largest
  disparities.  This one is **not** proved equivalent: it is a strengthening, stated so that what it
  adds is visible.

Nothing here proves the target.  Each theorem says where the obligation may be attacked.
-/

set_option linter.unusedVariables false

namespace LRC.Spec

open Arrangement MomentIterationN Flanks

/-! ## the subject's own data -/

/-- **The subject's least disparity.**  Not chosen: read off the speeds. -/
noncomputable def leastDisp (v : Fin 8 → ℝ) (k : Fin 8) : ℝ :=
  (diffSet v k).min' (diffSet_nonempty v k)

theorem leastDisp_mem (v : Fin 8 → ℝ) (k : Fin 8) : leastDisp v k ∈ diffSet v k :=
  Finset.min'_mem _ _

theorem leastDisp_le (v : Fin 8 → ℝ) (k : Fin 8) : ∀ d ∈ diffSet v k, leastDisp v k ≤ d :=
  fun d hd => Finset.min'_le _ _ hd

theorem leastDisp_pos {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    0 < leastDisp v k := diffSet_pos hv k _ (leastDisp_mem v k)

/-- **The subject's first reading**, `1/(8·e)` for its least disparity `e`: the instant at which the
nearest runner first leaves the subject's zone.  The cascade starts here. -/
noncomputable def firstReading (v : Fin 8 → ℝ) (k : Fin 8) : ℝ := 1 / (8 * leastDisp v k)

theorem firstReading_pos {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    0 < firstReading v k := by
  unfold firstReading
  have := leastDisp_pos hv k
  positivity

/-! ## the obligation for one subject -/

/-- **The obligation, for one subject.** -/
def LonelyForSubject (v : Fin 8 → ℝ) (k : Fin 8) : Prop := ∃ t : ℝ, 0 < t ∧ LonelyAt v k t

/-- The target is exactly this, for every arrangement and every subject. -/
theorem existenceOnArrangements_iff_subjects :
    ExistenceOnArrangements ↔
      ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, LonelyForSubject v k := Iff.rfl

/-- Through the bridge: the obligation for a subject is `Lonely` on that subject's own disparities. -/
theorem lonelyForSubject_iff_diffSet {v : Fin 8 → ℝ} {k : Fin 8} :
    LonelyForSubject v k ↔ ∃ s : ℝ, 0 < s ∧ Lonely 8 (diffSet v k) s := by
  unfold LonelyForSubject
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, ht, lonelyAt_iff_lonely_diffSet.mp h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, lonelyAt_iff_lonely_diffSet.mpr h⟩

/-! ## door 1 — a disparity hosts a lonely opening

**The obligation of record, amended 2026-09-20** (`Spec/Target.lean`, amendment block).  Door 1 is
the iteration-free door: it asks for a disparity `e` and a lap index `j`, and says the subject is
lonely at `(j + 1/8)/e`.  Nothing runs, so nothing has to stop.  In scales it reads *some candidate
scale `e/(8j+1)` is clear for every disparity* — `ScaleCandidates.lonely_iff_exists_candidate_scale`,
Theorem 6.15.

Discharging it means **exhibiting `(e, j)`** as a function of the difference set, which is
`MANUSCRIPT_v17.md` §6.7's rules-with-conditions form; `Construction8.ratio_condition` (Theorem 4.8)
is already one such rule, with `j = 0`.  No bound on `j` is needed: §6.10's measured ceiling `j ≤ 6`
is recorded there as measured, not proved, and nothing here rests on it.

It is an `↔` like the others, so it is **not easier** — only the right shape. -/

/-- **Door 1 — the obligation of record.**  Some other runner's disparity with the subject has an
opening at which the subject is lonely.  The openings are the speeds' own data; nothing is picked,
nothing iterates, and no bound on when or on how many appears. -/
def DoorFlank (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ i : Fin 8, i ≠ k ∧ ∃ j : ℕ, LonelyAt v k (flankOpening 8 |v i - v k| j)

/-- **Door 1 is the obligation.** -/
theorem doorFlank_iff {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    DoorFlank v k ↔ LonelyForSubject v k := by
  constructor
  · rintro ⟨i, hi, j, hj⟩
    refine ⟨flankOpening 8 |v i - v k| j, flankOpening_pos ?_ j, hj⟩
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hi (hv h))
  · intro h
    obtain ⟨e, he, j, hj⟩ := (exists_lonelyAt_iff_flank hv k).mp h
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp he
    exact ⟨i, hi, j, hj⟩

/-! ## door 2 — the cascade arrives -/

/-- **Door 2.**  The cascade from the subject's first reading reaches a fixed point: a step at which
nobody is in the way, so the step does nothing. -/
def DoorArrives (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ N : ℕ, move 8 (diffSet v k) ((move 8 (diffSet v k))^[N] (firstReading v k))
    = (move 8 (diffSet v k))^[N] (firstReading v k)

/-- **Door 2 is the obligation.** -/
theorem doorArrives_iff {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    DoorArrives v k ↔ LonelyForSubject v k := by
  rw [lonelyForSubject_iff_diffSet]
  exact ((lonely_iff_run_ends (n := 8) (diffSet_pos hv k) (leastDisp_mem v k)).1).symm

/-! ## door 3 — the cascade's instants are bounded -/

/-- **Door 3.**  The instants the cascade visits do not run away: one number above all of them. -/
def DoorCapped (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ U : ℝ, ∀ N : ℕ, (move 8 (diffSet v k))^[N] (firstReading v k) ≤ U

/-- **Door 3 is the obligation.**  A cap gives arrival; arrival gives a cap, because the iterates
stop moving. -/
theorem doorCapped_iff {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    DoorCapped v k ↔ LonelyForSubject v k := by
  rw [← doorArrives_iff hv k]
  constructor
  · rintro ⟨U, hU⟩
    exact ChainBounds.exists_fixed_of_capped (n := 8) (diffSet_pos hv k) (firstReading_pos hv k) hU
  · rintro ⟨N, hfix⟩
    refine ⟨(move 8 (diffSet v k))^[N] (firstReading v k), fun K => ?_⟩
    rcases le_or_gt K N with hKN | hKN
    · have e : (move 8 (diffSet v k))^[N] (firstReading v k)
          = (move 8 (diffSet v k))^[N - K] ((move 8 (diffSet v k))^[K] (firstReading v k)) := by
        rw [← Function.iterate_add_apply]; congr 1; omega
      rw [e]; exact iterate_ge (n := 8) (diffSet v k) _ _
    · obtain ⟨i, rfl⟩ : ∃ i, K = N + i := ⟨K - N, by omega⟩
      exact le_of_eq (FourDifferences.iterate_stable (n := 8) hfix i)

/-! ## door 4 — each runner is in the way finitely often -/

/-- **Door 4.**  Along the cascade, each other runner is in the subject's way at only finitely many
steps. -/
def DoorFAM (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ i : Fin 8, i ≠ k →
    {j : ℕ | inWay 8 |v i - v k| ((move 8 (diffSet v k))^[j] (firstReading v k))}.Finite

/-- **Door 4 is the obligation.**  Seven finite sets have a finite union, and a cascade that never
arrives has someone in the way at every step, so `ℕ` would sit inside that union. -/
theorem doorFAM_iff {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    DoorFAM v k ↔ LonelyForSubject v k := by
  classical
  rw [← doorArrives_iff hv k]
  constructor
  · intro h
    by_contra hno
    unfold DoorArrives at hno
    push Not at hno
    have hact : ∀ j : ℕ, ∃ d ∈ diffSet v k,
        inWay 8 d ((move 8 (diffSet v k))^[j] (firstReading v k)) := by
      intro j
      rcases move_eq_self_or_opening (n := 8) (diffSet v k)
        ((move 8 (diffSet v k))^[j] (firstReading v k)) with hfix | ⟨x, hx, hw, -⟩
      · exact absurd hfix (hno j)
      · exact ⟨x, hx, hw⟩
    have hfin : (⋃ d ∈ diffSet v k,
        {j : ℕ | inWay 8 d ((move 8 (diffSet v k))^[j] (firstReading v k))}).Finite := by
      refine Set.Finite.biUnion (diffSet v k).finite_toSet (fun d hd => ?_)
      obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
      exact h i hi
    have huniv : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ diffSet v k,
        {j : ℕ | inWay 8 d ((move 8 (diffSet v k))^[j] (firstReading v k))} := by
      intro j _
      obtain ⟨d, hd, hw⟩ := hact j
      exact Set.mem_biUnion hd hw
    exact Set.infinite_univ (hfin.subset huniv)
  · rintro ⟨N, hfix⟩ i hi
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro j hj
    by_contra hjN
    simp only [Set.mem_Iio, not_lt] at hjN
    obtain ⟨c, rfl⟩ : ∃ c, j = N + c := ⟨j - N, by omega⟩
    rw [Set.mem_setOf_eq, FourDifferences.iterate_stable (n := 8) hfix c] at hj
    have hmem : |v i - v k| ∈ diffSet v k := mem_diffSet.mpr ⟨i, hi, rfl⟩
    exact absurd (lonely_of_fixed (diffSet_pos hv k) hfix _ hmem) (not_le.mpr hj)

/-! ## door 5 — the flank is one of the three largest

Not proved equivalent, and deliberately so.  Doors 1–4 are the obligation restated; this one is a
**strengthening** of door 1, and stating it separately is what makes the extra content visible. -/

/-- **Door 5.**  The lonely opening of door 1 can be found at a disparity with at most two disparities
above it — one of the subject's three largest. -/
def DoorThreeLargest (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ i : Fin 8, i ≠ k ∧
    ((diffSet v k).filter (fun d => |v i - v k| < d)).card ≤ 2 ∧
    ∃ j : ℕ, LonelyAt v k (flankOpening 8 |v i - v k| j)

/-- **Door 5 gives the obligation.**  The converse is not claimed: door 5 says *where* the opening is
as well as that it exists, and that is strictly more. -/
theorem lonelyForSubject_of_threeLargest {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8)
    (h : DoorThreeLargest v k) : LonelyForSubject v k := by
  obtain ⟨i, hi, -, j, hj⟩ := h
  exact (doorFlank_iff hv k).mp ⟨i, hi, j, hj⟩

/-! ## the doors together -/

/-- **The four doors are one door.**  Each is the obligation for that subject, so closing any one of
them for every arrangement and every subject closes the conjecture at eight runners. -/
theorem doors_agree {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧
    (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧
    (DoorFAM v k ↔ LonelyForSubject v k) :=
  ⟨doorFlank_iff hv k, doorArrives_iff hv k, doorCapped_iff hv k, doorFAM_iff hv k⟩

/-- **And closing any one of them closes the target.** -/
theorem lonelyRunnerAt8_of_doorFlank
    (h : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, DoorFlank v k) :
    LonelyRunnerAt8 := fun v hv k => (doorFlank_iff hv k).mp (h v hv k)

theorem lonelyRunnerAt8_of_doorArrives
    (h : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, DoorArrives v k) :
    LonelyRunnerAt8 := fun v hv k => (doorArrives_iff hv k).mp (h v hv k)

theorem lonelyRunnerAt8_of_doorCapped
    (h : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, DoorCapped v k) :
    LonelyRunnerAt8 := fun v hv k => (doorCapped_iff hv k).mp (h v hv k)

theorem lonelyRunnerAt8_of_doorFAM
    (h : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, DoorFAM v k) :
    LonelyRunnerAt8 := fun v hv k => (doorFAM_iff hv k).mp (h v hv k)

/-! ## the coupling across subjects

`Arrangement.inWay_comm` says being in the way is **symmetric**: `i` is in `k`'s way exactly when `k`
is in `i`'s.  A difference set cannot state this, because it fixes one subject and keeps only that
subject's seven disparities.  On an arrangement there are **28 pairs**, not `8 × 7` independent
constraints, and the eight subjects' obligations are coupled through them.

At an instant `t` the runners in the way form an undirected graph on the eight runners.  A subject is
lonely exactly when it is **isolated** in that graph, and the sum of the eight degrees counts the
ordered blocking pairs — one identity binding all eight obligations at once.

Nothing here closes a door.  It states the object the doors live on. -/

open scoped Classical in
/-- **The subject's blocking degree at `t`**: how many runners are in its way. -/
noncomputable def blockDegree (v : Fin 8 → ℝ) (t : ℝ) (k : Fin 8) : ℕ :=
  (Finset.univ.filter (fun i : Fin 8 => i ≠ k ∧ InWay v k i t)).card

open scoped Classical in
/-- **Lonely is degree zero.**  The subject is lonely exactly when it is isolated. -/
theorem lonelyAt_iff_blockDegree_zero {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔ blockDegree v t k = 0 := by
  rw [lonelyAt_iff_no_inWay, blockDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i _ hc; exact h i hc.1 hc.2
  · intro h i hi hw; exact h (Finset.mem_univ i) ⟨hi, hw⟩

open scoped Classical in
/-- **The blocking relation is symmetric**, so the graph is undirected. -/
theorem blockDegree_symm_pairs {v : Fin 8 → ℝ} {t : ℝ} {i k : Fin 8} :
    (i ≠ k ∧ InWay v k i t) ↔ (k ≠ i ∧ InWay v i k t) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, inWay_comm.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, inWay_comm.mp h2⟩⟩

open scoped Classical in
/-- **The handshake identity.**  The eight degrees sum to the number of ordered blocking pairs.  This
is the coupling: the eight subjects' obligations at a single instant are not independent. -/
theorem sum_blockDegree (v : Fin 8 → ℝ) (t : ℝ) :
    ∑ k : Fin 8, blockDegree v t k
      = (Finset.univ.filter (fun p : Fin 8 × Fin 8 => p.2 ≠ p.1 ∧ InWay v p.1 p.2 t)).card := by
  simp only [blockDegree, Finset.card_filter]
  rw [Fintype.sum_prod_type]

open scoped Classical in
/-- **The obligation, in the graph.**  For every arrangement and every runner, some instant at which
that runner is isolated. -/
theorem existenceOnArrangements_iff_isolated :
    ExistenceOnArrangements ↔
      ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
        ∃ t : ℝ, 0 < t ∧ blockDegree v t k = 0 := by
  unfold ExistenceOnArrangements
  exact forall_congr' fun v => forall_congr' fun _ => forall_congr' fun k =>
    exists_congr fun t => and_congr_right fun _ => lonelyAt_iff_blockDegree_zero


/-! ## door 3 with a cap written down — `[REFUTED]`

**`DoorFirstLap` is false.  Do not attempt to prove it.**  It is kept, with the two implications
below, because both remain true and because deleting a refuted statement loses the record of why
this route is closed.  Nothing depends on it; both theorems are now vacuous.

*What was measured, and reproduces.*  Across **170,213 primitive 7-sets** exhaustively (every
primitive 7-subset of `[1,22]`) the cascade always arrives, and the arrival instant in the
**nearest runner's own laps** — `τ = e·t` for `e` the least disparity — never exceeds
`33/56 = 0.58929…`, attained at `(2,6,8,9,11,14,15)`.  That figure is correct.

*What was inferred from it, and is false.*  That the constant is unchanged as the range grows, hence
that the cascade arrives inside the nearest runner's first lap.  The maximum of `τ` is not stable:
is `33/56` on `[1,18]`, `[1,20]`, `[1,22]`, then `17/24 = 0.70833` on `[1,24]` at
`(3,9,11,14,15,19,24)`, then `17/22 = 0.77273` on `[1,30]` at `(4,11,14,17,19,24,30)`.  That shows `33/56` is not a bound; it does not show `τ` unbounded,
since a maximum over a nested family rises by construction.  Capping the difference range caps the denominator of the readings `u = d/e`, and depth
lives in fine denominators, so `[1,22]` could not see past itself.

*The refutation.*  The arrangement `(27, 70, 107, 137, 159, 188, 344, 393)`, subject `393` —
recorded in `MANUSCRIPT_v17.md` §6.7 as the 28-move adversarial case — has disparities
`{49, 205, 234, 256, 286, 323, 366}` and arrives at `t = 49/1872`, so

    τ = 49 · 49/1872 = 2401/1872 = 1.28259 > 1,

which is `t > 1 / leastDisp`.  The arrival is lonely, one reading sits at exactly `1/8`, and no
opening at or before it is lonely, so it is the first isolation instant.  A second witness is §6.7's
own second-lap case `(1, 31, 75, 97, 128, 160, 176, 225)`, subject `1`, at `τ = 165/128`.

*Why it was the wrong shape to begin with.*  The conjecture asks for loneliness at **some** time, so
no bound on *when* is ever required.  `MANUSCRIPT_v17.md` §6A, row two — *"No window, no bound on
when"* — bans exactly this, and a cap in units of the nearest runner's lap is a window in disguise.

`[REFUTED — exact rational arithmetic; experiments/n8/doorfirstlap_refutation_v1.{py,out},
doorfirstlap_cap_growth_v1.{py,out}; docs/n8/CAP_DEFECT_v1.md]` -/

/-- **Door 3, with a cap named.**  `[REFUTED]` — asserts `t ≤ 1/e`, i.e. `τ = e·t ≤ 1`, which fails
at `τ = 2401/1872` on the disparities `{49, 205, 234, 256, 286, 323, 366}`.  Kept as a record; the
two theorems below are true and vacuous. -/
def DoorFirstLap (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ N : ℕ, (move 8 (diffSet v k))^[N] (firstReading v k) ≤ 1 / leastDisp v k

/-- **The named cap would be a cap**, so door 3 with `U = 1/e` would still be the obligation.  True,
and vacuous: `DoorFirstLap` is `[REFUTED]`. -/
theorem doorCapped_of_doorFirstLap {v : Fin 8 → ℝ} {k : Fin 8} (h : DoorFirstLap v k) :
    DoorCapped v k := ⟨1 / leastDisp v k, h⟩

/-- **And it would close the conjecture.**  True, and vacuous: its hypothesis is `[REFUTED]`, so this
is not a route to the target. -/
theorem lonelyRunnerAt8_of_doorFirstLap
    (h : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, DoorFirstLap v k) :
    LonelyRunnerAt8 :=
  fun v hv k => (doorCapped_iff hv k).mp (doorCapped_of_doorFirstLap (h v hv k))

/-! ## door 5, and what it cannot be strengthened to

`DoorThreeLargest` measured on **35,872** sets (random 7-subsets of `[1,20]`, `[1,30]`, `[1,45]`,
`[1,70]`, plus every primitive arithmetic progression `a + d·i`, `a ≤ 39`, `d ≤ 24`): the best
available flank rank from the large end was `1` in 35,785 cases, `2` in 84, `3` in 3, and **never 4**.
So three is the right number and it is attained.  `[EMPIRICAL — 35,872 sets]`

The obvious strengthening — take the **largest** disparity — is **refuted**: `(2,3,5,7,8,13,16)` has
no lonely opening at flank `16`, and needs flank `13`, lap `1`.  The three sets needing rank three are
`(1,3,5,7,8,14,16)` at flank `8` lap `2`, `(1,4,5,6,7,8,14)` at flank `7` lap `2`, and
`(1,3,4,5,7,12,16)` at flank `7` lap `3`. -/

/-- **Door 5 with the largest disparity only.**  Stated so that the refutation has something to name —
this is `[REFUTED]` as a universal statement by `(2,3,5,7,8,13,16)`. -/
def DoorLargestFlank (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ i : Fin 8, i ≠ k ∧
    (∀ i' : Fin 8, i' ≠ k → |v i' - v k| ≤ |v i - v k|) ∧
    ∃ j : ℕ, LonelyAt v k (flankOpening 8 |v i - v k| j)

/-- **The largest-flank form is a special case of door 5**, so the refutation of the first says
nothing against the second. -/
theorem doorThreeLargest_of_doorLargestFlank {v : Fin 8 → ℝ} (hv : Function.Injective v)
    {k : Fin 8} (h : DoorLargestFlank v k) : DoorThreeLargest v k := by
  classical
  obtain ⟨i, hi, hmax, j, hj⟩ := h
  refine ⟨i, hi, ?_, j, hj⟩
  have : ((diffSet v k).filter (fun d => |v i - v k| < d)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    obtain ⟨i', hi', rfl⟩ := mem_diffSet.mp hd
    exact not_lt.mpr (hmax i' hi')
  rw [this]
  simp


end LRC.Spec
