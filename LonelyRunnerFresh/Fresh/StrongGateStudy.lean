import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.LonelyCells
import Fresh.Gate
import Fresh.Types

/-!
# The strong gate: what a counterexample would have to be, and why none is found (Task W)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Dilation`, `ChainLaws`,
`LonelyCells`, `Gate`, `Types`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is
positive (no runner is stationary).  Every statement is symbolic: for every finite set `ds` of positive disparities
with least element `m` (cascade coordinate `R = 8·m·t`).

Setting.  `Types.StrongGate` (OWED there) says: at the first state above `R = 7` of the cascade from the bound, no
runner in the way has its next opening beyond `R = 9`.  `Types.late_blocker_forces_slow_lap_one` says a violation has
a setter `x` of the move into the gate on lap 1 with `15 x < 17 m` (reading below `17/15`), and a blocker `y` with lap
`≥ 2`.

Results (each [L] has its `#print axioms` line below it; grades [L] / [OBS] / [OWED]).
* `idle_before_entry` [L]: a runner `x ≥ m` is never in the way at an instant `t` with `1/(8m) ≤ t ≤ 7/(8x)`.  In
  readings: `ρ_x` is idle on `R ∈ [1, 7/ρ_x]`.  (The same fact as `Gate.setter_gt`, stated as the clearness of `x`.)
* `violation_carves` [L]: a violation of the strong gate forces a runner `x` of `ds` with `m < x`, `15 x < 17 m`, such
  that the whole window `t ∈ [1/(8m), 7/(8x)]` (in `R`: `[1, 7/ρ_x]`, which contains `[1, 105/17]`, `105/17 > 6.17`) is
  blocked by the OTHER runners `ds \ {m, x}` alone: both `d_min` (idle until `R = 7`) and `x` (idle until `R = 7/ρ_x`)
  contribute nothing there.  The blocker `y` is one of those other runners, and `y ≠ m`, `y ≠ x`.
* `strongGate_of_fiveCarve` [L]: `FiveCarve` (OWED, below) implies `Types.StrongGate`.  `FiveCarve` says that any five
  disparities `≥ m` leave a lonely instant (a point not blocked by any of them) in `R ∈ [1, 7/ρ_x]` for `ρ_x < 17/15`.
  [OBS] with a large margin (exact integer enumeration plus float-steered searches; see `FiveCarve`): the first lonely
  instant of five readings from `R = 1` is at `R ≤ 4.4`; the window needed is `R ≥ 6.17`.  FiveCarve is NOT proved here.
  `FiveReach` (OWED; any five disparities `≥ m` have a lonely instant by `R = 6`) implies `FiveCarve`
  (`fiveCarve_of_fiveReach` [L]), so `FiveReach → StrongGate`.
* `late_blocker_fast` [L]: in a violation, `3 y > 5 m` (the blocker is fast: reading above `5/3`).
* `int_lonely_half` [L]: for integer disparities every lonely instant gives a lonely instant in `(0, 1/2]` (mirror).
  A gate crosser with integer `d_min = m` therefore has its first lonely instant in `R ∈ [9, 4m]`; this excludes
  `m ≤ 2` (as `Types` already did) and nothing more.
* `crosser_needs_multiple`, `crosser_dmin_three` … `crosser_dmin_seven` [L]: an integer gate crosser contains a multiple
  of every `q ≤ 8` with `8m/7 ≤ q ≤ 8m` (the instant `t = 1/q` is lonely otherwise).  These are the "multiple of 8"
  (needed for `m ≤ 7`) and "multiple of 7" (needed for `m ≤ 6`) conditions; for `m = 3, 4, 5` the list also contains
  6, then 5, then 4.  They are necessary only; the absence of integer crossers at `m = 3, 4, 5` is [OBS] (exhaustive).

Provenance.  `idle_before_entry` is `Gate.setter_gt` (record L5(b), `GATE_LEMMAS_v1.md`) read as a clearness
statement; `violation_carves` is new here (it combines `Types.late_blocker_forces_slow_lap_one`, `Gate.dmin_clear_first_window`
and `Cascade.seq_le_of_lonely`); in the existing tree the nearest statement is `LRC/Spec/FirstGateN.lean`
(`forced_nearest_move`, under the gap hypothesis `d ≥ 2`).  Nothing was copied.
-/

open Classical

namespace Fresh

namespace StrongGateStudy

open Cascade Dilation ChainLaws

/-! ## (1) An idle runner contributes nothing before its entry -/

/-- **A runner `x ≥ m` is clear on `[1/(8m), 7/(8x)]`** (in readings: `ρ_x` is idle on `R ∈ [1, 7/ρ_x]`).  Its first
lap zone opens at `7/(8x)`; the lap-0 zone ended before `1/(8m)`. -/
theorem idle_before_entry {m x t : ℝ} (hm : 0 < m) (hmx : m ≤ x) (hb : 1 / (8 * m) ≤ t) (ht : t ≤ 7 / (8 * x)) :
    ¬ InWay x t := by
  intro hw
  have hx0 : 0 < x := lt_of_lt_of_le hm hmx
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hb
  have h := Gate.setter_gt hm hmx hb hw
  rw [div_lt_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)] at ht
  nlinarith

#print axioms idle_before_entry

/-! ## (2) What a violation of the strong gate forces -/

/-- **A violation carves a window with five runners.**  Let `ds` have least element `m`, let the cascade from `1/(8m)`
cross `R = 7` at step `n` (`seq n ≤ 7/(8m) < seq (n+1)`), and let `y ∈ ds` be in the way at `seq (n+1)` with next opening
beyond `9/(8m)`.  Then there is `x ∈ ds` with `m < x`, `15 x < 17 m`, `x ≠ y`, `y ≠ m`, such that every instant `s` of
`[1/(8m), 7/(8x)]` has a blocker in `(ds \ {m}) \ {x}`. -/
theorem violation_carves {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hmem : m ∈ ds) (hlow : ∀ d ∈ ds, m ≤ d)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ}
    (hle : seq n ≤ 7 / (8 * m)) (hgt : 7 / (8 * m) < seq (n + 1))
    {y : ℝ} (hy : y ∈ ds) (hwy : InWay y (seq (n + 1))) (hlate : 9 / (8 * m) < nextOpening y (seq (n + 1))) :
    ∃ x ∈ ds, m < x ∧ 15 * x < 17 * m ∧ x ≠ y ∧ y ≠ m ∧
      y ∈ (ds.erase m).erase x ∧
      ∀ s, 1 / (8 * m) ≤ s → s ≤ 7 / (8 * x) → ∃ d ∈ (ds.erase m).erase x, InWay d s := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hb : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  -- the setter of the move into the gate
  obtain ⟨x, hx, hwx, hsx⟩ : ∃ x ∈ ds, InWay x (seq n) ∧ seq (n + 1) = nextOpening x (seq n) := by
    rcases hmv n with ⟨_, h⟩ | ⟨x, hx, hwx, hsx, _⟩
    · exact absurd (h ▸ hgt) (not_lt.mpr hle)
    · exact ⟨x, hx, hwx, hsx⟩
  obtain ⟨hlap, h15, -⟩ :=
    Types.late_blocker_forces_slow_lap_one hm (hlow x hx) (hlow y hy) hb hle hwx hsx hwy hlate
  -- `x ≠ m`: on lap 1, `x · seq n > 7/8`, while `m · seq n ≤ 7/8`
  have hmt : m * seq n ≤ 7 / 8 := by
    have := hle
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hxm : m < x := by
    rcases (hlow x hx).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := abs_lt.mp (abs_sub_lap_lt hwx)
      rw [hlap, ← h] at h1
      push_cast at h1
      linarith [h1.1]
  have hxy : x ≠ y := by
    rintro rfl
    exact Dilation.equal_not_inWay (hpos x hx) (hsx ▸ hwy)
  -- `y ≠ m`: `d_min` has next opening exactly `9/(8m)` in the gate
  obtain ⟨hlt9, hwm⟩ := Types.gate_entry hm hlow hle hgt (hmv n)
  have hym : y ≠ m := by
    rintro rfl
    rw [Types.nextOpening_dmin_of_gate hm hgt hlt9] at hlate
    exact lt_irrefl _ hlate
  have hyE : y ∈ (ds.erase m).erase x :=
    Finset.mem_erase.mpr ⟨fun h => hxy h.symm, Finset.mem_erase.mpr ⟨hym, hy⟩⟩
  refine ⟨x, hx, hxm, h15, hxy, hym, hyE, ?_⟩
  intro s hs1 hs7
  by_contra hcon
  push Not at hcon
  have hxm' : 7 / (8 * x) ≤ 7 / (8 * m) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hl : LonelyAt ds s := by
    intro d hd
    by_cases hdm : d = m
    · subst hdm
      exact Gate.dmin_clear_first_window hm hs1 (hs7.trans hxm')
    by_cases hdx : d = x
    · subst hdx
      exact not_inWay_iff.mp (idle_before_entry hm (hlow d hd) hs1 hs7)
    exact not_inWay_iff.mp (hcon d (Finset.mem_erase.mpr ⟨hdx, Finset.mem_erase.mpr ⟨hdm, hd⟩⟩))
  have hseq := seq_le_of_lonely hpos hl (h0 ▸ hs1) hmv (n + 1)
  linarith

#print axioms violation_carves

/-- **In a violation the blocker is fast**: reading `y/m > 5/3` (lap `≥ 2` at a state below `R = 9`). -/
theorem late_blocker_fast {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ}
    (hle : seq n ≤ 7 / (8 * m)) (hgt : 7 / (8 * m) < seq (n + 1))
    {y : ℝ} (hy : y ∈ ds) (hwy : InWay y (seq (n + 1))) (hlate : 9 / (8 * m) < nextOpening y (seq (n + 1))) :
    5 * m < 3 * y := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hb : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  obtain ⟨x, hx, hwx, hsx⟩ : ∃ x ∈ ds, InWay x (seq n) ∧ seq (n + 1) = nextOpening x (seq n) := by
    rcases hmv n with ⟨_, h⟩ | ⟨x, hx, hwx, hsx, _⟩
    · exact absurd (h ▸ hgt) (not_lt.mpr hle)
    · exact ⟨x, hx, hwx, hsx⟩
  obtain ⟨-, -, hk2⟩ :=
    Types.late_blocker_forces_slow_lap_one hm (hlow x hx) (hlow y hy) hb hle hwx hsx hwy hlate
  obtain ⟨hlt9, -⟩ := Types.gate_entry hm hlow hle hgt (hmv n)
  have hy0 : 0 < y := hpos y hy
  have h1 := abs_lt.mp (abs_sub_lap_lt hwy)
  have hk : (2 : ℝ) ≤ (lap y (seq (n + 1)) : ℝ) := by exact_mod_cast hk2
  have ht9 : seq (n + 1) < 9 / (8 * m) := hlt9
  have ht0 : 0 < seq (n + 1) := lt_of_lt_of_le (by positivity) (hb.trans (le_trans (le_of_isMove hpos (hmv n)) le_rfl))
  rw [lt_div_iff₀ (by positivity)] at ht9
  -- y t' > 15/8 and 8 m t' < 9 give 3y > 5m
  nlinarith

#print axioms late_blocker_fast

/-! ## (3) The reduction to a five-runner carving statement -/

/-- **FiveCarve** (OWED).  Any five disparities `≥ m` leave a lonely instant of `[1/(8m), 7/(8x)]` for every `x` with
`m < x` and `15 x < 17 m` (in readings: the first lonely point of five readings from `R = 1` lies at or before
`7/ρ_x`, and `7/ρ_x > 6.17`).  Observed with a large margin (all exact or float searches in the Task W scratch directory): the first lonely point of
five readings from `R = 1` is at `R ≤ 4.3996` in every search.  Exact integer enumeration of all 6-sets
`{A < a₂ < … < a₆ ≤ L}`: `A = 1..14, L = 100` (largest `275/64 = 4.2969`), and `A = 16, 20` with `L = 14·A`
(largest `100/23 = 4.3478`, `A = 20`; these are exact integer cascades); float-steered [OBS] only: hill-climbing on reals and 8·10⁸ random samples, supremum `≈ 4.3996`; the linear
programme of the best chain type (laps `1,1,1,1,1,2,2,3,2,3`) has maximum `2125/483 = 4.399585…` (not attained).  The window
needed is `R ≥ 7/ρ_x > 105/17 = 6.176`.  Not proved. -/
-- [PROVISIONAL: covering] FiveCarve is a covering statement (five readings cannot block a window); it supports
-- the claim `Types.StrongGate` through `strongGate_of_fiveCarve`.  OWED: nothing in this folder proves it.
-- STANDING: OWED
def FiveCarve : Prop :=
  ∀ (E : Finset ℝ) (m x : ℝ), E.card ≤ 5 → 0 < m → m < x → 15 * x < 17 * m → (∀ d ∈ E, m ≤ d) →
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * x) ∧ LonelyAt E s

/-- **FiveReach** (OWED), the clean form of `FiveCarve`: any five disparities `≥ m` leave a lonely instant in
`[1/(8m), 6/(8m)]` (readings: the first lonely point of five readings from `R = 1` is at `R ≤ 6`).  The same evidence as
`FiveCarve` (largest value seen `≈ 4.3996`, so `6` carries a large margin).  Not proved. -/
-- [PROVISIONAL: covering] a covering statement; supports `Types.StrongGate` through `fiveCarve_of_fiveReach` and
-- `strongGate_of_fiveCarve`.  OWED: nothing in this folder proves it.
-- STANDING: OWED
def FiveReach : Prop :=
  ∀ (E : Finset ℝ) (m : ℝ), E.card ≤ 5 → 0 < m → (∀ d ∈ E, m ≤ d) →
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 6 / (8 * m) ∧ LonelyAt E s

/-- `FiveReach → FiveCarve`: `x < 17m/15` gives `6/(8m) ≤ 7/(8x)`. -/
theorem fiveCarve_of_fiveReach (h : FiveReach) : FiveCarve := by
  intro E m x hE hm hmx hx hlow
  obtain ⟨s, hs1, hs6, hsl⟩ := h E m hE hm hlow
  have hx0 : 0 < x := lt_trans hm hmx
  refine ⟨s, hs1, hs6.trans ?_, hsl⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

#print axioms fiveCarve_of_fiveReach

/-- The disparity set of an arrangement has at most seven elements. -/
theorem card_disparitySet_le (v : Fin 8 → ℝ) (k : Fin 8) : (disparitySet v k).card ≤ 7 := by
  -- [PROVISIONAL: counting tool] an image has at most as many elements as its domain (7 other runners); it supports
  -- the hypothesis `E.card ≤ 5` of `FiveCarve` in `strongGate_of_fiveCarve`.
  unfold disparitySet
  calc ((Finset.univ.erase k).image (fun i => |v i - v k|)).card ≤ (Finset.univ.erase k).card :=
        Finset.card_image_le
    _ = 7 := by simp

#print axioms card_disparitySet_le

/-- **The strong gate follows from the five-runner carving statement.**  [L] `FiveCarve → StrongGate`. -/
theorem strongGate_of_fiveCarve (h : FiveCarve) : Types.StrongGate := by
  intro v hv k m hmin n hle hgt y hy hwy
  by_contra hlate
  push Not at hlate
  have hpos := disparitySet_pos hv k
  have hmem : m ∈ disparitySet v k := hmin.1
  have hm : 0 < m := hpos m hmem
  have hlow : ∀ d ∈ disparitySet v k, m ≤ d := fun d hd => hmin.2 hd
  obtain ⟨x, hx, hxm, h15, hxy, hym, hyE, hcarve⟩ :=
    violation_carves hm hmem hlow (cascadeSeq_zero _ _) (cascadeSeq_isMove _ _) hle hgt hy hwy hlate
  set E := ((disparitySet v k).erase m).erase x with hE
  have hxne : x ≠ m := ne_of_gt hxm
  -- [PROVISIONAL: counting tool] removing `m` and `x` from a set of at most 7 elements leaves at most 5; supports the
  -- hypothesis `E.card ≤ 5` of `FiveCarve`.
  have hcard : E.card ≤ 5 := by
    have h1 : ((disparitySet v k).erase m).card = (disparitySet v k).card - 1 :=
      Finset.card_erase_of_mem hmem
    have h2 : E.card = ((disparitySet v k).erase m).card - 1 :=
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxne, hx⟩)
    have h3 := card_disparitySet_le v k
    omega
  have hElow : ∀ d ∈ E, m ≤ d := fun d hd => hlow d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd))
  obtain ⟨s, hs1, hs7, hsl⟩ := h E m x hcard hm hxm h15 hElow
  obtain ⟨d, hd, hwd⟩ := hcarve s hs1 hs7
  exact not_inWay_iff.mpr (hsl d hd) hwd

#print axioms strongGate_of_fiveCarve

/-! ## (4) Integer disparities: the mirror puts the first lonely instant at or before one half -/

/-- **Integer disparities: a lonely instant gives one in `(0, 1/2]`.**  By `t ↦ t - ⌊t⌋` (period) and `t ↦ 1 - t`
(mirror), `Types.int_lonely_shift`.  The instant is positive because an integer reading at `t = 0` is not clear.
For `d_min = m` a gate crosser then has its first lonely instant at `R = 8 m t ≤ 4 m`, i.e. in `R ∈ [9, 4m]`;
for `m ≤ 2` this is empty or contradicts the first window (`Types.no_crossing_of_small_dmin`); for `m = 3, 4, 5` it
leaves `R ∈ [9, 12]`, `[9, 16]`, `[9, 20]` and says nothing further. -/
theorem int_lonely_half {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {m : ℝ} (hmem : m ∈ ds)
    {t : ℝ} (hl : LonelyAt ds t) : ∃ s, 0 < s ∧ s ≤ 1 / 2 ∧ LonelyAt ds s := by
  set f := t + ((-⌊t⌋ : ℤ) : ℝ) with hf
  have hlf : LonelyAt ds f := (Types.int_lonely_shift hint (-⌊t⌋) hl).1
  have hf0 : 0 ≤ f := by rw [hf]; push_cast; linarith [Int.floor_le t]
  have hf1 : f < 1 := by rw [hf]; push_cast; linarith [Int.lt_floor_add_one t]
  -- `f ≠ 0`: otherwise `m · 0` is an integer reading
  have hfne : 0 < f := by
    rcases hf0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hlf m hmem
      rw [← h, mul_zero] at this
      have h0 : distInt 0 = 0 := by simp [distInt]
      rw [h0] at this
      norm_num at this
  by_cases hhalf : f ≤ 1 / 2
  · exact ⟨f, hfne, hhalf, hlf⟩
  · push Not at hhalf
    have hls : LonelyAt ds ((1 : ℤ) - f) := (Types.int_lonely_shift hint 1 hlf).2
    push_cast at hls
    exact ⟨1 - f, by linarith, by linarith, hls⟩

#print axioms int_lonely_half

/-! ## (5) Integer disparities: the arithmetic lonely instants `t = 1/q`, `q ≤ 8`

For integer disparities the instant `t = 1/q` (`q ≤ 8`) is lonely unless some disparity is a multiple of `q`: every
reading is then `z/q` with `q ∤ z`, a nonzero residue, hence at distance `≥ 1/q ≥ 1/8` from the nearest integer.  When
`1/(8m) ≤ 1/q ≤ 7/(8m)` this instant lies in the first window of `d_min`, so a gate crosser must contain a multiple of
`q`.  The bound `8m ≤ 7q ≤ 56` makes the condition vacuous for `m > 7`: that is why integer crossers begin at
`d_min = 6` (needs multiples of 7 and 8), `m = 7` needs a multiple of 8, and `m = 8` onward needs nothing; `m = 3, 4, 5`
additionally need multiples of 6 (`m ≤ 5`), 5 (`m ≤ 4`), 4 (`m ≤ 3`).  Real disparities have no such instants. -/

/-- A reading `z/q` with `q ∤ z` is at distance at least `1/q` from the nearest integer. -/
theorem distInt_div_ge {z : ℤ} {q : ℕ} (hq : 0 < q) (hz : ¬ (q : ℤ) ∣ z) :
    (1 / (q : ℝ)) ≤ distInt ((z : ℝ) / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold distInt
  set k := round ((z : ℝ) / q) with hk
  have hne : z - (q : ℤ) * k ≠ 0 := by
    intro h
    exact hz ⟨k, by linarith⟩
  have habs : (1 : ℤ) ≤ |z - (q : ℤ) * k| := Int.one_le_abs hne
  have habsr : (1 : ℝ) ≤ |((z - (q : ℤ) * k : ℤ) : ℝ)| := by exact_mod_cast habs
  have e : (z : ℝ) / q - (k : ℝ) = ((z - (q : ℤ) * k : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hq']
  exact div_le_div_of_nonneg_right habsr hq'.le

#print axioms distInt_div_ge

/-- **For integer disparities, `t = 1/q` (`1 ≤ q ≤ 8`) is lonely unless some disparity is a multiple of `q`.** -/
theorem lonely_at_inv_of_no_multiple {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {q : ℕ} (hq1 : 1 ≤ q)
    (hq8 : q ≤ 8) (hno : ∀ d ∈ ds, ∀ z : ℤ, d = z → ¬ (q : ℤ) ∣ z) : LonelyAt ds (1 / (q : ℝ)) := by
  intro d hd
  obtain ⟨z, rfl⟩ := hint d hd
  have h1 := distInt_div_ge (z := z) (by omega) (hno _ hd z rfl)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h2 : (1 / 8 : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hq0 (by exact_mod_cast hq8)
  have e : (z : ℝ) * (1 / (q : ℝ)) = (z : ℝ) / q := by ring
  rw [e]
  linarith

#print axioms lonely_at_inv_of_no_multiple

/-- **A gate crosser with integer disparities contains a multiple of every `q ≤ 8` with `8m/7 ≤ q ≤ 8m`.**  If a state of
the cascade from `1/(8m)` exceeds `7/(8m)` (`R > 7`), then for each such `q` some disparity is a multiple of `q`;
otherwise `t = 1/q` is a lonely instant in `[1/(8m), 7/(8m)]` and the cascade cannot pass it. -/
theorem crosser_needs_multiple {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ d ∈ ds, m ≤ d) (hcross : ∃ N, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) N)
    {q : ℕ} (hq1 : 1 ≤ q) (hq8 : q ≤ 8) (hqm : (q : ℝ) ≤ 8 * m) (hqm' : 8 * m ≤ 7 * q) :
    ∃ d ∈ ds, ∃ z : ℤ, d = z ∧ (q : ℤ) ∣ z := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hl := lonely_at_inv_of_no_multiple hint hq1 hq8 (fun d hd z hz => hcon d hd z hz)
  obtain ⟨N, hN⟩ := hcross
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlo : 1 / (8 * m) ≤ 1 / (q : ℝ) := one_div_le_one_div_of_le hq0 hqm
  have hhi : 1 / (q : ℝ) ≤ 7 / (8 * m) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]
    linarith
  have hseq := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact hlo) (cascadeSeq_isMove ds (1 / (8 * m))) N
  linarith

#print axioms crosser_needs_multiple

/-- `d_min = 7` (integer): a crosser contains a multiple of 8. -/
theorem crosser_dmin_seven {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) (hlow : ∀ d ∈ ds, 7 ≤ d)
    (hcross : ∃ N, 7 / (8 * 7) < cascadeSeq ds (1 / (8 * 7)) N) :
    ∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((8 : ℕ) : ℤ) ∣ z :=
  crosser_needs_multiple hint (by norm_num) hlow hcross (q := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- `d_min = 6` (integer): a crosser contains a multiple of 7 and a multiple of 8. -/
theorem crosser_dmin_six {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) (hlow : ∀ d ∈ ds, 6 ≤ d)
    (hcross : ∃ N, 7 / (8 * 6) < cascadeSeq ds (1 / (8 * 6)) N) :
    (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((7 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((8 : ℕ) : ℤ) ∣ z) :=
  ⟨crosser_needs_multiple hint (by norm_num) hlow hcross (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)⟩

/-- `d_min = 5` (integer): a crosser contains multiples of 6, of 7 and of 8. -/
theorem crosser_dmin_five {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) (hlow : ∀ d ∈ ds, 5 ≤ d)
    (hcross : ∃ N, 7 / (8 * 5) < cascadeSeq ds (1 / (8 * 5)) N) :
    (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((6 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((7 : ℕ) : ℤ) ∣ z) ∧
      (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((8 : ℕ) : ℤ) ∣ z) :=
  ⟨crosser_needs_multiple hint (by norm_num) hlow hcross (q := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)⟩

/-- `d_min = 4` (integer): a crosser contains multiples of 5, 6, 7 and 8. -/
theorem crosser_dmin_four {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) (hlow : ∀ d ∈ ds, 4 ≤ d)
    (hcross : ∃ N, 7 / (8 * 4) < cascadeSeq ds (1 / (8 * 4)) N) :
    (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((5 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((6 : ℕ) : ℤ) ∣ z) ∧
      (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((7 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((8 : ℕ) : ℤ) ∣ z) :=
  ⟨crosser_needs_multiple hint (by norm_num) hlow hcross (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)⟩

/-- `d_min = 3` (integer): a crosser contains multiples of 4, 5, 6, 7 and 8. -/
theorem crosser_dmin_three {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) (hlow : ∀ d ∈ ds, 3 ≤ d)
    (hcross : ∃ N, 7 / (8 * 3) < cascadeSeq ds (1 / (8 * 3)) N) :
    (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((4 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((5 : ℕ) : ℤ) ∣ z) ∧
      (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((6 : ℕ) : ℤ) ∣ z) ∧ (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((7 : ℕ) : ℤ) ∣ z) ∧
      (∃ d ∈ ds, ∃ z : ℤ, d = z ∧ ((8 : ℕ) : ℤ) ∣ z) :=
  ⟨crosser_needs_multiple hint (by norm_num) hlow hcross (q := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   crosser_needs_multiple hint (by norm_num) hlow hcross (q := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)⟩

#print axioms crosser_dmin_seven
#print axioms crosser_dmin_six
#print axioms crosser_dmin_five
#print axioms crosser_dmin_four
#print axioms crosser_dmin_three

end StrongGateStudy

end Fresh
