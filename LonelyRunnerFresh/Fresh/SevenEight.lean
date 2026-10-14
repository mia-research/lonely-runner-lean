import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Gate
import Fresh.Types
import Fresh.OneMultiple

/-!
# The gate at every lap, the strong gate, and the unit's opening arithmetic (Task CD)

Written 2026-10-10.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Gate` (which brings `Doors`,
`LonelyCells`, `Localisation`, `Dilation`, `ChainLaws`), `Types`, `OneMultiple`.  Nothing from the existing `LonelyRunner`
repo.  Exact reals; every disparity is positive (no runner is stationary).  Every statement is symbolic: for every finite
set `ds` of positive disparities with least element `m`; the cascade coordinate is `R = 8·m·t`.

Data: `experiments/n8/seven_eight_v1.py` and `seven_eight_v1.out` (exact integer cascade, move limits throughout).

## What is proved (grades [L]; each theorem has its `#print axioms` line)

* (1) The zone of `d_min` at every lap `k` (`Gate.dmin_inWay_gate` is `k = 1`): `dmin_inWay_zone` (for `R ∈ (8k-1, 8k+1)`
  the unit `m` is in the way and its next opening is exactly `R = 8k+1`), `no_lonely_in_zone`, `zone_move_ge` and
  `zone_lands_iff` (hypothesis `m ∈ ds`; `m` least is NOT REQUIRED), `first_state_above`, `zone_entry` (the first state above
  `R = 8k-1` lies in the zone; `m` least IS REQUIRED, see the report: `ds = {1, 9}`, `m = 9` skips the zone), `exceeds_iff`
  (a state above `B` exists iff there is no lonely instant in `[1/(8m), B]`), `endless_passes_zone` (an endless cascade
  passes through every zone), `landing_not_in_zone`, `landing_past_zone`, `zones_crossed_iff` (a landing in slot `j` crossed
  exactly the zones of laps `1, …, j`).
* (2) `StrongGateK ds m k` (definition): every cascade state in zone `k` moves to exactly `R = 8k+1`.
  `strongGateK_iff` (equivalent to: no runner in the way at such a state has its next opening beyond `R = 8k+1`, i.e.
  `d_min` is a setter of the move), `types_strongGate_of_all` (`StrongGateK ds m 1` for every finite set gives
  `Types.StrongGate`), `strongGateK_of_lonely_le` (vacuous when a lonely instant lies at or below the zone start: so
  `StrongGateK` for all `k` does NOT imply endless), `opening_visited` (zone `k` crossed and `StrongGateK ds m k`: the
  state `R = 8k+1` is visited and `d_min` sets the move into it), `visits_below_landing`, `endless_openings_blocked`,
  `endless_reset`, `fixed_at_state_iff`, `reset_fixes_iff`.
* (3) The unit's openings, arithmetic: `not_inWay_opening_iff` (for integers `d`, `m > 0`: `d` is clear at `(8k+1)/(8m)` iff
  `m ≤ d(8k+1) mod 8m ≤ 7m`), `inWay_opening_period` (period `m` in `k`), `inWay_opening_iff_of_dvd` (for `m ∣ d`: in the
  way iff `8m ∣ d`, independently of `k`), `inWay_opening_not_indep` (without `m ∣ d` the answer depends on `k`),
  `opening_lonely_iff`, `start_lonely_iff`, `endless_has_multiple` (grid, endless: a member is divisible by `8m`),
  `grid_unit_openings_dead` (grid, start not lonely: no opening of the unit is lonely), `ap_unit_openings`,
  `ap_multiple_blocks`.
* (4) Periodic closure: `inWay_add_period`, `nextOpening_add_period`, `isMove_add_period`, `cascadeSeq_add_period`,
  `cascadeSeq_add_P`, `cascadeSeq_periodic`, `strongGateK_of_period` (if the cascade closes up after `P` moves with a shift
  `c/m` of `t`, `d c/m ∈ ℤ`, and the strong gate holds for the states of one period, then `StrongGateK ds m k` for every
  `k ≥ 1`).

## What is not proved (see the report)

`Types.StrongGate` itself, and `StrongGateK` for any particular set outside the exact finite checks of
`seven_eight_v1.py`, are OWED.  No separating statement between seven and eight disparities in terms of the unit's openings
is proved (the report gives the exact reason: `grid_unit_openings_dead` and the data show the unit flank is dead for most
ended seven-sets too).  Rule 7: a counting step appears only inside `Doors.fixed_of_bddAbove`
(tagged there `[PROVISIONAL: counting tool]`, supporting "a cascade bounded above fixes"); it is marked at each use here.

Provenance (each proof written for this file).  (1) generalises `Gate.dmin_inWay_gate`, `Gate.no_lonely_in_gate`,
`Gate.gate_move_ge_nine`, `Gate.gate_lands_at_nine_iff`, `Gate.first_state_above_seven`, `Gate.exceeds_seven_iff`
(`k = 1`, `B = 7/(8m)`).  (2) is `Types.StrongGate` at lap `k`.  (3) corresponds to `Localisation.clear_iff_fract`
and the first-lap residue law used in `Boundaries.unit_lonely`.  I did not copy a proof I did not understand.
-/

open Classical

namespace Fresh

namespace SevenEight

open Cascade Dilation ChainLaws

/-! ## (1) The zone of the unit at every lap -/

/-- **The unit is in the way on the whole zone of lap `k`** [L]: for `m > 0`, an integer `k` and
`(8k-1)/(8m) < t < (8k+1)/(8m)` (in `R = 8mt`: `R ∈ (8k-1, 8k+1)`) the reading `m t` is within `1/8` of the lap `k`,
and the next opening of `m` is exactly `(8k+1)/(8m)`.  `k = 1` is `Gate.dmin_inWay_gate`.  Hypothesis `m > 0`: REQUIRED
(the division); `k ≥ 1`: NOT REQUIRED (any integer `k`; at `k ≤ 0` the zone contains no positive instant beyond `1/(8m)`). -/
theorem dmin_inWay_zone {m t : ℝ} (hm : 0 < m) (k : ℤ)
    (h1 : (8 * (k : ℝ) - 1) / (8 * m) < t) (h2 : t < (8 * (k : ℝ) + 1) / (8 * m)) :
    InWay m t ∧ nextOpening m t = (8 * (k : ℝ) + 1) / (8 * m) := by
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [lt_div_iff₀ (by positivity)] at h2
  have hk : |m * t - (k : ℝ)| < 1 / 8 := by
    rw [abs_lt]; constructor <;> nlinarith
  refine ⟨LonelyCells.inWay_of_near k hk, ?_⟩
  rw [nextOpening_eq hk]
  field_simp

#print axioms dmin_inWay_zone

/-- **No instant of the zone is lonely** [L]: if `m ∈ ds`, no `t` with `(8k-1)/(8m) < t < (8k+1)/(8m)` is lonely.
Hypothesis `m ∈ ds`: REQUIRED (it is `d_min`'s own reading that blocks). -/
theorem no_lonely_in_zone {ds : Finset ℝ} {m t : ℝ} (hm : m ∈ ds) (hm0 : 0 < m) (k : ℤ)
    (h1 : (8 * (k : ℝ) - 1) / (8 * m) < t) (h2 : t < (8 * (k : ℝ) + 1) / (8 * m)) : ¬ LonelyAt ds t :=
  fun hl => (not_inWay_iff.mpr (hl m hm)) (dmin_inWay_zone hm0 k h1 h2).1

#print axioms no_lonely_in_zone

/-- **The move out of the zone** [L]: from a state in the zone of lap `k` the move reaches `R ≥ 8k+1`.
`k = 1` is `Gate.gate_move_ge_nine`. -/
theorem zone_move_ge {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (k : ℤ)
    {s₀ s₁ : ℝ} (h1 : (8 * (k : ℝ) - 1) / (8 * m) < s₀) (h2 : s₀ < (8 * (k : ℝ) + 1) / (8 * m))
    (hmv : IsMove ds s₀ s₁) : (8 * (k : ℝ) + 1) / (8 * m) ≤ s₁ := by
  obtain ⟨hw, ho⟩ := dmin_inWay_zone (hpos m hm) k h1 h2
  rcases hmv with ⟨hn, _⟩ | ⟨x, hx, hwx, he, hmax⟩
  · exact absurd hw (hn m hm)
  · rw [← ho]; exact hmax m hm hw

#print axioms zone_move_ge

/-- **The move out of the zone lands exactly at `R = 8k+1` iff `d_min` is a setter** [L]: iff no runner in the way at
the zone state has its next opening beyond `R = 8k+1`.  `k = 1` is `Gate.gate_lands_at_nine_iff`. -/
theorem zone_lands_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (k : ℤ)
    {s₀ s₁ : ℝ} (h1 : (8 * (k : ℝ) - 1) / (8 * m) < s₀) (h2 : s₀ < (8 * (k : ℝ) + 1) / (8 * m))
    (hmv : IsMove ds s₀ s₁) :
    s₁ = (8 * (k : ℝ) + 1) / (8 * m) ↔
      ∀ y ∈ ds, InWay y s₀ → nextOpening y s₀ ≤ (8 * (k : ℝ) + 1) / (8 * m) := by
  obtain ⟨hw, ho⟩ := dmin_inWay_zone (hpos m hm) k h1 h2
  rcases hmv with ⟨hn, _⟩ | ⟨x, hx, hwx, he, hmax⟩
  · exact absurd hw (hn m hm)
  · constructor
    · intro h y hy hwy
      rw [← h]; exact hmax y hy hwy
    · intro h
      apply le_antisymm
      · rw [he]; exact (ho ▸ h x hx hwx)
      · rw [← ho]; exact hmax m hm hw

#print axioms zone_lands_iff

/-- **The first state above any bound `B ≥ 1/(8m)`** [L]: if some cascade state exceeds `B`, there is a step `n` with
every state up to `n` at most `B` and `seq (n+1)` in `(B, B + 2/(8m))` (the gap bound: a move advances `R` by less than
`2`).  With `B = (8k-1)/(8m)` the interval is the zone of lap `k`.  `B = 7/(8m)` is `Gate.first_state_above_seven`. -/
theorem first_state_above {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) {B : ℝ}
    (hB : 1 / (8 * m) ≤ B) (h : ∃ n, B < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ n, (∀ i ≤ n, cascadeSeq ds (1 / (8 * m)) i ≤ B) ∧ B < cascadeSeq ds (1 / (8 * m)) (n + 1) ∧
      cascadeSeq ds (1 / (8 * m)) (n + 1) < B + 2 / (8 * m) := by
  have hm0 := Gate.least_pos hpos hm
  set seq := cascadeSeq ds (1 / (8 * m)) with hseq
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  let n₀ := Nat.find h
  have hn₀ : B < seq n₀ := Nat.find_spec h
  have hmin : ∀ i < n₀, seq i ≤ B := fun i hi => by
    have := Nat.find_min h hi
    push Not at this
    exact this
  have hne : n₀ ≠ 0 := by
    intro h0
    rw [h0, hseq, cascadeSeq_zero] at hn₀
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨n, fun i hi => hmin i (by omega), by rw [show n + 1 = n₀ from hn.symm]; exact hn₀, ?_⟩
  have := Gate.move_lt_add_quarter hm0 (fun d hd => hm.2 hd) (hmv n)
  have h2 := hmin n (by omega)
  linarith

#print axioms first_state_above

/-- **A state above `B` exists iff no lonely instant lies in `[1/(8m), B]`** [L].  `B = 7/(8m)` is
`Gate.exceeds_seven_iff`.  The `←` direction uses `Doors.fixed_of_bddAbove`,
**[PROVISIONAL: counting tool]** (tagged there; it supports "a cascade bounded above fixes", no existence claim). -/
theorem exceeds_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) (B : ℝ) :
    (∃ n, B < cascadeSeq ds (1 / (8 * m)) n) ↔
      ¬ ∃ t, 1 / (8 * m) ≤ t ∧ t ≤ B ∧ LonelyAt ds t := by
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  constructor
  · rintro ⟨n, hn⟩ ⟨t, h1, h7, hl⟩
    have := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact h1) hmv n
    linarith
  · intro h
    by_contra hc
    push Not at hc
    -- [PROVISIONAL: counting tool] inside `Doors.fixed_of_bddAbove`, supporting "a cascade bounded by `B` fixes".
    obtain ⟨N, hN⟩ := Doors.fixed_of_bddAbove hpos hm.1 ⟨B, by rintro _ ⟨n, rfl⟩; exact hc n⟩
    exact h ⟨_, by have := start_le_seq hpos hmv N; rwa [cascadeSeq_zero] at this, hc N,
      by have hh := hmv N; rw [hN] at hh; exact (isMove_self_iff hpos).mp hh⟩

#print axioms exceeds_iff

/-- **Zone entry at lap `k ≥ 1`** [L]: if some state exceeds `(8k-1)/(8m)`, there is a step `n` with every state up to
`n` at most `(8k-1)/(8m)`, the state `seq (n+1)` inside the zone `((8k-1)/(8m), (8k+1)/(8m))`, `m` in the way there with
next opening `(8k+1)/(8m)`, and `seq (n+2) ≥ (8k+1)/(8m)`.  So a cascade that gets past `R = 8k-1` passes through the
zone of lap `k`; `k = 1` is `Types.gate_crossing`/`Gate.first_state_above_seven` with `Gate.gate_move_ge_nine`.
Hypothesis `k ≥ 1`: REQUIRED for this form (the start `R = 1` must lie at or below `8k-1`). -/
theorem zone_entry {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) {k : ℕ}
    (hk : 1 ≤ k) (h : ∃ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ n, (∀ i ≤ n, cascadeSeq ds (1 / (8 * m)) i ≤ (8 * (k : ℝ) - 1) / (8 * m)) ∧
      (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) (n + 1) ∧
      cascadeSeq ds (1 / (8 * m)) (n + 1) < (8 * (k : ℝ) + 1) / (8 * m) ∧
      InWay m (cascadeSeq ds (1 / (8 * m)) (n + 1)) ∧
      nextOpening m (cascadeSeq ds (1 / (8 * m)) (n + 1)) = (8 * (k : ℝ) + 1) / (8 * m) ∧
      (8 * (k : ℝ) + 1) / (8 * m) ≤ cascadeSeq ds (1 / (8 * m)) (n + 2) := by
  have hm0 := Gate.least_pos hpos hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 1 / (8 * m) ≤ (8 * (k : ℝ) - 1) / (8 * m) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨n, hle, hgt, hlt⟩ := first_state_above hpos hm hB h
  have e : (8 * (k : ℝ) - 1) / (8 * m) + 2 / (8 * m) = (8 * (k : ℝ) + 1) / (8 * m) := by
    field_simp; ring
  have hlt' : cascadeSeq ds (1 / (8 * m)) (n + 1) < (8 * (k : ℝ) + 1) / (8 * m) := by linarith
  obtain ⟨hw, ho⟩ := dmin_inWay_zone hm0 (k : ℤ) (by exact_mod_cast hgt) (by exact_mod_cast hlt')
  refine ⟨n, hle, hgt, hlt', hw, by exact_mod_cast ho, ?_⟩
  exact_mod_cast zone_move_ge hpos hm.1 (k : ℤ) (by exact_mod_cast hgt) (by exact_mod_cast hlt')
    (cascadeSeq_isMove ds (1 / (8 * m)) (n + 1))

#print axioms zone_entry

/-- **An endless cascade passes through every zone** [L]: if the cascade from `1/(8m)` never reaches a fixed step,
then for every lap `k ≥ 1` some state lies in the zone `((8k-1)/(8m), (8k+1)/(8m))`.  Uses `Doors.fixed_of_bddAbove`,
**[PROVISIONAL: counting tool]** (an unbounded run), supporting "an endless cascade is unbounded". -/
theorem endless_passes_zone {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    (hend : ¬ ∃ N, cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) {k : ℕ} (hk : 1 ≤ k) :
    ∃ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) (n + 1) ∧
      cascadeSeq ds (1 / (8 * m)) (n + 1) < (8 * (k : ℝ) + 1) / (8 * m) := by
  have h : ∃ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n := by
    by_contra hc
    push Not at hc
    -- [PROVISIONAL: counting tool] via `Doors.fixed_of_bddAbove`: a cascade bounded above fixes.
    exact hend (Doors.fixed_of_bddAbove hpos hm.1 ⟨_, by rintro _ ⟨n, rfl⟩; exact hc n⟩)
  obtain ⟨n, -, h1, h2, -⟩ := zone_entry hpos hm hk h
  exact ⟨n, h1, h2⟩

#print axioms endless_passes_zone

/-- **Landing never lies in a zone** [L]: a fixed step of the cascade is not in any zone `((8k-1)/(8m), (8k+1)/(8m))`
(`Gate.landing_not_in_gate` for every lap). -/
theorem landing_not_in_zone {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) (k : ℤ)
    {N : ℕ} (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) :
    ¬ ((8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) N ∧
      cascadeSeq ds (1 / (8 * m)) N < (8 * (k : ℝ) + 1) / (8 * m)) := by
  rintro ⟨h1, h2⟩
  have h := cascadeSeq_isMove ds (1 / (8 * m)) N
  rw [hN] at h
  exact no_lonely_in_zone hm.1 (Gate.least_pos hpos hm) k h1 h2 ((isMove_self_iff hpos).mp h)

#print axioms landing_not_in_zone

/-- **The landing past a zone start is past the zone** [L]: if the cascade fixes at `N` and its landing exceeds
`(8k-1)/(8m)`, then it is at least `(8k+1)/(8m)` (`R ≥ 8k+1`). -/
theorem landing_past_zone {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) (k : ℤ)
    {N : ℕ} (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N)
    (h : (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) N) :
    (8 * (k : ℝ) + 1) / (8 * m) ≤ cascadeSeq ds (1 / (8 * m)) N := by
  by_contra hc
  exact landing_not_in_zone hpos hm k hN ⟨h, not_le.mp hc⟩

#print axioms landing_past_zone

/-- **Which zones a landing in slot `j` crossed** [L]: if the cascade fixes at `N` with landing `L`, and
`8j+1 ≤ 8mL ≤ 8j+7` (`lonely_slot` gives such a `j`), then for every `k : ℕ` (`k ≥ 1` NOT REQUIRED) some state exceeds `(8k-1)/(8m)` iff `k ≤ j`.
So the zones crossed are exactly laps `1, …, j`. -/
theorem zones_crossed_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) {j : ℤ}
    {N : ℕ} (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N)
    (hlo : 8 * (j : ℝ) + 1 ≤ 8 * m * cascadeSeq ds (1 / (8 * m)) N)
    (hhi : 8 * m * cascadeSeq ds (1 / (8 * m)) N ≤ 8 * (j : ℝ) + 7) (k : ℕ) :
    (∃ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) ↔ (k : ℤ) ≤ j := by
  have hm0 := Gate.least_pos hpos hm
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  have hl : LonelyAt ds (cascadeSeq ds (1 / (8 * m)) N) := by
    have h := hmv N
    rw [hN] at h
    exact (isMove_self_iff hpos).mp h
  constructor
  · rintro ⟨n, hn⟩
    have hle := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact start_le_seq hpos hmv N |>.trans_eq' (by rw [cascadeSeq_zero])) hmv n
    have h1 : (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) N := lt_of_lt_of_le hn hle
    rw [div_lt_iff₀ (by positivity)] at h1
    have : (k : ℝ) < j + 1 := by nlinarith
    have : (k : ℤ) < j + 1 := by exact_mod_cast this
    omega
  · intro hkj
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have : (k : ℝ) ≤ j := by exact_mod_cast hkj
    nlinarith

#print axioms zones_crossed_iff

/-! ## (2) The strong gate at lap `k` -/

/-- **`StrongGateK ds m k`**: every state of the cascade from `1/(8m)` that lies in the zone of lap `k` moves to exactly
`(8k+1)/(8m)` (`R = 8k+1`).  `Types.StrongGate` (OWED) is the statement for the first crossing at `k = 1`; by
`zone_move_ge` the move out of the zone is never earlier than `R = 8k+1`, and by `zone_lands_iff` the equality says that
`d_min` is a setter. -/
-- STANDING: DEFINITION
def StrongGateK (ds : Finset ℝ) (m : ℝ) (k : ℕ) : Prop :=
  ∀ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n →
    cascadeSeq ds (1 / (8 * m)) n < (8 * (k : ℝ) + 1) / (8 * m) →
    cascadeSeq ds (1 / (8 * m)) (n + 1) = (8 * (k : ℝ) + 1) / (8 * m)

/-- **`StrongGateK` is "no late blocker"** [L]: equivalent to: at every cascade state in the zone of lap `k`, every
runner in the way has its next opening at or before `R = 8k+1`. -/
theorem strongGateK_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (k : ℕ) :
    StrongGateK ds m k ↔ ∀ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n →
      cascadeSeq ds (1 / (8 * m)) n < (8 * (k : ℝ) + 1) / (8 * m) →
      ∀ y ∈ ds, InWay y (cascadeSeq ds (1 / (8 * m)) n) →
        nextOpening y (cascadeSeq ds (1 / (8 * m)) n) ≤ (8 * (k : ℝ) + 1) / (8 * m) := by
  constructor
  · intro h n h1 h2
    have := (zone_lands_iff hpos hm (k : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2)
      (cascadeSeq_isMove ds (1 / (8 * m)) n)).mp (by exact_mod_cast h n h1 h2)
    exact_mod_cast this
  · intro h n h1 h2
    have := (zone_lands_iff hpos hm (k : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2)
      (cascadeSeq_isMove ds (1 / (8 * m)) n)).mpr (by exact_mod_cast h n h1 h2)
    exact_mod_cast this

#print axioms strongGateK_iff

/-- **`Types.StrongGate` follows from `StrongGateK ds m 1` for every finite set** [L]: if for every finite set of positive
disparities with least element `m` the cascade from `1/(8m)` satisfies `StrongGateK ds m 1`, then `Types.StrongGate`.
(The converse is not formalised here; `Types.StrongGate` quantifies over disparity sets of arrangements.) -/
theorem types_strongGate_of_all
    (h : ∀ (ds : Finset ℝ) (m : ℝ), (∀ d ∈ ds, 0 < d) → IsLeast (ds : Set ℝ) m → StrongGateK ds m 1) :
    Types.StrongGate := by
  intro v hv k m hm n hle hgt y hy hwy
  have hpos := Cascade.disparitySet_pos hv k
  have hm' : IsLeast (disparitySet v k : Set ℝ) m := hm
  have hm0 := Gate.least_pos hpos hm'
  have hmv := cascadeSeq_isMove (disparitySet v k) (1 / (8 * m))
  have hlt := Gate.move_from_first_window hm0 (fun d hd => hm'.2 hd) hle (hmv n)
  have e7 : (8 * ((1 : ℕ) : ℝ) - 1) / (8 * m) = 7 / (8 * m) := by norm_num
  have e9 : (8 * ((1 : ℕ) : ℝ) + 1) / (8 * m) = 9 / (8 * m) := by norm_num
  have key := (strongGateK_iff hpos hm'.1 1).mp (h _ m hpos hm') (n + 1)
    (by rw [e7]; exact hgt) (by rw [e9]; exact hlt) y hy hwy
  rw [e9] at key
  exact key

#print axioms types_strongGate_of_all

/-- **`StrongGateK` is vacuous below the landing** [L]: if a lonely instant `t₁ ≥ 1/(8m)` exists with
`t₁ ≤ (8k-1)/(8m)`, the cascade never enters zone `k`, so `StrongGateK ds m k` holds.  Hence `StrongGateK` for all `k`
does not imply that the cascade is endless (every ended cascade satisfies it for the laps beyond its landing). -/
theorem strongGateK_of_lonely_le {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} {t₁ : ℝ}
    (hl : LonelyAt ds t₁) (h0 : 1 / (8 * m) ≤ t₁) (k : ℕ) (hle : t₁ ≤ (8 * (k : ℝ) - 1) / (8 * m)) :
    StrongGateK ds m k := by
  intro n h1 _
  have := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact h0) (cascadeSeq_isMove ds (1 / (8 * m))) n
  linarith

#print axioms strongGateK_of_lonely_le

/-- **The opening of the unit is visited, and the unit sets the move into it** [L]: if `StrongGateK ds m k` (`k ≥ 1`) and
some state exceeds `(8k-1)/(8m)`, then some state is exactly `(8k+1)/(8m)` and `d_min` is the setter of the move into it
(`IsSetterAt`).  This is `ρ_{d_min} = 1` at lap `k` (the observation of Task BG), as a consequence of the strong gate. -/
theorem opening_visited {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) {k : ℕ}
    (hk : 1 ≤ k) (hs : StrongGateK ds m k)
    (h : ∃ n, (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ n, cascadeSeq ds (1 / (8 * m)) (n + 2) = (8 * (k : ℝ) + 1) / (8 * m) ∧
      IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) (n + 1) m := by
  obtain ⟨n, -, h1, h2, hw, ho, -⟩ := zone_entry hpos hm hk h
  have e := hs (n + 1) h1 h2
  exact ⟨n, e, hm.1, hw, by rw [e, ho]⟩

#print axioms opening_visited

/-- **Every opening below the landing is a state** [L]: if the cascade fixes at `N`, `k ≥ 1`, `StrongGateK ds m k`
and the landing exceeds `(8k-1)/(8m)`, then `(8k+1)/(8m) ≤` landing and some state equals `(8k+1)/(8m)`, set by `d_min`. -/
theorem visits_below_landing {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) {k : ℕ}
    (hk : 1 ≤ k) (hs : StrongGateK ds m k) {N : ℕ}
    (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N)
    (h : (8 * (k : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) N) :
    (8 * (k : ℝ) + 1) / (8 * m) ≤ cascadeSeq ds (1 / (8 * m)) N ∧
      ∃ n, cascadeSeq ds (1 / (8 * m)) (n + 2) = (8 * (k : ℝ) + 1) / (8 * m) ∧
        IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) (n + 1) m :=
  ⟨by exact_mod_cast landing_past_zone hpos hm (k : ℤ) hN (by exact_mod_cast h),
    opening_visited hpos hm hk hs ⟨N, h⟩⟩

#print axioms visits_below_landing

/-- **In an endless cascade every opening of the unit is blocked** [L]: if the cascade from `1/(8m)` never fixes, then for
every `k` some runner of `ds` is in the way at `(8k+1)/(8m)`.  (No lonely instant exists at all, in particular none at an
opening of `d_min`; the AP case: the multiple of `8` blocks every opening.)  Uses `Doors.fixed_of_bddAbove`,
**[PROVISIONAL: counting tool]** (tagged there), supporting "a bounded cascade fixes". -/
theorem endless_openings_blocked {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hend : ¬ ∃ N, cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) (k : ℕ) :
    ∃ y ∈ ds, InWay y ((8 * (k : ℝ) + 1) / (8 * m)) := by
  have hm0 := hpos m hm
  by_contra hc
  push Not at hc
  have hl : LonelyAt ds ((8 * (k : ℝ) + 1) / (8 * m)) := fun y hy => not_inWay_iff.mp (hc y hy)
  have h0 : 1 / (8 * m) ≤ (8 * (k : ℝ) + 1) / (8 * m) :=
    div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by positivity)
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  exact hend (Doors.fixed_of_bddAbove hpos hm ⟨_, by
    rintro _ ⟨n, rfl⟩; exact seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact h0) hmv n⟩)

#print axioms endless_openings_blocked

/-- **Endless and strong at lap `k`: the reset** [L]: if the cascade never fixes and `StrongGateK ds m k` (`k ≥ 1`), the
state `(8k+1)/(8m)` is visited, `d_min` sets the move into it, and some runner is in the way there (so the cascade
leaves it).  The four assertions are the observations of Task BG (`ρ_{d_min} = 1`) at lap `k`. -/
theorem endless_reset {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    (hend : ¬ ∃ N, cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) {k : ℕ} (hk : 1 ≤ k)
    (hs : StrongGateK ds m k) :
    ∃ n, cascadeSeq ds (1 / (8 * m)) (n + 2) = (8 * (k : ℝ) + 1) / (8 * m) ∧
      IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) (n + 1) m ∧
      ∃ y ∈ ds, InWay y (cascadeSeq ds (1 / (8 * m)) (n + 2)) := by
  obtain ⟨n, hn⟩ := endless_passes_zone hpos hm hend hk
  obtain ⟨n', e, hset⟩ := opening_visited hpos hm hk hs ⟨n + 1, hn.1⟩
  refine ⟨n', e, hset, ?_⟩
  rw [e]
  exact endless_openings_blocked hpos hm.1 hend k

#print axioms endless_reset

/-! ## (3) The openings of the unit: arithmetic of the readings -/

/-- A residue form of "clear": for an integer `x` and a positive `N`, `x/N` reads at least `1/8` from a lap line iff
`N ≤ 8 (x mod N) ≤ 7 N` [L]. -/
theorem clear_div_iff (x : ℤ) (N : ℕ) (hN : 0 < N) :
    (1 / 8 : ℝ) ≤ distInt ((x : ℝ) / (N : ℝ)) ↔
      (N : ℤ) ≤ 8 * (x % (N : ℤ)) ∧ 8 * (x % (N : ℤ)) ≤ 7 * (N : ℤ) := by
  rw [Localisation.clear_iff_fract, Int.fract_div_intCast_eq_div_intCast_mod]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr, div_le_iff₀ hNr]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (N : ℝ) ≤ 8 * ((x % (N : ℤ) : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : 8 * ((x % (N : ℤ) : ℤ) : ℝ) ≤ 7 * (N : ℝ) := by linarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (N : ℝ) ≤ 8 * ((x % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2' : 8 * ((x % (N : ℤ) : ℤ) : ℝ) ≤ 7 * (N : ℝ) := by exact_mod_cast h2
    constructor <;> linarith

#print axioms clear_div_iff

/-- **The reading of `d` at the opening `(8k+1)/(8m)` of the unit** [L]: for integers `d`, `k` and `m > 0`,
`d` is NOT in the way at `(8k+1)/(8m)` iff `m ≤ (d (8k+1)) mod 8m ≤ 7 m`.  Hypotheses: `m > 0` REQUIRED; `d` an
integer REQUIRED for the residue form (the real-valued reading is `d (8k+1)/(8m)`). -/
theorem not_inWay_opening_iff (d : ℤ) (m : ℕ) (hm : 0 < m) (k : ℤ) :
    ¬ InWay (d : ℝ) ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) ↔
      (m : ℤ) ≤ (d * (8 * k + 1)) % (8 * (m : ℤ)) ∧ (d * (8 * k + 1)) % (8 * (m : ℤ)) ≤ 7 * (m : ℤ) := by
  have hN : 0 < 8 * m := by omega
  have e : (d : ℝ) * ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) = ((d * (8 * k + 1) : ℤ) : ℝ) / ((8 * m : ℕ) : ℝ) := by
    push_cast; ring
  rw [InWay, not_lt, e, clear_div_iff _ _ hN]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

#print axioms not_inWay_opening_iff

/-- **Period `m` in `k`** [L]: the reading of `d` at the opening `(8k+1)/(8m)` of the unit depends on `k` only mod `m`
(the unit flank is a finite check over `k = 0, …, m-1`; `m` is `d_min`). -/
theorem inWay_opening_period (d : ℤ) (m : ℕ) (hm : 0 < m) (k : ℤ) :
    InWay (d : ℝ) ((8 * ((k + m : ℤ) : ℝ) + 1) / (8 * (m : ℝ))) ↔ InWay (d : ℝ) ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) := by
  rw [← not_iff_not, not_inWay_opening_iff d m hm, not_inWay_opening_iff d m hm]
  have e : d * (8 * (k + m) + 1) = d * (8 * k + 1) + (8 * (m : ℤ)) * d := by ring
  rw [e, Int.add_mul_emod_self_left]

#print axioms inWay_opening_period

/-- **A multiple of `m` against the unit's openings** [L]: if `m ∣ d` then `d` is in the way at the opening
`(8k+1)/(8m)` iff `8m ∣ d`, the same for every `k`.  (For `d = m q`: the reading is `q(8k+1)/8`, congruent to `q/8`
mod 1, so `d` is clear iff `8 ∤ q`.)  Hypothesis `m ∣ d`: REQUIRED for the independence of `k` (see
`inWay_opening_not_indep`). -/
theorem inWay_opening_iff_of_dvd (d : ℤ) (m : ℕ) (hm : 0 < m) (hd : (m : ℤ) ∣ d) (k : ℤ) :
    InWay (d : ℝ) ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) ↔ 8 * (m : ℤ) ∣ d := by
  obtain ⟨q, rfl⟩ := hd
  rw [← not_iff_not, not_inWay_opening_iff _ m hm]
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have e : (m : ℤ) * q * (8 * k + 1) = (m : ℤ) * (q * (8 * k + 1)) := by ring
  rw [e, show (8 : ℤ) * m = m * 8 by ring, Int.mul_emod_mul_of_pos _ _ hm']
  have e2 : q * (8 * k + 1) % 8 = q % 8 := by
    rw [show q * (8 * k + 1) = q + 8 * (q * k) by ring, Int.add_mul_emod_self_left]
  rw [e2]
  constructor
  · rintro ⟨h1, h2⟩ h
    obtain ⟨c, hc⟩ := h
    have : q % 8 = 0 := by
      have : (m : ℤ) * q = (m * 8) * c := hc
      have : q = 8 * c := by nlinarith
      omega
    rw [this] at h1
    nlinarith
  · intro h
    have h8 : q % 8 ≠ 0 := fun h0 => h ⟨q / 8, by
      have : q = 8 * (q / 8) := by omega
      conv_lhs => rw [this]
      ring⟩
    have hlo : 1 ≤ q % 8 := by omega
    have hhi : q % 8 ≤ 7 := by omega
    constructor <;> nlinarith

#print axioms inWay_opening_iff_of_dvd

/-- **The unit's opening is lonely iff no member is a multiple of `8m`** [L]: for a finite set `ds` of integer
disparities that are all multiples of `m > 0` (the grid case `g = d_min`), the opening `(8k+1)/(8m)` of the unit is lonely
iff no member is divisible by `8m`; the answer is the same for every `k`.  For `m = 1` (the AP residues): iff no member is
`≡ 0 (mod 8)`. -/
theorem opening_lonely_iff (ds : Finset ℝ) (m : ℕ) (hm : 0 < m) (hds : ∀ d ∈ ds, ∃ z : ℤ, d = (z : ℝ) ∧ (m : ℤ) ∣ z)
    (k : ℤ) :
    LonelyAt ds ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) ↔ ∀ d ∈ ds, ∀ z : ℤ, d = (z : ℝ) → ¬ 8 * (m : ℤ) ∣ z := by
  constructor
  · intro hl d hd z hz hdz
    have h1 := hl d hd
    obtain ⟨z', hz', hmz⟩ := hds d hd
    have : z = z' := by
      have : (z : ℝ) = z' := hz ▸ hz'
      exact_mod_cast this
    subst this
    have hw := (inWay_opening_iff_of_dvd z m hm hmz k).mpr hdz
    rw [hz'] at h1
    exact (not_inWay_iff.mpr h1) hw
  · intro h d hd
    obtain ⟨z, hz, hmz⟩ := hds d hd
    rw [← not_inWay_iff, hz]
    intro hw
    exact h d hd z hz ((inWay_opening_iff_of_dvd z m hm hmz k).mp hw)

#print axioms opening_lonely_iff

/-- **Hypothesis audit: `m ∣ d` is required for independence of `k`** [L]: with `m = 3`, `d = 7` (`3 ∤ 7`): `7` is clear
at the opening `k = 0` (`7 mod 24 = 7 ∈ [3, 21]`) and in the way at `k = 2` (`7·17 mod 24 = 23 > 21`), so without `m ∣ d`
the answer depends on `k` (it is periodic of period `m`, `inWay_opening_period`). -/
theorem inWay_opening_not_indep :
    ¬ InWay ((7 : ℤ) : ℝ) ((8 * ((0 : ℤ) : ℝ) + 1) / (8 * ((3 : ℕ) : ℝ))) ∧
    InWay ((7 : ℤ) : ℝ) ((8 * ((2 : ℤ) : ℝ) + 1) / (8 * ((3 : ℕ) : ℝ))) := by
  refine ⟨?_, ?_⟩
  · rw [not_inWay_opening_iff 7 3 (by norm_num) 0]; norm_num
  · rw [← not_not (a := InWay _ _), not_inWay_opening_iff 7 3 (by norm_num) 2]; norm_num

#print axioms inWay_opening_not_indep

/-- **The start `R = 1` is lonely iff no member is a multiple of `8m`** [L]: for integer multiples of `m > 0`, the
cascade's starting instant `1/(8m)` (the opening `k = 0` of the unit) is lonely iff no member is divisible by `8m`. -/
theorem start_lonely_iff (ds : Finset ℝ) (m : ℕ) (hm : 0 < m) (hds : ∀ d ∈ ds, ∃ z : ℤ, d = (z : ℝ) ∧ (m : ℤ) ∣ z) :
    LonelyAt ds (1 / (8 * (m : ℝ))) ↔ ∀ d ∈ ds, ∀ z : ℤ, d = (z : ℝ) → ¬ 8 * (m : ℤ) ∣ z := by
  have := opening_lonely_iff ds m hm hds 0
  simpa using this

#print axioms start_lonely_iff

/-- **An endless cascade of integer multiples of `m` contains a multiple of `8m`** [L]: if every member of `ds` is an
integer multiple of `m > 0`, `m ∈ ds`, every disparity is positive, and the cascade from `1/(8m)` never fixes, then some
member is divisible by `8m`.  (In units of `m = 1`: a multiple of `8`; the AP residue `0 (mod 8)`.)  Hypothesis audit:
`m ∈ ds` REQUIRED (it fixes the start); the grid hypothesis (every member a multiple of `m`) REQUIRED for the lemma used
(`opening_lonely_iff`), and whether the conclusion survives without it is UNDECIDED (the 43 endless 8-sets with
`a ≤ 40` all have `m = g`, so none tests it).  Uses `Doors.fixed_of_bddAbove`, **[PROVISIONAL: counting tool]** (tagged
there). -/
theorem endless_has_multiple (ds : Finset ℝ) (m : ℕ) (hm : 0 < m) (hmem : (m : ℝ) ∈ ds)
    (hpos : ∀ d ∈ ds, 0 < d) (hds : ∀ d ∈ ds, ∃ z : ℤ, d = (z : ℝ) ∧ (m : ℤ) ∣ z)
    (hend : ¬ ∃ N, cascadeSeq ds (1 / (8 * (m : ℝ))) (N + 1) = cascadeSeq ds (1 / (8 * (m : ℝ))) N) :
    ∃ d ∈ ds, ∃ z : ℤ, d = (z : ℝ) ∧ 8 * (m : ℤ) ∣ z := by
  obtain ⟨y, hy, hw⟩ := endless_openings_blocked hpos hmem hend 0
  by_contra hc
  push Not at hc
  have hl := (start_lonely_iff ds m hm hds).mpr (fun d hd z hz => hc d hd z hz)
  have e : (8 * ((0 : ℕ) : ℝ) + 1) / (8 * (m : ℝ)) = 1 / (8 * (m : ℝ)) := by simp
  rw [e] at hw
  exact (not_inWay_iff.mpr (hl y hy)) hw

#print axioms endless_has_multiple

/-- **A state is a fixed point iff it is lonely** [L]: `cascadeSeq ds t₀ (n+1) = cascadeSeq ds t₀ n` iff the state is lonely. -/
theorem fixed_at_state_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (t₀ : ℝ) (n : ℕ) :
    cascadeSeq ds t₀ (n + 1) = cascadeSeq ds t₀ n ↔ LonelyAt ds (cascadeSeq ds t₀ n) := by
  constructor
  · intro h
    have := cascadeSeq_isMove ds t₀ n
    rw [h] at this
    exact (isMove_self_iff hpos).mp this
  · intro h
    exact isMove_unique (cascadeSeq_isMove ds t₀ n) ((isMove_self_iff hpos).mpr h)

#print axioms fixed_at_state_iff

/-- **A reset is the landing iff the unit's opening is lonely** [L]: if the state `seq (n+2)` equals `(8k+1)/(8m)` (the
reset of `opening_visited`), the cascade fixes there iff every reading is clear at `(8k+1)/(8m)`. -/
theorem reset_fixes_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} {k n : ℕ}
    (h : cascadeSeq ds (1 / (8 * m)) (n + 2) = (8 * (k : ℝ) + 1) / (8 * m)) :
    cascadeSeq ds (1 / (8 * m)) (n + 3) = cascadeSeq ds (1 / (8 * m)) (n + 2) ↔
      LonelyAt ds ((8 * (k : ℝ) + 1) / (8 * m)) := by
  rw [fixed_at_state_iff hpos _ (n + 2), h]

#print axioms reset_fixes_iff

/-- **In the grid case the unit's openings are never lonely once the start is not** [L]: if every member of `ds` is an
integer multiple of `m > 0` and the start `1/(8m)` is not lonely (the cascade moves at least once), then no opening
`(8k+1)/(8m)`, `k ∈ ℤ`, is lonely.  So for grid sets the first isolation is never at the unit's own opening (a lonely instant
is the candidate scale of another flank).  The grid hypothesis: REQUIRED here; for non-grid sets the data differ (22 of the 47
integer 7-set crossers land at `R = 9`, the unit's opening `k = 1`; none of them is a grid set). -/
theorem grid_unit_openings_dead (ds : Finset ℝ) (m : ℕ) (hm : 0 < m)
    (hds : ∀ d ∈ ds, ∃ z : ℤ, d = (z : ℝ) ∧ (m : ℤ) ∣ z) (hnot : ¬ LonelyAt ds (1 / (8 * (m : ℝ)))) (k : ℤ) :
    ¬ LonelyAt ds ((8 * (k : ℝ) + 1) / (8 * (m : ℝ))) := by
  intro hl
  exact hnot ((start_lonely_iff ds m hm hds).mpr ((opening_lonely_iff ds m hm hds k).mp hl))

#print axioms grid_unit_openings_dead

/-- **The AP residues** [L]: the disparities `1, …, 7` (as reals) are all clear at every opening `(8k+1)/8` of the unit
`m = 1`; adding any multiple `8c` (`c ≥ 1`, an integer) makes every opening of the unit blocked. -/
theorem ap_unit_openings (k : ℤ) :
    LonelyAt ((Finset.Icc (1 : ℤ) 7).image (fun z : ℤ => (z : ℝ))) ((8 * (k : ℝ) + 1) / (8 * ((1 : ℕ) : ℝ))) := by
  have h := opening_lonely_iff ((Finset.Icc (1 : ℤ) 7).image (fun z : ℤ => (z : ℝ))) 1 (by norm_num)
    (by
      intro d hd
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨z, rfl, by simp⟩) k
  refine h.mpr ?_
  intro d hd z hz hdv
  obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hd
  have : z' = z := by exact_mod_cast hz
  subst this
  rw [Finset.mem_Icc] at hz'
  have : (8 : ℤ) ∣ z' := by simpa using hdv
  omega

#print axioms ap_unit_openings

theorem ap_multiple_blocks (c : ℤ) (k : ℤ) :
    ¬ LonelyAt (insert ((8 * c : ℤ) : ℝ) ((Finset.Icc (1 : ℤ) 7).image (fun z : ℤ => (z : ℝ))))
      ((8 * (k : ℝ) + 1) / (8 * ((1 : ℕ) : ℝ))) := by
  intro hl
  have h := hl _ (Finset.mem_insert_self _ _)
  have hw : InWay (((8 * c : ℤ)) : ℝ) ((8 * (k : ℝ) + 1) / (8 * ((1 : ℕ) : ℝ))) :=
    (inWay_opening_iff_of_dvd (8 * c) 1 (by norm_num) (by simp) k).mpr (by simp)
  exact (not_inWay_iff.mpr h) hw

#print axioms ap_multiple_blocks

/-! ## (4) Periodic closure: the strong gate at every lap from one period -/

/-- Shifting the instant by `τ` with `d τ ∈ ℤ` does not change whether `d` is in the way [L]. -/
theorem inWay_add_period {d τ : ℝ} {z : ℤ} (h : d * τ = z) (t : ℝ) : InWay d (t + τ) ↔ InWay d t := by
  unfold InWay
  have : d * (t + τ) = d * t + (z : ℝ) := by rw [mul_add, h]
  rw [this, distInt_add_int]

#print axioms inWay_add_period

/-- The next opening shifts by `τ` when `d τ ∈ ℤ` [L]. -/
theorem nextOpening_add_period {d τ : ℝ} {z : ℤ} (hd : 0 < d) (h : d * τ = z) (t : ℝ) :
    nextOpening d (t + τ) = nextOpening d t + τ := by
  unfold nextOpening
  have e : d * (t + τ) - 1 / 8 = (d * t - 1 / 8) + (z : ℝ) := by rw [mul_add, h]; ring
  rw [e, Int.ceil_add_intCast]
  have hz : (z : ℝ) / d = τ := by rw [← h]; field_simp
  push_cast
  rw [← hz]
  ring

#print axioms nextOpening_add_period

/-- A move commutes with the shift by `τ` when every `d ∈ ds` has `d τ ∈ ℤ` [L]. -/
theorem isMove_add_period {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {τ : ℝ} (hτ : ∀ d ∈ ds, ∃ z : ℤ, d * τ = z)
    {t t' : ℝ} (h : IsMove ds t t') : IsMove ds (t + τ) (t' + τ) := by
  rcases h with ⟨hn, hte⟩ | ⟨x, hx, hw, he, hmax⟩
  · left
    refine ⟨fun d hd hw => ?_, by rw [hte]⟩
    obtain ⟨z, hz⟩ := hτ d hd
    exact hn d hd ((inWay_add_period hz t).mp hw)
  · right
    obtain ⟨z, hz⟩ := hτ x hx
    refine ⟨x, hx, (inWay_add_period hz t).mpr hw, ?_, ?_⟩
    · rw [he, nextOpening_add_period (hpos x hx) hz t]
    · intro d' hd' hw'
      obtain ⟨z', hz'⟩ := hτ d' hd'
      rw [nextOpening_add_period (hpos d' hd') hz' t]
      have := hmax d' hd' ((inWay_add_period hz' t).mp hw')
      linarith

#print axioms isMove_add_period

/-- The cascade from `t₀ + τ` is the cascade from `t₀`, shifted by `τ` [L]. -/
theorem cascadeSeq_add_period {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {τ : ℝ}
    (hτ : ∀ d ∈ ds, ∃ z : ℤ, d * τ = z) (t₀ : ℝ) (n : ℕ) :
    cascadeSeq ds (t₀ + τ) n = cascadeSeq ds t₀ n + τ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 := isMove_add_period hpos hτ (cascadeSeq_isMove ds t₀ n)
    rw [← ih] at h2
    exact isMove_unique (cascadeSeq_isMove ds (t₀ + τ) n) h2

#print axioms cascadeSeq_add_period

/-- **Periodic closure, one period** [L]: if `cascadeSeq ds t₀ P = t₀ + τ` (every `d τ ∈ ℤ`), then
`cascadeSeq ds t₀ (a + P) = cascadeSeq ds t₀ a + τ` for every `a`. -/
theorem cascadeSeq_add_P {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {τ : ℝ}
    (hτ : ∀ d ∈ ds, ∃ z : ℤ, d * τ = z) {t₀ : ℝ} {P : ℕ} (hP : cascadeSeq ds t₀ P = t₀ + τ) (a : ℕ) :
    cascadeSeq ds t₀ (a + P) = cascadeSeq ds t₀ a + τ := by
  have e : cascadeSeq ds t₀ (a + P) = cascadeSeq ds (cascadeSeq ds t₀ P) a := by
    unfold cascadeSeq
    exact Function.iterate_add_apply (step ds) a P t₀
  rw [e, hP]
  exact cascadeSeq_add_period hpos hτ t₀ a

#print axioms cascadeSeq_add_P

/-- **Periodic closure** [L]: the cascade repeats with shift `τ` every `P` moves. -/
theorem cascadeSeq_periodic {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {τ : ℝ}
    (hτ : ∀ d ∈ ds, ∃ z : ℤ, d * τ = z) {t₀ : ℝ} {P : ℕ} (hP : cascadeSeq ds t₀ P = t₀ + τ) (q n : ℕ) :
    cascadeSeq ds t₀ (n + q * P) = cascadeSeq ds t₀ n + q * τ := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : n + (q + 1) * P = (n + q * P) + P := by ring
    rw [e, cascadeSeq_add_P hpos hτ hP, ih]
    push_cast
    ring

#print axioms cascadeSeq_periodic

/-- **The strong gate at every lap from one period** [L]: let every member of `ds` satisfy `d (c/m) ∈ ℤ` (`c ≥ 1`), and let
the cascade from `1/(8m)` close up after `P` moves with `seq P = seq 0 + c/m` (a shift of `R` by `8c`).  If the states
`seq n`, `n < P`, in the zone of every lap `j ≥ 1` move to exactly `(8j+1)/(8m)`, then `StrongGateK ds m k` for every `k ≥ 1`.
(Finite check of the hypotheses: `seven_eight_v1.py`, for the 43 endless 8-sets with `a ≤ 40`.) -/
theorem strongGateK_of_period {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm0 : 0 < m) (c : ℕ) (hc : 0 < c)
    (hτ : ∀ d ∈ ds, ∃ z : ℤ, d * ((c : ℝ) / m) = z) {P : ℕ}
    (hP : cascadeSeq ds (1 / (8 * m)) P = 1 / (8 * m) + (c : ℝ) / m)
    (hwin : ∀ j : ℕ, 1 ≤ j → ∀ n, n < P → (8 * (j : ℝ) - 1) / (8 * m) < cascadeSeq ds (1 / (8 * m)) n →
      cascadeSeq ds (1 / (8 * m)) n < (8 * (j : ℝ) + 1) / (8 * m) →
      cascadeSeq ds (1 / (8 * m)) (n + 1) = (8 * (j : ℝ) + 1) / (8 * m)) :
    ∀ k : ℕ, 1 ≤ k → StrongGateK ds m k := by
  intro k hk n h1 h2
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  have hP0 : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h | h
    · subst h
      have h0 : cascadeSeq ds (1 / (8 * m)) 0 = 1 / (8 * m) := rfl
      rw [h0] at hP
      have : (0 : ℝ) < (c : ℝ) / m := by positivity
      linarith
    · exact h
  set τ : ℝ := (c : ℝ) / m with hτdef
  have hper := cascadeSeq_periodic hpos hτ hP
  obtain ⟨q, r, hrP, hn⟩ : ∃ q r, r < P ∧ n = r + q * P :=
    ⟨n / P, n % P, Nat.mod_lt n hP0, by rw [mul_comm]; exact (Nat.mod_add_div n P).symm⟩
  have hs : cascadeSeq ds (1 / (8 * m)) n = cascadeSeq ds (1 / (8 * m)) r + q * τ := by
    rw [hn]; exact hper q r
  have hs1 : cascadeSeq ds (1 / (8 * m)) (n + 1) = cascadeSeq ds (1 / (8 * m)) (r + 1) + q * τ := by
    have : n + 1 = (r + 1) + q * P := by rw [hn]; ring
    rw [this]; exact hper q (r + 1)
  have hstart := start_le_seq hpos hmv r
  rw [cascadeSeq_zero] at hstart
  have hqc : (q * c : ℝ) = (q * c : ℕ) := by push_cast; ring
  have hτq : (q : ℝ) * τ = ((q * c : ℕ) : ℝ) / m := by rw [hτdef]; push_cast; ring
  by_cases hlt : q * c < k
  · obtain ⟨j, hj⟩ : ∃ j, k = j + q * c := ⟨k - q * c, (Nat.sub_add_cancel hlt.le).symm⟩
    have hj1 : 1 ≤ j := by
      have : 0 < k - q * c := Nat.sub_pos_of_lt hlt
      have e : j = k - q * c := by rw [hj]; simp
      omega
    have ek : (8 * (k : ℝ) - 1) / (8 * m) = (8 * (j : ℝ) - 1) / (8 * m) + q * τ := by
      rw [hτq, hj]; push_cast; field_simp; ring
    have ek' : (8 * (k : ℝ) + 1) / (8 * m) = (8 * (j : ℝ) + 1) / (8 * m) + q * τ := by
      rw [hτq, hj]; push_cast; field_simp; ring
    rw [hs, ek] at h1
    rw [hs, ek'] at h2
    have := hwin j hj1 r hrP (by linarith) (by linarith)
    rw [hs1, this, ek']
  · exfalso
    push Not at hlt
    have hle : (k : ℝ) ≤ ((q * c : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [hs] at h2
    have h3 : (k : ℝ) / m ≤ q * τ := by rw [hτq]; exact div_le_div_of_nonneg_right hle hm0.le
    have h4 : (8 * (k : ℝ) + 1) / (8 * m) = 1 / (8 * m) + (k : ℝ) / m := by field_simp; ring
    linarith

#print axioms strongGateK_of_period

end SevenEight

end Fresh
