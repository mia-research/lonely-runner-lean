import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.DispCell
import Fresh.NormalForm
import Fresh.QuotientReduction
import Fresh.DisplacedLanding
import Fresh.Doors

/-!
# Chain cells: the polytope of speeds for which the cascade follows a given chain of setters (Task CF)

Written 2026-10-10.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `DispCell`, `NormalForm`, `QuotientReduction`,
`DisplacedLanding`, `Doors`.  Reals are Lean's `ℝ` (no floats); no runner is stationary (every speed of a `ChainRun` is positive); no density,
coverage, cap or move budget is the shape of any statement.  Where a window is set against a width the step carries
`[PROVISIONAL: covering]` with the claim it supports.

Setting.  The readings are the disparities `a x` of a subject.  A STATE is the instant `time = (K + 1/8)/a f`, the opening of runner
`f` on lap `K`; in it each runner is clear in the window of a lap or captured on a lap.  A CHAIN is a list of states, each linked to
the next by the cascade's own choice (the captured runner whose opening is latest).

## Contents (grade [L] = compiled by `check.sh`, `#print axioms` after each theorem)
(1) Generic stop theorem.  `isMove_of_link`: a state satisfying its conditions and linked to a successor makes the successor's instant
a `Framework.IsMove` (an instance of the cascade definition, not a new notion).  `isMove_of_last`, `chain_cascadeFixes`: a `ChainRun`
gives `Framework.CascadeFixes` from its first instant.  `chain_isolation` (via `Cascade.cascadeFixes_iff_isolation`, the classification
that `Doors.doors_agree` also reaches) and `chain_landing` (via `DisplacedLanding.final_landing`).
(2) Laps are derived.  `state_determined`: `kind` and `lap` are `kindAt`, `lapAt` of the speeds and the instant (floor for a clear
runner, nearest integer for a captured one).  `canon_stateOK`, `state_unique`, `chain_determined` (a chain is determined by its setter
word).  `stateOK_iff_lapfree`, `inWay_lapfree`: the lap-free form, with `ridx`, `quo`, `edev` of `NormalForm`/`QuotientReduction` at the
state's `R`.  `dev_lapfree`, `move_lapfree`, `lap_start_split`.
(3) Each move is a displacement.  `step_eq_disp` (the next instant is `DispCell.disp` of the setter), `step_mul_displacement`,
`step_displacement_eq`, `step_R`, `chain_total_displacement`.
(4) The example cell.  `QCell` (thirty-two inequalities), `exChain`, `qcell_point`, `point_cascadeFixes`, `finalLaps_not_complete`;
`Cell16` (sixteen inequalities), `cell16_fixes` (the cascade from its start follows A, B, C and stops, whatever the branches);
`point_ridx`, `point_not_complete`.
(5) Hypothesis tests.  `capt_linear_needs_pos`, `link_max_required`, `capt_strict_example`, `sB_three_captured`.

## Hypothesis tests (REQUIRED / NOT REQUIRED / UNDECIDED), each by trying to drop the hypothesis
* positivity of the speeds in `isMove_of_link`, `isMove_of_last`, `chain_cascadeFixes`: NOT REQUIRED [L] (no positivity hypothesis in
  the statements); positivity of the focus speed in `capt_iff_linear`, `window_iff_linear`: REQUIRED [L] (`capt_linear_needs_pos`).
* distinct speeds: NOT REQUIRED [L] (the disparity set is the image of `a`; no injectivity is stated).
* the maximality clause of `LinkOK`: REQUIRED [L] (`link_max_required`).
* `exactly one runner captured per state`: NOT REQUIRED [L] (`sB_three_captured`); the maximal opening names the setter.
* the lap as a parameter: NOT REQUIRED [L] (`state_determined`, `stateOK_iff_lapfree`).
* strictness of the capture inequality: REQUIRED [L] (`capt_strict_example`).
* the start `(d_min, lap 0)`: NOT REQUIRED for the move theorems, REQUIRED for `chain_isolation` and `chain_landing`.

## Provenance
The external file `PrefixCellClosure_v1.lean` (Codex worktree, read only, not imported, not compiled by this session) states
`prefix_cell_stops`, with helper theorems `clear_at_opening`, `loose_band_at_opening`, `only_candidate_step`.  Corresponding
theorems here, each written for this file from the statement and the idea of the argument (no proof was copied):
`window_iff_linear`/`not_inWay_of_lin` for `clear_at_opening`; `band_of_lin` for `loose_band_at_opening`;
`capt_of_band`/`isMove_of_bands` for `only_candidate_step`; `cell16_fixes` for `prefix_cell_stops`, here from the cascade's own
start (the external statement starts at the opening of `a7` on lap `164`).  No file of the existing repository was read for this task.
-/

open Classical

namespace Fresh.ChainCell

open Fresh

/-! ## (0) Window and capture at an instant -/

/-- Runner `x` is CAPTURED at `t` on lap `L`: it stands strictly within `1/8` of the whole lap `L`. -/
-- STANDING: DEFINITION
def Capt (x t : ℝ) (L : ℤ) : Prop := |x * t - (L : ℝ)| < 1 / 8

/-- Runner `x` is in the WINDOW of lap `N` at `t`: `N + 1/8 ≤ x t ≤ N + 7/8` (clear, on lap `N`). -/
-- STANDING: DEFINITION
def InWindow (x t : ℝ) (N : ℤ) : Prop := (N : ℝ) + 1 / 8 ≤ x * t ∧ x * t ≤ (N : ℝ) + 7 / 8

theorem capt_inWay {x t : ℝ} {L : ℤ} (h : Capt x t L) : InWay x t := by
  unfold InWay
  exact lt_of_le_of_lt (Cascade.distInt_le (x * t) L) h

theorem inWay_capt {x t : ℝ} (h : InWay x t) : Capt x t (round (x * t)) := h

theorem window_not_inWay {x t : ℝ} {N : ℤ} (h : InWindow x t N) : ¬ InWay x t := by
  intro hw
  obtain ⟨k, hk⟩ := Cascade.exists_near_int hw
  rw [abs_lt] at hk
  have h1 : k ≤ N ∨ N + 1 ≤ k := by omega
  rcases h1 with h1 | h1
  · have : (k : ℝ) ≤ N := by exact_mod_cast h1
    linarith [h.1, h.2]
  · have : (N : ℝ) + 1 ≤ k := by exact_mod_cast h1
    linarith [h.1, h.2]

theorem not_inWay_window {x t : ℝ} (h : ¬ InWay x t) : InWindow x t ⌊x * t⌋ := by
  have h8 : (1 / 8 : ℝ) ≤ distInt (x * t) := Cascade.not_inWay_iff.mp h
  have hf := Int.floor_le (x * t)
  have hf1 := Int.lt_floor_add_one (x * t)
  have d1 := Cascade.distInt_le (x * t) ⌊x * t⌋
  have d2 := Cascade.distInt_le (x * t) (⌊x * t⌋ + 1)
  push_cast at d2
  constructor
  · by_contra hc
    push Not at hc
    have : |x * t - (⌊x * t⌋ : ℝ)| < 1 / 8 := by rw [abs_lt]; constructor <;> linarith
    linarith
  · by_contra hc
    push Not at hc
    have : |x * t - ((⌊x * t⌋ : ℝ) + 1)| < 1 / 8 := by rw [abs_lt]; constructor <;> linarith
    linarith

theorem inWay_or_window (x t : ℝ) : Capt x t (round (x * t)) ∨ InWindow x t ⌊x * t⌋ := by
  by_cases h : InWay x t
  · exact Or.inl (inWay_capt h)
  · exact Or.inr (not_inWay_window h)

-- [PROVISIONAL: covering]: two laps within `1/8` of one value differ by less than `1/4 < 1`; supports `state_determined`
-- (a state's laps are functions of the speeds); serves rule 1 (the lap is derived, the displacement is the move).
theorem capt_unique {x t : ℝ} {L L' : ℤ} (h : Capt x t L) (h' : Capt x t L') : L = L' := by
  unfold Capt at h h'
  rw [abs_lt] at h h'
  have h1 : ((L - L' : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : (-1 : ℝ) < ((L - L' : ℤ) : ℝ) := by push_cast; linarith
  have h1' : L - L' < 1 := by exact_mod_cast h1
  have h2' : -1 < L - L' := by exact_mod_cast h2
  omega

theorem window_lap {x t : ℝ} {N : ℤ} (h : InWindow x t N) : N = ⌊x * t⌋ :=
  (Int.floor_eq_iff.mpr ⟨by linarith [h.1], by linarith [h.2]⟩).symm

theorem capt_lap {x t : ℝ} {L : ℤ} (h : Capt x t L) : L = round (x * t) := by
  unfold Capt at h
  rw [abs_lt] at h
  exact (NormalForm.round_eq_int _ _ (by linarith [h.1]) (by linarith [h.2])).symm

theorem capt_not_window {x t : ℝ} {L N : ℤ} (h : Capt x t L) (h' : InWindow x t N) : False :=
  window_not_inWay h' (capt_inWay h)


/-! ## (1) The linear form of a window or a capture at an opening

The state of the cascade whose instant is the opening `t = (K + 1/8)/f` of the runner of speed `f` on lap `K`.  At such an
instant every condition on a runner `x` is LINEAR in the speeds, with integer coefficients that carry the laps. -/

theorem reading_at_opening {x f : ℝ} (hf : 0 < f) (K : ℤ) :
    x * (((K : ℝ) + 1 / 8) / f) = (8 * (K : ℝ) + 1) * x / (8 * f) := by
  field_simp

theorem capt_iff_linear {x f : ℝ} (hf : 0 < f) (K L : ℤ) :
    Capt x (((K : ℝ) + 1 / 8) / f) L ↔
      (8 * (L : ℝ) - 1) * f < (8 * (K : ℝ) + 1) * x ∧ (8 * (K : ℝ) + 1) * x < (8 * (L : ℝ) + 1) * f := by
  unfold Capt
  rw [reading_at_opening hf, abs_lt]
  have h8 : (0 : ℝ) < 8 * f := by positivity
  have e : (8 * (K : ℝ) + 1) * x / (8 * f) - (L : ℝ) = ((8 * (K : ℝ) + 1) * x - 8 * f * (L : ℝ)) / (8 * f) := by
    field_simp
  rw [e, lt_div_iff₀ h8, div_lt_iff₀ h8]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

theorem window_iff_linear {x f : ℝ} (hf : 0 < f) (K N : ℤ) :
    InWindow x (((K : ℝ) + 1 / 8) / f) N ↔
      (8 * (N : ℝ) + 1) * f ≤ (8 * (K : ℝ) + 1) * x ∧ (8 * (K : ℝ) + 1) * x ≤ (8 * (N : ℝ) + 7) * f := by
  unfold InWindow
  rw [reading_at_opening hf]
  have h8 : (0 : ℝ) < 8 * f := by positivity
  rw [le_div_iff₀ h8, div_le_iff₀ h8]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The opening of `y` on lap `M` is no later than the opening of `x` on lap `L`: linear in the speeds. -/
theorem opening_le_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (L M : ℤ) :
    ((M : ℝ) + 1 / 8) / y ≤ ((L : ℝ) + 1 / 8) / x ↔ (8 * (M : ℝ) + 1) * x ≤ (8 * (L : ℝ) + 1) * y := by
  rw [div_le_div_iff₀ hy hx]
  constructor <;> intro h <;> nlinarith

/-! ## (2) States, links, chains -/

/-- Whether a runner is clear (in a window) or captured at a state. -/
inductive Kind
  | clear
  | capt
  deriving DecidableEq

/-- A state of the cascade on `n` readings: the instant is the opening of runner `f` on lap `K`; `kind x` and `lap x` say
whether runner `x` is clear (in the window of lap `lap x`) or captured (on lap `lap x`) there. -/
structure St (n : ℕ) where
  f : Fin n
  K : ℤ
  kind : Fin n → Kind
  lap : Fin n → ℤ

/-- The instant of a state: the opening of its runner on its lap. -/
noncomputable def St.time {n : ℕ} (a : Fin n → ℝ) (s : St n) : ℝ := ((s.K : ℝ) + 1 / 8) / a s.f

/-- The window and capture conditions of a state. -/
-- STANDING: DEFINITION
def StateOK {n : ℕ} (a : Fin n → ℝ) (s : St n) : Prop :=
  ∀ x, (s.kind x = Kind.clear → InWindow (a x) (s.time a) (s.lap x)) ∧
    (s.kind x = Kind.capt → Capt (a x) (s.time a) (s.lap x))

/-- The link from `s` to `s'`: the next setter is captured at `s`, on the lap `s'.K`, and its opening is the latest among the
captured runners of `s`. -/
-- STANDING: DEFINITION
def LinkOK {n : ℕ} (a : Fin n → ℝ) (s s' : St n) : Prop :=
  s.kind s'.f = Kind.capt ∧ s'.K = s.lap s'.f ∧
    ∀ y, s.kind y = Kind.capt → ((s.lap y : ℝ) + 1 / 8) / a y ≤ ((s.lap s'.f : ℝ) + 1 / 8) / a s'.f

/-- A chain cell: positive speeds, states `s 0, …, s m` each satisfying its conditions, consecutive states linked, and the last
state with every runner clear.  (The polytope of speeds for which the cascade follows this chain.) -/
-- STANDING: DEFINITION
structure ChainRun {n : ℕ} (a : Fin n → ℝ) (m : ℕ) (s : ℕ → St n) : Prop where
  pos : ∀ x, 0 < a x
  ok : ∀ i, i ≤ m → StateOK a (s i)
  link : ∀ i, i < m → LinkOK a (s i) (s (i + 1))
  last : ∀ x, (s m).kind x = Kind.clear

/-- The disparity set of the readings. -/
noncomputable def dset {n : ℕ} (a : Fin n → ℝ) : Finset ℝ := Finset.univ.image a

theorem mem_dset {n : ℕ} {a : Fin n → ℝ} {d : ℝ} : d ∈ dset a ↔ ∃ x, a x = d := by
  unfold dset; simp

/-! ## (3) The generic stop theorem: a chain state names its move -/

/-- **The move named by a state** [L].  If `s` satisfies its conditions and `s'` is linked to `s`, then `s'.time` IS a cascade
move from `s.time`.  This is an instance of the cascade definition `Framework.IsMove` (second disjunct): the named runner is in
the way, `nextOpening` is its opening on the captured lap (`Cascade.nextOpening_eq`), and every runner in the way opens no
later.  Positivity of the speeds is NOT used (REQUIRED hypotheses are tested below). -/
theorem isMove_of_link {n : ℕ} {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hl : LinkOK a s s') :
    IsMove (dset a) (s.time a) (s'.time a) := by
  obtain ⟨hk, hK, hmax⟩ := hl
  right
  have hc : Capt (a s'.f) (s.time a) (s.lap s'.f) := (hs s'.f).2 hk
  refine ⟨a s'.f, mem_dset.mpr ⟨_, rfl⟩, capt_inWay hc, ?_, ?_⟩
  · rw [Cascade.nextOpening_eq hc]
    unfold St.time
    rw [hK]
  · intro d' hd' hw
    obtain ⟨y, rfl⟩ := mem_dset.mp hd'
    have hyk : s.kind y = Kind.capt := by
      by_contra hne
      have hcl : s.kind y = Kind.clear := by cases h : s.kind y <;> simp_all
      exact window_not_inWay ((hs y).1 hcl) hw
    have hcy : Capt (a y) (s.time a) (s.lap y) := (hs y).2 hyk
    rw [Cascade.nextOpening_eq hcy]
    unfold St.time
    rw [hK]
    exact hmax y hyk

/-- **The last state fixes the cascade** [L]: all runners clear, so no one is in the way and `IsMove` is the first disjunct. -/
theorem isMove_of_last {n : ℕ} {a : Fin n → ℝ} {s : St n} (hs : StateOK a s) (hl : ∀ x, s.kind x = Kind.clear) :
    IsMove (dset a) (s.time a) (s.time a) := by
  left
  refine ⟨?_, rfl⟩
  intro d hd
  obtain ⟨y, rfl⟩ := mem_dset.mp hd
  exact window_not_inWay ((hs y).1 (hl y))

/-- **Generic stop theorem** [L]: along a `ChainRun` of length `m`, the instants `time (s i)` are the cascade's moves from
`time (s 0)`, and the cascade then fixes at `time (s m)`: `CascadeFixes (dset a) (time (s 0))`.  Every chain is an instance of
`Framework.CascadeFixes` (the cascade definition itself); the relation to `Doors.cascadeFixes_iff_seq` is that the sequence
used is the unique cascade sequence (`Cascade.seq_eq_cascadeSeq`). -/
theorem chain_cascadeFixes {n : ℕ} {a : Fin n → ℝ} {m : ℕ} {s : ℕ → St n} (h : ChainRun a m s) :
    CascadeFixes (dset a) ((s 0).time a) := by
  refine ⟨fun k => (s (min k m)).time a, rfl, ?_, m, ?_⟩
  · intro k
    by_cases hk : k < m
    · have e1 : min k m = k := min_eq_left hk.le
      have e2 : min (k + 1) m = k + 1 := min_eq_left (by omega)
      show IsMove (dset a) ((s (min k m)).time a) ((s (min (k + 1) m)).time a)
      rw [e1, e2]
      exact isMove_of_link (h.ok k hk.le) (h.link k hk)
    · have e1 : min k m = m := min_eq_right (by omega)
      have e2 : min (k + 1) m = m := min_eq_right (by omega)
      show IsMove (dset a) ((s (min k m)).time a) ((s (min (k + 1) m)).time a)
      rw [e1, e2]
      exact isMove_of_last (h.ok m le_rfl) h.last
  · simp

#print axioms isMove_of_link
#print axioms isMove_of_last
#print axioms chain_cascadeFixes


/-- The sequence of instants of a chain, held at its last state. -/
noncomputable def chainSeq {n : ℕ} (a : Fin n → ℝ) (m : ℕ) (s : ℕ → St n) (k : ℕ) : ℝ := (s (min k m)).time a

theorem chainSeq_isMove {n : ℕ} {a : Fin n → ℝ} {m : ℕ} {s : ℕ → St n} (h : ChainRun a m s) (k : ℕ) :
    IsMove (dset a) (chainSeq a m s k) (chainSeq a m s (k + 1)) := by
  unfold chainSeq
  by_cases hk : k < m
  · have e1 : min k m = k := min_eq_left hk.le
    have e2 : min (k + 1) m = k + 1 := min_eq_left (by omega)
    rw [e1, e2]
    exact isMove_of_link (h.ok k hk.le) (h.link k hk)
  · have e1 : min k m = m := min_eq_right (by omega)
    have e2 : min (k + 1) m = m := min_eq_right (by omega)
    rw [e1, e2]
    exact isMove_of_last (h.ok m le_rfl) h.last

theorem chainSeq_fixed {n : ℕ} (a : Fin n → ℝ) (m : ℕ) (s : ℕ → St n) :
    chainSeq a m s (m + 1) = chainSeq a m s m := by
  unfold chainSeq
  simp

#print axioms chainSeq_isMove
#print axioms chainSeq_fixed

/-- **The chain is the cascade of an arrangement** [L].  If the readings of a subject `k` of an arrangement are `a`, `d_min = m`
is the setter of state `0` on lap `0`, then the subject is isolated at some positive instant
(`Cascade.cascadeFixes_iff_isolation`).  The hypotheses `s 0 = (d_min, lap 0)` are REQUIRED for this corollary only: the
move theorem above does not use them. -/
theorem chain_isolation {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m)
    {a : Fin 7 → ℝ} (hds : disparitySet v k = dset a) {M : ℕ} {s : ℕ → St 7} (h : ChainRun a M s)
    (hK : (s 0).K = 0) (hf : a (s 0).f = m) : Isolation v k := by
  refine (Cascade.cascadeFixes_iff_isolation hv hm).mpr ?_
  rw [hds]
  have e : (s 0).time a = 1 / (8 * m) := by
    unfold St.time
    rw [hK, hf]
    have hm0 : m ≠ 0 := (Cascade.disparitySet_pos hv k m hm.1).ne'
    field_simp
    norm_num
  rw [← e]
  exact chain_cascadeFixes h

#print axioms chain_isolation

/-- **The chain lands at the least lonely `R`** [L].  With `m ∈ dset a` the base scale `d_min`, the chain's last instant is the
landing `IsLandingR` (the least `R > 0` with the whole set lonely), by `DisplacedLanding.final_landing`. -/
theorem chain_landing {n : ℕ} {a : Fin n → ℝ} {M : ℕ} {s : ℕ → St n} (h : ChainRun a M s) {m : ℝ}
    (hm : m ∈ dset a) (hK : (s 0).K = 0) (hf : a (s 0).f = m) :
    QuotientReduction.IsLandingR m (dset a) (8 * m * (s M).time a) := by
  have hpos : ∀ d ∈ dset a, 0 < d := by
    intro d hd
    obtain ⟨x, rfl⟩ := mem_dset.mp hd
    exact h.pos x
  have hm0 : 0 < m := hpos m hm
  have h0 : chainSeq a M s 0 = 1 / (8 * m) := by
    unfold chainSeq St.time
    simp only [Nat.zero_le, min_eq_left]
    rw [hK, hf]
    field_simp
    norm_num
  have := (DisplacedLanding.final_landing hpos hm h0 (chainSeq_isMove h) (chainSeq_fixed a M s)).1
  unfold chainSeq at this
  simpa using this

#print axioms chain_landing

/-! ## (4) The laps are DERIVED -/

/-- The kind of runner `x` at instant `t`: captured iff in the way. -/
noncomputable def kindAt (x t : ℝ) : Kind := if InWay x t then Kind.capt else Kind.clear

/-- The lap of runner `x` at instant `t`: the nearest lap if in the way, the floor if clear. -/
noncomputable def lapAt (x t : ℝ) : ℤ := if InWay x t then round (x * t) else ⌊x * t⌋

/-- **A state's data are functions of the speeds and the instant** [L]: if `s` satisfies its conditions, then for every
runner `x`, `kind x = kindAt (a x) (time)` and `lap x = lapAt (a x) (time)` (the floor of `a_x t` for a clear runner, the
nearest integer for a captured one).  The lap vector is not a parameter. -/
theorem state_determined {n : ℕ} {a : Fin n → ℝ} {s : St n} (hs : StateOK a s) (x : Fin n) :
    s.kind x = kindAt (a x) (s.time a) ∧ s.lap x = lapAt (a x) (s.time a) := by
  unfold kindAt lapAt
  cases hk : s.kind x
  · have hw := (hs x).1 hk
    have hn := window_not_inWay hw
    rw [if_neg hn, if_neg hn]
    exact ⟨rfl, window_lap hw⟩
  · have hc := (hs x).2 hk
    have hi := capt_inWay hc
    rw [if_pos hi, if_pos hi]
    exact ⟨rfl, capt_lap hc⟩

/-- Conversely, the canonical data at any instant satisfy the conditions of a state [L]: there is no instant at which the
laps fail to exist.  (`StateOK` for the state with `kindAt`, `lapAt`.) -/
theorem canon_stateOK {n : ℕ} (a : Fin n → ℝ) (f : Fin n) (K : ℤ) :
    StateOK a ⟨f, K, fun x => kindAt (a x) (((K : ℝ) + 1 / 8) / a f), fun x => lapAt (a x) (((K : ℝ) + 1 / 8) / a f)⟩ := by
  intro x
  dsimp only [St.time]
  by_cases hw : InWay (a x) (((K : ℝ) + 1 / 8) / a f)
  · constructor
    · intro h
      unfold kindAt at h
      rw [if_pos hw] at h
      cases h
    · intro _
      simp only [lapAt, if_pos hw]
      exact inWay_capt hw
  · constructor
    · intro _
      simp only [lapAt, if_neg hw]
      exact not_inWay_window hw
    · intro h
      unfold kindAt at h
      rw [if_neg hw] at h
      cases h

#print axioms state_determined
#print axioms canon_stateOK

/-- Two states at the same instant that satisfy their conditions are equal in kind and lap [L]. -/
theorem state_unique {n : ℕ} {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hs' : StateOK a s')
    (ht : s.time a = s'.time a) (x : Fin n) : s.kind x = s'.kind x ∧ s.lap x = s'.lap x := by
  have h1 := state_determined hs x
  have h2 := state_determined hs' x
  rw [ht] at h1
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

/-- **The chain is determined by its setter word** [L]: two chains of the same length for the same speeds, starting at the same
lap and with the same setter at every position, are the same chain (kind and lap of every runner at every state, and every
lap `K`).  The laps are derived from the speeds and the word. -/
theorem chain_determined {n : ℕ} {a : Fin n → ℝ} {m : ℕ} {s s' : ℕ → St n} (h : ChainRun a m s) (h' : ChainRun a m s')
    (hf : ∀ i, i ≤ m → (s i).f = (s' i).f) (h0 : (s 0).K = (s' 0).K) :
    ∀ i, i ≤ m → (s i).K = (s' i).K ∧ ∀ x, (s i).kind x = (s' i).kind x ∧ (s i).lap x = (s' i).lap x := by
  intro i
  induction i with
  | zero =>
    intro _
    have ht : (s 0).time a = (s' 0).time a := by unfold St.time; rw [h0, hf 0 (Nat.zero_le _)]
    exact ⟨h0, state_unique (h.ok 0 (Nat.zero_le _)) (h'.ok 0 (Nat.zero_le _)) ht⟩
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hl := h.link j (by omega)
    have hl' := h'.link j (by omega)
    have hK : (s (j + 1)).K = (s' (j + 1)).K := by
      rw [hl.2.1, hl'.2.1, hf (j + 1) hj, ih'.2 _ |>.2]
    have ht : (s (j + 1)).time a = (s' (j + 1)).time a := by
      unfold St.time; rw [hK, hf (j + 1) hj]
    exact ⟨hK, state_unique (h.ok _ hj) (h'.ok _ hj) ht⟩

#print axioms state_unique
#print axioms chain_determined


/-! ## (5) The lap-free form, in the coordinates of `NormalForm`

Base scale `m > 0` (in the application `m = d_min`), gate coordinate `R = 8 m t`.  A reading `d` has grid index
`idx m d = ridx + 8 quo` (`QuotientReduction`) and deviation `e = edev m d`.  The reading at `R` is `(d/m) R = (ridx + e) R + 8 quo R`,
and the whole multiple `8 ⌊quo R⌋` drops out modulo `8`; what remains is `(ridx + e) R + 8 {quo R}`. -/

/-- The residue-window reading of `d` at `R` from the grid-plus-deviation coordinates (no lap appears). -/
noncomputable def lapfreeReading (m d R : ℝ) : ℝ :=
  ((QuotientReduction.ridx m d : ℝ) + NormalForm.edev m d) * R + 8 * Int.fract ((QuotientReduction.quo m d : ℝ) * R)

/-- **Blocked at `R` iff the lap-free reading leaves the clear window** [L].  No lap, no integer other than `ridx`, `quo`. -/
theorem inWay_lapfree {m d R : ℝ} (hm : 0 < m) :
    InWay d (R / (8 * m)) ↔ ¬ NormalForm.Win (lapfreeReading m d R) := by
  have h1 := Cascade.not_inWay_iff (d := d) (t := R / (8 * m))
  have h2 := QuotientReduction.clear_iff_win m d R hm.ne'
  have h3 := QuotientReduction.win_orig_iff_fract m d R hm.ne'
  have h4 := QuotientReduction.dRed_div m d hm.ne'
  have h5 : (1 / 8 : ℝ) ≤ distInt (d * (R / (8 * m))) ↔ NormalForm.Win (lapfreeReading m d R) := by
    rw [h2, h3, h4]
    rfl
  rw [← not_iff_not, h1, h5]
  exact not_not.symm

#print axioms inWay_lapfree

/-- The gate coordinate of a state. -/
noncomputable def St.R {n : ℕ} (m : ℝ) (a : Fin n → ℝ) (s : St n) : ℝ := 8 * m * s.time a

theorem time_eq_R {n : ℕ} {m : ℝ} (hm : 0 < m) (a : Fin n → ℝ) (s : St n) : s.time a = s.R m a / (8 * m) := by
  unfold St.R
  field_simp

/-- The state's conditions with no lap: each clear runner has its lap-free reading in the clear window, each captured runner
outside it. -/
-- STANDING: DEFINITION
def LapFreeOK {n : ℕ} (m : ℝ) (a : Fin n → ℝ) (f : Fin n) (K : ℤ) (kind : Fin n → Kind) : Prop :=
  ∀ x, (kind x = Kind.clear → NormalForm.Win (lapfreeReading m (a x) (8 * m * (((K : ℝ) + 1 / 8) / a f)))) ∧
    (kind x = Kind.capt → ¬ NormalForm.Win (lapfreeReading m (a x) (8 * m * (((K : ℝ) + 1 / 8) / a f))))

/-- **The exact lap-free reformulation of a state's conditions** [L]: there exist laps making the state satisfy its window and
capture conditions iff the kinds are as the lap-free readings say.  So the laps in a `ChainRun` carry no information beyond the
kinds and the speeds: they exist, are unique (`state_determined`), and are not a parameter. -/
theorem stateOK_iff_lapfree {n : ℕ} {m : ℝ} (hm : 0 < m) (a : Fin n → ℝ) (f : Fin n) (K : ℤ) (kind : Fin n → Kind) :
    (∃ lap : Fin n → ℤ, StateOK a ⟨f, K, kind, lap⟩) ↔ LapFreeOK m a f K kind := by
  have hR : ∀ t : ℝ, 8 * m * t / (8 * m) = t := fun t => by field_simp
  constructor
  · rintro ⟨lap, hs⟩ x
    constructor
    · intro hk
      have hw := window_not_inWay ((hs x).1 hk)
      have := (inWay_lapfree (m := m) (d := a x) (R := 8 * m * (((K : ℝ) + 1 / 8) / a f)) hm).not
      rw [hR] at this
      exact not_not.mp (this.mp hw)
    · intro hk
      have hi := capt_inWay ((hs x).2 hk)
      have := (inWay_lapfree (m := m) (d := a x) (R := 8 * m * (((K : ℝ) + 1 / 8) / a f)) hm)
      rw [hR] at this
      exact this.mp hi
  · intro h
    refine ⟨fun x => lapAt (a x) (((K : ℝ) + 1 / 8) / a f), ?_⟩
    intro x
    dsimp only [St.time]
    have hiff := inWay_lapfree (m := m) (d := a x) (R := 8 * m * (((K : ℝ) + 1 / 8) / a f)) hm
    rw [hR] at hiff
    constructor
    · intro hk
      have hw : ¬ InWay (a x) (((K : ℝ) + 1 / 8) / a f) := fun hi => (hiff.mp hi) ((h x).1 hk)
      simp only [lapAt, if_neg hw]
      exact not_inWay_window hw
    · intro hk
      have hi : InWay (a x) (((K : ℝ) + 1 / 8) / a f) := hiff.mpr ((h x).2 hk)
      simp only [lapAt, if_pos hi]
      exact inWay_capt hi

#print axioms stateOK_iff_lapfree

/-- The signed residue `dev` read from the lap-free reading [L] (`sres8` is periodic modulo `8`). -/
theorem dev_lapfree (m d R : ℝ) (hm : m ≠ 0) : RealCase.dev m R d = RealCase.sres8 (lapfreeReading m d R) := by
  have e : d / m * R = lapfreeReading m d R + 8 * ((⌊(QuotientReduction.quo m d : ℝ) * R⌋ : ℤ) : ℝ) := by
    have h := QuotientReduction.reading_diff m d R hm
    have h4 := QuotientReduction.dRed_div m d hm
    have hf := Int.floor_add_fract ((QuotientReduction.quo m d : ℝ) * R)
    unfold lapfreeReading
    rw [h, h4]
    linarith
  unfold RealCase.dev RealCase.sres8
  rw [e]
  have : (lapfreeReading m d R + 8 * ((⌊(QuotientReduction.quo m d : ℝ) * R⌋ : ℤ) : ℝ)) / 8 =
      lapfreeReading m d R / 8 + ((⌊(QuotientReduction.quo m d : ℝ) * R⌋ : ℤ) : ℝ) := by ring
  rw [this, round_add_intCast]
  push_cast
  ring

/-- **The move in lap-free coordinates** [L]: a runner in the way at `R` is next open at
`8 m nextOpening = R + (1 - sres8 (lapfreeReading)) / ρ`, `ρ = d/m`. -/
theorem move_lapfree {m d R : ℝ} (hm : 0 < m) (hd : 0 < d) (hw : InWay d (R / (8 * m))) :
    8 * m * nextOpening d (R / (8 * m)) = R + (1 - RealCase.sres8 (lapfreeReading m d R)) / (d / m) := by
  rw [RealCase.nextOpening_gate hm hd hw, dev_lapfree m d R hm.ne']

#print axioms dev_lapfree
#print axioms move_lapfree

/-- The lap of a reading at the cascade's start, from the coordinates [L]: `round (ρ / 8) = quo + round ((ridx + e)/8)`.
The quotient carries the lap; the residue part adds `0` or `1`. -/
theorem lap_start_split (m d : ℝ) :
    round (d / m / 8) = QuotientReduction.quo m d + round (((QuotientReduction.ridx m d : ℝ) + NormalForm.edev m d) / 8) := by
  have h1 : (NormalForm.idx m d : ℝ) = (QuotientReduction.ridx m d : ℝ) + 8 * (QuotientReduction.quo m d : ℝ) := by
    exact_mod_cast QuotientReduction.idx_split m d
  have h2 : d / m = (NormalForm.idx m d : ℝ) + NormalForm.edev m d := by unfold NormalForm.edev; ring
  have h3 : d / m / 8 = ((QuotientReduction.ridx m d : ℝ) + NormalForm.edev m d) / 8 + (QuotientReduction.quo m d : ℝ) := by
    rw [h2, h1]; ring
  rw [h3, round_add_intCast]
  ring

#print axioms lap_start_split

/-! ## (6) Each move is a displacement of the setter, in the `DispCell` sense -/

/-- **A move is the displacement of the setter** [L]: `time s' = DispCell.disp (a setter) (time s)`, and
`a * displacement = lap + 1/8 - a * time` (`DispCell.mul_displacement`). -/
theorem step_eq_disp {n : ℕ} {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hl : LinkOK a s s') :
    s'.time a = DispCell.disp (a s'.f) (s.time a) := by
  have hc : Capt (a s'.f) (s.time a) (s.lap s'.f) := (hs s'.f).2 hl.1
  rw [DispCell.disp_of_near hc]
  unfold St.time
  rw [hl.2.1]

theorem step_mul_displacement {n : ℕ} {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hl : LinkOK a s s')
    (hpos : 0 < a s'.f) :
    a s'.f * DispCell.displacement (a s'.f) (s.time a) = (s'.K : ℝ) + 1 / 8 - a s'.f * s.time a := by
  have hc : Capt (a s'.f) (s.time a) (s.lap s'.f) := (hs s'.f).2 hl.1
  rw [DispCell.mul_displacement hpos hc, hl.2.1]

theorem step_displacement_eq {n : ℕ} {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hl : LinkOK a s s') :
    DispCell.displacement (a s'.f) (s.time a) = s'.time a - s.time a := by
  unfold DispCell.displacement
  rw [step_eq_disp hs hl]

/-- **The move in the gate coordinate** [L]: `R' = R + (1 - δ)/ρ`, `δ = dev` the signed residue of the setter at `R`
(`RealCase.nextOpening_gate`); `δ = sres8 (lapfreeReading)` in the grid-plus-deviation coordinates. -/
theorem step_R {n : ℕ} {m : ℝ} (hm : 0 < m) {a : Fin n → ℝ} {s s' : St n} (hs : StateOK a s) (hl : LinkOK a s s')
    (hpos : 0 < a s'.f) :
    s'.R m a = s.R m a + (1 - RealCase.sres8 (lapfreeReading m (a s'.f) (s.R m a))) / (a s'.f / m) := by
  have hc : Capt (a s'.f) (s.time a) (s.lap s'.f) := (hs s'.f).2 hl.1
  have hw : InWay (a s'.f) (s.R m a / (8 * m)) := by rw [← time_eq_R hm]; exact capt_inWay hc
  have := move_lapfree hm hpos hw
  rw [← time_eq_R hm] at this
  have hnext : s'.time a = nextOpening (a s'.f) (s.time a) := by
    rw [Cascade.nextOpening_eq hc]
    unfold St.time
    rw [hl.2.1]
  unfold St.R
  rw [hnext]
  exact this

#print axioms step_eq_disp
#print axioms step_mul_displacement
#print axioms step_displacement_eq
#print axioms step_R


/-! ## (7) The example cell: a chain of six states

Readings `a1 < … < a7` (`d_min = a1`).  The cascade from `1/(8 a1)` visits six instants: the opening of `a1` on lap `0` (A), of `a2`
on lap `26` (B), of `a4` on lap `91` (C), of `a7` on lap `164` (S0), of `a3` on lap `85` (S1), of `a6` on lap `159` (S2), where nothing is
in the way.  `QCell` lists the polytope: the sixteen inequalities of `Codex PrefixCellClosure_v1` (provenance: that file was read, its
sixteen inequalities were re-derived here as the binding window and capture conditions of A, B, C, and nothing was imported from it)
plus nine more that fix the branch (`a5` captured at B; `a3` captured at S0; `a6` captured at S1; the windows of S1, S2). -/

-- STANDING: DEFINITION
structure QCell (a1 a2 a3 a4 a5 a6 a7 : ℝ) : Prop where
  pos1 : 0 < a1
  pos2 : 0 < a2
  pos3 : 0 < a3
  pos4 : 0 < a4
  pos5 : 0 < a5
  pos6 : 0 < a6
  pos7 : 0 < a7
  h8 : 207 * a1 < a2
  h11 : a3 ≤ 671 * a1
  h12 : 721 * a1 ≤ a4
  h14 : 737 * a1 ≤ a5
  h17 : a6 ≤ 1255 * a1
  h18 : 1297 * a1 ≤ a7
  h25 : 673 * a2 ≤ 209 * a3
  h27 : 727 * a2 < 209 * a4
  h30 : 209 * a5 < 745 * a2
  h31 : 1263 * a2 < 209 * a6
  h32 : 19 * a6 < 115 * a2
  h34 : 11 * a7 ≤ 69 * a2
  h36 : 745 * a4 ≤ 729 * a5
  h37 : 1265 * a4 ≤ 729 * a6
  h50 : 437 * a4 < 243 * a7
  h51 : 729 * a7 < 1313 * a4
  x1 : 743 * a2 < 209 * a5
  x2 : 679 * a7 < 1313 * a3
  x3 : 1271 * a3 < 681 * a6
  x4 : 681 * a6 < 1273 * a3
  x5 : 681 * a4 ≤ 735 * a3
  x6 : 681 * a5 ≤ 751 * a3
  x7 : 681 * a7 ≤ 1319 * a3
  x8 : 1273 * a7 ≤ 1319 * a6

open Kind in
/-- State A: the opening of `a1` on lap `0`; `a2` captured on lap `26`. -/
def sA : St 7 := ⟨0, 0, ![clear, capt, clear, clear, clear, clear, clear], ![0, 26, 83, 90, 92, 156, 162]⟩

open Kind in
/-- State B: the opening of `a2` on lap `26`; `a4`, `a5`, `a6` captured on laps `91`, `93`, `158`. -/
def sB : St 7 := ⟨1, 26, ![clear, clear, clear, capt, capt, capt, clear], ![0, 26, 84, 91, 93, 158, 163]⟩

open Kind in
/-- State C: the opening of `a4` on lap `91`; `a7` captured on lap `164`. -/
def sC : St 7 := ⟨3, 91, ![clear, clear, clear, clear, clear, clear, capt], ![0, 26, 84, 91, 93, 158, 164]⟩

open Kind in
/-- State S0: the opening of `a7` on lap `164`; `a3` captured on lap `85`. -/
def sS0 : St 7 := ⟨6, 164, ![clear, clear, capt, clear, clear, clear, clear], ![0, 26, 85, 91, 93, 158, 164]⟩

open Kind in
/-- State S1: the opening of `a3` on lap `85`; `a6` captured on lap `159`. -/
def sS1 : St 7 := ⟨2, 85, ![clear, clear, clear, clear, clear, capt, clear], ![0, 26, 85, 91, 93, 159, 164]⟩

open Kind in
/-- State S2: the opening of `a6` on lap `159`; nobody in the way. -/
def sS2 : St 7 := ⟨5, 159, ![clear, clear, clear, clear, clear, clear, clear], ![0, 26, 85, 91, 93, 159, 164]⟩

/-- The six states as a sequence. -/
def exS : ℕ → St 7
  | 0 => sA
  | 1 => sB
  | 2 => sC
  | 3 => sS0
  | 4 => sS1
  | _ => sS2


set_option hygiene false in
/-- The linear closer for the example cell: every window or capture inequality is a linear consequence of `QCell`. -/
local macro "qclose" : tactic => `(tactic|
  (try (first
    | (refine ⟨?_, ?_⟩ <;> linarith [h.h8, h.h11, h.h12, h.h14, h.h17, h.h18, h.h25, h.h27, h.h30, h.h31, h.h32, h.h34, h.h36,
        h.h37, h.h50, h.h51, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.x8, h.pos1, h.pos2, h.pos3, h.pos4, h.pos5, h.pos6, h.pos7])
    | linarith [h.h8, h.h11, h.h12, h.h14, h.h17, h.h18, h.h25, h.h27, h.h30, h.h31, h.h32, h.h34, h.h36,
        h.h37, h.h50, h.h51, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.x8, h.pos1, h.pos2, h.pos3, h.pos4, h.pos5, h.pos6, h.pos7])))

set_option hygiene false in
/-- Positivity of the readings, as a function. -/
local macro "qpos" : tactic => `(tactic|
  (have hp : ∀ x, 0 < (![a1, a2, a3, a4, a5, a6, a7] : Fin 7 → ℝ) x := by
    intro x; fin_cases x <;> simp [h.pos1, h.pos2, h.pos3, h.pos4, h.pos5, h.pos6, h.pos7]))

set_option hygiene false in
/-- The conditions of a named state: each window or capture is linear in the speeds. -/
local macro "stok " s:ident : tactic => `(tactic|
  (qpos
   intro x
   fin_cases x
   all_goals
     constructor <;> intro hk
     all_goals first
       | (exfalso; simp [$s:ident] at hk; done)
       | skip
   all_goals first
     | (unfold St.time
        refine (window_iff_linear (hp _) _ _).mpr ?_
        simp [$s:ident]
        qclose)
     | (unfold St.time
        refine (capt_iff_linear (hp _) _ _).mpr ?_
        simp [$s:ident]
        qclose)))

set_option hygiene false in
/-- The link between two named states. -/
local macro "stlink " s:ident ", " s':ident : tactic => `(tactic|
  (qpos
   refine ⟨by simp [$s:ident, $s':ident], by simp [$s:ident, $s':ident], ?_⟩
   intro y hy
   fin_cases y
   all_goals first
     | (exfalso; simp [$s:ident] at hy; done)
     | skip
   all_goals
     refine (opening_le_iff (hp _) (hp _) _ _).mpr ?_
     simp [$s:ident, $s':ident]
     qclose))

theorem sA_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sA := by stok sA

theorem sB_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sB := by stok sB

theorem sC_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sC := by stok sC

theorem sS0_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sS0 := by stok sS0

theorem sS1_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sS1 := by stok sS1

theorem sS2_ok {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    StateOK ![a1, a2, a3, a4, a5, a6, a7] sS2 := by stok sS2

theorem link_AB {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    LinkOK ![a1, a2, a3, a4, a5, a6, a7] sA sB := by stlink sA, sB

theorem link_BC {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    LinkOK ![a1, a2, a3, a4, a5, a6, a7] sB sC := by stlink sB, sC

theorem link_CS0 {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    LinkOK ![a1, a2, a3, a4, a5, a6, a7] sC sS0 := by stlink sC, sS0

theorem link_S0S1 {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    LinkOK ![a1, a2, a3, a4, a5, a6, a7] sS0 sS1 := by stlink sS0, sS1

theorem link_S1S2 {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    LinkOK ![a1, a2, a3, a4, a5, a6, a7] sS1 sS2 := by stlink sS1, sS2

/-- **The example chain cell** [L]: every speed vector satisfying the thirty-two inequalities of `QCell` has the cascade follow
`A → B → C → S0 → S1 → S2` and stop at S2, with the laps `(0, 26, 85, 91, 93, 159, 164)` at the end. -/
theorem exChain {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) :
    ChainRun ![a1, a2, a3, a4, a5, a6, a7] 5 exS where
  pos := by
    intro x; fin_cases x <;> simp [h.pos1, h.pos2, h.pos3, h.pos4, h.pos5, h.pos6, h.pos7]
  ok := by
    intro i hi
    interval_cases i
    · exact sA_ok h
    · exact sB_ok h
    · exact sC_ok h
    · exact sS0_ok h
    · exact sS1_ok h
    · exact sS2_ok h
  link := by
    intro i hi
    interval_cases i
    · exact link_AB h
    · exact link_BC h
    · exact link_CS0 h
    · exact link_S0S1 h
    · exact link_S1S2 h
  last := by
    intro x; fin_cases x <;> rfl

#print axioms exChain


/-! ## (8) The example point, the lap vector, the total displacement -/

/-- **The cell is non-empty** [L]: an exact rational point `(1, 207193/1000, 670863/1000, 721147/1000, 369279/500, 1252081/1000,
259453/200)` satisfies all thirty-two inequalities, so the cascade from `1/(8 a1)` follows the six states and stops. -/
theorem qcell_point : QCell 1 (207193 / 1000) (670863 / 1000) (721147 / 1000) (369279 / 500) (1252081 / 1000) (259453 / 200) := by
  constructor <;> norm_num

theorem point_cascadeFixes :
    CascadeFixes (dset ![(1 : ℝ), 207193 / 1000, 670863 / 1000, 721147 / 1000, 369279 / 500, 1252081 / 1000, 259453 / 200])
      ((exS 0).time ![(1 : ℝ), 207193 / 1000, 670863 / 1000, 721147 / 1000, 369279 / 500, 1252081 / 1000, 259453 / 200]) :=
  chain_cascadeFixes (exChain qcell_point)

#print axioms qcell_point
#print axioms point_cascadeFixes

/-- The final lap vector of the example chain, `(0, 26, 85, 91, 93, 159, 164)`. -/
def finalLaps : Fin 7 → ℤ := ![0, 26, 85, 91, 93, 159, 164]

/-- The final lap vector IS the lap vector of the last state [L] (so it is a function of the speeds and the final instant,
`state_determined`). -/
theorem finalLaps_eq : sS2.lap = finalLaps := by
  funext x; fin_cases x <;> rfl

/-- **The final lap vector modulo 8 is not a complete residue system** [L]: its residues are `(0, 2, 5, 3, 5, 7, 4)`, residue `5`
occurs for `a3` and for `a5`, and residues `1`, `6` do not occur.  (The grid statement `Framework.CompleteResidues` is about the
grid indices `idx`, not the laps; the laps are `round (ρ R / 8)`, a quotient-like quantity.) -/
theorem finalLaps_not_complete : ¬ (∀ i j : Fin 7, finalLaps i % 8 = finalLaps j % 8 → i = j) := by
  intro h
  have := h 2 4 (by decide)
  exact absurd this (by decide)

theorem finalLaps_mod8 : (fun i => finalLaps i % 8) = ![0, 2, 5, 3, 5, 7, 4] := by
  funext i; fin_cases i <;> decide

#print axioms finalLaps_eq
#print axioms finalLaps_not_complete
#print axioms finalLaps_mod8

/-- **Total displacement** [L]: along a chain, `R_j = R_0 + Σ_{i<j} (1 - δ_i)/ρ_{i+1}`: the landing coordinate is `1` plus the
sum of the setters' displacements, `δ_i = sres8 (lapfreeReading)` of the next setter at `R_i`. -/
theorem chain_total_displacement {n : ℕ} {m : ℝ} (hm : 0 < m) {a : Fin n → ℝ} {M : ℕ} {s : ℕ → St n} (h : ChainRun a M s) :
    ∀ j, j ≤ M → (s j).R m a = (s 0).R m a +
      ∑ i ∈ Finset.range j, (1 - RealCase.sres8 (lapfreeReading m (a (s (i + 1)).f) ((s i).R m a))) / (a (s (i + 1)).f / m) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Finset.sum_range_succ, ← add_assoc, ← ih (by omega)]
    exact step_R hm (h.ok j (by omega)) (h.link j (by omega)) (h.pos _)

#print axioms chain_total_displacement


/-! ## (9) The sixteen inequalities alone: the cascade from its start follows A, B, C and stops

The chain cell above lists branch conditions (`x1` to `x8`).  Here just the sixteen inequalities of `Codex PrefixCellClosure_v1`
(plus positivity) are assumed, and the branches are split by the cascade itself: at B the runner `a5` is captured or clear; at S0 the
runner `a3` is captured or clear; at S1 the runner `a6` is captured or clear.  The argument is the one of `isMove_of_link` with the
loose band of a runner in place of its kind: a runner in the way inside the band of lap `M` is captured on lap `M`. -/

/-- The sixteen inequalities (and positivity). -/
-- STANDING: DEFINITION
structure Cell16 (a1 a2 a3 a4 a5 a6 a7 : ℝ) : Prop where
  pos1 : 0 < a1
  pos2 : 0 < a2
  pos3 : 0 < a3
  pos4 : 0 < a4
  pos5 : 0 < a5
  pos6 : 0 < a6
  pos7 : 0 < a7
  h8 : 207 * a1 < a2
  h11 : a3 ≤ 671 * a1
  h12 : 721 * a1 ≤ a4
  h14 : 737 * a1 ≤ a5
  h17 : a6 ≤ 1255 * a1
  h18 : 1297 * a1 ≤ a7
  h25 : 673 * a2 ≤ 209 * a3
  h27 : 727 * a2 < 209 * a4
  h30 : 209 * a5 < 745 * a2
  h31 : 1263 * a2 < 209 * a6
  h32 : 19 * a6 < 115 * a2
  h34 : 11 * a7 ≤ 69 * a2
  h36 : 745 * a4 ≤ 729 * a5
  h37 : 1265 * a4 ≤ 729 * a6
  h50 : 437 * a4 < 243 * a7
  h51 : 729 * a7 < 1313 * a4

theorem QCell.toCell16 {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : QCell a1 a2 a3 a4 a5 a6 a7) : Cell16 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨h.pos1, h.pos2, h.pos3, h.pos4, h.pos5, h.pos6, h.pos7, h.h8, h.h11, h.h12, h.h14, h.h17, h.h18, h.h25, h.h27, h.h30, h.h31,
    h.h32, h.h34, h.h36, h.h37, h.h50, h.h51⟩

/-- The opening of the runner of speed `f` on lap `K`. -/
noncomputable abbrev op (K : ℤ) (f : ℝ) : ℝ := ((K : ℝ) + 1 / 8) / f

theorem not_inWay_of_lin {x f : ℝ} (hf : 0 < f) (K N : ℤ) (h1 : (8 * (N : ℝ) + 1) * f ≤ (8 * (K : ℝ) + 1) * x)
    (h2 : (8 * (K : ℝ) + 1) * x ≤ (8 * (N : ℝ) + 7) * f) : ¬ InWay x (op K f) :=
  window_not_inWay ((window_iff_linear hf K N).mpr ⟨h1, h2⟩)

theorem capt_of_lin {x f : ℝ} (hf : 0 < f) (K L : ℤ) (h1 : (8 * (L : ℝ) - 1) * f < (8 * (K : ℝ) + 1) * x)
    (h2 : (8 * (K : ℝ) + 1) * x < (8 * (L : ℝ) + 1) * f) : Capt x (op K f) L :=
  (capt_iff_linear hf K L).mpr ⟨h1, h2⟩

/-- A runner in the way inside the band of lap `M` is captured on lap `M` [L].  [PROVISIONAL: covering]: a band of width `7/4`
against the capture radius `1/8` leaves one integer; supports `isMove_of_bands` and `cell16_fixes` (which lap a runner in the way
is on); serves rule 1 (the setters displace the `d_min` window `[1, 7]`, and the cascade shows where it lands). -/
theorem capt_of_band {y t : ℝ} {M : ℤ} (hw : InWay y t) (h1 : (M : ℝ) - 7 / 8 ≤ y * t) (h2 : y * t ≤ (M : ℝ) + 7 / 8) :
    Capt y t M := by
  obtain ⟨k, hk⟩ := Cascade.exists_near_int hw
  rw [abs_lt] at hk
  have a1 : ((k - M : ℤ) : ℝ) < 1 := by push_cast; linarith
  have a2 : (-1 : ℝ) < ((k - M : ℤ) : ℝ) := by push_cast; linarith
  have b1 : k - M < 1 := by exact_mod_cast a1
  have b2 : -1 < k - M := by exact_mod_cast a2
  have : k = M := by omega
  subst this
  unfold Capt
  rw [abs_lt]
  exact hk

theorem band_of_lin {x f : ℝ} (hf : 0 < f) (K M : ℤ) (h1 : (8 * (M : ℝ) - 7) * f ≤ (8 * (K : ℝ) + 1) * x)
    (h2 : (8 * (K : ℝ) + 1) * x ≤ (8 * (M : ℝ) + 7) * f) : (M : ℝ) - 7 / 8 ≤ x * op K f ∧ x * op K f ≤ (M : ℝ) + 7 / 8 := by
  unfold op
  rw [reading_at_opening hf]
  have h8 : (0 : ℝ) < 8 * f := by positivity
  rw [le_div_iff₀ h8, div_le_iff₀ h8]
  constructor <;> nlinarith

/-- **The move named by a setter, with loose bands for the others** [L].  `x0` is captured at `t` on lap `L0`; every runner of
`ds` is either not in the way, or in the band of some lap `M` with its opening on that lap no later than the opening of `x0`. -/
theorem isMove_of_bands {ds : Finset ℝ} {t x0 : ℝ} {L0 : ℤ} (hx0 : x0 ∈ ds) (hc : Capt x0 t L0)
    (hy : ∀ y ∈ ds, ¬ InWay y t ∨ ∃ M : ℤ, (M : ℝ) - 7 / 8 ≤ y * t ∧ y * t ≤ (M : ℝ) + 7 / 8 ∧
      ((M : ℝ) + 1 / 8) / y ≤ ((L0 : ℝ) + 1 / 8) / x0) :
    IsMove ds t (((L0 : ℝ) + 1 / 8) / x0) := by
  right
  refine ⟨x0, hx0, capt_inWay hc, (Cascade.nextOpening_eq hc).symm, ?_⟩
  intro d' hd' hw
  rcases hy d' hd' with hn | ⟨M, h1, h2, h3⟩
  · exact absurd hw hn
  · have hcm := capt_of_band hw h1 h2
    rw [Cascade.nextOpening_eq hcm]
    exact h3

/-- A setter satisfies its own band condition. -/
theorem disj_self {x t : ℝ} {L : ℤ} (hc : Capt x t L) :
    ¬ InWay x t ∨ ∃ M : ℤ, (M : ℝ) - 7 / 8 ≤ x * t ∧ x * t ≤ (M : ℝ) + 7 / 8 ∧
      ((M : ℝ) + 1 / 8) / x ≤ ((L : ℝ) + 1 / 8) / x := by
  right
  refine ⟨L, ?_, ?_, le_refl _⟩
  · unfold Capt at hc; rw [abs_lt] at hc; linarith [hc.1]
  · unfold Capt at hc; rw [abs_lt] at hc; linarith [hc.2]

theorem cascadeFixes_of_fixed {ds : Finset ℝ} {t : ℝ} (h : IsMove ds t t) : CascadeFixes ds t :=
  ⟨fun _ => t, rfl, fun _ => h, 0, rfl⟩

theorem cascadeFixes_cons {ds : Finset ℝ} {t t' : ℝ} (h : IsMove ds t t') (hf : CascadeFixes ds t') : CascadeFixes ds t := by
  obtain ⟨seq, h0, hmv, N, hN⟩ := hf
  refine ⟨fun k => Nat.casesOn k t (fun j => seq j), rfl, ?_, N + 1, hN⟩
  intro k
  cases k with
  | zero => simpa [h0] using h
  | succ j => exact hmv j

theorem isMove_fixed_of_notInWay {ds : Finset ℝ} {t : ℝ} (h : ∀ y ∈ ds, ¬ InWay y t) : IsMove ds t t := Or.inl ⟨h, rfl⟩

#print axioms capt_of_band
#print axioms isMove_of_bands
#print axioms cascadeFixes_cons

theorem forall_dset7 {a1 a2 a3 a4 a5 a6 a7 : ℝ} {P : ℝ → Prop} (h1 : P a1) (h2 : P a2) (h3 : P a3) (h4 : P a4)
    (h5 : P a5) (h6 : P a6) (h7 : P a7) : ∀ y ∈ dset ![a1, a2, a3, a4, a5, a6, a7], P y := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_dset.mp hy
  fin_cases x
  exacts [h1, h2, h3, h4, h5, h6, h7]

theorem mem_dset7_2 {a1 a2 a3 a4 a5 a6 a7 : ℝ} : a2 ∈ dset ![a1, a2, a3, a4, a5, a6, a7] := mem_dset.mpr ⟨1, rfl⟩
theorem mem_dset7_3 {a1 a2 a3 a4 a5 a6 a7 : ℝ} : a3 ∈ dset ![a1, a2, a3, a4, a5, a6, a7] := mem_dset.mpr ⟨2, rfl⟩
theorem mem_dset7_4 {a1 a2 a3 a4 a5 a6 a7 : ℝ} : a4 ∈ dset ![a1, a2, a3, a4, a5, a6, a7] := mem_dset.mpr ⟨3, rfl⟩
theorem mem_dset7_6 {a1 a2 a3 a4 a5 a6 a7 : ℝ} : a6 ∈ dset ![a1, a2, a3, a4, a5, a6, a7] := mem_dset.mpr ⟨5, rfl⟩
theorem mem_dset7_7 {a1 a2 a3 a4 a5 a6 a7 : ℝ} : a7 ∈ dset ![a1, a2, a3, a4, a5, a6, a7] := mem_dset.mpr ⟨6, rfl⟩


local macro "nw " p:term:max K:term:max N:term:max : term =>
  `(Or.inl (not_inWay_of_lin $p $K $N (by push_cast; linarith) (by push_cast; linarith)))

local macro "nwn " p:term:max K:term:max N:term:max : term =>
  `(not_inWay_of_lin $p $K $N (by push_cast; linarith) (by push_cast; linarith))

/-- **The sixteen inequalities force the cascade from its start to stop** [L].  [PROVISIONAL: covering]: the window and capture
widths at six instants are set against the polytope; supports the statement that this cell of speeds lies in the region where the
cascade fixes (a cell statement, not an existence claim); serves rule 1 (the isolation of the `d_min` window `[1, 7]` is displaced by
the setters `a2, a4, a7` and then by `a3`, `a6` if they are in the way, and the cascade shows where it lands).  For every positive `(a1,…,a7)` satisfying the sixteen
inequalities of `Cell16`, `CascadeFixes` holds from the cascade's start `1/(8 a1) = op 0 a1`.  The cascade passes A, B, C (the PAST
states; their window and capture conditions are implied by the sixteen), reaches the opening of `a7` on lap `164`, and then stops at
S0, or at S1 (after `a3`), or at S2 (after `a3` and `a6`); the branch is the cascade's own.  No hypothesis beyond `Cell16` is used, and
no bound on the number of moves enters any statement: the three exits are the three cases of "in the way or not". -/
theorem cell16_fixes {a1 a2 a3 a4 a5 a6 a7 : ℝ} (h : Cell16 a1 a2 a3 a4 a5 a6 a7) :
    CascadeFixes (dset ![a1, a2, a3, a4, a5, a6, a7]) (op 0 a1) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, h8, h11, h12, h14, h17, h18, h25, h27, h30, h31, h32, h34, h36, h37, h50, h51⟩ := h
  -- A -> B: `a2` is captured on lap 26, the others are in windows
  have hAB : IsMove (dset ![a1, a2, a3, a4, a5, a6, a7]) (op 0 a1) (op 26 a2) := by
    have hc : Capt a2 (op 0 a1) 26 := capt_of_lin p1 0 26 (by push_cast; linarith) (by push_cast; linarith)
    exact isMove_of_bands mem_dset7_2 hc
      (forall_dset7 (nw p1 0 0) (disj_self hc) (nw p1 0 83) (nw p1 0 90) (nw p1 0 92) (nw p1 0 156) (nw p1 0 162))
  -- B -> C: `a4` is captured on lap 91; `a5` and `a6` are in their bands
  have hBC : IsMove (dset ![a1, a2, a3, a4, a5, a6, a7]) (op 26 a2) (op 91 a4) := by
    have hc : Capt a4 (op 26 a2) 91 := capt_of_lin p2 26 91 (by push_cast; linarith) (by push_cast; linarith)
    refine isMove_of_bands mem_dset7_4 hc
      (forall_dset7 (nw p2 26 0) (nw p2 26 26) (nw p2 26 84) (disj_self hc) ?_ ?_ (nw p2 26 163))
    · exact Or.inr ⟨93, (band_of_lin p2 26 93 (by push_cast; linarith) (by push_cast; linarith)).1,
        (band_of_lin p2 26 93 (by push_cast; linarith) (by push_cast; linarith)).2,
        (opening_le_iff p4 p5 91 93).mpr (by push_cast; linarith)⟩
    · exact Or.inr ⟨158, (band_of_lin p2 26 158 (by push_cast; linarith) (by push_cast; linarith)).1,
        (band_of_lin p2 26 158 (by push_cast; linarith) (by push_cast; linarith)).2,
        (opening_le_iff p4 p6 91 158).mpr (by push_cast; linarith)⟩
  -- C -> S0: `a7` is captured on lap 164, the others are in windows
  have hCS : IsMove (dset ![a1, a2, a3, a4, a5, a6, a7]) (op 91 a4) (op 164 a7) := by
    have hc : Capt a7 (op 91 a4) 164 := capt_of_lin p4 91 164 (by push_cast; linarith) (by push_cast; linarith)
    exact isMove_of_bands mem_dset7_7 hc
      (forall_dset7 (nw p4 91 0) (nw p4 91 26) (nw p4 91 84) (nw p4 91 91) (nw p4 91 93) (nw p4 91 158) (disj_self hc))
  refine cascadeFixes_cons hAB (cascadeFixes_cons hBC (cascadeFixes_cons hCS ?_))
  -- S0: the windows of every runner but `a3`
  have w01 : ¬ InWay a1 (op 164 a7) := nwn p7 164 0
  have w02 : ¬ InWay a2 (op 164 a7) := nwn p7 164 26
  have w04 : ¬ InWay a4 (op 164 a7) := nwn p7 164 91
  have w05 : ¬ InWay a5 (op 164 a7) := nwn p7 164 93
  have w06 : ¬ InWay a6 (op 164 a7) := nwn p7 164 158
  have w07 : ¬ InWay a7 (op 164 a7) := nwn p7 164 164
  by_cases hw3 : InWay a3 (op 164 a7)
  · -- `a3` is captured on lap 85
    have hb3 := band_of_lin p7 164 85 (x := a3) (by push_cast; linarith) (by push_cast; linarith)
    have hc3 : Capt a3 (op 164 a7) 85 := capt_of_band hw3 hb3.1 hb3.2
    obtain ⟨c31, c32⟩ := (capt_iff_linear p7 164 85).mp hc3
    push_cast at c31 c32
    refine cascadeFixes_cons (isMove_of_bands mem_dset7_3 hc3
      (forall_dset7 (Or.inl w01) (Or.inl w02) (disj_self hc3) (Or.inl w04) (Or.inl w05) (Or.inl w06) (Or.inl w07))) ?_
    -- S1: the windows of every runner but `a6`
    have v01 : ¬ InWay a1 (op 85 a3) := nwn p3 85 0
    have v02 : ¬ InWay a2 (op 85 a3) := nwn p3 85 26
    have v03 : ¬ InWay a3 (op 85 a3) := nwn p3 85 85
    have v04 : ¬ InWay a4 (op 85 a3) := nwn p3 85 91
    have v05 : ¬ InWay a5 (op 85 a3) := nwn p3 85 93
    have v07 : ¬ InWay a7 (op 85 a3) := nwn p3 85 164
    by_cases hw6 : InWay a6 (op 85 a3)
    · have hb6 := band_of_lin p3 85 159 (x := a6) (by push_cast; linarith) (by push_cast; linarith)
      have hc6 : Capt a6 (op 85 a3) 159 := capt_of_band hw6 hb6.1 hb6.2
      obtain ⟨c61, c62⟩ := (capt_iff_linear p3 85 159).mp hc6
      push_cast at c61 c62
      refine cascadeFixes_cons (isMove_of_bands mem_dset7_6 hc6
        (forall_dset7 (Or.inl v01) (Or.inl v02) (Or.inl v03) (Or.inl v04) (Or.inl v05) (disj_self hc6) (Or.inl v07))) ?_
      -- S2: nobody in the way
      exact cascadeFixes_of_fixed (isMove_fixed_of_notInWay
        (forall_dset7 (nwn p6 159 0) (nwn p6 159 26) (nwn p6 159 85) (nwn p6 159 91) (nwn p6 159 93) (nwn p6 159 159)
          (nwn p6 159 164)))
    · exact cascadeFixes_of_fixed (isMove_fixed_of_notInWay
        (forall_dset7 v01 v02 v03 v04 v05 hw6 v07))
  · exact cascadeFixes_of_fixed (isMove_fixed_of_notInWay
      (forall_dset7 w01 w02 hw3 w04 w05 w06 w07))

#print axioms cell16_fixes


/-! ## (10) Hypothesis tests: which hypotheses are REQUIRED -/

/-- **`0 < f` is REQUIRED for the linear form of a capture** [L]: for `f = -1`, `x = 1/2`, `K = L = 0` the runner is captured
(`x t = -1/16`) while the linear inequalities fail (the interval `(8L-1) f < … < (8L+1) f` reverses). -/
theorem capt_linear_needs_pos :
    Capt (1 / 2 : ℝ) ((((0 : ℤ) : ℝ) + 1 / 8) / (-1)) 0 ∧
    ¬ ((8 * ((0 : ℤ) : ℝ) - 1) * (-1) < (8 * ((0 : ℤ) : ℝ) + 1) * (1 / 2 : ℝ) ∧
        (8 * ((0 : ℤ) : ℝ) + 1) * (1 / 2 : ℝ) < (8 * ((0 : ℤ) : ℝ) + 1) * (-1 : ℝ)) := by
  constructor
  · unfold Capt
    norm_num
  · norm_num

/-- **The maximality clause of the link is REQUIRED** [L]: for `ds = {1, 2}` at `t = 1` both runners are captured (laps `1`, `2`);
the opening of `1` is `9/8`, that of `2` is `17/16`; naming the runner `2` (opening `17/16`) is not a cascade move. -/
theorem link_max_required : ¬ IsMove ({1, 2} : Finset ℝ) 1 (17 / 16) := by
  have h1 : |(1 : ℝ) * 1 - ((1 : ℤ) : ℝ)| < 1 / 8 := by norm_num
  have h2 : |(2 : ℝ) * 1 - ((2 : ℤ) : ℝ)| < 1 / 8 := by norm_num
  have w1 : InWay (1 : ℝ) 1 := capt_inWay (x := 1) (t := 1) (L := 1) h1
  have w2 : InWay (2 : ℝ) 1 := capt_inWay (x := 2) (t := 1) (L := 2) h2
  have n1 : nextOpening (1 : ℝ) 1 = 9 / 8 := by rw [Cascade.nextOpening_eq h1]; norm_num
  have n2 : nextOpening (2 : ℝ) 1 = 17 / 16 := by rw [Cascade.nextOpening_eq h2]; norm_num
  rintro (⟨hn, -⟩ | ⟨d, hd, hw, ht, hmax⟩)
  · exact hn 1 (by simp) w1
  · have h12 := hmax 1 (by simp) w1
    rw [n1] at h12
    norm_num at h12

/-- **The capture is strict** [L]: at exactly `1/8` past a lap the runner is clear (in the window), not captured. -/
theorem capt_strict_example : InWindow (1 : ℝ) (9 / 8) 1 ∧ ¬ Capt (1 : ℝ) (9 / 8) 1 := by
  constructor
  · unfold InWindow; norm_num
  · unfold Capt; norm_num

/-- **A state may have several captured runners** [L]: the state B of the example has `a4`, `a5`, `a6` captured; the named setter
is the one with the latest opening, not the sole captured runner. -/
theorem sB_three_captured : sB.kind 3 = Kind.capt ∧ sB.kind 4 = Kind.capt ∧ sB.kind 5 = Kind.capt := ⟨rfl, rfl, rfl⟩

#print axioms capt_linear_needs_pos
#print axioms link_max_required
#print axioms capt_strict_example
#print axioms sB_three_captured

/-! ## (11) The grid-plus-deviation coordinates of the example point

At the rational point `(1, 207193/1000, 670863/1000, 721147/1000, 369279/500, 1252081/1000, 259453/200)` with `m = a1 = 1`. -/

theorem idx_eq_of {m d : ℝ} (c : ℤ) (h1 : (c : ℝ) - 1 / 2 ≤ d / m) (h2 : d / m < (c : ℝ) + 1 / 2) : NormalForm.idx m d = c :=
  NormalForm.round_eq_int _ _ h1 h2

/-- The residue representatives `ridx` of the seven readings at the example point: `(1, 7, 7, 1, 3, 4, 1)` [L]. -/
theorem point_ridx :
    QuotientReduction.ridx 1 (1 : ℝ) = 1 ∧ QuotientReduction.ridx 1 (207193 / 1000 : ℝ) = 7 ∧
    QuotientReduction.ridx 1 (670863 / 1000 : ℝ) = 7 ∧ QuotientReduction.ridx 1 (721147 / 1000 : ℝ) = 1 ∧
    QuotientReduction.ridx 1 (369279 / 500 : ℝ) = 3 ∧ QuotientReduction.ridx 1 (1252081 / 1000 : ℝ) = 4 ∧
    QuotientReduction.ridx 1 (259453 / 200 : ℝ) = 1 := by
  have i1 : NormalForm.idx 1 (1 : ℝ) = 1 := idx_eq_of 1 (by norm_num) (by norm_num)
  have i2 : NormalForm.idx 1 (207193 / 1000 : ℝ) = 207 := idx_eq_of 207 (by norm_num) (by norm_num)
  have i3 : NormalForm.idx 1 (670863 / 1000 : ℝ) = 671 := idx_eq_of 671 (by norm_num) (by norm_num)
  have i4 : NormalForm.idx 1 (721147 / 1000 : ℝ) = 721 := idx_eq_of 721 (by norm_num) (by norm_num)
  have i5 : NormalForm.idx 1 (369279 / 500 : ℝ) = 739 := idx_eq_of 739 (by norm_num) (by norm_num)
  have i6 : NormalForm.idx 1 (1252081 / 1000 : ℝ) = 1252 := idx_eq_of 1252 (by norm_num) (by norm_num)
  have i7 : NormalForm.idx 1 (259453 / 200 : ℝ) = 1297 := idx_eq_of 1297 (by norm_num) (by norm_num)
  unfold QuotientReduction.ridx
  rw [i1, i2, i3, i4, i5, i6, i7]
  norm_num

/-- **At the example point the grid indices are not a complete residue system** [L]: the residues `1` (three times) and `7`
(twice) repeat, so the point is not a small deformation of a complete grid at the cascade's start `R = 1`
(`Framework.CompleteResidues` on the readings fails). -/
theorem point_not_complete :
    ¬ (∀ i j : Fin 7, (![1, 7, 7, 1, 3, 4, 1] : Fin 7 → ℤ) i % 8 = (![1, 7, 7, 1, 3, 4, 1] : Fin 7 → ℤ) j % 8 → i = j) := by
  intro h
  have := h 1 2 (by decide)
  exact absurd this (by decide)

#print axioms point_ridx
#print axioms point_not_complete


/-! ## Axioms of the remaining theorems -/

#print axioms capt_inWay
#print axioms inWay_capt
#print axioms window_not_inWay
#print axioms not_inWay_window
#print axioms inWay_or_window
#print axioms capt_unique
#print axioms window_lap
#print axioms capt_lap
#print axioms capt_not_window
#print axioms reading_at_opening
#print axioms capt_iff_linear
#print axioms window_iff_linear
#print axioms opening_le_iff
#print axioms mem_dset
#print axioms time_eq_R
#print axioms sA_ok
#print axioms sB_ok
#print axioms sC_ok
#print axioms sS0_ok
#print axioms sS1_ok
#print axioms sS2_ok
#print axioms link_AB
#print axioms link_BC
#print axioms link_CS0
#print axioms link_S0S1
#print axioms link_S1S2
#print axioms QCell.toCell16
#print axioms not_inWay_of_lin
#print axioms capt_of_lin
#print axioms band_of_lin
#print axioms disj_self
#print axioms cascadeFixes_of_fixed
#print axioms isMove_fixed_of_notInWay
#print axioms forall_dset7
#print axioms mem_dset7_2
#print axioms mem_dset7_3
#print axioms mem_dset7_4
#print axioms mem_dset7_6
#print axioms mem_dset7_7
#print axioms idx_eq_of

end Fresh.ChainCell
