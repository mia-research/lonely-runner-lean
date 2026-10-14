import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.LonelyCells

/-!
# Types of cascade outcome: the d_min gate, the closer, and why lap-labelled types are unbounded (Task U)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Dilation`, `ChainLaws`,
`LonelyCells` (for `Localisation.clear_iff_fract`); nothing from the existing `LonelyRunner` repo.  Exact reals only;
every disparity is positive (no runner is stationary).  Every statement is symbolic: for every finite set `ds` of
positive disparities with least element `m` (the cascade coordinate is `R = 8·m·t`, so `R = 7` is `t = 7/(8m)` and
`R = 9` is `t = 9/(8m)`).

The exact-data investigation behind this file (all 7-subsets of `{1, …, N}` with gcd 1, `N ≤ 56`, exact integer
cascade, independently re-implemented in Fractions and compared on every set with `N ≤ 22`) is in the scratch
directory of Task U, not in the repo.  The statements below are the parts of it that hold for every arrangement and
that could be proved.

Results (each [L] has its `#print axioms` line below it).
* (1) The d_min gate (record L1, E340; v9 section 7):
  `gate_entry`: the first state above `R = 7` lies in `(7, 9)` and `d_min` is in the way there;
  `gate_next`: the move from that state reaches `R ≥ 9`;
  `inWay_dmin_of_gate`: no instant of `(7, 9)` is lonely (`d_min` is in the way on all of it);
  `gate_crossing`: along the cascade from the bound, if some state exceeds `R = 7` then there is a step
  `R_n ≤ 7 < R_{n+1} < 9` with `d_min` in the way at `R_{n+1}` and `R_{n+2} ≥ 9`.
* (2) The pre-crossing reduction `late_blocker_forces_slow_lap_one`: if at the first state above 7 some runner `y`
  other than `d_min` is in the way with its next opening beyond `R = 9` (the only way `d_min` can fail to SET the
  crossing move, the record's E340 claim), then the setter `x` of the move into the gate is on lap 1 and
  `15·x < 17·m` (its reading is below `17/15`), and `y` is on a lap `≥ 2`.  Pure arithmetic of the two zones; it uses
  neither the maximality of the move nor any other runner.  Corollary `strong_gate_of_gap`: if every other reading is
  at least `17/15`, the move out of the gate goes to exactly `R = 9` (set by `d_min`).
* (3) The closer: `clear_interval_length`: a runner clear on all of `[u, w]` has `d·(w − u) ≤ 3/4`;
  `lonely_interval_length`: on a lonely interval every disparity obeys it.  Consequence [reasoned in the comment
  there]: the closer is `d_min` (the landing cell ends at `R = 7`) only if `R* ≥ 7 − 6/ρ_max`.
* (4) `firstMove_lap`: for every `j ≥ 1` the set `{1, 2, 3, 4, 5, 6, 8j}` has its first cascade move set by `8j`
  on lap `j`: the (rank, lap) letters, hence the full types, are unbounded, and the lap is a scale label.
* (5) Integer disparities with `d_min ∈ {1, 2}`: `int_lonely_shift` (the lonely set is invariant under `t ↦ t + k`,
  `t ↦ k − t`), `first_window_of_small_dmin` (any isolation is carried into `R ∈ [1, 7]`), `no_crossing_of_small_dmin`
  (with any isolation, the cascade never leaves `[1, 7]`): an integer gate crosser with `d_min ≤ 2` would be a
  counterexample.  Says nothing for `d_min ≥ 3`.
* (6) `StrongGate` (OWED): `d_min` sets the move out of the gate (equivalently no runner in the way at the first state
  above 7 has its next opening beyond 9).  Tested, not proved: 0 counterexamples among all 47 integer gate
  crossers with `a₇ ≤ 70`, 34,672 perturbed crossers, and the exhaustive families tried with `ρ₂ < 17/15` (which contain no
  crosser at all); by (2) a counterexample needs `ρ₂ < 17/15`.

Provenance.  (1) is the record's gate lemma L1(a)–(c) and E340 (`GATE_LEMMAS_v1`, MECHANISM_MAP_v5 §11.9), proved
there by hand, and in the existing tree `LRC/Spec/FirstGateN.lean` (`move_lt_nine_of_le_seven`, `move_ge_nine`,
`lonely_above_seven_iff`, for readings normalised to `d_min = 1`); that file states that the width argument does not
prove a visit to 9 and proves the strong form only under the gap hypothesis `d ≥ 2` (`forced_nearest_move`,
`crossing_forces_nearest_setter`).  Its arguments were read and understood; the proofs here were written for this
file, in `t` with a general `m`.  (2) and `strong_gate_of_gap` are new: they lower that gap hypothesis from `2` to
`17/15` and say exactly what a counterexample to the strong form must look like.  (3) is the window length of the
boundary-set method (v9 §1; Fresh `Carving.window_length` states the length of one window, not this converse).
(4) is the record's D_max family (v9 §3, `(1, …, 7, 8m)`), here at the bound.  (5) uses the record's mirror
identity (E342) for whole-number readings.  Every proof was written for this file;
none was copied.
-/

open Classical

namespace Fresh

namespace Types

open Cascade Dilation

/-! ## (1) The d_min gate -/

/-- **The first state above `R = 7` lies below `R = 9`, and `d_min` is in the way there.**  If a move goes from
`t ≤ 7/(8m)` to `t' > 7/(8m)`, every disparity is at least `m > 0`, then `t' < 9/(8m)` and `InWay m t'`.
The setter's zone has width `1/(4x) ≤ 1/(4m)` in `t` (gap below 2). -/
theorem gate_entry {ds : Finset ℝ} {m t t' : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    (ht : t ≤ 7 / (8 * m)) (ht' : 7 / (8 * m) < t') (hmv : IsMove ds t t') :
    t' < 9 / (8 * m) ∧ InWay m t' := by
  have hlt : t < t' := lt_of_le_of_lt ht ht'
  have hstep : t' < 9 / (8 * m) := by
    rcases hmv with ⟨_, rfl⟩ | ⟨x, hx, hw, rfl, _⟩
    · exact absurd hlt (lt_irrefl _)
    · have hx0 : 0 < x := lt_of_lt_of_le hm (hlow x hx)
      rw [nextOpening_eq_add_gap hx0 hw]
      have hg := gap_lt_two hw
      have hg0 := gap_pos hw
      have h1 : gap x t / (8 * x) < 2 / (8 * x) := by
        apply div_lt_div_of_pos_right hg (by positivity)
      have h2 : 2 / (8 * x) ≤ 2 / (8 * m) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        linarith [hlow x hx]
      have h3 : 7 / (8 * m) + 2 / (8 * m) = 9 / (8 * m) := by ring
      linarith
  refine ⟨hstep, ?_⟩
  -- `m t'` lies in `(7/8, 9/8)`, within `1/8` of the integer `1`.
  have a1 : 7 / 8 < m * t' := by
    rw [div_lt_iff₀ (by positivity)] at ht'
    linarith
  have a2 : m * t' < 9 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at hstep
    linarith
  unfold InWay
  refine lt_of_le_of_lt (Cascade.distInt_le (m * t') 1) ?_
  rw [Int.cast_one, abs_lt]
  constructor <;> linarith

#print axioms gate_entry

/-- **`d_min` is in the way on all of `(7, 9)`**: no instant `t` with `7/(8m) < t < 9/(8m)` is clear for `m`. -/
theorem inWay_dmin_of_gate {m t : ℝ} (hm : 0 < m) (h1 : 7 / (8 * m) < t) (h2 : t < 9 / (8 * m)) : InWay m t := by
  have a1 : 7 / 8 < m * t := by
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have a2 : m * t < 9 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  unfold InWay
  refine lt_of_le_of_lt (Cascade.distInt_le (m * t) 1) ?_
  rw [Int.cast_one, abs_lt]
  constructor <;> linarith

#print axioms inWay_dmin_of_gate

/-- `d_min`'s next opening from inside the gate is `R = 9`. -/
theorem nextOpening_dmin_of_gate {m t : ℝ} (hm : 0 < m) (h1 : 7 / (8 * m) < t) (h2 : t < 9 / (8 * m)) :
    nextOpening m t = 9 / (8 * m) := by
  have a1 : 7 / 8 < m * t := by
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have a2 : m * t < 9 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  have hk : |m * t - ((1 : ℤ) : ℝ)| < 1 / 8 := by
    rw [Int.cast_one, abs_lt]
    constructor <;> linarith
  rw [nextOpening_eq hk]
  field_simp
  norm_num

#print axioms nextOpening_dmin_of_gate

/-- **The move out of the gate reaches `R ≥ 9`**: from `t'` in `(7/(8m), 9/(8m))`, with `m ∈ ds`, the next state is at
least `9/(8m)` (`d_min` is in the way, and the move goes to the largest next opening). -/
theorem gate_next {ds : Finset ℝ} {m t' t'' : ℝ} (hm : 0 < m) (hmem : m ∈ ds)
    (h1 : 7 / (8 * m) < t') (h2 : t' < 9 / (8 * m)) (hmv : IsMove ds t' t'') : 9 / (8 * m) ≤ t'' := by
  have hw := inWay_dmin_of_gate hm h1 h2
  rcases hmv with ⟨hno, _⟩ | ⟨x, _, _, rfl, hmax⟩
  · exact absurd hw (hno m hmem)
  · rw [← nextOpening_dmin_of_gate hm h1 h2]
    exact hmax m hmem hw

#print axioms gate_next

/-- **The gate along a cascade.**  For the cascade sequence from the bound `1/(8m)` (`m` the least disparity), if some
state exceeds `7/(8m)` then there is a step `n` with `seq n ≤ 7/(8m) < seq (n+1) < 9/(8m)`, `d_min` in the way at
`seq (n+1)`, and `seq (n+2) ≥ 9/(8m)`.  So a cascade that leaves the first window of `d_min` passes through `(7, 9)`
and then jumps to `R ≥ 9`; no landing lies in `(7, 9)`. -/
theorem gate_crossing {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hmem : m ∈ ds) (hlow : ∀ d ∈ ds, m ≤ d)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)))
    (hcross : ∃ N, 7 / (8 * m) < seq N) :
    ∃ n, seq n ≤ 7 / (8 * m) ∧ 7 / (8 * m) < seq (n + 1) ∧ seq (n + 1) < 9 / (8 * m) ∧
      InWay m (seq (n + 1)) ∧ 9 / (8 * m) ≤ seq (n + 2) := by
  classical
  let N := Nat.find hcross
  have hN : 7 / (8 * m) < seq N := Nat.find_spec hcross
  have hN0 : N ≠ 0 := by
    intro h
    have : 7 / (8 * m) < seq 0 := h ▸ hN
    rw [h0] at this
    have : 1 / (8 * m) < 1 / (8 * m) := by
      calc 1 / (8 * m) ≤ 7 / (8 * m) := by
            apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
        _ < 1 / (8 * m) := this
    exact lt_irrefl _ this
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hle : seq n ≤ 7 / (8 * m) := by
    have := Nat.find_min hcross (show n < N by omega)
    exact not_lt.mp this
  have hsn : seq (n + 1) = seq N := by rw [hn]
  have hgt : 7 / (8 * m) < seq (n + 1) := hsn ▸ hN
  obtain ⟨hlt9, hw⟩ := gate_entry hm hlow hle hgt (hmv n)
  exact ⟨n, hle, hgt, hlt9, hw, gate_next hm hmem hgt hlt9 (hmv (n + 1))⟩

#print axioms gate_crossing

/-! ## (2) The pre-crossing reduction

At the first state `t'` above `7/(8m)` the runners in the way are `d_min` (next opening `9/(8m)`) and possibly others.
The record (E340) states that `d_min` SETS the next move.  It does unless some `y` in the way at `t'` has its next
opening beyond `9/(8m)`.  The theorem below says what such a `y` forces on the move INTO the gate: the setter `x` of
that move is on lap 1 with reading below `17/15`.  The proof uses only the zone of `x` (containing `t ≤ 7/(8m)`, exit
`t'`) and the zone of `y` (containing `t'`, exit beyond `9/(8m)`). -/

/-- **A late blocker at the gate forces a slow setter on lap 1.**  Let `x ≥ m` be in the way at `t` with
`1/(8m) ≤ t ≤ 7/(8m)` and `t' = nextOpening x t`; let `y ≥ m` be in the way at `t'` with
`9/(8m) < nextOpening y t'`.  Then `lap x t = 1`, `15 x < 17 m`, and `lap y t' ≥ 2`. -/
theorem late_blocker_forces_slow_lap_one {m x y t t' : ℝ} (hm : 0 < m) (hmx : m ≤ x) (hmy : m ≤ y)
    (hb : 1 / (8 * m) ≤ t) (ht : t ≤ 7 / (8 * m)) (hwx : InWay x t) (hset : t' = nextOpening x t)
    (hwy : InWay y t') (hlate : 9 / (8 * m) < nextOpening y t') :
    lap x t = 1 ∧ 15 * x < 17 * m ∧ 2 ≤ lap y t' := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hmx
  have hy0 : 0 < y := lt_of_lt_of_le hm hmy
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hb
  -- the setter `x`: lap `N ≥ 1`, `x t > N − 1/8`, `x t' = N + 1/8`
  set N := lap x t with hNdef
  have hN1 : 1 ≤ N := one_le_lap_of_bound hm hmx hb hwx
  have hxt := abs_lt.mp (abs_sub_lap_lt hwx)
  rw [← hNdef] at hxt
  have hxt' : x * t' = (N : ℝ) + 1 / 8 := by rw [hset]; exact setter_reading hx0 hwx
  have hmt : m * t ≤ 7 / 8 := by
    rw [le_div_iff₀ (by positivity)] at ht
    linarith
  have ht'pos : 0 < t' := by rw [hset]; exact lt_trans ht0 (lt_nextOpening hx0 hwx)
  -- the late blocker `y`: lap `k`, `y t' > k − 1/8`, `9 y < m (8k + 1)`
  set k := lap y t' with hkdef
  have hyt := abs_lt.mp (abs_sub_lap_lt hwy)
  rw [← hkdef] at hyt
  have hyo : nextOpening y t' = ((k : ℝ) + 1 / 8) / y := nextOpening_eq_lap hwy
  rw [hyo, div_lt_div_iff₀ (by positivity) hy0] at hlate
  -- hlate : 9 * y < ((k : ℝ) + 1/8) * (8 * m)
  have hk2 : (2 : ℤ) ≤ k := by
    have : (1 : ℝ) < (k : ℝ) := by nlinarith
    have : (1 : ℤ) < k := by exact_mod_cast this
    omega
  have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  -- from `y`: `136 · m t' > 135`
  have hmt'y : 135 < 136 * (m * t') := by
    -- 9 y t' < (k + 1/8) 8 m t'  and  y t' > k − 1/8
    have e1 : 9 * (y * t') < ((k : ℝ) + 1 / 8) * (8 * (m * t')) := by nlinarith
    have e2 : 9 * ((k : ℝ) - 1 / 8) < ((k : ℝ) + 1 / 8) * (8 * (m * t')) := by nlinarith
    nlinarith
  -- from `x`: `m t' · (N − 1/8) < (7/8)(N + 1/8)`
  have hxm : m * t' * ((N : ℝ) - 1 / 8) < 7 / 8 * ((N : ℝ) + 1 / 8) := by
    -- m t' (x t) = (m t)(x t') and x t > N − 1/8, m t ≤ 7/8
    have e : m * t' * (x * t) = m * t * (x * t') := by ring
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hmt'0 : 0 < m * t' := by positivity
    have hmt0 : 0 < m * t := by positivity
    calc m * t' * ((N : ℝ) - 1 / 8) < m * t' * (x * t) := by
          apply mul_lt_mul_of_pos_left _ hmt'0
          linarith [hxt.1]
      _ = m * t * (x * t') := e
      _ ≤ 7 / 8 * ((N : ℝ) + 1 / 8) := by
          rw [hxt']
          apply mul_le_mul_of_nonneg_right hmt
          have : (1 : ℝ) ≤ (N : ℝ) := hNr
          linarith
  have hN : N = 1 := by
    by_contra hne
    have hN2 : (2 : ℤ) ≤ N := by omega
    have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    -- with N ≥ 2: m t' < (7/8)(8N+1)/(8N−1) ≤ 119/120 < 135/136
    nlinarith
  refine ⟨hN, ?_, hk2⟩
  -- with N = 1: x t' = 9/8 and 136 m t' > 135 give 15 x < 17 m
  rw [hN] at hxt'
  push_cast at hxt'
  nlinarith

#print axioms late_blocker_forces_slow_lap_one


/-- **The strong gate under a gap hypothesis.**  If every disparity other than `d_min = m` has `15 d ≥ 17 m` (reading at
least `17/15`), then at the first state above `R = 7` the cascade moves to exactly `R = 9`: `d_min` sets the move out of
the gate.  (The existing `Spec/FirstGateN.lean` proves this with the hypothesis `d ≥ 2m`; `late_blocker_forces_slow_lap_one`
lowers the threshold to `17/15`.) -/
theorem strong_gate_of_gap {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hmem : m ∈ ds)
    (hgap : ∀ d ∈ ds, d = m ∨ 17 * m ≤ 15 * d)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ}
    (hle : seq n ≤ 7 / (8 * m)) (hgt : 7 / (8 * m) < seq (n + 1)) : seq (n + 2) = 9 / (8 * m) := by
  have hlow : ∀ d ∈ ds, m ≤ d := by
    intro d hd
    rcases hgap d hd with h | h
    · exact le_of_eq h.symm
    · linarith
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  obtain ⟨hlt9, hw⟩ := gate_entry hm hlow hle hgt (hmv n)
  have hge := gate_next hm hmem hgt hlt9 (hmv (n + 1))
  have hb : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  -- the setter `x` of the move into the gate
  obtain ⟨x, hx, hwx, hsx⟩ : ∃ x ∈ ds, InWay x (seq n) ∧ seq (n + 1) = nextOpening x (seq n) := by
    rcases hmv n with ⟨_, h⟩ | ⟨x, hx, hwx, hsx, _⟩
    · exact absurd (h ▸ hgt) (not_lt.mpr hle)
    · exact ⟨x, hx, hwx, hsx⟩
  -- every runner in the way at `seq (n+1)` has its next opening at or before `9/(8m)`
  have hall : ∀ y ∈ ds, InWay y (seq (n + 1)) → nextOpening y (seq (n + 1)) ≤ 9 / (8 * m) := by
    intro y hy hwy
    by_contra hc
    push Not at hc
    obtain ⟨hlap, h15, -⟩ := late_blocker_forces_slow_lap_one hm (hlow x hx) (hlow y hy) hb hle hwx hsx hwy hc
    rcases hgap x hx with hxm | h17
    · -- `x = m` on lap 1 would put `m · seq n` above `7/8`
      have h1 := abs_lt.mp (abs_sub_lap_lt hwx)
      rw [hlap, hxm] at h1
      have : m * seq n ≤ 7 / 8 := by
        rw [le_div_iff₀ (by positivity)] at hle
        linarith
      push_cast at h1
      linarith
    · linarith
  rcases hmv (n + 1) with ⟨hno, _⟩ | ⟨d, hd, hwd, hsd, _⟩
  · exact absurd hw (hno m hmem)
  · rw [show n + 1 + 1 = n + 2 by omega] at hsd
    exact le_antisymm (hsd ▸ hall d hd hwd) hge

#print axioms strong_gate_of_gap

/-! ## (3) The closer: a lonely stretch is at most `3/(4 d)` long for every disparity `d` -/

/-- **A runner clear on all of `[u, w]` has `d (w − u) ≤ 3/4`**: the clear set of `d` is a union of closed windows of
length `3/(4d)` separated by open zones, and a connected stretch lies in one window. -/
theorem clear_interval_length {d u w : ℝ} (hd : 0 < d) (huw : u ≤ w)
    (hc : ∀ s ∈ Set.Icc u w, (1 / 8 : ℝ) ≤ distInt (d * s)) : d * (w - u) ≤ 3 / 4 := by
  by_contra hcon
  push Not at hcon
  have hu := (Localisation.clear_iff_fract (d * u)).mp (hc u ⟨le_rfl, huw⟩)
  set P := ⌊d * u⌋ with hP
  have hfr : Int.fract (d * u) = d * u - P := rfl
  rw [hfr] at hu
  -- the integer `P + 1` is reached inside `[d u, d w]`, or `d w` sits within `1/8` below it
  by_cases hreach : (P : ℝ) + 1 ≤ d * w
  · -- the instant `s = (P + 1)/d` is in `[u, w]` and `d s = P + 1` is an integer
    set s := ((P : ℝ) + 1) / d with hs
    have hds : d * s = ((P + 1 : ℤ) : ℝ) := by rw [hs]; push_cast; field_simp
    have hsu : u ≤ s := by
      rw [hs, le_div_iff₀ hd]; linarith
    have hsw : s ≤ w := by
      rw [hs, div_le_iff₀ hd]; linarith
    have := hc s ⟨hsu, hsw⟩
    rw [hds, Localisation.distInt_intCast] at this
    norm_num at this
  · push Not at hreach
    have hw := hc w ⟨huw, le_rfl⟩
    have hlt : distInt (d * w) < 1 / 8 := by
      refine lt_of_le_of_lt (Cascade.distInt_le (d * w) (P + 1)) ?_
      push_cast
      rw [abs_lt]
      constructor <;> nlinarith
    linarith

#print axioms clear_interval_length

/-- **On a lonely interval every disparity obeys the length bound.**  If every instant of `[u, w]` is lonely for `ds`,
then `d (w − u) ≤ 3/4` for every `d ∈ ds`.

[reasoned] Read at the landing cell `[t*, w]` with the closer equal to `d_min` (the cell ends at `w = 7/(8m)`, where
`d_min` enters): `R* ≥ 7 − 6/ρ_max` with `ρ_max = d_max/m`.  When `ρ_max > 7` (otherwise the cascade lands at `R = 1`,
record R1, and `[1, 7]` cannot be clear for a reading above 1) this puts the landing in `(6, 7]` with all of `[1, R*)`
blocked: a closer equal to `d_min` occurs only at near-crossers.  In the integer data the opener/closer class
`(7, 1)` first appears at `(6, 18, 23, 29, 32, 40, 50)`, in the same family as the first crossers. -/
theorem lonely_interval_length {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w : ℝ} (huw : u ≤ w)
    (hl : ∀ s ∈ Set.Icc u w, LonelyAt ds s) : ∀ d ∈ ds, d * (w - u) ≤ 3 / 4 :=
  fun d hd => clear_interval_length (hpos d hd) huw (fun s hs => hl s hs d hd)

#print axioms lonely_interval_length

/-! ## (4) The lap is a scale label: (rank, lap) letters are unbounded -/

/-- The family `{1, 2, 3, 4, 5, 6, 8j}` (the record's D_max family at the bound, every speed positive). -/
noncomputable def family (j : ℕ) : Finset ℝ := {1, 2, 3, 4, 5, 6, 8 * (j : ℝ)}

/-- A reading `k ∈ {1, …, 7}` is clear at `t = 1/8` (it stands at `k/8`). -/
theorem small_clear_at_eighth {k : ℝ} (h1 : 1 ≤ k) (h7 : k ≤ 7) : ¬ InWay k (1 / 8) := by
  rw [not_inWay_iff, Localisation.clear_iff_fract]
  have h0 : ⌊k * (1 / 8)⌋ = 0 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  rw [Int.fract, h0]
  push_cast
  constructor <;> linarith

#print axioms small_clear_at_eighth

/-- **For every `j ≥ 1`, the first cascade move of `{1, …, 6, 8j}` from the bound `1/8` is set by `8j` on lap `j`**:
`8j` is in the way at `1/8` with lap `j`, the others are clear, and the move lands at `(j + 1/8)/(8j)`.  Distinct `j`
give distinct first letters `(rank 7, lap j)`, so the set of full types (words of (rank, lap)) is infinite; the lap
grows with the ratio `d_max/d_min` and carries the scale, not the mechanism (the rank word `(7)` is the same for
every `j`). -/
theorem firstMove_lap (j : ℕ) (hj : 1 ≤ j) :
    InWay (8 * (j : ℝ)) (1 / 8) ∧ lap (8 * (j : ℝ)) (1 / 8) = j ∧
      IsMove (family j) (1 / 8) (((j : ℝ) + 1 / 8) / (8 * (j : ℝ))) := by
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hread : 8 * (j : ℝ) * (1 / 8) = ((j : ℤ) : ℝ) := by push_cast; ring
  have hw : InWay (8 * (j : ℝ)) (1 / 8) := by
    unfold InWay
    rw [hread, Localisation.distInt_intCast]
    norm_num
  have hlap : lap (8 * (j : ℝ)) (1 / 8) = j := by
    unfold lap; rw [hread, round_intCast]
  refine ⟨hw, hlap, Or.inr ⟨8 * (j : ℝ), by simp [family], hw, ?_, ?_⟩⟩
  · rw [nextOpening_eq_lap hw, hlap]; push_cast; ring
  · intro d' hd' hw'
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · exact absurd hw' (small_clear_at_eighth (by norm_num) (by norm_num))
    · rw [nextOpening_eq_lap hw, hlap]; push_cast; ring_nf; exact le_rfl

#print axioms firstMove_lap

/-- The first letters differ for different `j`: the laps are `j` and `j'`. -/
theorem firstMove_lap_injective {j j' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (h : lap (8 * (j : ℝ)) (1 / 8) = lap (8 * (j' : ℝ)) (1 / 8)) : j = j' := by
  rw [(firstMove_lap j hj).2.1, (firstMove_lap j' hj').2.1] at h
  exact_mod_cast h

#print axioms firstMove_lap_injective


/-! ## (5) Integer disparities with `d_min ∈ {1, 2}`: a gate crossing would be a counterexample

For integer disparities the lonely set is invariant under `t ↦ t + k` and `t ↦ k − t` (`k` an integer).  When
`d_min = 1` the clear windows of `d_min` in one period are `[1/8, 7/8]` alone; when `d_min = 2` they are
`[1/16, 7/16]` and its mirror `[9/16, 15/16]`.  So every isolation is carried by the symmetries into the FIRST window of
`d_min` (`R ∈ [1, 7]`), and the cascade from the bound never crosses the gate unless the subject has no isolation at
all.  For `d_min ≥ 3` the middle windows have no mirror image in the first window and this argument says nothing.
This is the symbolic reason behind half of the observation "no integer gate crosser with `a₁ ≤ 5`" (exhaustive to
`a₇ ≤ 100`); the cases `a₁ = 3, 4, 5` are observed only. -/

/-- **Integer readings: the lonely set is invariant under `t ↦ t + k` and `t ↦ k − t`.** -/
theorem int_lonely_shift {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {t : ℝ} (k : ℤ)
    (hl : LonelyAt ds t) : LonelyAt ds (t + k) ∧ LonelyAt ds (k - t) := by
  constructor
  · intro d hd
    obtain ⟨z, rfl⟩ := hint d hd
    have e : (z : ℝ) * (t + k) = (z : ℝ) * t + ((z * k : ℤ) : ℝ) := by push_cast; ring
    rw [e, Cascade.distInt_add_int]
    exact hl _ hd
  · intro d hd
    obtain ⟨z, rfl⟩ := hint d hd
    have e : (z : ℝ) * (k - t) = -((z : ℝ) * t) + ((z * k : ℤ) : ℝ) := by push_cast; ring
    rw [e, Cascade.distInt_add_int, Cascade.distInt_neg]
    exact hl _ hd

#print axioms int_lonely_shift

/-- **First window for `d_min ∈ {1, 2}`.**  For integer disparities containing `m = 1` or `m = 2`, any lonely instant
yields a lonely instant in `[1/(8m), 7/(8m)]` (in `R`: in `[1, 7]`). -/
theorem first_window_of_small_dmin {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {m : ℝ}
    (hm : m = 1 ∨ m = 2) (hmem : m ∈ ds) {t : ℝ} (hl : LonelyAt ds t) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  set f := t + ((-⌊t⌋ : ℤ) : ℝ) with hf
  have hlf : LonelyAt ds f := (int_lonely_shift hint (-⌊t⌋) hl).1
  have hf0 : 0 ≤ f := by rw [hf]; push_cast; linarith [Int.floor_le t]
  have hf1 : f < 1 := by rw [hf]; push_cast; linarith [Int.lt_floor_add_one t]
  have hc := (Localisation.clear_iff_fract (m * f)).mp (hlf m hmem)
  rcases hm with rfl | rfl
  · have hfr : Int.fract (1 * f) = f := by rw [one_mul]; exact Int.fract_eq_self.mpr ⟨hf0, hf1⟩
    rw [hfr] at hc
    exact ⟨f, by norm_num; linarith [hc.1], by norm_num; linarith [hc.2], hlf⟩
  · by_cases h2 : 2 * f < 1
    · have hfr : Int.fract (2 * f) = 2 * f := Int.fract_eq_self.mpr ⟨by linarith, h2⟩
      rw [hfr] at hc
      exact ⟨f, by norm_num; linarith [hc.1], by norm_num; linarith [hc.2], hlf⟩
    · push Not at h2
      have hfr : Int.fract (2 * f) = 2 * f - 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 1, by push_cast; ring⟩
      rw [hfr] at hc
      have hls : LonelyAt ds ((1 : ℤ) - f) := (int_lonely_shift hint 1 hlf).2
      push_cast at hls
      exact ⟨1 - f, by norm_num; linarith [hc.2], by norm_num; linarith [hc.1], hls⟩

#print axioms first_window_of_small_dmin

/-- **No gate crossing for integer disparities with `d_min ∈ {1, 2}` unless there is no isolation at all.**  If such a
set has any lonely instant, every state of the cascade from the bound `1/(8m)` is at most `7/(8m)` (`R ≤ 7`).
Contrapositive: an integer gate crosser with `d_min ≤ 2` would be a counterexample. -/
theorem no_crossing_of_small_dmin {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z)
    {m : ℝ} (hm : m = 1 ∨ m = 2) (hmem : m ∈ ds) {t : ℝ} (hl : LonelyAt ds t) :
    ∀ n, cascadeSeq ds (1 / (8 * m)) n ≤ 7 / (8 * m) := by
  obtain ⟨s, hs1, hs7, hls⟩ := first_window_of_small_dmin hint hm hmem hl
  intro n
  exact (seq_le_of_lonely hpos hls (by rw [cascadeSeq_zero]; exact hs1)
    (cascadeSeq_isMove ds (1 / (8 * m))) n).trans hs7

#print axioms no_crossing_of_small_dmin

/-! ## (6) The strong gate (OWED) -/

/-- **The strong gate** (record E340, "landing > 7 ⇔ reading 1 sets a move"): at the first state above `R = 7` of the
cascade from the bound, every runner in the way has its next opening at or before `R = 9`, so `d_min` sets the move
(to exactly `R = 9`).  `gate_crossing` proves the weak form (the next state is `≥ 9`); by
`late_blocker_forces_slow_lap_one` a counterexample needs the setter into the gate on lap 1 with reading below `17/15`.
Tested exactly, not proved (Task U scratch: integer crossers with `a₇ ≤ 70`, perturbed crossers, exhaustive families with
`ρ₂ < 17/15`; 0 counterexamples). -/
-- STANDING: OWED
def StrongGate : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k m, IsDmin v k m → ∀ n,
    cascadeSeq (disparitySet v k) (1 / (8 * m)) n ≤ 7 / (8 * m) →
    7 / (8 * m) < cascadeSeq (disparitySet v k) (1 / (8 * m)) (n + 1) →
    ∀ y ∈ disparitySet v k, InWay y (cascadeSeq (disparitySet v k) (1 / (8 * m)) (n + 1)) →
      nextOpening y (cascadeSeq (disparitySet v k) (1 / (8 * m)) (n + 1)) ≤ 9 / (8 * m)

end Types

end Fresh
