import Mathlib
import Fresh.Framework
import Fresh.NormalForm
import Fresh.QuotientReduction
import Fresh.DispCell
import Fresh.RealCase
import Fresh.LonelyCells
import Fresh.Doors

/-!
# The displaced landing of the cascade chain, as an integer part plus a deviation part (Task BD)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `NormalForm`, `QuotientReduction`, `DispCell`, `RealCase`,
`LonelyCells`, `Doors` (and through them `Cascade`, `ChainLaws`); nothing from the existing `LonelyRunner` repo (no file of it was read
for this task, no proof was copied).  Exact reals; no floats; no runner is stationary; no density, coverage, cap or move budget is the
shape of any statement.  Counting and covering steps: every window-against-spacing step is tagged `[PROVISIONAL: covering]` at the
step (`lap_unique`, `lap_first_opening`, `gridPart_one_slow`, `gridPart_prev_unique`); there is no counting tool.

Setting.  `m > 0` the base scale (`d_min` in the application), `ρ_s = s/m = idx_s + e_s` (`NormalForm.idx`, `NormalForm.edev`), gate
coordinate `R = 8 m t`.  A cascade chain is `R_0 = 1 < R_1 < … < R_N = R*`; the reading `s` is blocked at `R` iff `|ρ_s R - 8 z| < 1`,
`z = round(ρ_s R/8)` (the LAP), and the move goes to the opening `R' ρ_s = 8 z + 1` of the setter.

## Contents (grades: [L] Lean, see the `#print axioms` lines; [OBS] data in `experiments/n8/displaced_landing_v1.out`; [reasoned] not formalised)

(1) The chain.  `landing_step`, `setter_opening`: a step lands on the opening of its setter on the lap `z = round(ρ R_n/8)`.
`final_landing`: the final `R* = 8 m seq N` is `IsLandingR` (the least lonely `R > 0`) and is either `1` or the opening, on lap `z`, of a
setter of an earlier forward move that was blocked at `R_n`.  `consecutive_difference`: `(R_{n+1} - R_n) ρ = 1 - δ`, `δ = ρ R_n - 8 z`.
`junction_split`: the next residue splits into an INTEGER grid part and a deviation part (`ρ δ' = Jg + Jd`).

(2) Grid part and deviation part.  `gridPart a ix z = 8 z + 1 - a ix`.  `displaced_identity`: `(R - a) ρ_s = Ngrid - a e_s` for every integer `a`
(the deviation part is `-a e_s`; `m ≠ 0` is not used).  `displaced_displacement`.  Values of `Ngrid`: `gridPart_emod` (`≡ 1 - a idx` mod 8),
`gridPart_bounds` (`a e < Ngrid < idx + (a+1) e` for `a < R < a+1`), `gridPart_sign`, `gridPart_pos_facts` (`2 Ngrid + a > 0`; `e ≥ 0 → Ngrid ≥ 1`;
at `a = 1`: `Ngrid ≥ 0`, `Ngrid = 0 → e < 0`), `gridPart_prev_window` (`ρ(R_n - a) + a e < Ngrid < ρ(R_n - a) + a e + 2`: the integer part is
set by the PREVIOUS landing), `gridPart_prev_unique`, `gridPart_first_step` (first step from the bound: `Ngrid ∈ {0,1,2}`),
`lap_unique`, `lap_first_opening` and `gridPart_one_slow` (a slow last mover, `ρ ≤ 8`: the landing is its first opening after `a`; at `a = 1`
`Ngrid = (1 - idx) mod 8`), `gridPart_one_laps` (any `ρ`, `a = 1`: `Ngrid = (1 - idx) mod 8 + 8 w`, `w ≥ 0` the extra laps),
`gridPart_quo_shift` and `reduced_reading_at_landing` (the quotient shift: integer lap `z - a quo` plus the REAL correction `-quo (R - a)`).

(3) THE DISPLACED LANDING of the cascade chain [L].  `displaced_landing` (hypotheses: positivity, `m ∈ ds`, the cascade fixed at `N`, `R*` not an
integer): `a = ⌊R*⌋ ≥ 1`, `S` not lonely at `a`, and a setter `s` blocked at `R_n` on lap `z` with `R* ρ_s = 8z+1`,
`(R* - a) ρ_s = Ngrid - a e_s`, `a e_s < Ngrid < idx_s + (a+1) e_s`, `Ngrid ≡ 1 - a idx_s` (mod 8).

(4) The last mover against the integer instant `a`.  `self_residue`, `self_clear_at_int_iff` (window `|e a| ≤ 1`): the last mover is clear at `a` iff
`(Ngrid ≡ 1 → 1 ≤ |e a|) ∧ (Ngrid ≡ 0 → 0 ≤ e) ∧ (Ngrid ≡ 2 → e ≤ 0)` (mod 8).  `gridPart_zero` (`Ngrid = 0`: `a idx ≡ 1`, `R - a = -a e/ρ`,
`R > a ↔ e < 0`), `gridPart_one` (`Ngrid = 1`: `8 ∣ a idx`, `R - a = (1 - a e)/ρ`; `odd_mul_emod_zero`: for odd `a` a residue-`0` reading).
`blocked_at_int_iff` (a reading blocked at `a`: `r = 0 ∧ |e a| < 1`, or `r = 1 ∧ e < 0`, or `r = 7 ∧ e > 0`, `r = (ridx a) mod 8`),
`blocked_at_one_iff` (at `a = 1`: `ridx = 8`, or `ridx = 1 ∧ e < 0`, or `ridx = 7 ∧ e > 0`).

(5) The family of a residue-`0` reading (generalises `QuotientReduction.landing_family`).  `R1 = 1 + (1 - e0)/ρ0`; `R1_opening`
(`Ngrid = 1`), `residue_zero_blocks` (the reading blocks all of `[1, R1)`), `landing_R1_iff_lonely` (`R1` is the landing iff `S` is lonely at `R1`;
no only-blocker hypothesis; `landing_opening_iff_lonely`: the same for ANY reading blocked at `R = 1`), `family_landing_iff` (iff every other reading satisfies `Win (ridx + x_d)`, `x_d = e_d + (ridx_d + e_d)(R1 - 1) +
8 {quo_d (R1 - 1)}`), `family_landing_classes` (class inequalities, window `|x_d| ≤ 1`), `first_move_residue_zero` (the first cascade move when
`d0` is the only blocker at `R = 1`), `six_family_threshold` (`(1,…,6,8+e)`: the landing is `R1` iff `e ≥ -2/7`).  Counterexamples:
`second_move_example` (`(1,2,3,4,5,7,8)`: landing `9/7`, not `9/8`; the residue-`7` reading `7` moves into its zone), `second_move_deviation_example`.

## Hypothesis tests (REQUIRED / NOT REQUIRED / UNDECIDED); each by trying to drop it
* `m ≠ 0` in `displaced_identity`, `m > 0` in `gridPart_zero`: NOT REQUIRED [L] (not used).
* `ρ = s/m > 0` for the sign relations (`gridPart_sign`, `gridPart_bounds`, `gridPart_pos_facts`): REQUIRED [L] (`sign_needs_positive_example`).
* The landing equation `R1 ρ = 8 z + 1` in `gridPart_prev_window`, `gridPart_prev_unique`, `gridPart_first_step`: NOT REQUIRED [L].
* `hnon` (R* not an integer) in `displaced_landing`: REQUIRED for `1 ≤ a < R*` (at `R* = 1` no such `a` exists); `gridPart_sign` gives `Ngrid = a e` when `R* = a`.
* `m ∈ ds` in `final_landing`: NOT REQUIRED for the opening statement; REQUIRED for `IsLandingR` [L] (`family_unit_required_example`).
* `ρ ≤ 8` in `lap_first_opening`: REQUIRED [L] (`lap_first_opening_needs_slow`); in `gridPart_one_slow`: REQUIRED [L] (`gridPart_one_slow_needs_slow`).
  Whether the CASCADE lands on a later opening of a fast last mover is data: it does [OBS].
* The window `|e a| ≤ 1` in `self_clear_at_int_iff`, `blocked_at_int_iff`: REQUIRED [L] (`self_window_required_example`).
* The window `|x_d| ≤ 1` in `family_landing_classes`: REQUIRED [L] (`family_window_required_example`).
* The only-blocker hypothesis: NOT REQUIRED for `landing_R1_iff_lonely` and `family_landing_iff` [L]; REQUIRED for `first_move_residue_zero` [L]
  (`first_move_needs_only_blocker`).
* `idx ≡ 0 (mod 8)` of `d0`: NOT REQUIRED for the iff `landing = opening of d0 ↔ lonely there` [L] (`landing_opening_iff_lonely`: any reading blocked at
  `R = 1`, opening `ropen`); it fixes only the FORM `R1 = 1 + (1 - e0)/ρ0` (`ropen_eq_R1`; other classes have offsets `-e/ρ`, `(2-e)/ρ`, `NormalForm.isMove_one_classes`).
* Positivity of every disparity in the cascade: REQUIRED (a zero disparity is in the way at every instant, `DispCell.isClearFirst_zero_false`).

## What is NOT explained here
That the chain ends (the cascade reaches a fixed point) is the conjecture itself (`Doors.doors_agree`, `Cascade.cascadeForm_iff`) and is neither used nor derived here;
which reading is the last mover and what `R_{N-1}` is are not derived from `(a, idx, e)`: `gridPart_prev_window` fixes `Ngrid` once `R_{N-1}` is given.

Provenance.  `RealCase.isMove_gate` / `nextOpening_gate` (this repo) are used for the chain; `NormalForm.win_class`, `clear_at_unit`,
`QuotientReduction.mul_emod_ridx`, `lonelyR_ge_one`, `win_orig_iff_fract`, `dRed_div` for the integer instants and the family;
`QuotientReduction.opening_displacement` is the case `a idx = 8 w + 1` of `displaced_identity`; `landing_family` is the instance
`(1,…,6,8k)` of `family_landing_iff` [reasoned; its 100 cases k = 1..100 are checked in the data, [OBS]].  The junction split is MECHANISM_MAP E208 (stated there as algebra).
-/

open Classical

namespace Fresh.DisplacedLanding

open Fresh Fresh.NormalForm Fresh.QuotientReduction

/-! ## (1) The chain of landings: every landing is an opening of its setter -/

/-- **One cascade step in the gate coordinate** [L].  `R0 = 8 m t`, `R1 = 8 m t'`.  Either every reading is clear and the step
is the identity, or there is a setter `s` blocked at `R0` on lap `z = round (ρ_s R0 / 8)` and the new instant is the opening
of `s` on that lap: `R1 ρ_s = 8 z + 1`, strictly after `R0`, with every other blocked reading's opening no later. -/
theorem landing_step {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m t t' : ℝ} (hm : 0 < m) (hmv : IsMove ds t t') :
    ((∀ d ∈ ds, 1 ≤ |RealCase.dev m (8 * m * t) d|) ∧ t' = t) ∨
    (∃ s ∈ ds, ∃ z : ℤ, z = round (s / m * (8 * m * t) / 8) ∧ |s / m * (8 * m * t) - 8 * (z : ℝ)| < 1 ∧
      (8 * m * t') * (s / m) = 8 * (z : ℝ) + 1 ∧ 8 * m * t < 8 * m * t' ∧
      ∀ e' ∈ ds, |RealCase.dev m (8 * m * t) e'| < 1 →
        (1 - RealCase.dev m (8 * m * t) e') / (e' / m) ≤ (1 - RealCase.dev m (8 * m * t) s) / (s / m)) := by
  have e0 : (8 * m * t) / (8 * m) = t := by field_simp
  have hmv' : IsMove ds ((8 * m * t) / (8 * m)) t' := by rw [e0]; exact hmv
  rcases RealCase.isMove_gate hpos hm hmv' with ⟨hall, ht⟩ | ⟨s, hs, hb, ht, hmax⟩
  · left; exact ⟨hall, by rw [ht, e0]⟩
  · right
    have hsm : 0 < s / m := div_pos (hpos s hs) hm
    refine ⟨s, hs, round (s / m * (8 * m * t) / 8), rfl, ?_, ?_, ?_, hmax⟩
    · have : RealCase.dev m (8 * m * t) s = s / m * (8 * m * t) - 8 * (round (s / m * (8 * m * t) / 8) : ℝ) := rfl
      rw [← this]; exact hb
    · have hd : RealCase.dev m (8 * m * t) s = s / m * (8 * m * t) - 8 * (round (s / m * (8 * m * t) / 8) : ℝ) := rfl
      rw [ht, add_mul, div_mul_cancel₀ _ hsm.ne', hd]
      ring
    · rw [ht]
      have := RealCase.eps_pos hsm hb
      linarith

#print axioms landing_step

/-- **A setter's move, in the gate coordinate** [L].  If `s` is in the way at `t` and `t' = nextOpening s t`, then with
`R0 = 8 m t`, `R1 = 8 m t'` and the lap `z = round (ρ_s R0 / 8)`: the signed residue is `< 1` in absolute value, the new
instant is the opening of `s` on lap `z` (`R1 ρ_s = 8 z + 1`) and it is strictly later. -/
theorem setter_opening {m s t t' : ℝ} (hm : 0 < m) (hs : 0 < s) (hw : InWay s t) (ht : t' = nextOpening s t) :
    ∃ z : ℤ, z = round (s / m * (8 * m * t) / 8) ∧ |s / m * (8 * m * t) - 8 * (z : ℝ)| < 1 ∧
      (8 * m * t') * (s / m) = 8 * (z : ℝ) + 1 ∧ 8 * m * t < 8 * m * t' := by
  have e0 : (8 * m * t) / (8 * m) = t := by field_simp
  have hw' : InWay s ((8 * m * t) / (8 * m)) := by rw [e0]; exact hw
  have hb := (RealCase.inWay_gate_iff hm).mp hw'
  have hg := RealCase.nextOpening_gate hm hs hw'
  rw [e0] at hg
  have hsm : 0 < s / m := div_pos hs hm
  have hd : RealCase.dev m (8 * m * t) s = s / m * (8 * m * t) - 8 * (round (s / m * (8 * m * t) / 8) : ℝ) := rfl
  refine ⟨round (s / m * (8 * m * t) / 8), rfl, ?_, ?_, ?_⟩
  · rw [← hd]; exact hb
  · rw [ht, hg, add_mul, div_mul_cancel₀ _ hsm.ne', hd]
    ring
  · rw [ht, hg]
    have := RealCase.eps_pos hsm hb
    linarith

#print axioms setter_opening

/-- **The final landing of a chain** [L].  `ds` positive, `m ∈ ds`, `seq` a cascade sequence from the bound `1/(8m)`, fixed at
step `N`.  Then `R* = 8 m seq N` is the landing of `ds` at base `m` (`IsLandingR`: the least lonely `R > 0`), and either
`R* = 1` (no forward move) or the landing is the opening, on lap `z`, of a SETTER `s` of an earlier forward move `n < N`
that was blocked at `R_n = 8 m seq n`, with `R_n < R*`. -/
theorem final_landing {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) {seq : ℕ → ℝ}
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {N : ℕ} (hN : seq (N + 1) = seq N) :
    IsLandingR m ds (8 * m * seq N) ∧
    (8 * m * seq N = 1 ∨
      ∃ n < N, ∃ s ∈ ds, ∃ z : ℤ, z = round (s / m * (8 * m * seq n) / 8) ∧
        |s / m * (8 * m * seq n) - 8 * (z : ℝ)| < 1 ∧ (8 * m * seq N) * (s / m) = 8 * (z : ℝ) + 1 ∧
        8 * m * seq n < 8 * m * seq N) := by
  have hm0 : 0 < m := hpos m hm
  obtain ⟨hlon, hleast⟩ := Cascade.fixed_is_first_isolation hpos hm h0 hmv hN
  have hseq0 : 0 < seq 0 := by rw [h0]; positivity
  have hseqN : 0 < seq N := lt_of_lt_of_le hseq0 (Cascade.start_le_seq hpos hmv N)
  have e1 : 8 * m * seq N / (8 * m) = seq N := by field_simp
  refine ⟨⟨⟨by positivity, ?_⟩, ?_⟩, ?_⟩
  · unfold LonelyR; rw [e1]; exact hlon
  · rintro x ⟨hx, hxl⟩
    unfold LonelyR at hxl
    have := hleast (x / (8 * m)) (by positivity) hxl
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · rcases Doors.last_forward hmv N with h | ⟨n, hn, x, hx, hxe⟩
    · left; rw [h, h0]; field_simp
    · right
      obtain ⟨hxds, hxw, hxs⟩ := hx
      obtain ⟨z, hz, hb, hop, hlt⟩ := setter_opening hm0 (hpos x hxds) hxw hxs
      refine ⟨n, hn, x, hxds, z, hz, hb, ?_, ?_⟩
      · rw [← hxe]; exact hop
      · rw [← hxe]; exact hlt

#print axioms final_landing

/-! ## (2) Grid part and deviation part of a landing -/

/-- The GRID PART of an opening against the integer instant `a`: the opening `R ρ = 8 z + 1` of a reading of grid index `ix`
(lap `z`), minus the grid instant's `a · ix`.  An integer. -/
def gridPart (a ix z : ℤ) : ℤ := 8 * z + 1 - a * ix

/-- **The exact identity** [L].  If `R ρ = 8 z + 1` with `ρ = s/m`, then for every integer `a`
`(R - a) ρ = Ngrid(a, idx_s, z) - a e_s`: the displacement of the opening from the integer instant `a`, scaled by `ρ`, is an
INTEGER (the grid part) plus the DEVIATION PART `-a e_s`.  No hypothesis on `R`, `s`, `m` beyond the displayed equation
(`m ≠ 0` is not even used: `ρ = idx + e` is the definition of `e`). -/
theorem displaced_identity (m s R : ℝ) (a z : ℤ) (hz : R * (s / m) = 8 * (z : ℝ) + 1) :
    (R - a) * (s / m) = (gridPart a (idx m s) z : ℝ) - (a : ℝ) * edev m s := by
  have h : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  unfold gridPart
  push_cast
  rw [h] at hz ⊢
  linear_combination hz

#print axioms displaced_identity

/-- The displacement itself [L]: `R - a = (Ngrid - a e)/ρ`. -/
theorem displaced_displacement (m s R : ℝ) (a z : ℤ) (hsm : 0 < s / m) (hz : R * (s / m) = 8 * (z : ℝ) + 1) :
    R - a = ((gridPart a (idx m s) z : ℝ) - (a : ℝ) * edev m s) / (s / m) := by
  rw [eq_div_iff hsm.ne']
  exact displaced_identity m s R a z hz

#print axioms displaced_displacement

/-- **The difference of two consecutive landings** [L].  Setter `s` at `R0` on lap `z`, landing `R1`: `(R1 - R0) ρ_s = 1 - δ`,
`δ = ρ_s R0 - 8 z`.  This is the identity `displaced_identity` with `a` replaced by the real `R0` (the grid part is then
`8 z + 1 - ρ R0` and is the real `1 - δ`). -/
theorem consecutive_difference (R0 R1 ρ δ : ℝ) (z : ℤ) (hδ : δ = ρ * R0 - 8 * (z : ℝ)) (h1 : R1 * ρ = 8 * (z : ℝ) + 1) :
    (R1 - R0) * ρ = 1 - δ := by
  rw [hδ]; linear_combination h1

#print axioms consecutive_difference

/-- **The junction splits into a grid part and a deviation part** [L] (MM E208).  Consecutive setters `s` (lap `z`) and `s'`
(lap `z'`), with `R1 ρ = 8 z + 1`: the residue of `s'` at the landing `R1` is
`δ' = ρ' R1 - 8 z'`, and `ρ δ' = Jg + Jd` where `Jg = idx'(8z+1) - 8 z' idx` is an INTEGER and
`Jd = e'(8z+1) - 8 z' e` is the deviation part. -/
theorem junction_split (m s s' R1 : ℝ) (z z' : ℤ) (hz : R1 * (s / m) = 8 * (z : ℝ) + 1) :
    (s / m) * ((s' / m) * R1 - 8 * (z' : ℝ)) =
      ((idx m s' * (8 * z + 1) - 8 * z' * idx m s : ℤ) : ℝ) + (edev m s' * (8 * (z : ℝ) + 1) - 8 * (z' : ℝ) * edev m s) := by
  have h : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  have h' : s' / m = (idx m s' : ℝ) + edev m s' := by unfold edev; ring
  push_cast
  have : (s / m) * ((s' / m) * R1 - 8 * (z' : ℝ)) = (s' / m) * (R1 * (s / m)) - 8 * (z' : ℝ) * (s / m) := by ring
  rw [this, hz, h, h']; ring

#print axioms junction_split

/-! ### Which values the grid part can take -/

/-- **The class of the grid part mod 8** [L]: `Ngrid + a · idx = 8 z + 1`, so `Ngrid ≡ 1 - a · idx (mod 8)`.  It is fixed by
`(a, idx_s)`; the multiple of 8 that is added is the lap. -/
theorem gridPart_emod (a ix z : ℤ) : gridPart a ix z % 8 = (1 - a * ix) % 8 := by
  unfold gridPart; omega

#print axioms gridPart_emod

/-- **The grid part lies strictly between `a e` and `idx + (a+1) e` when `a < R < a + 1`** [L] (`ρ > 0`). -/
theorem gridPart_bounds (m s R : ℝ) (a z : ℤ) (hsm : 0 < s / m) (hz : R * (s / m) = 8 * (z : ℝ) + 1)
    (h1 : (a : ℝ) < R) (h2 : R < (a : ℝ) + 1) :
    (a : ℝ) * edev m s < (gridPart a (idx m s) z : ℝ) ∧
      (gridPart a (idx m s) z : ℝ) < (idx m s : ℝ) + ((a : ℝ) + 1) * edev m s := by
  have hid := displaced_identity m s R a z hz
  have hρ : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  constructor
  · have : 0 < (R - a) * (s / m) := mul_pos (by linarith) hsm
    linarith
  · have : (R - a) * (s / m) < 1 * (s / m) := mul_lt_mul_of_pos_right (by linarith) hsm
    linarith

#print axioms gridPart_bounds

/-- **Sign relations** [L].  For `R > a` the grid part exceeds `a e`; for `R < a` it is below `a e`; for `R = a` it equals
`a e` (so `a e` is then an integer). -/
theorem gridPart_sign (m s R : ℝ) (a z : ℤ) (hsm : 0 < s / m) (hz : R * (s / m) = 8 * (z : ℝ) + 1) :
    ((a : ℝ) < R ↔ (a : ℝ) * edev m s < (gridPart a (idx m s) z : ℝ)) ∧
    (R < (a : ℝ) ↔ (gridPart a (idx m s) z : ℝ) < (a : ℝ) * edev m s) ∧
    (R = (a : ℝ) ↔ (gridPart a (idx m s) z : ℝ) = (a : ℝ) * edev m s) := by
  have hid := displaced_identity m s R a z hz
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : 0 < (R - a) * (s / m) := mul_pos (by linarith) hsm
    linarith
  · by_contra hc; push Not at hc
    have : (R - a) * (s / m) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hsm.le
    linarith
  · have : (R - a) * (s / m) < 0 := mul_neg_of_neg_of_pos (by linarith) hsm
    linarith
  · by_contra hc; push Not at hc
    have : 0 ≤ (R - a) * (s / m) := mul_nonneg (by linarith) hsm.le
    linarith
  · have : (R - a) * (s / m) = 0 := by rw [h]; ring
    linarith
  · have h0 : (R - a) * (s / m) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h hsm.ne'

#print axioms gridPart_sign

/-- **Consequences for `R > a`, `a ≥ 1`** [L]: `2 Ngrid + a > 0` (since `e ≥ -1/2`); `e ≥ 0` gives `Ngrid ≥ 1`;
at `a = 1`: `Ngrid ≥ 0`, and `Ngrid = 0` forces `e < 0`. -/
theorem gridPart_pos_facts (m s R : ℝ) (a z : ℤ) (hsm : 0 < s / m) (hz : R * (s / m) = 8 * (z : ℝ) + 1)
    (ha : 1 ≤ a) (hR : (a : ℝ) < R) :
    0 < 2 * gridPart a (idx m s) z + a ∧ (0 ≤ edev m s → 1 ≤ gridPart a (idx m s) z) ∧
    (a = 1 → 0 ≤ gridPart a (idx m s) z) ∧ (a = 1 → gridPart a (idx m s) z = 0 → edev m s < 0) := by
  have hN := ((gridPart_sign m s R a z hsm hz).1).mp hR
  have he := edev_ge m s
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  refine ⟨?_, fun h0 => ?_, fun h1 => ?_, fun h1 h0 => ?_⟩
  · have : (0 : ℝ) < 2 * (gridPart a (idx m s) z : ℝ) + a := by nlinarith
    exact_mod_cast this
  · have : (0 : ℝ) < (gridPart a (idx m s) z : ℝ) := by nlinarith
    have : 0 < gridPart a (idx m s) z := by exact_mod_cast this
    omega
  · subst h1
    by_contra hc; push Not at hc
    have : gridPart 1 (idx m s) z ≤ -1 := by omega
    have : (gridPart 1 (idx m s) z : ℝ) ≤ -1 := by exact_mod_cast this
    push_cast at hN
    linarith
  · subst h1
    rw [h0] at hN
    push_cast at hN
    linarith

#print axioms gridPart_pos_facts

/-! ### The lap, when the last mover is slow (`ρ ≤ 8`) -/

/-- **Two openings of one reading in the same unit window have the same lap when `ρ ≤ 8`** [L]: the openings of a reading
are spaced `8/ρ ≥ 1` apart, so an open window `(a, a+1)` holds at most one.  [PROVISIONAL: covering] (window length against opening
spacing; supports: the lap of a slow last mover is determined). -/
theorem lap_unique (ρ R R' : ℝ) (z z' : ℤ) (a : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 8)
    (hz : R * ρ = 8 * (z : ℝ) + 1) (hz' : R' * ρ = 8 * (z' : ℝ) + 1)
    (h1 : a < R) (h2 : R < a + 1) (h1' : a < R') (h2' : R' < a + 1) : z = z' := by
  have e : 8 * ((z : ℝ) - z') = (R - R') * ρ := by linear_combination hz' - hz
  have hlt : (R - R') * ρ < 1 * ρ := mul_lt_mul_of_pos_right (by linarith) hρ
  have hgt : (-1) * ρ < (R - R') * ρ := mul_lt_mul_of_pos_right (by linarith) hρ
  have c1 : (z : ℝ) - z' < 1 := by linarith
  have c2 : -1 < (z : ℝ) - z' := by linarith
  have d1 : z - z' < 1 := by exact_mod_cast c1
  have d2 : -1 < z - z' := by exact_mod_cast c2
  omega

#print axioms lap_unique

/-- **The landing is the FIRST opening of the last mover after `a`, when `ρ ≤ 8`** [L]: the lap is
`z = ⌊(a ρ - 1)/8⌋ + 1`, the least lap whose opening exceeds `a`, hence
`Ngrid = 8 (⌊(a ρ - 1)/8⌋ + 1) + 1 - a · idx`.  [PROVISIONAL: covering] (window length 1 against opening spacing `8/ρ ≥ 1`;
supports: the integer part of a slow last mover is fixed by `(a, idx, e)`). -/
theorem lap_first_opening (ρ R : ℝ) (z a : ℤ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 8) (hz : R * ρ = 8 * (z : ℝ) + 1)
    (h1 : (a : ℝ) < R) (h2 : R < (a : ℝ) + 1) : z = ⌊((a : ℝ) * ρ - 1) / 8⌋ + 1 := by
  have c1 : (a : ℝ) * ρ < 8 * (z : ℝ) + 1 := by rw [← hz]; exact mul_lt_mul_of_pos_right h1 hρ
  have c2 : 8 * (z : ℝ) + 1 < ((a : ℝ) + 1) * ρ := by rw [← hz]; exact mul_lt_mul_of_pos_right h2 hρ
  have q1 : ((a : ℝ) * ρ - 1) / 8 < (z : ℝ) := by linarith
  have q2 : (z : ℝ) < ((a : ℝ) * ρ - 1) / 8 + 1 := by nlinarith
  have f1 := Int.floor_le (((a : ℝ) * ρ - 1) / 8)
  have f2 := Int.lt_floor_add_one (((a : ℝ) * ρ - 1) / 8)
  have g1 : ⌊((a : ℝ) * ρ - 1) / 8⌋ < z := by
    have : (⌊((a : ℝ) * ρ - 1) / 8⌋ : ℝ) < z := by linarith
    exact_mod_cast this
  have g2 : z < ⌊((a : ℝ) * ρ - 1) / 8⌋ + 2 := by
    have : (z : ℝ) < (⌊((a : ℝ) * ρ - 1) / 8⌋ : ℝ) + 2 := by linarith
    exact_mod_cast this
  omega

#print axioms lap_first_opening

/-- **At `a = 1`, for `ρ ≤ 8`, the grid part is the residue `(1 - idx) mod 8`** [L].  `1 < R < 2`, `R ρ = 8 z + 1`, `ρ = s/m ≤ 8`
give `Ngrid = (1 - idx_s) mod 8 ∈ {0,…,7}`, and `Ngrid = 0` (that is `idx ≡ 1`) forces `e < 0`.  So for a slow last mover the
integer part is determined by the residue of its grid index alone.  [PROVISIONAL: covering] (window `(e, idx + 2e)` against the
class mod 8; supports: the same claim). -/
theorem gridPart_one_slow (m s R : ℝ) (z : ℤ) (hsm : 0 < s / m) (hρ8 : s / m ≤ 8)
    (hz : R * (s / m) = 8 * (z : ℝ) + 1) (h1 : (1 : ℝ) < R) (h2 : R < 2) :
    gridPart 1 (idx m s) z = (1 - idx m s) % 8 ∧ (idx m s % 8 = 1 → edev m s < 0) := by
  have hb := gridPart_bounds m s R 1 z hsm hz (by exact_mod_cast h1) (by push_cast; linarith)
  have hρ : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  have he1 := edev_ge m s
  have he2 := edev_lt m s
  have hem := gridPart_emod 1 (idx m s) z
  push_cast at hb
  obtain ⟨hb1, hb2⟩ := hb
  set N := gridPart 1 (idx m s) z with hNdef
  set ix := idx m s with hix
  have hN0 : 0 ≤ N := by
    by_contra hc; push Not at hc
    have : (N : ℝ) ≤ -1 := by exact_mod_cast (show N ≤ -1 by omega)
    linarith
  have hN8 : N < 8 := by
    by_contra hc; push Not at hc
    have h8 : (8 : ℝ) ≤ N := by exact_mod_cast hc
    rcases le_or_gt (edev m s) 0 with he | he
    · have : ix ≤ 8 := by
        have : (ix : ℝ) < 9 := by linarith
        have : ix < 9 := by exact_mod_cast this
        omega
      have : (ix : ℝ) ≤ 8 := by exact_mod_cast this
      linarith
    · have : ix ≤ 7 := by
        have : (ix : ℝ) < 8 := by linarith
        have : ix < 8 := by exact_mod_cast this
        omega
      have : (ix : ℝ) ≤ 7 := by exact_mod_cast this
      linarith
  have hNe : N = (1 - ix) % 8 := by omega
  refine ⟨hNe, fun h => ?_⟩
  have : N = 0 := by omega
  rw [this] at hb1
  push_cast at hb1
  linarith

#print axioms gridPart_one_slow

/-! ### The quotient shift -/

/-- **The grid part against the reduced index** [L]: `Ngrid(a, idx, z) = Ngrid(a, ridx, z - a quo)`.  The integer part of the
original is the integer part of the quotient-reduced reading at the lap shifted by the INTEGER `a quo`. -/
theorem gridPart_quo_shift (m s : ℝ) (a z : ℤ) :
    gridPart a (idx m s) z = gridPart a (ridx m s) (z - a * quo m s) := by
  unfold gridPart
  rw [idx_split m s]
  ring

/-- **The reduced reading at the original landing** [L].  `R ρ = 8 z + 1` gives `R · (dRed/m) = 8 (z - a quo) + 1 - 8 quo (R - a)`:
an integer lap `z - a quo` plus a REAL correction `-quo (R - a)`, which vanishes exactly when `quo = 0` or `R = a`
(`opening_reduced`, with `q R = q a + q (R - a)`). -/
theorem reduced_reading_at_landing (m s R : ℝ) (a z : ℤ) (hm : m ≠ 0) (hz : R * (s / m) = 8 * (z : ℝ) + 1) :
    R * (dRed m s / m) = 8 * ((z : ℝ) - (a : ℝ) * (quo m s : ℝ)) + 1 - 8 * (quo m s : ℝ) * (R - a) := by
  have h := opening_reduced R (s / m) (dRed m s / m) (quo m s : ℝ) z (by
    unfold dRed; field_simp; ring) hz
  rw [h]; ring

#print axioms gridPart_quo_shift
#print axioms reduced_reading_at_landing

/-! ### The last mover against the integer instant `a`: classes `Ngrid = 0`, `Ngrid = 1`, larger -/

/-- **The residue of the last mover's own reading at `a` is `(1 - Ngrid) mod 8`** [L]. -/
theorem self_residue (m s : ℝ) (a z : ℤ) : (idx m s * a) % 8 = (1 - gridPart a (idx m s) z) % 8 := by
  unfold gridPart
  have : idx m s * a = a * idx m s := mul_comm _ _
  rw [this]
  omega

/-- **Is the last mover itself clear at the integer instant `a`?** [L].  `a > 0`, window `|e a| ≤ 1`.  Its reading at `a` is
`((1 - Ngrid) mod 8) + e a`, so it is clear iff `(Ngrid ≡ 1 → 1 ≤ |e a|) ∧ (Ngrid ≡ 0 → 0 ≤ e) ∧ (Ngrid ≡ 2 → e ≤ 0)` (mod 8).
In particular `Ngrid ≡ 3,…,7 (mod 8)` leaves it clear at `a`: it enters the way only after the cascade has moved. The window is
REQUIRED (`self_window_required_example`). -/
theorem self_clear_at_int_iff (m s : ℝ) (hm : 0 < m) (a z : ℤ) (ha : 0 < a) (hw : |edev m s * (a : ℝ)| ≤ 1) :
    (1 / 8 : ℝ) ≤ distInt (s * ((a : ℝ) / (8 * m))) ↔
      ((gridPart a (idx m s) z % 8 = 1 → 1 ≤ |edev m s * (a : ℝ)|) ∧
       (gridPart a (idx m s) z % 8 = 0 → 0 ≤ edev m s) ∧ (gridPart a (idx m s) z % 8 = 2 → edev m s ≤ 0)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [clear_at_unit hm a s, self_residue m s a z,
    win_class ((1 - gridPart a (idx m s) z) % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) _ hw]
  have s1 : 0 ≤ edev m s * (a : ℝ) ↔ 0 ≤ edev m s :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonneg h ha'.le⟩
  have s2 : edev m s * (a : ℝ) ≤ 0 ↔ edev m s ≤ 0 :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonpos_of_nonpos_of_nonneg h ha'.le⟩
  rw [s1, s2]
  have e0 : (1 - gridPart a (idx m s) z) % 8 = 0 ↔ gridPart a (idx m s) z % 8 = 1 := by omega
  have e1 : (1 - gridPart a (idx m s) z) % 8 = 1 ↔ gridPart a (idx m s) z % 8 = 0 := by omega
  have e7 : (1 - gridPart a (idx m s) z) % 8 = 7 ↔ gridPart a (idx m s) z % 8 = 2 := by omega
  rw [e0, e1, e7]

#print axioms self_residue
#print axioms self_clear_at_int_iff

/-- **`Ngrid = 0`: the pure deviation displacement** [L].  `Ngrid = 0` iff `8 z + 1 = a · idx`; then `a · idx ≡ 1 (mod 8)`,
`R - a = -a e/ρ`, `R > a` iff `e < 0` (`a > 0`), and, in the window, the last mover is itself BLOCKED at `a` exactly when
`e < 0`. -/
theorem gridPart_zero (m s R : ℝ) (a z : ℤ) (ha : 0 < a) (hsm : 0 < s / m)
    (hz : R * (s / m) = 8 * (z : ℝ) + 1) (h0 : gridPart a (idx m s) z = 0) :
    (a * idx m s) % 8 = 1 ∧ R - a = -((a : ℝ) * edev m s) / (s / m) ∧ ((a : ℝ) < R ↔ edev m s < 0) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hd := displaced_displacement m s R a z hsm hz
  have hs := (gridPart_sign m s R a z hsm hz).1
  rw [h0] at hd hs
  push_cast at hd hs
  refine ⟨?_, by rw [hd]; ring_nf, ?_⟩
  · unfold gridPart at h0; omega
  · rw [hs]
    constructor
    · intro h; by_contra hc; push Not at hc; nlinarith
    · intro h; nlinarith

/-- **`Ngrid = 1`: one lap beyond the grid instant** [L].  `Ngrid = 1` iff `8 z = a · idx`; then `8 ∣ a · idx` (for odd `a` this
is `idx ≡ 0 (mod 8)`, a residue-`0` reading), and `R - a = (1 - a e)/ρ`. -/
theorem gridPart_one (m s R : ℝ) (a z : ℤ) (hsm : 0 < s / m) (hz : R * (s / m) = 8 * (z : ℝ) + 1)
    (h1 : gridPart a (idx m s) z = 1) :
    (a * idx m s) % 8 = 0 ∧ R - a = (1 - (a : ℝ) * edev m s) / (s / m) := by
  have hd := displaced_displacement m s R a z hsm hz
  rw [h1] at hd
  push_cast at hd
  refine ⟨?_, hd⟩
  unfold gridPart at h1; omega

#print axioms gridPart_zero
#print axioms gridPart_one

/-- For odd `a`, `8 ∣ a · idx` iff `idx ≡ 0 (mod 8)` [L], i.e. `ridx = 8`. -/
theorem odd_mul_emod_zero (a ix : ℤ) (ha : a % 2 = 1) : (a * ix) % 8 = 0 ↔ ix % 8 = 0 := by
  constructor
  · intro h
    have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases this with h1 | h1 | h1 | h1 <;>
      · have := Int.emod_emod_of_dvd (a * ix) (show (8 : ℤ) ∣ 8 by norm_num)
        have h2 : (a * ix) % 8 = ((a % 8) * (ix % 8)) % 8 := Int.mul_emod _ _ _
        rw [h1] at h2
        have h3 : ix % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
        have h4 : 0 ≤ ix % 8 := Int.emod_nonneg _ (by norm_num)
        omega
  · intro h
    have h2 : (a * ix) % 8 = ((a % 8) * (ix % 8)) % 8 := Int.mul_emod _ _ _
    rw [h2, h]; simp

#print axioms odd_mul_emod_zero

/-! ### Which readings block at the integer instant `a` -/

/-- **A reading is blocked at the integer `a`: the classes** [L].  `a > 0`, window `|e a| ≤ 1`, `r = (ridx · a) mod 8`: blocked iff
`(r = 0 ∧ |e a| < 1) ∨ (r = 1 ∧ e < 0) ∨ (r = 7 ∧ e > 0)`.  (`NormalForm.win_class` with `QuotientReduction.mul_emod_ridx`.) -/
theorem blocked_at_int_iff (m d : ℝ) (hm : 0 < m) (a : ℤ) (ha : 0 < a) (hw : |edev m d * (a : ℝ)| ≤ 1) :
    ¬ ((1 / 8 : ℝ) ≤ distInt (d * ((a : ℝ) / (8 * m)))) ↔
      ((ridx m d * a % 8 = 0 ∧ |edev m d * (a : ℝ)| < 1) ∨ (ridx m d * a % 8 = 1 ∧ edev m d < 0) ∨
        (ridx m d * a % 8 = 7 ∧ 0 < edev m d)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [clear_at_unit hm a d, mul_emod_ridx,
    win_class (ridx m d * a % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) _ hw]
  have s1 : 0 ≤ edev m d * (a : ℝ) ↔ 0 ≤ edev m d :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonneg h ha'.le⟩
  have s2 : edev m d * (a : ℝ) ≤ 0 ↔ edev m d ≤ 0 :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonpos_of_nonpos_of_nonneg h ha'.le⟩
  rw [s1, s2]
  constructor
  · intro h
    by_cases h0 : ridx m d * a % 8 = 0
    · left; exact ⟨h0, by by_contra hc; exact h ⟨fun _ => not_lt.mp hc, fun h1 => by omega, fun h7 => by omega⟩⟩
    by_cases h1 : ridx m d * a % 8 = 1
    · right; left; exact ⟨h1, by by_contra hc; push Not at hc; exact h ⟨fun h0' => absurd h0' h0, fun _ => hc, fun h7 => by omega⟩⟩
    by_cases h7 : ridx m d * a % 8 = 7
    · right; right; exact ⟨h7, by by_contra hc; push Not at hc; exact h ⟨fun h0' => absurd h0' h0, fun h1' => absurd h1' h1, fun _ => hc⟩⟩
    exact absurd ⟨fun h0' => absurd h0' h0, fun h1' => absurd h1' h1, fun h7' => absurd h7' h7⟩ h
  · rintro (⟨h0, hb⟩ | ⟨h1, he⟩ | ⟨h7, he⟩) ⟨c0, c1, c7⟩
    · linarith [c0 h0]
    · linarith [c1 h1]
    · linarith [c7 h7]

#print axioms blocked_at_int_iff

/-- **At `a = 1`** [L]: reading `d` is blocked iff `ridx = 8`, or `ridx = 1` with `e < 0`, or `ridx = 7` with `e > 0`.  The window
holds automatically (`|e| ≤ 1/2`). -/
theorem blocked_at_one_iff (m d : ℝ) (hm : 0 < m) :
    ¬ ((1 / 8 : ℝ) ≤ distInt (d * ((1 : ℤ) / (8 * m) : ℝ))) ↔
      (ridx m d = 8 ∨ (ridx m d = 1 ∧ edev m d < 0) ∨ (ridx m d = 7 ∧ 0 < edev m d)) := by
  have hw : |edev m d * ((1 : ℤ) : ℝ)| ≤ 1 := by
    have := abs_edev_le m d; simp only [Int.cast_one, mul_one]; linarith
  have h := blocked_at_int_iff m d hm 1 one_pos hw
  have hb : |edev m d * ((1 : ℤ) : ℝ)| < 1 := by
    have := abs_edev_le m d; simp only [Int.cast_one, mul_one]; linarith
  have g1 := ridx_ge m d
  have g2 := ridx_le m d
  rw [h]
  constructor
  · rintro (⟨h0, -⟩ | ⟨h1, he⟩ | ⟨h7, he⟩)
    · left; omega
    · right; left; exact ⟨by omega, he⟩
    · right; right; exact ⟨by omega, he⟩
  · rintro (h8 | ⟨h1, he⟩ | ⟨h7, he⟩)
    · left; exact ⟨by omega, hb⟩
    · right; left; exact ⟨by omega, he⟩
    · right; right; exact ⟨by omega, he⟩

#print axioms blocked_at_one_iff

/-! ### The displaced landing of a chain -/

/-- **THE DISPLACED LANDING of the cascade chain** [L].  `ds` positive, `m ∈ ds`, `seq` the cascade from the bound fixed at
step `N`, and the landing `R* = 8 m seq N` NOT an integer (the displaced regime: no integer instant is the landing).  Then with
`a = ⌊R*⌋ ≥ 1` (so `a < R* < a + 1`, and `S` is not lonely at `a`) there is a setter `s` of an earlier forward move
`n < N`, blocked at `R_n`, on lap `z`, with
* `R* ρ_s = 8 z + 1` (the landing is an opening of the last mover),
* `(R* - a) ρ_s = Ngrid - a e_s`, `Ngrid = gridPart a idx_s z = 8 z + 1 - a idx_s` an integer,
* `a e_s < Ngrid < idx_s + (a+1) e_s` and `Ngrid ≡ 1 - a idx_s (mod 8)`.
Hypotheses: `hnon` is the only one beyond the cascade's own.  It is not used for the identity (`displaced_identity` holds for
every integer `a`), only to place `a` strictly below `R*`; if `R* = a` is an integer, `gridPart_sign` gives `Ngrid = a e`. -/
theorem displaced_landing {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) {seq : ℕ → ℝ}
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {N : ℕ} (hN : seq (N + 1) = seq N)
    (hnon : ∀ a : ℤ, 8 * m * seq N ≠ (a : ℝ)) :
    ∃ a : ℤ, 1 ≤ a ∧ (a : ℝ) < 8 * m * seq N ∧ 8 * m * seq N < (a : ℝ) + 1 ∧ ¬ LonelyR m ds (a : ℝ) ∧
      ∃ n < N, ∃ s ∈ ds, ∃ z : ℤ,
        z = round (s / m * (8 * m * seq n) / 8) ∧ |s / m * (8 * m * seq n) - 8 * (z : ℝ)| < 1 ∧
        (8 * m * seq N) * (s / m) = 8 * (z : ℝ) + 1 ∧
        (8 * m * seq N - a) * (s / m) = (gridPart a (idx m s) z : ℝ) - (a : ℝ) * edev m s ∧
        (a : ℝ) * edev m s < (gridPart a (idx m s) z : ℝ) ∧
        (gridPart a (idx m s) z : ℝ) < (idx m s : ℝ) + ((a : ℝ) + 1) * edev m s ∧
        gridPart a (idx m s) z % 8 = (1 - a * idx m s) % 8 := by
  have hm0 : 0 < m := hpos m hm
  obtain ⟨hland, hcase⟩ := final_landing hpos hm h0 hmv hN
  have hR0 : 0 < 8 * m * seq N := hland.1.1
  have hge : 1 ≤ 8 * m * seq N := lonelyR_ge_one hm0 hm hR0 hland.1.2
  set R := 8 * m * seq N with hR
  have hfl : (⌊R⌋ : ℝ) ≤ R := Int.floor_le R
  have hlt : (⌊R⌋ : ℝ) < R := lt_of_le_of_ne hfl (fun h => hnon ⌊R⌋ h.symm)
  have hfl2 : R < (⌊R⌋ : ℝ) + 1 := Int.lt_floor_add_one R
  have ha1 : 1 ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using hge)
  refine ⟨⌊R⌋, ha1, hlt, hfl2, fun hl => ?_, ?_⟩
  · have := hland.2 ⟨by exact_mod_cast (show 0 < ⌊R⌋ by omega), hl⟩
    linarith
  · rcases hcase with h1 | ⟨n, hn, s, hs, z, hz, hb, hop, hlt'⟩
    · exact absurd h1 (hnon 1 ∘ fun h => by simpa using h)
    · have hsm : 0 < s / m := div_pos (hpos s hs) hm0
      have hbd := gridPart_bounds m s R ⌊R⌋ z hsm hop hlt hfl2
      refine ⟨n, hn, s, hs, z, hz, hb, hop, displaced_identity m s R ⌊R⌋ z hop, hbd.1, hbd.2, gridPart_emod _ _ _⟩

#print axioms displaced_landing

/-! ## (3) The first move of a residue-`0` reading, and when it is the landing -/

/-- The first move of a residue-`0` reading `d0`: `R1 = 1 + (1 - e0)/ρ0`.  Here `a = 1`, `Ngrid = 1`, deviation part `-e0`. -/
noncomputable def R1 (m d0 : ℝ) : ℝ := 1 + (1 - edev m d0) / (d0 / m)

theorem R1_gt_one (m d0 : ℝ) (hm : 0 < m) (hd0 : 0 < d0) : 1 < R1 m d0 := by
  unfold R1
  have : 0 < (1 - edev m d0) / (d0 / m) := div_pos (by linarith [edev_lt m d0]) (div_pos hd0 hm)
  linarith

/-- `R1 ρ0 = 8k + 1` for `idx = 8 k` (the first move is the opening of `d0` on lap `k`, i.e. `Ngrid = 1`) [L]. -/
theorem R1_opening (m d0 : ℝ) (hm : 0 < m) (hd0 : 0 < d0) (k : ℤ) (hk : idx m d0 = 8 * k) :
    R1 m d0 * (d0 / m) = 8 * (k : ℝ) + 1 := by
  have hρ : d0 / m = (idx m d0 : ℝ) + edev m d0 := by unfold edev; ring
  have hρ0 : d0 / m ≠ 0 := (div_pos hd0 hm).ne'
  have hk' : (idx m d0 : ℝ) = 8 * (k : ℝ) := by exact_mod_cast hk
  unfold R1
  rw [add_mul, div_mul_cancel₀ _ hρ0, hρ, hk']
  ring

/-- **A residue-`0` reading blocks every `R ∈ [1, R1)`** [L]: `ρ0 R = 8k + y`, `y ∈ [e0, 1)`, `|y| < 1`.  Hypotheses: `m, d0 > 0`,
`idx_{d0} ≡ 0 (mod 8)`. -/
theorem residue_zero_blocks (m d0 R : ℝ) (hm : 0 < m) (hd0 : 0 < d0) (h8 : idx m d0 % 8 = 0)
    (hR1 : 1 ≤ R) (hR2 : R < R1 m d0) : ¬ ((1 / 8 : ℝ) ≤ distInt (d0 * (R / (8 * m)))) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, idx m d0 = 8 * k := ⟨idx m d0 / 8, by omega⟩
  have hρ : d0 / m = (idx m d0 : ℝ) + edev m d0 := by unfold edev; ring
  have hρpos : 0 < d0 / m := div_pos hd0 hm
  have hk' : (idx m d0 : ℝ) = 8 * (k : ℝ) := by exact_mod_cast hk
  have hop := R1_opening m d0 hm hd0 k hk
  have he1 := edev_ge m d0
  have he2 := edev_lt m d0
  rw [clear_iff_win m d0 R hm.ne']
  have hy1 : -1 / 2 ≤ d0 / m * R - 8 * (k : ℝ) := by
    have : d0 / m * 1 ≤ d0 / m * R := mul_le_mul_of_nonneg_left hR1 hρpos.le
    linarith
  have hy2 : d0 / m * R - 8 * (k : ℝ) < 1 := by
    have : d0 / m * R < d0 / m * R1 m d0 := mul_lt_mul_of_pos_left hR2 hρpos
    linarith
  have e : d0 / m * R = (d0 / m * R - 8 * (k : ℝ)) + 8 * (k : ℝ) := by ring
  rw [e, win_shift]
  intro h
  have hc := win_class 0 (le_refl _) (by norm_num) (d0 / m * R - 8 * (k : ℝ)) (by rw [abs_le]; constructor <;> linarith)
  simp only [Int.cast_zero, zero_add] at hc
  have := (hc.mp h).1 trivial
  have h2 : |d0 / m * R - 8 * (k : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith
  linarith

#print axioms R1_gt_one
#print axioms R1_opening
#print axioms residue_zero_blocks

/-- **The landing is `R1` iff the set is lonely at `R1`** [L].  `m ∈ S` (the unit), `d0 ∈ S` of residue `0`.  NO hypothesis that
`d0` is the only blocker at `R = 1` (NOT REQUIRED): lonely at `R1` forces `d0` to be the maximal opener automatically.
`m ∈ S` is REQUIRED (`family_unit_required_example`). -/
theorem landing_R1_iff_lonely (m : ℝ) (S : Finset ℝ) (hm : 0 < m) (hmS : m ∈ S) (d0 : ℝ) (hd0S : d0 ∈ S) (hd0 : 0 < d0)
    (h8 : idx m d0 % 8 = 0) : IsLandingR m S (R1 m d0) ↔ LonelyR m S (R1 m d0) := by
  constructor
  · intro h; exact h.1.2
  · intro hl
    refine ⟨⟨by linarith [R1_gt_one m d0 hm hd0], hl⟩, ?_⟩
    rintro x ⟨hx, hxl⟩
    have h1 : 1 ≤ x := lonelyR_ge_one hm hmS hx hxl
    by_contra hc
    push Not at hc
    exact residue_zero_blocks m d0 x hm hd0 h8 h1 hc (hxl d0 hd0S)

#print axioms landing_R1_iff_lonely

/-! ### Any reading blocked at `R = 1`: the same iff -/

/-- The opening of a reading blocked at `R = 1`: `1 + (1 - δ)/ρ`, `δ = dev m 1 d0` (for a residue-`0` reading `δ = e0` and this is `R1`). -/
noncomputable def ropen (m d0 : ℝ) : ℝ := 1 + (1 - RealCase.dev m 1 d0) / (d0 / m)

theorem ropen_eq_R1 (m d0 : ℝ) (h8 : idx m d0 % 8 = 0) : ropen m d0 = R1 m d0 := by
  unfold ropen R1; rw [dev_one_r0 m d0 h8]

/-- **A reading blocked at `R = 1` blocks all of `[1, ropen)`** [L].  `m, d0 > 0`, `|dev m 1 d0| < 1`.  Residue `0` is NOT required
(`residue_zero_blocks` is the case `δ = e0`). -/
theorem blocks_until_opening (m d0 R : ℝ) (hm : 0 < m) (hd0 : 0 < d0) (hb : |RealCase.dev m 1 d0| < 1)
    (hR1 : 1 ≤ R) (hR2 : R < ropen m d0) : ¬ ((1 / 8 : ℝ) ≤ distInt (d0 * (R / (8 * m)))) := by
  have hρ : 0 < d0 / m := div_pos hd0 hm
  have hz : d0 / m * 1 = 8 * (round (d0 / m * 1 / 8) : ℝ) + RealCase.dev m 1 d0 := by
    unfold RealCase.dev RealCase.sres8; ring
  have hsh : R = 1 + (R - 1) := by ring
  rw [RealCase.gate_reading hm, hsh]
  have hcl := RealCase.clear_shift_iff (d0 / m) 1 (R - 1) (RealCase.dev m 1 d0) (round (d0 / m * 1 / 8)) hz
  rw [hcl]
  have hbl := RealCase.blocked_until_opening (ε := R - 1) hρ hb (by linarith) (by unfold ropen at hR2; linarith)
  intro h
  have h' : Win (RealCase.dev m 1 d0 + d0 / m * (R - 1)) := h
  have hc := win_class 0 (le_refl _) (by norm_num) (RealCase.dev m 1 d0 + d0 / m * (R - 1)) hbl.le
  simp only [Int.cast_zero, zero_add] at hc
  have := (hc.mp h').1 trivial
  linarith

/-- **For any reading blocked at `R = 1`: its opening is the landing iff `S` is lonely there** [L].  `m ∈ S`, `d0 ∈ S` blocked at `R = 1`.
The residue of `d0` is NOT required; the only-blocker hypothesis is NOT required.  (`landing_R1_iff_lonely` is the case of a residue-`0`
reading, `ropen_eq_R1`.) -/
theorem landing_opening_iff_lonely (m : ℝ) (S : Finset ℝ) (hm : 0 < m) (hmS : m ∈ S) (d0 : ℝ) (hd0S : d0 ∈ S) (hd0 : 0 < d0)
    (hb : |RealCase.dev m 1 d0| < 1) : IsLandingR m S (ropen m d0) ↔ LonelyR m S (ropen m d0) := by
  have hgt : 1 < ropen m d0 := by
    unfold ropen; have := RealCase.eps_pos (div_pos hd0 hm) hb; linarith
  constructor
  · intro h; exact h.1.2
  · intro hl
    refine ⟨⟨by linarith, hl⟩, ?_⟩
    rintro x ⟨hx, hxl⟩
    have h1 : 1 ≤ x := lonelyR_ge_one hm hmS hx hxl
    by_contra hc
    push Not at hc
    exact blocks_until_opening m d0 x hm hd0 hb h1 hc (hxl d0 hd0S)

#print axioms ropen_eq_R1
#print axioms blocks_until_opening
#print axioms landing_opening_iff_lonely

/-- Window form: `Win (r + x)` for `r ∈ {1,…,8}`, `|x| ≤ 1` [L]. -/
theorem win_ridx (r : ℤ) (hr1 : 1 ≤ r) (hr8 : r ≤ 8) (x : ℝ) (hx : |x| ≤ 1) :
    Win ((r : ℝ) + x) ↔ ((r = 8 → 1 ≤ |x|) ∧ (r = 1 → 0 ≤ x) ∧ (r = 7 → x ≤ 0)) := by
  by_cases h : r = 8
  · subst h
    have e : ((8 : ℤ) : ℝ) + x = x + 8 * ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [e, win_shift]
    have hc := win_class 0 (le_refl _) (by norm_num) x hx
    simp only [Int.cast_zero, zero_add] at hc
    rw [hc]
    exact ⟨fun ⟨a, _, _⟩ => ⟨fun _ => a trivial, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩,
      fun ⟨a, _, _⟩ => ⟨fun _ => a (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩⟩
  · have := win_class r (by omega) (by omega) x hx
    rw [this]
    exact ⟨fun ⟨_, b, c⟩ => ⟨fun h' => absurd h' h, b, c⟩, fun ⟨_, b, c⟩ => ⟨fun h' => absurd h' (by omega), b, c⟩⟩

#print axioms win_ridx

/-- The deviation of reading `d` at `R1`, in the reduced coordinate: `x_d = e_d + (ridx_d + e_d) δ + 8 {quo_d δ}`, `δ = R1 - 1`. -/
noncomputable def xdev (m d0 d : ℝ) : ℝ :=
  edev m d + ((ridx m d : ℝ) + edev m d) * (R1 m d0 - 1) + 8 * Int.fract ((quo m d : ℝ) * (R1 m d0 - 1))

/-- **The reading of `d` at `R1` is `ridx + x_d`** [L]: `dRed/m · R1 + 8 {quo R1} = ridx_d + x_d`. -/
theorem reading_at_R1 (m d0 d : ℝ) (hm : m ≠ 0) :
    dRed m d / m * R1 m d0 + 8 * Int.fract ((quo m d : ℝ) * R1 m d0) = (ridx m d : ℝ) + xdev m d0 d := by
  unfold xdev
  have h1 : Int.fract ((quo m d : ℝ) * R1 m d0) = Int.fract ((quo m d : ℝ) * (R1 m d0 - 1)) := by
    have : (quo m d : ℝ) * R1 m d0 = (quo m d : ℝ) * (R1 m d0 - 1) + ((quo m d : ℤ) : ℝ) := by ring
    rw [this, Int.fract_add_intCast]
  rw [h1, dRed_div m d hm]
  ring

/-- **THE FAMILY, exactly** [L].  `m > 0`, `m ∈ S`, `d0 ∈ S` with `idx ≡ 0 (mod 8)`.  `R1 = 1 + (1 - e0)/ρ0` is the landing iff
every other reading satisfies `Win (ridx_d + x_d)`, `x_d = e_d + (ridx_d + e_d)(R1 - 1) + 8 {quo_d (R1 - 1)}`.  No sampling, no
window, no only-blocker hypothesis. -/
theorem family_landing_iff (m : ℝ) (S : Finset ℝ) (hm : 0 < m) (hmS : m ∈ S) (d0 : ℝ) (hd0S : d0 ∈ S) (hd0 : 0 < d0)
    (h8 : idx m d0 % 8 = 0) :
    IsLandingR m S (R1 m d0) ↔ ∀ d ∈ S, d ≠ d0 → Win ((ridx m d : ℝ) + xdev m d0 d) := by
  rw [landing_R1_iff_lonely m S hm hmS d0 hd0S hd0 h8]
  unfold LonelyR Cascade.LonelyAt
  constructor
  · intro h d hd hne
    have := h d hd
    rw [clear_iff_win m d _ hm.ne', win_orig_iff_fract m d _ hm.ne', reading_at_R1 m d0 d hm.ne'] at this
    exact this
  · intro h d hd
    rw [clear_iff_win m d _ hm.ne']
    by_cases hne : d = d0
    · subst hne
      obtain ⟨k, hk⟩ : ∃ k : ℤ, idx m d = 8 * k := ⟨idx m d / 8, by omega⟩
      have := R1_opening m d hm hd0 k hk
      rw [show d / m * R1 m d = R1 m d * (d / m) by ring, this]
      have e : (8 * (k : ℝ) + 1) = 1 + 8 * (k : ℝ) := by ring
      rw [e, win_shift, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [win_orig_iff_fract m d _ hm.ne', reading_at_R1 m d0 d hm.ne']
      exact h d hd hne

#print axioms reading_at_R1
#print axioms family_landing_iff

/-- **The same, as residue-class inequalities** [L], under the window `|x_d| ≤ 1` (REQUIRED, `family_window_required_example`):
every other reading has `(ridx = 8 → 1 ≤ |x|) ∧ (ridx = 1 → 0 ≤ x) ∧ (ridx = 7 → x ≤ 0)`. -/
theorem family_landing_classes (m : ℝ) (S : Finset ℝ) (hm : 0 < m) (hmS : m ∈ S) (d0 : ℝ) (hd0S : d0 ∈ S) (hd0 : 0 < d0)
    (h8 : idx m d0 % 8 = 0) (hw : ∀ d ∈ S, d ≠ d0 → |xdev m d0 d| ≤ 1) :
    IsLandingR m S (R1 m d0) ↔ ∀ d ∈ S, d ≠ d0 →
      ((ridx m d = 8 → 1 ≤ |xdev m d0 d|) ∧ (ridx m d = 1 → 0 ≤ xdev m d0 d) ∧ (ridx m d = 7 → xdev m d0 d ≤ 0)) := by
  rw [family_landing_iff m S hm hmS d0 hd0S hd0 h8]
  refine forall₂_congr (fun d hd => ?_)
  refine imp_congr_right (fun hne => ?_)
  exact win_ridx (ridx m d) (ridx_ge m d) (ridx_le m d) _ (hw d hd hne)

#print axioms family_landing_classes

/-- **The first cascade move, when `d0` is the only blocker at `R = 1`** [L].  If every other reading is clear at `R = 1`, then
`t'` is the move from the bound iff `8 m t' = R1`.  (Hypothesis `m, d0 > 0`, `idx ≡ 0`.) -/
theorem first_move_residue_zero {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (hpos : ∀ d ∈ S, 0 < d) (d0 : ℝ) (h0S : d0 ∈ S)
    (h8 : idx m d0 % 8 = 0)
    (hothers : ∀ d ∈ S, d ≠ d0 → (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m)))) (t' : ℝ) :
    IsMove S (1 / (8 * m)) t' ↔ 8 * m * t' = R1 m d0 := by
  have hdev0 : RealCase.dev m 1 d0 = edev m d0 := dev_one_r0 m d0 h8
  have hb0 : |RealCase.dev m 1 d0| < 1 := by
    rw [hdev0]; have := abs_edev_le m d0; linarith
  have hbl : ∀ e' ∈ S, |RealCase.dev m 1 e'| < 1 → e' = d0 := by
    intro e' he' hb
    by_contra hne
    have hw : InWay e' (1 / (8 * m)) := (RealCase.inWay_gate_iff hm).mpr hb
    exact (Cascade.not_inWay_iff.mpr (hothers e' he' hne)) hw
  constructor
  · intro hmv
    rcases RealCase.isMove_gate hpos hm hmv with ⟨hall, -⟩ | ⟨e', he', hb, ht', -⟩
    · exact absurd (hall d0 h0S) (not_le.mpr hb0)
    · have := hbl e' he' hb
      subst this
      rw [ht', hdev0]; rfl
  · intro ht
    refine RealCase.isMove_of_gate hpos hm h0S hb0 (by rw [ht, hdev0]; rfl) ?_
    intro e' he' hb
    rw [hbl e' he' hb]

#print axioms first_move_residue_zero

/-! ## (4) Hypothesis tests: each hypothesis dropped, with an explicit instance -/

/-- Helper [L]: `Win y ↔ 1 ≤ y - 8n ≤ 7` when `0 ≤ y - 8 n < 8`. -/
theorem win_mod (y : ℝ) (n : ℤ) (h0 : 0 ≤ y - 8 * (n : ℝ)) (h8 : y - 8 * (n : ℝ) < 8) :
    Win y ↔ (1 ≤ y - 8 * (n : ℝ) ∧ y - 8 * (n : ℝ) ≤ 7) := by
  have e : y = (y - 8 * (n : ℝ)) + 8 * (n : ℝ) := by ring
  conv_lhs => rw [e]
  rw [win_shift]
  exact win_of_Ico h0 h8

theorem idx_int (m d : ℝ) (c : ℤ) (h1 : (c : ℝ) - 1 / 2 ≤ d / m) (h2 : d / m < (c : ℝ) + 1 / 2) : idx m d = c := by
  unfold idx; exact round_eq_int _ _ h1 h2

/-- **The second move** [L].  `S = (1,2,3,4,5,7,8)`, `m = 1`, `d0 = 8` (`idx 8`, `e = 0`): `d0` is the only blocker at `R = 1`
(the others are clear: `7` sits at residue `7` with `e = 0`), `R1 = 9/8`, but `S` is NOT lonely at `R1` (the reading `7` has
moved to `63/8 > 7`), and the landing is `9/7`, set by the runner `7` (residue `7`, `e = 0 > -(ρ~)(R1 - 1)`). -/
theorem second_move_example :
    R1 1 (8 : ℝ) = 9 / 8 ∧ (∀ d ∈ ({1, 2, 3, 4, 5, 7, 8} : Finset ℝ), d ≠ 8 → (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * 1)))) ∧
    ¬ LonelyR 1 ({1, 2, 3, 4, 5, 7, 8} : Finset ℝ) (9 / 8) ∧ IsLandingR 1 ({1, 2, 3, 4, 5, 7, 8} : Finset ℝ) (9 / 7) := by
  have hidx : idx 1 (8 : ℝ) = 8 := idx_int 1 8 8 (by norm_num) (by norm_num)
  have he : edev 1 (8 : ℝ) = 0 := by unfold edev; rw [hidx]; norm_num
  have hR1 : R1 1 (8 : ℝ) = 9 / 8 := by unfold R1; rw [he]; norm_num
  refine ⟨hR1, ?_, ?_, ?_⟩
  · intro d hd hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have := (clear_iff_win 1 d 1 one_ne_zero)
    have e : d * (1 / (8 * 1)) = d * ((1 : ℝ) / (8 * 1)) := rfl
    rw [e, this]
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [div_one, mul_one, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · exact absurd rfl hne
  · intro h
    have h7 := h 7 (by simp)
    unfold LonelyR Cascade.LonelyAt at h
    rw [clear_iff_win 1 7 _ one_ne_zero, div_one, win_of_Ico (by norm_num) (by norm_num)] at h7
    norm_num at h7
  · refine ⟨⟨by norm_num, ?_⟩, ?_⟩
    · unfold LonelyR Cascade.LonelyAt
      intro d hd
      rw [clear_iff_win 1 d _ one_ne_zero, div_one]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_mod _ 1 (by norm_num) (by norm_num)]; norm_num
      · rw [win_mod _ 1 (by norm_num) (by norm_num)]; norm_num
    · rintro x ⟨hx, hxl⟩
      have hmem : (1 : ℝ) ∈ ({1, 2, 3, 4, 5, 7, 8} : Finset ℝ) := by simp
      have h1 : 1 ≤ x := lonelyR_ge_one one_pos hmem hx hxl
      by_contra hlt
      push Not at hlt
      have hx8 : (9 : ℝ) / 8 ≤ x := by
        by_contra hc
        push Not at hc
        have hb := residue_zero_blocks 1 8 x one_pos (by norm_num) (by rw [hidx]; norm_num) h1 (by rw [hR1]; exact hc)
        exact hb (by have := hxl 8 (by simp); simpa using this)
      have h7 := hxl 7 (by simp)
      rw [clear_iff_win 1 7 _ one_ne_zero, div_one] at h7
      rcases lt_or_ge x (8 / 7) with hc | hc
      · rw [win_mod _ 0 (by push_cast; linarith) (by push_cast; linarith)] at h7
        push_cast at h7
        linarith [h7.2]
      · rw [win_mod _ 1 (by push_cast; linarith) (by push_cast; linarith)] at h7
        push_cast at h7
        linarith [h7.1]

#print axioms second_move_example

/-- **`m ∈ S` is REQUIRED for `landing_R1_iff_lonely`** [L]: `m = 1`, `S = {2, 8}`, `d0 = 8`: `S` is lonely at `R1 = 9/8`, yet the landing
is not `9/8` because `S` is already lonely at `R = 1/2`. -/
theorem family_unit_required_example :
    R1 1 (8 : ℝ) = 9 / 8 ∧ LonelyR 1 ({2, 8} : Finset ℝ) (9 / 8) ∧ ¬ IsLandingR 1 ({2, 8} : Finset ℝ) (9 / 8) := by
  have hidx : idx 1 (8 : ℝ) = 8 := idx_int 1 8 8 (by norm_num) (by norm_num)
  have he : edev 1 (8 : ℝ) = 0 := by unfold edev; rw [hidx]; norm_num
  have hR1 : R1 1 (8 : ℝ) = 9 / 8 := by unfold R1; rw [he]; norm_num
  refine ⟨hR1, ?_, ?_⟩
  · unfold LonelyR Cascade.LonelyAt
    intro d hd
    rw [clear_iff_win 1 d _ one_ne_zero, div_one]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
    · rw [win_mod _ 1 (by norm_num) (by norm_num)]; norm_num
  · intro h
    have hl : LonelyR 1 ({2, 8} : Finset ℝ) (1 / 2) := by
      unfold LonelyR Cascade.LonelyAt
      intro d hd
      rw [clear_iff_win 1 d _ one_ne_zero, div_one]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
      · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
    have := h.2 ⟨by norm_num, hl⟩
    norm_num at this

#print axioms family_unit_required_example

/-- **The window of `family_landing_classes` is REQUIRED** [L]: `m = 1`, `S = {1, 32/5, 8}`, `d0 = 8`.  The reading `32/5` has
`ridx = 6`, `e = 2/5`, `x = 6/5 > 1`; the class inequalities (nothing is asked of residue `6`) hold for both other readings, yet
`S` is NOT lonely at `R1 = 9/8` (`(32/5)(9/8) = 36/5 > 7`). -/
theorem family_window_required_example :
    (∀ d ∈ ({1, 32 / 5, 8} : Finset ℝ), d ≠ 8 →
      ((ridx 1 d = 8 → 1 ≤ |xdev 1 8 d|) ∧ (ridx 1 d = 1 → 0 ≤ xdev 1 8 d) ∧ (ridx 1 d = 7 → xdev 1 8 d ≤ 0))) ∧
    ¬ IsLandingR 1 ({1, 32 / 5, 8} : Finset ℝ) (R1 1 8) ∧ |xdev 1 8 (32 / 5 : ℝ)| = 6 / 5 := by
  have hidx : idx 1 (8 : ℝ) = 8 := idx_int 1 8 8 (by norm_num) (by norm_num)
  have he : edev 1 (8 : ℝ) = 0 := by unfold edev; rw [hidx]; norm_num
  have hR1 : R1 1 (8 : ℝ) = 9 / 8 := by unfold R1; rw [he]; norm_num
  have hi6 : idx 1 (32 / 5 : ℝ) = 6 := idx_int 1 _ 6 (by norm_num) (by norm_num)
  have hr6 : ridx 1 (32 / 5 : ℝ) = 6 := by unfold ridx; rw [hi6]; norm_num
  have hq6 : quo 1 (32 / 5 : ℝ) = 0 := by unfold quo; rw [hi6]; norm_num
  have he6 : edev 1 (32 / 5 : ℝ) = 2 / 5 := by unfold edev; rw [hi6]; norm_num
  have hx6 : xdev 1 8 (32 / 5 : ℝ) = 6 / 5 := by
    unfold xdev; rw [hr6, hq6, he6, hR1]; norm_num
  have hi1 : idx 1 (1 : ℝ) = 1 := idx_self one_pos
  have hr1 : ridx 1 (1 : ℝ) = 1 := by unfold ridx; rw [hi1]; norm_num
  have hq1 : quo 1 (1 : ℝ) = 0 := by unfold quo; rw [hi1]; norm_num
  have he1 : edev 1 (1 : ℝ) = 0 := edev_self one_pos
  have hx1 : xdev 1 8 (1 : ℝ) = 1 / 8 := by
    unfold xdev; rw [hr1, hq1, he1, hR1]; norm_num
  refine ⟨?_, ?_, by rw [hx6]; norm_num⟩
  · intro d hd hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · rw [hr1, hx1]; norm_num
    · rw [hr6]; norm_num
    · exact absurd rfl hne
  · intro h
    rw [hR1] at h
    have hl := h.1.2
    have h2 := hl (32 / 5) (by simp)
    rw [clear_iff_win 1 _ _ one_ne_zero, div_one, win_mod _ 0 (by norm_num) (by norm_num)] at h2
    norm_num at h2

#print axioms family_window_required_example

/-- **The slow-reading hypothesis `ρ ≤ 8` of `gridPart_one_slow` is REQUIRED** [L]: `m = 1`, `s = 17` (`idx = 17`, `e = 0`),
`R = 25/17 ∈ (1,2)`, lap `z = 3`: `Ngrid = 8`, whereas `(1 - idx) mod 8 = 0`.  The integer part is `(1 - idx) mod 8` plus ONE
extra full lap of the last mover. -/
theorem gridPart_one_slow_needs_slow :
    (25 / 17 : ℝ) * (17 / 1) = 8 * ((3 : ℤ) : ℝ) + 1 ∧ (1 : ℝ) < 25 / 17 ∧ (25 / 17 : ℝ) < 2 ∧
      gridPart 1 (idx 1 (17 : ℝ)) 3 = 8 ∧ (1 - idx 1 (17 : ℝ)) % 8 = 0 := by
  have hi : idx 1 (17 : ℝ) = 17 := idx_int 1 17 17 (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · unfold gridPart; rw [hi]; norm_num
  · rw [hi]; norm_num

/-- **Without the window, the last mover need not be blocked at `a` when `Ngrid = 0`, `e < 0`** [L]: `m = 1`, `s = 9/2`
(`idx = 5`, `e = -1/2`), `a = 5`, `R = 50/9 ∈ (5, 6)`, lap `z = 3`: `Ngrid = 0`, yet `s` is clear at `a = 5` (`|e a| = 5/2 > 1`). -/
theorem self_window_required_example :
    (50 / 9 : ℝ) * (9 / 2 / 1) = 8 * ((3 : ℤ) : ℝ) + 1 ∧ (5 : ℝ) < 50 / 9 ∧ (50 / 9 : ℝ) < 6 ∧
      gridPart 5 (idx 1 (9 / 2 : ℝ)) 3 = 0 ∧ edev 1 (9 / 2 : ℝ) < 0 ∧
      (1 / 8 : ℝ) ≤ distInt ((9 / 2 : ℝ) * (((5 : ℤ) : ℝ) / (8 * 1))) := by
  have hi : idx 1 (9 / 2 : ℝ) = 5 := idx_int 1 _ 5 (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · unfold gridPart; rw [hi]; norm_num
  · unfold edev; rw [hi]; norm_num
  · rw [clear_at_unit one_pos 5 (9 / 2), hi]
    have he : edev 1 (9 / 2 : ℝ) = -1 / 2 := by unfold edev; rw [hi]; norm_num
    rw [he, win_mod _ (-1) (by norm_num) (by norm_num)]
    norm_num

#print axioms gridPart_one_slow_needs_slow
#print axioms self_window_required_example

/-- **At `a = 1`, any `ρ`: the grid part is `(1 - idx) mod 8` plus a non-negative number of full laps** [L]
(`1 < R < 2`).  `Ngrid = (1 - idx) mod 8 + 8 w`, `w ≥ 0`, and `Ngrid < idx + 2e`.  `w` is the number of extra laps the last mover
makes between its grid instant and the landing; `gridPart_one_slow` is `w = 0`. -/
theorem gridPart_one_laps (m s R : ℝ) (z : ℤ) (hsm : 0 < s / m)
    (hz : R * (s / m) = 8 * (z : ℝ) + 1) (h1 : (1 : ℝ) < R) (h2 : R < 2) :
    ∃ w : ℤ, 0 ≤ w ∧ gridPart 1 (idx m s) z = (1 - idx m s) % 8 + 8 * w ∧
      ((gridPart 1 (idx m s) z : ℤ) : ℝ) < (idx m s : ℝ) + 2 * edev m s := by
  have hb := gridPart_bounds m s R 1 z hsm hz (by exact_mod_cast h1) (by push_cast; linarith)
  have he1 := edev_ge m s
  have hem := gridPart_emod 1 (idx m s) z
  push_cast at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hN0 : 0 ≤ gridPart 1 (idx m s) z := by
    by_contra hc; push Not at hc
    have : (gridPart 1 (idx m s) z : ℝ) ≤ -1 := by exact_mod_cast (show gridPart 1 (idx m s) z ≤ -1 by omega)
    linarith
  refine ⟨(gridPart 1 (idx m s) z - (1 - idx m s) % 8) / 8, ?_, ?_, by linarith⟩ <;> omega

#print axioms gridPart_one_laps

/-! ## (5) The integer part is fixed by the previous landing -/

/-- **The grid part against the PREVIOUS landing** [L].  A step of the chain: setter `s` blocked at `R0` on lap `z`
(`|ρ R0 - 8 z| < 1`), landing `R1` (`R1 ρ = 8 z + 1`).  For every integer `a`, with `u = R0 - a`,
`Ngrid(a, idx, z) = ρ u + a e + (1 - δ)`, `δ = ρ R0 - 8 z`; hence
`ρ (R0 - a) + a e < Ngrid < ρ (R0 - a) + a e + 2`.  The integer part is the previous landing's offset from the grid instant
(times `ρ`), plus the deviation part, plus the `(0,2)` of the move.  The landing equation `R1 ρ = 8 z + 1` is not used (only that
`z` is the lap on which `s` is blocked at `R0`): that hypothesis is NOT REQUIRED. -/
theorem gridPart_prev_window (m s R0 : ℝ) (a z : ℤ) (hb : |s / m * R0 - 8 * (z : ℝ)| < 1) :
    (s / m) * (R0 - a) + (a : ℝ) * edev m s < (gridPart a (idx m s) z : ℝ) ∧
      (gridPart a (idx m s) z : ℝ) < (s / m) * (R0 - a) + (a : ℝ) * edev m s + 2 := by
  have h : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  unfold gridPart
  push_cast
  rw [h] at hb1 hb2 ⊢
  constructor <;> nlinarith [hb1, hb2]

/-- **The integer part is DETERMINED by its class mod 8 and the previous landing** [L]: two laps `z, z'` for which `|ρ R0 - 8 z| < 1`
and `|ρ R0 - 8 z'| < 1` (the same blocked reading at the same `R0`) are equal, so their grid parts are equal.  Equivalently two
integers in the open window of length 2 of `gridPart_prev_window` that are congruent mod 8 coincide.  [PROVISIONAL: covering] (window length 2 against the period 8; supports: the integer part is fixed by its class and the previous landing).
(The landing equations `R1 ρ = 8 z + 1` are NOT used: this hypothesis is not required.) -/
theorem gridPart_prev_unique (m s R0 : ℝ) (a z z' : ℤ) (hb : |s / m * R0 - 8 * (z : ℝ)| < 1)
    (hb' : |s / m * R0 - 8 * (z' : ℝ)| < 1) : gridPart a (idx m s) z = gridPart a (idx m s) z' := by
  obtain ⟨c1, c2⟩ := abs_lt.mp hb
  obtain ⟨c1', c2'⟩ := abs_lt.mp hb'
  have e : ((8 * (z - z') : ℤ) : ℝ) < 2 := by push_cast; linarith
  have e' : (-2 : ℝ) < ((8 * (z - z') : ℤ) : ℝ) := by push_cast; linarith
  have f1 : 8 * (z - z') < 2 := by exact_mod_cast e
  have f2 : -2 < 8 * (z - z') := by exact_mod_cast e'
  have : z = z' := by omega
  rw [this]

/-- **First step from the bound, `a = 1`** [L]: with `R0 = 1` the window is `(e, e + 2)`, so the grid part of the first move is
`0`, `1` or `2`; `0` needs `e < 0`, and `2` needs `e > 0`.  (These are the residue classes `1`, `0`, `7` of `isMove_one_classes`.) -/
theorem gridPart_first_step (m s : ℝ) (z : ℤ) (hb : |s / m * 1 - 8 * (z : ℝ)| < 1) :
    0 ≤ gridPart 1 (idx m s) z ∧ gridPart 1 (idx m s) z ≤ 2 ∧ (gridPart 1 (idx m s) z = 0 → edev m s < 0) ∧
      (gridPart 1 (idx m s) z = 2 → 0 < edev m s) := by
  have hw := gridPart_prev_window m s 1 1 z hb
  have he1 := edev_ge m s
  have he2 := edev_lt m s
  have hρ : s / m = (idx m s : ℝ) + edev m s := by unfold edev; ring
  obtain ⟨w1, w2⟩ := hw
  push_cast at w1 w2
  have w1' : edev m s < (gridPart 1 (idx m s) z : ℝ) := by simpa using w1
  have w2' : (gridPart 1 (idx m s) z : ℝ) < edev m s + 2 := by simpa using w2
  refine ⟨?_, ?_, fun h0 => ?_, fun h2 => ?_⟩
  · by_contra hc; push Not at hc
    have : (gridPart 1 (idx m s) z : ℝ) ≤ -1 := by exact_mod_cast (show gridPart 1 (idx m s) z ≤ -1 by omega)
    linarith
  · by_contra hc; push Not at hc
    have : (3 : ℝ) ≤ (gridPart 1 (idx m s) z : ℝ) := by exact_mod_cast (show 3 ≤ gridPart 1 (idx m s) z by omega)
    linarith
  · rw [h0] at w1'; push_cast at w1'; linarith
  · rw [h2] at w2'; push_cast at w2'; linarith

#print axioms gridPart_prev_window
#print axioms gridPart_prev_unique
#print axioms gridPart_first_step
#print axioms win_mod
#print axioms idx_int
#print axioms R1_gt_one

/-! ## (6) The family `(1,…,6, 8 + e)`: the threshold, and a deviation counterexample -/

/-- The integer readings `1 ≤ j ≤ 8` at base `m = 1`: `ridx = j`, `quo = 0`, `e = 0` [L]. -/
theorem small_reading (d : ℝ) (j : ℤ) (hd : d = (j : ℝ)) (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    ridx 1 d = j ∧ quo 1 d = 0 ∧ edev 1 d = 0 := by
  have hi : idx 1 d = j := idx_int 1 d j (by rw [hd, div_one]; linarith) (by rw [hd, div_one]; linarith)
  refine ⟨?_, ?_, ?_⟩
  · unfold ridx; rw [hi]; omega
  · unfold quo; rw [hi]; omega
  · unfold edev; rw [hi, hd]; simp

/-- **The family `(1,2,3,4,5,6, 8 + e)`, `e ∈ [-1/2, 1/2)`: the landing is `R1` exactly when `e ≥ -2/7`** [L].  `d0 = 8 + e` has
`ridx = 8`, `R1 = 9/(8 + e)`; the readings `1,…,5` are always clear at `R1` and the reading `6` is clear iff `6 R1 ≤ 7` iff
`e ≥ -2/7`.  For `e < -2/7` the first move is NOT the landing (`second_move_deviation_example`).  Nothing else is needed:
no window, no sampling.  The same family with `8k + e`, `k ≥ 2`, always lands at `R1` (`[OBS]`, `displaced_landing_v1.out`). -/
theorem six_family_threshold (e : ℝ) (he1 : -1 / 2 ≤ e) (he2 : e < 1 / 2) :
    IsLandingR 1 ({1, 2, 3, 4, 5, 6, 8 + e} : Finset ℝ) (R1 1 (8 + e)) ↔ -2 / 7 ≤ e := by
  have hidx : idx 1 (8 + e) = 8 := idx_int 1 (8 + e) 8 (by rw [div_one]; push_cast; linarith) (by rw [div_one]; push_cast; linarith)
  have hed : edev 1 (8 + e) = e := by unfold edev; rw [hidx]; push_cast; ring
  have hpos : (0 : ℝ) < 8 + e := by linarith
  have hR1 : R1 1 (8 + e) = 9 / (8 + e) := by
    unfold R1; rw [hed, div_one]; field_simp; ring
  have hlo : 1 < R1 1 (8 + e) := R1_gt_one 1 (8 + e) one_pos hpos
  have hhi : R1 1 (8 + e) ≤ 6 / 5 := by
    rw [hR1, div_le_div_iff₀ hpos (by norm_num)]; linarith
  have hmem : (1 : ℝ) ∈ ({1, 2, 3, 4, 5, 6, 8 + e} : Finset ℝ) := by simp
  have hd0S : (8 + e) ∈ ({1, 2, 3, 4, 5, 6, 8 + e} : Finset ℝ) := by simp
  rw [family_landing_iff 1 _ one_pos hmem (8 + e) hd0S hpos (by rw [hidx]; norm_num)]
  -- the value of the reading j at R1
  have key : ∀ (d : ℝ) (j : ℤ), d = (j : ℝ) → 1 ≤ j → j ≤ 8 →
      (Win ((ridx 1 d : ℝ) + xdev 1 (8 + e) d) ↔ Win ((j : ℝ) * R1 1 (8 + e))) := by
    intro d j hd h1 h8
    obtain ⟨hr, hq, hee⟩ := small_reading d j hd h1 h8
    unfold xdev
    rw [hr, hq, hee]
    have : (j : ℝ) + (0 + ((j : ℝ) + 0) * (R1 1 (8 + e) - 1) + 8 * Int.fract (((0 : ℤ) : ℝ) * (R1 1 (8 + e) - 1))) =
        (j : ℝ) * R1 1 (8 + e) := by simp; ring
    rw [this]
  have ne6 : ∀ x : ℝ, x ≤ 6 → x ≠ 8 + e := fun x hx h => by linarith
  constructor
  · intro h
    have h6 := h 6 (by simp) (ne6 6 le_rfl)
    rw [key 6 6 (by norm_num) (by norm_num) (by norm_num), win_of_Ico (by push_cast; positivity) (by push_cast; linarith)] at h6
    push_cast at h6
    rw [hR1] at h6
    have := h6.2
    rw [mul_div_assoc', div_le_iff₀ hpos] at this
    linarith
  · intro h d hd hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hb : ∀ j : ℤ, 1 ≤ j → j ≤ 6 → (j : ℝ) * R1 1 (8 + e) ≤ 7 → Win ((j : ℝ) * R1 1 (8 + e)) := by
      intro j h1 h6 h7
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast h1
      have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast h6
      rw [win_of_Ico (by positivity) (by nlinarith)]
      constructor <;> nlinarith
    have b5 : ∀ j : ℤ, 1 ≤ j → j ≤ 5 → Win ((j : ℝ) * R1 1 (8 + e)) := fun j h1 h5 => by
      have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast h5
      exact hb j h1 (by omega) (by nlinarith)
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (key 1 1 (by norm_num) (by norm_num) (by norm_num)).mpr (by simpa using b5 1 (by norm_num) (by norm_num))
    · exact (key 2 2 (by norm_num) (by norm_num) (by norm_num)).mpr (by simpa using b5 2 (by norm_num) (by norm_num))
    · exact (key 3 3 (by norm_num) (by norm_num) (by norm_num)).mpr (by simpa using b5 3 (by norm_num) (by norm_num))
    · exact (key 4 4 (by norm_num) (by norm_num) (by norm_num)).mpr (by simpa using b5 4 (by norm_num) (by norm_num))
    · exact (key 5 5 (by norm_num) (by norm_num) (by norm_num)).mpr (by simpa using b5 5 (by norm_num) (by norm_num))
    · refine (key 6 6 (by norm_num) (by norm_num) (by norm_num)).mpr ?_
      have : ((6 : ℤ) : ℝ) * R1 1 (8 + e) ≤ 7 := by
        rw [hR1]; push_cast
        rw [mul_div_assoc', div_le_iff₀ hpos]; linarith
      simpa using hb 6 (by norm_num) (by norm_num) this
    · exact absurd rfl hne

#print axioms small_reading
#print axioms six_family_threshold

/-- **A deviation counterexample, exact** [L]: `S = (1,2,3,4,5,6,15/2)`, `d0 = 15/2` (`idx = 8` by the tie rule, `e = -1/2`),
`R1 = 6/5`, but the reading `6` is at `36/5 > 7`: `S` is not lonely at `R1`, so the first move is not the landing. -/
theorem second_move_deviation_example :
    R1 1 (15 / 2 : ℝ) = 6 / 5 ∧ ¬ LonelyR 1 ({1, 2, 3, 4, 5, 6, 15 / 2} : Finset ℝ) (6 / 5) := by
  have hidx : idx 1 (15 / 2 : ℝ) = 8 := idx_int 1 _ 8 (by norm_num) (by norm_num)
  have hed : edev 1 (15 / 2 : ℝ) = -1 / 2 := by unfold edev; rw [hidx]; norm_num
  have hR1 : R1 1 (15 / 2 : ℝ) = 6 / 5 := by unfold R1; rw [hed]; norm_num
  refine ⟨hR1, fun h => ?_⟩
  have h6 := h 6 (by simp)
  rw [clear_iff_win 1 6 _ one_ne_zero, div_one, win_of_Ico (by norm_num) (by norm_num)] at h6
  norm_num at h6

#print axioms second_move_deviation_example

/-! ## (7) More hypothesis tests -/

/-- **The sign relations REQUIRE `ρ > 0`** [L]: with a negative `ρ = s/m` (`m = 1`, `s = -1`) the landing equation can hold with
`R > a` while the grid part is BELOW `a e`.  (No runner is stationary or of negative disparity in the framework, so the
hypothesis is part of the object; this shows the equivalences of `gridPart_sign` do not survive without it.) -/
theorem sign_needs_positive_example :
    (7 : ℝ) * (-1 / 1) = 8 * ((-1 : ℤ) : ℝ) + 1 ∧ ((1 : ℤ) : ℝ) < 7 ∧
      ¬ (((1 : ℤ) : ℝ) * edev 1 (-1 : ℝ) < (gridPart 1 (idx 1 (-1 : ℝ)) (-1) : ℝ)) := by
  have hi : idx 1 (-1 : ℝ) = -1 := idx_int 1 (-1) (-1) (by norm_num) (by norm_num)
  have he : edev 1 (-1 : ℝ) = 0 := by unfold edev; rw [hi]; norm_num
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [he]
  unfold gridPart; rw [hi]; norm_num

/-- **`ρ ≤ 8` is REQUIRED for the first-opening formula `lap_first_opening`** [L]: `ρ = 16`, `a = 1`, `R = 25/16 ∈ (1,2)`, lap `3`;
the first opening after `a` is on lap `⌊(1·16 - 1)/8⌋ + 1 = 2` (`R = 17/16`).  (Whether the CASCADE ever lands on a later opening
of a fast last mover is data: `displaced_landing_v1.out`.) -/
theorem lap_first_opening_needs_slow :
    (25 / 16 : ℝ) * 16 = 8 * ((3 : ℤ) : ℝ) + 1 ∧ (1 : ℝ) < 25 / 16 ∧ (25 / 16 : ℝ) < 2 ∧
      (3 : ℤ) ≠ ⌊(((1 : ℤ) : ℝ) * 16 - 1) / 8⌋ + 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have : ⌊(((1 : ℤ) : ℝ) * 16 - 1) / 8⌋ = 1 := by
    rw [Int.floor_eq_iff]; constructor <;> norm_num
  rw [this]; norm_num

/-- Helper: `sres8` of a numeral with a known nearest multiple [L]. -/
theorem sres8_of (x : ℝ) (c : ℤ) (h1 : (c : ℝ) - 1 / 2 ≤ x / 8) (h2 : x / 8 < (c : ℝ) + 1 / 2) : RealCase.sres8 x = x - 8 * c := by
  unfold RealCase.sres8; rw [round_eq_int _ c h1 h2]

/-- **The only-blocker hypothesis is REQUIRED for `first_move_residue_zero`** [L]: `S = (1,2,3,4,5,36/5,8)`, `m = 1`, `d0 = 8` (residue
`0`, `R1 = 9/8`), but `36/5` (residue `7`, `e = 1/5 > 0`) is also blocked at `R = 1`, with the later opening `5/4`.  The first
move is `5/4`, not `R1`.  (`landing_R1_iff_lonely` does not use the hypothesis.) -/
theorem first_move_needs_only_blocker :
    R1 1 (8 : ℝ) = 9 / 8 ∧ IsMove ({1, 2, 3, 4, 5, 36 / 5, 8} : Finset ℝ) (1 / (8 * 1)) ((5 / 4) / 8) ∧
      ¬ IsMove ({1, 2, 3, 4, 5, 36 / 5, 8} : Finset ℝ) (1 / (8 * 1)) ((R1 1 (8 : ℝ)) / (8 * 1)) := by
  have hidx : idx 1 (8 : ℝ) = 8 := idx_int 1 8 8 (by norm_num) (by norm_num)
  have he : edev 1 (8 : ℝ) = 0 := by unfold edev; rw [hidx]; norm_num
  have hR1 : R1 1 (8 : ℝ) = 9 / 8 := by unfold R1; rw [he]; norm_num
  have hpos : ∀ d ∈ ({1, 2, 3, 4, 5, 36 / 5, 8} : Finset ℝ), 0 < d := by
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hmv : IsMove ({1, 2, 3, 4, 5, 36 / 5, 8} : Finset ℝ) (1 / (8 * 1)) ((5 / 4) / 8) := by
    have d36 : RealCase.dev 1 1 (36 / 5 : ℝ) = -4 / 5 := by
      unfold RealCase.dev; rw [sres8_of _ 1 (by norm_num) (by norm_num)]; norm_num
    have hdev : ∀ d : ℝ, d ∈ ({1, 2, 3, 4, 5, 36 / 5, 8} : Finset ℝ) → |RealCase.dev 1 1 d| < 1 → (1 - RealCase.dev 1 1 d) / (d / 1) ≤ 1 / 4 := by
      intro d hd hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · unfold RealCase.dev at hb; rw [sres8_of _ 0 (by norm_num) (by norm_num)] at hb; norm_num at hb
      · unfold RealCase.dev at hb; rw [sres8_of _ 0 (by norm_num) (by norm_num)] at hb; norm_num at hb
      · unfold RealCase.dev at hb; rw [sres8_of _ 0 (by norm_num) (by norm_num)] at hb; norm_num at hb
      · unfold RealCase.dev at hb; rw [sres8_of _ 1 (by norm_num) (by norm_num)] at hb; norm_num at hb
      · unfold RealCase.dev at hb; rw [sres8_of _ 1 (by norm_num) (by norm_num)] at hb; norm_num at hb
      · rw [d36]; norm_num
      · unfold RealCase.dev
        rw [sres8_of _ 1 (by norm_num) (by norm_num)]; norm_num
    have := RealCase.isMove_of_gate hpos (m := 1) (R0 := 1) (t' := (5 / 4) / 8) one_pos (e := 36 / 5) (by simp)
      (by rw [d36]; norm_num) (by rw [d36]; norm_num) (fun e' he' hb => by rw [d36]; norm_num; have := hdev e' he' hb; simpa using this)
    simpa using this
  refine ⟨hR1, hmv, fun h => ?_⟩
  have := Cascade.isMove_unique hmv h
  rw [hR1] at this
  norm_num at this

#print axioms sign_needs_positive_example
#print axioms lap_first_opening_needs_slow
#print axioms sres8_of
#print axioms first_move_needs_only_blocker

end Fresh.DisplacedLanding
