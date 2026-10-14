import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.FiveReach
import Fresh.Ladder
import Fresh.Gate

/-!
# The ladder at five readings: the budget law of a return (Task AY)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is stationary); no floats.

## What this file adds to `Fresh/Ladder.lean` (Task AU)

AU proved four disparities by the cascade chain (`reach_three_cascade`: `slowest_return`, `no_xyxy`, `block_four_false`)
and recorded the budget law of a return (`lap_lower_of_ratio`, `step_lt_ratio`) without formalising the product.  Here:

* **(1) The additive budget law** (`budget_sum`).  If `x` sets the move at `n` and is in the way again at `seq k`, `k > n`,
  then for the setters `w s` of the moves `s = n+1, …, k-1`
  `3 < ∑ x / w s`.
  It is the telescoping of `Dilation.nextOpening_eq_add_gap` (each move advances the instant by `gap/(8y) < 1/(4y)`)
  against the return inequality `x·seq k > j + 7/8`, `x·seq (n+1) = j + 1/8`.  No lap bound, no ordering of the readings,
  no integrality and no `m` are used; positivity of the disparities and the cascade moves only.
* **(2) The product form of AU** (`budget_product`): `(N+6)/N < ∏ F(ρ_s N)` with `N = 8j+1`, `ρ_s = w s / x`,
  `F P = P/(P-2)` for `P ≥ 9` and `9/7` otherwise; it needs the laps of the intermediate setters to be at least `1`
  (REQUIRED for this proof; the additive form does not need it).
* **(3) Corollaries recovered from (1)**: `return_after_four` (same statement as `Ladder.slowest_return`, hypothesis weakened to
  'every INTERMEDIATE setter is at least x'; no cube computation), the first clause of `triple_law` (`3 y < x`), and the pair law
  (`x y z x` forces `x/y + x/z > 3`).
* **(4) The first-entry law** (`entry_budget`): the same telescoping from the start `seq 0 = 1/(8m)`.
* **(5) Window laws** (`four_consecutive_distinct`, `return_three_distinct`): any four consecutive moves have at least three
  distinct setters; a return of a reading at most every intermediate setter has at least three distinct intermediate setters.
* **(6) OWED**: `FourDistinctLaw` (four distinct intermediate setters at a first return of the slowest; exact data only, tagged
  OWED); conditional corollaries `slowest_of_four_never_returns`, `five_first_return_all_others`.

NOT proved here: any existence statement (`Reach 4`, `Reach 5`, a lonely instant for five readings).  Nothing in this file
bounds where a lonely instant lies.

Provenance (existing declarations whose argument was read and understood, nothing copied): `FiveReach.return_law`,
`FiveReach.triple_law`, `FiveReach.step_lt`, `Ladder.lap_lower_of_ratio`, `Ladder.step_lt_ratio`,
`Dilation.nextOpening_eq_add_gap` and its commentary ("Successive setters' start slots").
-/

open Classical

namespace Fresh

namespace Ladder5

open Cascade Dilation ChainLaws FiveReachStudy Ladder

/-! ## (0) Bookkeeping: setters between a setting and a later visit -/

/-- If nobody is in the way at `seq s`, the cascade is stuck there forever. -/
theorem fixed_forever {E : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {s : ℕ}
    (hall : ∀ d ∈ E, ¬ InWay d (seq s)) : ∀ i : ℕ, seq (s + i) = seq s := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hall' : ∀ d ∈ E, ¬ InWay d (seq (s + i)) := by
      intro d hd; rw [ih]; exact hall d hd
    rcases hmv (s + i) with ⟨_, hfix⟩ | ⟨d, hd, hwd, _⟩
    · calc seq (s + (i + 1)) = seq (s + i + 1) := rfl
        _ = seq (s + i) := hfix
        _ = seq s := ih
    · exact absurd hwd (hall' d hd)

#print axioms fixed_forever

/-- **Every move before a later visit has a setter.**  If some member `x` of `E` is in the way at `seq k`, then for every
`s < k` somebody is in the way at `seq s` and the move at `s` has a setter. -/
theorem setter_before_visit {E : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {x : ℝ}
    (hxE : x ∈ E) {k : ℕ} (hw : InWay x (seq k)) {s : ℕ} (hs : s < k) : ∃ y, IsSetterAt E seq s y := by
  by_contra hno
  have hall : ∀ d ∈ E, ¬ InWay d (seq s) := by
    by_contra h
    push Not at h
    exact hno (exists_setter hmv (fun hall => by
      obtain ⟨d, hd, hdw⟩ := h
      exact hall d hd hdw))
  have := fixed_forever hmv hall (k - s)
  rw [show s + (k - s) = k by omega] at this
  rw [this] at hw
  exact hall x hxE hw

#print axioms setter_before_visit

/-! ## (1) The increment of one move -/

/-- **One move advances the instant by less than `1/(4y)` and by a positive amount.**  Corresponds to
`nextOpening_eq_add_gap` with `0 < gap < 2` (`Dilation.gap_pos`, `Dilation.gap_lt_two`). -/
theorem incr_setter {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {s : ℕ} {y : ℝ}
    (hy : IsSetterAt E seq s y) : 0 < seq (s + 1) - seq s ∧ seq (s + 1) - seq s < 1 / (4 * y) := by
  have hy0 := hpos y hy.1
  have h := nextOpening_eq_add_gap hy0 hy.2.1
  rw [← hy.2.2] at h
  have hg0 := gap_pos hy.2.1
  have hg2 := gap_lt_two hy.2.1
  have e : seq (s + 1) - seq s = gap y (seq s) / (8 * y) := by linarith
  rw [e]
  refine ⟨by positivity, ?_⟩
  have : gap y (seq s) / (8 * y) < 2 / (8 * y) := div_lt_div_of_pos_right hg2 (by positivity)
  calc gap y (seq s) / (8 * y) < 2 / (8 * y) := this
    _ = 1 / (4 * y) := by field_simp; ring

#print axioms incr_setter

/-- **The elapsed time between two landings is at most the sum of the `1/(4y)` of the setters in between.** -/
theorem sum_incr {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (a : ℕ) (w : ℕ → ℝ) :
    ∀ i : ℕ, (∀ s, a ≤ s → s < a + i → IsSetterAt E seq s (w s)) →
      seq (a + i) - seq a ≤ ∑ s ∈ Finset.Ico a (a + i), 1 / (4 * w s) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hws
    have h1 := ih (fun s h1 h2 => hws s h1 (by omega))
    have h2 := (incr_setter hpos (hws (a + i) (by omega) (by omega))).2
    rw [show a + (i + 1) = a + i + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    linarith

#print axioms sum_incr

/-! ## (2) The additive budget law -/

/-- **The budget law of a return (additive form)** [L].  `x` sets the move at `n` and is in the way again at `seq k`
(`k > n`); `w s` is the setter of the move at `s` for `n < s < k`.  Then `3 < ∑_{s=n+1}^{k-1} x / w s`.
Hypotheses: `hpos` (positive disparities; REQUIRED as stated, the proof divides by `x` and `w s`; negative disparities
reduce to it by `distInt_abs_mul`), the cascade moves `hmv`, `n < k`, `x` the setter at `n`, `x` in the way at `seq k`.
NOT REQUIRED (the proof does not use them): `0 < seq 0`, any lower bound on the laps, any ordering of the readings, a
base `m`, integrality, `seq 0 = 1/(8m)`. -/
theorem budget_sum {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    3 < ∑ s ∈ Finset.Ico (n + 1) k, x / w s := by
  have hx0 := hpos x hx.1
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  -- the reading of `x` only grows (`x > 0`, the cascade never goes back), so its later lap is a higher one
  have hle : seq (n + 1) ≤ seq k := seq_mono hpos hmv (Nat.succ_le_of_lt hnk)
  have h1 : x * seq (n + 1) ≤ x * seq k := mul_le_mul_of_nonneg_left hle hx0.le
  have hb := abs_lt.mp (abs_sub_lap_lt hw)
  have hlap0 : (lap x (seq n) : ℝ) < (lap x (seq k) : ℝ) := by linarith
  have hlap1 : lap x (seq n) < lap x (seq k) := by exact_mod_cast hlap0
  have hlap' : (lap x (seq n) : ℝ) + 1 ≤ (lap x (seq k) : ℝ) := by
    have : lap x (seq n) + 1 ≤ lap x (seq k) := by omega
    exact_mod_cast this
  -- x · (seq k − seq (n+1)) > 3/4
  have h34 : 3 / 4 < x * (seq k - seq (n + 1)) := by nlinarith [hb.1]
  have hsum := sum_incr hpos (n + 1) w (k - (n + 1)) (by
    intro s h1 h2
    exact hws s (by omega) (by omega))
  rw [show n + 1 + (k - (n + 1)) = k by omega] at hsum
  have hmul : x * (seq k - seq (n + 1)) ≤ x * ∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) :=
    mul_le_mul_of_nonneg_left hsum hx0.le
  have hcongr : x * ∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) = (∑ s ∈ Finset.Ico (n + 1) k, x / w s) / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_Ico.mp hs
    have hw0 := hpos _ (hws s (by omega) (by omega)).1
    field_simp
  rw [hcongr] at hmul
  linarith

#print axioms budget_sum

/-- **Budget law, setters supplied by the cascade** [L]: the same with the setters chosen. -/
theorem budget_sum_exists {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) :
    ∃ w : ℕ → ℝ, (∀ s, n < s → s < k → IsSetterAt E seq s (w s)) ∧ 3 < ∑ s ∈ Finset.Ico (n + 1) k, x / w s := by
  have hex : ∀ s, n < s → s < k → ∃ y, IsSetterAt E seq s y :=
    fun s _ hs => setter_before_visit hmv hx.1 hw hs
  choose! w hw' using hex
  exact ⟨w, hw', budget_sum hpos hmv hnk hx hw w hw'⟩

#print axioms budget_sum_exists

/-! ### Corollaries: AU's laws are the small cases of the additive law -/

/-- **`slowest_return` from the budget law** [L].  If every intermediate setter is at least `x`, each term of the sum is
at most `1`, so there are more than three terms: `n + 5 ≤ k`.  Same statement as `Ladder.slowest_return` (which needs a
base `m`, `seq 0 = 1/(8m)` and the cube computation), here with the weaker hypothesis that only the intermediate setters
are at least `x`. -/
theorem return_after_four {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) (hge : ∀ s, n < s → s < k → ∀ y, IsSetterAt E seq s y → x ≤ y) : n + 5 ≤ k := by
  obtain ⟨w, hws, hsum⟩ := budget_sum_exists hpos hmv hnk hx hw
  have hx0 := hpos x hx.1
  have hterm : ∀ s ∈ Finset.Ico (n + 1) k, x / w s ≤ 1 := by
    intro s hs
    have hs' := Finset.mem_Ico.mp hs
    have hset := hws s (by omega) hs'.2
    have hw0 := hpos _ hset.1
    rw [div_le_one hw0]
    exact hge s (by omega) hs'.2 _ hset
  have hle : ∑ s ∈ Finset.Ico (n + 1) k, x / w s ≤ ∑ s ∈ Finset.Ico (n + 1) k, (1 : ℝ) := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico] at hle
  simp only [nsmul_eq_mul, mul_one] at hle
  have h3 : (3 : ℝ) < ((k - (n + 1) : ℕ) : ℝ) := by linarith
  have h3' : 3 < k - (n + 1) := by exact_mod_cast h3
  omega

#print axioms return_after_four

/-- **The first clause of `triple_law` from the budget law** [L]: `x y x` forces `3 y < x`. -/
theorem triple_clause {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x)
    (hy : IsSetterAt E seq (n + 1) y) (hx' : IsSetterAt E seq (n + 2) x) : 3 * y < x := by
  have hs := budget_sum hpos hmv (k := n + 2) (by omega) hx hx'.2.1 (fun _ => y) (by
    intro s h1 h2
    have : s = n + 1 := by omega
    subst this; exact hy)
  have hy0 := hpos y hy.1
  have : Finset.Ico (n + 1) (n + 2) = {n + 1} := by ext i; simp
  rw [this, Finset.sum_singleton] at hs
  rw [lt_div_iff₀ hy0] at hs
  linarith

#print axioms triple_clause

/-- **The pair law** [L]: `x y z x` (the second `x` in the way at `seq (n+3)`) forces `3 < x/y + x/z`. -/
theorem pair_law {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x y z : ℝ} (hx : IsSetterAt E seq n x)
    (hy : IsSetterAt E seq (n + 1) y) (hz : IsSetterAt E seq (n + 2) z) (hx' : InWay x (seq (n + 3))) :
    3 < x / y + x / z := by
  have hs := budget_sum hpos hmv (k := n + 3) (by omega) hx hx' (fun s => if s = n + 1 then y else z) (by
    intro s h1 h2
    by_cases h : s = n + 1
    · subst h; simpa using hy
    · have : s = n + 2 := by omega
      subst this; simpa using hz)
  have : Finset.Ico (n + 1) (n + 3) = {n + 1, n + 2} := by ext i; simp; omega
  rw [this, Finset.sum_pair (by omega)] at hs
  simpa using hs

#print axioms pair_law

/-- **Three consecutive moves cannot return a reading to the way when every setter in between is at least it** [L]
(`x y z x` with `y, z ≥ x`: each of `x/y, x/z` is at most `1`, the sum at most `2 < 3`). -/
theorem no_return_in_three {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) 
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {x y z : ℝ} (hx : IsSetterAt E seq n x)
    (hy : IsSetterAt E seq (n + 1) y) (hz : IsSetterAt E seq (n + 2) z) (hxy : x ≤ y) (hxz : x ≤ z)
    (hx' : InWay x (seq (n + 3))) : False := by
  have h := pair_law hpos hmv hx hy hz hx'
  have hx0 := hpos x hx.1
  have hy0 := hpos y hy.1
  have hz0 := hpos z hz.1
  have h1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  have h2 : x / z ≤ 1 := (div_le_one hz0).mpr hxz
  linarith

#print axioms no_return_in_three

/-! ## (3) The first-entry law: the same telescoping from the start of the cascade -/

/-- **First-entry law** [L].  The cascade from `seq 0 = 1/(8m)` with every member of `E` at least `m`.  If `y ∈ E` is in
the way at `seq k` (so on a lap `≥ 1`, `Dilation.one_le_lap_of_bound`), then the setters `w s` of the moves `s < k`
satisfy `7/2 - y/(2m) < ∑_{s<k} y / w s`.  For `y = m` this reads `3 < ∑ m / w s`: the first return of the unit needs the
same budget `3` as any return, which is the gate `R ∈ [1, 7]` of `Gate`.  For `y > m` the threshold is lowered by
`(y - m)/(2m)`, the credit of a reading that is already `y/m` eighths ahead at the start.  Hypotheses: `0 < m`,
`m ≤ d` for `d ∈ E` (REQUIRED: gives lap `≥ 1`; with a reading below `m` the lap can be `0` and the bound fails,
`Ladder.audit_lower_bound`), `seq 0 = 1/(8m)` (REQUIRED: it is where the credit is measured). -/
theorem entry_budget {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d)
    (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {k : ℕ} {y : ℝ} (hyE : y ∈ E)
    (hw : InWay y (seq k)) (w : ℕ → ℝ) (hws : ∀ s, s < k → IsSetterAt E seq s (w s)) :
    7 / 2 - y / (2 * m) < ∑ s ∈ Finset.range k, y / w s := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hy0 := hpos y hyE
  have hb : 1 / (8 * m) ≤ seq k := h0 ▸ start_le_seq hpos hmv k
  have hl1 : 1 ≤ lap y (seq k) := one_le_lap_of_bound hm (hlow y hyE) hb hw
  have hl1' : (1 : ℝ) ≤ (lap y (seq k) : ℝ) := by exact_mod_cast hl1
  have hbd := (abs_lt.mp (abs_sub_lap_lt hw)).1
  have hsum := sum_incr hpos 0 w k (by intro s _ h2; exact hws s (by omega))
  rw [zero_add, ← Finset.range_eq_Ico] at hsum
  have hmul : y * (seq k - seq 0) ≤ y * ∑ s ∈ Finset.range k, 1 / (4 * w s) :=
    mul_le_mul_of_nonneg_left hsum hy0.le
  have hcongr : y * ∑ s ∈ Finset.range k, 1 / (4 * w s) = (∑ s ∈ Finset.range k, y / w s) / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hw0 := hpos _ (hws s (Finset.mem_range.mp hs)).1
    field_simp
  rw [hcongr] at hmul
  have hy8 : y * seq 0 = y / (8 * m) := by rw [h0]; field_simp
  have : 7 / 8 < y * seq k := by linarith
  have e : y * (seq k - seq 0) = y * seq k - y / (8 * m) := by rw [mul_sub, hy8]
  have hym : y / (2 * m) = 4 * (y / (8 * m)) := by field_simp; ring
  rw [e] at hmul
  linarith

#print axioms entry_budget

/-! ## (4) The product form of AU, and its relation to the additive law -/

/-- The step factor of an intermediate reading with `P = ρ N`: `P/(P-2)` once `P ≥ 9`, and the cap `9/7` below. -/
noncomputable def Fp (P : ℝ) : ℝ := if 9 ≤ P then P / (P - 2) else 9 / 7

theorem Fp_pos (P : ℝ) : 0 < Fp P := by
  unfold Fp
  split_ifs with h
  · exact div_pos (by linarith) (by linarith)
  · norm_num

#print axioms Fp_pos

/-- **One intermediate move, in the product form** [L]: `x` sets at `n` on lap `j`, `y` sets at `s > n` on a lap `≥ 1`;
then `seq (s+1) ≤ Fp (y/x · (8j+1)) · seq s`. -/
theorem step_le_Fp {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n s : ℕ} {x y : ℝ} (hx : IsSetterAt E seq n x) (hns : n < s)
    (hy : IsSetterAt E seq s y) (hl : 1 ≤ lap y (seq s)) :
    seq (s + 1) ≤ Fp (y / x * (8 * (lap x (seq n) : ℝ) + 1)) * seq s := by
  unfold Fp
  split_ifs with h9
  · exact (step_lt_ratio hpos h0 hmv hx hns hy h9).le
  · have hl' : (1 : ℝ) ≤ (lap y (seq s) : ℝ) := by exact_mod_cast hl
    have := step_lt hpos h0 hmv hy (N0 := 1) le_rfl hl'
    norm_num at this
    exact this.le

#print axioms step_le_Fp

/-- **The product form of the budget law** [L] (AU's `∏ ρN/(ρN − 2) > (N+6)/N`, for real readings).  With `x`, `n`, `k`,
`w` as in `budget_sum` and every intermediate setter on a lap `≥ 1`:
`(8j+7)/(8j+1) < ∏_{s=n+1}^{k-1} Fp (w s / x · (8j+1))`, `j = lap x (seq n)`.
REQUIRED by this proof: `0 < seq 0` and the lap bound on the intermediates (cap `9/7` below `P = 9`).  Neither is used by
`budget_sum`.  Whether the statement can fail without them is UNDECIDED. -/
theorem budget_product {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s))
    (hlap1 : ∀ s, n < s → s < k → 1 ≤ lap (w s) (seq s)) :
    (8 * (lap x (seq n) : ℝ) + 7) / (8 * (lap x (seq n) : ℝ) + 1) <
      ∏ s ∈ Finset.Ico (n + 1) k, Fp (w s / x * (8 * (lap x (seq n) : ℝ) + 1)) := by
  have hret := return_law hpos h0 hmv hnk hx hw
  have hap : 0 < seq (n + 1) := lt_of_lt_of_le h0 (start_le_seq hpos hmv (n + 1))
  have hiter : ∀ i : ℕ, (∀ s, n + 1 ≤ s → s < n + 1 + i → IsSetterAt E seq s (w s)) →
      (∀ s, n + 1 ≤ s → s < n + 1 + i → 1 ≤ lap (w s) (seq s)) →
      seq (n + 1 + i) ≤ (∏ s ∈ Finset.Ico (n + 1) (n + 1 + i),
        Fp (w s / x * (8 * (lap x (seq n) : ℝ) + 1))) * seq (n + 1) := by
    intro i
    induction i with
    | zero => intro _ _; simp
    | succ i ih =>
      intro hs hl
      have h1 := ih (fun s a b => hs s a (by omega)) (fun s a b => hl s a (by omega))
      have h2 := step_le_Fp hpos h0 hmv hx (show n < n + 1 + i by omega) (hs (n + 1 + i) (by omega) (by omega))
        (hl (n + 1 + i) (by omega) (by omega))
      rw [show n + 1 + (i + 1) = n + 1 + i + 1 by ring, Finset.prod_Ico_succ_top (by omega)]
      have hF := Fp_pos (w (n + 1 + i) / x * (8 * (lap x (seq n) : ℝ) + 1))
      calc seq (n + 1 + i + 1) ≤ Fp (w (n + 1 + i) / x * (8 * (lap x (seq n) : ℝ) + 1)) * seq (n + 1 + i) := h2
        _ ≤ Fp (w (n + 1 + i) / x * (8 * (lap x (seq n) : ℝ) + 1)) *
            ((∏ s ∈ Finset.Ico (n + 1) (n + 1 + i), Fp (w s / x * (8 * (lap x (seq n) : ℝ) + 1))) * seq (n + 1)) := by
              gcongr
        _ = _ := by ring
  have hk := hiter (k - (n + 1)) (fun s a b => hws s (by omega) (by omega)) (fun s a b => hlap1 s (by omega) (by omega))
  rw [show n + 1 + (k - (n + 1)) = k by omega] at hk
  have hj0 : (0 : ℝ) ≤ (lap x (seq n) : ℝ) := by exact_mod_cast setter_lap_nonneg hpos h0 hmv hx
  have hden : 0 < 8 * (lap x (seq n) : ℝ) + 1 := by linarith
  have : (8 * (lap x (seq n) : ℝ) + 7) / (8 * (lap x (seq n) : ℝ) + 1) * seq (n + 1) <
      (∏ s ∈ Finset.Ico (n + 1) k, Fp (w s / x * (8 * (lap x (seq n) : ℝ) + 1))) * seq (n + 1) :=
    lt_of_lt_of_le hret hk
  exact lt_of_mul_lt_mul_right this hap.le

#print axioms budget_product

/-- `1 + ∑ a ≤ ∏ (1 + a)` for non-negative `a` (Bernoulli, by induction on the finite set). -/
theorem one_add_sum_le_prod {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    1 + ∑ i ∈ S, a i ≤ ∏ i ∈ S, (1 + a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hS : ∀ j ∈ S, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have h1 := ih hS
    have hai := ha i (Finset.mem_insert_self i S)
    have hsum : 0 ≤ ∑ j ∈ S, a j := Finset.sum_nonneg hS
    nlinarith

#print axioms one_add_sum_le_prod

/-! ## (5) The window law: four consecutive moves have three distinct setters, and what a return of the slowest needs -/

/-- **Any four consecutive moves have at least three distinct setters** [L].  Setters never repeat in a row
(`setter_not_twice_in_row`); if only two values occurred they would alternate `x y x y`, which `Ladder.no_xyxy`
(`triple_law` twice) forbids.  No ordering of the readings and no base `m` is used. -/
theorem four_consecutive_distinct {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n : ℕ} {a b c d : ℝ} (ha : IsSetterAt E seq n a)
    (hb : IsSetterAt E seq (n + 1) b) (hc : IsSetterAt E seq (n + 2) c) (hd : IsSetterAt E seq (n + 3) d) :
    2 < ({a, b, c, d} : Finset ℝ).card := by
  by_contra hcon
  have hcard : ({a, b, c, d} : Finset ℝ).card ≤ 2 := by omega
  have hab : a ≠ b := fun h => setter_not_twice_in_row hpos ha (h ▸ hb)
  have hbc : b ≠ c := fun h => setter_not_twice_in_row hpos hb (h ▸ hc)
  have hcd : c ≠ d := fun h => setter_not_twice_in_row hpos hc (h ▸ hd)
  have e02 : a = c := eq_of_card_le_two hcard (by simp) (by simp) (by simp) hab hbc
  have e13 : b = d := eq_of_card_le_two hcard (by simp) (by simp) (by simp) hbc hcd
  subst e02
  subst e13
  exact no_xyxy hpos h0 hmv ha hb hc hd

#print axioms four_consecutive_distinct

/-- **A return of a reading that is at most every intermediate setter has at least three distinct readings among
its intermediate setters** [L] (`return_after_four` gives four moves, `four_consecutive_distinct` three values among
the first four).  This is the part of "the readings in between are spread" that the cascade chain proves with the laws of
this folder; the fourth reading is the owed step below. -/
theorem return_three_distinct {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hx : IsSetterAt E seq n x)
    (hw : InWay x (seq k)) (hge : ∀ s, n < s → s < k → ∀ y, IsSetterAt E seq s y → x ≤ y)
    (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    2 < ((Finset.Ico (n + 1) k).image w).card := by
  have h5 := return_after_four hpos hmv hnk hx hw hge
  have h4 := four_consecutive_distinct hpos h0 hmv (hws (n + 1) (by omega) (by omega))
    (hws (n + 2) (by omega) (by omega)) (hws (n + 3) (by omega) (by omega)) (hws (n + 4) (by omega) (by omega))
  refine lt_of_lt_of_le h4 (Finset.card_le_card ?_)
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  simp only [Finset.mem_image, Finset.mem_Ico]
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨n + 1, ⟨le_rfl, by omega⟩, rfl⟩
  · exact ⟨n + 2, ⟨by omega, by omega⟩, rfl⟩
  · exact ⟨n + 3, ⟨by omega, by omega⟩, rfl⟩
  · exact ⟨n + 4, ⟨by omega, by omega⟩, rfl⟩

#print axioms return_three_distinct

/-- **OWED, supported by exact data [OBS], not proved**: *the four-distinct law.*  In the cascade from `1/(8m)` with every
reading at least `m`, if `a` is at most every reading and sets the move at `n`, and is in the way at `seq k` with `a`
not in the way at any `seq s`, `n < s < k` (a first return), then the intermediate setters take at least FOUR distinct
values.  Data (`experiments/n8/ladder5_v2.out`, line 'FOUR-DISTINCT form', exactly this statement: the slowest SET at `n`, first later
state with it in the way): 0 violations in every population; `K = 5` (`Q = 12, M = 10`: 303 returns; `Q = 8, M = 14`: 286; `Q = 6, M = 30`: 5329), all with
exactly 4 distinct values; `K = 6` (`Q = 6, M = 10`): 4269 returns, 154 with 4 values, 4115 with 5; `K = 3, 4`: no return of the slowest.
So the form is 'at least four', not 'all others' (`K = 6`). The budget law alone does
not give it (`experiments/n8/ladder5_v2.out`, section 5: a word `v t u v` is budget-feasible), so a law of position
(zone shadowing) is needed; see the report. -/
-- STANDING: OWED
def FourDistinctLaw : Prop :=
  ∀ (E : Finset ℝ) (m : ℝ) (seq : ℕ → ℝ) (a : ℝ) (n k : ℕ),
    0 < m → (∀ d ∈ E, m ≤ d) → seq 0 = 1 / (8 * m) → (∀ i, IsMove E (seq i) (seq (i + 1))) →
    (∀ d ∈ E, a ≤ d) → IsSetterAt E seq n a → n < k → InWay a (seq k) →
    (∀ s, n < s → s < k → ¬ InWay a (seq s)) →
    ∀ w : ℕ → ℝ, (∀ s, n < s → s < k → IsSetterAt E seq s (w s)) →
      3 < ((Finset.Ico (n + 1) k).image w).card

/-- **Conditional [L]: with the four-distinct law, the slowest of four readings never returns** (`E.card ≤ 4`).  The
intermediate setters are not `a` (a setter is in the way), so they lie in `E.erase a`, of size at most `3`. -/
theorem slowest_of_four_never_returns (h : FourDistinctLaw) {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ}
    (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (h0 : seq 0 = 1 / (8 * m))
    (hmv : ∀ i, IsMove E (seq i) (seq (i + 1))) (hcard : E.card ≤ 4) (ha : ∀ d ∈ E, a ≤ d)
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) :
    ¬ InWay a (seq k) := by
  intro hw
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hex : ∀ s, n < s → s < k → ∃ y, IsSetterAt E seq s y :=
    fun s _ hs => setter_before_visit hmv hn.1 hw hs
  choose! w hw' using hex
  have h3 := h E m seq a n k hm hlow h0 hmv ha hn hnk hw hfirst w hw'
  have hsub : (Finset.Ico (n + 1) k).image w ⊆ E.erase a := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    have hs' := Finset.mem_Ico.mp hs
    have hset := hw' s (by omega) hs'.2
    refine Finset.mem_erase.mpr ⟨?_, hset.1⟩
    intro hva
    have := hset.2.1
    rw [hva] at this
    exact hfirst s (by omega) hs'.2 this
  have hE : (E.erase a).card ≤ 3 := by
    have := Finset.card_erase_of_mem hn.1
    omega
  have := Finset.card_le_card hsub
  omega

#print axioms slowest_of_four_never_returns

/-- **Conditional [L]: with the four-distinct law and five readings, the first return of the slowest passes through every
other reading.**  The intermediate setters lie in `E.erase a` (size at most `4`) and take at least four values, so their set
of values is exactly `E.erase a`.  Conditional on the OWED `FourDistinctLaw`; it states the shape of the segment between
a setting of the slowest and its first return at `E.card ≤ 5`, and proves nothing about existence of a lonely instant. -/
theorem five_first_return_all_others (h : FourDistinctLaw) {E : Finset ℝ} {m : ℝ} {seq : ℕ → ℝ} {a : ℝ} {n k : ℕ}
    (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (h0 : seq 0 = 1 / (8 * m))
    (hmv : ∀ i, IsMove E (seq i) (seq (i + 1))) (hcard : E.card ≤ 5) (ha : ∀ d ∈ E, a ≤ d)
    (hn : IsSetterAt E seq n a) (hnk : n < k) (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s))
    (hw : InWay a (seq k)) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    (Finset.Ico (n + 1) k).image w = E.erase a := by
  have h3 := h E m seq a n k hm hlow h0 hmv ha hn hnk hw hfirst w hws
  have hsub : (Finset.Ico (n + 1) k).image w ⊆ E.erase a := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    have hs' := Finset.mem_Ico.mp hs
    have hset := hws s (by omega) hs'.2
    refine Finset.mem_erase.mpr ⟨?_, hset.1⟩
    intro hva
    have := hset.2.1
    rw [hva] at this
    exact hfirst s (by omega) hs'.2 this
  have hE : (E.erase a).card ≤ 4 := by
    have := Finset.card_erase_of_mem hn.1
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

#print axioms five_first_return_all_others

end Ladder5

end Fresh
