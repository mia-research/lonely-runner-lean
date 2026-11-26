import Mathlib
import Fresh.Framework
import Fresh.Localisation

/-!
# The neighbourhood of the AP: a deviation displaces the isolation to a named instant (Task L)

Written 2026-10-07.  Imports Mathlib, `Fresh.Framework` and `Fresh.Localisation` (for `clear_of_window`,
`distInt_neg`, `distInt_le`).  Nothing is imported from the existing `LonelyRunner` repo.

This is a LOCAL displacement statement under rule 1.  It is not an existence argument for the conjecture and is not
offered as a route to it.  The radius on the deviations is a HYPOTHESIS of the local statement; it is not a bound on
anything the cascade does.

Setting.  Speeds `apV c e i = c + i + e i` (`i = 0 … 7`), the AP of gap 1 with deviation `e`, `|e n| ≤ ε`.
The named instant `apT e k` (same formulas as the existing file, stated here natively):
* interior subject `k = 1 … 6`: `1/(8 m)`, `m` the nearer of its two neighbour gaps;
* end subject `k = 0` (and `k = 7` mirrored), near gap `a`, far reading `f`: `1/(8 a)` if `f ≤ 7 a`, else the
  class-7 instant `49/(8 f)`.

The argument is SYMBOLIC in the offset `j = i - k`; no (subject, reading) pair is treated by its own lemma.
* Interior (`interior_clear`): the reading `δ = j + e_i - e_k` satisfies `m ≤ |δ| ≤ 7m`.  The lower bound is the
  definition of `m` for `|j| = 1` and `2 - 2ε ≥ 1 + 2ε` for `|j| ≥ 2`; the upper bound is `|j| + 2ε ≤ 6 + 2ε ≤ 7(1-2ε)`,
  which is exactly `ε ≤ 1/16`.  Then `δ/(8m)` lies in the window `[1/8, 7/8]` (or its negative).
* End, class 1 (`f ≤ 7a`): the same window, with `j = 7` given by the branch condition.
* End, class 7 (`f > 7a`): the reading `j` sits in the window `N = j - 1`; the two window inequalities are the exact
  identities `49 δ - (8j-7) f = 7(7-j) + 49 e_j - (8j-7) e_7 - (56-8j) e_0 ≥ 7(7-j) - 98 ε` and
  `(8j-1) f - 49 δ = 7(j-1) + (8j-1) e_7 - 49 e_j + (50-8j) e_0 ≥ 7(j-1) - 98 ε`, read for general `j`
  (`j = 1` uses the branch condition, `j = 7` is the far runner itself at exactly one eighth).

Results (grades in the report):
* `ap_isolated_of_le` : radius `ε ≤ 1/16` gives `IsolatedAt (apV c e) k (apT e k)` for every `k`.
* `ap_nbhd_isolated`  : the existing statement's hypothesis `|e n| ≤ 1/32`, as a corollary.
* `ap_isolation`, `apV_isArrangement` : `Isolation` and the arrangement property.
* `apT_displacement`, `apT_interior_displacement` : the named instant is within `2ε/7` of the ideal AP instant `1/8`
  (interior always; end runner in class 1) or `7/8` (end runner in class 7).
* The exception, understood (`cx_*`): at `ε = 1/15 > 1/16` the named instant of subject 1 FAILS at the pair
  `(1, 7)`: the six-gap reading `92/15` exceeds `7 d_min = 91/15` (the ratio condition at the subject's own `d_min`
  is what `ε ≤ 1/16` guarantees, and it is what breaks).  The isolation is not destroyed: it is displaced to
  `135/488`, where the cascade from `1/(8 d_min)` arrives (three moves, setters `92/15, 76/15, 61/15`; the moves
  were computed in exact rationals outside Lean, the isolation at `135/488` is proved here).  So `1/16` is the sharp
  radius for these named instants, and the `1/32` of the existing file is not needed.

Provenance.  `LRC/Spec/APNeighbourhoodN.lean` (existing repo): `apV`, `endT`, `apT` (formulas re-stated),
`clear_div` / `clear_R1_pos` / `clear_R1_neg` (here `clear_ahead`, `clear_behind`, `clear_classSeven`, re-proved from
`clear_of_window`), the 56 generated lemmas `c_i_j` and `ap_nbhd_readings` (here replaced by the three symbolic
lemmas `interior_clear`, `end_clear` and the mirror), `ap_nbhd_lonely` (here `ap_nbhd_isolated`), `apV_injective`,
`apV_pos`, `apT_pos`, `ap_nbhd_exists` (here `apV_isArrangement`, `apT_pos`, `ap_isolation`).  The existing proofs
were read; none was copied; the class-7 identities above were derived for this file.

No counting, covering, density, cap or move budget is used anywhere in this file.  No runner is stationary: every
statement is about speed differences; the arrangement lemma needs `ε < c`.
-/

open Classical

namespace Fresh.APNeighbourhood

open Fresh Fresh.Localisation

/-! ## Definitions -/

/-- The deviated AP: speed `c + i + e i`. -/
noncomputable def apV (c : ℝ) (e : ℕ → ℝ) (i : Fin 8) : ℝ := c + ((i : ℕ) : ℝ) + e (i : ℕ)

/-- An end runner's instant: its own `1/(8 a)` (class 1), or the class-7 instant of its far reading `f`. -/
noncomputable def endT (a f : ℝ) : ℝ := if f ≤ 7 * a then 1 / (8 * a) else 49 / (8 * f)

/-- The named instant of subject `k`. -/
noncomputable def apT (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then endT (1 + e 1 - e 0) (7 + e 7 - e 0)
  else if k = 7 then endT (1 + e 7 - e 6) (7 + e 7 - e 0)
  else 1 / (8 * min (1 + e (k + 1) - e k) (1 + e k - e (k - 1)))

/-! ## Windows -/

/-- A reading between `m` and `7m` is clear at `1/(8m)` (window `N = 0`). -/
theorem clear_ahead {δ m : ℝ} (hm : 0 < m) (h1 : m ≤ δ) (h2 : δ ≤ 7 * m) :
    (1 / 8 : ℝ) ≤ distInt (δ * (1 / (8 * m))) := by
  have h8 : 0 < 8 * m := by positivity
  have hx : δ * (1 / (8 * m)) = δ / (8 * m) := by ring
  rw [hx]
  apply clear_of_window 0
  · rw [le_div_iff₀ h8]; push_cast; linarith
  · rw [div_le_iff₀ h8]; push_cast; linarith

#print axioms clear_ahead

/-- A reading between `-7m` and `-m` is clear at `1/(8m)`. -/
theorem clear_behind {δ m : ℝ} (hm : 0 < m) (h1 : m ≤ -δ) (h2 : -δ ≤ 7 * m) :
    (1 / 8 : ℝ) ≤ distInt (δ * (1 / (8 * m))) := by
  rw [← distInt_neg, ← neg_mul]
  exact clear_ahead hm h1 h2

#print axioms clear_behind

/-- The class-7 window: `(8N+1) f ≤ 49 δ ≤ (8N+7) f` puts `δ · 49/(8f)` in `[N + 1/8, N + 7/8]`. -/
theorem clear_classSeven {δ f : ℝ} (N : ℤ) (hf : 0 < f) (h1 : (8 * (N : ℝ) + 1) * f ≤ 49 * δ)
    (h2 : 49 * δ ≤ (8 * (N : ℝ) + 7) * f) : (1 / 8 : ℝ) ≤ distInt (δ * (49 / (8 * f))) := by
  have h8 : 0 < 8 * f := by positivity
  have hx : δ * (49 / (8 * f)) = (49 * δ) / (8 * f) := by ring
  rw [hx]
  apply clear_of_window N
  · rw [le_div_iff₀ h8]; linarith
  · rw [div_le_iff₀ h8]; linarith

#print axioms clear_classSeven

/-! ## The symbolic reading lemmas -/

/-- Bounds `-ε ≤ e n ≤ ε` from the hypothesis. -/
theorem bnd {e : ℕ → ℝ} {ε : ℝ} (he : ∀ n, n < 8 → |e n| ≤ ε) {n : ℕ} (hn : n < 8) :
    -ε ≤ e n ∧ e n ≤ ε := abs_le.mp (he n hn)

#print axioms bnd

/-- **Interior subject, every reading, one argument in the offset `i - k`.**  With `m` the nearer neighbour gap, the
reading `δ = (i - k) + e_i - e_k` satisfies `m ≤ |δ| ≤ 7 m` because `|i - k| ≤ 6` and `ε ≤ 1/16`. -/
theorem interior_clear (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (i : ℕ) (hi : i ≤ 7) (hik : i ≠ k) :
    (1 / 8 : ℝ) ≤ distInt (((i : ℝ) - k + e i - e k) *
      (1 / (8 * min (1 + e (k + 1) - e k) (1 + e k - e (k - 1))))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hsub : k' + 1 - 1 = k' := by omega
  rw [hsub]
  obtain ⟨a0, a1⟩ := bnd he (n := k') (by omega)
  obtain ⟨b0, b1⟩ := bnd he (n := k' + 1) (by omega)
  obtain ⟨c0, c1⟩ := bnd he (n := k' + 1 + 1) (by omega)
  obtain ⟨d0, d1⟩ := bnd he (n := i) (by omega)
  set m := min (1 + e (k' + 1 + 1) - e (k' + 1)) (1 + e (k' + 1) - e k') with hmdef
  have hmR : m ≤ 1 + e (k' + 1 + 1) - e (k' + 1) := min_le_left _ _
  have hmL : m ≤ 1 + e (k' + 1) - e k' := min_le_right _ _
  have hmlo : 1 - 2 * ε ≤ m := le_min (by linarith) (by linarith)
  have hmpos : 0 < m := by linarith
  have hk'R : ((k' : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show k' ≤ 5 by omega)
  have hiR : ((i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
  push_cast
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · -- a reading behind: `-δ = (k - i) + e_k - e_i`, with `1 ≤ k - i ≤ 6`
    apply clear_behind hmpos
    · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with heq | hlt'
      · subst heq; linarith
      · have : ((i : ℕ) : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast hlt'
        linarith
    · linarith
  · -- a reading ahead: `δ = (i - k) + e_i - e_k`, with `1 ≤ i - k ≤ 6`
    apply clear_ahead hmpos
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with heq | hlt'
      · subst heq; push_cast; linarith
      · have : (k' : ℝ) + 3 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt'
        linarith
    · linarith

#print axioms interior_clear

/-- **End subject `0`, every reading `j = 1 … 7`, one argument in `j`.**  Class 1 (`f ≤ 7a`): the window `[a, 7a]`.
Class 7 (`f > 7a`): window `N = j - 1`, by the two identities of the module docstring. -/
theorem end_clear (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (j : ℕ) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) :
    (1 / 8 : ℝ) ≤ distInt (((j : ℝ) + e j - e 0) * endT (1 + e 1 - e 0) (7 + e 7 - e 0)) := by
  obtain ⟨z0, z1⟩ := bnd he (n := 0) (by omega)
  obtain ⟨o0, o1⟩ := bnd he (n := 1) (by omega)
  obtain ⟨s0, s1⟩ := bnd he (n := 7) (by omega)
  obtain ⟨j0, j1⟩ := bnd he (n := j) (by omega)
  have hjR1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjR7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
  unfold endT
  split_ifs with hc
  · -- class 1
    apply clear_ahead (by linarith)
    · rcases eq_or_lt_of_le hj1 with heq | hlt
      · subst heq; push_cast; linarith
      · have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlt
        linarith
    · rcases eq_or_lt_of_le hj7 with heq | hlt
      · subst heq; push_cast; linarith
      · have : (j : ℝ) ≤ 6 := by exact_mod_cast (Nat.lt_succ_iff.mp hlt)
        linarith
  · -- class 7
    push Not at hc
    have hf : 0 < 7 + e 7 - e 0 := by linarith
    apply clear_classSeven ((j : ℤ) - 1) hf
    · push_cast
      rcases eq_or_lt_of_le hj7 with heq | hlt
      · subst heq; push_cast; linarith
      · have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (Nat.lt_succ_iff.mp hlt)
        -- `49 δ - (8j-7) f = 7(7-j) + 49 e_j - (8j-7) e_7 - (56-8j) e_0 ≥ 7(7-j) - 98 ε`
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 * j - 7 by linarith) (show 0 ≤ ε - e 7 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 56 - 8 * j by linarith) (show 0 ≤ ε + e 0 by linarith)]
    · push_cast
      rcases eq_or_lt_of_le hj1 with heq | hlt
      · subst heq; push_cast; linarith
      · have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlt
        rcases eq_or_lt_of_le hj7 with heq | hlt7
        · subst heq; push_cast; linarith
        · have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (Nat.lt_succ_iff.mp hlt7)
          -- `(8j-1) f - 49 δ = 7(j-1) + (8j-1) e_7 - 49 e_j + (50-8j) e_0 ≥ 7(j-1) - 98 ε`
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 * j - 1 by linarith) (show 0 ≤ ε + e 7 by linarith),
            mul_nonneg (show (0 : ℝ) ≤ 50 - 8 * j by linarith) (show 0 ≤ ε + e 0 by linarith)]

#print axioms end_clear

/-! ## The mirror: subject 7 is subject 0 of the reflected deviation -/

/-- The reflected deviation `e' n = -e (7 - n)`. -/
noncomputable def mirror (e : ℕ → ℝ) : ℕ → ℝ := fun n => -e (7 - n)

theorem mirror_bound {e : ℕ → ℝ} {ε : ℝ} (he : ∀ n, n < 8 → |e n| ≤ ε) :
    ∀ n, n < 8 → |mirror e n| ≤ ε := by
  intro n _
  simp only [mirror, abs_neg]
  exact he _ (by omega)

#print axioms mirror_bound

/-- Subject `7`, every reading `i = 0 … 6`: the reflected reading is the end-runner reading of `mirror e`. -/
theorem end_clear_seven (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (i : ℕ) (hi : i < 7) :
    (1 / 8 : ℝ) ≤ distInt (((i : ℝ) - 7 + e i - e 7) * endT (1 + e 7 - e 6) (7 + e 7 - e 0)) := by
  have h := end_clear (mirror e) ε (mirror_bound he) hε (7 - i) (by omega) (by omega)
  have hT : endT (1 + mirror e 1 - mirror e 0) (7 + mirror e 7 - mirror e 0) =
      endT (1 + e 7 - e 6) (7 + e 7 - e 0) := by
    simp only [mirror]; norm_num; ring_nf
  have hR : (((7 - i : ℕ) : ℝ) + mirror e (7 - i) - mirror e 0) = -((i : ℝ) - 7 + e i - e 7) := by
    simp only [mirror]
    rw [Nat.sub_sub_self (by omega : i ≤ 7), Nat.cast_sub (by omega : i ≤ 7)]
    push_cast; ring
  rw [hT, hR, neg_mul, distInt_neg] at h
  exact h

#print axioms end_clear_seven

/-! ## The theorem -/

/-- **Every runner of the deviated AP is isolated at its named instant, for every deviation of radius `≤ 1/16`.** -/
theorem ap_isolated_of_le (c : ℝ) (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (k : Fin 8) : IsolatedAt (apV c e) k (apT e k) := by
  intro i hik
  have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
  have hd : apV c e i - apV c e k = ((i : ℕ) : ℝ) - ((k : ℕ) : ℝ) + e i - e k := by
    unfold apV; ring
  rw [hd]
  have hi7 : (i : ℕ) ≤ 7 := by omega
  by_cases h0 : (k : ℕ) = 0
  · have hT : apT e k = endT (1 + e 1 - e 0) (7 + e 7 - e 0) := by simp [apT, h0]
    rw [hT, h0]
    have := end_clear e ε he hε i (by omega) hi7
    simpa using this
  · by_cases h7 : (k : ℕ) = 7
    · have hT : apT e k = endT (1 + e 7 - e 6) (7 + e 7 - e 0) := by simp [apT, h7]
      rw [hT, h7]
      have := end_clear_seven e ε he hε i (by omega)
      simpa using this
    · have hT : apT e k = 1 / (8 * min (1 + e (k + 1) - e k) (1 + e k - e (k - 1))) := by
        simp [apT, h0, h7]
      rw [hT]
      exact interior_clear e ε he hε k (by omega) (by omega) i hi7 hik'

#print axioms ap_isolated_of_le

/-- **The existing statement's hypothesis (`|e n| ≤ 1/32`), as a corollary.** -/
theorem ap_nbhd_isolated (c : ℝ) (e : ℕ → ℝ) (he : ∀ n, n < 8 → |e n| ≤ 1 / 32) (k : Fin 8) :
    IsolatedAt (apV c e) k (apT e k) :=
  ap_isolated_of_le c e (1 / 32) he (by norm_num) k

#print axioms ap_nbhd_isolated

/-! ## Positivity, arrangement, isolation -/

theorem endT_pos {a f : ℝ} (ha : 0 < a) (hf : 0 < f) : 0 < endT a f := by
  unfold endT; split_ifs <;> positivity

#print axioms endT_pos

theorem apT_pos (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16) (k : Fin 8) :
    0 < apT e k := by
  have hb := fun n (hn : n < 8) => bnd he hn
  obtain ⟨z0, z1⟩ := hb 0 (by omega)
  obtain ⟨o0, o1⟩ := hb 1 (by omega)
  obtain ⟨x0, x1⟩ := hb 6 (by omega)
  obtain ⟨s0, s1⟩ := hb 7 (by omega)
  unfold apT
  split_ifs with h0 h7
  · exact endT_pos (by linarith) (by linarith)
  · exact endT_pos (by linarith) (by linarith)
  · obtain ⟨p0, p1⟩ := hb ((k : ℕ) + 1) (by omega)
    obtain ⟨q0, q1⟩ := hb (k : ℕ) (by omega)
    obtain ⟨r0, r1⟩ := hb ((k : ℕ) - 1) (by omega)
    have : 0 < min (1 + e ((k : ℕ) + 1) - e k) (1 + e k - e ((k : ℕ) - 1)) :=
      lt_min (by linarith) (by linarith)
    positivity

#print axioms apT_pos

/-- The deviated AP is an arrangement (all speeds positive, pairwise distinct) when `ε < c`. -/
theorem apV_isArrangement (c : ℝ) (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (hc : ε < c) : IsArrangement (apV c e) := by
  constructor
  · intro i
    obtain ⟨b0, _⟩ := bnd he (n := (i : ℕ)) i.isLt
    have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    unfold apV; linarith
  · intro i j h
    unfold apV at h
    obtain ⟨i0, i1⟩ := bnd he (n := (i : ℕ)) i.isLt
    obtain ⟨j0, j1⟩ := bnd he (n := (j : ℕ)) j.isLt
    by_contra hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h' => hne (Fin.ext h')
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
      linarith
    · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt
      linarith

#print axioms apV_isArrangement

/-- **Isolation for every subject** of every arrangement within radius `1/16` of the AP. -/
theorem ap_isolation (c : ℝ) (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (k : Fin 8) : Isolation (apV c e) k :=
  ⟨apT e k, apT_pos e ε he hε k, ap_isolated_of_le c e ε he hε k⟩

#print axioms ap_isolation

/-! ## The displacement is small: the named instant is within `2ε/7` of an ideal AP instant -/

/-- Class 1: `|1/(8m) - 1/8| ≤ 2ε/7` when `|m - 1| ≤ 2ε`, `ε ≤ 1/16`. -/
theorem disp_one {m ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) (h1 : 1 - 2 * ε ≤ m) (h2 : m ≤ 1 + 2 * ε) :
    |1 / (8 * m) - 1 / 8| ≤ 2 * ε / 7 := by
  have hm : 0 < m := by linarith
  have key : 1 / (8 * m) - 1 / 8 = (1 - m) / (8 * m) := by field_simp
  rw [key, abs_le]
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

#print axioms disp_one

/-- Class 7: `|49/(8f) - 7/8| ≤ 2ε/7` when `|f - 7| ≤ 2ε`, `ε ≤ 1/16`. -/
theorem disp_seven {f ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) (h1 : 7 - 2 * ε ≤ f) (h2 : f ≤ 7 + 2 * ε) :
    |49 / (8 * f) - 7 / 8| ≤ 2 * ε / 7 := by
  have hf : 0 < f := by linarith
  have key : 49 / (8 * f) - 7 / 8 = (49 - 7 * f) / (8 * f) := by field_simp
  rw [key, abs_le]
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

#print axioms disp_seven

/-- **Interior subjects: the isolation is displaced from the AP instant `1/8` by at most `2ε/7`.** -/
theorem apT_interior_displacement (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16)
    (k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) : |apT e k - 1 / 8| ≤ 2 * ε / 7 := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (he 0 (by omega))
  obtain ⟨p0, p1⟩ := bnd he (n := k + 1) (by omega)
  obtain ⟨q0, q1⟩ := bnd he (n := k) (by omega)
  obtain ⟨r0, r1⟩ := bnd he (n := k - 1) (by omega)
  have hT : apT e k = 1 / (8 * min (1 + e (k + 1) - e k) (1 + e k - e (k - 1))) := by
    simp [apT, show k ≠ 0 by omega, show k ≠ 7 by omega]
  rw [hT]
  apply disp_one hε0 hε
  · exact le_min (by linarith) (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

#print axioms apT_interior_displacement

/-- **Every subject: the named instant is within `2ε/7` of the AP instant `1/8` or of its mirror `7/8`** (the
second only for an end runner in class 7). -/
theorem apT_displacement (e : ℕ → ℝ) (ε : ℝ) (he : ∀ n, n < 8 → |e n| ≤ ε) (hε : ε ≤ 1 / 16) (k : Fin 8) :
    |apT e k - 1 / 8| ≤ 2 * ε / 7 ∨ |apT e k - 7 / 8| ≤ 2 * ε / 7 := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (he 0 (by omega))
  obtain ⟨z0, z1⟩ := bnd he (n := 0) (by omega)
  obtain ⟨o0, o1⟩ := bnd he (n := 1) (by omega)
  obtain ⟨x0, x1⟩ := bnd he (n := 6) (by omega)
  obtain ⟨s0, s1⟩ := bnd he (n := 7) (by omega)
  by_cases h0 : (k : ℕ) = 0
  · have hT : apT e k = endT (1 + e 1 - e 0) (7 + e 7 - e 0) := by simp [apT, h0]
    rw [hT]; unfold endT
    split_ifs
    · left; exact disp_one hε0 hε (by linarith) (by linarith)
    · right; exact disp_seven hε0 hε (by linarith) (by linarith)
  · by_cases h7 : (k : ℕ) = 7
    · have hT : apT e k = endT (1 + e 7 - e 6) (7 + e 7 - e 0) := by simp [apT, h7]
      rw [hT]; unfold endT
      split_ifs
      · left; exact disp_one hε0 hε (by linarith) (by linarith)
      · right; exact disp_seven hε0 hε (by linarith) (by linarith)
    · left; exact apT_interior_displacement e ε he hε k (by omega) (by omega)

#print axioms apT_displacement

/-! ## The exception, understood: radius `1/16` is sharp for the named instants

At `η = 1/15` put `e_0 = η`, `e_1 = -η`, `e_7 = η`, all other `e_n = 0`.  Subject 1 has `d_min = 1 - 2η = 13/15`
(its gap to runner 0) and the reading of runner 7 is `6 + 2η = 92/15 > 7 · 13/15 = 91/15`: the far reading leaves the
window `[m, 7m]`, so at `1/(8 d_min) = 15/104` it reads `23/26`, within `3/26 < 1/8` of a lap.  The pair that forces
`ε ≤ 1/16` is `(1, 7)` (mirror: `(6, 0)`): `6 + 2ε ≤ 7(1 - 2ε)` is exactly `ε ≤ 1/16`.  The isolation is displaced, not
destroyed: at `135/488` (where the cascade from `15/104` fixes, after setters `92/15`, `76/15`, `61/15`) subject 1 is
isolated. -/

/-- The counterexample deviation. -/
noncomputable def cxE : ℕ → ℝ := fun n => if n = 0 then 1 / 15 else if n = 1 then -(1 / 15) else
  if n = 7 then 1 / 15 else 0

theorem cx_bound : ∀ n, n < 8 → |cxE n| ≤ 1 / 15 := by
  intro n _
  unfold cxE
  split_ifs <;> norm_num

#print axioms cx_bound

theorem cx_apT : apT cxE 1 = 15 / 104 := by
  have hmin : min (1 + cxE (1 + 1) - cxE 1) (1 + cxE 1 - cxE (1 - 1)) = 13 / 15 := by
    norm_num [cxE]
  simp only [apT, show (1 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≠ 7 by omega, if_false]
  rw [hmin]; norm_num

#print axioms cx_apT

/-- **The named instant fails beyond radius `1/16`**: at `|e n| ≤ 1/15`, subject 1 is not isolated at `apT e 1`,
because runner 7 is within `3/26` of a lap there. -/
theorem cx_not_isolated (c : ℝ) : ¬ IsolatedAt (apV c cxE) 1 (apT cxE 1) := by
  intro h
  have h7 := h 7 (by decide)
  rw [cx_apT] at h7
  have hval : (apV c cxE 7 - apV c cxE 1) * (15 / 104) = 23 / 26 := by
    simp only [apV, cxE]; norm_num; ring
  rw [hval] at h7
  have := distInt_le (23 / 26 : ℝ) 1
  norm_num at this
  linarith

#print axioms cx_not_isolated

/-- **Displaced, not destroyed**: the same arrangement isolates subject 1 at `135/488`. -/
theorem cx_isolated_displaced (c : ℝ) : IsolatedAt (apV c cxE) 1 (135 / 488) := by
  intro i hi
  fin_cases i
  all_goals try exact absurd rfl hi
  all_goals simp only [apV, cxE]; norm_num
  all_goals
    first
      | exact clear_of_window (-1) (by push_cast; linarith) (by push_cast; linarith)
      | exact clear_of_window 0 (by push_cast; linarith) (by push_cast; linarith)
      | exact clear_of_window 1 (by push_cast; linarith) (by push_cast; linarith)

#print axioms cx_isolated_displaced

end Fresh.APNeighbourhood
