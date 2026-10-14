import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Localisation
import Fresh.LonelyCells
import Fresh.PairLaw

/-!
# The grid pair law, with the interval (Task Q)

Written 2026-10-07.  Imports Mathlib and the Fresh modules `Framework`, `Cascade`, `Localisation`, `LonelyCells`,
`PairLaw`; nothing from the existing `LonelyRunner` repo.  Exact reals; every reading positive (no runner stationary).

This is a LOCAL displacement statement (rule 1).  The radius `η` is a hypothesis on RESCALED positions at the two class
instants (where each runner stands relative to its grid position `o_j a/8`); it is not a bound on the cascade, on moves,
or on anything the cascade does.  No counting, covering, density, cap or move budget appears in any statement or step.

Setting.  Readings `d : ι → ℝ` on a finite set `S`, integer offsets `o : ι → ℤ` (grid positions), a complete nonzero
residue system mod 8 (`setting_of_complete`).  Class `a` odd; opener `A` (`o_A ≡ a`), closer `B` (`o_B ≡ −a`).  The
class instant through runner `j` is `cI d o j a = o_j a/(8 d_j)`: `u_a = cI A`, `w_a = cI B`.  Mirror `b ≡ −a`:
opener `B`, closer `A` (`setting_mirror`).

Results (all [L]).
* (1) `opening_at_u`: `8 n_A + 1 = o_A a`, `d_A u_a = n_A + 1/8`.  `entry_at_w`: `8 n_B + 7 = o_B a`,
  `d_B w_a = n_B + 7/8`.  Integrality from `a² ≡ 1 (mod 8)` (`odd_sq_modEq`, symbolic).
* (2) `u_le_w_iff`: `u_a ≤ w_a ↔ o_A d_B ≤ o_B d_A`.  `pair_cover`: one of the pair's conditions holds; both iff
  `o_A d_B = o_B d_A` (the touch).
* (3) `grid_interval_lonely`: `ClassHyp` with `η ≤ 1/8` ⇒ `[u_a, w_a]` lonely.  Each runner stays in ONE window
  `⌊o_j a/8⌋`, because its position is monotone in `t` and is in that window at both ends; interior runners have
  `o_j a mod 8 ∈ [2, 6]` (`interior_res`, symbolic: residue 0, 1, 7 would force `o_j ≡ 0, a, −a`).  The opener and
  closer need: `d_A w_a ≤ o_A a/8 + 3/4` (`A` not past its entry at `w`), `o_B a/8 − 3/4 ≤ d_B u_a` (`B` past its
  opening at `u`), i.e. `d_A (w − u) ≤ 3/4` and `d_B (w − u) ≤ 3/4`.  `grid_interval_lonely_window`: the exact
  per-runner window form.  `grid_interval_isCell`: with `a, o_A > 0` and `o_A d_B ≤ o_B d_A`, a maximal cell, opener
  `A` at lap `n_A`, closer `B` at lap `n_B`; `grid_interval_width`.  `grid_pair_law`: one class of each mirror pair
  gives a cell (hypothesis needed only for the class whose ratio condition holds).  `grid_instant_lonely`: the
  record's left-end form.  `eta_sharp`: `1/8` cannot be raised.  `drift_le`: the hypothesis bounds the drift
  `d_j (w − u) ≤ 2η`.
* (4) Exceptions.  `ap_case`: `o = (1..7)` gives `PairLaw.uA`, `PairLaw.wA`.  `ap_exception_eta`: the AP exception
  (`PairLaw.cxD`, class 7, runner 2) is exactly the failure of `ClassHyp` for runner 2 at `w_7`, at the same threshold
  `ρ = 1/22`.  With a large offset `o = (1, 2, 3, 4, 5, 8m + 6, 7)`: `F1_interval_fails` (the class interval contains a
  lap-line instant of runner 6 for `ρ ≥ 3/(28m + 24)`, while `F1_instant_lonely` keeps the instant for every `m`),
  `F1_displaced_cell` (closer changes from runner 1 to runner 6), `F2_both_instants_fail` (neither class instant of
  the pair `(1, 7)` is lonely, though `|d_j − o_j| ≤ ρ`), `F2_example_cell`, `F2_example_cascade` (the cascade from
  `u_7` makes one move, to runner 6's opening, and fixes).  The naive radius `|d_j − o_j g| ≤ ρ g` is the wrong
  theory for grids: its thresholds decay like `1/m` with the offset; the drift is proportional to the offset.

Provenance.  Existing repo `LRC/Spec/GridPairLawN.lean`: `clear_interior`, `clear_leaving`, `clear_entering` (here
replaced by the single window `⌊o_j a/8⌋` and `Localisation.clear_of_window`), `grid_pair_law` (here
`grid_instant_lonely` and `grid_pair_law`, the latter now a CELL on the interval), `grid_class_clear` (its per-reading
conditions are the instant case of `ClassHyp`; several readings per edge not treated here).  `GridPairN.grid_pair`
(reflection to the partner instant `((8−a)/a) t`) read; its partner instant is `cI B b` here.  `GridClassN.gridTp`
read for the class rule; not reused.  The existing proofs were read and understood; none was copied.  The interval,
the cell, the residue lemmas, the window form, the drift law and all exceptions are new here.
-/

open Classical

namespace Fresh.GridPairLaw

open Fresh Fresh.Localisation Fresh.LonelyCells

/-! ## Residues mod 8, symbolic -/

/-- An odd square is `1 mod 8`. -/
theorem odd_sq_modEq {a : ℤ} (ha : a % 2 = 1) : a * a ≡ 1 [ZMOD 8] := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
  obtain ⟨q, hq⟩ := Int.even_mul_succ_self m
  have e : (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
  rw [e, hq, Int.ModEq]
  omega

#print axioms odd_sq_modEq

/-- `o a ≡ 1` forces `o ≡ a` (multiply by `a`, use `a² ≡ 1`). -/
theorem eq_of_res_one {o a : ℤ} (ha : a % 2 = 1) (h : o * a ≡ 1 [ZMOD 8]) : o ≡ a [ZMOD 8] := by
  have h1 : o * (a * a) ≡ o * 1 [ZMOD 8] := (odd_sq_modEq ha).mul_left o
  have h2 : (o * a) * a ≡ 1 * a [ZMOD 8] := h.mul_right a
  rw [mul_one] at h1; rw [one_mul, mul_assoc] at h2
  exact h1.symm.trans h2

#print axioms eq_of_res_one

/-- `o ≡ a` gives `o a ≡ 1`. -/
theorem res_one_of_eq {o a : ℤ} (ha : a % 2 = 1) (h : o ≡ a [ZMOD 8]) : o * a ≡ 1 [ZMOD 8] :=
  (h.mul_right a).trans (odd_sq_modEq ha)

#print axioms res_one_of_eq

/-- `o ≡ −a` gives `o a ≡ −1`. -/
theorem res_seven_of_eq {o a : ℤ} (ha : a % 2 = 1) (h : o ≡ -a [ZMOD 8]) : o * a ≡ -1 [ZMOD 8] := by
  have h1 := h.mul_right a
  rw [neg_mul] at h1
  exact h1.trans (odd_sq_modEq ha).neg

#print axioms res_seven_of_eq

/-- `o a ≡ −1` forces `o ≡ −a`. -/
theorem eq_of_res_seven {o a : ℤ} (ha : a % 2 = 1) (h : o * a ≡ -1 [ZMOD 8]) : o ≡ -a [ZMOD 8] := by
  have h' : (-o) * a ≡ 1 [ZMOD 8] := by
    have := h.neg; rwa [neg_neg, ← neg_mul] at this
  have := (eq_of_res_one ha h').neg
  rwa [neg_neg] at this

#print axioms eq_of_res_seven

/-- `8 ∣ o a` with `a` odd forces `8 ∣ o`. -/
theorem dvd_of_res_zero {o a : ℤ} (ha : a % 2 = 1) (h : o * a ≡ 0 [ZMOD 8]) : o ≡ 0 [ZMOD 8] := by
  have h1 : o * (a * a) ≡ o * 1 [ZMOD 8] := (odd_sq_modEq ha).mul_left o
  have h2 : (o * a) * a ≡ 0 * a [ZMOD 8] := h.mul_right a
  rw [mul_one] at h1; rw [zero_mul, mul_assoc] at h2
  exact h1.symm.trans h2

#print axioms dvd_of_res_zero

/-- **Interior residue** [L]: if `o` is not `0`, `a` or `−a` mod 8 (`a` odd), then `o a mod 8 ∈ [2, 6]`. -/
theorem interior_res {o a : ℤ} (ha : a % 2 = 1) (h0 : ¬ o ≡ 0 [ZMOD 8]) (h1 : ¬ o ≡ a [ZMOD 8])
    (h7 : ¬ o ≡ -a [ZMOD 8]) : 2 ≤ (o * a) % 8 ∧ (o * a) % 8 ≤ 6 := by
  have r0 : (o * a) % 8 ≠ 0 := fun h => h0 (dvd_of_res_zero ha (by rw [Int.ModEq, h]; rfl))
  have r1 : (o * a) % 8 ≠ 1 := fun h => h1 (eq_of_res_one ha (by rw [Int.ModEq, h]; rfl))
  have r7 : (o * a) % 8 ≠ 7 := fun h => h7 (eq_of_res_seven ha (by rw [Int.ModEq, h]; rfl))
  have := Int.emod_nonneg (o * a) (by norm_num : (8 : ℤ) ≠ 0)
  have := Int.emod_lt_of_pos (o * a) (by norm_num : (0 : ℤ) < 8)
  omega

#print axioms interior_res

/-- The split `x = 8 (x / 8) + x % 8`, in the reals. -/
theorem split_real (x : ℤ) : (x : ℝ) = 8 * ((x / 8 : ℤ) : ℝ) + ((x % 8 : ℤ) : ℝ) := by
  have h := Int.mul_ediv_add_emod x 8
  have : (((8 * (x / 8) + x % 8 : ℤ)) : ℝ) = (x : ℝ) := by rw [h]
  push_cast at this
  linarith

#print axioms split_real

/-- A residue known mod 8 gives the exact remainder. -/
theorem emod_of_modEq {x r : ℤ} (h : x ≡ r [ZMOD 8]) (h0 : 0 ≤ r) (h8 : r < 8) : x % 8 = r := by
  rw [Int.ModEq] at h; rw [h]; exact Int.emod_eq_of_lt h0 h8

#print axioms emod_of_modEq


/-! ## Objects of the grid class -/

variable {ι : Type*}

/-- The disparity set of the readings indexed by `S`. -/
noncomputable def gds (S : Finset ι) (d : ι → ℝ) : Finset ℝ := S.image d

/-- The grid position of runner `j` at class `a`: `o_j a / 8` (laps). -/
noncomputable def gpos (o : ι → ℤ) (a : ℤ) (j : ι) : ℝ := (o j : ℝ) * a / 8

/-- The class instant through runner `j`: the instant at which runner `j` sits exactly on its grid position,
`o_j a / (8 d_j)`.  The opening of class `a` is `cI d o A a`, its entry `cI d o B a`. -/
noncomputable def cI (d : ι → ℝ) (o : ι → ℤ) (j : ι) (a : ℤ) : ℝ := (o j : ℝ) * a / (8 * d j)

/-- The window (lap) of runner `j` at class `a`: `⌊o_j a / 8⌋`. -/
def lap (o : ι → ℤ) (a : ℤ) (j : ι) : ℤ := (o j * a) / 8

theorem mul_cI (d : ι → ℝ) (o : ι → ℤ) (j : ι) (a : ℤ) (h : 0 < d j) : d j * cI d o j a = gpos o a j := by
  unfold cI gpos; field_simp

#print axioms mul_cI

theorem gpos_split (o : ι → ℤ) (a : ℤ) (j : ι) :
    gpos o a j = (lap o a j : ℝ) + (((o j * a) % 8 : ℤ) : ℝ) / 8 := by
  unfold gpos lap
  have := split_real (o j * a)
  push_cast at this ⊢
  linarith

#print axioms gpos_split

/-- The residue setting of class `a`: `A` (offset `≡ a`) and `B` (offset `≡ −a`) in `S`, every other runner of `S`
with offset not `≡ 0, a, −a (mod 8)` (true for a complete nonzero residue system, `setting_of_complete`), every reading
positive (no runner stationary), `a` odd. -/
-- STANDING: DEFINITION
def ClassSetting (S : Finset ι) (d : ι → ℝ) (o : ι → ℤ) (A B : ι) (a : ℤ) : Prop :=
  a % 2 = 1 ∧ A ∈ S ∧ B ∈ S ∧ o A ≡ a [ZMOD 8] ∧ o B ≡ -a [ZMOD 8] ∧
    (∀ j ∈ S, j ≠ A → j ≠ B → ¬ o j ≡ 0 [ZMOD 8] ∧ ¬ o j ≡ a [ZMOD 8] ∧ ¬ o j ≡ -a [ZMOD 8]) ∧
    (∀ j ∈ S, 0 < d j)

/-- **The local displacement hypothesis of class `a`, radius `η`** (rescaled positions, not a bound on the cascade):
every runner other than `A`, `B` is within `η` of its grid position `o_j a/8` at both class instants `u = cI A`,
`w = cI B`; the opener `A` has not advanced more than `3/4` past its grid position by `w`, and the closer `B` was not
more than `3/4` behind its grid position at `u`. -/
-- STANDING: DEFINITION
def ClassHyp (S : Finset ι) (d : ι → ℝ) (o : ι → ℤ) (A B : ι) (a : ℤ) (η : ℝ) : Prop :=
  (∀ j ∈ S, j ≠ A → j ≠ B →
      |d j * cI d o A a - gpos o a j| ≤ η ∧ |d j * cI d o B a - gpos o a j| ≤ η) ∧
    d A * cI d o B a ≤ gpos o a A + 3 / 4 ∧ gpos o a B - 3 / 4 ≤ d B * cI d o A a

/-- **Complete residues give the setting** [L]: if no offset in `S` is `≡ 0` and no two share a residue mod 8, and
`A`, `B` carry the residues `a`, `−a`, the setting holds. -/
theorem setting_of_complete {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} (ha : a % 2 = 1)
    (hA : A ∈ S) (hB : B ∈ S) (hoA : o A ≡ a [ZMOD 8]) (hoB : o B ≡ -a [ZMOD 8])
    (hnz : ∀ j ∈ S, ¬ o j ≡ 0 [ZMOD 8]) (hinj : ∀ i ∈ S, ∀ j ∈ S, o i ≡ o j [ZMOD 8] → i = j)
    (hpos : ∀ j ∈ S, 0 < d j) : ClassSetting S d o A B a := by
  refine ⟨ha, hA, hB, hoA, hoB, fun j hj hjA hjB => ⟨hnz j hj, fun h => hjA ?_, fun h => hjB ?_⟩, hpos⟩
  · exact hinj j hj A hA (h.trans hoA.symm)
  · exact hinj j hj B hB (h.trans hoB.symm)

#print axioms setting_of_complete

/-- **The mirror class swaps the roles** [L]: class `b` with `a + b ≡ 0 (mod 8)` has opener `B` and closer `A`. -/
theorem setting_mirror {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a b : ℤ}
    (h : ClassSetting S d o A B a) (hab : a + b ≡ 0 [ZMOD 8]) : ClassSetting S d o B A b := by
  obtain ⟨ha, hA, hB, hoA, hoB, hint, hpos⟩ := h
  have hb : b ≡ -a [ZMOD 8] := by
    have := hab.add_left (-a); simpa [add_comm, add_left_comm] using this
  have hb' : -b ≡ a [ZMOD 8] := by have := hb.neg; rwa [neg_neg] at this
  have hbodd : b % 2 = 1 := by
    have h8 : b % 8 = (-a) % 8 := hb
    omega
  refine ⟨hbodd, hB, hA, hoB.trans hb.symm, hoA.trans hb'.symm, fun j hj hjB hjA => ?_, hpos⟩
  obtain ⟨h0, h1, h7⟩ := hint j hj hjA hjB
  exact ⟨h0, fun h => h7 (h.trans hb), fun h => h1 (h.trans hb')⟩

#print axioms setting_mirror

/-! ## (1) The two zone events of the class -/

/-- **(1a) `opening_at_u`** [L]: `u_a = o_A a/(8 d_A)` is an opening of `d_A`: with `n_A = ⌊o_A a/8⌋`,
`8 n_A + 1 = o_A a`, `d_A u_a = n_A + 1/8` and `u_a = (n_A + 1/8)/d_A`. -/
theorem opening_at_u {d : ι → ℝ} {o : ι → ℤ} {A : ι} {a : ℤ} (ha : a % 2 = 1) (hoA : o A ≡ a [ZMOD 8])
    (hd : 0 < d A) :
    8 * lap o a A + 1 = o A * a ∧ d A * cI d o A a = (lap o a A : ℝ) + 1 / 8 ∧
      cI d o A a = ((lap o a A : ℝ) + 1 / 8) / d A := by
  have hr : (o A * a) % 8 = 1 := emod_of_modEq (res_one_of_eq ha hoA) (by norm_num) (by norm_num)
  have hz : 8 * lap o a A + 1 = o A * a := by
    unfold lap; have := Int.mul_ediv_add_emod (o A * a) 8; omega
  have hm : d A * cI d o A a = (lap o a A : ℝ) + 1 / 8 := by
    rw [mul_cI d o A a hd, gpos_split, hr]; norm_num
  refine ⟨hz, hm, ?_⟩
  rw [eq_div_iff hd.ne', mul_comm, hm]

#print axioms opening_at_u

/-- **(1b) `entry_at_w`** [L]: `w_a = o_B a/(8 d_B)` is an entry of `d_B`: `8 n_B + 7 = o_B a`,
`d_B w_a = n_B + 7/8`. -/
theorem entry_at_w {d : ι → ℝ} {o : ι → ℤ} {B : ι} {a : ℤ} (ha : a % 2 = 1) (hoB : o B ≡ -a [ZMOD 8])
    (hd : 0 < d B) :
    8 * lap o a B + 7 = o B * a ∧ d B * cI d o B a = (lap o a B : ℝ) + 7 / 8 ∧
      cI d o B a = ((lap o a B : ℝ) + 7 / 8) / d B := by
  have hr : (o B * a) % 8 = 7 := by
    have := res_seven_of_eq ha hoB
    have h7 : (-1 : ℤ) ≡ 7 [ZMOD 8] := by decide
    exact emod_of_modEq (this.trans h7) (by norm_num) (by norm_num)
  have hz : 8 * lap o a B + 7 = o B * a := by
    unfold lap; have := Int.mul_ediv_add_emod (o B * a) 8; omega
  have hm : d B * cI d o B a = (lap o a B : ℝ) + 7 / 8 := by
    rw [mul_cI d o B a hd, gpos_split, hr]; norm_num
  refine ⟨hz, hm, ?_⟩
  rw [eq_div_iff hd.ne', mul_comm, hm]

#print axioms entry_at_w

/-! ## (2) The ratio condition and its mirror -/

/-- **(2a) `u_le_w_iff`** [L]: `u_a ≤ w_a ↔ o_A d_B ≤ o_B d_A` (for `a > 0`). -/
theorem u_le_w_iff (d : ι → ℝ) (o : ι → ℤ) {A B : ι} {a : ℤ} (hdA : 0 < d A) (hdB : 0 < d B) (ha : 0 < a) :
    cI d o A a ≤ cI d o B a ↔ (o A : ℝ) * d B ≤ o B * d A := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  unfold cI
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : (o A : ℝ) * a * (8 * d B) = (8 * a) * (o A * d B) := by ring
  have e2 : (o B : ℝ) * a * (8 * d A) = (8 * a) * (o B * d A) := by ring
  rw [e1, e2]
  exact mul_le_mul_iff_of_pos_left (by positivity)

#print axioms u_le_w_iff

/-- **(2b) The mirror condition is the reverse** [L]: class `b` (opener `B`, closer `A`) has
`u_b ≤ w_b ↔ o_B d_A ≤ o_A d_B`; so for the pair at least one holds, and both iff `o_A d_B = o_B d_A` (the touch). -/
theorem pair_cover (d : ι → ℝ) (o : ι → ℤ) {A B : ι} {a b : ℤ} (hdA : 0 < d A) (hdB : 0 < d B) (ha : 0 < a)
    (hb : 0 < b) :
    (cI d o A a ≤ cI d o B a ∨ cI d o B b ≤ cI d o A b) ∧
      ((cI d o A a ≤ cI d o B a ∧ cI d o B b ≤ cI d o A b) ↔ (o A : ℝ) * d B = o B * d A) := by
  rw [u_le_w_iff d o hdA hdB ha, u_le_w_iff d o hdB hdA hb]
  refine ⟨le_total _ _ |>.imp id id |>.elim (fun h => Or.inl h) (fun h => Or.inr h), ?_⟩
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

#print axioms pair_cover

/-! ## (3) The interval is lonely -/

/-- Monotone window: if `x ≥ 0` is in the window `N` at both ends, it is clear throughout. -/
theorem window_on {x u w t : ℝ} (N : ℤ) (hx : 0 ≤ x) (hu : (N : ℝ) + 1 / 8 ≤ x * u)
    (hw : x * w ≤ (N : ℝ) + 7 / 8) (ht : t ∈ Set.Icc u w) : (1 / 8 : ℝ) ≤ distInt (x * t) :=
  PairLaw.window_on N hx hu hw ht

/-- An interior runner within `η ≤ 1/8` of its grid position is in its window `lap`. -/
theorem interior_window {o : ι → ℤ} {a : ℤ} {j : ι} {y η : ℝ} (hη : η ≤ 1 / 8)
    (hr : 2 ≤ (o j * a) % 8 ∧ (o j * a) % 8 ≤ 6) (h : |y - gpos o a j| ≤ η) :
    (lap o a j : ℝ) + 1 / 8 ≤ y ∧ y ≤ (lap o a j : ℝ) + 7 / 8 := by
  rw [gpos_split] at h
  have r2 : (2 : ℝ) ≤ (((o j * a) % 8 : ℤ) : ℝ) := by exact_mod_cast hr.1
  have r6 : (((o j * a) % 8 : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hr.2
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

#print axioms interior_window

/-- **(3a) `grid_interval_lonely`** [L]: in the residue setting of class `a`, under the local displacement hypothesis
of radius `η ≤ 1/8`, every runner of `S` is clear on all of `[u_a, w_a] = [o_A a/(8 d_A), o_B a/(8 d_B)]`.  Runner `j`
stays in the single window `⌊o_j a/8⌋` throughout: its position is monotone in `t`, and it is in that window at both
ends (interior runners: residue `o_j a mod 8 ∈ [2, 6]`, `η ≤ 1/8`; `A`: at `n_A + 1/8` at `u`, at most `n_A + 7/8` at
`w`; `B`: at `n_B + 7/8` at `w`, at least `n_B + 1/8` at `u`). -/
theorem grid_interval_lonely {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} {η : ℝ}
    (hs : ClassSetting S d o A B a) (hη : η ≤ 1 / 8) (hh : ClassHyp S d o A B a η) :
    Set.Icc (cI d o A a) (cI d o B a) ⊆ lonelySet (gds S d) := by
  obtain ⟨ha, hA, hB, hoA, hoB, hint, hpos⟩ := hs
  obtain ⟨hdev, hAw, hBu⟩ := hh
  intro t ht x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hdj := hpos j hj
  by_cases hjA : j = A
  · subst hjA
    obtain ⟨-, hm, -⟩ := opening_at_u ha hoA hdj
    have hs := gpos_split o a j
    have hr : (o j * a) % 8 = 1 := emod_of_modEq (res_one_of_eq ha hoA) (by norm_num) (by norm_num)
    rw [hr] at hs
    push_cast at hs
    exact window_on (lap o a j) hdj.le (by rw [hm]) (by linarith) ht
  by_cases hjB : j = B
  · subst hjB
    obtain ⟨-, hm, -⟩ := entry_at_w ha hoB hdj
    have hs := gpos_split o a j
    have hr : (o j * a) % 8 = 7 := by
      have h7 : (-1 : ℤ) ≡ 7 [ZMOD 8] := by decide
      exact emod_of_modEq ((res_seven_of_eq ha hoB).trans h7) (by norm_num) (by norm_num)
    rw [hr] at hs
    push_cast at hs
    exact window_on (lap o a j) hdj.le (by linarith) (by rw [hm]) ht
  obtain ⟨h0, h1, h7⟩ := hint j hj hjA hjB
  have hr := interior_res ha h0 h1 h7
  obtain ⟨hu, hw⟩ := hdev j hj hjA hjB
  exact window_on (lap o a j) hdj.le (interior_window hη hr hu).1 (interior_window hη hr hw).2 ht

#print axioms grid_interval_lonely

/-- **(3b) `grid_interval_isCell`** [L]: with also `0 < a`, `0 < o_A` and the ratio condition `o_A d_B ≤ o_B d_A`, the
interval `[u_a, w_a]` is a cell (maximal): runner `A` (lap `n_A`) is in the way just before `u_a`, runner `B` (lap
`n_B`) just after `w_a`.  A touch when `o_A d_B = o_B d_A`. -/
theorem grid_interval_isCell {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} {η : ℝ}
    (hs : ClassSetting S d o A B a) (hη : η ≤ 1 / 8) (hh : ClassHyp S d o A B a η) (ha0 : 0 < a)
    (hoA0 : 0 < o A) (hle : (o A : ℝ) * d B ≤ o B * d A) : IsCell (gds S d) (cI d o A a) (cI d o B a) := by
  have hsub := grid_interval_lonely hs hη hh
  obtain ⟨ha, hA, hB, hoA, hoB, -, hpos⟩ := hs
  have hx0 := hpos A hA
  have hy0 := hpos B hB
  have hpa : 0 < o A * a := mul_pos hoA0 ha0
  obtain ⟨-, hTx, -⟩ := opening_at_u ha hoA hx0
  obtain ⟨-, hSy, -⟩ := entry_at_w ha hoB hy0
  have hle' := (u_le_w_iff d o hx0 hy0 ha0).mpr hle
  have hu0 : 0 < cI d o A a := by
    unfold cI; apply div_pos (by exact_mod_cast hpa) (by linarith)
  have hmA : d A ∈ gds S d := Finset.mem_image_of_mem d hA
  have hmB : d B ∈ gds S d := Finset.mem_image_of_mem d hB
  refine ⟨hu0, hle', hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (cI d o A a - 1 / (8 * d A)) with hsdef
    have hq : 0 < 1 / (8 * d A) := by positivity
    have hq' : 1 / (8 * d A) < 1 / (4 * d A) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : cI d o A a - 1 / (4 * d A) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs2 : s < cI d o A a := max_lt hu' (by linarith)
    have hw := inWay_before_opening hx0 hTx hs1 hs2
    exact not_lonely_of_inWay hmA hw (hsub' ⟨le_max_left _ _, le_trans hs2.le hle'⟩)
  · intro w' hw' hsub'
    set s := min w' (cI d o B a + 1 / (8 * d B)) with hsdef
    have hq : 0 < 1 / (8 * d B) := by positivity
    have hq' : 1 / (8 * d B) < 1 / (4 * d B) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : cI d o B a < s := lt_min hw' (by linarith)
    have hs2 : s < cI d o B a + 1 / (4 * d B) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hw := inWay_after_entry hy0 hSy hs1 hs2
    exact not_lonely_of_inWay hmB hw (hsub' ⟨le_trans hle' hs1.le, min_le_left _ _⟩)

#print axioms grid_interval_isCell

/-- **(3c) `grid_interval_width`** [L]: the width of the class cell, `w − u = (n_B + 7/8)/d_B − (n_A + 1/8)/d_A`
with `8 n_A + 1 = o_A a` and `8 n_B + 7 = o_B a`: `LonelyCells.cell_width` with opener `A` and closer `B` named. -/
theorem grid_interval_width {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} (ha : a % 2 = 1)
    (hoA : o A ≡ a [ZMOD 8]) (hoB : o B ≡ -a [ZMOD 8]) (hdA : 0 < d A) (hdB : 0 < d B) :
    8 * lap o a A + 1 = o A * a ∧ 8 * lap o a B + 7 = o B * a ∧
      cI d o B a - cI d o A a = ((lap o a B : ℝ) + 7 / 8) / d B - ((lap o a A : ℝ) + 1 / 8) / d A := by
  obtain ⟨h1, -, hu⟩ := opening_at_u ha hoA hdA
  obtain ⟨h2, -, hw⟩ := entry_at_w ha hoB hdB
  exact ⟨h1, h2, by rw [hu, hw]⟩

#print axioms grid_interval_width

/-- **(3d) `grid_pair_law`** [L]: for a mirror pair `a + b ≡ 0 (mod 8)` with `a, b, o_A, o_B > 0`, one of the two
classes gives a cell: class `a` (`[o_A a/(8d_A), o_B a/(8d_B)]`) when `o_A d_B ≤ o_B d_A`, class `b`
(`[o_B b/(8d_B), o_A b/(8d_A)]`) when `o_B d_A ≤ o_A d_B`.  The local hypothesis is required only of the class whose
ratio condition holds. -/
theorem grid_pair_law {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a b : ℤ} {η : ℝ}
    (hs : ClassSetting S d o A B a) (hab : a + b ≡ 0 [ZMOD 8]) (hη : η ≤ 1 / 8)
    (ha0 : 0 < a) (hb0 : 0 < b) (hoA0 : 0 < o A) (hoB0 : 0 < o B)
    (hha : (o A : ℝ) * d B ≤ o B * d A → ClassHyp S d o A B a η)
    (hhb : (o B : ℝ) * d A ≤ o A * d B → ClassHyp S d o B A b η) :
    IsCell (gds S d) (cI d o A a) (cI d o B a) ∨ IsCell (gds S d) (cI d o B b) (cI d o A b) := by
  have hs' := setting_mirror hs hab
  rcases le_total ((o A : ℝ) * d B) (o B * d A) with h | h
  · exact Or.inl (grid_interval_isCell hs hη (hha h) ha0 hoA0 h)
  · exact Or.inr (grid_interval_isCell hs' hη (hhb h) hb0 hoB0 h)

#print axioms grid_pair_law

/-- **(3e) The record's form: the instant** [L]: with only the conditions AT `u_a` (interior runners within `η ≤ 1/8`
of their grid positions at `u_a`, `B` at least `n_B + 1/8` there) and the ratio condition `o_A d_B ≤ o_B d_A`, the
subject is lonely at `u_a`.  (The ratio condition puts `B` before its entry at `u_a`.) -/
theorem grid_instant_lonely {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} {η : ℝ}
    (hs : ClassSetting S d o A B a) (hη : η ≤ 1 / 8) (ha0 : 0 < a)
    (hdev : ∀ j ∈ S, j ≠ A → j ≠ B → |d j * cI d o A a - gpos o a j| ≤ η)
    (hBu : gpos o a B - 3 / 4 ≤ d B * cI d o A a) (hle : (o A : ℝ) * d B ≤ o B * d A) :
    Cascade.LonelyAt (gds S d) (cI d o A a) := by
  obtain ⟨ha, hA, hB, hoA, hoB, hint, hpos⟩ := hs
  have hle' := (u_le_w_iff d o (hpos A hA) (hpos B hB) ha0).mpr hle
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hdj := hpos j hj
  by_cases hjA : j = A
  · subst hjA
    obtain ⟨-, hm, -⟩ := opening_at_u ha hoA hdj
    exact clear_of_window (lap o a j) (by rw [hm]) (by rw [hm]; linarith)
  by_cases hjB : j = B
  · subst hjB
    obtain ⟨-, hm, -⟩ := entry_at_w ha hoB hdj
    have hs := gpos_split o a j
    have hr : (o j * a) % 8 = 7 := by
      have h7 : (-1 : ℤ) ≡ 7 [ZMOD 8] := by decide
      exact emod_of_modEq ((res_seven_of_eq ha hoB).trans h7) (by norm_num) (by norm_num)
    rw [hr] at hs
    push_cast at hs
    have hmono := mul_le_mul_of_nonneg_left hle' hdj.le
    exact clear_of_window (lap o a j) (by linarith) (by linarith)
  obtain ⟨h0, h1, h7⟩ := hint j hj hjA hjB
  exact clear_of_window (lap o a j) (interior_window hη (interior_res ha h0 h1 h7) (hdev j hj hjA hjB)).1
    (interior_window hη (interior_res ha h0 h1 h7) (hdev j hj hjA hjB)).2

#print axioms grid_instant_lonely


/-- **(3f) The exact window form** [L]: the sharpest hypothesis of this argument, per runner: each interior runner is
in its own window `⌊o_j a/8⌋` at both ends (`n_j + 1/8 ≤ d_j u`, `d_j w ≤ n_j + 7/8`; with `o_j a = 8 n_j + R_j` this
is a lower margin `(R_j − 1)/8` at `u` and an upper margin `(7 − R_j)/8` at `w`), and the opener and closer conditions
as in `ClassHyp`.  `grid_interval_lonely` is its uniform case `η = 1/8`. -/
theorem grid_interval_lonely_window {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ}
    (hs : ClassSetting S d o A B a)
    (hwin : ∀ j ∈ S, j ≠ A → j ≠ B →
      (lap o a j : ℝ) + 1 / 8 ≤ d j * cI d o A a ∧ d j * cI d o B a ≤ (lap o a j : ℝ) + 7 / 8)
    (hAw : d A * cI d o B a ≤ gpos o a A + 3 / 4) (hBu : gpos o a B - 3 / 4 ≤ d B * cI d o A a) :
    Set.Icc (cI d o A a) (cI d o B a) ⊆ lonelySet (gds S d) := by
  obtain ⟨ha, hA, hB, hoA, hoB, -, hpos⟩ := hs
  intro t ht x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  have hdj := hpos j hj
  by_cases hjA : j = A
  · subst hjA
    obtain ⟨-, hm, -⟩ := opening_at_u ha hoA hdj
    have hs := gpos_split o a j
    have hr : (o j * a) % 8 = 1 := emod_of_modEq (res_one_of_eq ha hoA) (by norm_num) (by norm_num)
    rw [hr] at hs
    push_cast at hs
    exact window_on (lap o a j) hdj.le (by rw [hm]) (by linarith) ht
  by_cases hjB : j = B
  · subst hjB
    obtain ⟨-, hm, -⟩ := entry_at_w ha hoB hdj
    have hs := gpos_split o a j
    have hr : (o j * a) % 8 = 7 := by
      have h7 : (-1 : ℤ) ≡ 7 [ZMOD 8] := by decide
      exact emod_of_modEq ((res_seven_of_eq ha hoB).trans h7) (by norm_num) (by norm_num)
    rw [hr] at hs
    push_cast at hs
    exact window_on (lap o a j) hdj.le (by linarith) (by rw [hm]) ht
  exact window_on (lap o a j) hdj.le (hwin j hj hjA hjB).1 (hwin j hj hjA hjB).2 ht

#print axioms grid_interval_lonely_window

/-- **(3g) The local form bounds the drift** [L]: under `ClassHyp` with radius `η`, each interior runner drifts by at
most `2η` over the class interval: `d_j (w − u) ≤ 2η`.  The drift `d_j (w − u)` grows with the offset (`d_j ≈ o_j g`),
so the hypothesis is a condition on rescaled positions, not on `|d_j − o_j g|` (see (4d), (4f)). -/
theorem drift_le {S : Finset ι} {d : ι → ℝ} {o : ι → ℤ} {A B : ι} {a : ℤ} {η : ℝ}
    (hh : ClassHyp S d o A B a η) {j : ι} (hj : j ∈ S) (hjA : j ≠ A) (hjB : j ≠ B) :
    d j * (cI d o B a - cI d o A a) ≤ 2 * η := by
  obtain ⟨h1, h2⟩ := hh.1 j hj hjA hjB
  have := (abs_le.mp h1).1
  have := (abs_le.mp h2).2
  rw [mul_sub]; linarith

#print axioms drift_le

/-! ## Sharpness of the radius and of the end conditions -/

/-- **`eta_sharp`** [L]: the radius `1/8` cannot be raised: for every `η > 1/8` (and `< 3/8`) a reading within `η` of an
interior grid position `n + 2/8` can be in the way (`n + 2/8 − η` is within `1/8` of `n`).  The end conditions `3/4`
are sharp in the same way (an opener past `n_A + 7/8` at `w` is past its own entry). -/
theorem eta_sharp {η : ℝ} (h1 : 1 / 8 < η) (h2 : η < 3 / 8) (n : ℤ) :
    |((n : ℝ) + 2 / 8 - η) - ((n : ℝ) + 2 / 8)| ≤ η ∧ distInt ((n : ℝ) + 2 / 8 - η) < 1 / 8 := by
  refine ⟨by rw [show (n : ℝ) + 2 / 8 - η - ((n : ℝ) + 2 / 8) = -η by ring, abs_neg, abs_of_pos (by linarith)], ?_⟩
  have := distInt_le ((n : ℝ) + 2 / 8 - η) n
  have h3 : |(n : ℝ) + 2 / 8 - η - n| < 1 / 8 := by
    rw [abs_lt]; constructor <;> linarith
  linarith

#print axioms eta_sharp

/-! ## (4) Exceptions

All examples index the seven readings by `S7 = {1, …, 7}` with grid step `1`.  `gds S7 d` is `PairLaw.pds d`. -/

/-- The seven reading labels. -/
def S7 : Finset ℕ := Finset.Icc 1 7

theorem gds_S7 (d : ℕ → ℝ) : gds S7 d = PairLaw.pds d := rfl

#print axioms gds_S7

theorem mem_S7 {j : ℕ} (h1 : 1 ≤ j) (h7 : j ≤ 7) : j ∈ S7 := Finset.mem_Icc.mpr ⟨h1, h7⟩

/-- The AP offsets `o_j = j`. -/
def apO : ℕ → ℤ := fun j => j

/-- **(4a) The AP is the case `o = (1, …, 7)`** [L]: the class-`a` opening and entry of this file are
`PairLaw.uA`, `PairLaw.wA` (opener `a`, closer `8 − a`). -/
theorem ap_case (d : ℕ → ℝ) (a : ℕ) :
    cI d apO a a = PairLaw.uA d a ∧ cI d apO (8 - a) a = PairLaw.wA d a (8 - a) := by
  unfold cI apO PairLaw.uA PairLaw.wA
  push_cast
  constructor
  · ring
  · ring

#print axioms ap_case

/-- **(4b) The AP exception of `PairLaw` is exactly the failure of the local hypothesis at the entry** [L]: in
`PairLaw.cxD ρ` (`d_1 = 1 − ρ`, `d_2 = 2 + ρ`), class 7 (opener 7, closer 1), runner 2 sits at its grid position
`14/8` plus `21ρ/(8(1 − ρ))` at `w_7`; the hypothesis `|·| ≤ 1/8` holds iff `ρ ≤ 1/22`, the sharp radius of
`PairLaw.interval_lonely` and the threshold of `PairLaw.record_interval_fails`. -/
theorem ap_exception_eta {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    PairLaw.cxD ρ 2 * cI (PairLaw.cxD ρ) apO 1 7 - gpos apO 7 2 = 21 * ρ / (8 * (1 - ρ)) ∧
      (|PairLaw.cxD ρ 2 * cI (PairLaw.cxD ρ) apO 1 7 - gpos apO 7 2| ≤ 1 / 8 ↔ ρ ≤ 1 / 22) := by
  have hp : (0 : ℝ) < 1 - ρ := by linarith
  have e : PairLaw.cxD ρ 2 * cI (PairLaw.cxD ρ) apO 1 7 - gpos apO 7 2 = 21 * ρ / (8 * (1 - ρ)) := by
    unfold cI gpos apO; rw [PairLaw.cxD_one, PairLaw.cxD_two]; push_cast
    field_simp; ring
  refine ⟨e, ?_⟩
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

#print axioms ap_exception_eta

/-- The grid offsets with one large offset: `o = (1, 2, 3, 4, 5, 8m + 6, 7)`, a complete nonzero residue system. -/
def oF (m : ℕ) : ℕ → ℤ := fun j => if j = 6 then 8 * m + 6 else j

theorem oF_mod (m : ℕ) (j : ℕ) : oF m j ≡ j [ZMOD 8] := by
  unfold oF
  split_ifs with h
  · subst h; rw [Int.ModEq]; push_cast; omega
  · rfl

#print axioms oF_mod

theorem oF_one (m : ℕ) : oF m 1 = 1 := by simp [oF]
theorem oF_six (m : ℕ) : oF m 6 = 8 * m + 6 := by simp [oF]
theorem oF_seven (m : ℕ) : oF m 7 = 7 := by simp [oF]
theorem oF_other (m : ℕ) {j : ℕ} (h : j ≠ 6) : oF m j = j := by simp [oF, h]

/-- The class-7 setting for `oF m` (opener runner 7, closer runner 1), for any positive readings. -/
theorem oF_setting (m : ℕ) {d : ℕ → ℝ} (hpos : ∀ j ∈ S7, 0 < d j) : ClassSetting S7 d (oF m) 7 1 7 := by
  apply setting_of_complete (by norm_num) (mem_S7 (by norm_num) le_rfl) (mem_S7 le_rfl (by norm_num))
  · rw [oF_seven]
  · rw [oF_one]; decide
  · intro j hj h
    have hj' := Finset.mem_Icc.mp hj
    have := (oF_mod m j).symm.trans h
    rw [Int.ModEq] at this; push_cast at this; omega
  · intro i hi j hj h
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    have := ((oF_mod m i).symm.trans h).trans (oF_mod m j)
    rw [Int.ModEq] at this; omega
  · exact hpos

#print axioms oF_setting

/-! ### Family F1: a slowed closer and a large interior offset; the instant survives, the interval does not -/

/-- `d_1 = 1 − ρ`, `d_6 = 8m + 6`, `d_j = j` otherwise: every reading within `ρ` of its offset (grid step 1). -/
noncomputable def dF1 (m : ℕ) (ρ : ℝ) : ℕ → ℝ := fun j => if j = 1 then 1 - ρ else if j = 6 then 8 * m + 6 else j

theorem dF1_one (m : ℕ) (ρ : ℝ) : dF1 m ρ 1 = 1 - ρ := by simp [dF1]
theorem dF1_six (m : ℕ) (ρ : ℝ) : dF1 m ρ 6 = 8 * m + 6 := by simp [dF1]
theorem dF1_other (m : ℕ) (ρ : ℝ) {j : ℕ} (h1 : j ≠ 1) (h6 : j ≠ 6) : dF1 m ρ j = j := by simp [dF1, h1, h6]

/-- The naive hypothesis `|d_j − o_j| ≤ ρ` holds in F1. -/
theorem dF1_naive (m : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) : ∀ j ∈ S7, |dF1 m ρ j - oF m j| ≤ ρ := by
  intro j _
  by_cases h1 : j = 1
  · subst h1; rw [dF1_one, oF_one]; push_cast
    rw [show (1 : ℝ) - ρ - 1 = -ρ by ring, abs_neg, abs_of_nonneg h0]
  by_cases h6 : j = 6
  · subst h6; rw [dF1_six, oF_six]; push_cast; simp [h0]
  · rw [dF1_other m ρ h1 h6, oF_other m h6]; push_cast; simp [h0]

#print axioms dF1_naive

theorem dF1_pos (m : ℕ) {ρ : ℝ} (h : ρ < 1) : ∀ j ∈ S7, 0 < dF1 m ρ j := by
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  by_cases h1 : j = 1
  · subst h1; rw [dF1_one]; linarith
  by_cases h6 : j = 6
  · subst h6; rw [dF1_six]; positivity
  · rw [dF1_other m ρ h1 h6]; exact_mod_cast (show 0 < j by omega)

#print axioms dF1_pos

/-- **(4c) `F1_instant_lonely`** [L]: in F1, for `0 ≤ ρ ≤ 6/7`, the class-7 ratio condition holds and the opening
`u_7 = 7/8` is lonely, for EVERY `m` (by `grid_instant_lonely` with `η = 0`: every interior runner is exactly on its
grid position at `u_7`, since the opener 7 is undeviated). -/
theorem F1_instant_lonely (m : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 6 / 7) :
    cI (dF1 m ρ) (oF m) 7 7 = 7 / 8 ∧ (oF m 7 : ℝ) * dF1 m ρ 1 ≤ oF m 1 * dF1 m ρ 7 ∧
      Cascade.LonelyAt (gds S7 (dF1 m ρ)) (cI (dF1 m ρ) (oF m) 7 7) := by
  have h7 : dF1 m ρ 7 = 7 := by rw [dF1_other m ρ (by norm_num) (by norm_num)]; norm_num
  have hu : cI (dF1 m ρ) (oF m) 7 7 = 7 / 8 := by unfold cI; rw [h7, oF_seven]; norm_num
  have hle : (oF m 7 : ℝ) * dF1 m ρ 1 ≤ oF m 1 * dF1 m ρ 7 := by
    rw [oF_seven, oF_one, dF1_one, h7]; push_cast; linarith
  refine ⟨hu, hle, ?_⟩
  apply grid_instant_lonely (oF_setting m (dF1_pos m (by linarith))) (η := 0) (by norm_num) (by norm_num)
  · intro j hj hj7 hj1
    rw [hu]
    have h' : dF1 m ρ j = oF m j := by
      by_cases h6 : j = 6
      · subst h6; rw [dF1_six, oF_six]; push_cast; ring
      · rw [dF1_other m ρ hj1 h6, oF_other m h6]; push_cast; ring
    rw [h']; unfold gpos; push_cast; rw [show (oF m j : ℝ) * (7 / 8) - oF m j * 7 / 8 = 0 by ring]; simp
  · rw [hu, dF1_one]; unfold gpos; rw [oF_one]; push_cast; linarith
  · exact hle

#print axioms F1_instant_lonely

/-- **(4d) `F1_interval_fails`** [L]: in F1, for every `m` and `3/(28m + 24) ≤ ρ < 1`, the naive hypothesis holds at
radius `ρ`, the class-7 ratio condition holds, and the class interval `[u_7, w_7] = [7/8, 7/(8(1 − ρ))]` is NOT lonely:
it contains `t* = (7m + 6)/(8m + 6)`, where runner 6 (offset `8m + 6`) stands on lap line `7m + 6`.  Why: runner 6
drifts by `d_6 (w_7 − u_7) = 7 (8m + 6) ρ/(8 (1 − ρ))` during the interval, proportional to its OFFSET, against an upper
margin of `5/8` (residue `7·6 ≡ 2`, so `5/8` from its entry and `6/8 + 1/8` from the next lap line).  The zones that
overlap are runner 6's zone around lap `7m + 6` and the closer 1's clear stretch before its entry `7/8`.  For each
fixed `ρ > 0` a large enough `m` breaks the interval: no radius on `|d_j − o_j|` alone suffices. -/
theorem F1_interval_fails (m : ℕ) {ρ : ℝ} (h1 : 3 / (28 * m + 24) ≤ ρ) (h2 : ρ < 1) :
    (∀ j ∈ S7, |dF1 m ρ j - oF m j| ≤ ρ) ∧ (oF m 7 : ℝ) * dF1 m ρ 1 ≤ oF m 1 * dF1 m ρ 7 ∧
      ¬ Set.Icc (cI (dF1 m ρ) (oF m) 7 7) (cI (dF1 m ρ) (oF m) 1 7) ⊆ lonelySet (gds S7 (dF1 m ρ)) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hρ : 3 ≤ (28 * m + 24) * ρ := by rw [div_le_iff₀ (by positivity)] at h1; linarith
  have h0 : 0 ≤ ρ := by nlinarith
  have h7 : dF1 m ρ 7 = 7 := by rw [dF1_other m ρ (by norm_num) (by norm_num)]; norm_num
  refine ⟨dF1_naive m h0, by rw [oF_seven, oF_one, dF1_one, h7]; push_cast; linarith, ?_⟩
  intro hsub
  set ts : ℝ := (7 * m + 6) / (8 * m + 6) with hts
  have hu : cI (dF1 m ρ) (oF m) 7 7 = 7 / 8 := by unfold cI; rw [h7, oF_seven]; norm_num
  have hw : cI (dF1 m ρ) (oF m) 1 7 = 7 / (8 * (1 - ρ)) := by
    unfold cI; rw [dF1_one, oF_one]; push_cast; ring
  have hmem : ts ∈ Set.Icc (cI (dF1 m ρ) (oF m) 7 7) (cI (dF1 m ρ) (oF m) 1 7) := by
    rw [hu, hw, hts]
    constructor
    · rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    · rw [div_le_div_iff₀ (by positivity) (by nlinarith)]; nlinarith
  have hl := hsub hmem (dF1 m ρ 6) (Finset.mem_image_of_mem _ (mem_S7 (by norm_num) (by norm_num)))
  have e : dF1 m ρ 6 * ts = ((7 * m + 6 : ℕ) : ℤ) := by
    rw [dF1_six, hts]; push_cast; field_simp
  rw [e, distInt_intCast] at hl
  norm_num at hl

#print axioms F1_interval_fails


theorem mul_frac_le {x P D c : ℝ} (hD : 0 < D) (h : x * P ≤ c * D) : x * (P / D) ≤ c := by
  rw [← mul_div_assoc, div_le_iff₀ hD]; exact h

theorem le_mul_frac {x P D c : ℝ} (hD : 0 < D) (h : c * D ≤ x * P) : c ≤ x * (P / D) := by
  rw [← mul_div_assoc, le_div_iff₀ hD]; exact h

#print axioms mul_frac_le
#print axioms le_mul_frac

/-- **(4e) `F1_displaced_cell`** [L]: in F1 with `m ≥ 1` and `5/(56m + 47) ≤ ρ ≤ 1/8`, the cell at the class-7
opening is `[7/8, (56m + 47)/(8 (8m + 6))]`: opened by runner 7 as in the grid, CLOSED BY RUNNER 6 (its entry at
lap `7m + 5`) instead of the grid's closer runner 1.  The isolation is displaced, not destroyed: the closer changes
from the slowed runner 1 to the large-offset runner 6, exactly as in the AP exception (`PairLaw.displaced_cell`, where
runner 2 replaces runner 1).  At the AP the threshold is `ρ = 1/22` (runner 2); here it is `5/(56m + 47)`, which
tends to `0` with the offset. -/
theorem F1_displaced_cell (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (h1 : 5 / (56 * m + 47) ≤ ρ) (h2 : ρ ≤ 1 / 8) :
    IsCell (gds S7 (dF1 m ρ)) (7 / 8) ((56 * m + 47) / (8 * (8 * m + 6))) := by
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hρ : 5 ≤ (56 * m + 47) * ρ := by rw [div_le_iff₀ (by positivity)] at h1; linarith
  have hD : (0 : ℝ) < 8 * (8 * m + 6) := by positivity
  set T : ℝ := (56 * m + 47) / (8 * (8 * m + 6)) with hT
  have hle : (7 / 8 : ℝ) ≤ T := by rw [hT, le_div_iff₀ hD]; nlinarith
  have hsub : Set.Icc (7 / 8 : ℝ) T ⊆ lonelySet (gds S7 (dF1 m ρ)) := by
    intro t ht x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := Finset.mem_Icc.mp hj
    obtain ⟨hj1, hj7⟩ := hj'
    interval_cases j
    · rw [dF1_one]
      refine window_on 0 (by linarith) (by push_cast; nlinarith) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_other m ρ (by norm_num) (by norm_num)]
      refine window_on 1 (by norm_num) (by norm_num) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_other m ρ (by norm_num) (by norm_num)]
      refine window_on 2 (by norm_num) (by norm_num) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_other m ρ (by norm_num) (by norm_num)]
      refine window_on 3 (by norm_num) (by norm_num) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_other m ρ (by norm_num) (by norm_num)]
      refine window_on 4 (by norm_num) (by norm_num) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_six]
      refine window_on ((7 * m + 5 : ℕ) : ℤ) (by positivity) (by push_cast; nlinarith) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
    · rw [dF1_other m ρ (by norm_num) (by norm_num)]
      refine window_on 6 (by norm_num) (by norm_num) ?_ ht
      push_cast; exact mul_frac_le hD (by nlinarith)
  have h7 : dF1 m ρ 7 = 7 := by rw [dF1_other m ρ (by norm_num) (by norm_num)]; norm_num
  have h6 : (0 : ℝ) < dF1 m ρ 6 := by rw [dF1_six]; positivity
  refine ⟨by norm_num, hle, hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (7 / 8 - 1 / 56) with hsdef
    have hs1 : (7 / 8 : ℝ) - 1 / (4 * 7) < s := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hs2 : s < 7 / 8 := max_lt hu' (by norm_num)
    have hw := inWay_before_opening (x := 7) (by norm_num) (N := 6) (by norm_num) hs1 hs2
    have hmem : (7 : ℝ) ∈ gds S7 (dF1 m ρ) := by
      rw [← h7]; exact Finset.mem_image_of_mem _ (mem_S7 (by norm_num) le_rfl)
    exact not_lonely_of_inWay hmem hw (hsub' ⟨le_max_left _ _, le_trans hs2.le hle⟩)
  · intro w' hw' hsub'
    set s := min w' (T + 1 / (8 * dF1 m ρ 6)) with hsdef
    have hq : 0 < 1 / (8 * dF1 m ρ 6) := by positivity
    have hq' : 1 / (8 * dF1 m ρ 6) < 1 / (4 * dF1 m ρ 6) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : T < s := lt_min hw' (by linarith)
    have hs2 : s < T + 1 / (4 * dF1 m ρ 6) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hent : dF1 m ρ 6 * T = (((7 * m + 5 : ℕ) : ℤ) : ℝ) + 7 / 8 := by
      rw [dF1_six, hT]; push_cast; field_simp; ring
    have hw := inWay_after_entry h6 hent hs1 hs2
    have hmem : dF1 m ρ 6 ∈ gds S7 (dF1 m ρ) := Finset.mem_image_of_mem _ (mem_S7 (by norm_num) (by norm_num))
    exact not_lonely_of_inWay hmem hw (hsub' ⟨le_trans hle hs1.le, min_le_left _ _⟩)

#print axioms F1_displaced_cell

/-! ### Family F2: a sped-up opener and a large interior offset; both class instants of the pair fail -/

/-- `d_1 = 1 − ρ`, `d_6 = 8m + 6 − ρ`, `d_7 = 7 + ρ`, `d_j = j` otherwise (grid step 1, offsets `oF m`). -/
noncomputable def dF2 (m : ℕ) (ρ : ℝ) : ℕ → ℝ :=
  fun j => if j = 1 then 1 - ρ else if j = 6 then 8 * m + 6 - ρ else if j = 7 then 7 + ρ else j

theorem dF2_one (m : ℕ) (ρ : ℝ) : dF2 m ρ 1 = 1 - ρ := by simp [dF2]
theorem dF2_six (m : ℕ) (ρ : ℝ) : dF2 m ρ 6 = 8 * m + 6 - ρ := by simp [dF2]
theorem dF2_seven (m : ℕ) (ρ : ℝ) : dF2 m ρ 7 = 7 + ρ := by simp [dF2]
theorem dF2_other (m : ℕ) (ρ : ℝ) {j : ℕ} (h1 : j ≠ 1) (h6 : j ≠ 6) (h7 : j ≠ 7) : dF2 m ρ j = j := by
  simp [dF2, h1, h6, h7]

/-- The naive hypothesis `|d_j − o_j| ≤ ρ` holds in F2. -/
theorem dF2_naive (m : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) : ∀ j ∈ S7, |dF2 m ρ j - oF m j| ≤ ρ := by
  intro j _
  by_cases h1 : j = 1
  · subst h1; rw [dF2_one, oF_one]; push_cast
    rw [show (1 : ℝ) - ρ - 1 = -ρ by ring, abs_neg, abs_of_nonneg h0]
  by_cases h6 : j = 6
  · subst h6; rw [dF2_six, oF_six]; push_cast
    rw [show (8 * m + 6 - ρ : ℝ) - (8 * m + 6) = -ρ by ring, abs_neg, abs_of_nonneg h0]
  by_cases h7 : j = 7
  · subst h7; rw [dF2_seven, oF_seven]; push_cast
    rw [show (7 + ρ : ℝ) - 7 = ρ by ring, abs_of_nonneg h0]
  · rw [dF2_other m ρ h1 h6 h7, oF_other m h6]; push_cast; simp [h0]

#print axioms dF2_naive

/-- **(4f) `F2_both_instants_fail`** [L]: for every `m` and `7/(56m + 90) < ρ < 21/(56m + 88)`, `ρ < 1/5`: the naive
hypothesis `|d_j − o_j| ≤ ρ` holds; the class-7 ratio condition holds and the class-1 one fails strictly; and NEITHER
class instant is lonely: at `u_7 = 49/(8(7 + ρ))` runner 6 is within `1/8` of lap `7m + 5`, at `u_1 = 1/(8(1 − ρ))`
runner 7 is within `1/8` of lap `1`.  So the record's left-end pair law is false under a radius on `|d_j − o_j|`
(at `ρ = 1/20` from `m = 1`; at `ρ = 1/22`, the AP's sharp radius, from `m = 2`, offset `22`).  Why: runner 6's
reading at `u_7` is its grid position `7m + 5 + 2/8` times `(8m + 6 − ρ) 7/((8m + 6)(7 + ρ))`; the opener 7 sped up by
`ρ` pulls the instant back by the factor `7/(7 + ρ)`, which moves runner 6 back by about `(7m + 5) ρ/7`, proportional to
its OFFSET, against a lower margin of `1/8` (residue `2`).  The overlapping zones: runner 6's zone around lap `7m + 5`
still covers the opening of runner 7. -/
theorem F2_both_instants_fail (m : ℕ) {ρ : ℝ} (h1 : 7 / (56 * m + 90) < ρ) (h2 : ρ < 21 / (56 * m + 88))
    (h3 : ρ < 1 / 5) :
    (∀ j ∈ S7, |dF2 m ρ j - oF m j| ≤ ρ) ∧ (oF m 7 : ℝ) * dF2 m ρ 1 ≤ oF m 1 * dF2 m ρ 7 ∧
      (oF m 7 : ℝ) * dF2 m ρ 1 < oF m 1 * dF2 m ρ 7 ∧
      ¬ Cascade.LonelyAt (gds S7 (dF2 m ρ)) (cI (dF2 m ρ) (oF m) 7 7) ∧
      ¬ Cascade.LonelyAt (gds S7 (dF2 m ρ)) (cI (dF2 m ρ) (oF m) 1 1) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hρ1 : 7 < (56 * m + 90) * ρ := by rw [div_lt_iff₀ (by positivity)] at h1; linarith
  have hρ2 : (56 * m + 88) * ρ < 21 := by rw [lt_div_iff₀ (by positivity)] at h2; linarith
  have h0 : 0 < ρ := by nlinarith
  have hstrict : (oF m 7 : ℝ) * dF2 m ρ 1 < oF m 1 * dF2 m ρ 7 := by
    rw [oF_seven, oF_one, dF2_one, dF2_seven]; push_cast; linarith
  refine ⟨dF2_naive m h0.le, hstrict.le, hstrict, ?_, ?_⟩
  · intro hl
    have h := hl (dF2 m ρ 6) (Finset.mem_image_of_mem _ (mem_S7 (by norm_num) (by norm_num)))
    have e : dF2 m ρ 6 * cI (dF2 m ρ) (oF m) 7 7 = 49 * (8 * m + 6 - ρ) / (8 * (7 + ρ)) := by
      unfold cI; rw [dF2_six, dF2_seven, oF_seven]; push_cast; field_simp; ring
    rw [e] at h
    have hd : (0 : ℝ) < 8 * (7 + ρ) := by positivity
    have hlo : (((7 * m + 5 : ℕ) : ℤ) : ℝ) - 1 / 8 < 49 * (8 * m + 6 - ρ) / (8 * (7 + ρ)) := by
      rw [lt_div_iff₀ hd]; push_cast; nlinarith
    have hhi : 49 * (8 * m + 6 - ρ) / (8 * (7 + ρ)) < (((7 * m + 5 : ℕ) : ℤ) : ℝ) + 1 / 8 := by
      rw [div_lt_iff₀ hd]; push_cast; nlinarith
    have := distInt_le (49 * (8 * m + 6 - ρ) / (8 * (7 + ρ))) ((7 * m + 5 : ℕ) : ℤ)
    have hab : |49 * (8 * m + 6 - ρ) / (8 * (7 + ρ)) - (((7 * m + 5 : ℕ) : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]; constructor <;> linarith
    linarith
  · intro hl
    have h := hl (dF2 m ρ 7) (Finset.mem_image_of_mem _ (mem_S7 (by norm_num) le_rfl))
    have hp : (0 : ℝ) < 1 - ρ := by linarith
    have e : dF2 m ρ 7 * cI (dF2 m ρ) (oF m) 1 1 = (7 + ρ) / (8 * (1 - ρ)) := by
      unfold cI; rw [dF2_seven, dF2_one, oF_one]; push_cast; field_simp
    rw [e] at h
    have hd : (0 : ℝ) < 8 * (1 - ρ) := by positivity
    have hlo : ((1 : ℤ) : ℝ) - 1 / 8 < (7 + ρ) / (8 * (1 - ρ)) := by rw [lt_div_iff₀ hd]; push_cast; nlinarith
    have hhi : (7 + ρ) / (8 * (1 - ρ)) < ((1 : ℤ) : ℝ) + 1 / 8 := by rw [div_lt_iff₀ hd]; push_cast; nlinarith
    have := distInt_le ((7 + ρ) / (8 * (1 - ρ))) 1
    have hab : |(7 + ρ) / (8 * (1 - ρ)) - ((1 : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]; constructor <;> linarith
    linarith

#print axioms F2_both_instants_fail


/-! ### F2 at `m = 1`, `ρ = 1/20`: the cascade displaces the isolation to runner 6's opening (exact rationals)

Readings `(19/20, 2, 3, 4, 5, 279/20, 141/20)`, offsets `(1, 2, 3, 4, 5, 14, 7)`.  -/

theorem dF2_ex_pos : ∀ x ∈ gds S7 (dF2 1 (1 / 20)), 0 < x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hj1, hj7⟩ := Finset.mem_Icc.mp hj
  interval_cases j <;> norm_num [dF2]

#print axioms dF2_ex_pos

/-- **(4g) `F2_example_cell`** [L]: the cell `[485/558, 35/38]`, opened by runner 6 at lap 12 (instead of the grid's
opener 7 at `u_7 = 245/282`), closed by runner 1 at its entry `7/8` as in the grid. -/
theorem F2_example_cell : IsCell (gds S7 (dF2 1 (1 / 20))) (485 / 558) (35 / 38) := by
  have hsub : Set.Icc (485 / 558 : ℝ) (35 / 38) ⊆ lonelySet (gds S7 (dF2 1 (1 / 20))) := by
    intro t ht x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hj1, hj7⟩ := Finset.mem_Icc.mp hj
    interval_cases j
    · exact window_on 0 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 1 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 2 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 3 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 4 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 12 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
    · exact window_on 6 (by norm_num [dF2]) (by norm_num [dF2]) (by norm_num [dF2]) ht
  have h6 : dF2 1 (1 / 20) 6 = 279 / 20 := by norm_num [dF2]
  have h1 : dF2 1 (1 / 20) 1 = 19 / 20 := by norm_num [dF2]
  refine ⟨by norm_num, by norm_num, hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (485 / 558 - 1 / (8 * (279 / 20))) with hsdef
    have hs1 : (485 / 558 : ℝ) - 1 / (4 * (279 / 20)) < s := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hs2 : s < 485 / 558 := max_lt hu' (by norm_num)
    have hw := inWay_before_opening (x := 279 / 20) (by norm_num) (N := 12) (by norm_num) hs1 hs2
    have hmem : (279 / 20 : ℝ) ∈ gds S7 (dF2 1 (1 / 20)) := by
      rw [← h6]; exact Finset.mem_image_of_mem _ (mem_S7 (by norm_num) (by norm_num))
    exact not_lonely_of_inWay hmem hw (hsub' ⟨le_max_left _ _, le_trans hs2.le (by norm_num)⟩)
  · intro w' hw' hsub'
    set s := min w' (35 / 38 + 1 / (8 * (19 / 20))) with hsdef
    have hs1 : (35 / 38 : ℝ) < s := lt_min hw' (by norm_num)
    have hs2 : s < 35 / 38 + 1 / (4 * (19 / 20)) := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hw := inWay_after_entry (x := 19 / 20) (by norm_num) (N := 0) (by norm_num) hs1 hs2
    have hmem : (19 / 20 : ℝ) ∈ gds S7 (dF2 1 (1 / 20)) := by
      rw [← h1]; exact Finset.mem_image_of_mem _ (mem_S7 le_rfl (by norm_num))
    exact not_lonely_of_inWay hmem hw (hsub' ⟨le_trans (by norm_num) hs1.le, min_le_left _ _⟩)

#print axioms F2_example_cell

/-- **(4h) `F2_example_cascade`** [L]: the cascade, run from the class instant `u_7 = 245/282` (a local statement:
the cascade's own start is `1/(8 d_min)`), makes ONE move, to runner 6's opening `485/558` (runner 6 is the only runner
in the way at `u_7`; runner 7 stands exactly at its opening `6 + 1/8`), and is fixed there.  So the grid's class-7
isolation is displaced by the cascade to the opening of the large-offset runner, by `485/558 − 245/282 = 5/13113`. -/
theorem F2_example_cascade :
    cI (dF2 1 (1 / 20)) (oF 1) 7 7 = 245 / 282 ∧
      IsMove (gds S7 (dF2 1 (1 / 20))) (245 / 282) (485 / 558) ∧
      IsMove (gds S7 (dF2 1 (1 / 20))) (485 / 558) (485 / 558) := by
  have h6 : dF2 1 (1 / 20) 6 = 279 / 20 := by norm_num [dF2]
  have hmem6 : dF2 1 (1 / 20) 6 ∈ gds S7 (dF2 1 (1 / 20)) :=
    Finset.mem_image_of_mem _ (mem_S7 (by norm_num) (by norm_num))
  have hk : |dF2 1 (1 / 20) 6 * (245 / 282) - ((12 : ℤ) : ℝ)| < 1 / 8 := by
    rw [h6, abs_lt]; constructor <;> norm_num
  have hnext : nextOpening (dF2 1 (1 / 20) 6) (245 / 282) = 485 / 558 := by
    rw [Cascade.nextOpening_eq hk, h6]; norm_num
  refine ⟨by unfold cI; norm_num [dF2, oF], Or.inr ⟨_, hmem6, inWay_of_near 12 hk, hnext.symm, ?_⟩, ?_⟩
  · intro x hx hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hj1, hj7⟩ := Finset.mem_Icc.mp hj
    have clr : ∀ N : ℤ, (N : ℝ) + 1 / 8 ≤ dF2 1 (1 / 20) j * (245 / 282) →
        dF2 1 (1 / 20) j * (245 / 282) ≤ (N : ℝ) + 7 / 8 → False :=
      fun N h1 h2 => Cascade.not_inWay_iff.mpr (clear_of_window N h1 h2) hw
    interval_cases j
    · exact (clr 0 (by norm_num [dF2]) (by norm_num [dF2])).elim
    · exact (clr 1 (by norm_num [dF2]) (by norm_num [dF2])).elim
    · exact (clr 2 (by norm_num [dF2]) (by norm_num [dF2])).elim
    · exact (clr 3 (by norm_num [dF2]) (by norm_num [dF2])).elim
    · exact (clr 4 (by norm_num [dF2]) (by norm_num [dF2])).elim
    · exact le_of_eq hnext
    · exact (clr 6 (by norm_num [dF2]) (by norm_num [dF2])).elim
  · rw [Cascade.isMove_self_iff dF2_ex_pos]
    exact F2_example_cell.2.2.1 ⟨le_rfl, by norm_num⟩

#print axioms F2_example_cascade

end Fresh.GridPairLaw
