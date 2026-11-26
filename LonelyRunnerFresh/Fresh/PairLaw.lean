import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Localisation
import Fresh.LonelyCells
import Fresh.APNeighbourhood

/-!
# The pair law: a deformation of the AP displaces the class instant into a cell (Task P)

Written 2026-10-07.  Imports Mathlib and the Fresh modules `Framework`, `Cascade`, `Localisation`, `LonelyCells`,
`APNeighbourhood`; nothing from the existing `LonelyRunner` repo.  Exact reals; every disparity is positive (no runner is
stationary: the `d j` are readings, i.e. speed differences from a subject of positive speed, and each is proved positive
from the deformation hypothesis).

This is a LOCAL displacement statement (rule 1).  It is not an existence argument and is not offered as a route to one.
The radius `ρ` in `|d j − j c| ≤ ρ c` is a HYPOTHESIS of the local statement; it is not a bound on the cascade, on moves,
or on anything the cascade does.  No counting, covering, density, cap or move budget appears anywhere in this file.

Objects.  Readings `d 1, …, d 7` (`d : ℕ → ℝ`), the disparity set `pds d = {d 1, …, d 7}`.  A class `a` (odd, `1 ≤ a ≤ 7`)
with mirror `b = 8 − a` (hypothesis `a + b = 8`).  The two zone events of the class:
* `uA d a = a²/(8 d_a)`: runner `a` OPENS (leaves its zone), reading `(a² − 1)/8 + 1/8` (`opening_at_u`);
* `wA d a b = a b/(8 d_b)`: runner `b` ENTERS its zone, reading `(a−1)(7−a)/8 + 7/8` (`entry_at_w`).
At the AP (`d j = j c`) the two coincide at `a/(8c)`: a touch.

The argument is symbolic in the reading `j`.  Write `j a = 8 n + R` (`n = ⌊j a/8⌋`, `R = j a mod 8`).  Runner `j` sits in
the window `[n + 1/8, n + 7/8]` on all of `[u, w]` iff `(8n+1) d_a ≤ a² d_j` (at `u`) and `a b d_j ≤ (8n+7) d_b` (at `w`).
The residue `R` is never `0`, is `1` only for `j = a`, and `7` only for `j = b` (`res_ne_zero`, `res_one`, `res_seven`:
`a² ≡ 1 mod 8`).  For `j = a` the first condition is an identity, for `j = b` the second is.  Otherwise each condition
reduces, by one exact identity (`lower_of_core`, `upper_of_core`), to a "core" inequality in `a, j, n, R, ρ` alone:
* at `u`: `a (R − 1) − ρ (a² + 8n + 1) ≥ 0`, true for `ρ ≤ 1/14` because `R ≥ 2` (`core_lower`);
* at `w`: `b (7 − R) − ρ (8n + 7 + a b) ≥ 0`, true for `ρ ≤ 1/22` (`core_upper_small` for `a ≤ 5` using only
  `1 ≤ R ≤ 6`; `core_upper_seven` for `a = 7`, where `R = 8 − j` and `n = j − 1`, i.e. runner `j` stands `j/8` before
  lap `j`).

Results.
* (1) `opening_at_u`, `entry_at_w` [L].
* (2) `interval_lonely` [L]: radius `ρ ≤ 1/22` ⇒ `[u_a, w_a] ⊆ lonelySet (pds d)`.
* (3) `u_le_w_iff` [L]: `u_a ≤ w_a ↔ a d_b ≤ b d_a`.  `pair_law` [L]: for every mirror pair one class is a cell.
  `pair_both_iff` [L]: both classes survive iff `a d_b = b d_a`, and then both are touches (`pair_touch`).
  `pair_exclusive` [L]: if class `a` is strict the class `b` interval is empty.  The two conditions are not exact
  negations: their common boundary is equality, which is the touch.
* (4) `interval_isCell` [L]: when nonempty, `[u_a, w_a]` is a cell (maximal: runner `a` is in the way just before `u_a`,
  runner `b` just after `w_a`), opener `d_a`, closer `d_b`; `interval_width` [L].
* The record's own statement (left end only, radius `c/20`): `instant_lonely_record`, `pair_law_record` [L].
* (5) The exception, understood.  At radius `c/20` the record's INTERVAL `[a²/(8d_a), a(8−a)/(8d_{8−a})]` is not
  lonely in general: class `a = 7` fails.  `cxD ρ` (`d 1 = 1 − ρ`, `d 2 = 2 + ρ`, `d j = j` otherwise, `c = 1`):
  `record_interval_fails` [L] for every `1/22 < ρ < 1/8` (so at `ρ = 1/20`, `record_interval_fails_c20`): at `w_7`
  runner `2` is inside its zone.  Why: in class 7 runner `2` sits at `14/8`, one eighth before its entry `15/8`; runner `2`
  speeding up and the closer `1` slowing down make runner 2 enter first, exactly when `7 (2 + ρ) > 15 (1 − ρ)`, i.e.
  `ρ > 1/22`.  The isolation is NOT destroyed: `displaced_cell` [L] shows that for `1/22 ≤ ρ ≤ 1/14` the cell is
  `[7/8, 15/(8(2 + ρ))]`, opened by runner 7 as before and closed by runner 2 instead of runner 1.  So `1/22` is the sharp
  radius for "the closer is runner `8 − a`", and the record's interval claim is the wrong statement at `c/20`; the
  right statement is `interval_lonely` (radius `1/22`), or the record's left-end statement (radius `1/20`).

Provenance.  Existing repo `LRC/Spec/ProgressionPairN.lean` (E69): `clear_mid`, `clear_leave`, `clear_enter` (here
replaced by the single window `n = ⌊j a/8⌋` and `Localisation.clear_of_window`), `dev_bound` (here `lower_of_core`,
`upper_of_core` and the core lemmas, which keep the residue `R` and so are exact rather than a `1/8` envelope),
`instant_lonely` (here `instant_lonely_record`, and the stronger `interval_lonely`), `pair_law` (here `pair_law_record`
and `pair_law`).  The existing proofs were read and understood; none was copied.  The existing file proves only the
left end of each interval; the interval, the cell, the residue lemmas, the both-iff-equality law and the exception are
new here.
-/

open Classical

namespace Fresh.PairLaw

open Fresh Fresh.Localisation Fresh.LonelyCells

/-! ## Objects -/

/-- The seven readings as a disparity set. -/
noncomputable def pds (d : ℕ → ℝ) : Finset ℝ := (Finset.Icc 1 7).image d

/-- The opening instant of class `a`: runner `a` leaves its zone. -/
noncomputable def uA (d : ℕ → ℝ) (a : ℕ) : ℝ := (a : ℝ) ^ 2 / (8 * d a)

/-- The entry instant of class `a`: runner `b = 8 − a` enters its zone. -/
noncomputable def wA (d : ℕ → ℝ) (a b : ℕ) : ℝ := (a : ℝ) * b / (8 * d b)

theorem lonelyAt_pds_iff (d : ℕ → ℝ) (t : ℝ) :
    Cascade.LonelyAt (pds d) t ↔ ∀ j, 1 ≤ j → j ≤ 7 → (1 / 8 : ℝ) ≤ distInt (d j * t) := by
  unfold Cascade.LonelyAt pds
  constructor
  · intro h j h1 h7
    exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨h1, h7⟩, rfl⟩)
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact h j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

#print axioms lonelyAt_pds_iff

theorem mem_pds (d : ℕ → ℝ) {j : ℕ} (h1 : 1 ≤ j) (h7 : j ≤ 7) : d j ∈ pds d :=
  Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨h1, h7⟩, rfl⟩

#print axioms mem_pds

/-! ## Residues mod 8 (symbolic) -/

/-- An odd square is `1 mod 8`. -/
theorem odd_sq_mod8 {a : ℕ} (ha : a % 2 = 1) : a * a % 8 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
  obtain ⟨q, hq⟩ := Nat.even_mul_succ_self m
  have e : (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
  rw [e, hq]; omega

#print axioms odd_sq_mod8

/-- For odd `a` and `1 ≤ j ≤ 7`, `8 ∤ j a`. -/
theorem res_ne_zero {a j : ℕ} (ha : a % 2 = 1) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) : j * a % 8 ≠ 0 := by
  intro h
  have hd : 8 ∣ j * a := Nat.dvd_of_mod_eq_zero h
  have h2 : Nat.Coprime 2 a := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ha)
  have hcop : Nat.Coprime 8 a := by simpa using Nat.Coprime.pow_left 3 h2
  have := hcop.dvd_of_dvd_mul_right hd
  omega

#print axioms res_ne_zero

theorem mul_sq_mod {a j : ℕ} (ha : a % 2 = 1) : j * (a * a) % 8 = j % 8 := by
  rw [Nat.mul_mod, odd_sq_mod8 ha]; simp

#print axioms mul_sq_mod

/-- Residue `1` (the leaving position) only for `j = a`: `j a ≡ 1 ⇒ j ≡ j a² ≡ a`. -/
theorem res_one {a j : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (h : j * a % 8 = 1) :
    j = a := by
  have e1 := mul_sq_mod (j := j) ha
  have e2 : j * (a * a) % 8 = a % 8 := by
    rw [← mul_assoc, Nat.mul_mod, h]; simp
  omega

#print axioms res_one

/-- Residue `7` (the entering position) only for `j = 8 − a`: `j a ≡ −1 ⇒ j ≡ −a`. -/
theorem res_seven {a j : ℕ} (ha : a % 2 = 1) (ha7 : a ≤ 7) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (h : j * a % 8 = 7) :
    j + a = 8 := by
  have e1 := mul_sq_mod (j := j) ha
  have e2 : j * (a * a) % 8 = 7 * (a % 8) % 8 := by
    rw [← mul_assoc, Nat.mul_mod, h]
  omega

#print axioms res_seven

/-- The mirror reading has residue `7`: `b a ≡ −a² ≡ 7`. -/
theorem mirror_res {a b : ℕ} (ha : a % 2 = 1) (hab : a + b = 8) : b * a % 8 = 7 := by
  have h1 := odd_sq_mod8 ha
  have h2 : b * a + a * a = 8 * a := by
    have : (b + a) * a = 8 * a := by rw [show b + a = 8 by omega]
    linarith [add_mul b a a]
  generalize b * a = X at *
  generalize a * a = Y at *
  omega

#print axioms mirror_res

/-! ## (1) The two zone events of the class -/

/-- **(1a) `u_a` is an opening of `d_a`** [L]: `d_a u_a = k + 1/8` with the natural lap `k = (a² − 1)/8`. -/
theorem opening_at_u (d : ℕ → ℝ) {a : ℕ} (ha : a % 2 = 1) (hda : 0 < d a) :
    ∃ k : ℕ, (8 * (k : ℝ) + 1 = (a : ℝ) ^ 2) ∧ d a * uA d a = (k : ℝ) + 1 / 8 ∧
      uA d a = ((k : ℝ) + 1 / 8) / d a := by
  have h := odd_sq_mod8 ha
  have hk : 8 * (a * a / 8) + 1 = a * a := by omega
  have hkR : 8 * ((a * a / 8 : ℕ) : ℝ) + 1 = (a : ℝ) ^ 2 := by
    have : ((8 * (a * a / 8) + 1 : ℕ) : ℝ) = ((a * a : ℕ) : ℝ) := by rw [hk]
    push_cast at this; rw [sq]; linarith
  have hmul : d a * uA d a = (a : ℝ) ^ 2 / 8 := by unfold uA; field_simp
  refine ⟨a * a / 8, hkR, by rw [hmul]; linarith, ?_⟩
  rw [eq_div_iff hda.ne', mul_comm, hmul]; linarith

#print axioms opening_at_u

/-- **(1b) `w_a` is an entry of `d_b`** [L]: `d_b w_a = k' + 7/8` with the natural lap `k'`, `8 k' = (a − 1)(7 − a)`. -/
theorem entry_at_w (d : ℕ → ℝ) {a b : ℕ} (ha : a % 2 = 1) (hab : a + b = 8) (hdb : 0 < d b) :
    ∃ k' : ℕ, (8 * (k' : ℝ) + 7 = (a : ℝ) * b) ∧ (8 * (k' : ℝ) = ((a : ℝ) - 1) * (7 - a)) ∧
      d b * wA d a b = (k' : ℝ) + 7 / 8 ∧ wA d a b = ((k' : ℝ) + 7 / 8) / d b := by
  have h := mirror_res ha hab
  have hk : 8 * (b * a / 8) + 7 = b * a := by omega
  have hkR : 8 * ((b * a / 8 : ℕ) : ℝ) + 7 = (a : ℝ) * b := by
    have : ((8 * (b * a / 8) + 7 : ℕ) : ℝ) = ((b * a : ℕ) : ℝ) := by rw [hk]
    push_cast at this; linarith
  have hbR : (b : ℝ) = 8 - a := by
    have : ((a + b : ℕ) : ℝ) = 8 := by rw [hab]; norm_num
    push_cast at this; linarith
  have hmul : d b * wA d a b = (a : ℝ) * b / 8 := by unfold wA; field_simp
  refine ⟨b * a / 8, hkR, by rw [hbR] at hkR; linarith, by rw [hmul]; linarith, ?_⟩
  rw [eq_div_iff hdb.ne', mul_comm, hmul]; linarith

#print axioms entry_at_w

/-! ## Windows and the two exact reductions -/

theorem window_on {x u w t : ℝ} (N : ℤ) (hx : 0 ≤ x) (hu : (N : ℝ) + 1 / 8 ≤ x * u)
    (hw : x * w ≤ (N : ℝ) + 7 / 8) (ht : t ∈ Set.Icc u w) : (1 / 8 : ℝ) ≤ distInt (x * t) := by
  apply clear_of_window N
  · linarith [mul_le_mul_of_nonneg_left ht.1 hx]
  · linarith [mul_le_mul_of_nonneg_left ht.2 hx]

#print axioms window_on

theorem lo_inst {x y p n : ℝ} (hy : 0 < y) (h : (8 * n + 1) * y ≤ p * x) : n + 1 / 8 ≤ x * (p / (8 * y)) := by
  rw [show x * (p / (8 * y)) = (p * x) / (8 * y) by ring, le_div_iff₀ (by positivity)]
  linarith

#print axioms lo_inst

theorem hi_inst {x y p n : ℝ} (hy : 0 < y) (h : p * x ≤ (8 * n + 7) * y) : x * (p / (8 * y)) ≤ n + 7 / 8 := by
  rw [show x * (p / (8 * y)) = (p * x) / (8 * y) by ring, div_le_iff₀ (by positivity)]
  linarith

#print axioms hi_inst

/-- **The lower reduction** [L]: `(8n+1) d_a ≤ a² d_j` follows from the core `a (R − 1) − ρ (a² + 8n + 1) ≥ 0`, by the
exact identity `a²(J − ρ)c − (8n+1)(A + ρ)c = c · core` (using `J A = 8n + R`). -/
theorem lower_of_core {c ρ A J n R dj da : ℝ} (hc : 0 < c) (hn : 0 ≤ 8 * n + 1) (hA : 0 ≤ A)
    (hjA : J * A = 8 * n + R) (hdj : |dj - J * c| ≤ ρ * c) (hda : |da - A * c| ≤ ρ * c)
    (hcore : 0 ≤ A * (R - 1) - ρ * (A ^ 2 + 8 * n + 1)) : (8 * n + 1) * da ≤ A ^ 2 * dj := by
  obtain ⟨j0, -⟩ := abs_le.mp hdj
  obtain ⟨-, a1⟩ := abs_le.mp hda
  have h1 : (8 * n + 1) * da ≤ (8 * n + 1) * (A * c + ρ * c) := mul_le_mul_of_nonneg_left (by linarith) hn
  have h2 : A ^ 2 * (J * c - ρ * c) ≤ A ^ 2 * dj := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have key : A ^ 2 * (J * c - ρ * c) - (8 * n + 1) * (A * c + ρ * c) =
      c * (A * (R - 1) - ρ * (A ^ 2 + 8 * n + 1)) := by linear_combination (A * c) * hjA
  have := mul_nonneg hc.le hcore
  linarith

#print axioms lower_of_core

/-- **The upper reduction** [L]: `A B d_j ≤ (8n+7) d_b` follows from the core `B (7 − R) − ρ (8n + 7 + A B) ≥ 0`. -/
theorem upper_of_core {c ρ A B J n R dj db : ℝ} (hc : 0 < c) (hn : 0 ≤ 8 * n + 7) (hAB : 0 ≤ A * B)
    (hjA : J * A = 8 * n + R) (hdj : |dj - J * c| ≤ ρ * c) (hdb : |db - B * c| ≤ ρ * c)
    (hcore : 0 ≤ B * (7 - R) - ρ * (8 * n + 7 + A * B)) : A * B * dj ≤ (8 * n + 7) * db := by
  obtain ⟨-, j1⟩ := abs_le.mp hdj
  obtain ⟨b0, -⟩ := abs_le.mp hdb
  have h1 : A * B * dj ≤ A * B * (J * c + ρ * c) := mul_le_mul_of_nonneg_left (by linarith) hAB
  have h2 : (8 * n + 7) * (B * c - ρ * c) ≤ (8 * n + 7) * db := mul_le_mul_of_nonneg_left (by linarith) hn
  have key : (8 * n + 7) * (B * c - ρ * c) - A * B * (J * c + ρ * c) =
      c * (B * (7 - R) - ρ * (8 * n + 7 + A * B)) := by linear_combination (-(B * c)) * hjA
  have := mul_nonneg hc.le hcore
  linarith

#print axioms upper_of_core

/-! ## The core inequalities (the only place the radius enters; it is a hypothesis of the local statement) -/

/-- Core at the opening, `R ≥ 2`, radius `ρ ≤ 1/14`. -/
theorem core_lower {ρ A J n R : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 14) (hA : 0 ≤ A) (hA7 : A ≤ 7) (hJ7 : J ≤ 7)
    (hR : 2 ≤ R) (hjA : J * A = 8 * n + R) : 0 ≤ A * (R - 1) - ρ * (A ^ 2 + 8 * n + 1) := by
  have hJA : J * A ≤ 7 * A := mul_le_mul_of_nonneg_right hJ7 hA
  have e1 : A ≤ A * (R - 1) := by nlinarith
  have e2 : ρ * (A ^ 2 + 8 * n + 1) ≤ ρ * (A * (A + 7)) := mul_le_mul_of_nonneg_left (by nlinarith) hρ0
  have f : A * (A + 7) ≤ 14 * A := by nlinarith
  have e3 : ρ * (A * (A + 7)) ≤ 1 / 14 * (14 * A) := mul_le_mul hρ f (by positivity) (by norm_num)
  linarith

#print axioms core_lower

/-- Core at the entry, class `a ≤ 5`, `1 ≤ R ≤ 6`, radius `ρ ≤ 1/22`. -/
theorem core_upper_small {ρ A B J n R : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 22) (hA1 : 1 ≤ A) (hA5 : A ≤ 5)
    (hB : B = 8 - A) (hJ7 : J ≤ 7) (hR1 : 1 ≤ R) (hR6 : R ≤ 6) (hjA : J * A = 8 * n + R) :
    0 ≤ B * (7 - R) - ρ * (8 * n + 7 + A * B) := by
  subst hB
  have hJA : J * A ≤ 7 * A := mul_le_mul_of_nonneg_right hJ7 (by linarith)
  have e1 : 8 - A ≤ (8 - A) * (7 - R) := by nlinarith
  have hX : 8 * n + 7 + A * (8 - A) ≤ 15 * A + 6 - A ^ 2 := by nlinarith
  have hX0 : 0 ≤ 15 * A + 6 - A ^ 2 := by nlinarith
  have e2 : ρ * (8 * n + 7 + A * (8 - A)) ≤ ρ * (15 * A + 6 - A ^ 2) := mul_le_mul_of_nonneg_left hX hρ0
  have e3 : ρ * (15 * A + 6 - A ^ 2) ≤ 1 / 22 * (15 * A + 6 - A ^ 2) := mul_le_mul_of_nonneg_right hρ hX0
  -- `22 (8 − A) − (15 A + 6 − A²) = (A − 5)(A − 32) + 10 > 0` for `A ≤ 5`
  nlinarith

#print axioms core_upper_small

/-- Core at the entry, class `a = 7` (`b = 1`): `R = 8 − J`, `n = J − 1`; the core is `J − 1 − ρ (8J + 6)`, which is
`≥ 0` for `ρ ≤ 1/22` exactly because `J ≥ 2` (equality at `J = 2`, `ρ = 1/22`). -/
theorem core_upper_seven {ρ A B J n R : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 22) (hA : A = 7) (hB : B = 1)
    (hn : n = J - 1) (hR : R = 8 - J) (hJ2 : 2 ≤ J) : 0 ≤ B * (7 - R) - ρ * (8 * n + 7 + A * B) := by
  subst hA hB hn hR
  have : ρ * (8 * J + 6) ≤ 1 / 22 * (8 * J + 6) := mul_le_mul_of_nonneg_right hρ (by linarith)
  nlinarith

#print axioms core_upper_seven

/-- Core at the opening for the upper side (the record's left-end statement), `1 ≤ R ≤ 6`, radius `ρ ≤ 1/20`. -/
theorem core_upper_u {ρ A J n R : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 20) (hA1 : 1 ≤ A) (hA7 : A ≤ 7) (hJ7 : J ≤ 7)
    (hR1 : 1 ≤ R) (hR6 : R ≤ 6) (hjA : J * A = 8 * n + R) : 0 ≤ A * (7 - R) - ρ * (8 * n + 7 + A * A) := by
  have hJA : J * A ≤ 7 * A := mul_le_mul_of_nonneg_right hJ7 (by linarith)
  have e1 : A ≤ A * (7 - R) := by nlinarith
  have hX : 8 * n + 7 + A * A ≤ 20 * A := by nlinarith
  have e2 : ρ * (8 * n + 7 + A * A) ≤ ρ * (20 * A) := mul_le_mul_of_nonneg_left hX hρ0
  have e3 : ρ * (20 * A) ≤ 1 / 20 * (20 * A) := mul_le_mul_of_nonneg_right hρ (by linarith)
  linarith

#print axioms core_upper_u

/-! ## Basic consequences of the deformation hypothesis -/

theorem rho_nonneg {c ρ : ℝ} {d : ℕ → ℝ} (hc : 0 < c)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) : 0 ≤ ρ := by
  by_contra h
  push Not at h
  have := mul_neg_of_neg_of_pos h hc
  linarith [abs_nonneg (d 1 - (1 : ℕ) * c), hd 1 le_rfl (by norm_num)]

#print axioms rho_nonneg

/-- Every reading is positive (no runner is stationary relative to the subject) for `ρ < 1`. -/
theorem d_pos {c ρ : ℝ} {d : ℕ → ℝ} (hc : 0 < c) (hρ : ρ < 1)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) {i : ℕ} (h1 : 1 ≤ i) (h7 : i ≤ 7) : 0 < d i := by
  obtain ⟨l, -⟩ := abs_le.mp (hd i h1 h7)
  have hi : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have : c ≤ (i : ℝ) * c := by nlinarith
  have : ρ * c < c := by nlinarith
  linarith

#print axioms d_pos

/-- The residue split `j a = 8 n + R` in the reals. -/
theorem split_real (j a : ℕ) : (j : ℝ) * a = 8 * ((j * a / 8 : ℕ) : ℝ) + ((j * a % 8 : ℕ) : ℝ) := by
  have h := Nat.div_add_mod (j * a) 8
  have : ((8 * (j * a / 8) + j * a % 8 : ℕ) : ℝ) = ((j * a : ℕ) : ℝ) := by rw [h]
  push_cast at this
  linarith

#print axioms split_real

/-! ## (2) The class interval is lonely, radius `1/22` -/

/-- **(2) `interval_lonely`** [L]: for every odd class `a` with mirror `b = 8 − a` and every deformation of radius
`ρ ≤ 1/22` (a hypothesis of this local statement, not a bound on the cascade), every runner of `pds d` is clear on all
of `[a²/(8 d_a), a b/(8 d_b)]`.  Each runner `j` stays in the single window `n = ⌊j a/8⌋` throughout. -/
theorem interval_lonely {c ρ : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c) (hρ : ρ ≤ 1 / 22)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) (ha : a % 2 = 1) (hab : a + b = 8) :
    Set.Icc (uA d a) (wA d a b) ⊆ lonelySet (pds d) := by
  intro t ht
  show Cascade.LonelyAt _ _
  rw [lonelyAt_pds_iff]
  intro j hj1 hj7
  have ha1 : 1 ≤ a := by omega
  have ha7 : a ≤ 7 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb7 : b ≤ 7 := by omega
  have hρ0 := rho_nonneg hc hd
  have hpos := fun i (h1 : 1 ≤ i) (h7 : i ≤ 7) => d_pos hc (by linarith) hd h1 h7
  have hda := hd a ha1 ha7
  have hdb := hd b hb1 hb7
  have hdj := hd j hj1 hj7
  have hR := split_real j a
  have hR0 := res_ne_zero ha hj1 hj7
  have hR8 : j * a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hbR : (b : ℝ) = 8 - a := by
    have : ((a + b : ℕ) : ℝ) = 8 := by rw [hab]; norm_num
    push_cast at this; linarith
  have hA1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hA7 : (a : ℝ) ≤ 7 := by exact_mod_cast ha7
  have hJ7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
  apply window_on ((j * a / 8 : ℕ) : ℤ) (hpos j hj1 hj7).le _ _ ht
  · -- at the opening `u_a`
    rw [Int.cast_natCast]
    unfold uA
    apply lo_inst (hpos a ha1 ha7)
    by_cases hja : j = a
    · have h1 : j * a % 8 = 1 := by rw [hja]; exact odd_sq_mod8 ha
      rw [h1, hja] at hR
      rw [hja]
      push_cast at hR
      apply le_of_eq
      rw [sq]; rw [← hR]
    · have h1 : j * a % 8 ≠ 1 := fun h => hja (res_one ha ha7 hj1 hj7 h)
      have h2 : (2 : ℝ) ≤ ((j * a % 8 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ j * a % 8 by omega)
      exact lower_of_core hc (by positivity) (by positivity) hR hdj hda
        (core_lower hρ0 (by linarith) (by positivity) hA7 hJ7 h2 hR)
  · -- at the entry `w_a`
    rw [Int.cast_natCast]
    unfold wA
    apply hi_inst (hpos b hb1 hb7)
    by_cases hjb : j = b
    · have h1 : j * a % 8 = 7 := by rw [hjb]; exact mirror_res ha hab
      rw [h1, hjb] at hR
      rw [hjb]
      push_cast at hR
      apply le_of_eq
      rw [mul_comm (a : ℝ) b, hR]
    · have h1 : j * a % 8 ≠ 7 := fun h => hjb (by have := res_seven ha ha7 hj1 hj7 h; omega)
      have hR1 : (1 : ℝ) ≤ ((j * a % 8 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j * a % 8 by omega)
      have hR6 : ((j * a % 8 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (show j * a % 8 ≤ 6 by omega)
      have hAB : (0 : ℝ) ≤ a * b := by positivity
      rcases (show a ≤ 5 ∨ a = 7 by omega) with h5 | h7
      · have hA5 : (a : ℝ) ≤ 5 := by exact_mod_cast h5
        exact upper_of_core hc (by positivity) hAB hR hdj hdb
          (core_upper_small hρ0 hρ hA1 hA5 hbR hJ7 hR1 hR6 hR)
      · have hdiv := Nat.div_add_mod (j * a) 8
        rw [h7] at hdiv h1 hR0
        have hb : b = 1 := by omega
        have hj2 : 2 ≤ j := by omega
        have hn : j * 7 / 8 + 1 = j := by omega
        have hr : j * 7 % 8 + j = 8 := by omega
        have hnR : ((j * a / 8 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [h7]; have : ((j * 7 / 8 + 1 : ℕ) : ℝ) = (j : ℝ) := by rw [hn]
          push_cast at this; linarith
        have hrR : ((j * a % 8 : ℕ) : ℝ) = 8 - (j : ℝ) := by
          rw [h7]; have : ((j * 7 % 8 + j : ℕ) : ℝ) = 8 := by rw [hr]; norm_num
          push_cast at this; linarith
        have hJ2 : (2 : ℝ) ≤ j := by exact_mod_cast hj2
        exact upper_of_core hc (by positivity) hAB hR hdj hdb
          (core_upper_seven hρ0 hρ (by rw [h7]; norm_num) (by rw [hb]; norm_num) hnR hrR hJ2)

#print axioms interval_lonely

/-! ## (3) Nonempty iff the ratio condition; the pair law -/

/-- **(3a) `u_le_w_iff`** [L]: `a²/(8 d_a) ≤ a b/(8 d_b) ↔ a d_b ≤ b d_a`. -/
theorem u_le_w_iff (d : ℕ → ℝ) {a b : ℕ} (hda : 0 < d a) (hdb : 0 < d b) (ha1 : 1 ≤ a) :
    uA d a ≤ wA d a b ↔ (a : ℝ) * d b ≤ b * d a := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha1
  unfold uA wA
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : (a : ℝ) ^ 2 * (8 * d b) = (8 * a) * (a * d b) := by ring
  have e2 : (a : ℝ) * b * (8 * d a) = (8 * a) * (b * d a) := by ring
  rw [e1, e2]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc (show (0 : ℝ) < 8 * a by positivity)
    linarith
  · intro h
    exact mul_le_mul_of_nonneg_left h (by positivity)

#print axioms u_le_w_iff

/-! ## (4) The surviving interval is a cell: opener `d_a`, closer `d_b` -/

/-- **(4a) `interval_isCell`** [L]: at radius `ρ ≤ 1/22` (a hypothesis of the local statement), when
`a d_b ≤ b d_a` the interval `[u_a, w_a]` is a cell of `pds d`: lonely, and maximal because runner `a` is in the way
just before `u_a` (its opening) and runner `b` just after `w_a` (its entry).  A touch when `u_a = w_a`. -/
theorem interval_isCell {c ρ : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c) (hρ : ρ ≤ 1 / 22)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) (ha : a % 2 = 1) (hab : a + b = 8)
    (hle : (a : ℝ) * d b ≤ b * d a) : IsCell (pds d) (uA d a) (wA d a b) := by
  have ha1 : 1 ≤ a := by omega
  have ha7 : a ≤ 7 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb7 : b ≤ 7 := by omega
  have hx0 := d_pos hc (by linarith) hd ha1 ha7
  have hy0 := d_pos hc (by linarith) hd hb1 hb7
  obtain ⟨k, -, hku, -⟩ := opening_at_u d ha hx0
  obtain ⟨k', -, -, hkw, -⟩ := entry_at_w d ha hab hy0
  have hsub := interval_lonely hc hρ hd ha hab
  have hle' : uA d a ≤ wA d a b := (u_le_w_iff d hx0 hy0 ha1).mpr hle
  have hA : (0 : ℝ) < a := by exact_mod_cast ha1
  have hu0 : 0 < uA d a := by unfold uA; exact div_pos (pow_pos hA 2) (by linarith)
  have hTx : d a * uA d a = ((k : ℤ) : ℝ) + 1 / 8 := by rw [Int.cast_natCast]; exact hku
  have hSy : d b * wA d a b = ((k' : ℤ) : ℝ) + 7 / 8 := by rw [Int.cast_natCast]; exact hkw
  refine ⟨hu0, hle', hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (uA d a - 1 / (8 * d a)) with hsdef
    have hq : 0 < 1 / (8 * d a) := by positivity
    have hq' : 1 / (8 * d a) < 1 / (4 * d a) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : uA d a - 1 / (4 * d a) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs2 : s < uA d a := max_lt hu' (by linarith)
    have hw := inWay_before_opening hx0 hTx hs1 hs2
    exact not_lonely_of_inWay (mem_pds d ha1 ha7) hw (hsub' ⟨le_max_left _ _, le_trans hs2.le hle'⟩)
  · intro w' hw' hsub'
    set s := min w' (wA d a b + 1 / (8 * d b)) with hsdef
    have hq : 0 < 1 / (8 * d b) := by positivity
    have hq' : 1 / (8 * d b) < 1 / (4 * d b) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : wA d a b < s := lt_min hw' (by linarith)
    have hs2 : s < wA d a b + 1 / (4 * d b) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hw := inWay_after_entry hy0 hSy hs1 hs2
    exact not_lonely_of_inWay (mem_pds d hb1 hb7) hw (hsub' ⟨le_trans hle' hs1.le, min_le_left _ _⟩)

#print axioms interval_isCell

/-- **(4b) `interval_width`** [L]: the width of the surviving cell is entry minus opening,
`w_a − u_a = (k' + 7/8)/d_b − (k + 1/8)/d_a`, with `8k + 1 = a²`, `8k' = (a − 1)(7 − a)`: the `cell_width` of
`LonelyCells` with opener `d_a` and closer `d_b` named. -/
theorem interval_width (d : ℕ → ℝ) {a b : ℕ} (ha : a % 2 = 1) (hab : a + b = 8) (hda : 0 < d a) (hdb : 0 < d b) :
    ∃ k k' : ℕ, 8 * (k : ℝ) + 1 = (a : ℝ) ^ 2 ∧ 8 * (k' : ℝ) = ((a : ℝ) - 1) * (7 - a) ∧
      wA d a b - uA d a = ((k' : ℝ) + 7 / 8) / d b - ((k : ℝ) + 1 / 8) / d a := by
  obtain ⟨k, hk, -, hu⟩ := opening_at_u d ha hda
  obtain ⟨k', -, hk', -, hw⟩ := entry_at_w d ha hab hdb
  exact ⟨k, k', hk, hk', by rw [hu, hw]⟩

#print axioms interval_width

/-- **(4c) Agreement with `LonelyCells`** [L]: for the cell `[u_a, w_a]`, `cell_left_end_is_opening` and
`cell_right_end_is_entry` apply; here the opener and closer are named: `d_a` reads `k + 1/8` at `u_a` and `d_b` reads
`k' + 7/8` at `w_a`. -/
theorem interval_ends {c ρ : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c) (hρ : ρ ≤ 1 / 22)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) (ha : a % 2 = 1) (hab : a + b = 8)
    (hle : (a : ℝ) * d b ≤ b * d a) :
    IsCell (pds d) (uA d a) (wA d a b) ∧ d a ∈ pds d ∧ d b ∈ pds d ∧
      (∃ k : ℕ, d a * uA d a = (k : ℝ) + 1 / 8) ∧ (∃ k' : ℕ, d b * wA d a b = (k' : ℝ) + 7 / 8) := by
  have ha1 : 1 ≤ a := by omega
  have ha7 : a ≤ 7 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb7 : b ≤ 7 := by omega
  obtain ⟨k, -, hku, -⟩ := opening_at_u d ha (d_pos hc (by linarith) hd ha1 ha7)
  obtain ⟨k', -, -, hkw, -⟩ := entry_at_w d ha hab (d_pos hc (by linarith) hd hb1 hb7)
  exact ⟨interval_isCell hc hρ hd ha hab hle, mem_pds d ha1 ha7, mem_pds d hb1 hb7, ⟨k, hku⟩, ⟨k', hkw⟩⟩

#print axioms interval_ends

/-- **(3b) The pair law** [L]: at radius `ρ ≤ 1/22`, for each mirror pair `(a, 8 − a)` (so `(1,7)` and `(3,5)`) one of
the two classes survives as a cell.  The two conditions `a d_b ≤ b d_a` and `b d_a ≤ a d_b` cover every case by
totality of the order. -/
theorem pair_law {c ρ : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c) (hρ : ρ ≤ 1 / 22)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) (ha : a % 2 = 1) (hab : a + b = 8) :
    IsCell (pds d) (uA d a) (wA d a b) ∨ IsCell (pds d) (uA d b) (wA d b a) := by
  have hb : b % 2 = 1 := by omega
  have hba : b + a = 8 := by omega
  rcases le_total ((a : ℝ) * d b) (b * d a) with h | h
  · exact Or.inl (interval_isCell hc hρ hd ha hab h)
  · exact Or.inr (interval_isCell hc hρ hd hb hba h)

#print axioms pair_law

/-- **(3c) Both classes survive iff `a d_b = b d_a`** [L]: the two conditions are not exact negations; their common
boundary is equality. -/
theorem pair_both_iff (d : ℕ → ℝ) {a b : ℕ} (hda : 0 < d a) (hdb : 0 < d b) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) :
    (uA d a ≤ wA d a b ∧ uA d b ≤ wA d b a) ↔ (a : ℝ) * d b = b * d a := by
  rw [u_le_w_iff d hda hdb ha1, u_le_w_iff d hdb hda hb1]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

#print axioms pair_both_iff

/-- **(3d) At the boundary both classes are touches** [L]: `a d_b = b d_a` gives `u_a = w_a` and `u_b = w_b`. -/
theorem pair_touch (d : ℕ → ℝ) {a b : ℕ} (hda : 0 < d a) (hdb : 0 < d b) (h : (a : ℝ) * d b = b * d a) :
    uA d a = wA d a b ∧ uA d b = wA d b a := by
  unfold uA wA
  constructor
  · rw [div_eq_div_iff (by positivity) (by positivity)]; linear_combination (8 * (a : ℝ)) * h
  · rw [div_eq_div_iff (by positivity) (by positivity)]; linear_combination (-8 * (b : ℝ)) * h

#print axioms pair_touch

/-- **(3e) Strict survival of one class empties the other** [L]: `a d_b < b d_a` gives `w_b < u_b`. -/
theorem pair_exclusive (d : ℕ → ℝ) {a b : ℕ} (hda : 0 < d a) (hdb : 0 < d b) (hb1 : 1 ≤ b)
    (h : (a : ℝ) * d b < b * d a) : wA d b a < uA d b := by
  by_contra hc
  push Not at hc
  have := (u_le_w_iff d hdb hda hb1).mp hc
  linarith

#print axioms pair_exclusive

/-! ## The record's statement: the left end, radius `c/20` -/

/-- **`instant_lonely_record`** [L]: at radius `ρ ≤ 1/20` and `a d_b ≤ b d_a`, the opening `u_a` is lonely (the
record's `instant_lonely`, re-derived with the residue window). -/
theorem instant_lonely_record {c ρ : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c) (hρ : ρ ≤ 1 / 20)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ ρ * c) (ha : a % 2 = 1) (hab : a + b = 8)
    (hcond : (a : ℝ) * d b ≤ b * d a) : Cascade.LonelyAt (pds d) (uA d a) := by
  rw [lonelyAt_pds_iff]
  intro j hj1 hj7
  have ha1 : 1 ≤ a := by omega
  have ha7 : a ≤ 7 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb7 : b ≤ 7 := by omega
  have hρ0 := rho_nonneg hc hd
  have hpos := fun i (h1 : 1 ≤ i) (h7 : i ≤ 7) => d_pos hc (by linarith) hd h1 h7
  have hda := hd a ha1 ha7
  have hdj := hd j hj1 hj7
  have hR := split_real j a
  have hR0 := res_ne_zero ha hj1 hj7
  have hR8 : j * a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hA1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hA7 : (a : ℝ) ≤ 7 := by exact_mod_cast ha7
  have hJ7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
  apply clear_of_window ((j * a / 8 : ℕ) : ℤ)
  · rw [Int.cast_natCast]
    unfold uA
    apply lo_inst (hpos a ha1 ha7)
    by_cases hja : j = a
    · have h1 : j * a % 8 = 1 := by rw [hja]; exact odd_sq_mod8 ha
      rw [h1, hja] at hR
      rw [hja]
      push_cast at hR
      apply le_of_eq
      rw [sq]; rw [← hR]
    · have h1 : j * a % 8 ≠ 1 := fun h => hja (res_one ha ha7 hj1 hj7 h)
      have h2 : (2 : ℝ) ≤ ((j * a % 8 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ j * a % 8 by omega)
      exact lower_of_core hc (by positivity) (by positivity) hR hdj hda
        (core_lower hρ0 (by linarith) (by positivity) hA7 hJ7 h2 hR)
  · rw [Int.cast_natCast]
    unfold uA
    apply hi_inst (hpos a ha1 ha7)
    by_cases hjb : j = b
    · have h1 : j * a % 8 = 7 := by rw [hjb]; exact mirror_res ha hab
      rw [h1, hjb] at hR
      rw [hjb]
      push_cast at hR
      have := mul_le_mul_of_nonneg_left hcond (show (0 : ℝ) ≤ a by positivity)
      rw [← hR]
      linarith
    · have h1 : j * a % 8 ≠ 7 := fun h => hjb (by have := res_seven ha ha7 hj1 hj7 h; omega)
      have hR1 : (1 : ℝ) ≤ ((j * a % 8 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j * a % 8 by omega)
      have hR6 : ((j * a % 8 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (show j * a % 8 ≤ 6 by omega)
      have := upper_of_core hc (by positivity) (by positivity) hR hdj hda
        (core_upper_u hρ0 hρ hA1 hA7 hJ7 hR1 hR6 hR)
      rw [sq]; exact this

#print axioms instant_lonely_record

/-- **`pair_law_record`** [L]: the record's `pair_law` in its own form (radius `c/20`, left ends): for each mirror pair
one class instant `u_a` or `u_b` is lonely. -/
theorem pair_law_record {c : ℝ} {d : ℕ → ℝ} {a b : ℕ} (hc : 0 < c)
    (hd : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ c / 20) (ha : a % 2 = 1) (hab : a + b = 8) :
    Cascade.LonelyAt (pds d) (uA d a) ∨ Cascade.LonelyAt (pds d) (uA d b) := by
  have hd' : ∀ j, 1 ≤ j → j ≤ 7 → |d j - j * c| ≤ (1 / 20) * c := fun j h1 h7 => by
    have := hd j h1 h7; linarith
  have hb : b % 2 = 1 := by omega
  have hba : b + a = 8 := by omega
  rcases le_total ((a : ℝ) * d b) (b * d a) with h | h
  · exact Or.inl (instant_lonely_record hc le_rfl hd' ha hab h)
  · exact Or.inr (instant_lonely_record hc le_rfl hd' hb hba h)

#print axioms pair_law_record

/-! ## (5) The exception, understood: the record's interval at radius `c/20`, class 7

`cxD ρ`: `c = 1`, `d 1 = 1 − ρ` (the closer of class 7 slowed), `d 2 = 2 + ρ` (runner 2 sped up), `d j = j` otherwise.
In class 7 runner `2` sits at `7·2/8 = 14/8`, one eighth before its entry `15/8`, and its distance to that entry shrinks
as the interval `[u_7, w_7]` lengthens.  Runner 2 enters before the closer runner 1 exactly when
`7 (2 + ρ) > 15 (1 − ρ)`, i.e. `ρ > 1/22`.  Then the cell of class 7 is `[7/8, 15/(8 (2 + ρ))]`, closed by runner 2: the
isolation is displaced, not destroyed, and the record's right end is the wrong statement. -/

/-- The deformation of the exception. -/
noncomputable def cxD (ρ : ℝ) : ℕ → ℝ := fun j => if j = 1 then 1 - ρ else if j = 2 then 2 + ρ else (j : ℝ)

theorem cxD_one (ρ : ℝ) : cxD ρ 1 = 1 - ρ := by simp [cxD]
theorem cxD_two (ρ : ℝ) : cxD ρ 2 = 2 + ρ := by simp [cxD]
theorem cxD_other (ρ : ℝ) {j : ℕ} (h1 : j ≠ 1) (h2 : j ≠ 2) : cxD ρ j = j := by simp [cxD, h1, h2]

#print axioms cxD_one
#print axioms cxD_two
#print axioms cxD_other

/-- The exception satisfies the deformation hypothesis at radius `ρ` (with `c = 1`). -/
theorem cx_hyp {ρ : ℝ} (hρ0 : 0 ≤ ρ) : ∀ j, 1 ≤ j → j ≤ 7 → |cxD ρ j - j * 1| ≤ ρ * 1 := by
  intro j _ _
  by_cases h1 : j = 1
  · subst h1; rw [cxD_one]; norm_num; rw [abs_of_nonneg hρ0]
  by_cases h2 : j = 2
  · subst h2; rw [cxD_two]; norm_num; rw [abs_of_nonneg hρ0]
  · rw [cxD_other ρ h1 h2]; simp [hρ0]

#print axioms cx_hyp

/-- In the exception class 7 is the surviving class of the pair `(1, 7)` (`7 d_1 ≤ d_7`) and class 1 is empty for
`0 < ρ < 1` (`d_7 > 7 d_1`). -/
theorem cx_class_seven (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (7 : ℝ) * cxD ρ 1 < 1 * cxD ρ 7 ∧ wA (cxD ρ) 1 7 < uA (cxD ρ) 1 := by
  have h7 : cxD ρ 7 = 7 := by rw [cxD_other ρ (by norm_num) (by norm_num)]; norm_num
  have hlt : (7 : ℝ) * cxD ρ 1 < 1 * cxD ρ 7 := by rw [cxD_one, h7]; linarith
  refine ⟨hlt, ?_⟩
  have hda : 0 < cxD ρ 7 := by rw [h7]; norm_num
  have hdb : 0 < cxD ρ 1 := by
    rw [cxD_one]; linarith
  exact pair_exclusive (cxD ρ) (a := 7) (b := 1) hda hdb le_rfl (by exact_mod_cast hlt)

#print axioms cx_class_seven

/-- **(5a) `record_interval_fails`** [L]: for every `1/22 < ρ < 1/8` the record's right end `w_7 = 7/(8 d_1)` of the
class-7 interval is NOT lonely: runner `2` reads `7(2 + ρ)/(8(1 − ρ))`, within `1/8` of lap `2`. -/
theorem record_interval_fails {ρ : ℝ} (h1 : 1 / 22 < ρ) (h2 : ρ < 1 / 8) :
    wA (cxD ρ) 7 1 ∉ lonelySet (pds (cxD ρ)) := by
  intro h
  have h2' := (lonelyAt_pds_iff (cxD ρ) _).mp h 2 (by norm_num) (by norm_num)
  have hx : cxD ρ 2 * wA (cxD ρ) 7 1 = 7 * (2 + ρ) / (8 * (1 - ρ)) := by
    unfold wA; rw [cxD_one, cxD_two]; push_cast; ring
  rw [hx] at h2'
  have hpos : (0 : ℝ) < 8 * (1 - ρ) := by linarith
  have hlo : 15 / 8 < 7 * (2 + ρ) / (8 * (1 - ρ)) := by rw [lt_div_iff₀ hpos]; linarith
  have hhi : 7 * (2 + ρ) / (8 * (1 - ρ)) < 17 / 8 := by rw [div_lt_iff₀ hpos]; linarith
  have hd := distInt_le (7 * (2 + ρ) / (8 * (1 - ρ))) 2
  have : |7 * (2 + ρ) / (8 * (1 - ρ)) - ((2 : ℤ) : ℝ)| < 1 / 8 := by
    rw [abs_lt]; push_cast; constructor <;> linarith
  linarith

#print axioms record_interval_fails

/-- **(5b)** The same at the record's radius `c/20` (`ρ = 1/20`, `c = 1`): the hypothesis holds, class 7 is the
surviving class, and its record interval's right end is not lonely. -/
theorem record_interval_fails_c20 :
    (∀ j, 1 ≤ j → j ≤ 7 → |cxD (1 / 20) j - j * 1| ≤ 1 / 20 * 1) ∧
      (7 : ℝ) * cxD (1 / 20) 1 ≤ 1 * cxD (1 / 20) 7 ∧ wA (cxD (1 / 20)) 7 1 ∉ lonelySet (pds (cxD (1 / 20))) :=
  ⟨cx_hyp (by norm_num), (cx_class_seven _ (by norm_num) (by norm_num)).1.le, record_interval_fails (by norm_num) (by norm_num)⟩

#print axioms record_interval_fails_c20

/-- **(5c) `displaced_cell`** [L]: for `1/22 ≤ ρ ≤ 1/14` the class-7 cell of the exception is `[7/8, 15/(8(2 + ρ))]`:
opened by runner 7 at `u_7 = 7/8` as in the record, closed by runner 2 (entry `15/8`) instead of runner 1.  The
isolation is displaced, not destroyed. -/
theorem displaced_cell {ρ : ℝ} (h1 : 1 / 22 ≤ ρ) (h2 : ρ ≤ 1 / 14) :
    uA (cxD ρ) 7 = 7 / 8 ∧ IsCell (pds (cxD ρ)) (7 / 8) (15 / (8 * (2 + ρ))) := by
  have h7 : cxD ρ 7 = 7 := by rw [cxD_other ρ (by norm_num) (by norm_num)]; norm_num
  have hy : (0 : ℝ) < 2 + ρ := by linarith
  refine ⟨by unfold uA; rw [h7]; norm_num, ?_⟩
  have hle : (7 / 8 : ℝ) ≤ 15 / (8 * (2 + ρ)) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hsub : Set.Icc (7 / 8 : ℝ) (15 / (8 * (2 + ρ))) ⊆ lonelySet (pds (cxD ρ)) := by
    intro t ht
    show Cascade.LonelyAt _ _
    rw [lonelyAt_pds_iff]
    intro j hj1 hj7
    by_cases hj : j = 1
    · subst hj; rw [cxD_one]
      have hw := hi_inst (x := 1 - ρ) (n := 0) hy (p := 15) (by linarith)
      exact window_on 0 (by linarith) (by push_cast; nlinarith) (by push_cast; linarith) ht
    by_cases hj' : j = 2
    · subst hj'; rw [cxD_two]
      have hw := hi_inst (x := 2 + ρ) (n := 1) hy (p := 15) (by linarith)
      exact window_on 1 (by linarith) (by push_cast; nlinarith) (by push_cast; linarith) ht
    · -- `j = 3 … 7`, symbolic in `j`: window `j − 1`
      rw [cxD_other ρ hj hj']
      have hJ3 : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
      have hJ7 : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
      have hw := hi_inst (x := (j : ℝ)) (n := (j : ℝ) - 1) hy (p := 15) (by nlinarith)
      exact window_on ((j : ℤ) - 1) (by linarith) (by push_cast; linarith) (by push_cast; linarith) ht
  refine ⟨by norm_num, hle, hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (7 / 8 - 1 / 56) with hsdef
    have hs1 : (7 / 8 : ℝ) - 1 / (4 * 7) < s := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hs2 : s < 7 / 8 := max_lt hu' (by norm_num)
    have hw := inWay_before_opening (x := 7) (by norm_num) (N := 6) (by norm_num) hs1 hs2
    have hm : (7 : ℝ) ∈ pds (cxD ρ) := by rw [← h7]; exact mem_pds _ (by norm_num) (by norm_num)
    exact not_lonely_of_inWay hm hw (hsub' ⟨le_max_left _ _, le_trans hs2.le hle⟩)
  · intro w' hw' hsub'
    set W := 15 / (8 * (2 + ρ)) with hW
    set s := min w' (W + 1 / (8 * (2 + ρ))) with hsdef
    have hq : 0 < 1 / (8 * (2 + ρ)) := by positivity
    have hq' : 1 / (8 * (2 + ρ)) < 1 / (4 * (2 + ρ)) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : W < s := lt_min hw' (by linarith)
    have hs2 : s < W + 1 / (4 * (2 + ρ)) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hent : (2 + ρ) * W = ((1 : ℤ) : ℝ) + 7 / 8 := by rw [hW]; field_simp; norm_num
    have hw := inWay_after_entry hy hent hs1 hs2
    have hm : 2 + ρ ∈ pds (cxD ρ) := by rw [← cxD_two]; exact mem_pds _ (by norm_num) (by norm_num)
    exact not_lonely_of_inWay hm hw (hsub' ⟨le_trans hle hs1.le, min_le_left _ _⟩)

#print axioms displaced_cell

end Fresh.PairLaw
