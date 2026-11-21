# chambds_lean_gen_v1.py -- generate Fresh/ChamberDatasheet.lean from chambds_instances_v1.json
# (produced by chambds_classes_v1.py).  Structure:
#   1. the datasheet predicates (STANDING: DEFINITION tags),
#   2. the per-kind consumption TEMPLATE theorems (proved once; instances term-apply them),
#      component-level D1/D2 (the S2 scope, fires for all 7797 census classes),
#      chamber-window-uniform D1/D2 (the S1 scope, fires for 0 census classes -- the shape
#      the middle-branch assembly needs; kept with an honest no-firing note),
#      E894 START/END boundary consumption (Fresh.SliverLines; 0 current classes),
#   3. the per-class literal instances (BandCertDataExt pattern), ordered NO-ALIVE-ON-GRID
#      first, then GRID-TOO-COARSE, then SKELETON-UNPROBED, capped by argv[1] (0 = no cap),
#   4. #print axioms lines.
# New file only; nothing existing is edited.
import json, sys

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
LEAN = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/ChamberDatasheet.lean'
JSONF = DIR + 'chambds_instances_v1.json'

HEAD = '''import Mathlib.Tactic
import Fresh.SliverLines

/-!
# The chamber datasheet (Track T Lean landing)

The chamber probe (`experiments/n8/v3_chamber_open_probe_v1_dump.json`; 2,898,013 OPEN
cases deduped to 7,797 classes keyed by (skeleton, kL, kR, cellL, cellR, a, b)) certifies:
no alive 5-reading tuple anywhere on the probed grids (controls: [T 2,898,112/2,898,112]
column-dead; alive-machinery fires on the 96 recorded carves; the GRID-TOO-COARSE classes
are refined-dead in their chamber interiors).  This file is the per-class certificate
emission and its Lean consumption shape.  Data side:
`experiments/n8/chambds_classes_v1.py` (+ `chambds_classes_v1.tsv`,
`chambds_counts_v1.out`); generator of this file: `chambds_lean_gen_v1.py`.

## The two evaluation scopes (both reported; neither buried)

* **S2, component-level at the FIXED edges (A, B)** (the class key's `a`, `b` -- the
  instrument's own COMP-DEAD kill component for every recorded tuple): the lap-j band of
  the component `[A, B]` is `((8j-1)/A, (8j+1)/B)`, nonempty iff `(8j-1)*B < (8j+1)*A`.
  D1: `9*A <= 7*B` (no band ever opens).  D2: with `J` = the largest nonempty band,
  `(8J+1) <= 25*B` (the top band ends at/below 25, so the component is dead over
  [25, inf)).  Classification result: **all 7,797 classes fire the S2 two-line**
  (1,091 D1 + 6,706 D2; 0 OWED, 0 boundary, 0 degenerate), matching the instrument's
  all-COMP-DEAD kill kinds.  Emitted below as the per-class instances
  `chds_* : ColDead50 A B`.
* **S1, chamber-window-UNIFORM** (the two-line evaluated at the class's q-window endpoints
  `[Llo/Rhi, Lhi/Rlo]`, `chamber_test` semantics): D1 iff `9*(8kL+1)*Rhi <= 7*(8kR-1)*Llo`;
  D2 iff `q_min > phi` and `(8*J(q_min)+1)*Rhi <= 25*(8kR-1)`.  The census dumps a case
  ONLY when `chamber_test` returns OPEN for it, so S1 cannot fire on the census --
  **verified 0/7,797 by recomputation, not assumed**.  The templates
  `datasheet_D1_chamber`, `datasheet_D2_chamber` are the S1 consumption shape (kept for
  the middle-branch assembly); no current class instantiates them.

The S1 gap is honest: within a chamber the certifying component's edges vary
(`a_t = (8kL+1)/rho_L`), and the far tuples of the chamber defeat the two-line (the
components are interlacing-killed, i.e. the column dies only through the RUNNING
INTERSECTION of the components' band unions).  The probe's no-alive-on-grid evidence is
the data-side support; the Lean band-union lemma is future work.  The refined-dead classes
carry the additional refined-probe datum in `experiments/n8/chambds_classes_v1.tsv` and
all fire S2-D2 anyway.

## The bridge (STANDING: OWED)

The per-class atoms say: the component `[A, B]` is dead over the [25, 50) column.  The
middle-branch consumption needs, per tuple: (alpha) the Lean K6-component decomposition of
the reading 5-tuple (the `zones_of` / `k6_components` structure of
`v3_chamber_open_probe_v1_enum.py`), (beta) the band-union lemma -- one dead component
kills the column (a live tail lies in EVERY component's band union, so one empty union
empties the intersection; a one-liner GIVEN the decomposition), and (gamma) the
hyperplane-partition step carrying the recorded-tuple deaths to every tuple of the
cell-box (the S1 gap).  None of the three is proved here; none is faked.
-/

namespace Fresh.ChamberDatasheet

/-! ## The datasheet predicates -/

/-- STANDING: DEFINITION -- the lap-j live shape of the component `[a, b]`: the tail `r`
keeps `[a, b]` alive at lap `j` iff `r` lies in the component's lap-j band
`[(8j-1)/a, (8j+1)/b)` (the entry side open -- the search's own mode, matching
`Fresh.SliverLines`). -/
def CompLive (a b r : ℝ) (j : ℕ) : Prop :=
  (8 * (j:ℝ) - 1) / a ≤ r ∧ r < (8 * (j:ℝ) + 1) / b

/-- STANDING: DEFINITION -- the certifying component `[a, b]` is **dead over the
[25, 50) column**: no tail in the column keeps it alive at any lap.  Window convention:
the half-open `[25, 50)` mirrors the instrument's `feasible_set(a, b, 25, 50)` band
inclusion exactly (a band contributes a feasible tail iff `(8j-1)/a < 50` and
`(8j+1)/b > 25`).  This is the datasheet's per-class atom; the bridge to the tuple-level
column predicate is documented above and is NOT proved here. -/
def ColDead50 (a b : ℝ) : Prop :=
  ∀ r : ℝ, (25:ℝ) ≤ r → r < 50 → ∀ j : ℕ, ¬ CompLive a b r j

/-- STANDING: DEFINITION -- the chamber-tuple live shape for a boundary assignment
`(kL, kR)`: the certifying component's edges are `a_t = (8kL+1)/rho_L`, `b_t =
(8kR-1)/rho_R`, so its lap-j band is `[(8j-1)*rho_L/(8kL+1), (8j+1)*rho_R/(8kR-1))` (the
race bands of the instrument's `race_certificate`). -/
def RaceLive (kL kR : ℕ) (rL rR r : ℝ) (j : ℕ) : Prop :=
  (8 * (j:ℝ) - 1) * rL / (8 * (kL:ℝ) + 1) ≤ r ∧ r < (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1)

/-- STANDING: DEFINITION -- the chamber tuple's certifying component is dead over
[25, ∞): no tail `r ≥ 25` keeps it alive at any lap. -/
def RaceColDead (kL kR : ℕ) (rL rR : ℝ) : Prop :=
  ∀ r : ℝ, (25:ℝ) ≤ r → ∀ j : ℕ, ¬ RaceLive kL kR rL rR r j

/-- STANDING: DEFINITION -- the START boundary component `[1, b_t]`, `b_t = (8kR-1)/rho_R`
(`kL` carries the START sentinel 0: no L reading). -/
def StartColDead (kR : ℕ) (rR : ℝ) : Prop :=
  ∀ r : ℝ, (25:ℝ) ≤ r → ∀ j : ℕ,
    ¬ ((8 * (j:ℝ) - 1 : ℝ) ≤ r ∧ r < (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1))

/-- STANDING: DEFINITION -- the END boundary component `[a_t, 7]`, `a_t = (8kL+1)/rho_L`
(`kR` carries the END sentinel 0: no R reading). -/
def EndColDead (kL : ℕ) (rL : ℝ) : Prop :=
  ∀ r : ℝ, (25:ℝ) ≤ r → ∀ j : ℕ,
    ¬ ((8 * (j:ℝ) - 1) * rL / (8 * (kL:ℝ) + 1) ≤ r ∧ r < (8 * (j:ℝ) + 1) / 7)

/-! ## The band-counting core (proved once; the instances term-apply the templates) -/

/-- A band of `[a, b]` that contains a tail `r` between its sides is nonempty as an
interval: `(8j-1)*b < (8j+1)*a`. -/
theorem band_nonempty_of_live {a b r : ℝ} {j : ℕ} (ha0 : 0 < a) (hb0 : 0 < b)
    (hlive : CompLive a b r j) : (8 * (j:ℝ) - 1) * b < (8 * (j:ℝ) + 1) * a := by
  obtain ⟨hlow, hup⟩ := hlive
  have hlow' : 8 * (j:ℝ) - 1 ≤ r * a := (div_le_iff₀ ha0).mp hlow
  have hup' : r * b < 8 * (j:ℝ) + 1 := (lt_div_iff₀ hb0).mp hup
  have h1 : (8 * (j:ℝ) - 1) * b ≤ (r * a) * b := mul_le_mul_of_nonneg_right hlow' hb0.le
  have h2 : (r * a) * b < (8 * (j:ℝ) + 1) * a := by
    calc (r * a) * b = (r * b) * a := by ring
    _ < (8 * (j:ℝ) + 1) * a := mul_lt_mul_of_pos_right hup' ha0
  linarith

/-- Lap 0 is never live for a component `[a, b]` with `1 ≤ b` and a tail `r ≥ 25`. -/
theorem lap0_not_live {a b r : ℝ} (hlive : CompLive a b r 0) (hb1 : (1:ℝ) ≤ b)
    (hr : (25:ℝ) ≤ r) : False := by
  obtain ⟨_, h2⟩ := hlive
  simp at h2
  have hle : b⁻¹ ≤ 1 := inv_le_one hb1
  linarith

/-- **datasheet_D1** (component-level two-line, first line): `9a ≤ 7b` -- no band of
`[a, b]` ever opens (band `j` would force `9(8j-1) < 7(8j+1)`, i.e. `j < 1`), so the
component is dead over the [25, 50) column. -/
theorem datasheet_D1 (a b : ℝ) (ha1 : (1:ℝ) ≤ a) (hab : a ≤ b) (hD1 : (9:ℝ) * a ≤ 7 * b) :
    ColDead50 a b := by
  intro r hr1 _ j hlive
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · exact lap0_not_live hlive (by linarith) hr1
  · exfalso
    have hnb := band_nonempty_of_live ha0 hb0 hlive
    have hscal : (9:ℝ) * ((8 * (j:ℝ) - 1) * b)
        < (7:ℝ) * ((8 * (j:ℝ) + 1) * b) := by
      nlinarith [hnb, mul_le_mul_of_nonneg_right hD1 (by linarith : (0:ℝ) ≤ 8 * (j:ℝ) + 1)]
    have hstep : b * (9 * (8 * (j:ℝ) - 1)) < b * (7 * (8 * (j:ℝ) + 1)) := by
      linarith [hscal]
    have h9lt : (9:ℝ) * (8 * (j:ℝ) - 1) < 7 * (8 * (j:ℝ) + 1) :=
      lt_of_mul_lt_mul_left hstep (le_of_lt hb0)
    have hfin : (16:ℝ) * (j:ℝ) < (16:ℝ) := by linarith
    have hjlt : (j:ℝ) < 1 := by linarith
    have hjnat : j < 1 := by exact_mod_cast hjlt
    omega

/-- **datasheet_D2** (component-level two-line, second line): with `J` the largest
nonempty band (band `J+1` empty, emitted as `a + b ≤ 8(J+1)(b-a)`) and the top band
ending at or below 25 (`8J+1 ≤ 25b`), every live tail forces `j ≤ J` and then `r < 25`
-- the component is dead over the [25, 50) column (indeed over [25, ∞)). -/
theorem datasheet_D2 (a b : ℝ) (J : ℕ) (ha1 : (1:ℝ) ≤ a) (hab : a < b)
    (hJ1 : (a + b : ℝ) ≤ 8 * ((J:ℝ) + 1) * (b - a))
    (hJ2 : (8 * (J:ℝ) + 1) ≤ 25 * b) :
    ColDead50 a b := by
  intro r hr1 _ j hlive
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hba : 0 < b - a := by linarith
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · exact lap0_not_live hlive (by linarith) hr1
  · exfalso
    have hnb := band_nonempty_of_live ha0 hb0 hlive
    have hstep : (8:ℝ) * (j:ℝ) * (b - a) < a + b := by linarith [hnb]
    have hkey : (8:ℝ) * (b - a) * (j:ℝ) < (8:ℝ) * (b - a) * ((J:ℝ) + 1) := by
      linarith [hstep, hJ1]
    have hjltJ : (j:ℝ) < (J:ℝ) + 1 := lt_of_mul_lt_mul_left hkey (le_of_lt hba)
    have hjJ : j ≤ J := by
      have h : j < J + 1 := by exact_mod_cast hjltJ
      omega
    have hp1 : (0:ℝ) ≤ 8 * (j:ℝ) + 1 := by linarith
    have hc : (8:ℝ) * (j:ℝ) + 1 ≤ 8 * (J:ℝ) + 1 := by
      exact_mod_cast (by omega : 8 * j + 1 ≤ 8 * J + 1)
    have htop1 : r < (8 * (j:ℝ) + 1) / b := hlive.2
    have htop2 : (8 * (j:ℝ) + 1) / b ≤ (8 * (J:ℝ) + 1) / b := (div_le_div_right hb0).mpr hc
    have htop3 : (8 * (J:ℝ) + 1) / b ≤ 25 := (div_le_iff₀ hb0).mpr hJ2
    linarith

/-! ## The chamber-window-uniform consumption shape (S1 scope)

The two-line rule evaluated at the chamber's q-interval endpoints, consumed for a chamber
tuple (readings `rL`, `rR` in the L/R window literals).  **No census class instantiates
these** (verified: the census dumps only `chamber_test == OPEN` cases); they are the Lean
shape the middle-branch assembly's band-union step will consume. -/
-- STANDING: OWED (chamber-uniform instances; the band-union lemma is future work)

/-- The S1 sandwich core: a live race band at the tuple, pushed through the window bounds,
is a nonempty band at the chamber's minimal `q_min = Llo/Rhi`. -/
theorem race_sandwich {kL kR : ℕ} {rL rR r Llo Rhi : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hL1 : Llo ≤ rL) (hR2 : rR ≤ Rhi)
    (hposM : 0 < 8 * (kL:ℝ) + 1) (hposN : 0 < 8 * (kR:ℝ) - 1)
    (hlive : RaceLive kL kR rL rR r j) :
    (8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1))
      < (8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1)) := by
  have hj1' : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ 8 * (j:ℝ) - 1 := by linarith
  have hp1 : (0:ℝ) ≤ 8 * (j:ℝ) + 1 := by linarith
  have hN0 : (0:ℝ) < 8 * (kR:ℝ) - 1 := hposN
  have hM0 : (0:ℝ) < 8 * (kL:ℝ) + 1 := hposM
  obtain ⟨hlow, hup⟩ := hlive
  have hlow' : (8 * (j:ℝ) - 1) * rL ≤ r * (8 * (kL:ℝ) + 1) := (div_le_iff₀ hM0).mp hlow
  have hup' : r * (8 * (kR:ℝ) - 1) < (8 * (j:ℝ) + 1) * rR := (lt_div_iff₀ hN0).mp hup
  have hchain : (8 * (j:ℝ) - 1) * rL * (8 * (kR:ℝ) - 1)
      < (8 * (j:ℝ) + 1) * rR * (8 * (kL:ℝ) + 1) := by
    have h1 : (8 * (j:ℝ) - 1) * rL * (8 * (kR:ℝ) - 1)
        ≤ r * (8 * (kL:ℝ) + 1) * (8 * (kR:ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hlow' (le_of_lt hN0)
    have h3 : r * (8 * (kR:ℝ) - 1) * (8 * (kL:ℝ) + 1)
        < (8 * (j:ℝ) + 1) * rR * (8 * (kL:ℝ) + 1) :=
      mul_lt_mul_of_pos_right hup' hM0
    have h2 : r * (8 * (kL:ℝ) + 1) * (8 * (kR:ℝ) - 1)
        < (8 * (j:ℝ) + 1) * rR * (8 * (kL:ℝ) + 1) := by
      calc r * (8 * (kL:ℝ) + 1) * (8 * (kR:ℝ) - 1)
          = r * (8 * (kR:ℝ) - 1) * (8 * (kL:ℝ) + 1) := by ring
        _ < (8 * (j:ℝ) + 1) * rR * (8 * (kL:ℝ) + 1) := h3
    linarith
  have hL : Llo * (8 * (kR:ℝ) - 1) ≤ rL * (8 * (kR:ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hL1 (le_of_lt hN0)
  have hR : rR * (8 * (kL:ℝ) + 1) ≤ Rhi * (8 * (kL:ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hR2 (le_of_lt hM0)
  have hs1 : (8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1))
      ≤ (8 * (j:ℝ) - 1) * (rL * (8 * (kR:ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hL hj0
  have hs2 : (8 * (j:ℝ) + 1) * (rR * (8 * (kL:ℝ) + 1))
      ≤ (8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hR hp1
  linarith [hchain, hs1, hs2]

/-- **datasheet_D1_chamber** (S1, first line): `9*(8kL+1)*Rhi ≤ 7*(8kR-1)*Llo` -- i.e.
`q_min = Llo/Rhi ≥ 9*phi/7` with `phi = (8kL+1)/(8kR-1)` -- kills every chamber tuple's
certifying component: band 1 is already empty at `q_min` and band-nonempty is monotone in
`q`, so no lap-j band ever opens. -/
theorem datasheet_D1_chamber (kL kR : ℕ) (rL rR Llo Rhi r : ℝ)
    (hL1 : Llo ≤ rL) (hR2 : rR ≤ Rhi)
    (hposM : 0 < 8 * (kL:ℝ) + 1) (hposX : 0 < Llo * (8 * (kR:ℝ) - 1))
    (hkr : 1 ≤ 8 * (kR:ℝ) - 1) (hrhi : Rhi ≤ 17) (hrhi0 : 0 ≤ Rhi)
    (hD1 : (9:ℝ) * (Rhi * (8 * (kL:ℝ) + 1)) ≤ 7 * (Llo * (8 * (kR:ℝ) - 1))) :
    RaceColDead kL kR rL rR := by
  intro r hr j hlive
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · exfalso
    have hjz : j = 0 := by omega
    subst hjz
    obtain ⟨_, h2⟩ := hlive
    simp at h2
    have hRhiN : Rhi ≤ 17 * (8 * (kR:ℝ) - 1) := by nlinarith [hrhi, hkr, hrhi0]
    have hup2 : rR / (8 * (kR:ℝ) - 1) ≤ Rhi / (8 * (kR:ℝ) - 1) :=
      (div_le_div_right (by linarith)).mpr hR2
    have hRhi17 : Rhi / (8 * (kR:ℝ) - 1) ≤ 17 := (div_le_iff₀ (by linarith)).mpr hRhiN
    linarith
  · exfalso
    have hposX' : (0:ℝ) < Llo * (8 * (kR:ℝ) - 1) := hposX
    have hs := race_sandwich hj1 hL1 hR2 hposM (by linarith) hlive
    have h1 : (9:ℝ) * ((8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1)))
        < (9:ℝ) * ((8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1))) := by nlinarith
    have h2 : (9:ℝ) * ((8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1)))
        ≤ (7:ℝ) * ((8 * (j:ℝ) + 1) * (Llo * (8 * (kR:ℝ) - 1))) := by
      nlinarith [mul_le_mul_of_nonneg_right hD1 (by linarith : (0:ℝ) ≤ 8 * (j:ℝ) + 1)]
    have hD1' : (9:ℝ) * ((8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1)))
        < (7:ℝ) * ((8 * (j:ℝ) + 1) * (Llo * (8 * (kR:ℝ) - 1))) := by linarith
    have hscal : (Llo * (8 * (kR:ℝ) - 1)) * (9 * (8 * (j:ℝ) - 1))
        < (Llo * (8 * (kR:ℝ) - 1)) * (7 * (8 * (j:ℝ) + 1)) := by linarith [hD1']
    have h9lt : (9:ℝ) * (8 * (j:ℝ) - 1) < 7 * (8 * (j:ℝ) + 1) :=
      lt_of_mul_lt_mul_left hscal (le_of_lt hposX')
    have hfin : (16:ℝ) * (j:ℝ) < (16:ℝ) := by linarith
    have hjlt : (j:ℝ) < 1 := by linarith
    have hjnat : j < 1 := by exact_mod_cast hjlt
    omega

/-- The S1 band-counting core: past the chamber's `Jm` no band is nonempty at `q_min`
(band nonemptiness decreases in `q`, and `q_min ≥ phi` via `hneg`). -/
theorem band_count (kL kR : ℕ) (Llo Rhi : ℝ) (Jm j : ℕ)
    (hposX : 0 < Llo * (8 * (kR:ℝ) - 1)) (hposY : 0 < Rhi * (8 * (kL:ℝ) + 1))
    (hneg : Rhi * (8 * (kL:ℝ) + 1) ≤ Llo * (8 * (kR:ℝ) - 1))
    (hband0 : (8 * ((Jm:ℝ) + 1) - 1) * (Llo * (8 * (kR:ℝ) - 1))
              ≥ (8 * ((Jm:ℝ) + 1) + 1) * (Rhi * (8 * (kL:ℝ) + 1)))
    (hj : Jm + 1 ≤ j)
    (hb : (8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1))
          < (8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1))) : False := by
  have hjc : (Jm:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast hj
  have hprod : ((j:ℝ) - ((Jm:ℝ) + 1)) * (Rhi * (8 * (kL:ℝ) + 1) - Llo * (8 * (kR:ℝ) - 1))
      ≤ 0 := by
    nlinarith [hjc, hneg, hposX, hposY]
  have hdec : (8 * (j:ℝ) + 1) * (Rhi * (8 * (kL:ℝ) + 1))
        - (8 * (j:ℝ) - 1) * (Llo * (8 * (kR:ℝ) - 1))
      ≤ (8 * ((Jm:ℝ) + 1) + 1) * (Rhi * (8 * (kL:ℝ) + 1))
        - (8 * ((Jm:ℝ) + 1) - 1) * (Llo * (8 * (kR:ℝ) - 1)) := by
    nlinarith [hprod, hposX, hposY]
  linarith [hdec, hband0, hb]

/-- **datasheet_D2_chamber** (S1, second line): with `Jm = J(q_min)` (band `Jm+1` empty at
`q_min`, emitted as `hband0`) and the D2 line `(8*Jm+1)*Rhi ≤ 25*(8kR-1)`, every chamber
tuple's certifying component is dead over [25, ∞). -/
theorem datasheet_D2_chamber (kL kR : ℕ) (rL rR Llo Rhi r : ℝ) (Jm : ℕ)
    (hL1 : Llo ≤ rL) (hL2 : rL ≤ Lhi) (hR2 : rR ≤ Rhi)
    (hposM : 0 < 8 * (kL:ℝ) + 1) (hposX : 0 < Llo * (8 * (kR:ℝ) - 1))
    (hposY : 0 < Rhi * (8 * (kL:ℝ) + 1))
    (hkr : 1 ≤ 8 * (kR:ℝ) - 1) (hrhi : Rhi ≤ 17) (hrhi0 : 0 ≤ Rhi)
    (hneg : Rhi * (8 * (kL:ℝ) + 1) ≤ Llo * (8 * (kR:ℝ) - 1))
    (hband0 : (8 * ((Jm:ℝ) + 1) - 1) * (Llo * (8 * (kR:ℝ) - 1))
              ≥ (8 * ((Jm:ℝ) + 1) + 1) * (Rhi * (8 * (kL:ℝ) + 1)))
    (hD2 : (8 * (Jm:ℝ) + 1) * Rhi ≤ 25 * (8 * (kR:ℝ) - 1)) :
    RaceColDead kL kR rL rR := by
  intro r hr j hlive
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · exfalso
    have hjz : j = 0 := by omega
    subst hjz
    obtain ⟨_, h2⟩ := hlive
    simp at h2
    have hRhiN : Rhi ≤ 17 * (8 * (kR:ℝ) - 1) := by nlinarith [hrhi, hkr, hrhi0]
    have hup2 : rR / (8 * (kR:ℝ) - 1) ≤ Rhi / (8 * (kR:ℝ) - 1) :=
      (div_le_div_right (by linarith)).mpr hR2
    have hRhi17 : Rhi / (8 * (kR:ℝ) - 1) ≤ 17 := (div_le_iff₀ (by linarith)).mpr hRhiN
    linarith
  · rcases Nat.lt_or_ge j (Jm + 1) with hlow | hhigh
    · exfalso
      have hp1 : (0:ℝ) ≤ 8 * (j:ℝ) + 1 := by linarith
      have hc : (8:ℝ) * (j:ℝ) + 1 ≤ 8 * (Jm:ℝ) + 1 := by
        exact_mod_cast (by omega : 8 * j + 1 ≤ 8 * Jm + 1)
      have ht1 : (8 * (j:ℝ) + 1) * rR ≤ (8 * (j:ℝ) + 1) * Rhi :=
        mul_le_mul_of_nonneg_left hR2 hp1
      have ht2 : (8 * (j:ℝ) + 1) * Rhi ≤ (8 * (Jm:ℝ) + 1) * Rhi :=
        mul_le_mul_of_nonneg_right hc (le_of_lt hrhi0)
      have htop : r < (25:ℝ) := by
        have h1 : r < (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1) := hlive.2
        have h2 : (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1)
            ≤ (8 * (Jm:ℝ) + 1) * Rhi / (8 * (kR:ℝ) - 1) :=
          (div_le_div_right (by linarith)).mpr (by linarith [ht1, ht2])
        have h3 : (8 * (Jm:ℝ) + 1) * Rhi / (8 * (kR:ℝ) - 1) ≤ 25 :=
          (div_le_iff₀ (by linarith)).mpr hD2
        linarith
      linarith [hr]
    · exfalso
      have hs := race_sandwich hj1 hL1 hR2 hposM (by linarith) hlive
      exact band_count kL kR Llo Rhi Jm j hposX hposY hneg hband0 hhigh hs

/-! ## The E894 boundary-line consumption (START / END)

The boundary components' sliver lines (`Fresh.SliverLines`): START `b ≥ 33/31` kills
`[1, b_t]`, END `a ≤ 1225/177` kills `[a_t, 7]`, at the chamber window via the emitted
literal lines (`33*Rhi ≤ 31*(8kR-1)`, `177*(8kL+1) ≤ 1225*Llo`).  **No census class
instantiates these** -- the v2 instrument routes boundary certificates out of the OPEN
census (expected 0); the templates are the datasheet's boundary route. -/
-- STANDING: OWED (boundary instances; 0 current classes)

theorem datasheet_E894_start (kR : ℕ) (rR Rhi : ℝ)
    (hR2 : rR ≤ Rhi) (hpos : 0 < rR) (hposN : 0 < 8 * (kR:ℝ) - 1)
    (hline : (33:ℝ) * Rhi ≤ 31 * (8 * (kR:ℝ) - 1)) :
    StartColDead kR rR := by
  intro r hr j hlive
  have hb : (33:ℝ) / 31 ≤ (8 * (kR:ℝ) - 1) / rR := by
    rw [le_div_iff₀ hpos]
    have h1 : (33:ℝ) * rR ≤ (31:ℝ) * (8 * (kR:ℝ) - 1) := by nlinarith [hline, hR2]
    nlinarith [h1]
  have hup' : r < (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1) := by
    obtain ⟨hup, _⟩ := hlive
    have hid : (8 * (j:ℝ) + 1) / ((8 * (kR:ℝ) - 1) / rR)
        = (8 * (j:ℝ) + 1) * rR / (8 * (kR:ℝ) - 1) := by field_simp
    rw [hid]
    exact hup
  obtain ⟨_, hlow⟩ := hlive
  exact Fresh.SliverLines.sliverStart_dead ((8 * (kR:ℝ) - 1) / rR) r hb hr j ⟨hup', hlow⟩

theorem datasheet_E894_end (kL : ℕ) (rL Llo Lhi : ℝ)
    (hL1 : Llo ≤ rL) (hL2 : rL ≤ Lhi) (hpos : 0 < rL)
    (hLhi1 : Lhi ≤ 8 * (kL:ℝ) + 1)
    (hline : (177:ℝ) * (8 * (kL:ℝ) + 1) ≤ 1225 * Llo) :
    EndColDead kL rL := by
  intro r hr j hlive
  have ha1 : (1:ℝ) ≤ (8 * (kL:ℝ) + 1) / rL := by
    rw [le_div_iff₀ hpos]
    nlinarith [hL2, hLhi1]
  have ha : (8 * (kL:ℝ) + 1) / rL ≤ (1225:ℝ) / 177 := by
    rw [div_le_iff₀ hpos]
    have h1 : (1225:ℝ) * Llo ≤ (1225:ℝ) * rL := by nlinarith [hL1]
    nlinarith [hline, h1]
  have hlow' : (8 * (j:ℝ) - 1) * rL / (8 * (kL:ℝ) + 1) ≤ r := by
    obtain ⟨hlow, _⟩ := hlive
    have hid : (8 * (j:ℝ) - 1) / ((8 * (kL:ℝ) + 1) / rL)
        = (8 * (j:ℝ) - 1) * rL / (8 * (kL:ℝ) + 1) := by field_simp
    rw [hid]
    exact hlow
  obtain ⟨_, hup⟩ := hlive
  exact Fresh.SliverLines.sliverEnd_dead ((8 * (kL:ℝ) + 1) / rL) r ha1 ha hr j ⟨hlow', hup⟩

/-! ## The per-class instances (the emitted datasheet)

One theorem per census class, term-applying the S2 template at the class's literal
component edges (the emission is capped only by compile budget; the order is
NO-ALIVE-ON-GRID first, then GRID-TOO-COARSE, then SKELETON-UNPROBED). -/

'''

TAIL = '''
/-! ## The axiom footprint -/

#print axioms datasheet_D1
#print axioms datasheet_D2
#print axioms datasheet_D1_chamber
#print axioms datasheet_D2_chamber
#print axioms datasheet_E894_start
#print axioms datasheet_E894_end
{axioms_inst}

end Fresh.ChamberDatasheet
'''

def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 0   # 0 = no cap
    d = json.load(open(JSONF))
    ins = d['instances']
    order = {'NO-ALIVE-ON-GRID': 0, 'GRID-TOO-COARSE': 1, 'SKELETON-UNPROBED': 2}
    tv = {}
    with open(DIR + 'chambds_classes_v1.tsv') as f:
        for line in f:
            if line.startswith('#'):
                continue
            p = line.rstrip('\n').split('\t')
            tv[int(p[0])] = (p[9], int(p[8]))   # verdict, n_cases
    ins.sort(key=lambda x: (order.get(tv.get(x['idx'], ('?', 0))[0], 3),
                            -tv.get(x['idx'], (0, 0))[1], x['idx']))
    n_emit = len(ins) if cap <= 0 else min(cap, len(ins))
    parts = [HEAD]
    for x in ins[:n_emit]:
        idx = x['idx']; kind = x['kind']; a = x['a']; b = x['b']; J = x.get('Jm', '')
        verdict, ncases = tv.get(idx, ('?', 0))
        if kind == 'D1':
            parts.append('/-- ds#%d | %s | kL=%s kR=%s | a=%s b=%s | D1 (9a <= 7b) | %s cases | %s -/\n'
                         % (idx, x['skel'], x['kL'], x['kR'], a, b, ncases, verdict))
            parts.append('theorem chds_%d : ColDead50 (%s : ℝ) (%s : ℝ) :=\n'
                         '  datasheet_D1 (%s : ℝ) (%s : ℝ) (by norm_num) (by norm_num) (by norm_num)\n'
                         % (idx, a, b, a, b))
        else:
            parts.append('/-- ds#%d | %s | kL=%s kR=%s | a=%s b=%s | J=%s | %s cases | %s -/\n'
                         % (idx, x['skel'], x['kL'], x['kR'], a, b, J, ncases, verdict))
            parts.append('theorem chds_%d : ColDead50 (%s : ℝ) (%s : ℝ) :=\n'
                         '  datasheet_D2 (%s : ℝ) (%s : ℝ) %s (by norm_num) (by norm_num)'
                         ' (by norm_num) (by norm_num)\n'
                         % (idx, a, b, a, b, J))
    axioms_inst = ''
    if n_emit > 0:
        first = ins[0]['idx']; last = ins[n_emit - 1]['idx']
        axioms_inst = '#print axioms chds_%d\n#print axioms chds_%d' % (first, last)
    src = ''.join(parts) + TAIL.format(axioms_inst=axioms_inst)
    open(LEAN, 'w').write(src)
    print('wrote %s: %d instances of %d (D1 %d / D2 %d)'
          % (LEAN, n_emit, len(ins),
             sum(1 for x in ins[:n_emit] if x['kind'] == 'D1'),
             sum(1 for x in ins[:n_emit] if x['kind'] == 'D2')))

if __name__ == '__main__':
    main()
