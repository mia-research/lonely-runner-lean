import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.KTaxonomy

/-!
# The filter-completeness skeleton (log E802 item 6), native

Written 2026-11-06.  New file; nothing existing is edited.  Built on `Fresh.KTaxonomy`
(`StabilizesAtMin`, the sorter, `openersAt_lap_ge_one`, `distInt_ge_eighth_iff`),
`Fresh.Cascade` (`cascadeFixes_iff_isolation`, `exists_dmin`), `Fresh.CatalogueCoalescence`
(`reducedAdmissible_iff_not_isolation`) and `Fresh.ShapeRoot` (`ShapeAdmissible`,
`shapeUp_isolation`, `shapeUp_or_admissible`, `reduced_imp_shapeAdmissible`).

E802 item 6, in the cascade's own terms, with the taxonomy coordinate `R = 8·(d_min reading)·t`
(the taxonomy's `R` after normalising the least reading to 1; `W_m = [8m+1, 8m+7]`):

* the window law: the least reading (reading 1) is clear at `t` iff `R mod 8 ∈ [1,7]`
  (`dmin_clear_iff_window`) — proved, elementary from `distInt`;
* every landing lies in some window and none in the gap `(7,9)` (`landing_window`,
  `window_avoids_gap`) — proved;
* a no-move cascade lands at `R = 1` exactly (`noMove_R_one`) — proved (audit: all no-move
  rows land at `R = 1`);
* reading `d_min` as opener anchors `R` at a window's left end `8j+1` with `j ≥ 1`, so it
  cannot open `W₀` (`dmin_opener_left_end`, `dmin_cannot_open_W0`) — proved (the anchor law is
  opener-sided, catalogue audit [T 52000/52000]; the converse — an anchor at reading `d_min`
  forcing `d_min` to be the opener — is not definitionally true and is not claimed);
* so the 14 labels of E369/E802 (no move; opener readings in `W₀`; opener readings in `W₁`)
  are complete exactly when every arrangement lands below 17: `OutcomeLabelComplete ↔
  CascadeLandsBelow17` (`outcomeLabelComplete_iff`, `allLabelled_iff_allLandBelow17`) — proved,
  given the label definition as "no move or in `W₀ ∪ W₁`"; the restriction to `W₀ ∪ W₁` itself
  is the owed content (E802: "the list of 14 is complete exactly when every arrangement lands
  below 17").

The bridge to the shape filter (`FilterShapeBridge`, OWED): E802's completeness statement is
internal to the cascade language and is proved above; the shape-side connection splits into a
proved fragment (no counterexamples survive: `LonelyRunnerEight` and emptiness of
`ReducedAdmissible` follow from all-land-below-17; every cascade fixes under shape
completeness) and two owed halves.  Record (2026-11-06): the two regional halves are
computationally certified — the G1 c(1) box sweep over all 74,613 J2 tuples (74,527 no-chain,
73 chained and killed by the W₁ joint search, 0 joint hits) supports "W₀ covered ⇒ W₁ open"
at box level, and outside J2 landing ∈ W₁ ⟺ [1,7] carved empty [P, Localisation], a carve
capping `ρ₇ ≤ 511/31 < 17`; the landing supremum over `ρ₇ ≤ 25` is `26433/2209` (E368, tree,
float-LP).  None of this is derived, and nothing here imports it.

Certificate spine (J, 2026-11-06): the Nov-4 envelope and box certificate systems do not nest,
so one spine must carry the whole argument; the box spine is the one that tiles J2.
`FilterCompleteVia` relativises the completeness target to a chosen spine `C`.
-/

open Classical

namespace Fresh.FilterSkeleton

open Fresh Fresh.Cascade Fresh.KTaxonomy

variable {ds : Finset ℝ} {t₀ : ℝ} {N : ℕ}

/-! ## The window law for reading 1 (E802 item 6) -/

/-- Phase to `R`: a phase window `[j+1/8, j+7/8]` is the `R`-window `[8j+1, 8j+7]`. -/
theorem window_R_of_phase {x : ℝ} {j : ℤ} (h1 : ((j : ℝ)) + 1 / 8 ≤ x)
    (h2 : x ≤ ((j : ℝ)) + 7 / 8) :
    8 * x ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) := by
  have h8 : (0 : ℝ) < 8 := by norm_num
  have c1 : 8 * (((j : ℝ)) + 1 / 8) ≤ 8 * x := mul_le_mul_of_nonneg_left h1 h8.le
  have c2 : 8 * x ≤ 8 * (((j : ℝ)) + 7 / 8) := mul_le_mul_of_nonneg_left h2 h8.le
  have e1 : 8 * (((j : ℝ)) + 1 / 8) = (((8 * j : ℤ) : ℝ) + 1) := by push_cast; try ring
  have e2 : 8 * (((j : ℝ)) + 7 / 8) = (((8 * j : ℤ) : ℝ) + 7) := by push_cast; try ring
  exact Set.mem_Icc.mpr ⟨by linarith [c1, e1], by linarith [c2, e2]⟩

#print axioms window_R_of_phase

theorem phase_of_window_R {x : ℝ} {j : ℤ}
    (h : 8 * x ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)) :
    ((j : ℝ)) + 1 / 8 ≤ x ∧ x ≤ ((j : ℝ)) + 7 / 8 := by
  rw [Set.mem_Icc] at h
  obtain ⟨h1, h2⟩ := h
  have h8 : (0 : ℝ) < 8 := by norm_num
  have e1 : (((8 * j : ℤ) : ℝ) + 1) = 8 * (((j : ℝ)) + 1 / 8) := by push_cast; try ring
  have e2 : (((8 * j : ℤ) : ℝ) + 7) = 8 * (((j : ℝ)) + 7 / 8) := by push_cast; try ring
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨by nlinarith [h1, h8], by nlinarith [h2, h8]⟩

#print axioms phase_of_window_R

/-- **The window law** (E802 item 6): reading 1 (the `d_min` reading) is clear at `t` exactly
when `R = 8·m·t` lies in a window `[8j+1, 8j+7]` — "R mod 8 ∈ [1,7]". -/
theorem dmin_clear_iff_window {m t : ℝ} :
    (1 / 8 ≤ distInt (m * t)) ↔
      ∃ j : ℤ, 8 * m * t ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) := by
  have e : 8 * m * t = 8 * (m * t) := by ring
  rw [e]
  constructor
  · intro h
    obtain ⟨j, h1, h2⟩ := (distInt_ge_eighth_iff (m * t)).mp h
    exact ⟨j, window_R_of_phase h1 h2⟩
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := phase_of_window_R hj
    exact (distInt_ge_eighth_iff (m * t)).mpr ⟨j, h1, h2⟩

#print axioms dmin_clear_iff_window

/-- Every landing lies in some window of reading 1. -/
theorem landing_window (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (hS : StabilizesAtMin ds t₀ N) :
    ∃ j : ℤ, 8 * m * cascadeSeq ds t₀ N ∈
      Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) :=
  dmin_clear_iff_window.mp (stabilizesAtMin_lonely hpos hS m hm)

#print axioms landing_window

/-- No window point lies in the gap `(7,9)`: no landing lies strictly between `W₀` and `W₁`. -/
theorem window_avoids_gap {x : ℝ} {j : ℤ}
    (h : 8 * x ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)) :
    ¬ (7 < 8 * x ∧ 8 * x < 9) := by
  rw [Set.mem_Icc] at h
  push_cast at h
  obtain ⟨h1, h2⟩ := h
  rintro ⟨g1, g2⟩
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hjm : j ≤ -1 := by omega
    have hjr : ((j : ℝ)) ≤ -1 := by exact_mod_cast hjm
    have hm8 := mul_le_mul_of_nonneg_left hjr (by norm_num : (0 : ℝ) ≤ 8)
    have e8 : (8 : ℝ) * (-1) = -8 := by norm_num
    linarith
  · subst hj
    norm_num at h1 h2
    linarith
  · have hjm : 1 ≤ j := by omega
    have hjr : (1 : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hjm
    have hm8 := mul_le_mul_of_nonneg_left hjr (by norm_num : (0 : ℝ) ≤ 8)
    have e8 : (8 : ℝ) * 1 = 8 := by norm_num
    linarith

#print axioms window_avoids_gap

/-- The landing is in one of the first two windows `W₀ ∪ W₁` (`R < 17`; the windows are
`[8j+1, 8j+7]` with `j = 0` or `j = 1`). -/
-- STANDING: DEFINITION
def InWindow01 (m T : ℝ) : Prop :=
  ∃ j : ℤ, 0 ≤ j ∧ j ≤ 1 ∧ 8 * m * T ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7)

/-- A no-move cascade starts at the bound, and `R = 1` there exactly (audit: every no-move row
lands at `R = 1`). -/
theorem noMove_R_one {m : ℝ} (hm : 0 < m) : InWindow01 m (1 / (8 * m)) := by
  refine ⟨0, by norm_num, by norm_num, ?_⟩
  have e : 8 * m * (1 / (8 * m)) = 1 := by
    field_simp
  rw [e]
  exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩

#print axioms noMove_R_one

/-- The anchor law, `d_min` side: if the least reading is the opener, the landing is a window
left end `8j+1` with `j ≥ 1` (audit: `R·ρ_opener = 8·lap + 1`, opener-sided). -/
theorem dmin_opener_left_end (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) {m : ℝ} (hm : m ∈ ds) (hd : m ∈ openersAt ds t₀ N) :
    ∃ j : ℤ, 1 ≤ j ∧
      8 * m * cascadeSeq ds t₀ N = (((8 * j : ℤ) : ℝ) + 1) := by
  obtain ⟨k, hk1, hk2⟩ := Fresh.KTaxonomy.openersAt_lap_ge_one hpos hbd hS hd
  refine ⟨k, hk1, ?_⟩
  have e : 8 * m * cascadeSeq ds t₀ N = 8 * (m * cascadeSeq ds t₀ N) := by ring
  rw [e, hk2]
  push_cast
  ring

#print axioms dmin_opener_left_end

/-- Reading 1 cannot open `W₀` (E802 item 6: "rank 1 cannot open W₀"; E369's 14 = 1 + 6 + 7
uses exactly this). -/
theorem dmin_cannot_open_W0 (hpos : ∀ d ∈ ds, 0 < d) (hbd : ∀ d ∈ ds, 1 / 8 ≤ d * t₀)
    (hS : StabilizesAtMin ds t₀ N) {m : ℝ} (hm : m ∈ ds) (hd : m ∈ openersAt ds t₀ N) :
    ¬ (8 * m * cascadeSeq ds t₀ N ∈ Set.Icc (1 : ℝ) 7) := by
  obtain ⟨j, hj1, hj2⟩ := dmin_opener_left_end hpos hbd hS hm hd
  rintro ⟨h1, h2⟩
  rw [hj2] at h2
  push_cast at h2
  have hjr : (1 : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hj1
  linarith

#print axioms dmin_cannot_open_W0

/-! ## Lands below 17 and the outcome labels -/

/-- The cascade from the bound `1/(8·d_min)` lands, and the landing is in `W₀ ∪ W₁`
("lands below 17"). -/
-- STANDING: DEFINITION
def CascadeLandsBelow17 (ds : Finset ℝ) (m : ℝ) : Prop :=
  ∃ N, StabilizesAtMin ds (1 / (8 * m)) N ∧
    InWindow01 m (cascadeSeq ds (1 / (8 * m)) N)

/-- The outcome labels are complete: the cascade lands and the outcome is the no-move label or
a window label of `W₀ ∪ W₁` (E369/E802: no move; opener readings in `W₀`; opener readings in
`W₁` — 1 + 6 + 7 labels, "rank 1 in `W₀`" excluded by `dmin_cannot_open_W0`). -/
-- STANDING: DEFINITION
def OutcomeLabelComplete (ds : Finset ℝ) (m : ℝ) : Prop :=
  ∃ N, StabilizesAtMin ds (1 / (8 * m)) N ∧
    (N = 0 ∨ InWindow01 m (cascadeSeq ds (1 / (8 * m)) N))

/-- E802 item 6's equivalence, native: the labels are complete exactly when the cascade lands
below 17 (no move already lands at `R = 1`). -/
theorem outcomeLabelComplete_iff (hm : 0 < m) :
    OutcomeLabelComplete ds m ↔ CascadeLandsBelow17 ds m := by
  constructor
  · rintro ⟨N, hS, h0 | hw⟩
    · exact ⟨N, hS, by rw [h0]; exact noMove_R_one hm⟩
    · exact ⟨N, hS, hw⟩
  · rintro ⟨N, hS, hw⟩
    exact ⟨N, hS, Or.inr hw⟩

#print axioms outcomeLabelComplete_iff

/-- All arrangements land below 17. -/
-- STANDING: DEFINITION
def AllArrangementsLandBelow17 : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    CascadeLandsBelow17 (disparitySet v k) m

/-- All arrangements are labelled (the filter sorts every arrangement into the 14). -/
-- STANDING: DEFINITION
def AllArrangementsLabelled : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    OutcomeLabelComplete (disparitySet v k) m

theorem allLabelled_iff_allLandBelow17 :
    AllArrangementsLabelled ↔ AllArrangementsLandBelow17 := by
  constructor
  · intro h v hv k m hm
    have hpos := Fresh.Cascade.disparitySet_pos hv k
    have hmpos : 0 < m := hpos m (Finset.mem_coe.mpr hm.1)
    exact (outcomeLabelComplete_iff hmpos).mp (h v hv k m hm)
  · intro h v hv k m hm
    have hpos := Fresh.Cascade.disparitySet_pos hv k
    have hmpos : 0 < m := hpos m (Finset.mem_coe.mpr hm.1)
    obtain ⟨N, hS, hw⟩ := h v hv k m hm
    exact ⟨N, hS, Or.inr hw⟩

#print axioms allLabelled_iff_allLandBelow17

/-! ## The proved fragments of the shape bridge -/

/-- Landing below 17 gives isolation (a landing is lonely by the construction theorem). -/
theorem isolation_of_cascadeLandsBelow17 {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8}
    {m : ℝ} (hm : IsDmin v k m) (h : CascadeLandsBelow17 (disparitySet v k) m) :
    Isolation v k := by
  obtain ⟨N, hS, _⟩ := h
  exact (Fresh.Cascade.cascadeFixes_iff_isolation hv hm).mpr
    (Fresh.KTaxonomy.stabilizesAtMin_imp_cascadeFixes hS)

#print axioms isolation_of_cascadeLandsBelow17

/-- "Every arrangement lands below 17" contains existence for every arrangement (E802 item 6's
caveat: the statement is order 8 with a stated place, not a reduction of it). -/
theorem lonelyRunnerEight_of_allLandBelow17 (h : AllArrangementsLandBelow17) :
    LonelyRunnerEight := by
  intro v hv k
  obtain ⟨m, hm⟩ := Fresh.Cascade.exists_dmin (v := v) k
  exact isolation_of_cascadeLandsBelow17 hv hm (h v hv k m hm)

#print axioms lonelyRunnerEight_of_allLandBelow17

/-! (Transfer copy: the shape-bridge fragments and `FilterShapeBridge` are omitted here; they
need `Fresh.CatalogueCoalescence` and `Fresh.ShapeRoot`, which are not part of the kernel.) -/

/-- A certificate spine: a predicate on (readings, landing) certifying the outcome.  The Nov-4
envelope and box systems do not nest (J, 2026-11-06), so ONE spine must carry the whole
argument; the box spine is the one that tiles J2.  `FilterCompleteVia C` relativises the
completeness target to the chosen spine `C`. -/
-- STANDING: DEFINITION
def FilterCompleteVia (C : Finset ℝ → ℝ → Prop) : Prop :=
  ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
    ∃ N, StabilizesAtMin (disparitySet v k) (1 / (8 * m)) N ∧
      C (disparitySet v k) (cascadeSeq (disparitySet v k) (1 / (8 * m)) N) ∧
      InWindow01 m (cascadeSeq (disparitySet v k) (1 / (8 * m)) N)

/-- With the box spine `C` chosen, `FilterCompleteVia C` implies every arrangement lands below
17 (`AllArrangementsLandBelow17`), hence every fragment above; `FilterCompleteVia C` itself is
the owed spine statement. -/
theorem allLandBelow17_of_filterCompleteVia {C : Finset ℝ → ℝ → Prop}
    (h : FilterCompleteVia C) : AllArrangementsLandBelow17 := by
  intro v hv k m hm
  obtain ⟨N, hS, _, hw⟩ := h v hv k m hm
  exact ⟨N, hS, hw⟩

#print axioms allLandBelow17_of_filterCompleteVia

/-! ## The box-spine covering step (rule 7 tag) -/

/-- The box-spine covering claim of the J2 filter (2026-11-06 G1 c(1) sweep: 74,613 closed
boxes; 74,527 admit no W₀ chain, 73 chained and killed by the W₁ joint search, 0 joint hits;
13 wide boxes on budget retries are no-chain candidates).  Each per-box statement is an
IMPLICATION over the FULL closed box — vacuous where no chain exists — so the assembly needs
only that the boxes cover the region (a decidable integer check, the Lean form of the
covering core being `Fresh.Certs.box_totality`/`box_cover_range`/`refine_cover` over unclipped
closed dyadic boxes, with the surplus past 17 and below ρ₂ = 1 named as harmless) together
with each box's own soundness on its domain.  **[PROVISIONAL: covering]**, claim named: the
74,613 closed boxes of the enumeration cover the J2 region and each per-box certificate is
sound on its full box.  The completeness target itself stays OWED (E802 item 6). -/
-- STANDING: OWED
def BoxSpineCover : Prop := AllArrangementsLabelled

#print axioms BoxSpineCover

end Fresh.FilterSkeleton
