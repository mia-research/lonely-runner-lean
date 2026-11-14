import Fresh.FilterAssembly
import Fresh.PinchCert

/-!
# Band totality + per-box exclusion certificates: the `OutsideBelow17` branch (O3)

Written 2026-11-09.  New file; nothing existing is edited.  Fourth attempt at this module
after three provider-quota kills; started clean.  (A prior uncommitted draft of this name
existed from a killed session but did NOT compile — four `linarith` cast failures in its
floor-box Stage-2 lemmas — and was not reused; a copy is preserved outside the tree at
`/tmp/BandNoCarve.lean.bak.20261109`.)  This is the O3 composition of the E834 assembly
skeleton: the OUTSIDE branch `Fresh.FilterAssembly.OutsideBelow17` — arrangements with a
normalised reading past 17 but none past 49 (the band `[17,23) ∪ (23,25) X24 ∪ [25,49)` of
its docstring) — derived from (band totality) + (per-box exclusion certificates), composed
entirely through the EXISTING soundness layer:

* `Fresh.Certs.FixedClearCert` / `fixedClear_clear` / `fixedClear_noCarve` (schema (a));
* `Fresh.Certs.WindowCert` / `windowCert_clear` / `windowCert_noCarve` (schema (b));
* `Fresh.Certs.noCarve_split` with the canonical tie planes `planeH1 = ρ₇−7ρ₅` /
  `planeH2 = 3ρ₆−5ρ₄` (`Fresh.Certs.planeH1`/`planeH2`) — schema class (c), the
  seam-cycle-plane split (`frontier_plane_cert_v1.py` at the data level);
* `Fresh.Pinch.pinchIntCert_of_dyadic` (schema (e), the h₃ = 25ρ₇ − 89ρ₅ exit-exit
  tangency; parametric in the lap pair `(a, b)`, the h₃ case `a = 11, b = 3` applied
  data-side via `Fresh.Pinch.pinchIntCert_of_dyadic_h3`);
* the bridges `Fresh.FilterAssembly.cascadeLandsBelow17_of_clearPoint`,
  `Fresh.FilterAssembly.clear_of_image`, `Fresh.FilterAssembly.notCarve_witness`.

## Stage 1 (banked first): the composition

`BandCertData` is the explicit data hypothesis, mirroring `Fresh.FilterAssembly.CoverData`
(the J2-range analogue) for the band: for every normalized reading-tuple in the band, one
of the four schema classes holds.  Each schema's conclusion is wired to the uniform
clear-point form `BandClearPoint g` (a point `s ∈ [1,15]`, `s ≤ 7` or `9 ≤ s`, clear for
every reading — exactly `cascadeLandsBelow17_of_clearPoint`'s input):

* fixed-R₀: `s = R₀ ∈ [1,7]` via `fixedClear_clear` (clear-point route);
* window-type: `s = X ∈ [1,7]` via `windowCert_clear` (clear-point route);
* seam-plane: `NoCarve g` via `Fresh.Certs.noCarve_split` (both sides carry (a)/(b)
  certificates), then `notCarve_witness` gives the lonely instant `t ∈ [1/8, 7/8]` and
  `s = 8t ∈ [1,7]` (no-carve route);
* pinch: `NoCarve g` via `pinchIntCert_of_dyadic` (no-carve route, same `s = 8t`).

`bandTuple` is the band analogue of `Fresh.FilterAssembly.coverTuple` (bound 49 instead of
17, plus the past-17 witness).  Both composition theorems are PROVED:
`outsideBelow17_of_bandData : BandCertData → OutsideBelow17` and `bandNoCarve` with
`OutsideBelow17`'s statement verbatim.

## Stage 2: parametric discharges (per-box hand enumeration is out of scope)

`clearAtOne_coord` (the band analogue of `FilterAssembly.cL_one_coord`, real-interval
form): a reading in `[1,49]` avoiding every open way-zone `(8j−1, 8j+1)`, `j = 1..6`, lies
in a closed gap `[8j+1, 8j+7]` at `R = 1`.  `fixedR0_of_clearAtOne` builds the fixed-R₀
schema (with `R₀ = 1` and the readings' own faces) from it; `bandCertData_of_avoidsAtOne`
and `outsideBelow17_of_avoidsAtOne` compose.  This discharges `BandCertData` for the
sub-band whose every reading is clear at `R = 1` (readings in
`[1,7] ∪ [9,15] ∪ [17,23] ∪ [25,31] ∪ [33,39] ∪ [41,47] ∪ {49}`); the `(23,25)` X24 family
and the h₃ straddler strip need the window-type / seam-plane / pinch schemas and stay
hypothesis-carrying (named below).

## Grading (rule 18) and divergences, stated honestly

* PROVED here, general: the `BandClearPoint` wiring for all four schema classes (Stage-1
  soundness lemmas), `bandTuple`, `outsideBelow17_of_bandData`, `bandNoCarve`, and the
  Stage-2 `R = 1` chain.  All `#print axioms`-clean (`[propext, Classical.choice,
  Quot.sound]`).
* HYPOTHESIS-carrying (OWED, data-side, each named): `BandCertData` itself — the band
  totality [PROVISIONAL: covering], tagged at the definition and at its use; its
  per-range discharges beyond the `R = 1`-clear sub-band (the X24 `(23,25)` window-type
  data, the seam-plane per-box splits, the h₃ pinch grid windows `lo5P/hi5P` —
  `tail_h3_pinch_grid_v1.out` records 509/509 certified at `D = 512`, aggregate only, no
  per-box dump in the artifact).
* Divergences from the artifacts, recorded: (i) `BandSeamPlane` is stated at the per-tuple
  level as the two side IMPLICATIONS of `noCarve_split` (`h g ≤ 0 → SideCertBox g`,
  `0 ≤ h g → SideCertBox g`); the per-box parent/sub-box structure that VALIDATES the side
  certificates is data-side, as in `frontier_plane_cert_v1.py`.  (ii) `BandPinch` is
  parametric in `(a, b)` (PinchCert's own form); the h₃ instantiation `(11, 3)` is applied
  by the data side.  (iii) The Stage-2 discharge uses degenerate faces (`lo = hi = g i`):
  sound because every schema here is an implication over its box.  (iv) `BandRange` does
  not require sorted readings or `g 0 = 1`; those are data-side enumeration savings, not
  soundness content (same convention as `CoverData`/`InRange17`).
-/

open Classical

namespace Fresh.BandNoCarve

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FilterAssembly

/-! ## The band, and the uniform clear-point conclusion of the four schemas -/

/-- The band of normalized reading-tuples: every reading in `[1,49]` (the least reading is
`1` in the normalization, so this holds for every normalised disparity tuple) and some
reading past `17` (the `OutsideBelow17` hypotheses, normalised).  No sortedness (`g 0 = 1`
etc.) is required: that is a data-side enumeration saving, not soundness content. -/
-- STANDING: DEFINITION
def BandRange (g : Fin 7 → ℝ) : Prop :=
  (∀ i, 1 ≤ g i ∧ g i ≤ 49) ∧ ∃ i, 17 < g i

/-- The uniform conclusion of the four schema classes: a clear point `s ∈ [1,15]` with
`s ≤ 7` or `9 ≤ s` (i.e. `s` in the closed window range of `W₀ ∪ W₁`), clear for every
reading — exactly `cascadeLandsBelow17_of_clearPoint`'s input shape. -/
-- STANDING: DEFINITION
def BandClearPoint (g : Fin 7 → ℝ) : Prop :=
  ∃ s : ℝ, 1 ≤ s ∧ s ≤ 15 ∧ (s ≤ 7 ∨ 9 ≤ s) ∧
    ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))

/-! ## The four schema classes (the `Fresh.Certs` + `Fresh.Pinch` interfaces) -/

/-- **Schema class 1 (fixed-R₀)**: `g` lies in the faces of a `Fresh.Certs.FixedClearCert`
(schema (a) of E832 item 1): a rational `R₀ ∈ [1,7]` whose scaled faces sit in closed
gaps.  Soundness: `fixedClear_clear`/`fixedClear_noCarve`. -/
-- STANDING: DEFINITION
def BandFixedR0 (g : Fin 7 → ℝ) : Prop :=
  ∃ c : Fresh.Certs.FixedClearCert, ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i

/-- **Schema class 2 (window-type)**: `g` lies in the faces of a `Fresh.Certs.WindowCert`
(schema (b) of E833 item 1): per-reading laps with the exit/entry inequalities and
`1 ≤ X ≤ Y ≤ 7`.  Soundness: `windowCert_clear`/`windowCert_noCarve`. -/
-- STANDING: DEFINITION
def BandWindowType (g : Fin 7 → ℝ) : Prop :=
  ∃ c : Fresh.Certs.WindowCert, ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i

/-- A side certificate of the seam split: a fixed-R₀ or window-type certificate of
`Fresh.Certs` containing `g` in its faces (both conclude `NoCarve` on their boxes). -/
-- STANDING: DEFINITION
def SideCertBox (g : Fin 7 → ℝ) : Prop :=
  (∃ c : Fresh.Certs.FixedClearCert, ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) ∨
  (∃ c : Fresh.Certs.WindowCert, ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i)

/-- **Schema class 3 (seam-cycle-plane)**: the plane-split certificate — schema (c) of
E833 item 1, `Fresh.Certs.noCarve_split` with the canonical tie planes `planeH1 = ρ₇−7ρ₅`
(E830's exact cycle) / `planeH2 = 3ρ₆−5ρ₄` (E832 item 4) at the data level: on EITHER side
of the plane, `g` lies in that side's `(a)/(b)` sub-box certificate.  (The per-box parent
box and the two sub-boxes that validate the side conditions are data-side,
`frontier_plane_cert_v1.py`; here the split is stated per-tuple, which is all the
composition consumes.) -/
-- STANDING: DEFINITION
def BandSeamPlane (g : Fin 7 → ℝ) : Prop :=
  ∃ h : (Fin 7 → ℝ) → ℝ, (h g ≤ 0 → SideCertBox g) ∧ (0 ≤ h g → SideCertBox g)

/-- **Schema class 4 (pinch)**: the tangency-plane box schema of `Fresh.Pinch` — `g` lies
in the closed dyadic box `k/D` with `ρ₅` in the plane region's grid window
`[lo5P/D, (hi5P+1)/D]`, exactly on the tangency plane `TangentPlane a b` (the h₃ case is
`a = 11, b = 3`, `25ρ₇ = 89ρ₅`), and the all-integer `PinchIntCond a b D k mj lo5P hi5P`
holds (`tail_h3_pinch_grid_v1.py`, `D = 512`, 509/509 certified, data-side).  Soundness:
`Fresh.Pinch.pinchIntCert_of_dyadic`. -/
-- STANDING: DEFINITION
def BandPinch (g : Fin 7 → ℝ) : Prop :=
  ∃ (a b : ℕ) (D : ℕ) (k mj : Fin 7 → ℤ) (lo5P hi5P : ℤ),
    0 < D ∧ Fresh.Pinch.InBox D k g ∧
      ((lo5P : ℝ) / D ≤ g 4 ∧ g 4 ≤ ((hi5P + 1 : ℤ) : ℝ) / D) ∧
      Fresh.Pinch.TangentPlane a b g ∧
      Fresh.Pinch.PinchIntCond a b (D : ℤ) k mj lo5P hi5P

/-- **The band certificate data hypothesis** — the band totality: every normalized
reading-tuple in the band is excluded by one of the four schema classes.  This mirrors
`Fresh.FilterAssembly.CoverData` (the J2-range covering) for the band, over real tuples
(the schemas here are box implications over real readings, not integer tuples).
**[PROVISIONAL: covering]**, claim it supports: `OutsideBelow17`, via
`outsideBelow17_of_bandData` below (rule 7(b); the per-range data discharges are named in
the module docstring's grading section). -/
-- STANDING: DEFINITION
def BandCertData : Prop :=
  ∀ g : Fin 7 → ℝ, BandRange g →
    BandFixedR0 g ∨ BandWindowType g ∨ BandSeamPlane g ∨ BandPinch g

/-! ## Stage 1: the per-schema wiring to the uniform clear point -/

/-- The no-carve route to the clear point: `NoCarve g` gives a lonely instant
`t ∈ [1/8, 7/8]` (`notCarve_witness`), hence the clear point `s = 8t ∈ [1,7]` (the same
transport as `allLandBelow17_of_coverData`'s no-carve branches). -/
theorem clearPoint_of_noCarve {g : Fin 7 → ℝ} (hnc : Fresh.Certs.NoCarve g) :
    BandClearPoint g := by
  obtain ⟨t, ht1, ht2, hlon⟩ := (notCarve_witness g).mp hnc
  refine ⟨8 * t, by linarith, by linarith, Or.inl (by linarith), ?_⟩
  intro i
  have hdist := hlon (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have he : (8 * t) / 8 = t := by field_simp
  rw [he]
  exact hdist

#print axioms clearPoint_of_noCarve

/-- Schema 1 (fixed-R₀) gives the clear point `s = R₀ ∈ [1,7]` (`fixedClear_clear`). -/
theorem clearPoint_of_fixedR0 {g : Fin 7 → ℝ} (h : BandFixedR0 g) : BandClearPoint g := by
  obtain ⟨c, hbox⟩ := h
  have hR₁ := c.hR₁
  have hR₇ := c.hR₇
  exact ⟨c.R₀, hR₁, by linarith, Or.inl hR₇, fixedClear_clear c g hbox⟩

#print axioms clearPoint_of_fixedR0

/-- Schema 2 (window-type) gives the clear point `s = X ∈ [1,7]` (`windowCert_clear`). -/
theorem clearPoint_of_windowType {g : Fin 7 → ℝ} (h : BandWindowType g) :
    BandClearPoint g := by
  obtain ⟨c, hbox⟩ := h
  have hX₁ := c.hXY₁
  have hX₂ := c.hXY₂
  have hX₃ := c.hXY₃
  exact ⟨c.X, hX₁, by linarith, Or.inl (by linarith), windowCert_clear c g hbox⟩

#print axioms clearPoint_of_windowType

/-- A side certificate of the seam split excludes carving (`fixedClear_noCarve` /
`windowCert_noCarve`). -/
theorem noCarve_of_sideCert {g : Fin 7 → ℝ} (h : SideCertBox g) : Fresh.Certs.NoCarve g := by
  rcases h with ⟨c, hbox⟩ | ⟨c, hbox⟩
  · exact fixedClear_noCarve c g hbox
  · exact windowCert_noCarve c g hbox

#print axioms noCarve_of_sideCert

/-- Schema 3 (seam-plane) excludes carving, by `Fresh.Certs.noCarve_split` composed with
the side certificates. -/
theorem noCarve_of_seamPlane {g : Fin 7 → ℝ} (h : BandSeamPlane g) : Fresh.Certs.NoCarve g := by
  obtain ⟨hpl, h₁, h₂⟩ := h
  exact Fresh.Certs.noCarve_split hpl g
    (fun hle => noCarve_of_sideCert (h₁ hle))
    (fun hge => noCarve_of_sideCert (h₂ hge))

#print axioms noCarve_of_seamPlane

/-- Schema 4 (pinch) excludes carving, by `Fresh.Pinch.pinchIntCert_of_dyadic`
(`Fresh.Pinch.NoCarve` and `Fresh.Certs.NoCarve` are the same predicate, both
`¬ FrontierFamilyCap.CarvesOneSeven (image g univ)`). -/
theorem noCarve_of_pinch {g : Fin 7 → ℝ} (h : BandPinch g) : Fresh.Certs.NoCarve g := by
  obtain ⟨a, b, D, k, mj, lo5P, hi5P, hD, hbox, h5P, hplane, hcond⟩ := h
  exact Fresh.Pinch.pinchIntCert_of_dyadic a b hD k mj hcond g hbox h5P hplane

#print axioms noCarve_of_pinch

/-- All four schema classes give the uniform clear point (the schema disjunction of
`BandCertData`, discharged through the four wirings above). -/
theorem clearPoint_of_bandCert {g : Fin 7 → ℝ}
    (h : BandFixedR0 g ∨ BandWindowType g ∨ BandSeamPlane g ∨ BandPinch g) :
    BandClearPoint g := by
  rcases h with h1 | h2 | h3 | h4
  · exact clearPoint_of_fixedR0 h1
  · exact clearPoint_of_windowType h2
  · exact clearPoint_of_noCarve (noCarve_of_seamPlane h3)
  · exact clearPoint_of_noCarve (noCarve_of_pinch h4)

#print axioms clearPoint_of_bandCert

/-! ## The arrangement-to-tuple construction (the band analogue of `coverTuple`) -/

/-- Every band arrangement's normalised disparity set is enumerated by a `Fin 7 → ℝ`
reading tuple in the band (`coverTuple`'s construction with the bound 49 and the past-17
witness: the sorted normalised set, padded with `1`, which lies in the set). -/
theorem bandTuple {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hv : Fresh.IsArrangement v)
    (hm : Fresh.IsDmin v k m) (hex : ∃ d ∈ disparitySet v k, 17 * m < d)
    (hmax : ∀ d ∈ disparitySet v k, d ≤ 49 * m) :
    ∃ g : Fin 7 → ℝ, BandRange g ∧
      (Finset.image g Finset.univ = Finset.image (fun d => d / m) (disparitySet v k)) := by
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hge : ∀ d ∈ disparitySet v k, m ≤ d := fun d hd => hm.2 hd
  set dsn : Finset ℝ := Finset.image (fun d => d / m) (disparitySet v k) with hdsneq
  have h1in : (1 : ℝ) ∈ dsn := by
    rw [hdsneq]
    exact Finset.mem_image.mpr ⟨m, hm.1, div_self (ne_of_gt hm0)⟩
  have hge1 : ∀ d ∈ dsn, 1 ≤ d := by
    intro d hd
    rw [hdsneq, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    have h1 : (m : ℝ) ≤ d2 := by exact_mod_cast (hge d2 hd2)
    have h3 : (1 : ℝ) = m / m := by rw [div_self (ne_of_gt hm0)]
    calc (1 : ℝ) = m / m := h3
      _ ≤ d2 / m := by
          rw [← h3, le_div_iff₀ hm0]
          linarith
  have hle49 : ∀ d ∈ dsn, d ≤ 49 := by
    intro d hd
    rw [hdsneq, Finset.mem_image] at hd
    obtain ⟨d2, hd2, rfl⟩ := hd
    have h1 : (d2 : ℝ) ≤ 49 * m := by exact_mod_cast (hmax d2 hd2)
    have h2 : d2 / m ≤ 49 := (div_le_iff₀ hm0).mpr h1
    exact h2
  have hcard : dsn.card ≤ 7 := by
    rw [hdsneq]
    have h1 := Finset.card_image_le (f := fun d => d / m) (s := disparitySet v k)
    have h2c : (disparitySet v k).card
        = (Finset.image (fun i => |v i - v k|) (Finset.univ.erase k)).card := rfl
    have h2 := Finset.card_image_le (f := fun i => |v i - v k|) (s := Finset.univ.erase k)
    have h4 : (Finset.univ.erase k).card = 7 := by
      have h3 : (Finset.univ (α := Fin 8)).card = 8 := by simp
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), h3]
    omega
  set L : List ℝ := dsn.sort (· ≤ ·) with hLdef
  have hLlen : L.length = dsn.card := Finset.length_sort (· ≤ ·)
  have hLmem : ∀ x ∈ L, x ∈ dsn := fun x hx => (Finset.mem_sort (· ≤ ·)).mp hx
  have hlen : L.length ≤ 7 := by rw [hLlen]; exact hcard
  set g : Fin 7 → ℝ := fun i => if h : (i : ℕ) < L.length then L[i] else 1 with hgdef
  have hgin : ∀ i, g i ∈ dsn := by
    intro i
    simp only [hgdef]
    by_cases h : (i : ℕ) < L.length
    · rw [dif_pos h]
      exact hLmem _ (List.mem_iff_getElem.mpr ⟨i, h, rfl⟩)
    · rw [dif_neg h]
      exact h1in
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · intro i
    exact ⟨hge1 _ (hgin i), hle49 _ (hgin i)⟩
  · obtain ⟨d, hdmem, hd17⟩ := hex
    have hdin : d / m ∈ dsn := Finset.mem_image.mpr ⟨d, hdmem, rfl⟩
    have hd17' : (17 : ℝ) < d / m := by
      rw [lt_div_iff₀ hm0]
      exact hd17
    have hdL : d / m ∈ L := Finset.mem_sort (· ≤ ·) |>.mpr hdin
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hdL
    refine ⟨⟨j, by omega⟩, ?_⟩
    simp only [hgdef]
    rw [dif_pos hj]
    show 17 < L[(j : ℕ)]
    rw [hjeq]
    exact hd17'
  · refine Finset.ext fun d => ⟨fun hd => ?_, fun hd => ?_⟩
    · rw [Finset.mem_image] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact hgin i
    · have hdL : d ∈ L := Finset.mem_sort (· ≤ ·) |>.mpr hd
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hdL
      rw [Finset.mem_image]
      refine ⟨⟨j, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [hgdef]
      rw [dif_pos hj]
      show L[(j : ℕ)] = d
      exact hjeq

#print axioms bandTuple

/-! ## Stage 1 (main): the O3 composition -/

/-- **The O3 composition**: band totality (`BandCertData`, [PROVISIONAL: covering]) plus
the per-box exclusion certificates (the four `Fresh.Certs`/`Fresh.Pinch` schemas) give
`OutsideBelow17` — every arrangement with a normalised reading past 17 but none past 49
lands below 17.  Chain: `bandTuple` (the normalised disparity set is enumerated by a band
tuple) → the band-totality step (tagged below) → the schema's clear point
(`clearPoint_of_bandCert`) → the core bridge `cascadeLandsBelow17_of_clearPoint` (with
`clear_of_image` transporting the clearance from the tuple to the disparity set). -/
theorem outsideBelow17_of_bandData (hData : BandCertData) : OutsideBelow17 := by
  intro v hv k m hm hex hmax
  obtain ⟨g, hrange, himage⟩ := bandTuple hv hm hex hmax
  -- [PROVISIONAL: covering] — the band-totality step: every normalized reading-tuple of
  -- the band carries one of the four schemas (`BandCertData`).  Claim it supports:
  -- `OutsideBelow17` for this arrangement (the cascade lands below 17), via the schema
  -- soundness wired above and the core bridge (rule 7(b)).
  obtain ⟨s, hs1, hs2, hsw, hcl⟩ := clearPoint_of_bandCert (hData g hrange)
  exact cascadeLandsBelow17_of_clearPoint hv hm s hs1 hs2 hsw (clear_of_image himage hcl)

#print axioms outsideBelow17_of_bandData

/-- **The main theorem, `OutsideBelow17`'s statement verbatim** (unfolded
statement-for-statement from `Fresh.FilterAssembly.OutsideBelow17`): the band certificates
give the outside branch of the n=8 filter assembly. -/
theorem bandNoCarve (hData : BandCertData) :
    ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v → ∀ (k : Fin 8) (m : ℝ), Fresh.IsDmin v k m →
      (∃ d ∈ disparitySet v k, 17 * m < d) → (∀ d ∈ disparitySet v k, d ≤ 49 * m) →
      Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m :=
  outsideBelow17_of_bandData hData

#print axioms bandNoCarve

/-! ## Stage 2: the parametric `R = 1` discharge (band analogue of `cL_one`) -/

/-- `x` avoids the open way-zones `(8j−1, 8j+1)` of the laps `j = 1..6` (the zones met by
`[1,49]` at `R = 1`): the decidable per-reading avoidance datum of the `R = 1` clear
point. -/
-- STANDING: DEFINITION
def AvoidsZonesAtOne (x : ℝ) : Prop :=
  ∀ j : ℤ, (1 : ℤ) ≤ j → j ≤ 6 →
    ¬ (((8 * j - 1 : ℤ) : ℝ) < x ∧ x < ((8 * j + 1 : ℤ) : ℝ))

/-- The per-reading `R = 1` gap selection (the band analogue of `cL_one_coord`,
real-interval form): a reading in `[1,49]` avoiding every open way-zone `(8j−1, 8j+1)`,
`j = 1..6`, lies in a closed gap `[8j+1, 8j+7]`.  The laps are `j = 0..6`
(`[1,7], [9,15], [17,23], [25,31], [33,39], [41,47], [49,55]`). -/
theorem clearAtOne_coord (x : ℝ) (hx1 : (1 : ℝ) ≤ x) (hx49 : x ≤ 49)
    (havo : AvoidsZonesAtOne x) :
    ∃ j : ℤ, ((8 * j + 1 : ℤ) : ℝ) ≤ x ∧ x ≤ ((8 * j + 7 : ℤ) : ℝ) := by
  -- the zone-avoidance in implication form: past a zone's lower edge, the avoidance
  -- forces the reading past the zone's upper edge (the lap-opening steps)
  have ha1 : 7 < x → 9 ≤ x := by
    have h := havo 1 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  have ha2 : 15 < x → 17 ≤ x := by
    have h := havo 2 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  have ha3 : 23 < x → 25 ≤ x := by
    have h := havo 3 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  have ha4 : 31 < x → 33 ≤ x := by
    have h := havo 4 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  have ha5 : 39 < x → 41 ≤ x := by
    have h := havo 5 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  have ha6 : 47 < x → 49 ≤ x := by
    have h := havo 6 (by norm_num) (by norm_num)
    push_neg at h; push_cast at h; norm_num at h; exact h
  rcases le_or_gt x 7 with h | h
  · exact ⟨0, by push_cast; norm_num; linarith, by push_cast; norm_num; linarith⟩
  · have h9 : 9 ≤ x := ha1 h
    rcases le_or_gt x 15 with h | h
    · exact ⟨1, by push_cast; norm_num; linarith, by push_cast; norm_num; linarith⟩
    · have h17 : 17 ≤ x := ha2 h
      rcases le_or_gt x 23 with h | h
      · exact ⟨2, by push_cast; norm_num; linarith, by push_cast; norm_num; linarith⟩
      · have h25 : 25 ≤ x := ha3 h
        rcases le_or_gt x 31 with h | h
        · exact ⟨3, by push_cast; norm_num; linarith, by push_cast; norm_num; linarith⟩
        · have h33 : 33 ≤ x := ha4 h
          rcases le_or_gt x 39 with h | h
          · exact ⟨4, by push_cast; norm_num; linarith, by push_cast; norm_num; linarith⟩
          · have h41 : 41 ≤ x := ha5 h
            rcases le_or_gt x 47 with h | h
            · exact ⟨5, by push_cast; norm_num; linarith,
                by push_cast; norm_num; linarith⟩
            · have h49 : 49 ≤ x := ha6 h
              exact ⟨6, by push_cast; norm_num; linarith,
                by push_cast; norm_num; linarith⟩

#print axioms clearAtOne_coord

/-- The `R₀ = 1` instance of the fixed-R₀ schema: a tuple whose readings each lie in a
closed gap at `R = 1` carries a `Fresh.Certs.FixedClearCert` (with `R₀ = 1` and the
readings' own faces — the faces are degenerate `lo = hi = g i`, sound because the schema
is an implication over its box). -/
theorem fixedR0_of_clearAtOne {g : Fin 7 → ℝ}
    (hgap : ∀ i, ∃ j : ℤ, ((8 * j + 1 : ℤ) : ℝ) ≤ g i ∧ g i ≤ ((8 * j + 7 : ℤ) : ℝ)) :
    BandFixedR0 g := by
  choose j hj using hgap
  have hgap' : ∀ i, (((8 * j i : ℤ) : ℝ) + 1) ≤ (1 : ℝ) * g i ∧
      (1 : ℝ) * g i ≤ (((8 * j i : ℤ) : ℝ) + 7) := by
    intro i
    obtain ⟨h1, h2⟩ := hj i
    constructor
    · push_cast; push_cast at h1; linarith
    · push_cast; push_cast at h2; linarith
  exact ⟨⟨g, g, 1, j, by norm_num, by norm_num, fun _ => le_refl _, hgap'⟩,
    fun _ => ⟨le_refl _, le_refl _⟩⟩

#print axioms fixedR0_of_clearAtOne

/-- **The `R = 1` discharge of the band data**: if every band tuple's readings avoid the
open way-zones at `R = 1`, the fixed-R₀ schema covers the band, so `BandCertData` holds.
**[PROVISIONAL: covering]**, claim it supports: `OutsideBelow17` (via
`outsideBelow17_of_bandData`).  This discharges the sub-band with all readings in
`[1,7] ∪ [9,15] ∪ [17,23] ∪ [25,31] ∪ [33,39] ∪ [41,47] ∪ {49}`; the `(23,25)` X24 family
and the h₃ straddler strip need the other three schemas (OWED, data-side). -/
theorem bandCertData_of_avoidsAtOne
    (h : ∀ g : Fin 7 → ℝ, BandRange g → ∀ i, AvoidsZonesAtOne (g i)) :
    BandCertData := by
  intro g hrg
  refine Or.inl (fixedR0_of_clearAtOne ?_)
  intro i
  exact clearAtOne_coord (g i) (hrg.1 i).1 (hrg.1 i).2 (h g hrg i)

#print axioms bandCertData_of_avoidsAtOne

/-- The composed `R = 1` discharge: band readings all avoiding the `R = 1` way-zones give
`OutsideBelow17` directly. -/
theorem outsideBelow17_of_avoidsAtOne
    (h : ∀ g : Fin 7 → ℝ, BandRange g → ∀ i, AvoidsZonesAtOne (g i)) : OutsideBelow17 :=
  outsideBelow17_of_bandData (bandCertData_of_avoidsAtOne h)

#print axioms outsideBelow17_of_avoidsAtOne

end Fresh.BandNoCarve
