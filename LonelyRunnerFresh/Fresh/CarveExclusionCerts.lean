import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.KTaxonomy
import Fresh.FilterSkeleton
import Fresh.FrontierFamilyCap

/-!
# The carve-exclusion certificate schemas (E832 / E833), native

Written 2026-11-07.  New file; nothing existing is edited.  This is the Lean form of the
certificate systems of E832 item 1 and E833 item 1 (whose soundness arguments are graded [P]
there and marked "not in Lean" in both Consequences); the per-box DATA instantiations stay
computational, as in the artifacts `frontier_box_dfs_v1.c`, `frontier_window_cert_v1.py`,
`frontier_plane_cert_v1.py`.  Everything here is the reusable framework; the box spine of
`Fresh.FilterSkeleton.FilterCompleteVia` is the consumer.

Coordinate convention (E832): the `R`-coordinate, readings normalised with `ρ₁ = 1`; an
instant `t` corresponds to `R = 8t`; reading `ρ` is clear at `t` iff `ρR` lies in a closed gap
`[8j+1, 8j+7]` (`clearAt_R_iff`).  Readings are a function `g : Fin 7 → ℝ` (`g 0 = ρ₁ = 1`);
certificate soundness is stated over the FULL closed box (unclipped: nothing intersects
`{ρ₇ ≤ 17}` or `{ρ₂ > 1}`; the surplus past 17 and below `ρ₂ = 1` is harmless and named in
`box_cover_range`, not hidden).  A box certificate is an IMPLICATION over the box — vacuous
off the box — so the assembly needs only C ∪ family-domains = the enumerated boxes (a
decidable integer check at the data level) plus each certificate's own soundness on its
domain.  No existential box-level statement is used anywhere.

Schemas.
* (a) `FixedClearCert` (E832 item 1): a rational `R₀ ∈ [1,7]` and, per reading, closed box
  faces `[lo i, hi i]` and a gap index `j i` with `R₀·[lo i, hi i] ⊆ [8j+1, 8j+7]`;
  soundness `fixedClear_clear`/`fixedClear_lonely`/`fixedClear_noCarve`: every arrangement
  with readings in the faces has `R₀/8` a lonely instant of `W₀`, so `[1,7]` is not carved.
  The data-level check is the integer form `FixedClearIntCond` (decidable instance provided)
  — E832's `(8j+1)·base ≤ r·n`, `r·(n+1) ≤ (8j+7)·base` with the box-scale factor `D` made
  explicit (`fixedClearCert_of_dyadic_int`).
* (b) `WindowCert` (E833 item 1(b)): per-reading laps `j i` with the exit inequality
  `(8j_i+1) ≤ lo i · X` and the entry inequality `hi i · Y ≤ (8j_i+7)`, and `1 ≤ X ≤ Y ≤ 7`;
  soundness `windowCert_clear`/`windowCert_lonely`/`windowCert_noCarve`: `[X/8, Y/8]` is a
  nonempty clear window, `X/8` a lonely instant of `W₀`, no carve.  The face inequalities are
  the corner checks (each per-reading inequality is monotone in its one reading, so its
  extreme is a face — the decoupled form of E833's "64 corners"); the coupled two-reading
  form `A ρ_t ≤ B ρ_s` is `pair_corner`.
* (c) `noCarve_split` (E833 1(c)): the plane-split principle — certificates on the two sides
  of a plane `h = 0` cover the box.  The canonical planes of the artifacts are named
  (`planeH1` = `ρ₇ − 7ρ₅` from E830's exact cycle, `planeH2` = `3ρ₆ − 5ρ₄` from E832 item 4).
* (d) `InDyadicBox`, `box_totality`, `box_cover_range`, `refine_cover`: the dyadic-box
  totality — floor-based selections are non-decreasing, closed boxes contain their readings,
  children cover the parent.  These are the Lean form of the covering step, tagged
  [PROVISIONAL: covering] with the claim named, per rule 7.
* (e) `PinchCert` (2026-11-07, the h₃ = 25ρ₇ − 89ρ₅ straddler mechanism): the pinch-point
  certificate — on the tangency plane 25ρ₇ = 89ρ₅ (exit-meets-exit: 89/ρ₇ = 25/ρ₅, ρ₇'s
  lap-11 zone exit edge coinciding with ρ₅'s lap-3 zone exit edge) the point t = 25/(8ρ₅) is
  exactly at both readings' clearance edges and is a lonely instant for every arrangement on
  the plane.  A fourth certificate type: the clear point is a rational FUNCTION of the
  readings (R* = 25/ρ₅ on the plane), not a fixed R₀.  Data-side: 509/509 straddler leaves
  certified (`tail_h3_pinch_v1.py`, the grid-ℤ form `tail_h3_pinch_grid_v1.py`).

Divergences from the artifacts, recorded: (i) E832's printed integer inequalities omit the
box-scale factor `D` (their `n` is at the box's own depth scale); here the exact form
`(8j+1)·base·D ≤ r·k i` is used, so `R₀ = r/base` and the faces are `k i/D` exactly.
(ii) E833's window type identifies `X` with an exit `(8j_p+1)/ρ_p` and `Y` with an entry
`(8j_q−1)/ρ_q`; that identification is how the SEARCH finds `X, Y`, and the soundness needs
only `1 ≤ X ≤ Y ≤ 7` plus the per-reading inequalities — so the Lean schema drops the
exit/entry identification (a generalisation, not a weakening).  (iii) E833's "64 corners"
become the per-reading face checks `hexit`/`hentry` plus `pair_corner` for coupled
inequalities; a joint 64-corner search is data-side.  (iv) the h₃ straddler leaves admit NO
E830-style seam-cycle identity: the mission-candidate product (89/(8a−1))·(25/(8b−1)) = 1
needs (8a−1)(8b−1) = 2225 = 5²·89, whose divisors are 1 or 5 mod 8, never 7 — entry edges are
7 mod 8 (exhausted over the leaf lap ranges in `tail_h3_cycles_v1.py`, [T 0] for 2-, 3- and
4-link cycles); h₃ is the exit-exit tangency, and its certificate is (e).
-/

open Classical

namespace Fresh.Certs

/-! ## Coordinate helpers -/

/-- Clear at an instant, for a readings function: loneliness for the image set. -/
theorem lonelyAt_image (g : Fin 7 → ℝ) (t : ℝ) :
    Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) t ↔
      ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * t) := by
  constructor
  · intro h i
    exact h (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact h i

#print axioms lonelyAt_image

/-- The `R`-coordinate clear condition: reading `ρ` is clear at the instant `t = R/8` exactly
when `ρR` lies in a closed gap `[8j+1, 8j+7]` (E832's "distance of `ρR/8` from an integer at
least `1/8`"). -/
theorem clearAt_R_iff (ρ R : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (ρ * (R / 8)) ↔
      ∃ j : ℤ, ρ * R ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) := by
  have e : ((8 : ℝ)) * (ρ * (R / 8)) = ρ * R := by ring
  constructor
  · intro h
    obtain ⟨k, hk1, hk2⟩ := (Fresh.KTaxonomy.distInt_ge_eighth_iff (ρ * (R / 8))).mp h
    refine ⟨k, ?_⟩
    have hphase := Fresh.FilterSkeleton.window_R_of_phase (x := ρ * (R / 8)) (j := k) hk1 hk2
    rw [e] at hphase
    exact hphase
  · rintro ⟨j, hj⟩
    have h8in : ((8 : ℝ)) * (ρ * (R / 8)) ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) := by
      rw [e]; exact hj
    have hphase := Fresh.FilterSkeleton.phase_of_window_R (x := ρ * (R / 8)) (j := j) h8in
    exact (Fresh.KTaxonomy.distInt_ge_eighth_iff (ρ * (R / 8))).mpr ⟨j, hphase.1, hphase.2⟩

#print axioms clearAt_R_iff

/-- A strict zone `(8j−1, 8j+1)` at `R` puts the reading in the way at the instant `R/8`. -/
theorem inWay_of_zone {ρ R : ℝ} {j : ℤ}
    (h1 : (((8 * j - 1 : ℤ) : ℝ)) < ρ * R) (h2 : ρ * R < (((8 * j + 1 : ℤ) : ℝ))) :
    Fresh.InWay ρ (R / 8) := by
  have hj8 : ((8 * j : ℤ) : ℝ) = 8 * ((j : ℝ)) := by push_cast; ring
  have hj8m : (((8 * j - 1 : ℤ) : ℝ)) = ((8 * j : ℤ) : ℝ) - 1 := by push_cast; ring
  have hj8p : (((8 * j + 1 : ℤ) : ℝ)) = ((8 * j : ℤ) : ℝ) + 1 := by push_cast; ring
  have e : ρ * (R / 8) = (j : ℝ) + ((ρ * R - ((8 * j : ℤ) : ℝ)) / 8) := by
    field_simp
    push_cast
    ring
  have b1 : ((j : ℝ)) - 1 / 8 < ρ * (R / 8) := by
    rw [e]
    have h1' : ρ * R - ((8 * j : ℤ) : ℝ) > -1 := by linarith [h1, hj8m]
    linarith
  have b2 : ρ * (R / 8) < ((j : ℝ)) + 1 / 8 := by
    rw [e]
    have h2' : ρ * R - ((8 * j : ℤ) : ℝ) < 1 := by linarith [h2, hj8p]
    linarith
  exact Fresh.OneMover.inWay_of_window j b1 b2

#print axioms inWay_of_zone

/-- The no-carve predicate for a readings function (the box certificates' conclusion). -/
-- STANDING: DEFINITION
def NoCarve (g : Fin 7 → ℝ) : Prop :=
  ¬ Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)

/-! ## (a) The fixed-clear-point certificate (E832 item 1) -/

/-- A fixed clear point for a box: the rational `R₀ ∈ [1,7]` and, per reading, closed faces
`[lo i, hi i]` and a gap index `j i` with `R₀·[lo i, hi i] ⊆ [8j+1, 8j+7]`.  (For the
six-reading boxes of E832 the reading `ρ₁ = 1` is pinned by `lo 0 = hi 0 = 1`, `j 0 = 0`.) -/
-- STANDING: DEFINITION
structure FixedClearCert where
  lo : Fin 7 → ℝ
  hi : Fin 7 → ℝ
  R₀ : ℝ
  j : Fin 7 → ℤ
  hR₁ : 1 ≤ R₀
  hR₇ : R₀ ≤ 7
  hface : ∀ i, lo i ≤ hi i
  hgap : ∀ i, (((8 * j i : ℤ) : ℝ) + 1) ≤ R₀ * lo i ∧ R₀ * hi i ≤ (((8 * j i : ℤ) : ℝ) + 7)

/-- **Soundness of the fixed-clear-point certificate**: every arrangement whose readings lie
in the faces has `g i·R₀ ∈ [8j_i+1, 8j_i+7]` for every reading.  The certificate holds over
the FULL closed box; nothing is clipped. -/
theorem fixedClear_clear (c : FixedClearCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) :
    ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (c.R₀ / 8)) := by
  intro i
  have hR₁ := c.hR₁
  have hR₇ := c.hR₇
  have hgap1 := (c.hgap i).1
  have hgap2 := (c.hgap i).2
  have hpos : (0 : ℝ) ≤ c.R₀ := by linarith
  have hstep1 : c.R₀ * c.lo i ≤ c.R₀ * g i := mul_le_mul_of_nonneg_left (hbox i).1 hpos
  have hstep2 : c.R₀ * g i ≤ c.R₀ * c.hi i := mul_le_mul_of_nonneg_left (hbox i).2 hpos
  have hmem1 : (((8 * c.j i : ℤ) : ℝ) + 1) ≤ g i * c.R₀ := by linarith
  have hmem2 : g i * c.R₀ ≤ (((8 * c.j i : ℤ) : ℝ) + 7) := by linarith
  rw [clearAt_R_iff (g i) c.R₀]
  exact ⟨c.j i, Set.mem_Icc.mpr ⟨hmem1, hmem2⟩⟩

#print axioms fixedClear_clear

/-- **The lonely instant of `W₀`**: `R₀/8 ∈ [1/8, 7/8]` is lonely for every arrangement in
the box. -/
theorem fixedClear_lonely (c : FixedClearCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) :
    Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) (c.R₀ / 8) :=
  (lonelyAt_image g _).mpr (fixedClear_clear c g hbox)

#print axioms fixedClear_lonely

theorem fixedClear_mem_window (c : FixedClearCert) :
    c.R₀ / 8 ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  have hR₁ := c.hR₁
  have hR₇ := c.hR₇
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

#print axioms fixedClear_mem_window

/-- **No carve**: a box with a fixed clear point holds no arrangement that carves `[1,7]` —
the carve would cover `R = R₀`, putting a reading in the way at the lonely instant. -/
theorem fixedClear_noCarve (c : FixedClearCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) : NoCarve g := by
  intro hcarve
  obtain ⟨ρ, hρmem, j, hz1, hz2⟩ := hcarve c.R₀ c.hR₁ c.hR₇
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz1' : (((8 * j - 1 : ℤ) : ℝ)) < g i * c.R₀ := by push_cast; linarith
  have hz2' : g i * c.R₀ < (((8 * j + 1 : ℤ) : ℝ)) := by push_cast; linarith
  have hway := inWay_of_zone (ρ := g i) (R := c.R₀) hz1' hz2'
  have hclear := fixedClear_clear c g hbox i
  unfold Fresh.InWay at hway
  linarith

#print axioms fixedClear_noCarve

/-- The integer data-level check (E832 item 1's `(8j+1)·base ≤ r·n`, `r·(n+1) ≤ (8j+7)·base`,
with the box-scale factor `D` explicit).  All quantities are integers, so the check is
decidable (`FixedClearIntCond` carries a `Decidable` instance). -/
-- STANDING: DEFINITION
def FixedClearIntCond (D base : ℤ) (k j : Fin 7 → ℤ) (r : ℤ) : Prop :=
  ∀ i, (8 * j i + 1) * base * D ≤ r * k i ∧ r * (k i + 1) ≤ (8 * j i + 7) * base * D

instance (D base : ℤ) (k j : Fin 7 → ℤ) (r : ℤ) :
    Decidable (FixedClearIntCond D base k j r) :=
  Fintype.decidableForallFintype

/-- The integer conditions build the certificate: `R₀ = r/base` with faces
`[k i/D, (k i+1)/D]` (the box is CLOSED, the halving enumeration's children included).  This
is the decidable per-box check of the box spine: all hypotheses are integer inequalities. -/
noncomputable def fixedClearCert_of_dyadic_int {D base : ℤ} (hD : 0 < D) (hbase : 0 < base)
    (k j : Fin 7 → ℤ) {r : ℤ} (hR₁ : 1 * base ≤ r) (hR₇ : r ≤ 7 * base)
    (hint : FixedClearIntCond D base k j r) : FixedClearCert where
  lo := fun i => (k i : ℝ) / D
  hi := fun i => ((k i + 1 : ℤ) : ℝ) / D
  R₀ := (r : ℝ) / base
  j := j
  hR₁ := by
    have hb : (0 : ℝ) < base := by exact_mod_cast hbase
    have hr : (1 : ℝ) * base ≤ r := by exact_mod_cast hR₁
    exact (le_div_iff₀ hb).mpr hr
  hR₇ := by
    have hb : (0 : ℝ) < base := by exact_mod_cast hbase
    have hr : r ≤ (7 : ℝ) * base := by exact_mod_cast hR₇
    exact (div_le_iff₀ hb).mpr hr
  hface := by
    intro i
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hleZ : (k i : ℤ) ≤ (k i + 1 : ℤ) := by omega
    have hleR : ((k i : ℤ) : ℝ) ≤ ((k i + 1 : ℤ) : ℝ) := by exact_mod_cast hleZ
    have hle2 : ((k i : ℤ) : ℝ) * D ≤ ((k i + 1 : ℤ) : ℝ) * D :=
      mul_le_mul_of_nonneg_right hleR hD'.le
    exact (div_le_div_iff₀ hD' hD').mpr hle2
  hgap := by
    intro i
    have hb1 : (0 : ℝ) < base := by exact_mod_cast hbase
    have hd1 : (0 : ℝ) < D := by exact_mod_cast hD
    have hb : (0 : ℝ) < (base : ℝ) * (D : ℝ) := mul_pos hb1 hd1
    obtain ⟨c1, c2⟩ := hint i
    constructor
    · have c1' : (8 * j i + 1) * (base * D) ≤ r * k i := by linarith
      have hcast : (((8 * j i + 1 : ℤ) * (base * D : ℤ) : ℤ) : ℝ) ≤ ((r * k i : ℤ) : ℝ) :=
        Int.cast_le.mpr c1'
      push_cast at hcast
      have hb2 : ((base * D : ℤ) : ℝ) = (base : ℝ) * (D : ℝ) := by push_cast; ring
      have hb3 : ((r * k i : ℤ) : ℝ) = (r : ℝ) * ((k i : ℤ) : ℝ) := by push_cast; ring
      have hb4 : ((8 * j i : ℤ) : ℝ) = 8 * ((j i : ℤ) : ℝ) := by push_cast; ring
      have hdivP : (((8 * j i : ℤ) : ℝ) + 1)
          ≤ (r : ℝ) * ((k i : ℤ) : ℝ) / ((base : ℝ) * (D : ℝ)) := by
        rw [le_div_iff₀ hb, hb4]
        linarith
      have hrw : (r : ℝ) / (base : ℝ) * ((k i : ℝ) / (D : ℝ))
          = (r : ℝ) * ((k i : ℤ) : ℝ) / ((base : ℝ) * (D : ℝ)) := by
        field_simp
      rw [hrw]
      exact hdivP
    · have c2' : r * (k i + 1) ≤ (8 * j i + 7) * (base * D) := by linarith
      have hcast1 : ((r * (k i + 1 : ℤ) : ℤ) : ℝ)
          ≤ (((8 * j i + 7 : ℤ) * (base * D : ℤ) : ℤ) : ℝ) := Int.cast_le.mpr c2'
      have hcast : (r : ℝ) * ((k i + 1 : ℤ) : ℝ)
          ≤ (8 * ((j i : ℤ) : ℝ) + 7) * ((base : ℝ) * (D : ℝ)) := by
        have e1 : ((r * (k i + 1 : ℤ) : ℤ) : ℝ) = (r : ℝ) * ((k i + 1 : ℤ) : ℝ) :=
          Int.cast_mul r (k i + 1)
        have e2 : (((8 * j i + 7 : ℤ) * (base * D : ℤ) : ℤ) : ℝ)
            = (8 * ((j i : ℤ) : ℝ) + 7) * ((base : ℝ) * (D : ℝ)) := by push_cast; ring
        rw [e1, e2] at hcast1
        exact hcast1
      have hb5 : ((8 * j i : ℤ) : ℝ) = 8 * ((j i : ℤ) : ℝ) := by push_cast; ring
      have hrw : (r : ℝ) / (base : ℝ) * (((k i + 1 : ℤ) : ℝ) / (D : ℝ))
          = (r : ℝ) * ((k i + 1 : ℤ) : ℝ) / ((base : ℝ) * (D : ℝ)) := by
        field_simp
      have hdivP : (r : ℝ) * ((k i + 1 : ℤ) : ℝ) / ((base : ℝ) * (D : ℝ))
          ≤ (((8 * j i : ℤ) : ℝ) + 7) := by
        rw [div_le_iff₀ hb, hb5]
        linarith
      rw [hrw]
      exact hdivP

#print axioms fixedClearCert_of_dyadic_int

/-! ## (b) The window-type certificate (E833 item 1(b)) -/

/-- A window type for a box: per-reading laps `j i` with the exit inequality
`(8j_i+1) ≤ lo i · X` and the entry inequality `hi i · Y ≤ (8j_i+7)`, and `1 ≤ X ≤ Y ≤ 7`.
The face form is the corner check: the exit inequality `(8j_i+1)/ρ ≤ X` is decreasing in `ρ`
(worst at `lo i`), the entry inequality `Y ≤ (8j_i+7)/ρ` is increasing in `ρ` (worst at
`hi i`).  `hlopos` says the faces are nonnegative (the enumerated boxes live in the positive
readings; `ρ₁`'s face `[1,1]` included).  (E833's identification of `X` with an exit zone's
edge and `Y` with an entry zone's edge is how the search finds `X, Y`; the soundness needs
only the inequalities, so the Lean schema drops that identification.) -/
-- STANDING: DEFINITION
structure WindowCert where
  lo : Fin 7 → ℝ
  hi : Fin 7 → ℝ
  X : ℝ
  Y : ℝ
  j : Fin 7 → ℤ
  hXY₁ : 1 ≤ X
  hXY₂ : X ≤ Y
  hXY₃ : Y ≤ 7
  hface : ∀ i, lo i ≤ hi i
  hlopos : ∀ i, 0 ≤ lo i
  hexit : ∀ i, (((8 * j i : ℤ) : ℝ) + 1) ≤ lo i * X
  hentry : ∀ i, hi i * Y ≤ (((8 * j i : ℤ) : ℝ) + 7)

/-- **Soundness of the window-type certificate**: every arrangement with readings in the
faces has `g i·X ∈ [8j_i+1, 8j_i+7]` for every reading. -/
theorem windowCert_clear (c : WindowCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) :
    ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (c.X / 8)) := by
  intro i
  have hx1 := c.hXY₁
  have hx2 := c.hXY₂
  have hx3 := c.hXY₃
  have hlopos := c.hlopos i
  have hgap1 := c.hexit i
  have hgap2 := c.hentry i
  have hXpos : (0 : ℝ) ≤ c.X := by linarith
  have hgi1 := (hbox i).1
  have hgi2 := (hbox i).2
  have hgpos : (0 : ℝ) ≤ g i := by linarith
  have hstep1 : c.lo i * c.X ≤ g i * c.X := mul_le_mul_of_nonneg_right hgi1 hXpos
  have hstep2 : g i * c.X ≤ g i * c.Y := mul_le_mul_of_nonneg_left hx2 hgpos
  have hYpos : (0 : ℝ) ≤ c.Y := by linarith
  have hstep3 : g i * c.Y ≤ c.hi i * c.Y := mul_le_mul_of_nonneg_right hgi2 hYpos
  have hmem1 : (((8 * c.j i : ℤ) : ℝ) + 1) ≤ g i * c.X := le_trans hgap1 hstep1
  have hmem2 : g i * c.X ≤ (((8 * c.j i : ℤ) : ℝ) + 7) :=
    le_trans (le_trans hstep2 hstep3) hgap2
  rw [clearAt_R_iff (g i) c.X]
  exact ⟨c.j i, Set.mem_Icc.mpr ⟨hmem1, hmem2⟩⟩

#print axioms windowCert_clear

/-- The clear window is nonempty and inside `W₀`: `X/8 ∈ [1/8, 7/8]` is lonely. -/
theorem windowCert_lonely (c : WindowCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) :
    ∃ t ∈ Set.Icc (1 / 8 : ℝ) (7 / 8), Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) t := by
  have hx1 := c.hXY₁
  have hx2 := c.hXY₂
  have hx3 := c.hXY₃
  refine ⟨c.X / 8, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
  exact (lonelyAt_image g _).mpr (windowCert_clear c g hbox)

#print axioms windowCert_lonely

/-- **No carve** from a window type: the carve would cover `R = X ∈ [1,7]`, putting a reading
in the way inside the clear window. -/
theorem windowCert_noCarve (c : WindowCert) (g : Fin 7 → ℝ)
    (hbox : ∀ i, c.lo i ≤ g i ∧ g i ≤ c.hi i) : NoCarve g := by
  intro hcarve
  obtain ⟨ρ, hρmem, j, hz1, hz2⟩ := hcarve c.X c.hXY₁ (le_trans c.hXY₂ c.hXY₃)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz1' : (((8 * j - 1 : ℤ) : ℝ)) < g i * c.X := by push_cast; linarith
  have hz2' : g i * c.X < (((8 * j + 1 : ℤ) : ℝ)) := by push_cast; linarith
  have hway := inWay_of_zone (ρ := g i) (R := c.X) hz1' hz2'
  have hclear := windowCert_clear c g hbox i
  unfold Fresh.InWay at hway
  linarith

#print axioms windowCert_noCarve

/-- The coupled two-reading corner principle (E833's linear inequalities `A ρ_t ≤ B ρ_s`):
over a rectangle, `A x ≤ B y` for ALL pairs holds iff it holds at the extreme corner
`(hi_t, lo_s)` (for `A, B ≥ 0`). -/
theorem pair_corner {A B lo_t hi_t lo_s hi_s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlt : lo_t ≤ hi_t) (hls : lo_s ≤ hi_s) :
    ((∀ x ∈ Set.Icc lo_t hi_t, ∀ y ∈ Set.Icc lo_s hi_s, A * x ≤ B * y) ↔ A * hi_t ≤ B * lo_s) := by
  constructor
  · intro h
    exact h hi_t (Set.mem_Icc.mpr ⟨hlt, le_rfl⟩) lo_s (Set.mem_Icc.mpr ⟨le_rfl, hls⟩)
  · intro h x hx y hy
    rw [Set.mem_Icc] at hx hy
    calc A * x ≤ A * hi_t := mul_le_mul_of_nonneg_left hx.2 hA
      _ ≤ B * lo_s := h
      _ ≤ B * y := mul_le_mul_of_nonneg_left hy.1 hB

#print axioms pair_corner

/-! ## (c) The plane-split certificate (E833 item 1(c)) -/

/-- The plane-split principle: certificates on the two sides of a plane `h = 0` cover the
box.  Each side certificate is an implication over its half (unclipped full-box form), so the
split is vacuous-safe and composes with (a), (b) and (e). -/
theorem noCarve_split (h : (Fin 7 → ℝ) → ℝ) (g : Fin 7 → ℝ)
    (h₁ : h g ≤ 0 → NoCarve g) (h₂ : h g ≥ 0 → NoCarve g) : NoCarve g := by
  rcases le_total (h g) 0 with hle | hge
  · exact h₁ hle
  · exact h₂ hge

#print axioms noCarve_split

/-- The canonical tie plane `h₁ = ρ₇ − 7ρ₅` (E830's exact two-link cycle of product 1). -/
-- STANDING: DEFINITION
def planeH1 (g : Fin 7 → ℝ) : ℝ := g 6 - 7 * g 4

/-- The canonical tie plane `h₂ = 3ρ₆ − 5ρ₄` (E832 item 4: links `ρ₄` lap 1 → `ρ₆` lap 2 and
`ρ₆` lap 3 → `ρ₄` lap 2). -/
-- STANDING: DEFINITION
def planeH2 (g : Fin 7 → ℝ) : ℝ := 3 * g 5 - 5 * g 3

/-- The straddler tie plane `h₃ = 25ρ₇ − 89ρ₅`: the exit-exit tangency plane (`89/ρ₇ =
25/ρ₅`; NOT an E830 seam-cycle plane — the cycle form is parity-refuted, see the module
docstring (iv)); its certificate is the pinch-point certificate (e). -/
-- STANDING: DEFINITION
def planeH3 (g : Fin 7 → ℝ) : ℝ := 25 * g 6 - 89 * g 4

/-! ## (d) Dyadic-box totality (the covering step, Lean form) -/

/-- A closed dyadic box of depth `D`: readings `g i ∈ [k i/D, (k i+1)/D]` (E832 item 1's box;
closed, so the children of the halving enumeration are included). -/
-- STANDING: DEFINITION
def InDyadicBox (D : ℕ) (k : Fin 7 → ℤ) (g : Fin 7 → ℝ) : Prop :=
  ∀ i, ((k i : ℝ) / D) ≤ g i ∧ g i ≤ (((k i + 1 : ℤ) : ℝ)) / D

/-- **[PROVISIONAL: covering]**, claim named: the closed boxes of the enumeration cover every
sorted readings vector — take `k i = ⌊D·g i⌋`, which is non-decreasing when `g` is, and the
closed box `[⌊Dg⌋/D, (⌊Dg⌋+1)/D]` contains `g`.  (E832 item 1: "the closed boxes of the
enumeration cover every sorted `(ρ₂,…,ρ₇)` with `ρ₇` in the stated range".) -/
theorem box_totality (g : Fin 7 → ℝ) (hmono : ∀ i j, i ≤ j → g i ≤ g j) (D : ℕ) (hD : 1 ≤ D) :
    InDyadicBox D (fun i => Int.floor (D * g i)) g ∧
      ∀ i j, i ≤ j → Int.floor (D * g i) ≤ Int.floor (D * g j) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · intro i
    have hf1 : ((Int.floor (D * g i) : ℤ) : ℝ) ≤ D * g i := Int.floor_le _
    have hf2 : D * g i < ((Int.floor (D * g i) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hup : ((Int.floor (D * g i) : ℤ) : ℝ) + 1
        = (((Int.floor (D * g i) : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
    constructor
    · rw [div_le_iff₀ hD']
      linarith
    · rw [le_div_iff₀ hD']
      linarith [hf2, hup]
  · intro i j hij
    exact Int.floor_mono (mul_le_mul_of_nonneg_left (hmono i j hij) hD'.le)

#print axioms box_totality

/-- The covering over a range `[a, b)` of `ρ₇` (integer endpoints, as in E832's sweeps
`[25,29)`, `[29,37)`, `[37,39)`, `[39,41)`): the box index `k 6 = ⌊D·g 6⌋` lies in
`[a·D, b·D − 1]`.  The certificate domains are the FULL closed boxes; the boxes' surplus past
`b` (up to `(b·D)/D = b + 1/D`) and below `a` is harmless: the certificates are implications,
vacuous off their boxes, and the surplus is named here rather than clipped.
**[PROVISIONAL: covering]**, claim named: the closed boxes with `k 6` in that index range
cover every sorted readings vector with `ρ₇` in `[a, b)`. -/
theorem box_cover_range (g : Fin 7 → ℝ) (hmono : ∀ i j, i ≤ j → g i ≤ g j) (D : ℕ) (hD : 1 ≤ D)
    (a b : ℤ) : (a : ℝ) ≤ g 6 → g 6 < (b : ℝ) →
      ∃ k : Fin 7 → ℤ, InDyadicBox D k g ∧ a * D ≤ k 6 ∧ k 6 ≤ b * D - 1 := by
  intro hlo hhi
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨htot, _⟩ := box_totality g hmono D hD
  refine ⟨fun i => Int.floor (D * g i), htot, ?_, ?_⟩
  · show a * D ≤ Int.floor (D * g 6)
    have hfold : ((a * (D : ℤ) : ℤ) : ℝ) = (a : ℝ) * (D : ℝ) := by push_cast; ring
    have hd : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    have h1 : ((a : ℝ)) * ((D : ℝ)) ≤ (g 6) * ((D : ℝ)) :=
      mul_le_mul_of_nonneg_right hlo hd.le
    have h2 : (g 6) * ((D : ℝ)) = ((D : ℝ)) * g 6 := mul_comm _ _
    have hkey : ((a * (D : ℤ) : ℤ) : ℝ) ≤ (D : ℝ) * g 6 := by rw [hfold]; linarith
    rw [Int.le_floor (a := (D : ℝ) * g 6)]
    linarith
  · show Int.floor (D * g 6) ≤ b * D - 1
    have h1 : (D : ℝ) * g 6 < (D : ℝ) * ((b : ℝ)) := mul_lt_mul_of_pos_left hhi hD'
    have h2 : (D : ℝ) * ((b : ℝ)) = ((b : ℝ)) * (D : ℝ) := mul_comm _ _
    have hkey : D * g 6 < ((b * D : ℤ) : ℝ) := by push_cast; linarith [h1, h2]
    have hfl : Int.floor (D * g 6) < b * D := Int.floor_lt.mpr hkey
    omega

#print axioms box_cover_range

/-- Children cover the parent (the halving step of the enumeration, E832 item 1): a box at
depth `D` is covered by the children at depth `2D` with index `k' i` in `[2k i, 2k i + 2]`.
(The boxes are CLOSED, so the parent's right face `(k i + 1)/D` lands in the child
`2k i + 2` — the third child; closed boxes tile with face overlaps, which is harmless for the
certificates: each is an implication over its box.  E832's "children with no non-decreasing
selection dropped" is the data-side of the same convention.)
**[PROVISIONAL: covering]**, claim named: the halved children cover the box. -/
theorem refine_cover {D : ℕ} (hD : 1 ≤ D) (k : Fin 7 → ℤ) (g : Fin 7 → ℝ)
    (h : InDyadicBox D k g) :
    ∃ k' : Fin 7 → ℤ, InDyadicBox (2 * D) k' g ∧
      ∀ i, (2 * k i : ℤ) ≤ k' i ∧ k' i ≤ 2 * k i + 2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h2D : (0 : ℝ) < (2 : ℝ) * (D : ℝ) := by positivity
  have hfold2 : ((2 * D : ℕ) : ℝ) = (2 : ℝ) * (D : ℝ) := by push_cast; ring
  refine ⟨fun i => Int.floor (2 * D * g i), ?_, fun i => ?_⟩
  · intro i
    obtain ⟨h1, h2⟩ := h i
    have hlo : ((2 * k i : ℤ) : ℝ) ≤ 2 * D * g i := by
      have e : ((2 * k i : ℤ) : ℝ) = 2 * ((k i : ℤ) : ℝ) := by push_cast; ring
      have hkey : ((k i : ℤ) : ℝ) ≤ g i * (D : ℝ) := (div_le_iff₀ hD').mp h1
      linarith
    have hhi : 2 * D * g i ≤ (((2 * k i + 1 : ℤ) : ℝ)) + 1 := by
      have e : (((2 * k i + 1 : ℤ) : ℝ)) + 1 = 2 * (((k i + 1 : ℤ) : ℝ)) := by push_cast; ring
      have hkey : g i * (D : ℝ) ≤ ((k i + 1 : ℤ) : ℝ) := (le_div_iff₀ hD').mp h2
      linarith
    have hf1 : ((Int.floor (2 * D * g i) : ℤ) : ℝ) ≤ 2 * D * g i := Int.floor_le _
    have hf2 : 2 * D * g i < ((Int.floor (2 * D * g i) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hup : ((Int.floor (2 * D * g i) : ℤ) : ℝ) + 1
        = (((Int.floor (2 * D * g i) : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
    constructor
    · show ((Int.floor (2 * D * g i) : ℤ) : ℝ) / ((2 * D : ℕ) : ℝ) ≤ g i
      rw [hfold2, div_le_iff₀ h2D]
      linarith
    · show g i ≤ (((Int.floor (2 * D * g i) : ℤ) + 1 : ℤ) : ℝ) / ((2 * D : ℕ) : ℝ)
      rw [hfold2, le_div_iff₀ h2D]
      linarith [hf2, hup]
  · obtain ⟨h1, h2⟩ := h i
    have hlo : ((2 * k i : ℤ) : ℝ) ≤ 2 * D * g i := by
      have e : ((2 * k i : ℤ) : ℝ) = 2 * ((k i : ℤ) : ℝ) := by push_cast; ring
      have hkey : ((k i : ℤ) : ℝ) ≤ g i * (D : ℝ) := (div_le_iff₀ hD').mp h1
      linarith
    have hkey2 : 2 * D * g i ≤ (((2 * k i + 2 : ℤ) : ℝ)) := by
      have e : (((2 * k i + 2 : ℤ) : ℝ)) = 2 * (((k i + 1 : ℤ) : ℝ)) := by push_cast; ring
      have hkey : g i * (D : ℝ) ≤ ((k i + 1 : ℤ) : ℝ) := (le_div_iff₀ hD').mp h2
      have h2 : (2 : ℝ) * (g i * (D : ℝ)) ≤ 2 * ((k i + 1 : ℤ) : ℝ) := by linarith
      linarith [e, h2]
    show (2 * k i : ℤ) ≤ Int.floor (2 * D * g i) ∧ Int.floor (2 * D * g i) ≤ 2 * k i + 2
    constructor
    · rw [Int.le_floor (a := (2 : ℝ) * (D : ℝ) * g i)]
      linarith
    · have hst : (((2 * k i + 3 : ℤ) : ℝ)) = (((2 * k i + 2 : ℤ) : ℝ)) + 1 := by
        push_cast; ring
      have hflt : Int.floor (2 * D * g i) < 2 * k i + 3 := by
        rw [Int.floor_lt (a := (2 : ℝ) * (D : ℝ) * g i)]
        linarith [hkey2, hst]
      linarith

#print axioms refine_cover


/-! ## (e) The pinch-point certificate — SUPERSEDED

The pinch schema for the tangency plane h₃ = 25ρ₇ − 89ρ₅ (exit-exit equality) was drafted here
2026-11-07 but did not compile (`div_le_div_iff₀` / `mul_div_assoc` rewrite patterns fail in this
import context).  The completed, general, axiom-clean version lives in `Fresh/PinchCert.lean`
(`TangentPlane`, `tangentPlane_noCarve`, `planeH3_lonely`, `PinchIntCond`, `pinchIntCert_of_dyadic`,
`pinchIntCert_of_dyadic_h3`), which supersedes this section entirely.  Nothing else in this file
depends on it.  Previous-agent provenance: the (e) draft here was the first attempt (2026-11-07
~12:20); the completion note is by the coordinating session, 2026-11-07 ~21:30, with the file's
(a)–(d) sections byte-identical to the pre-truncation state.
-/
