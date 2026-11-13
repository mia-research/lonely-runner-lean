import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.KTaxonomy
import Fresh.FilterSkeleton
import Fresh.FrontierFamilyCap

/-!
# The pinch-point certificate for tangency planes (the h₃-type, fourth schema)

Written 2026-11-07.  New file; nothing existing is edited.  Self-contained: imports the
framework stack, not `Fresh.Certs` (whose fourth-schema draft this supersedes in cleaner
form).

The h₃ = 25ρ₇ − 89ρ₅ straddler mechanism (log `tail_h3_pinch_v1.py`, 509/509 certified;
`tail_h3_cycles_v1.py`, [T 0] for every seam-cycle route): the plane h₃ = 0 is the
EXIT-EXIT TANGENCY 89/ρ₇ = 25/ρ₅ — ρ₇'s lap-11 zone exit edge coinciding with ρ₅'s lap-3
zone exit edge.  Exit-meets-exit is NOT a seam (seams are exit-meets-entry), so no
E830-style link-cycle identity exists for h₃: the mission-candidate product
(89/(8a−1))·(25/(8b−1)) = 1 needs (8a−1)(8b−1) = 2225 = 5²·89, whose divisors are 1 or 5
mod 8, never 7 — entry edges are 7 mod 8 (exhausted over the leaf lap ranges, [T 0] for
2-, 3- and 4-link cycles; the plane sits strictly between the seams 81/23 = 3.5217 and
25/7 = 3.5714).

The certificate: on the tangency plane ρ₇/ρ₅ = (8a+1)/(8b+1) — BOTH edges exit edges
(a = 11, b = 3 for h₃) — the point R* = (8b+1)/ρ₅ = (8a+1)/ρ₇ sits exactly at BOTH
readings' clearance edges (phases (8b+1)/8 and (8a+1)/8, `distInt` = 1/8, the closed
condition holds), so R* is covered by neither.  If every other reading's phase ratio
(8b+1)ρ_r/ρ₅ lies in a closed gap `[8j+1, 8j+7]` (linear-in-ρ inequalities once the plane
equation is substituted), then R*/8 is a lonely instant for the whole arrangement:
`tangentPlane_lonely`, `tangentPlane_noCarve`.  A fourth certificate type: the clear point
is a rational FUNCTION of the readings (R* = (8b+1)/ρ₅ on the plane), not a fixed R₀.

The box-level integer conditions on the grid indices (the data-side decidable check,
`(8j_i+1)(hi5P+1) ≤ (8b+1)k_i ∧ (8b+1)(k_i+1) ≤ (8j_i+7)lo5P` with `lo5P/hi5P` the grid
bounds of the plane region's ρ₅-range — 509/509 in `tail_h3_pinch_grid_v1.py`) are
formalized in section (c) as `PinchIntCond` / `pinchIntCert_of_dyadic` (parametric (a, b)) /
`pinchIntCert_of_dyadic_h3` (the h₃ instantiation); what remains OWED is the box-spine
three-region composition (end of section (c)).

Provenance note: completed 2026-11-07 (same day) — residual elaboration plumbing in
`tangentPlane_lonely` fixed (the two `by_cases` branches needed `rho5_phase`'s unused
implicit `a` fixed by hand and `rho7_phase`'s explicit `hplane` passed; a bare `omega`
before each branch and a trailing `ring` after a goal-closing `field_simp` removed), the two
`PlaneH3` conversion theorems repaired, and section (c) delivered.

Composition (the three-region split, data-side): box + tangency plane ⇒ left (window
type) ∨ right (window type) ∨ on-plane (this certificate); the sides' window types are the
`Fresh.Certs` schemas, the plane strip is this file's.
-/

open Classical

namespace Fresh.Pinch

/-! ## Helpers -/

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

/-- The no-carve predicate for a readings function (the certificates' conclusion). -/
-- STANDING: DEFINITION
def NoCarve (g : Fin 7 → ℝ) : Prop :=
  ¬ Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)

/-- A strict zone `(8j−1, 8j+1)` at `R` puts the reading in the way at the instant `R/8`. -/
theorem inWay_of_zone {ρ R : ℝ} {j : ℤ}
    (h1 : (((8 * j - 1 : ℤ) : ℝ)) < ρ * R) (h2 : ρ * R < (((8 * j + 1 : ℤ) : ℝ))) :
    Fresh.InWay ρ (R / 8) := by
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

/-! ## (a) The tangency plane and its pinch point -/

/-- The tangency plane of the lap pair `(a, b)`: ρ₇/ρ₅ = (8a+1)/(8b+1) — both edges exit
edges, so on the plane the two zones die together.  The h₃ case is `a = 11, b = 3`
(`25ρ₇ = 89ρ₅`). -/
-- STANDING: DEFINITION
def TangentPlane (a b : ℕ) (g : Fin 7 → ℝ) : Prop := (8 * b + 1 : ℝ) * g 6 = (8 * a + 1) * g 4

/-- On the tangency plane both readings are positive (the plane's ratio is positive). -/
theorem g6pos {a b : ℕ} {g : Fin 7 → ℝ} (hpos4 : (0 : ℝ) < g 4) (hplane : TangentPlane a b g) :
    (0 : ℝ) < g 6 := by
  unfold TangentPlane at hplane
  have h1 : (0 : ℝ) < (8 * a + 1 : ℝ) := by positivity
  have h2 : (0 : ℝ) < (8 * b + 1 : ℝ) := by positivity
  have h6eq : g 6 = ((8 * a + 1 : ℝ) * g 4) / (8 * b + 1 : ℝ) := by
    rw [eq_div_iff (ne_of_gt (by positivity : (0 : ℝ) < (8 * b + 1 : ℝ)))]
    linarith
  rw [h6eq]
  exact div_pos (mul_pos h1 hpos4) h2

#print axioms g6pos

/-- The pinch point: on the plane, R* = (8b+1)/ρ₅ = (8a+1)/ρ₇ exactly. -/
-- STANDING: DEFINITION
noncomputable def Rstar (a b : ℕ) (g : Fin 7 → ℝ) : ℝ := (8 * b + 1) / g 4

theorem rstar_eq {a b : ℕ} {g : Fin 7 → ℝ} (hpos4 : (0 : ℝ) < g 4)
    (hplane : TangentPlane a b g) :
    Rstar a b g = (8 * a + 1) / g 6 := by
  have hg6 : (0 : ℝ) < g 6 := g6pos hpos4 hplane
  unfold Rstar
  rw [div_eq_div_iff (ne_of_gt hpos4) (ne_of_gt hg6)]
  exact hplane

#print axioms rstar_eq

/-- On the plane, reading 5's phase at R* is exactly `(8b+1)/8`: distInt = 1/8, the closed
clear condition holds — R* is the reading's zone EXIT edge, covered by neither side. -/
theorem rho5_phase {a b : ℕ} {g : Fin 7 → ℝ} (hpos4 : (0 : ℝ) < g 4) :
    (8 * b + 1 : ℝ) * g 4 / (8 * g 4) = (8 * b + 1) / 8 := by
  have hg4ne : g 4 ≠ 0 := ne_of_gt hpos4
  have hc1 : ((8 : ℝ) * (b : ℝ) + 1) * g 4 = g 4 * ((8 : ℝ) * (b : ℝ) + 1) := mul_comm _ _
  have hc2 : (8 : ℝ) * g 4 = g 4 * 8 := mul_comm _ _
  rw [hc1, hc2]
  exact mul_div_mul_left (a := (8 : ℝ) * (b : ℝ) + 1) (b := 8) (c := g 4) hg4ne

#print axioms rho5_phase

/-- On the plane, reading 7's phase at R* is exactly `(8a+1)/8`: distInt = 1/8. -/
theorem rho7_phase {a b : ℕ} {g : Fin 7 → ℝ} (hpos4 : (0 : ℝ) < g 4)
    (hplane : TangentPlane a b g) :
    (8 * a + 1 : ℝ) * g 4 / (8 * g 4) = (8 * a + 1) / 8 := by
  have hg4ne : g 4 ≠ 0 := ne_of_gt hpos4
  have hc1 : ((8 : ℝ) * (a : ℝ) + 1) * g 4 = g 4 * ((8 : ℝ) * (a : ℝ) + 1) := mul_comm _ _
  have hc2 : (8 : ℝ) * g 4 = g 4 * 8 := mul_comm _ _
  rw [hc1, hc2]
  exact mul_div_mul_left (a := (8 : ℝ) * (a : ℝ) + 1) (b := 8) (c := g 4) hg4ne

#print axioms rho7_phase

/-! ## (b) Soundness on the plane (per-arrangement form) -/

/-- **The pinch-point soundness** (any lap pair `(a, b)`): for an arrangement exactly on the
tangency plane with `R* = (8b+1)/ρ₅ ∈ [1,7]` and every other reading's phase ratio
`(8b+1)ρ_r/ρ₅` in a closed gap `[8j+1, 8j+7]` (linear-in-ρ inequalities; ρ₅ and ρ₇ need no
condition — their phases at R* are exactly `(8b+1)/8` and `(8a+1)/8`), the pinch point
`R*/8` is a lonely instant of the whole arrangement. -/
theorem tangentPlane_lonely (a b : ℕ) (g : Fin 7 → ℝ) (j : Fin 7 → ℤ)
    (hpos4 : (0 : ℝ) < g 4) (hplane : TangentPlane a b g)
    (hR1 : (1 : ℝ) ≤ Rstar a b g) (hR7 : Rstar a b g ≤ 7)
    (hgap : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      (((8 * j i : ℤ) + 1) * g 4 ≤ (8 * b + 1) * g i ∧
        (8 * b + 1) * g i ≤ ((8 * j i : ℤ) + 7) * g 4)) :
    Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) (Rstar a b g / 8) := by
  have hg4ne : g 4 ≠ 0 := ne_of_gt hpos4
  have hcomm : ∀ i : Fin 7, g i * (Rstar a b g / 8) = (8 * b + 1) * g i / (8 * g 4) := by
    intro i
    unfold Rstar
    field_simp
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  show (1 / 8 : ℝ) ≤ distInt (g i * (Rstar a b g / 8))
  by_cases hi4 : i = 4
  · subst hi4
    -- `rho5_phase`'s unused implicit `a` must be fixed by hand or `rw` leaks an `ℕ` goal
    rw [hcomm, rho5_phase (a := a) hpos4]
    have h8b : ((8 : ℝ) * (b : ℝ) + 1) / 8 = (b : ℝ) + 1 / 8 := by field_simp
    rw [h8b]
    have hdist := Fresh.Cascade.distInt_eighth_add_int ((b : ℕ) : ℤ)
    rw [add_comm (1 / 8) (((b : ℕ) : ℤ) : ℝ)] at hdist
    push_cast at hdist ⊢
    linarith
  by_cases hi6 : i = 6
  · subst hi6
    rw [hcomm, hplane, rho7_phase hpos4 hplane]
    have h8a : ((8 : ℝ) * (a : ℝ) + 1) / 8 = (a : ℝ) + 1 / 8 := by field_simp
    rw [h8a]
    have hdist := Fresh.Cascade.distInt_eighth_add_int ((a : ℕ) : ℤ)
    rw [add_comm (1 / 8) (((a : ℕ) : ℤ) : ℝ)] at hdist
    push_cast at hdist ⊢
    linarith
  · have hgap1 := (hgap i hi4 hi6).1
    have hgap2 := (hgap i hi4 hi6).2
    have hxlo : (((8 * j i : ℤ) + 1 : ℝ)) / 8 ≤ (8 * b + 1 : ℝ) * g i / (8 * g 4) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (by positivity : (0 : ℝ) < 8 * g 4)]
      nlinarith [hgap1]
    have hxhi : (8 * b + 1 : ℝ) * g i / (8 * g 4) ≤ (((8 * j i : ℤ) + 7 : ℝ)) / 8 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * g 4) (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hgap2]
    have h8x1 : ((8 * j i : ℤ) + 1 : ℝ) / 8 = ((j i : ℤ) : ℝ) + 1 / 8 := by
      push_cast
      ring
    have h8x2 : (((8 * j i : ℤ) + 7 : ℝ)) / 8 = ((j i : ℤ) : ℝ) + 7 / 8 := by
      push_cast
      ring
    have hx : (8 * b + 1 : ℝ) * g i / (8 * g 4)
        ∈ Set.Icc (((j i : ℤ) : ℝ) + 1 / 8) (((j i : ℤ) : ℝ) + 7 / 8) := by
      rw [← h8x1, ← h8x2]
      exact Set.mem_Icc.mpr ⟨hxlo, hxhi⟩
    have hclr := (Fresh.KTaxonomy.distInt_ge_eighth_iff
      ((8 * b + 1) * g i / (8 * g 4))).mpr ⟨j i, hx⟩
    rwa [← hcomm i] at hclr

#print axioms tangentPlane_lonely

/-- The lonely instant lies in `W₀`: `R*/8 ∈ [1/8, 7/8]` from `R* ∈ [1,7]`. -/
theorem tangentPlane_mem_window (a b : ℕ) (g : Fin 7 → ℝ)
    (hpos4 : (0 : ℝ) < g 4) (hR1 : (1 : ℝ) ≤ Rstar a b g) (hR7 : Rstar a b g ≤ 7) :
    Rstar a b g / 8 ∈ Set.Icc (1 / 8 : ℝ) (7 / 8) := by
  exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

#print axioms tangentPlane_mem_window

/-- **planeNoCarve**: a box's on-plane arrangements are not carves of `[1,7]` — the carve
would cover `R = R* ∈ [1,7]`, putting a reading in the way at the lonely instant. -/
theorem tangentPlane_noCarve (a b : ℕ) (g : Fin 7 → ℝ) (j : Fin 7 → ℤ)
    (hpos4 : (0 : ℝ) < g 4) (hplane : TangentPlane a b g)
    (hR1 : (1 : ℝ) ≤ Rstar a b g) (hR7 : Rstar a b g ≤ 7)
    (hgap : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      (((8 * j i : ℤ) + 1) * g 4 ≤ (8 * b + 1) * g i ∧
        (8 * b + 1) * g i ≤ ((8 * j i : ℤ) + 7) * g 4)) :
    NoCarve g := by
  intro hcarve
  obtain ⟨ρ, hρmem, k, hz1, hz2⟩ := hcarve (Rstar a b g) hR1 hR7
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz1' : g i * (Rstar a b g) < (((8 * k + 1 : ℤ) : ℝ)) := by
    push_cast at hz2 ⊢
    linarith
  have hz2' : (((8 * k - 1 : ℤ) : ℝ)) < g i * (Rstar a b g) := by
    push_cast at hz1 ⊢
    linarith
  have hway := inWay_of_zone (ρ := g i) (R := Rstar a b g) hz2' hz1'
  have hclear := tangentPlane_lonely a b g j hpos4 hplane hR1 hR7 hgap (g i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  unfold Fresh.InWay at hway
  linarith

#print axioms tangentPlane_noCarve

/-! ## (c) The box-level integer conditions (the decidable data-side check) -/

/-- A closed dyadic box of depth `D` (the `Fresh.Certs.InDyadicBox` shape, restated here so
this file stays self-contained: no `Fresh.Certs` import). -/
-- STANDING: DEFINITION
def InBox (D : ℕ) (k : Fin 7 → ℤ) (g : Fin 7 → ℝ) : Prop :=
  ∀ i, ((k i : ℝ) / D) ≤ g i ∧ g i ≤ (((k i + 1 : ℤ) : ℝ)) / D

/-- The box-level integer conditions of the pinch certificate for the tangency plane `(a, b)`
— exactly the data-side decidable test of `tail_h3_pinch_grid_v1.py` (509/509 certified,
h₃ band data): the plane region's ρ₅-grid window is `[lo5P/D, (hi5P+1)/D]`, the pinch point
range holds (`hi5P+1 ≤ (8b+1)D`, `(8b+1)D ≤ 7·lo5P`, i.e. R* = (8b+1)/ρ₅ ∈ [1,7] on the
window), and per other reading `i` the phase-ratio window of `tangentPlane_lonely` holds over
the WHOLE plane-region box as the integer faces
`(8m_i+1)(hi5P+1) ≤ (8b+1)k_i ∧ (8b+1)(k_i+1) ≤ (8m_i+7)lo5P`.  All-integer, so decidable. -/
-- STANDING: DEFINITION
def PinchIntCond (a b : ℕ) (D : ℤ) (k m : Fin 7 → ℤ) (lo5P hi5P : ℤ) : Prop :=
  hi5P + 1 ≤ (8 * b + 1) * D ∧ (8 * b + 1) * D ≤ 7 * lo5P ∧
    (∀ i : Fin 7, i ≠ 4 → i ≠ 6 → 0 ≤ m i) ∧
    (∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      (8 * m i + 1) * (hi5P + 1) ≤ (8 * b + 1) * k i ∧
        (8 * b + 1) * (k i + 1) ≤ (8 * m i + 7) * lo5P)

instance (a b : ℕ) (D : ℤ) (k m : Fin 7 → ℤ) (lo5P hi5P : ℤ) :
    Decidable (PinchIntCond a b D k m lo5P hi5P) := by
  unfold PinchIntCond
  infer_instance

/-- **The box-level pinch certificate, plane region**: the integer conditions build the
per-arrangement hypotheses of `tangentPlane_noCarve`.  For every arrangement whose readings
lie in the closed dyadic box `g i ∈ [k_i/D, (k_i+1)/D]`, whose ρ₅ lies in the plane region's
grid window `g 4 ∈ [lo5P/D, (hi5P+1)/D]`, and which sits exactly on the tangency plane
(`TangentPlane a b g`), the arrangement is not a carve of `[1,7]`: the pinch point
R* = (8b+1)/ρ₅ = (8a+1)/ρ₇ lies in [1,7] (window bounds against `(8b+1)D`), and every other
reading's phase ratio `(8b+1)ρ_r/ρ₅` at R* lies in a closed gap, by the integer chain
`(8m_i+1)·g4 ≤ (8m_i+1)(hi5P+1)/D ≤ (8b+1)k_i/D ≤ (8b+1)g_i` (and the upper twin
`(8b+1)g_i ≤ (8b+1)(k_i+1)/D ≤ (8m_i+7)lo5P/D ≤ (8m_i+7)g4`). -/
theorem pinchIntCert_of_dyadic (a b : ℕ) {D : ℕ} (hD : 0 < D)
    (k m : Fin 7 → ℤ) {lo5P hi5P : ℤ} (hcond : PinchIntCond a b (D : ℤ) k m lo5P hi5P)
    (g : Fin 7 → ℝ) (hbox : InBox D k g)
    (h5P : ((lo5P : ℝ)) / D ≤ g 4 ∧ g 4 ≤ ((hi5P + 1 : ℤ) : ℝ) / D)
    (hplane : TangentPlane a b g) : NoCarve g := by
  obtain ⟨hR₁int, hR₇int, hmposint, hwin⟩ := hcond
  have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hlo5Ppos : (0 : ℤ) < lo5P := by
    have hb1Z : (0 : ℤ) < 8 * b + 1 := by omega
    have hDZ : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
    have h3 : (0 : ℤ) < (8 * b + 1) * (D : ℤ) := mul_pos hb1Z hDZ
    omega
  have hg4 : (0 : ℝ) < g 4 :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast hlo5Ppos) hD') h5P.1
  have hR1 : (1 : ℝ) ≤ Rstar a b g := by
    have h4' : g 4 ≤ (8 * b + 1 : ℝ) := by
      have e1 : ((hi5P + 1 : ℤ) : ℝ) / (D : ℝ) ≤ (8 * b + 1 : ℝ) := by
        rw [div_le_iff₀ hD']
        exact_mod_cast hR₁int
      exact le_trans h5P.2 e1
    unfold Rstar
    exact (le_div_iff₀ hg4).mpr (by linarith)
  have hR7 : Rstar a b g ≤ 7 := by
    unfold Rstar
    have hkey : (8 * b + 1 : ℝ) ≤ (7 : ℝ) * g 4 := by
      have hc : (8 * b + 1 : ℝ) * (D : ℝ) ≤ (7 : ℝ) * ((lo5P : ℤ) : ℝ) := by
        exact_mod_cast hR₇int
      have h1 : (8 * b + 1 : ℝ) ≤ (7 : ℝ) * ((lo5P : ℤ) : ℝ) / (D : ℝ) := by
        rw [le_div_iff₀ hD']
        exact hc
      have h2 : (7 : ℝ) * ((lo5P : ℤ) : ℝ) / (D : ℝ) ≤ (7 : ℝ) * g 4 := by
        calc (7 : ℝ) * ((lo5P : ℤ) : ℝ) / (D : ℝ)
            = (7 : ℝ) * (((lo5P : ℤ) : ℝ) / (D : ℝ)) := by ring
          _ ≤ (7 : ℝ) * g 4 := mul_le_mul_of_nonneg_left h5P.1 (by norm_num)
      linarith
    exact (div_le_iff₀ hg4).mpr hkey
  refine tangentPlane_noCarve a b g m hg4 hplane hR1 hR7 ?_
  intro i hi4 hi6
  have hmpos := hmposint i hi4 hi6
  obtain ⟨hblo, hbhi⟩ := hbox i
  obtain ⟨h5lo, h5hi⟩ := h5P
  obtain ⟨w1, w2⟩ := hwin i hi4 hi6
  constructor
  · -- lower: (8m_i+1)·g4 ≤ (8m_i+1)(hi5P+1)/D ≤ (8b+1)k_i/D ≤ (8b+1)g_i
    have hstep1 : ((8 * m i : ℤ) + 1 : ℝ) * g 4
        ≤ ((8 * m i : ℤ) + 1 : ℝ) * (((hi5P + 1 : ℤ) : ℝ) / (D : ℝ)) := by
      refine mul_le_mul_of_nonneg_left h5hi ?_
      have h81 : (0 : ℤ) ≤ 8 * m i + 1 := by omega
      exact_mod_cast h81
    have hstep2 : ((8 * m i : ℤ) + 1 : ℝ) * (((hi5P + 1 : ℤ) : ℝ) / (D : ℝ))
        ≤ (8 * b + 1 : ℝ) * (((k i : ℤ) : ℝ) / (D : ℝ)) := by
      have hc : ((8 * m i : ℤ) + 1 : ℝ) * ((hi5P + 1 : ℤ) : ℝ)
          ≤ (8 * b + 1 : ℝ) * ((k i : ℤ) : ℝ) := by
        exact_mod_cast w1
      calc ((8 * m i : ℤ) + 1 : ℝ) * (((hi5P + 1 : ℤ) : ℝ) / (D : ℝ))
          = ((8 * m i : ℤ) + 1 : ℝ) * ((hi5P + 1 : ℤ) : ℝ) / (D : ℝ) := by ring
        _ ≤ (8 * b + 1 : ℝ) * ((k i : ℤ) : ℝ) / (D : ℝ) := by
              refine (div_le_div_iff₀ hD' hD').mpr ?_
              exact mul_le_mul_of_nonneg_right hc hD'.le
        _ = (8 * b + 1 : ℝ) * (((k i : ℤ) : ℝ) / (D : ℝ)) := by ring
    have hstep3 : (8 * b + 1 : ℝ) * (((k i : ℤ) : ℝ) / (D : ℝ)) ≤ (8 * b + 1 : ℝ) * g i := by
      refine mul_le_mul_of_nonneg_left hblo ?_
      positivity
    linarith
  · -- upper twin: (8b+1)g_i ≤ (8b+1)(k_i+1)/D ≤ (8m_i+7)lo5P/D ≤ (8m_i+7)g4
    have hstep1 : (8 * b + 1 : ℝ) * g i
        ≤ (8 * b + 1 : ℝ) * (((k i + 1 : ℤ) : ℝ) / (D : ℝ)) := by
      refine mul_le_mul_of_nonneg_left hbhi ?_
      positivity
    have hstep2 : (8 * b + 1 : ℝ) * (((k i + 1 : ℤ) : ℝ) / (D : ℝ))
        ≤ (((8 * m i : ℤ) + 7 : ℝ)) * (((lo5P : ℤ) : ℝ) / (D : ℝ)) := by
      have hc : (8 * b + 1 : ℝ) * ((k i + 1 : ℤ) : ℝ)
          ≤ (((8 * m i : ℤ) + 7 : ℝ)) * ((lo5P : ℤ) : ℝ) := by
        exact_mod_cast w2
      calc (8 * b + 1 : ℝ) * (((k i + 1 : ℤ) : ℝ) / (D : ℝ))
          = (8 * b + 1 : ℝ) * ((k i + 1 : ℤ) : ℝ) / (D : ℝ) := by ring
        _ ≤ (((8 * m i : ℤ) + 7 : ℝ)) * ((lo5P : ℤ) : ℝ) / (D : ℝ) := by
              refine (div_le_div_iff₀ hD' hD').mpr ?_
              exact mul_le_mul_of_nonneg_right hc hD'.le
        _ = (((8 * m i : ℤ) + 7 : ℝ)) * (((lo5P : ℤ) : ℝ) / (D : ℝ)) := by ring
    have hstep3 : (((8 * m i : ℤ) + 7 : ℝ)) * (((lo5P : ℤ) : ℝ) / (D : ℝ))
        ≤ (((8 * m i : ℤ) + 7 : ℝ)) * g 4 := by
      refine mul_le_mul_of_nonneg_left h5lo ?_
      have h87 : (0 : ℤ) ≤ 8 * m i + 7 := by omega
      exact_mod_cast h87
    linarith

#print axioms pinchIntCert_of_dyadic

/-! ### Still OWED (box-spine composition, data-side driven)

The three-region split of a dyadic box straddling h₃ = 0 — left strip (window-type
certificate, `Fresh.Certs` schemas) ∨ right strip (window-type) ∨ on-plane strip (this
file's `pinchIntCert_of_dyadic_h3`) — as a single disjunction-form box theorem: the
composition itself is mechanical once the data side supplies, per box, the plane-region
ρ₅-grid window (`lo5P = ⌊f·D⌋`, `hi5P = ⌈g·D⌉ − 1` with `[f, g]` the exact plane∩face₅
interval) and the per-side window data.  The extraction of `lo5P/hi5P` from the face data is
integer arithmetic on the grid, hence decidable, but not yet formalized here. -/

/-! ## (d) The h₃ instantiation (a = 11, b = 3) -/

/-- The h₃ tangency plane: 25ρ₇ = 89ρ₅ (exit edges 8·11+1 = 89, 8·3+1 = 25). -/
-- STANDING: DEFINITION
def PlaneH3 (g : Fin 7 → ℝ) : Prop := (25 : ℝ) * g 6 = 89 * g 4

theorem planeH3_tangent {g : Fin 7 → ℝ} : PlaneH3 g ↔ TangentPlane 11 3 g := by
  constructor
  · intro h
    unfold PlaneH3 at h
    have he1 : (8 * 3 + 1 : ℝ) = 25 := by norm_num
    have he2 : (8 * 11 + 1 : ℝ) = 89 := by norm_num
    rw [← he1, ← he2] at h
    exact h
  · intro h
    unfold TangentPlane at h
    have he1 : (8 * (3 : ℕ) + 1 : ℝ) = 25 := by norm_num
    have he2 : (8 * (11 : ℕ) + 1 : ℝ) = 89 := by norm_num
    rw [he1, he2] at h
    exact h

#print axioms planeH3_tangent

/-- The h₃ box-level pinch certificate — the [17,23)-band data's decidable check: the
integer conditions at a := 11, b := 3 (so `(8b+1) = 25`: `hi5P+1 ≤ 25D`, `25D ≤ 7lo5P`,
`(8m_i+1)(hi5P+1) ≤ 25k_i ∧ 25(k_i+1) ≤ (8m_i+7)lo5P`) with the plane hypothesis in `PlaneH3`
form (25ρ₇ = 89ρ₅). -/
theorem pinchIntCert_of_dyadic_h3 {D : ℕ} (hD : 0 < D)
    (k m : Fin 7 → ℤ) {lo5P hi5P : ℤ} (hcond : PinchIntCond 11 3 (D : ℤ) k m lo5P hi5P)
    (g : Fin 7 → ℝ) (hbox : InBox D k g)
    (h5P : ((lo5P : ℝ)) / D ≤ g 4 ∧ g 4 ≤ ((hi5P + 1 : ℤ) : ℝ) / D)
    (hplane : PlaneH3 g) : NoCarve g :=
  pinchIntCert_of_dyadic 11 3 hD k m hcond g hbox h5P (planeH3_tangent.mp hplane)

#print axioms pinchIntCert_of_dyadic_h3

/-- The h₃ pinch-point soundness: on the plane 25ρ₇ = 89ρ₅, with R* = 25/ρ₅ = 89/ρ₇ ∈
[1,7] and the other readings' ratio phases 25ρ_r/ρ₅ in their closed gaps, the pinch point
R*/8 is a lonely instant of the whole arrangement. -/
theorem planeH3_lonely (g : Fin 7 → ℝ) (j : Fin 7 → ℤ)
    (hpos4 : (0 : ℝ) < g 4) (hplane : PlaneH3 g)
    (hR1 : (1 : ℝ) ≤ 25 / g 4) (hR7 : 25 / g 4 ≤ 7)
    (hgap : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      (((8 * j i : ℤ) + 1) * g 4 ≤ 25 * g i ∧ 25 * g i ≤ ((8 * j i : ℤ) + 7) * g 4)) :
    Fresh.Cascade.LonelyAt (Finset.image g Finset.univ) (25 / (8 * g 4)) := by
  unfold PlaneH3 at hplane
  have he1 : (8 * (3 : ℕ) + 1 : ℝ) = 25 := by norm_num
  have he2 : (8 * (11 : ℕ) + 1 : ℝ) = 89 := by norm_num
  rw [← he1, ← he2] at hplane
  -- bridge the h₃ literals through the (a, b) = (11, 3) Rstar form explicitly
  have hRs : Rstar 11 3 g = 25 / g 4 := by
    unfold Rstar
    norm_num
  rw [← hRs] at hR1 hR7
  have hgap' : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 →
      (((8 * j i : ℤ) + 1) * g 4 ≤ (8 * 3 + 1) * g i ∧
        (8 * 3 + 1) * g i ≤ ((8 * j i : ℤ) + 7) * g 4) := by
    intro i h4 h6
    obtain ⟨c1, c2⟩ := hgap i h4 h6
    rw [← he1] at c1 c2
    exact ⟨c1, c2⟩
  have hRs8 : Rstar 11 3 g / 8 = 25 / (8 * g 4) := by
    rw [hRs, div_div, mul_comm (g 4) 8]
  rw [← hRs8]
  exact tangentPlane_lonely 11 3 g j hpos4 hplane hR1 hR7 hgap'

#print axioms planeH3_lonely

end Fresh.Pinch
