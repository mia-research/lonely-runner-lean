import Fresh.BandTailCover

/-!
# The tail composition theorem: the pinned carve locus above 23, composed

Provenance: `experiments/n8/tailcomp2_lemma_v1.out` (Theorem S / Theorem U — the tail
composition, every case named with its kill), `tailcomp2_pincheck_v1.py/.out` (the exact
two-regime verification ledger), `tailrest_anchor_lemma_v1.out` (the anchor classification,
[T 105/105]), `tailrest_composition_v1.out` (pieces T1–T6 and the residue ledger).
Formalized 2026-11-14; new file, nothing existing is edited, nothing committed.

SETTING (R-coordinates, readings normalised with ρ₁ = 1, the pin `ρ₆ ≤ 49/7 = 7`).
`Fresh.BandTailCover` (GREEN) supplies the vocabulary and the two comb halves:
`InStrip` (the strips `C_j = (8j−1, 8j+1)`), `anchor_classification` (under the pin the
`R = 1` coverer of a carve is `ρ₇`'s self-anchor alone), `gap_carve_free` (every pinned gap
`G_m = (8m+1, 8m+7)` is carve-free — one comb argument), and `pinnedCarve_selfAnchor`.

CONTENT — the composition theorem `pinnedTail` in the mission's shape: under the pin, given
the strip instruments as explicit hypotheses and the case hypothesis
`(ρ₇ ≥ 25 ∨ ρ₇ ∈ (23,25))`, EITHER there is no carve of `[1,7]` OR `ρ₇` lies in the X24
locus `(23, 86989/3565]` — i.e. no carve of `[1,7]` with `ρ₇ ≥ 25` outside `(23,25)`, and
the only surviving carves above 23 are inside the attained X24 cap.  Case split on `ρ₇`'s
strip membership (via the self-anchor extraction `pinnedCarve_strip_ge25`):
* the anchor classification forces the `R = 1` coverer to be the self-anchor `(ρ₇, j)`;
  `ρ₇ ≥ 25` and `C₃ = (23,25)` open at 25 force the lap `j ≥ 4` (gaps and edges are already
  dead — a carve forces `ρ₇` INTO a strip, the gap corollary's contrapositive shadow);
* `j ≤ 6` (strips `C₄, C₅, C₆ = (31,33), (39,41), (47,49)`) is handed to the completed
  chase kills (hypothesis `Fresh.BandTailCover.StripChaseKill46`);
* `j ≥ 7` puts `ρ₇ ≥ 55 ≥ 50`, handed to the covering session's width certificate
  (hypothesis `Fresh.BandTailCover.TailAbove50Cover`; `Fresh.TailSlowWidth` carries the
  `native_decide` replay of the 1,287-root checker, whose `Lean.ofReduceBool` is outside
  this file's axiom discipline, and its `BandClearPoint` conclusion also lands in
  `W₀ ∪ W₁` — only the `s ≤ 7` branch discharges a `NoCarve` of `[1,7]`; the `NoCarve`-form
  instrument is OWED);
* the `(23,25)` branch is `C₃` itself: the strip-3 chase cap (hypothesis `Strip3Cap86989`,
  X24 attained) confines every carve there to `ρ₇ ≤ 86989/3565`.

The strengthened composition `pinnedTailLocus` consumes the strip-2 cap as well
(hypothesis `Strip2Cap511`, cap `511/31` attained): under the pin with `ρ₇ > 15`, either
no carve, or `ρ₇` lies in `(15, 511/31]` (strip 2) or `(23, 86989/3565]` (strip 3) — the
carve locus above 15, on the same instruments plus the m = 2 chase cap.

OWEDs (named, rule 7 — the banked computational results carried as explicit hypotheses;
the OWED is the data-side, mechanical connection of the chase ledger to these Lean forms):
* `Strip2Cap511` (T1 — the complete strip-2 chase: cap `511/31 = (73/31)(49/7)` attained,
  `midbound2_postmortem` Part A);
* `Strip3Cap86989` (T2 — the complete strip-3 chase: cap `86989/3565` attained, X24);
* `Fresh.BandTailCover.StripChaseKill46` (T4 — the completed chases `midbound_chase_v1/v2`,
  `feas_types = 0`, `complete = True`);
* `Fresh.BandTailCover.TailAbove50Cover` (T5 — the covering session's width certificate in
  `NoCarve` form, see `Fresh.TailSlowWidth` above).
The composition proves that these hypotheses SUFFICE.  The comb pieces (anchor
classification, gap corollary, strip arithmetic, the compositions themselves) are PROVED
here with the standard axioms only.
-/

namespace Fresh.TailComposition

open Fresh Fresh.Cascade Fresh.BandTailCover

/-! ## §1  The strip-index arithmetic (the case-split vocabulary) -/

/-- A reading at `25` or above sits in no strip below `C₄` — `C₃ = (23,25)` is open at
exactly 25 (`tailcomp2_pincheck_v1` P1(iii), exact). -/
theorem four_le_of_ge_25 {ρ : ℝ} (h25 : (25 : ℝ) ≤ ρ) {j : ℤ} (h : InStrip ρ j) :
    4 ≤ j := by
  obtain ⟨_, hhi⟩ := inStrip_iff.mp h
  have h1 : (25 : ℝ) < ((8 * j + 1 : ℤ) : ℝ) := lt_of_le_of_lt h25 hhi
  have h2 : ((24 : ℤ) : ℝ) < ((8 * j : ℤ) : ℝ) := by push_cast at h1 ⊢; linarith
  have h3 : (24 : ℤ) < 8 * j := Int.cast_lt.mp h2
  omega

#print axioms four_le_of_ge_25

/-- A reading in strip `C_j` with `j ≥ 7` is at least `8·7 − 1 = 55` — past the covering
certificate's `ρ₇ ≥ 50` hypothesis (`tailrest_composition_v1` T5's domain). -/
theorem ge_fiftyfive_of_strip_seven {ρ : ℝ} {j : ℤ} (hj : 7 ≤ j) (h : InStrip ρ j) :
    (55 : ℝ) ≤ ρ := by
  obtain ⟨hlo, _⟩ := inStrip_iff.mp h
  have hz : (55 : ℤ) ≤ 8 * j - 1 := by omega
  have hc : (55 : ℝ) ≤ ((8 * j - 1 : ℤ) : ℝ) := by exact_mod_cast hz
  exact le_trans hc (le_of_lt hlo)

#print axioms ge_fiftyfive_of_strip_seven

/-- The strip-2 window: `C₂ = (15,17)` unpacked (`tailcomp2_lemma_v1` U2's domain). -/
theorem strip2_iff {ρ : ℝ} : InStrip ρ 2 ↔ (15 : ℝ) < ρ ∧ ρ < 17 := by
  rw [inStrip_iff]
  have e1 : ((8 * 2 - 1 : ℤ) : ℝ) = (15 : ℝ) := by norm_num
  have e2 : ((8 * 2 + 1 : ℤ) : ℝ) = (17 : ℝ) := by norm_num
  rw [e1, e2]

#print axioms strip2_iff

/-- The strip-3 window: `C₃ = (23,25)` unpacked — exactly the X24 band (`U3`). -/
theorem strip3_iff {ρ : ℝ} : InStrip ρ 3 ↔ (23 : ℝ) < ρ ∧ ρ < 25 := by
  rw [inStrip_iff]
  have e1 : ((8 * 3 - 1 : ℤ) : ℝ) = (23 : ℝ) := by norm_num
  have e2 : ((8 * 3 + 1 : ℤ) : ℝ) = (25 : ℝ) := by norm_num
  rw [e1, e2]

#print axioms strip3_iff

/-- The strip-index confinement for `15 < ρ₇ < 50` at lap `j ≤ 6`: the self-anchor's lap
is 2, 3, or in the chase range 4–6 (`tailcomp2_lemma_v1`'s U2/U3/U4 split; the lower bound
is `C₁`'s upper edge 9 < 15, the upper one `j ≤ 6` is the hypothesis). -/
theorem strip_case_of_bounds {ρ : ℝ} (h15 : (15 : ℝ) < ρ) {j : ℤ} (h : InStrip ρ j)
    (hj6 : j ≤ 6) : j = 2 ∨ j = 3 ∨ (4 ≤ j ∧ j ≤ 6) := by
  obtain ⟨_, hhi⟩ := inStrip_iff.mp h
  have h3 : (15 : ℝ) < ((8 * j + 1 : ℤ) : ℝ) := lt_trans h15 hhi
  have h4 : ((14 : ℤ) : ℝ) < ((8 * j : ℤ) : ℝ) := by push_cast at h3 ⊢; linarith
  have h5 : (14 : ℤ) < 8 * j := Int.cast_lt.mp h4
  by_cases hj2 : j = 2
  · exact Or.inl hj2
  · by_cases hj3 : j = 3
    · exact Or.inr (Or.inl hj3)
    · exact Or.inr (Or.inr ⟨by omega, hj6⟩)

#print axioms strip_case_of_bounds

/-! ## §2  The comb extraction: the anchor classification and the gap corollary -/

/-- **The self-anchor extraction** (the anchor classification, `tailrest_anchor_lemma_v1`
(i)+(ii), composed): under the pin, a carve of `[1,7]` forces `ρ₇` into SOME strip — the
`R = 1` coverer is `ρ₇`'s self-anchor `(ρ₇, j)`, so `ρ₇` lies in `C_j`.  The gap regimes
and the strip-edge values (`ρ₇ = 8m ± 1`, in no strip and no gap) are dead before this
point: the gap corollary `Fresh.BandTailCover.gap_carve_free` is the special case
`ρ₇ ∈ G_m` of the contrapositive, via `Fresh.BandTailCover.notInStrip_of_gap`. -/
theorem pinnedCarve_strip {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ j : ℤ, InStrip (g 6) j := by
  obtain ⟨ρ, hρmem, j, hj1, hj2⟩ := hcarve 1 (by norm_num) (by norm_num)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρmem
  have hz : InStrip (g i) j := zoneAtOne_iff.mp ⟨hj1, hj2⟩
  obtain ⟨h6, _⟩ := anchor_classification pin ordered hpin hz
  have hiE : i = 6 := Fin.val_injective h6
  subst hiE
  exact ⟨j, hz⟩

#print axioms pinnedCarve_strip

/-- **The tail self-anchor** (corollary C1 of the anchor classification): under the pin,
every carve with `ρ₇ ≥ 25` is `ρ₇`-self-anchored at a FORCED lap `j ≥ 4` — the pinned tail
reduces to the strips `C_m`, `m ≥ 4`.  (`Fresh.BandTailCover.pinnedCarve_selfAnchor`'s
conclusion, re-derived through the extraction.) -/
theorem pinnedCarve_strip_ge25 {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ))
    (h25 : (25 : ℝ) ≤ g 6) :
    ∃ j : ℤ, 4 ≤ j ∧ InStrip (g 6) j := by
  obtain ⟨j, hj⟩ := pinnedCarve_strip pin ordered hpin hcarve
  exact ⟨j, four_le_of_ge_25 h25 hj, hj⟩

#print axioms pinnedCarve_strip_ge25

/-- The pinned gap corollary as a bridge: `ρ₇` in the open gap `G_m = (8m+1, 8m+7)` meets
no strip (`Fresh.BandTailCover.notInStrip_of_gap`), so the extraction kills the carve —
`Fresh.BandTailCover.gap_carve_free`'s statement, composed here from the extraction. -/
theorem noCarve_of_gap {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 7) {m : ℤ}
    (hgap : ((8 * m + 1 : ℤ) : ℝ) < g 6 ∧ g 6 < ((8 * m + 7 : ℤ) : ℝ)) :
    Fresh.Certs.NoCarve g := by
  intro hcarve
  obtain ⟨j, hj⟩ := pinnedCarve_strip pin ordered hpin hcarve
  exact absurd hj (notInStrip_of_gap hgap j)

#print axioms noCarve_of_gap

/-! ## §3  The instruments: the banked computational results, carried as hypotheses -/

/-- **OWED (T1, data-side)**: the complete strip-2 chase — every carve with `ρ₇ ∈ C₂ =
(15,17)` under the pin has `ρ₇ ≤ 511/31 = (73/31)(49/7)`; the cap type is alive at the cap
(`midbound2_postmortem` Part A), above it `feas = 0`, `complete = True`.  The chase ledger
is exact but computational; the Lean-form theorem is owed. -/
-- STANDING: OWED
def Strip2Cap511 : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    (15 : ℝ) < g 6 → g 6 < 17 → g 6 ≤ 511 / 31

/-- **OWED (T2, data-side)**: the complete strip-3 chase — every carve with `ρ₇ ∈ C₃ =
(23,25)` under the pin has `ρ₇ ≤ 86989/3565` (the X24 cap, attained); `(86989/3565, 25)`
is carve-free (`feas = 0`, `complete = True`). -/
-- STANDING: OWED
def Strip3Cap86989 : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 7 →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    (23 : ℝ) < g 6 → g 6 < 25 → g 6 ≤ 86989 / 3565

/-- The X24 cap is inside the window: `86989/3565 < 25` (exact). -/
theorem cap3_lt_25 : (86989 : ℝ) / 3565 < 25 := by norm_num

#print axioms cap3_lt_25

/-! ## §4  The composition theorem -/

/-- **THE TAIL COMPOSITION THEOREM (the tail proper)** (`tailcomp2_lemma_v1` Theorem U,
pieces U1/U4/U5): under the pin `ρ₆ ≤ 49/7 = 7`, with the strip-4–6 chase kills and the
`ρ₇ ≥ 50` covering kill as hypotheses, there is NO carve of `[1,7]` with `ρ₇ ≥ 25`.

Proof shape (the case split on `ρ₇`'s strip membership): a carve forces the self-anchor
`(ρ₇, j)` (the anchor classification); `ρ₇ ≥ 25` forces `j ≥ 4`; then `j ≤ 6` hands the
strip to the chases (U4) and `j ≥ 7` puts `ρ₇ ≥ 55 ≥ 50`, handed to the width certificate
(U5).  The gaps and strip edges are dead before the split — the carve forces `ρ₇` into a
strip (the gap corollary's contrapositive), which is U1. -/
theorem pinnedTail25 {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 49 / 7)
    (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover)
    (h25 : (25 : ℝ) ≤ g 6) :
    Fresh.Certs.NoCarve g := by
  have h7 : g 5 ≤ 7 := le_trans hpin (by norm_num)
  intro hcarve
  obtain ⟨j, hj4, hj⟩ := pinnedCarve_strip_ge25 pin ordered h7 hcarve h25
  rcases lt_or_ge j 7 with hj6 | hj7
  · exact absurd hcarve (hS g pin ordered h7 j hj4 (by omega) hj)
  · exact absurd hcarve (hT5 g pin ordered h7
      (le_trans (by norm_num : (50 : ℝ) ≤ 55) (ge_fiftyfive_of_strip_seven hj7 hj)))

#print axioms pinnedTail25

/-- **The composition theorem in the mission's shape** (`tailcomp2_lemma_v1` Theorem U +
the X24 clause): under the pin, with the strip instruments as hypotheses and the case
hypothesis `(ρ₇ ≥ 25 ∨ ρ₇ ∈ (23,25))`, either there is no carve of `[1,7]`, or `ρ₇` lies
in the X24 locus `(23, 86989/3565]` — i.e. no carve with `ρ₇ ≥ 25` outside `(23,25)`, and
the `(23,25)` band's carves are confined to the attained X24 cap. -/
theorem pinnedTail {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 49 / 7)
    (hCap3 : Strip3Cap86989)
    (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover)
    (hcase : (25 : ℝ) ≤ g 6 ∨ ((23 : ℝ) < g 6 ∧ g 6 < 25)) :
    Fresh.Certs.NoCarve g ∨ ((23 : ℝ) < g 6 ∧ g 6 ≤ 86989 / 3565) := by
  have h7 : g 5 ≤ 7 := le_trans hpin (by norm_num)
  rcases hcase with h25 | hwin
  · exact Or.inl (pinnedTail25 pin ordered hpin hS hT5 h25)
  · -- the X24 window is exactly strip 3: the chase cap confines the carves
    by_cases hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)
    · exact Or.inr ⟨hwin.1, hCap3 g pin ordered h7 hcarve hwin.1 hwin.2⟩
    · exact Or.inl hcarve

#print axioms pinnedTail

/-- **The strengthened composition: the carve locus above 15** (`tailcomp2_lemma_v1`
Theorem U, pieces U1–U5): under the pin, with all four strip instruments as hypotheses and
`ρ₇ > 15`, either no carve of `[1,7]`, or `ρ₇` lies in `(15, 511/31]` (strip 2, T1) or in
`(23, 86989/3565]` (strip 3 / X24, T2) — the carve locus above 15, gaps and strips
`m ≥ 4` dead on the same instruments. -/
theorem pinnedTailLocus {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hpin : g 5 ≤ 49 / 7)
    (hCap2 : Strip2Cap511) (hCap3 : Strip3Cap86989)
    (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover)
    (h15 : (15 : ℝ) < g 6) :
    Fresh.Certs.NoCarve g ∨
      ((15 : ℝ) < g 6 ∧ g 6 ≤ 511 / 31) ∨ ((23 : ℝ) < g 6 ∧ g 6 ≤ 86989 / 3565) := by
  have h7 : g 5 ≤ 7 := le_trans hpin (by norm_num)
  by_cases hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)
  · -- the anchor classification: the carve forces the self-anchor (ρ₇, j)
    obtain ⟨j, hj⟩ := pinnedCarve_strip pin ordered h7 hcarve
    rcases lt_or_ge j 7 with hj6 | hj7
    · rcases strip_case_of_bounds h15 hj (by omega) with rfl | rfl | hjm
      · -- U2: strip 2, the m = 2 cap
        obtain ⟨h15', h17'⟩ := strip2_iff.mp hj
        exact Or.inr (Or.inl ⟨h15', hCap2 g pin ordered h7 hcarve h15' h17'⟩)
      · -- U3: strip 3, the X24 cap
        obtain ⟨h23', h25'⟩ := strip3_iff.mp hj
        exact Or.inr (Or.inr ⟨h23', hCap3 g pin ordered h7 hcarve h23' h25'⟩)
      · -- U4: strips 4–6, the completed chases
        exact absurd hcarve (hS g pin ordered h7 j hjm.1 hjm.2 hj)
    · -- U5: the self-anchor's lap is ≥ 7, so ρ₇ ≥ 55 ≥ 50
      exact Or.inl (hT5 g pin ordered h7
        (le_trans (by norm_num : (50 : ℝ) ≤ 55) (ge_fiftyfive_of_strip_seven hj7 hj)))
  · exact Or.inl hcarve

#print axioms pinnedTailLocus

/-! ## §5  The composed statements, discharged from the instruments -/

/-- The mission's target statement (`tailcomp2_lemma_v1`'s tail composition, ∀-form). -/
-- STANDING: OWED
def PinnedTail23 : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 49 / 7 →
    ((25 : ℝ) ≤ g 6 ∨ ((23 : ℝ) < g 6 ∧ g 6 < 25)) →
    Fresh.Certs.NoCarve g ∨ ((23 : ℝ) < g 6 ∧ g 6 ≤ 86989 / 3565)

/-- The strengthened locus statement, ∀-form. -/
-- STANDING: OWED
def PinnedTailLocus : Prop :=
  ∀ g : Fin 7 → ℝ, g 0 = 1 → Monotone g → g 5 ≤ 49 / 7 → (15 : ℝ) < g 6 →
    Fresh.Certs.NoCarve g ∨
      ((15 : ℝ) < g 6 ∧ g 6 ≤ 511 / 31) ∨ ((23 : ℝ) < g 6 ∧ g 6 ≤ 86989 / 3565)

/-- The mission's target, discharged: the three strip instruments SUFFICE for it (T2+T4+T5;
T1 is not consumed above 23). -/
theorem pinnedTail23_of_instruments (hCap3 : Strip3Cap86989)
    (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover) : PinnedTail23 := by
  intro g pin ordered hpin hcase
  exact pinnedTail pin ordered hpin hCap3 hS hT5 hcase

#print axioms pinnedTail23_of_instruments

/-- The strengthened locus, discharged: all four strip instruments SUFFICE for it
(T1+T2+T4+T5). -/
theorem pinnedTailLocus_of_instruments (hCap2 : Strip2Cap511) (hCap3 : Strip3Cap86989)
    (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover) : PinnedTailLocus := by
  intro g pin ordered hpin h15
  exact pinnedTailLocus pin ordered hpin hCap2 hCap3 hS hT5 h15

#print axioms pinnedTailLocus_of_instruments

/-- **`Fresh.BandTailCover.PinnedTailCover` discharged from the same two instruments it
named** (`StripChaseKill46`, `TailAbove50Cover`): the covering side of the pinned tail
lemma, no carve with `ρ₇ ≥ 25` — re-derived here through the self-anchor extraction and
the strip-index split. -/
theorem pinnedTailCover_of_hyp (hS : Fresh.BandTailCover.StripChaseKill46)
    (hT5 : Fresh.BandTailCover.TailAbove50Cover) :
    Fresh.BandTailCover.PinnedTailCover := by
  intro g pin ordered hpin h25
  have hp49 : g 5 ≤ 49 / 7 := le_trans hpin (by norm_num)
  exact pinnedTail25 pin ordered hp49 hS hT5 h25

#print axioms pinnedTailCover_of_hyp

end Fresh.TailComposition
