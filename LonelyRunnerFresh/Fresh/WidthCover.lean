import Mathlib.Tactic
import Fresh.WidthCert
import Fresh.K6BandUnion

/-!
# The width-cover landing: variable-edge components die by width

Bridge gamma's per-class certificates so far consume the EXACT component edges `(A, B)`
of a recorded representative (`InClass`, `gamma_join50`), so their scope is the codim-2
slice where the tuple's component edges equal the representative's.  The width lemma
(`Fresh.WidthCert`) removes that restriction: a component's column death needs only its
WIDTH, so every component of width `>= 2/25` dies, whatever its edges.

The certifying component's edges are `a = (8*kL+9)/rL` (the exit edge of the L reading's
lap-`kL+1` zone) and `b = (8*kR+7)/rR` (the entry edge of the R reading's lap-`kR+1`
zone), so its width `w = b - a` is monotone in the two boundary readings: increasing in
`rL`, decreasing in `rR`.  Hence `w` is minimized over a reading box at the corner
`(lL, uR)` — the per-cell corner argument's engine: a corner fact `2/25 <= w(lL, uR)`
gives `2/25 <= w(rL, rR)` for every interior pair.

Landed here:

* `gap_width_bound` — the monotone corner-to-interior width bound (pure rational
  arithmetic);
* `colDead_of_width_mem` — the width lemma restated as beta's `ColDead` (definitionally);
* `tuple_dead_of_width` — the composition: a wide component of `rho` kills the tuple's
  `[25, 50)` column (`band_union50` + width, no datasheet atom, no exact edges);
* `tuple_dead_of_width_box` — the per-class form: the corner fact at the class's reading
  box gives the interior width bound, so the tuple dies;
* a worked instance (`rhoEx = ![2, 3, 4, 6, 8]`, component `(3/2, 7/4)`, width `1/4`).

The per-class corner facts `2/25 <= (8kR+7)/uR - (8kL+9)/lL` are the datum this file
makes load-bearing; they are checked data-side per class (exact rationals) and then each
class's certificate covers its whole reading box, not just the representative slice.
-/

namespace Fresh.WidthCover

open Fresh.WidthCert Fresh.K6BandUnion

/-- **The corner-to-interior width bound.**  The gap width
`w(rL, rR) = (8*kR+7)/rR - (8*kL+9)/rL` of the interval between the L reading's
lap-`kL+1` zone exit and the R reading's lap-`kR+1` zone entry is increasing in `rL` and
decreasing in `rR`; therefore it is minimized over the box `lL ≤ rL ≤ uL`,
`lR ≤ rR ≤ uR` at the corner `(lL, uR)`. -/
theorem gap_width_bound (kL kR : ℕ) (lL uR rL rR : ℚ) (S : ℚ)
    (hS : 0 < S)
    (hlL : 0 < lL) (hrR : 0 < rR)
    (hL : lL ≤ rL) (hR : rR ≤ uR)
    (hcorner : (2:ℚ) / S ≤ ((8*kR+7 : ℕ) : ℚ) / uR - ((8*kL+9 : ℕ) : ℚ) / lL) :
    (2:ℚ) / S ≤ ((8*kR+7 : ℕ) : ℚ) / rR - ((8*kL+9 : ℕ) : ℚ) / rL := by
  have hN1 : (0:ℚ) < ((8*kR+7 : ℕ) : ℚ) := by positivity
  have hN2 : (0:ℚ) < ((8*kL+9 : ℕ) : ℚ) := by positivity
  have hN1' : (0:ℚ) ≤ ((8*kR+7 : ℕ) : ℚ) := le_of_lt hN1
  have hN2' : (0:ℚ) ≤ ((8*kL+9 : ℕ) : ℚ) := le_of_lt hN2
  -- (8kR+7)/uR ≤ (8kR+7)/rR  (rR ≤ uR, all denominators positive)
  have hb : ((8*kR+7 : ℕ) : ℚ) / uR ≤ ((8*kR+7 : ℕ) : ℚ) / rR :=
    div_le_div_of_nonneg_left hN1' hrR hR
  -- (8kL+9)/rL ≤ (8kL+9)/lL  (lL ≤ rL, all denominators positive)
  have ha : ((8*kL+9 : ℕ) : ℚ) / rL ≤ ((8*kL+9 : ℕ) : ℚ) / lL :=
    div_le_div_of_nonneg_left hN2' hlL hL
  linarith

/-- **The width lemma in beta's `ColDead` shape** — the conclusion of
`Fresh.WidthCert.colDead50_of_width` is definitionally `ColDead p`. -/
theorem colDead_of_width_mem (p : ℚ × ℚ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hw : (2:ℚ) / 25 ≤ p.2 - p.1) : ColDead p :=
  fun s hs h50 j hb => no_band_of_width p hp1 hp2 25 (by norm_num) hw s hs j hb

/-- **The width-cover composition.**  A component of `rho` of width `>= 2/25` kills the
tuple's `[25, 50)` column — no datasheet atom, no exact-edge match: the component's edges
may be anything. -/
theorem tuple_dead_of_width (rho : Fin 5 → ℚ) (p : ℚ × ℚ)
    (hp : p ∈ K6Comps rho) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hw : (2:ℚ) / 25 ≤ p.2 - p.1) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ TupleLonely rho s :=
  band_union50 rho p hp (colDead_of_width_mem p hp1 hp2 hw) s hs h50

/-- **The per-class form.**  The certifying component's edges are
`((8kL+9)/rL, (8kR+7)/rR)`; the corner fact at the class's reading box
(`2/S ≤ (8kR+7)/uR - (8kL+9)/lL`) gives the width bound at every interior pair via
`gap_width_bound`, so the tuple dies at EVERY tail `s ≥ S` (no upper window: the width
argument kills the band at any scale past `S`, all laps). -/
theorem tuple_dead_of_width_box (rho : Fin 5 → ℚ) (kL kR : ℕ) (lL uR rL rR : ℚ)
    (hlL : 0 < lL) (hrL : 0 < rL) (hrR : 0 < rR)
    (hL : lL ≤ rL) (hR : rR ≤ uR)
    (hmem : (((8*kL+9 : ℕ) : ℚ) / rL, ((8*kR+7 : ℕ) : ℚ) / rR) ∈ K6Comps rho)
    (S : ℚ) (hS : 25 ≤ S)
    (hcorner : (2:ℚ) / S ≤ ((8*kR+7 : ℕ) : ℚ) / uR - ((8*kL+9 : ℕ) : ℚ) / lL)
    (s : ℚ) (hs : S ≤ s) :
    ¬ TupleLonely rho s := by
  have hN1 : (0:ℚ) < ((8*kR+7 : ℕ) : ℚ) := by positivity
  have hN2 : (0:ℚ) < ((8*kL+9 : ℕ) : ℚ) := by positivity
  have hS0 : (0:ℚ) < S := lt_of_lt_of_le (by norm_num : (0:ℚ) < 25) hS
  have hw : (2:ℚ) / S ≤ ((8*kR+7 : ℕ) : ℚ) / rR - ((8*kL+9 : ℕ) : ℚ) / rL :=
    gap_width_bound kL kR lL uR rL rR S hS0 hlL hrR hL hR hcorner
  intro hall
  obtain ⟨j, hB⟩ := hall (((8*kL+9 : ℕ) : ℚ) / rL, ((8*kR+7 : ℕ) : ℚ) / rR) hmem
  exact no_band_of_width _ (div_pos hN2 hrL) (div_pos hN1 hrR) S hS0 hw s hs j hB

/-! ## The worked instance -/

/-- The worked tuple's second component, width `1/4 >= 2/25`: the whole `[25, 50)`
column of `rhoEx = ![2, 3, 4, 6, 8]` is dead by width alone (no datasheet atom). -/
example (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ TupleLonely rhoEx s :=
  tuple_dead_of_width rhoEx (3/2, 7/4) pEx_mem (by norm_num) (by norm_num)
    (by norm_num : (2:ℚ) / 25 ≤ (7/4 : ℚ) - (3/2 : ℚ)) s hs h50

/-- The no-exists form of the worked instance. -/
example : ¬ ∃ s : ℚ, 25 ≤ s ∧ s < 50 ∧ TupleLonely rhoEx s := by
  rintro ⟨s, hs, h50, hl⟩
  exact tuple_dead_of_width rhoEx (3/2, 7/4) pEx_mem (by norm_num) (by norm_num)
    (by norm_num : (2:ℚ) / 25 ≤ (7/4 : ℚ) - (3/2 : ℚ)) s hs h50 hl

end Fresh.WidthCover

#print axioms Fresh.WidthCover.gap_width_bound
#print axioms Fresh.WidthCover.colDead_of_width_mem
#print axioms Fresh.WidthCover.tuple_dead_of_width
#print axioms Fresh.WidthCover.tuple_dead_of_width_box
