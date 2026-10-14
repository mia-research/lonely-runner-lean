import Mathlib
import Fresh.Framework
import Fresh.Grid

/-!
# D_max: shifting a speed by a multiple of 8 grid steps leaves the isolation instants fixed

Written 2026-10-08, after the owner's original document: "mod n reaches infinity so no matter how large any particular
speed is, if it is a multiple of 8 it will globally isolate with the other global isolationable speeds".

Statement.  Take a grid arrangement `v j = v₀ + idx j · d` and replace runner `j` by `v j + 8·c j·d` (`c j` any
integer).  Then (i) the new arrangement is again a grid (indices `idx j + 8 c j` are still a complete residue system),
so it is globally isolated at every `a/(8d)`, `a` a unit mod 8; and (ii) at those instants every reading is unchanged
modulo whole laps: `distInt` of each difference of speeds times the instant is the same before and after.  So a D_max
shift displaces nothing: the isolation stays exactly where it was.  No runner is stationary; everything is a difference.
-/

open Classical

namespace Fresh

/-- The shifted speeds are a grid with the shifted indices. -/
theorem dmax_complete (idx c : Fin 8 → ℤ) (h : CompleteResidues idx) :
    CompleteResidues (fun j => idx j + 8 * c j) := by
  intro j j' hjj
  apply h
  have h1 : (idx j + 8 * c j) % 8 = idx j % 8 := by omega
  have h2 : (idx j' + 8 * c j') % 8 = idx j' % 8 := by omega
  rw [← h1, ← h2]; exact hjj

/-- **D_max shift, global form.** -/
theorem dmax_globalIsolation (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx c : Fin 8 → ℤ)
    (hd : 0 < d) (hidx : CompleteResidues idx)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + 8 * (c j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) :
    GloballyIsolatedAt v ((a : ℝ) / (8 * d)) := by
  refine gridGlobalIsolation v d v₀ (fun j => idx j + 8 * c j) hd (dmax_complete idx c hidx) ?_ a ha
  intro j; rw [hv j]; push_cast; ring

/-- **D_max shift, reading form.** At `a/(8d)` the reading of runner `i` against subject `k` is the same modulo whole
laps before and after the shift; the displacement of the isolation is zero. -/
theorem dmax_reading_unchanged (v v' : Fin 8 → ℝ) (d : ℝ) (hd : 0 < d) (c : Fin 8 → ℤ)
    (hv' : ∀ j, v' j = v j + 8 * (c j : ℝ) * d) (a : ℤ) (i k : Fin 8) :
    distInt ((v' i - v' k) * ((a : ℝ) / (8 * d))) = distInt ((v i - v k) * ((a : ℝ) / (8 * d))) := by
  have hd0 : d ≠ 0 := hd.ne'
  have : (v' i - v' k) * ((a : ℝ) / (8 * d))
      = (v i - v k) * ((a : ℝ) / (8 * d)) + (((c i - c k) * a : ℤ) : ℝ) := by
    rw [hv' i, hv' k]; push_cast; field_simp; ring
  rw [this, distInt_add_int]

/-- Isolation of a subject at the grid instants is therefore unchanged by the shift. -/
theorem dmax_isolatedAt_iff (v v' : Fin 8 → ℝ) (d : ℝ) (hd : 0 < d) (c : Fin 8 → ℤ)
    (hv' : ∀ j, v' j = v j + 8 * (c j : ℝ) * d) (a : ℤ) (k : Fin 8) :
    IsolatedAt v' k ((a : ℝ) / (8 * d)) ↔ IsolatedAt v k ((a : ℝ) / (8 * d)) := by
  unfold IsolatedAt
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rw [dmax_reading_unchanged v v' d hd c hv' a i k]

#print axioms dmax_complete
#print axioms dmax_globalIsolation
#print axioms dmax_reading_unchanged
#print axioms dmax_isolatedAt_iff

end Fresh
