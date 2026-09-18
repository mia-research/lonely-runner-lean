import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The neighbour at a grid instant is a function of the residues alone

Owner's question: *"does the variation away from AP/grid change the neighbour of the isolation
in a predictable way?"*

Write a commensurable arrangement in reduced units as `w i = π i + n · q i` — residue plus whole
laps.  Deformation therefore has two independent parts, and this file settles the `q` part.

At a grid instant `t = p/n`, runner `j`'s position relative to subject `i` is `gridPos n p (w j −
w i)`, and `gridPos_congr` shows that number depends on the disparity only through its residue
mod `n`.  `laps_invisible` is the consequence: moving whole laps moves nothing.  So the entire
cyclic ordering of the pack around the subject — hence which runner is nearest ahead and which
nearest behind — is fixed by `π`, and the `q` part of a deformation is invisible.

`neighbour_laps_invisible` states that for the nearest-ahead runner itself.

Verified 16,000 of 16,000 in `experiments/n8/neighbour_rule_v4.py`; the sharper `±p` form of the
rule (ahead is the runner at residue offset `p`, using `p⁻¹ = p` in the Klein group `(ℤ/8)ˣ`)
12,800 of 12,800 in `neighbour_rule_v1.py`.

Scope: **grid instants only.**  At the cascade's own instant the same invariance holds 10.4% of
the time, against a matched null of 1.9% (`neighbour_rule_v5.py`) — so residues carry real
information there, roughly 5× the null, and come nowhere near determining the answer.  See
`NEIGHBOUR_DEFORMATION_v1.md`.
Development file; nothing here is load-bearing for a manuscript result. -/

namespace GridNeighbour

/-- Runner `j`'s position relative to subject `i` at the grid instant `p/n`, where `d = w j − w i`
is the disparity in reduced (integer) units. -/
noncomputable def gridPos (n p : ℕ) (d : ℤ) : ℝ := Int.fract ((d : ℝ) * p / n)

theorem gridPos_eq (n p : ℕ) (d : ℤ) :
    gridPos n p d = (((d * p) % n : ℤ) : ℝ) / n := by
  unfold gridPos
  have h : (d : ℝ) * p / n = ((d * p : ℤ) : ℝ) / n := by push_cast; ring
  rw [h, Int.fract_div_intCast_eq_div_intCast_mod]

/-- **A relative position at a grid instant sees only the disparity's residue.** -/
theorem gridPos_congr (n p : ℕ) {d d' : ℤ} (h : d % n = d' % n) :
    gridPos n p d = gridPos n p d' := by
  rw [gridPos_eq, gridPos_eq, Int.mul_emod, h, ← Int.mul_emod]

/-- **Whole laps are invisible.**  Two arrangements with the same residues `π` and any whole-lap
parts `q`, `q'` put every runner at the same place relative to every subject, at every grid
instant.  Deforming `q` therefore cannot move the neighbour. -/
theorem laps_invisible (n p : ℕ) (π q q' : Fin 8 → ℤ) (i j : Fin 8) :
    gridPos n p ((π j + n * q j) - (π i + n * q i))
      = gridPos n p ((π j + n * q' j) - (π i + n * q' i)) := by
  refine gridPos_congr n p ?_
  have e1 : (π j + (n:ℤ) * q j) - (π i + (n:ℤ) * q i)
      = (π j - π i) + (n:ℤ) * (q j - q i) := by ring
  have e2 : (π j + (n:ℤ) * q' j) - (π i + (n:ℤ) * q' i)
      = (π j - π i) + (n:ℤ) * (q' j - q' i) := by ring
  rw [e1, e2, Int.add_mul_emod_self_left, Int.add_mul_emod_self_left]

/-- The nearest-ahead runner is the same under any whole-lap deformation: the two arrangements
present the subject with the *same function* `j ↦ gridPos`, so any selection rule stated in that
function — nearest ahead, nearest behind, the whole cyclic order — returns the same answer. -/
theorem neighbour_laps_invisible (n p : ℕ) (π q q' : Fin 8 → ℤ) (i : Fin 8) :
    (fun j => gridPos n p ((π j + n * q j) - (π i + n * q i)))
      = fun j => gridPos n p ((π j + n * q' j) - (π i + n * q' i)) :=
  funext fun j => laps_invisible n p π q q' i j

end GridNeighbour
