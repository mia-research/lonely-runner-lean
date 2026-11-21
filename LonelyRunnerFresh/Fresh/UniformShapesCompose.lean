import Mathlib
import Fresh.TropicalCycle
import Fresh.UniformShapes_R2

/-!
# UniformShapesCompose: the consumption note — shape lemmas + tropicalCycle = candidate death

New file (2026-11-21); nothing existing is edited.  This is E902 item 4's [P→L] CONSUMPTION
half, proved for one worked shape as the pattern for the general per-member transcription.

## The composition schema (how the death argument assembles)

A maximal-word transcription (the per-member MechDataBatch layer named in
`v3_uniformity_lemma_findings_v1.md` §4) carries, for each of the word's killing cycles,
its shape id, its realized offset pattern τ, and the member's base `m` (an integer ≥ 5,
the self family's strip parameter).  The death of the word at the candidate is the
composition of three PROVED pieces:

1. **The word's row instances (data side).**  For the word `z_0..z_{n-1}` with readings
   `r_i`, laps `l_i`, the row grammar emits `u_p <(≤) c · u_q` rows; the killing cycle is
   the failed candidate edge + the least-product path, each edge an instance
   `RHolds strict (g a / g b) c` over the seven readings `g` (the maximal-word hypothesis:
   some positive `g` realizes every row — `Fresh.TropicalCycle.TEdge`/`EdgeSat` semantics).
   For the worked shape the two cycle edges are the candidate entry row
   `u_6 < ((8(m+2)+1)/(8(m+3)−1)) · u_5` (zone 6 at the candidate's lap m+3, frontier
   reading 5 at the death-frontier lap m+2 — the pattern's free slots) and the word's own
   strict `z_entry` row `u_5 < ((8(m+1)+1)/(8(m+1)−1)) · u_6` (both laps tied+1).
2. **The shape lemma (the generated half-line form, `Fresh.UniformShapes_R2`).**
   `shape_u202_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < 32*m + 8` — the exact deficit
   `D_τ(m) = B_τ(m) − A_τ(m)` of the cycle product `P_τ(m) = A_τ(m)/B_τ(m)` with
   `A_τ = (8m+17)(8m+9)`, `B_τ = (8m+23)(8m+7)`; the instrument (replay-validated
   1219/1219 + 13741/13741) proved this pattern uniform, and the generator re-derived and
   certified it exactly.
3. **The engine (PROVED, `Fresh.TropicalCycle.tropicalCycle_infeasible`).**  A head-to-tail
   closed walk of satisfied edges with weight product `< 1` is impossible.

Composition: (1) realizes the walk `6 → 5 → 6`; (2) gives the product
`((8m+17)/(8m+23))·((8m+9)/(8m+7)) < 1` exactly when `D_τ(m) = 32m+8 > 0`; (3) closes
`False`.  Contrapositive: **in any realized maximal word with base m ≥ 5, the candidate
(zone 6, lap m+3) is rejected** — the word dies at this candidate, which is the death
argument the per-member transcription consumes shape-instance by shape-instance.

The general transcription instantiates this schema per (shape, pattern, member): the
per-member file supplies hypothesis (1) as its row table, the generated shape lemma
supplies (2), and `tropicalCycle_infeasible` is (3) unchanged.  No new engine work: the
schema IS `tropicalCycle_infeasible` with the shape lemma feeding the bad-cycle side.
-/

namespace Fresh.UniformShapesCompose

open Fresh.TropicalCycle
open Fresh.UniformShapes

/-- **The worked composition (shape `6→5→(closed)`, kind `cand_entry + z_entry`, pattern
τ = (3, 2)): the shape lemma + the two row instances kill the candidate.**  Any positive
reading vector satisfying the word's candidate-entry row and the `z_entry` row at the
pattern's laps (candidate zone lap m+3, frontier lap m+2, word laps m+1) is impossible for
every base `m ≥ 5` — the candidate (6, m+3) is rejected, i.e. the maximal word dies at it. -/
theorem shape_u202_pat1_kills_cand (m : ℚ) (hm : 5 ≤ m)
    (g : Fin 7 → ℝ) (h5 : 0 < g 5) (h6 : 0 < g 6)
    (hcand : RHolds true (g 6 / g 5)
      (((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ)))
    (hpath : RHolds true (g 5 / g 6)
      (((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ))) : False := by
  -- the two cycle edges as TropicalCycle edges (the row instances, definitional)
  have hc : EdgeSat g (⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ),
      true⟩ : TEdge) := hcand
  have hp : EdgeSat g (⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ),
      true⟩ : TEdge) := hpath
  -- the closed walk 6 → 5 → 6
  have hw : WalkFrom 6
      [⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ), true⟩,
       ⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩] 6 :=
    WalkFrom.cons 6 ⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ), true⟩
      [⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩] 6 rfl
      (WalkFrom.cons 5 ⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩
        [] 6 rfl (WalkFrom.nil 6))
  have hsat : ∀ x ∈ ([⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ), true⟩,
      ⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩] : List TEdge),
      EdgeSat g x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · rcases hx with rfl | hx
      · exact hp
      · exact absurd hx List.not_mem_nil
  have hend : ∀ x ∈ ([⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ), true⟩,
      ⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩] : List TEdge),
      0 < g x.a ∧ 0 < g x.b := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨h6, h5⟩
    · rcases hx with rfl | hx
      · exact ⟨h5, h6⟩
      · exact absurd hx List.not_mem_nil
  -- the engine: a satisfied closed walk admits no bad cycle
  have hcontra := tropicalCycle_infeasible hw hsat hend
  -- the shape lemma (the generated half-line form) + the exact deficit identity
  have hD := shape_u202_pat1_uniform m hm
  have hq : ((8 * (m + 2) + 1 : ℚ) / (8 * (m + 3) - 1))
      * ((8 * (m + 1) + 1 : ℚ) / (8 * (m + 1) - 1)) < 1 := by
    have hb1 : (0:ℚ) < 8 * (m + 3) - 1 := by linarith
    have hb2 : (0:ℚ) < 8 * (m + 1) - 1 := by linarith
    have hkey : (8 * (m + 2) + 1 : ℚ) * (8 * (m + 1) + 1)
        < (8 * (m + 3) - 1) * (8 * (m + 1) - 1) := by
      have hident : (8 * (m + 3) - 1 : ℚ) * (8 * (m + 1) - 1)
          = (8 * (m + 2) + 1) * (8 * (m + 1) + 1) + (32 * m + 8 : ℚ) := by ring
      linarith
    rw [div_mul_div_comm]
    exact (div_lt_iff₀ (mul_pos hb1 hb2)).mpr (by linarith)
  -- cast the ℚ product inequality to the walk's weight product
  have hprod : (List.map TEdge.c [⟨6, 5, ((8 * (m + 2) + 1 : ℚ) : ℝ) / ((8 * (m + 3) - 1 : ℚ) : ℝ), true⟩,
      ⟨5, 6, ((8 * (m + 1) + 1 : ℚ) : ℝ) / ((8 * (m + 1) - 1 : ℚ) : ℝ), true⟩]).prod
      = (↑((8 * (m + 2) + 1 : ℚ) / (8 * (m + 3) - 1)) : ℝ)
        * (↑((8 * (m + 1) + 1 : ℚ) / (8 * (m + 1) - 1)) : ℝ) := by
    simp [List.map_cons, List.prod_cons]
  refine hcontra ?_
  refine Or.inl ?_
  rw [hprod]
  have hrc : (↑((8 * (m + 2) + 1 : ℚ) / (8 * (m + 3) - 1)) : ℝ)
      * (↑((8 * (m + 1) + 1 : ℚ) / (8 * (m + 1) - 1)) : ℝ) < 1 := by
    have h : (↑(((8 * (m + 2) + 1 : ℚ) / (8 * (m + 3) - 1))
        * ((8 * (m + 1) + 1 : ℚ) / (8 * (m + 1) - 1))) : ℝ) < 1 := by
      exact_mod_cast hq
    rw [Rat.cast_mul] at h
    exact h
  exact hrc

#print axioms shape_u202_pat1_kills_cand

end Fresh.UniformShapesCompose
