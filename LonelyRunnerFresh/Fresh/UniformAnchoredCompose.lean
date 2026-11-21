import Mathlib
import Fresh.TropicalCycle
import Fresh.UniformAnchored_R3

/-!
# UniformAnchoredCompose: the anchored consumption note — k15 killing shape + tropicalCycle

New file (2026-11-21); nothing existing is edited.  The CONSUMPTION half of the anchored
emission (E907's sibling), proved for one worked instance as the pattern for the general
per-member transcription — the exact analogue of `Fresh.UniformShapesCompose` for the
ANCHORED family, with the base fixed at the realized orbit index k = 15.

## The worked instance (shape a034: `6→4→5→(closed)`, kinds `cand_irred + z_entry + z_entry`,
pattern τ = (−7) at base k = 15 — the 3-row irred worst instance 3705/3751@k15)

The census word (death node 7 of member y6k15, `v3_march_census_v2_y6k15.out`; replayed and
re-validated by `uniform_gen_anchored_v1.py` — rejection multiset 19/19, products 145/145,
irred corrections 9/9):

    z = [3@1, 2@1, 4@2, 1@1, 5@5, 3@2, 4@3, 6@8, 5@6, 2@2, 5@7, 4@4, 3@3, 1@2, 4@5, 2@3,
         3@4, 6@15, 5@11]

against the candidate `(zone 4, lap 6)` (window [5, 7]).  The candidate's rejection is the
closed walk `4 → 5 → 6 → 4` of three satisfied rows:

1. the word's `z_entry` row at positions 10→11 (`5@7 → 4@4`): `u_4 < (8·7+1)/(8·4−1) · u_5`
   = `57/31 · u_5`;
2. the word's `z_entry` row at positions 7→8 (`6@8 → 5@6`): `u_5 < (8·8+1)/(8·6−1) · u_6`
   = `65/47 · u_6`;
3. the candidate's `cand_irred` row (candidate zone 4 at lap 6 against the word's anchor
   `6@15`, the reading-6 slot tied to the base): `u_6 < (8·6−1)/(8·15+1) · u_4`
   = `47/121 · u_4`.

The weight product is `47/121 · 57/31 · 65/47 = 3705/3751 < 1` — exactly the generated
per-base-instance shape lemma `Fresh.UniformAnchored.shape_a034_pat2_k15` (deficit
`D_τ(15) = 3751 − 3705 = 2162 > 0`; the pattern's killing set over k ≥ 13 is [13, 15],
which contains the realized base).  The engine (PROVED,
`Fresh.TropicalCycle.tropicalCycle_infeasible`) closes `False`: a satisfied closed walk
admits no bad cycle.  Contrapositive: **any positive reading vector satisfying the census
word's rows is impossible — the word dies at the candidate (zone 4, lap 6)**.

The general transcription instantiates this schema per (shape, pattern, realized base): the
per-member file supplies the cycle's row instances as hypotheses (word rows + family
window rows — apex/cover-floor/cover-entry on the hinge reading — at the realized laps),
the generated `Fresh.UniformAnchored_R<len>` lemma supplies the product inequality, and
`tropicalCycle_infeasible` is the engine unchanged.  No new engine work.
-/

namespace Fresh.UniformAnchoredCompose

open Fresh.TropicalCycle
open Fresh.UniformAnchored

/-- **The worked composition (shape `6→4→5→(closed)`, kinds `cand_irred+z_entry+z_entry`,
pattern τ = (−7), base k = 15, census word of death node 7 of y6k15): the shape lemma +
the three row instances kill the candidate.**  Any positive reading vector satisfying the
word's two `z_entry` rows and the candidate's `cand_irred` row at the realized laps is
impossible — the candidate (zone 4, lap 6) is rejected, i.e. the maximal word dies at it. -/
theorem shape_a034_pat2_k15_kills_cand (g : Fin 7 → ℝ) (hpos : ∀ i, 0 < g i)
    (hrow1 : RHolds true (g 4 / g 5) (((57:ℚ) / (31:ℚ) : ℝ)))
    (hrow2 : RHolds true (g 5 / g 6) (((65:ℚ) / (47:ℚ) : ℝ)))
    (hcand : RHolds true (g 6 / g 4) (((47:ℚ) / (121:ℚ) : ℝ))) : False := by
  -- the three cycle rows as TropicalCycle edges (the row instances of the census word,
  -- definitional)
  have he1 : EdgeSat g (⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩ : TEdge) := hrow1
  have he2 : EdgeSat g (⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩ : TEdge) := hrow2
  have he3 : EdgeSat g (⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩ : TEdge) := hcand
  -- the closed walk 4 → 5 → 6 → 4 (candidate zone → path → candidate's anchor → candidate)
  have hw : WalkFrom 4
      [⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩,
       ⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩,
       ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] 4 :=
    WalkFrom.cons 4 ⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩
      [⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩, ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] 4 rfl
      (WalkFrom.cons 5 ⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩
        [⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] 4 rfl
        (WalkFrom.cons 6 ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩ [] 4 rfl (WalkFrom.nil 4)))
  have hsat : ∀ x ∈ ([⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩,
      ⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩,
      ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] : List TEdge),
      EdgeSat g x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he1
    · rcases hx with rfl | hx
      · exact he2
      · rcases hx with rfl | hx
        · exact he3
        · exact absurd hx List.not_mem_nil
  have hend : ∀ x ∈ ([⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩,
      ⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩,
      ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] : List TEdge),
      0 < g x.a ∧ 0 < g x.b := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hpos 4, hpos 5⟩
    · rcases hx with rfl | hx
      · exact ⟨hpos 5, hpos 6⟩
      · rcases hx with rfl | hx
        · exact ⟨hpos 6, hpos 4⟩
        · exact absurd hx List.not_mem_nil
  -- the engine: a satisfied closed walk admits no bad cycle
  have hcontra := tropicalCycle_infeasible hw hsat hend
  refine hcontra ?_
  refine Or.inl ?_
  -- the walk's weight product, in the cycle's edge order
  have hprod : (List.map TEdge.c ([⟨4, 5, ((57:ℚ) / (31:ℚ) : ℝ), true⟩,
      ⟨5, 6, ((65:ℚ) / (47:ℚ) : ℝ), true⟩,
      ⟨6, 4, ((47:ℚ) / (121:ℚ) : ℝ), true⟩] : List TEdge)).prod
      = (↑((57:ℚ) / (31:ℚ)) : ℝ) * (↑((65:ℚ) / (47:ℚ)) * ↑((47:ℚ) / (121:ℚ))) := by
    simp [List.map_cons, List.prod_cons]
  rw [hprod]
  -- the shape lemma (the generated per-base-instance form) — the ℚ product, reordered to
  -- the walk's edge order and cast to ℝ
  have hq' : ((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((47:ℚ) / (121:ℚ)) < 1 := by
    have hq := shape_a034_pat2_k15
    rw [mul_assoc] at hq
    rw [mul_comm ((47:ℚ) / (121:ℚ)) (((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)))] at hq
    exact hq
  have h : (↑(((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((47:ℚ) / (121:ℚ))) : ℝ) < 1 := by
    exact_mod_cast hq'
  rw [Rat.cast_mul, Rat.cast_mul, mul_assoc] at h
  exact h

#print axioms shape_a034_pat2_k15_kills_cand

end Fresh.UniformAnchoredCompose
