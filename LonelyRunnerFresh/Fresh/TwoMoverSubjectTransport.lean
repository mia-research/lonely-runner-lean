import Fresh.TwoMoverSubjectSeparated
import Fresh.PathForm

/-!
Rules: 1–4, 8–18. Positive scale, common drift, physical mirror and
relabeling transport for the new all-subject arrangement family.
A signed nonzero scale uses t/|s|; the negative sign reverses readings,
whose exact circle distances are unchanged. Physical positivity is retained
as an explicit hypothesis on the transported eight-speed arrangement.
The family proof inherits provisional tags only through the six S2 branches.
-/
open Classical
namespace Fresh.OneMover
open Fresh

/-- Exact signed affine speed transport; no runner is made stationary. -/
theorem subject_isolation_affine {v : Fin 8 → ℝ} {k : Fin 8}
    (B s : ℝ) (hs : s ≠ 0) (h : Isolation v k) :
    Isolation (fun i => B+s*v i) k := by
  obtain ⟨t, ht, hclear⟩ := h
  refine ⟨t/|s|, div_pos ht (abs_pos.mpr hs), ?_⟩
  intro i hi
  have hc := hclear i hi
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have he : (B+s*v i-(B+s*v k))*(t/|s|) = -((v i-v k)*t) := by
      rw [abs_of_neg hsneg]
      field_simp
      <;> ring
    rw [he, Fresh.Localisation.distInt_neg]
    exact hc
  · have he : (B+s*v i-(B+s*v k))*(t/|s|) = (v i-v k)*t := by
      rw [abs_of_pos hspos]
      field_simp
      <;> ring
    rw [he]
    exact hc

/-- The proved physical arrangement class at arbitrary scale/drift, physical
mirror and relabeling. The signed scale parameter includes both mirror domains. -/
theorem subject_end_affine_all (c x y B s : ℝ) (hs : s ≠ 0)
    (σ : Equiv.Perm (Fin 8))
    (hbase : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hphysical : IsArrangement (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)))
    (hx0 : 0 ≤ x) (hx : x < 1/6)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∀ k : Fin 8, Isolation (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)) k := by
  intro k
  have hi := subject_end_all_of_retention c x y hbase hx0 hx hretain (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

/-- Signed-scale and relabeling closure of the unbounded end-subject family. -/
theorem subject_end_affine_separated_all (c x y B s : ℝ) (hs : s ≠ 0)
    (σ : Equiv.Perm (Fin 8))
    (hbase : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hphysical : IsArrangement (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)))
    (hx : x < 1/6) (hd : 1-x ≤ |y-(c+x)|)
    (hsep : 4*(6-x) ≤ 3*|y-(c+x)|)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∀ k : Fin 8, Isolation (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)) k := by
  intro k
  have hi := subject_end_all_separated c x y hbase hx hd hsep hretain (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms subject_isolation_affine
#print axioms subject_end_affine_all
#print axioms subject_end_affine_separated_all
end Fresh.OneMover
