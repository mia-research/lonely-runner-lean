import Fresh.TwoMoverSubjectTransport

/-!
Rules: 1–4, 8–18. Physical arrangement class packaging the proved subject-mover
families for consumption by an arrangement-class union. Positivity and
injectivity of the physical speeds are explicit. The base is a physical AP
with its endpoint subject and the other endpoint moved; signed affine scale
and arbitrary relabeling include physical mirrors. The two alternatives are
(1) the sharper nonnegative-x retention family, or (2) the separated family
with x unbounded below. No numerical bound, sample, or unproved universal
continuation enters this class.
[PROVISIONAL: covering; counting tool] inherited only through the six frozen
subjects' established S2 theorem branches; the new moved-subject displacement
and other moved-subject clearance use exact native boundary inequalities.
-/

namespace Fresh.OneMover
open Fresh

/-- An all-subject physical family. The OR joins the sharper near-endpoint
branch with the unbounded separated-outlier branch. -/
-- STANDING: DEFINITION
def TwoMoverSubjectClass (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v ∧
  ∃ (c x y B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    s ≠ 0 ∧ IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7) ∧
    v = (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)) ∧
    x < 1/6 ∧
    2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)| ∧
    (0 ≤ x ∨ (1-x ≤ |y-(c+x)| ∧ 4*(6-x) ≤ 3*|y-(c+x)|))

/-- Consuming theorem: every moving subject of the class isolates. -/
theorem twoMoverSubjectClass_isolation {v : Fin 8 → ℝ}
    (h : TwoMoverSubjectClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨hpos, hinj, c, x, y, B, s, σ, hs, hbase, hv, hx, hretain, hbranch⟩ := h
  have hphysical : IsArrangement (fun i => B+s*twoMover c (c+x) y (0 : Fin 8) 7 (σ i)) := by
    rw [← hv]
    exact ⟨hpos, hinj⟩
  rw [hv]
  rcases hbranch with hx0 | ⟨hd,hsep⟩
  · exact subject_end_affine_all c x y B s hs σ hbase hphysical hx0 hx hretain k
  · exact subject_end_affine_separated_all c x y B s hs σ hbase hphysical hx hd hsep hretain k

#print axioms twoMoverSubjectClass_isolation
end Fresh.OneMover
