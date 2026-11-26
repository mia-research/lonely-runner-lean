import Fresh.UniformStepFourArrangement
import Fresh.StepFourAll

/-!
Rules:1–4,8–18. All-subject4+4 physical AP blocks with ANY positive real
step ratio b, arbitrary common scale/drift/mirror/labels, and original gap
at least21max(1,b) in units of the first internal step. The actual proved
uniform mixed-packet theorem discharges the conditional physical assembly.
[PROVISIONAL: counting tool; covering] inherited source phase selection/split.
-/
namespace Fresh.UniformStepFourArrangement
open Fresh Fresh.UnequalAPArrangement

theorem uniform_four_all (c A b : ℝ) (hb : 0<b)
    (hgap : 21*max (1 : ℝ) b ≤ A-3) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 4) k :=
  uniform_four_positive_all_of (fun x b hb hx => Fresh.StepFourAll.step_four_all hb hx) c A b hb hgap

theorem uniformFourArrangement_isolation {V : Fin 8 → ℝ}
    (h : UniformFourArrangementClass V) (k : Fin 8) : Isolation V k :=
  uniformFourArrangement_isolation_of (fun x b hb hx => Fresh.StepFourAll.step_four_all hb hx) h k

#print axioms uniform_four_all
#print axioms uniformFourArrangement_isolation
end Fresh.UniformStepFourArrangement
