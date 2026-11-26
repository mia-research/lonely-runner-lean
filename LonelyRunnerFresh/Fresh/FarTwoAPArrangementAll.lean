import Fresh.APPhaseAll
import Fresh.FarTwoAPArrangement

/-!
Rules:1–4,8–18. Every subject for two separated AP blocks with arbitrary
positive real internal steps, sizes2..6,total8, original gap at least96
of the larger internal step. The actual proved AP packet theorem discharges
the explicit conditional assembly. Physical positive/distinct speeds,
signed scale, physical mirror, common drift and all labels are retained.
[PROVISIONAL: counting tool; covering] inherited phase selection/finite joins.
-/
namespace Fresh.FarTwoAPArrangement
open Fresh Fresh.UnequalAPArrangement

theorem far_two_ap_all (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 0<b) (hgap : 96*max (1 : ℝ) b ≤ A-((p : ℝ)-1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b p) k :=
  far_positive_all_of Fresh.APPhaseCharts.ap_packet_all c A b p hp2 hp6 hb hgap

theorem farTwoAPBlock_isolation {V : Fin 8 → ℝ}
    (h : FarTwoAPBlockClass V) (k : Fin 8) : Isolation V k :=
  farTwoAPBlock_isolation_of Fresh.APPhaseCharts.ap_packet_all h k

#print axioms far_two_ap_all
#print axioms farTwoAPBlock_isolation
end Fresh.FarTwoAPArrangement
