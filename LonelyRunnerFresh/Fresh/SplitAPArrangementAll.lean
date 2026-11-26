import Fresh.SplitAPPositive
import Fresh.SplitAPArrangement

/-!
Rules: 1–4, 8–18. All moving subjects for two disjoint AP blocks with
the same step, total eight speeds, each block length at least two.
The actual positive splitTrain theorem discharges the conditional assembly.
No additional gap size is required beyond strict ordering of the blocks.
Signed scale, physical mirror, drift and labels are included in the class.
[PROVISIONAL: covering; counting tool] inherited from SplitAPPositive.
Interleaved blocks 0<A<p-1 are outside this theorem; A=p-1 is a collision.
-/
namespace Fresh.SplitAPArrangement
open Fresh Fresh.SplitAPBands

theorem two_block_all (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hgap : (p : ℝ)-1 < A) : ∀ k : Fin 8, Isolation (speeds c A p) k :=
  two_block_all_of_split split_train_positive c A p hp2 hp6 hgap

theorem twoAPBlock_isolation {v : Fin 8 → ℝ}
    (h : TwoAPBlockClass v) (k : Fin 8) : Isolation v k :=
  twoAPBlock_isolation_of_split split_train_positive h k

#print axioms two_block_all
#print axioms twoAPBlock_isolation
end Fresh.SplitAPArrangement
