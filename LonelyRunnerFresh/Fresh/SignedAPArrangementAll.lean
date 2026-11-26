import Fresh.SignedSplitAPAll
import Fresh.SignedAPArrangement

/-!
Rules: 1–4, 8–18. Unconditional physical realization of two same-step AP
blocks at any noninteger relative offset, including interleaving. Each block
has at least two moving runners and total size eight. All original physical
speeds remain positive and distinct through the arrangement class.
[PROVISIONAL: covering; counting tool] inherited from the signed family.
-/
namespace Fresh.SplitAPArrangement
open Fresh Fresh.SplitAPBands

theorem noninteger_two_block_all (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hA : ∀ m : ℤ, A ≠ m) : ∀ k : Fin 8, Isolation (speeds c A p) k :=
  two_block_all_of_signed signed_split_train_noninteger c A p hp2 hp6 hA

theorem nonintegerTwoAPBlock_isolation {v : Fin 8 → ℝ}
    (h : NonintegerTwoAPBlockClass v) (k : Fin 8) : Isolation v k :=
  nonintegerTwoAPBlock_isolation_of_signed signed_split_train_noninteger h k

#print axioms noninteger_two_block_all
#print axioms nonintegerTwoAPBlock_isolation
end Fresh.SplitAPArrangement
