import Fresh.SplitAPArrangement
import Fresh.OneMoverS1Self

/-! Rules1–4,8–18. Singleton/seven AP block splits rejoin the established
one-mover theorem. These are reused families, not new displacement laws.
[PROVISIONAL: covering; counting tool] inherited from S1. -/
namespace Fresh.SplitAPArrangement
open Fresh Fresh.OneMover

theorem singleton_one_eq (c A : ℝ) : speeds c A 1 = oneMover (c+A-1) c 0 := by
  funext i
  fin_cases i <;> norm_num [speeds,oneMover,Fin.ext_iff] <;> ring

theorem singleton_seven_eq (c A : ℝ) : speeds c A 7 = oneMover c (c+A) 7 := by
  funext i
  fin_cases i <;> norm_num [speeds,oneMover,Fin.ext_iff] <;> ring

theorem one_mover_all_of_injective (c x : ℝ) (m : Fin 8)
    (hinj : Function.Injective (oneMover c x m)) :
    ∀ k : Fin 8, Isolation (oneMover c x m) k := by
  have hx : ∀ i : Fin 8, i ≠ m → x ≠ c+((i : ℕ) : ℝ) := by
    intro i him he
    have hs : oneMover c x m m=oneMover c x m i := by simp [oneMover,him,he]
    exact him (hinj hs).symm
  intro k
  exact s1 c x m k hx

theorem singleton_one_all (c A : ℝ) (hinj : Function.Injective (speeds c A 1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1) k := by
  rw [singleton_one_eq] at hinj ⊢
  exact one_mover_all_of_injective _ _ _ hinj

theorem singleton_seven_all (c A : ℝ) (hinj : Function.Injective (speeds c A 7)) :
    ∀ k : Fin 8, Isolation (speeds c A 7) k := by
  rw [singleton_seven_eq] at hinj ⊢
  exact one_mover_all_of_injective _ _ _ hinj

#print axioms singleton_one_eq
#print axioms singleton_seven_eq
#print axioms one_mover_all_of_injective
#print axioms singleton_one_all
#print axioms singleton_seven_all
end Fresh.SplitAPArrangement
