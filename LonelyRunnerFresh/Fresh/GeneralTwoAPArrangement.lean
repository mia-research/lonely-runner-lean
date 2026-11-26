import Fresh.SignedAPArrangementAll
import Fresh.TwoAPBlockInteger
import Fresh.APBlockSwap
import Fresh.APBlockSingleton

/-!
Rules: 1–4, 8–18. Every real relative offset of two same-step AP blocks,
each nonempty, total eight. Noninteger offsets include arbitrary
interleaving. Injectivity forces integer offsets into one of the two proved
separated branches; a block-label swap handles the negative branch.
Physical positivity/injectivity, signed scale, mirror, drift and labels remain
explicit. [PROVISIONAL: covering; counting tool] inherited from source laws.
-/
namespace Fresh.SplitAPArrangement
open Fresh Fresh.OneMover

theorem general_two_block_all (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hinj : Function.Injective (speeds c A p)) :
    ∀ k : Fin 8, Isolation (speeds c A p) k := by
  by_cases hnot : ∀ m : ℤ, A ≠ (m : ℝ)
  · exact noninteger_two_block_all c A p hp2 hp6 hnot
  · push_neg at hnot
    obtain ⟨m,hm⟩ := hnot
    rcases integer_offset_separated c A p hp2 hp6 m hm hinj with hgap | hnegative
    · exact two_block_all c A p hp2 hp6 hgap
    · exact negative_two_block_all c A p hp2 hp6 hnegative

theorem two_block_all_sizes (c A : ℝ) (p : ℕ) (hp1 : 1 ≤ p) (hp7 : p ≤ 7)
    (hinj : Function.Injective (speeds c A p)) :
    ∀ k : Fin 8, Isolation (speeds c A p) k := by
  by_cases h1 : p=1
  · subst p
    exact singleton_one_all c A hinj
  by_cases h7 : p=7
  · subst p
    exact singleton_seven_all c A hinj
  exact general_two_block_all c A p (by omega) (by omega) hinj

/-- Every real offset and every nonempty two-block size split, with
physical collision exclusions explicit. Singleton branches rejoin S1. -/
-- STANDING: DEFINITION
def GeneralTwoAPBlockClass (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v ∧
  ∃ (c A B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ p ≤ 7 ∧ s ≠ 0 ∧ Function.Injective (speeds c A p) ∧
    v = (fun i => B+s*speeds c A p (σ i))

theorem generalTwoAPBlock_isolation {v : Fin 8 → ℝ}
    (h : GeneralTwoAPBlockClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨hpos,hinj,c,A,B,s,p,σ,hp2,hp6,hs,hbase,hv⟩ := h
  rw [hv]
  have hi := two_block_all_sizes c A p hp2 hp6 hbase (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms general_two_block_all
#print axioms two_block_all_sizes
#print axioms generalTwoAPBlock_isolation
end Fresh.SplitAPArrangement
