import LonelyRunner.LRC.Spec.CoreWindowInsertionN

/-!
# Compatibility of obstructions to several core-clear windows

Eliminate the inserted speed from a fixed family of capture labels. Strict
cross inequalities are necessary and sufficient. Their failure certifies a
surviving core window, but no claim is made that failure always occurs.
-/

namespace LRC.CoreWindowCompatibility

variable {ι : Type*}

/-- Positive common points of finitely many open intervals are determined
by all lower-to-upper comparisons, provided every upper endpoint is positive. -/
theorem positive_open_intervals_iff (S : Finset ι) (hS : S.Nonempty)
    (lo hi : ι → ℝ) (hhi : ∀ i ∈ S, 0 < hi i) :
    (∃ V : ℝ, 0 < V ∧ ∀ i ∈ S, lo i < V ∧ V < hi i) ↔
      ∀ i ∈ S, ∀ j ∈ S, lo i < hi j := by
  classical
  constructor
  · rintro ⟨V, _, h⟩ i hiS j hjS
    exact (h i hiS).1.trans (h j hjS).2
  · intro h
    let b := S.inf' hS hi
    let a := max 0 (S.sup' hS lo)
    have hb : 0 < b := by
      obtain ⟨i, hiS, he⟩ := Finset.exists_mem_eq_inf' hS hi
      simpa [b, he] using hhi i hiS
    have hab : a < b := by
      apply max_lt hb
      obtain ⟨j, hjS, he⟩ := Finset.exists_mem_eq_inf' hS hi
      change S.sup' hS lo < S.inf' hS hi
      rw [he]
      exact (Finset.sup'_lt_iff hS).mpr (fun i hiS => h i hiS j hjS)
    refine ⟨(a + b) / 2, ?_, ?_⟩
    · have ha : 0 ≤ a := le_max_left _ _
      linarith
    · intro i hiS
      have hl : lo i ≤ a := (Finset.le_sup' lo hiS).trans (le_max_right _ _)
      have hu : b ≤ hi i := Finset.inf'_le hi hiS
      constructor <;> linarith

/-- Exact symbolic elimination of the added speed for a prescribed capture
label on each window. Includes comparisons of a window with itself. -/
theorem joint_capture_iff (S : Finset ι) (hS : S.Nonempty)
    (L U : ι → ℝ) (K : ι → ℤ)
    (hL : ∀ i ∈ S, 0 < L i) (hU : ∀ i ∈ S, 0 < U i)
    (hK : ∀ i ∈ S, 0 ≤ K i) :
    (∃ V : ℝ, 0 < V ∧ ∀ i ∈ S,
      (K i : ℝ) - 1 / 8 < V * L i ∧ V * U i < (K i : ℝ) + 1 / 8) ↔
    ∀ i ∈ S, ∀ j ∈ S,
      ((K i : ℝ) - 1 / 8) * U j < ((K j : ℝ) + 1 / 8) * L i := by
  have hhi : ∀ i ∈ S, 0 < ((K i : ℝ) + 1 / 8) / U i := by
    intro i hi
    have hk : (0 : ℝ) ≤ K i := by exact_mod_cast hK i hi
    exact div_pos (by linarith) (hU i hi)
  have hw := positive_open_intervals_iff S hS
    (fun i => ((K i : ℝ) - 1 / 8) / L i)
    (fun i => ((K i : ℝ) + 1 / 8) / U i) hhi
  have hb : (∃ V : ℝ, 0 < V ∧ ∀ i ∈ S,
      (K i : ℝ) - 1 / 8 < V * L i ∧ V * U i < (K i : ℝ) + 1 / 8) ↔
      ∃ V : ℝ, 0 < V ∧ ∀ i ∈ S,
        ((K i : ℝ) - 1 / 8) / L i < V ∧
          V < ((K i : ℝ) + 1 / 8) / U i := by
    apply exists_congr
    intro V
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rw [div_lt_iff₀ (hL i hi), lt_div_iff₀ (hU i hi)]
  rw [hb, hw]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  exact div_lt_div_iff₀ (hL i hi) (hU j hj)

end LRC.CoreWindowCompatibility
