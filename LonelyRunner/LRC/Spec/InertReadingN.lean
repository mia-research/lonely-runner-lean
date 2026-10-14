import LonelyRunner.LRC.Cascade.Iteration

/-!
# Inert-reading replacement (E316/E327)

A reading clear at each visited core state does not change those moves.
The clearance hypothesis is retained at every state; matching one phase
alone does not suffice. This is a sufficient reduction, not a claim that
arbitrary active readings can be removed or shifted.
-/

namespace LRC.InertReading
open MomentIterationN

theorem move_insert_clear (S : Finset ℝ) {d t : ℝ}
    (hclear : (8 : ℝ)⁻¹ ≤ circDist (d * t)) :
    move 8 (insert d S) t = move 8 S t := by
  classical
  by_cases hd : d ∈ S
  · rw [Finset.insert_eq_of_mem hd]
  · have hw : ¬ inWay 8 d t := not_lt_of_ge hclear
    unfold move
    rw [Finset.fold_insert hd, if_neg hw]
    exact max_eq_right (le_move (n := 8) S t)

theorem iterate_insert_clear (S : Finset ℝ) {d b : ℝ} (N : ℕ)
    (hclear : ∀ j < N, (8 : ℝ)⁻¹ ≤ circDist (d * (move 8 S)^[j] b)) :
    (move 8 (insert d S))^[N] b = (move 8 S)^[N] b := by
  revert hclear
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hclear
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun j hj => hclear j (Nat.lt_succ_of_lt hj))]
    exact move_insert_clear S (hclear N (Nat.lt_succ_self N))

/-- Two readings may be interchanged when both stay clear at every visited
core state. The result holds for each finite prefix length supplied. -/
theorem replacement_preserves_iterates (S : Finset ℝ) {d e b : ℝ} (N : ℕ)
    (hd : ∀ j < N, (8 : ℝ)⁻¹ ≤ circDist (d * (move 8 S)^[j] b))
    (he : ∀ j < N, (8 : ℝ)⁻¹ ≤ circDist (e * (move 8 S)^[j] b)) :
    (move 8 (insert d S))^[N] b = (move 8 (insert e S))^[N] b :=
  (iterate_insert_clear S N hd).trans (iterate_insert_clear S N he).symm

end LRC.InertReading
