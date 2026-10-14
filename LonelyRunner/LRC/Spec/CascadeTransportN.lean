import LonelyRunner.LRC.Cascade.Iteration

/-!
# Exact cascade transport, including unsuccessful separation steps

A sole blocker determines the next move without assuming that the endpoint is lonely.
The setter is clear at that endpoint, but there may be several new blockers. For any
previously active reading that is active again, its blocking lap has strictly increased.
These are local transport statements; they do not assert global termination.
-/

namespace LRC.CascadeTransport

open MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- A sole blocker sets the cascade move, whether or not other runners block its endpoint. -/
theorem move_eq_opening_of_only_blocker {ds : Finset ℝ} {c t : ℝ}
    (hcS : c ∈ ds) (hc : 0 < c) (hw : inWay n c t)
    (honly : ∀ d ∈ ds, inWay n d t → d = c) :
    move n ds t = nextOpening n c t := by
  classical
  apply le_antisymm
  · unfold move
    rw [Finset.fold_max_le]
    refine ⟨(lt_nextOpening hc hw).le, ?_⟩
    intro d hd
    split_ifs with h
    · rw [honly d hd h]
    · exact (lt_nextOpening hc hw).le
  · exact nextOpening_le_move hcS hw

/-- At a setter's opening, any remaining blocker is a different reading. This says nothing
about how many such readings there are, nor whether the setter can return on a later lap. -/
theorem blocker_ne_setter {c d t : ℝ} (hc : 0 < c)
    (hd : inWay n d (nextOpening n c t)) : d ≠ c := by
  intro h
  subst d
  unfold inWay at hd
  rw [circDist_at_nextOpening hc] at hd
  exact lt_irrefl _ hd

/-- Exact transport of a grid reading through a setter's exit. The displacement retains
the ratio `d/c`, including whole laps; taking residues before this step would lose it. -/
theorem reading_at_exit {c d t : ℝ} (hc : 0 < c) {K : ℤ}
    (hnear : |c * t - K| < (n : ℝ)⁻¹) :
    d * nextOpening n c t =
      d * t + (d / c) * ((K : ℝ) + (n : ℝ)⁻¹ - c * t) := by
  rw [nextOpening_eq hc hnear]
  field_simp
  ring

/-- A reading active both before and after a move cannot be in the same or an earlier
blocking lap: the maximum opening has already exhausted its old blocking interval. -/
theorem active_return_lap_increases {ds : Finset ℝ} {d t : ℝ} {K L : ℤ}
    (hdS : d ∈ ds) (hd : 0 < d) (hw : inWay n d t)
    (hK : |d * t - K| < (n : ℝ)⁻¹)
    (hL : |d * move n ds t - L| < (n : ℝ)⁻¹) : K < L := by
  have hopen := nextOpening_le_move hdS hw
  rw [nextOpening_eq hd hK, div_le_iff₀ hd] at hopen
  have hu := (abs_lt.mp hL).2
  have : (K : ℝ) < L := by nlinarith
  exact_mod_cast this

/-- Across any number of intervening handoffs, a previously blocked reading cannot return
to its old blocking lap. Later laps remain possible, so this is not global termination. -/
theorem return_lap_increases {ds : Finset ℝ} {d b : ℝ} {i j : ℕ} {K L : ℤ}
    (hdS : d ∈ ds) (hd : 0 < d) (hij : i < j)
    (hK : |d * (move n ds)^[i] b - K| < (n : ℝ)⁻¹)
    (hL : |d * (move n ds)^[j] b - L| < (n : ℝ)⁻¹) : K < L := by
  have hmono : Monotone (fun r : ℕ => (move n ds)^[r] b) := by
    apply monotone_nat_of_le_succ
    intro r
    rw [Function.iterate_succ_apply']
    exact le_move ds _
  have hw : inWay n d ((move n ds)^[i] b) :=
    lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ K) hK
  have hopen := nextOpening_le_move hdS hw
  have htime := hmono (Nat.succ_le_of_lt hij)
  change (move n ds)^[i + 1] b ≤ (move n ds)^[j] b at htime
  rw [Function.iterate_succ_apply'] at htime
  have hbound := le_trans hopen htime
  rw [nextOpening_eq hd hK, div_le_iff₀ hd] at hbound
  have hu := (abs_lt.mp hL).2
  have : (K : ℝ) < L := by nlinarith
  exact_mod_cast this

end LRC.CascadeTransport
