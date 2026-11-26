import Fresh.NativeGroupEndpointRecovery

/-! Supplied comparisons may change their active packet at every step.
A finite history is an input here, never a length bound or a termination
argument. Two such histories from the same entry, when both endpoints clear
the whole arrangement, necessarily coalesce even if intermediate captures differ. -/
namespace Fresh.NativePacketHistoryCoalescence
open Fresh Fresh.Cascade Fresh.Localisation

theorem history_le_of_whole_lonely {whole : Finset ℝ}
    (hp : ∀ d∈whole, 0 < d) (packet : ℕ → Finset ℝ) (state : ℕ → ℝ)
    (N : ℕ) (t : ℝ)
    (hsub : ∀ j, j < N → packet j ⊆ whole)
    (hm : ∀ j, j < N → IsMove (packet j) (state j) (state (j+1)))
    (hstart : state 0 ≤ t) (hl : LonelyAt whole t) : state N ≤ t := by
  have hbound : ∀ j, j ≤ N → state j ≤ t := by
    intro j
    induction j with
    | zero => intro _; exact hstart
    | succ j ih =>
      intro hj
      exact isMove_le_of_lonely (fun d hd=>hp d (hsub j (by omega) hd))
        (fun d hd=>hl d (hsub j (by omega) hd)) (ih (by omega)) (hm j (by omega))
  exact hbound N le_rfl

theorem isolated_histories_coalesce {whole : Finset ℝ}
    (hp : ∀ d∈whole, 0 < d) (packet other : ℕ → Finset ℝ)
    (state trace : ℕ → ℝ) (N M : ℕ)
    (hs : state 0=trace 0)
    (hsub : ∀ j, j < N → packet j ⊆ whole)
    (hosub : ∀ j, j < M → other j ⊆ whole)
    (hm : ∀ j, j < N → IsMove (packet j) (state j) (state (j+1)))
    (hom : ∀ j, j < M → IsMove (other j) (trace j) (trace (j+1)))
    (hstart : state 0 ≤ state N) (hostart : trace 0 ≤ trace M)
    (hl : LonelyAt whole (state N)) (hol : LonelyAt whole (trace M)) :
    state N=trace M := by
  apply le_antisymm
  · exact history_le_of_whole_lonely hp packet state N _ hsub hm (by rw [hs]; exact hostart) hol
  · exact history_le_of_whole_lonely hp other trace M _ hosub hom (by rw [←hs]; exact hstart) hl

#print axioms history_le_of_whole_lonely
#print axioms isolated_histories_coalesce
end Fresh.NativePacketHistoryCoalescence
