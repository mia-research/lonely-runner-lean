import Fresh.FourBlockPacketEntryArrangement

/-! An AP-independent native input family. When the fastest captured original
reading opens, every other reading retains its own integer window from the
entry [1/8,5/8] band. Its target clearance follows from actual displacement. -/
namespace Fresh.FastestCaptureRetention
open Fresh Fresh.Cascade Fresh.Localisation

noncomputable def opening (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ)+1/8)/d

-- STANDING: DEFINITION
noncomputable def FastestCaptureClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    u≠k ∧ 0 < Q ∧ (N : ℝ)-1/8 < |v u-v k| *Q ∧ |v u-v k| *Q < (N : ℝ)+1/8 ∧
    ∀ i : Fin 8, i≠k → i≠u → |v i-v k| ≤ |v u-v k| ∧
      (L i : ℝ)+1/8 ≤ |v i-v k| *Q ∧ |v i-v k| *Q ≤ (L i : ℝ)+5/8

theorem terminal_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u : Fin 8) (hu : u≠k)
    (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ)
    (hlo : (N : ℝ)-1/8 < |v u-v k| *Q) (hhi : |v u-v k| *Q < (N : ℝ)+1/8)
    (hb : ∀ i : Fin 8, i≠k → i≠u → |v i-v k| ≤ |v u-v k| ∧
      (L i : ℝ)+1/8 ≤ |v i-v k| *Q ∧ |v i-v k| *Q ≤ (L i : ℝ)+5/8) :
    Q < opening |v u-v k| N ∧
    IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
    IsolatedAt v k (opening |v u-v k| N) := by
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  have ho : |v u-v k| *opening |v u-v k| N=(N : ℝ)+1/8 := by
    dsimp [opening]
    field_simp
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ N hd ho hlo hhi
  have hclear : IsolatedAt v k (opening |v u-v k| N) := by
    intro i hi
    rw [←Fresh.Localisation.distInt_abs_mul]
    by_cases hiu : i=u
    · subst i
      apply clear_of_window N
      · exact ho.ge
      · linarith only [ho]
    · have hwin := Fresh.NativeOpeningRetention.slower_window _ _ Q _ N (L i) hd (abs_nonneg _) (hb i hi hiu).1
        ho hlo hhi (hb i hi hiu).2.1 (hb i hi hiu).2.2
      exact clear_of_window (L i) hwin.1 hwin.2.le
  have hnear : abs (|v u-v k| *Q-(N : ℝ)) < 1/8 := by rw [abs_lt]; constructor <;> linarith
  have hw : InWay |v u-v k| Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ N) hnear
  have hop : nextOpening |v u-v k| Q=opening |v u-v k| N := by rw [nextOpening_eq hnear]; rfl
  have hmem : |v u-v k| ∈ disparitySet v k := mem_disparitySet.mpr ⟨u,hu,rfl⟩
  refine ⟨by linarith only [ht.1],?_,hclear⟩
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening (Fresh.Cascade.disparitySet_pos hv k) hmem hw hop
    ((Fresh.Localisation.isolatedAt_iff _ _ _).1 hclear)

theorem fastestCapture_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FastestCaptureClass v k) : Isolation v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hb⟩ := h
  obtain ⟨ht,hm,hclear⟩ := terminal_move hv k u hu Q N L hlo hhi hb
  exact ⟨opening |v u-v k| N,lt_trans hQ ht,hclear⟩

#print axioms terminal_move
#print axioms fastestCapture_isolation
end Fresh.FastestCaptureRetention
