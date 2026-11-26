import Fresh.FastestCaptureRetention

/-! A captured original competitor also clears at the fastest setter's
opening: its own opening is no later, while the actual displacement is
less than one quarter of its lap. Retained and captured readings combine. -/
namespace Fresh.FastestCaptureRecovery
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FastestCaptureRetention

theorem captured_partner_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d) (hsd : s ≤ d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (N : ℝ)-1/8 < d*Q) (hhi : d*Q < (N : ℝ)+1/8)
    (hpartner : s*Q < (K : ℝ)+1/8)
    (horder : d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P < (K : ℝ)+3/8 := by
  have ht := Fresh.NativeOpeningRetention.capture_advance d Q P N hd hopen hlo hhi
  have hstep := mul_le_mul_of_nonneg_right hsd ht.1.le
  have hl := Fresh.NativeOpeningRecovery.opening_order_lower d s P N K hd hopen horder
  constructor <;> linarith only [ht.2,hstep,hpartner,hl]

-- STANDING: DEFINITION
noncomputable def FastestRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    u≠k ∧ 0 < Q ∧ (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
    ∀ i : Fin 8, i≠k → i≠u → |v i-v k| ≤ |v u-v k| ∧
      (((L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧ |v i-v k| * Q ≤ (L i : ℝ)+5/8) ∨
       ((L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8 ∧
        |v u-v k| * ((L i : ℝ)+1/8) ≤ |v i-v k| * ((N : ℝ)+1/8)))

theorem terminal_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u : Fin 8) (hu : u≠k)
    (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ)
    (hlo : (N : ℝ)-1/8 < |v u-v k| * Q) (hhi : |v u-v k| * Q < (N : ℝ)+1/8)
    (hb : ∀ i : Fin 8, i≠k → i≠u → |v i-v k| ≤ |v u-v k| ∧
      (((L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧ |v i-v k| * Q ≤ (L i : ℝ)+5/8) ∨
       ((L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8 ∧
        |v u-v k| * ((L i : ℝ)+1/8) ≤ |v i-v k| * ((N : ℝ)+1/8)))) :
    Q < opening |v u-v k| N ∧ IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
      IsolatedAt v k (opening |v u-v k| N) := by
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ N hd ho hlo hhi
  have hclear : IsolatedAt v k (opening |v u-v k| N) := by
    intro i hi
    rw [←Fresh.Localisation.distInt_abs_mul]
    by_cases hiu : i=u
    · subst i
      apply clear_of_window N
      · exact ho.ge
      · linarith only [ho]
    · rcases hb i hi hiu with ⟨hsd,hret|hcap⟩
      · have hw := Fresh.NativeOpeningRetention.slower_window _ _ Q _ N (L i) hd (abs_nonneg _) hsd ho hlo hhi hret.1 hret.2
        exact clear_of_window (L i) hw.1 hw.2.le
      · have hw := captured_partner_window _ _ Q _ N (L i) hd hsd ho hlo hhi hcap.2.1 hcap.2.2
        apply clear_of_window (L i) hw.1
        linarith only [hw.2]
  have hnear : abs (|v u-v k| * Q-(N : ℝ)) < 1/8 := by rw [abs_lt]; constructor <;> linarith
  have hw : InWay |v u-v k| Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ N) hnear
  have hop : nextOpening |v u-v k| Q=opening |v u-v k| N := by rw [nextOpening_eq hnear]; rfl
  refine ⟨by linarith only [ht.1],?_,hclear⟩
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening (Fresh.Cascade.disparitySet_pos hv k)
    (mem_disparitySet.mpr ⟨u,hu,rfl⟩) hw hop ((Fresh.Localisation.isolatedAt_iff _ _ _).1 hclear)

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FastestRecoveryClass v k) : Isolation v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hb⟩ := h
  obtain ⟨ht,hm,hclear⟩ := terminal_move hv k u hu Q N L hlo hhi hb
  exact ⟨opening |v u-v k| N,lt_trans hQ ht,hclear⟩

theorem retained_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : FastestCaptureClass v k) : FastestRecoveryClass v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hb⟩ := h
  refine ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,?_⟩
  intro i hi hiu
  exact ⟨(hb i hi hiu).1,Or.inl (hb i hi hiu).2⟩

theorem captured_order_of_move {ds : Finset ℝ} {d s Q P : ℝ} (N K : ℤ)
    (hm : IsMove ds Q P) (hmem : s ∈ ds) (hd : 0 < d) (hs : 0 < s)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (K : ℝ)-1/8 < s*Q) (hhi : s*Q < (K : ℝ)+1/8) :
    d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8) := by
  have hn : |s*Q-(K : ℝ)| < 1/8 := by rw [abs_lt]; constructor <;> linarith
  have hw : InWay s Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ K) hn
  have ht : nextOpening s Q ≤ P := by
    rcases hm with hfixed|⟨e,he,hwe,hP,hmax⟩
    · exact (hfixed.1 s hmem hw).elim
    · exact hmax s hmem hw
  have heq : s*nextOpening s Q=(K : ℝ)+1/8 := by
    rw [nextOpening_eq hn]
    field_simp
  have hl : (K : ℝ)+1/8 ≤ s*P := by
    have hh := mul_le_mul_of_nonneg_left ht hs.le
    linarith only [hh,heq]
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  have hlow := mul_le_mul_of_nonneg_left hl hd.le
  nlinarith only [hscaled,hlow]

-- STANDING: DEFINITION
noncomputable def ActualFastestClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    u≠k ∧ 0 < Q ∧ (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
    IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
    ∀ i : Fin 8, i≠k → i≠u → |v i-v k| ≤ |v u-v k| ∧
      (((L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧ |v i-v k| * Q ≤ (L i : ℝ)+5/8) ∨
       ((L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8))

theorem actual_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : ActualFastestClass v k) : FastestRecoveryClass v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hm,hb⟩ := h
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  refine ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,?_⟩
  intro i hi hiu
  refine ⟨(hb i hi hiu).1,?_⟩
  rcases (hb i hi hiu).2 with hret|hcap
  · exact Or.inl hret
  · have hmem : |v i-v k| ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
    exact Or.inr ⟨hcap.1,hcap.2,captured_order_of_move N (L i) hm hmem hd
      (Fresh.Cascade.disparitySet_pos hv k _ hmem) ho hcap.1 hcap.2⟩

theorem actual_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ActualFastestClass v k) : Isolation v k :=
  recovery_isolation (actual_into_recovery h)

#print axioms captured_order_of_move
#print axioms actual_into_recovery
#print axioms actual_isolation
#print axioms captured_partner_window
#print axioms terminal_move
#print axioms recovery_isolation
#print axioms retained_into_recovery
end Fresh.FastestCaptureRecovery
