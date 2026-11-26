import Fresh.FastestCaptureRecovery

/-! Original relative faces remove the fastest-setter restriction. Clear
readings retain their actual integer window when their entry closing face
allows the native capture displacement; captured partners may be up to
three times the setter, with opening order supplied by the actual move. -/
namespace Fresh.NativeRelativeCapture
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FastestCaptureRetention

theorem retained_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d) (hs : 0 ≤ s)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (N : ℝ)-1/8 < d*Q) (hhi : d*Q < (N : ℝ)+1/8)
    (hlower : (K : ℝ)+1/8 ≤ s*Q)
    (hface : s/4 ≤ d*((K : ℝ)+7/8-s*Q)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (K : ℝ)+7/8 := by
  have ht := Fresh.NativeOpeningRetention.capture_advance d Q P N hd hopen hlo hhi
  have hstep : d*(s*(P-Q)) ≤ s/4 := by
    calc
      _ = s*(d*(P-Q)) := by ring
      _ ≤ s*(1/4) := mul_le_mul_of_nonneg_left ht.2.le hs
      _ = _ := by ring
  have hlow := mul_nonneg hs ht.1.le
  constructor <;> nlinarith only [hstep,hlow,hlower,hface,hd]

theorem captured_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d) (hsd : s ≤ 3*d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (N : ℝ)-1/8 < d*Q) (hhi : d*Q < (N : ℝ)+1/8)
    (hpartner : s*Q < (K : ℝ)+1/8)
    (horder : d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P < (K : ℝ)+7/8 := by
  have ht := Fresh.NativeOpeningRetention.capture_advance d Q P N hd hopen hlo hhi
  have hstep := mul_le_mul_of_nonneg_right hsd ht.1.le
  have hl := Fresh.NativeOpeningRecovery.opening_order_lower d s P N K hd hopen horder
  constructor <;> nlinarith only [ht.2,hstep,hpartner,hl]

-- STANDING: DEFINITION
noncomputable def RelativeCaptureClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    u≠k ∧ 0 < Q ∧ (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
    IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
    ∀ i : Fin 8, i≠k → i≠u →
      (((L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧
        |v i-v k|/4 ≤ |v u-v k| * ((L i : ℝ)+7/8-|v i-v k| * Q)) ∨
       ((L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8 ∧
        |v i-v k| ≤ 3*|v u-v k|))

theorem terminal_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u : Fin 8) (hu : u≠k)
    (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ)
    (hlo : (N : ℝ)-1/8 < |v u-v k| * Q) (hhi : |v u-v k| * Q < (N : ℝ)+1/8)
    (hm : IsMove (disparitySet v k) Q (opening |v u-v k| N))
    (hb : ∀ i : Fin 8, i≠k → i≠u →
      (((L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧
        |v i-v k|/4 ≤ |v u-v k| * ((L i : ℝ)+7/8-|v i-v k| * Q)) ∨
       ((L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8 ∧
        |v i-v k| ≤ 3*|v u-v k|))) :
    Q < opening |v u-v k| N ∧ IsolatedAt v k (opening |v u-v k| N) := by
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ N hd ho hlo hhi
  refine ⟨by linarith only [ht.1],?_⟩
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul]
  by_cases hiu : i=u
  · subst i
    apply clear_of_window N
    · exact ho.ge
    · linarith only [ho]
  · rcases hb i hi hiu with hret|hcap
    · have hw := retained_window _ _ Q _ N (L i) hd (abs_nonneg _) ho hlo hhi hret.1 hret.2
      exact clear_of_window (L i) hw.1 hw.2
    · have hmem : |v i-v k| ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
      have horder := Fresh.FastestCaptureRecovery.captured_order_of_move N (L i) hm hmem hd
        (Fresh.Cascade.disparitySet_pos hv k _ hmem) ho hcap.1 hcap.2.1
      have hw := captured_window _ _ Q _ N (L i) hd hcap.2.2 ho hlo hhi hcap.2.1 horder
      exact clear_of_window (L i) hw.1 hw.2.le

theorem relative_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RelativeCaptureClass v k) : Isolation v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hm,hb⟩ := h
  obtain ⟨ht,hclear⟩ := terminal_clear hv k u hu Q N L hlo hhi hm hb
  exact ⟨opening |v u-v k| N,lt_trans hQ ht,hclear⟩

theorem fastest_into_relative {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.FastestCaptureRecovery.FastestRecoveryClass v k) : RelativeCaptureClass v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hb⟩ := h
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  have hm := (Fresh.FastestCaptureRecovery.terminal_move hv k u hu Q N L hlo hhi hb).2.1
  refine ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hm,?_⟩
  intro i hi hiu
  rcases hb i hi hiu with ⟨hsd,hret|hcap⟩
  · refine Or.inl ⟨hret.1,?_⟩
    have hprod := mul_nonneg hd.le (sub_nonneg.mpr hret.2)
    nlinarith only [hprod,hsd]
  · exact Or.inr ⟨hcap.1,hcap.2.1,by linarith only [hsd,hd]⟩

#print axioms retained_window
#print axioms captured_window
#print axioms terminal_clear
#print axioms relative_isolation
#print axioms fastest_into_relative
end Fresh.NativeRelativeCapture
