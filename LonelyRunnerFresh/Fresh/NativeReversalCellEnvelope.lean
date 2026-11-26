import Fresh.NativeQuietReversalFamily

/-! One native cell envelope unifies wider outsider windows, including labels
above the current setter label. The envelope is derived from the old pair's
parameter face; no outsider closing/clearance comparison is supplied. Integer
labels remain independent and unbounded through the family parameters. -/
namespace Fresh.NativeReversalCellEnvelope
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeReturnSurvivors
  Fresh.NativeOpeningReversal Fresh.NativeOpeningReversalArrangement
  Fresh.NativeQuietReversalFamily Fresh.NativeFixedPrefixArrangement

-- STANDING: DEFINITION
noncomputable def Cell (M J : ℤ) (q : ℝ) : Prop :=
  0≤J ∧ (J : ℝ)+1/8≤q ∧
    (4*(M : ℝ)+1)*(q-(J : ℝ))+(J : ℝ) ≤ (7/2 : ℝ)*(M : ℝ)

theorem cell_window (M A N J : ℤ) (q T : ℝ)
    (hM : 1≤M) (hA : 1≤A) (hN : 4*A*M≤N) (hcell : Cell M J q)
    (hTlo : 1≤T) (hThi : T≤ending A N) : ¬InWay q T := by
  obtain ⟨hJ,hqlo,hface⟩ := hcell
  have hjr : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hmr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hmp : 0 < 4*(M : ℝ) := by linarith only [hmr]
  have hqp : 0≤q := by linarith only [hjr,hqlo]
  have ht := mul_le_mul_of_nonneg_left (sub_le_sub_right hThi 1) hmp.le
  have he := ending_step_face M A N hM hA hN
  have hstep : 4*(M : ℝ)*(T-1)≤1 := ht.trans he
  have hscaled := mul_le_mul_of_nonneg_left hstep hqp
  have hlo := mul_le_mul_of_nonneg_left hTlo hqp
  apply not_lt.mpr
  apply clear_of_window J
  · nlinarith only [hlo,hqlo]
  · have hupper : 4*(M : ℝ)*(q*T-((J : ℝ)+7/8))≤0 := by
      nlinarith only [hscaled,hface]
    by_contra hn
    have hp := mul_pos hmp (show 0<q*T-((J : ℝ)+7/8) by linarith only [hn])
    linarith only [hp,hupper]

theorem cell_label_range (M J : ℤ) (q : ℝ) (hM : 1≤M) (h : Cell M J q) : J<3*M := by
  obtain ⟨hJ,hqlo,hface⟩ := h
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hp : 0≤4*(M : ℝ)+1 := by linarith only [hm]
  have hs := mul_le_mul_of_nonneg_right (show (1/8 : ℝ) ≤ q-(J : ℝ) by linarith only [hqlo]) hp
  by_contra hn
  have hi : 3*M≤J := by omega
  have hr : 3*(M : ℝ)≤(J : ℝ) := by exact_mod_cast hi
  nlinarith only [hs,hface,hr]

theorem cell_exists_iff (M J : ℤ) (hM : 1≤M) :
    (∃ q : ℝ, Cell M J q) ↔ 0≤J ∧ J<3*M := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨hq.1,cell_label_range M J q hM hq⟩
  · rintro ⟨hJ,hJM⟩
    have hjm : (J : ℝ)+1≤3*(M : ℝ) := by exact_mod_cast hJM
    refine ⟨(J : ℝ)+1/8,hJ,by linarith,?_⟩
    nlinarith only [hjm]

theorem cell_upper_iff (M J : ℤ) (q : ℝ) (hM : 1≤M) :
    (4*(M : ℝ)+1)*(q-(J : ℝ))+(J : ℝ) ≤ (7/2 : ℝ)*(M : ℝ) ↔
      q≤(J : ℝ)+((7/2 : ℝ)*(M : ℝ)-(J : ℝ))/(4*(M : ℝ)+1) := by
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hp : 0<4*(M : ℝ)+1 := by linarith only [hm]
  have hh := (le_div_iff₀ hp : q-(J : ℝ)≤((7/2 : ℝ)*(M : ℝ)-(J : ℝ))/(4*(M : ℝ)+1) ↔
    (q-(J : ℝ))*(4*(M : ℝ)+1)≤(7/2 : ℝ)*(M : ℝ)-(J : ℝ))
  constructor
  · intro h
    have hs := hh.2 (by nlinarith only [h])
    linarith only [hs]
  · intro h
    have hs := hh.1 (by linarith only [h])
    nlinarith only [hs]

theorem wider_residue_cell (M J : ℤ) (q : ℝ) (hM : 1≤M) (hJ : 0≤J) (hJM : J<M)
    (hqlo : (J : ℝ)+1/8≤q) (hqhi : q≤(J : ℝ)+5/8) : Cell M J q := by
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hjm : (J : ℝ)+1≤(M : ℝ) := by exact_mod_cast hJM
  have hp : 0≤4*(M : ℝ)+1 := by linarith only [hm]
  have hs := mul_le_mul_of_nonneg_right (show q-(J : ℝ)≤5/8 by linarith only [hqhi]) hp
  exact ⟨hJ,hqlo,by nlinarith only [hs,hjm]⟩

theorem adjacent_residue_cell (M : ℤ) (q : ℝ) (hM : 1≤M)
    (hqlo : (M : ℝ)+1/8≤q) (hqhi : q≤(M : ℝ)+1/2) : Cell M M q := by
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hp : 0≤4*(M : ℝ)+1 := by linarith only [hm]
  have hs := mul_le_mul_of_nonneg_right (show q-(M : ℝ)≤1/2 by linarith only [hqhi]) hp
  exact ⟨by omega,hqlo,by nlinarith only [hs,hm]⟩

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b : Fin 8) (M A N : ℤ) (x : ℝ),
    a≠k ∧ b≠k ∧ a≠b ∧ 1≤M ∧ 1≤A ∧ 4*A*M≤N ∧ -(1/8 : ℝ)≤x ∧ x≤1/8 ∧
    reading v k a=anchor N ∧ reading v k b=partner M A N x ∧
    ∀ i : Fin 8, i≠k → i≠a → i≠b → ∃ J : ℤ, Cell M J (reading v k i)

theorem class_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Class v k) : PairRecoveryClass v k := by
  classical
  obtain ⟨hv,a,b,M,A,N,x,ha,hb,hab,hM,hA,hN,hxlo,hxhi,hda,hsb,houtside⟩ := h
  refine ⟨hv,a,b,1,N,ha,hb,hab,by norm_num,?_,?_,?_⟩
  · rw [hda]; simp only [mul_one,anchor]
  · rw [hsb]; exact (partner_entry M A N x hM hA hN hxlo hxhi).1
  · intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    have him := Finset.mem_sdiff.mp hi
    have hik := (Finset.mem_erase.mp him.1).1
    have hia : i≠a := by intro he; apply him.2; simp [he]
    have hib : i≠b := by intro he; apply him.2; simp [he]
    obtain ⟨J,hcell⟩ := houtside i hik hia hib
    rw [hda,hsb]
    exact cell_window M A N J _ _ hM hA hN hcell
      (partner_endpoint_bounds M A N x hM hA hN hxlo hxhi).1.le
      (partner_endpoint_bounds M A N x hM hA hN hxlo hxhi).2

theorem old_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeQuietReversalFamily.Class v k) : Class v k := by
  obtain ⟨hv,a,b,M,A,N,x,ha,hb,hab,hM,hA,hN,hxlo,hxhi,hda,hsb,houtside⟩ := h
  refine ⟨hv,a,b,M,A,N,x,ha,hb,hab,hM,hA,hN,hxlo,hxhi,hda,hsb,?_⟩
  intro i hi hia hib
  obtain ⟨J,hJ,hJM,hqlo,hqhi⟩ := houtside i hi hia hib
  exact ⟨J,wider_residue_cell M J _ hM hJ hJM hqlo (by linarith only [hqhi])⟩

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  pairRecovery_isolation (class_into_recovery h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

theorem old_scaled_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeQuietReversalFamily.ScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,old_into_class hbase⟩

#print axioms cell_window
#print axioms cell_label_range
#print axioms cell_exists_iff
#print axioms cell_upper_iff
#print axioms wider_residue_cell
#print axioms adjacent_residue_cell
#print axioms class_into_recovery
#print axioms old_into_class
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms old_scaled_into_class
end Fresh.NativeReversalCellEnvelope
