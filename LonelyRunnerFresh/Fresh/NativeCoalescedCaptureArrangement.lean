import Fresh.NativeCoalescedCaptureRelay

/-! Coalesced sole captures join the old partner family even when other
readers previously returned and recovered. A whole interval of changed
speeds may use different selected openings and then rejoin one fixed-group
opening; endpoint-label comparisons derive every interior clearance. -/
namespace Fresh.NativeCoalescedCaptureArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeOneReaderDeformation Fresh.NativeCoalescedCaptureRelay Fresh.NativeCapturedPartnerJoin
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def SoleFitsClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (U B : ℝ) (a : Fin 8), 0<U ∧ a≠k ∧
    IsMove (others v k a) U B ∧
    (label (reading v k a*U) : ℝ)+1/8 ≤ reading v k a*B ∧
    LonelyAt (others v k a) B ∧ InWay (reading v k a) B ∧
    (∀ i : Fin 8,i≠k → i≠a → handoffOpening v k B a ≤ closing (reading v k i) B)

theorem soleFits_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleFitsClass v k) : PartnerClass v k := by
  obtain ⟨hv,U,B,a,hU,ha,hm,hface,hfixed,hw,hfit⟩ := h
  have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hfull := (unchanged_move_iff (others_pos hv k a) (reading v k a) U B hp hm).2 hface
  rw [insert_others v k a ha] at hfull
  apply sole_capture_fits_partner hv k a U B hU ha hfull hw _ hfit
  intro i hi hia
  have hmem : reading v k i∈others v k a :=
    Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hia,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩⟩,rfl⟩
  exact not_lt.mpr (hfixed _ hmem)

theorem soleFits_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleFitsClass v k) : Isolation v k :=
  partner_isolation (soleFits_into_partner h)

theorem soleFits_into_old_sole {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleFitsClass v k) :
    SoleNoReturnClass v k := by
  obtain ⟨hv,U,B,a,hU,ha,hm,hface,hfixed,hw,hfit⟩ := h
  have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hfull := (unchanged_move_iff (others_pos hv k a) (reading v k a) U B hp hm).2 hface
  rw [insert_others v k a ha] at hfull
  have hother : ∀ i : Fin 8,i≠k → i≠a → ¬InWay (reading v k i) B := by
    intro i hi hia
    exact not_lt.mpr (hfixed _ (Finset.mem_image.mpr ⟨i,
      Finset.mem_erase.mpr ⟨hia,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩⟩,rfl⟩))
  have hsur := (survivor_iff hv k U B hfull a).2 ⟨ha,hw⟩
  have ht := sole_capture_handoff hv k a U B ha hfull hw hother
  refine ⟨hv,U,B,a,hU,hfull,hsur,?_,?_⟩
  · intro i hi
    by_contra hn
    exact hother i hi.1 hn ((survivor_iff hv k U B hfull i).1 hi).2
  · intro i hi
    by_cases he : i=a
    · subst i
      exact handoff_selected_zero hv k U B hfull a hsur
    · have hip := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
      apply (zero_iff_original_upper _ B _ hip.le ht.1.le).2
      have hh := (le_div_iff₀ hip).1 (hfit i hi he)
      simpa only [closing,mul_comm] using hh

theorem old_sole_into_soleFits {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleNoReturnClass v k) :
    SoleFitsClass v k := by
  obtain ⟨hv,U,B,a,hU,hm,hsa,hsole,hzero⟩ := h
  have ha := hsa.1
  have hw := ((survivor_iff hv k U B hm a).1 hsa).2
  have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hinsert : IsMove (insert (reading v k a) (others v k a)) U B := by
    rw [insert_others v k a ha]
    exact hm
  have hrest := delete_current_capture_move (reading v k a) U B hp hinsert hw
  refine ⟨hv,U,B,a,hU,ha,hrest,
    move_passes_entry_opening (disparitySet_pos hv k) U B _ hm (mem_disparitySet.mpr ⟨a,ha,rfl⟩),?_,hw,?_⟩
  · intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    have hia := (Finset.mem_erase.mp hi).1
    have hik := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    apply not_lt.mp
    intro hwi
    exact hia (hsole i ((survivor_iff hv k U B hm i).2 ⟨hik,hwi⟩))
  · intro i hi hia
    have hip := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    have ht := (sole_survivor_handoff hv k U B hm a hsa hsole).1
    have hu := (zero_iff_original_upper _ B _ hip.le ht.le).1 (hzero i hi)
    apply (le_div_iff₀ hip).2
    simpa only [closing,mul_comm] using hu

theorem soleFits_iff_old_sole {v : Fin 8 → ℝ} {k : Fin 8} :
    SoleFitsClass v k ↔ SoleNoReturnClass v k := ⟨soleFits_into_old_sole,old_sole_into_soleFits⟩

-- Endpoint speeds are comparison parameters, not additional physical runners.
-- The physical speed in the interval is still subject to IsArrangement.
-- STANDING: DEFINITION
noncomputable def RejoinIntervalClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a : Fin 8) (B C lo hi : ℝ) (M : ℤ), a≠k ∧ 0<B ∧ 0<lo ∧
    lo ≤ reading v k a ∧ reading v k a ≤ hi ∧
    label (lo*B)=M ∧ label (hi*B)=M ∧ InWay hi B ∧
    step (others v k a) B ≤ opening hi M ∧
    IsMove (others v k a) (opening lo M) C ∧ opening lo M<C ∧
    (∀ d∈others v k a,label (d*opening hi M)=label (d*opening lo M)) ∧
    LonelyAt (others v k a) C ∧ label (lo*C)=label (hi*C) ∧ ¬InWay lo C

theorem rejoinInterval_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RejoinIntervalClass v k) : Isolation v k := by
  obtain ⟨hv,a,B,C,lo,hi,M,ha,hB,hlo,hloR,hRhi,hlabelLo,hlabelHi,hwHi,hbase,hnext,hstrict,hrecords,hfixed,hlabelsC,hclearLo⟩ := h
  have hm := delayed_interval_moves (others_pos hv k a) lo (reading v k a) hi B C M
    hlo hloR hRhi hB hlabelLo hlabelHi hwHi hbase hnext hstrict hrecords
  have hQ : 0<opening (reading v k a) M := lt_trans hB hm.1
  have hQC := le_of_isMove (by
    intro d hd
    rw [insert_others v k a ha] at hd
    exact disparitySet_pos hv k d hd) hm.2.2
  have hC := lt_of_lt_of_le hQ hQC
  have hl := delayed_interval_isolated lo (reading v k a) hi C hloR hRhi hC.le hfixed hlabelsC hclearLo
  rw [insert_others v k a ha] at hl
  exact ⟨C,hC,(isolatedAt_iff_lonelyAt v k C).2 hl⟩

theorem rejoinInterval_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : RejoinIntervalClass v k) :
    CanonicalReturnClass v k := by
  obtain ⟨hv,a,B,C,lo,hi,M,ha,hB,hlo,hloR,hRhi,hlabelLo,hlabelHi,hwHi,hbase,hnext,hstrict,hrecords,hfixed,hlabelsC,hclearLo⟩ := h
  let Q := opening (reading v k a) M
  have hm := delayed_interval_moves (others_pos hv k a) lo (reading v k a) hi B C M
    hlo hloR hRhi hB hlabelLo hlabelHi hwHi hbase hnext hstrict hrecords
  have hQ : 0<Q := lt_trans hB hm.1
  have hmQC : IsMove (disparitySet v k) Q C := by
    simpa only [Q,insert_others v k a ha] using hm.2.2
  have hCpos : 0<C := lt_of_lt_of_le hQ (le_of_isMove (disparitySet_pos hv k) hmQC)
  have hclear : IsolatedAt v k C := by
    have hl := delayed_interval_isolated lo (reading v k a) hi C hloR hRhi hCpos.le hfixed hlabelsC hclearLo
    rw [insert_others v k a ha] at hl
    exact (isolatedAt_iff_lonelyAt v k C).2 hl
  have hM0 := positive_entry_label lo B hlo hB
  rw [hlabelLo] at hM0
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have hbounds := interval_opening_bounds lo (reading v k a) hi M hlo hloR hRhi (by linarith only [hMR])
  have hrecord : ∀ d∈others v k a,label (d*Q)=label (d*opening lo M) := by
    intro d hd
    exact label_between _ _ _ (mul_le_mul_of_nonneg_left hbounds.1 (others_pos hv k a d hd).le)
      (mul_le_mul_of_nonneg_left hbounds.2 (others_pos hv k a d hd).le) (hrecords d hd)
  rcases hnext with hfix|⟨d,hd,hwd,hC,hmax⟩
  · exact (ne_of_lt hstrict hfix.2.symm).elim
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hgk := (Finset.mem_erase.mp (Finset.mem_erase.mp hg).2).1
    have hdmem : reading v k g∈others v k a := Finset.mem_image.mpr ⟨g,hg,rfl⟩
    have hgp := others_pos hv k a _ hdmem
    have hlabel := hrecord _ hdmem
    rw [captured_opening _ _ hwd] at hC
    have hO : opening (reading v k g) (label (reading v k g*Q))=C := by
      dsimp [labelledOpening] at hC
      rw [hlabel]
      exact hC.symm
    have hQC : Q<C := lt_of_le_of_lt hbounds.2 hstrict
    have hid : reading v k g*C=(label (reading v k g*Q) : ℝ)+1/8 := by
      have hh := (div_eq_iff hgp.ne').1 hO
      nlinarith only [hh]
    have hwg : InWay (reading v k g) Q := by
      apply (inWay_iff_lower_not_passed _ _).2
      have hh := mul_lt_mul_of_pos_left hQC hgp
      nlinarith only [hh,hid]
    have hcap := capture_at_label _ Q hwg
    refine ⟨hv,g,Q,label (reading v k g*Q),hgk,hQ,hcap.1,hcap.2,?_,?_⟩
    · change IsMove (disparitySet v k) Q (opening (reading v k g) (label (reading v k g*Q)))
      rw [hO]
      exact hmQC
    · intro i hi hreturn
      change reading v k g*((label (reading v k i*opening (reading v k g) (label (reading v k g*Q))) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*Q) : ℝ)+1/8)
      rw [hO]
      have hnot : ¬InWay (reading v k i) C := by
        exact not_lt.mpr ((isolatedAt_iff_lonelyAt v k C).1 hclear _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩))
      have hlow := le_of_not_gt (fun hh=>hnot ((inWay_iff_lower_not_passed _ _).2 hh))
      have hprod := mul_le_mul_of_nonneg_left hlow hgp.le
      have hidentity := congrArg (fun x : ℝ=>reading v k i*x) hid
      change reading v k g*((label (reading v k i*C) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*Q) : ℝ)+1/8)
      nlinarith only [hprod,hidentity]

#print axioms soleFits_into_partner
#print axioms soleFits_isolation
#print axioms soleFits_into_old_sole
#print axioms old_sole_into_soleFits
#print axioms soleFits_iff_old_sole
#print axioms rejoinInterval_isolation
#print axioms rejoinInterval_into_canonical
end Fresh.NativeCoalescedCaptureArrangement
