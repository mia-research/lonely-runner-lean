import Fresh.NativeOpeningReversal
import Fresh.NativePacketUnionCompression

/-! Physical two-reader reversal/recovery families. The pair endpoint is
proved from its openings; only outsiders' recovery or a first closing guard
remains a hypothesis. Whole speed intervals share a final return opening. -/
open Classical
namespace Fresh.NativeOpeningReversalArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery
  Fresh.NativeOpeningReversal Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def PairRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b : Fin 8) (B : ℝ) (N : ℤ),
    a≠k ∧ b≠k ∧ a≠b ∧ 0<B ∧ reading v k a*B=(N : ℝ)+1/8 ∧ InWay (reading v k b) B ∧
    (∀ d∈outside v k {a,b},¬InWay d (partnerEnd (reading v k a) (reading v k b) B))

theorem pairRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PairRecoveryClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,a,b,B,N,ha,hb,hab,hB,ho,hw,hout⟩ := h
  have hI : ({a,b} : Finset (Fin 8)) ⊆ Finset.univ.erase k := by
    intro i hi
    rcases Finset.mem_insert.mp hi with he|hi
    · subst i; exact Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩
    · rw [Finset.mem_singleton.mp hi]; exact Finset.mem_erase.mpr ⟨hb,Finset.mem_univ _⟩
  have hd := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hs := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hh := pair_last_move_and_clear (reading v k a) (reading v k b) B N hd hs ho hw
  obtain ⟨U,hBU,hUE,hm⟩ := hh.1
  have hpart : part v k {a,b}={reading v k a,reading v k b} := by simp [part]
  rw [←hpart] at hm
  have hc : LonelyAt (part v k {a,b}) (partnerEnd (reading v k a) (reading v k b) B) := by
    simpa only [hpart] using hh.2
  have hf := endpoint_clear_preserves_move (part_pos hv k {a,b} hI) (outside_pos hv k {a,b}) _ _ hm hout
  have hclear := endpoint_union_lonely hc hout
  rw [part_union_outside v k {a,b} hI] at hf hclear
  exact canonical_of_isolating_move hv k _ _ (hB.trans_le hBU) hUE hf ((isolatedAt_iff_lonelyAt v k _).2 hclear)

theorem pairRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PairRecoveryClass v k) : Isolation v k := canonical_isolation (pairRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def PairGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b : Fin 8) (B f : ℝ) (N : ℤ),
    a≠k ∧ b≠k ∧ a≠b ∧ 0<B ∧ reading v k a*B=(N : ℝ)+1/8 ∧ InWay (reading v k b) B ∧
    f∈outside v k {a,b} ∧ (∀ d∈outside v k {a,b},¬InWay d B) ∧
    (∀ d∈outside v k {a,b},closing f B ≤ closing d B) ∧
    partnerEnd (reading v k a) (reading v k b) B ≤ closing f B

theorem pairGuard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PairGuardClass v k) : PairRecoveryClass v k := by
  obtain ⟨hv,a,b,B,f,N,ha,hb,hab,hB,ho,hw,hf,hclear,hfirst,hfit⟩ := h
  have hd := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hs := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  obtain ⟨U,hBU,hUE,hm⟩ := (pair_last_move_and_clear _ _ B N hd hs ho hw).1
  have hBE := hBU.trans hUE.le
  refine ⟨hv,a,b,B,N,ha,hb,hab,hB,ho,hw,?_⟩
  intro d hdmem
  have hp := outside_pos hv k {a,b} d hdmem
  have hlo := le_of_not_gt (fun hh=>(hclear d hdmem) ((inWay_iff_lower_not_passed d B).2 hh))
  have hu := (le_div_iff₀ hp).1 (hfit.trans (hfirst d hdmem))
  have hu' : d*partnerEnd (reading v k a) (reading v k b) B ≤ (label (d*B) : ℝ)+7/8 := by
    simpa only [closing,mul_comm] using hu
  exact (band_at_point d B _ _ (label (d*B)) hp.le hBE le_rfl hlo hu').1

theorem pairGuard_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PairGuardClass v k) : Isolation v k := pairRecovery_isolation (pairGuard_into_recovery h)

-- All intermediate partner openings in an interval return to one fixed
-- anchor opening. Endpoint capture inequalities are strict, without floats.
theorem reversal_interval_endpoint (d lo s hi B : ℝ) (N M L : ℤ)
    (hd : 0<d) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hB : 0<B)
    (ho : d*B=(N : ℝ)+1/8) (hla : label (lo*B)=M) (hlb : label (hi*B)=M)
    (hwhi : InWay hi B) (hM : 0 ≤ (M : ℝ)+1/8)
    (hleft : (L : ℝ)-1/8<d*opening hi M) (hright : d*opening lo M<(L : ℝ)+1/8) :
    partnerEnd d s B=opening d L ∧ LonelyAt ({d,s} : Finset ℝ) (opening d L) := by
  have hs := hlo.trans_le hls
  have hlabel := speed_interval_label lo s hi B hls hsh hB.le (hla.trans hlb.symm)
  rw [hla] at hlabel
  have hw := speed_interval_capture lo s hi B hls hsh hB.le (hla.trans hlb.symm) hwhi
  have hbounds := interval_opening_bounds lo s hi M hlo hls hsh hM
  have hlow := hleft.trans_le (mul_le_mul_of_nonneg_left hbounds.1 hd.le)
  have hhigh := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbounds.2 hd.le) hright
  have hL : label (d*opening s M)=L := (entry_iff_label d (opening s M) L).1 (Or.inr ⟨hlow,hhigh⟩)
  have hwD : InWay d (opening s M) := (inWay_iff_lower_not_passed _ _).2 (by rw [hL]; exact hhigh)
  have he : labelledOpening s B=opening s M := by simp only [labelledOpening,hlabel]
  have hE : partnerEnd d s B=opening d L := by
    unfold partnerEnd
    rw [he,if_pos hwD]
    simp only [labelledOpening,hL]
  exact ⟨hE,hE ▸ (pair_last_move_and_clear d s B N hd hs ho hw).2⟩

-- A completed pair tail either isolates or forces a genuinely third reader.
-- In particular, pure alternation of these two readers cannot continue.
theorem pair_endpoint_captures_outside {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a b : Fin 8) (B : ℝ) (N : ℤ) (ha : a≠k) (hb : b≠k)
    (ho : reading v k a*B=(N : ℝ)+1/8) (hw : InWay (reading v k b) B)
    (i : Fin 8) (hi : InWay (reading v k i) (partnerEnd (reading v k a) (reading v k b) B)) :
    i≠a ∧ i≠b := by
  have hd := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hs := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hc := (pair_last_move_and_clear _ _ B N hd hs ho hw).2
  constructor
  · intro he; subst i
    exact not_lt_of_ge (hc _ (Finset.mem_insert_self _ _)) hi
  · intro he; subst i
    exact not_lt_of_ge (hc _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hi

theorem pair_endpoint_dichotomy {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a b : Fin 8) (B : ℝ) (N : ℤ) (ha : a≠k) (hb : b≠k)
    (ho : reading v k a*B=(N : ℝ)+1/8) (hw : InWay (reading v k b) B) :
    IsolatedAt v k (partnerEnd (reading v k a) (reading v k b) B) ∨
      ∃ i : Fin 8,i≠k ∧ i≠a ∧ i≠b ∧
        InWay (reading v k i) (partnerEnd (reading v k a) (reading v k b) B) := by
  by_cases hc : IsolatedAt v k (partnerEnd (reading v k a) (reading v k b) B)
  · exact Or.inl hc
  · right
    have hh : ∃ i : Fin 8,i≠k ∧ InWay (reading v k i) (partnerEnd (reading v k a) (reading v k b) B) := by
      by_contra hn
      apply hc
      rw [isolatedAt_iff_lonelyAt]
      intro d hd
      obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
      exact not_lt.mp (fun hw=>hn ⟨i,hi,hw⟩)
    obtain ⟨i,hi,hw'⟩ := hh
    have hx := pair_endpoint_captures_outside hv k a b B N ha hb ho hw i hw'
    exact ⟨i,hi,hx.1,hx.2,hw'⟩

#print axioms pair_endpoint_captures_outside
#print axioms pair_endpoint_dichotomy

#print axioms pairRecovery_into_canonical
#print axioms pairRecovery_isolation
#print axioms pairGuard_into_recovery
#print axioms pairGuard_isolation
#print axioms reversal_interval_endpoint
end Fresh.NativeOpeningReversalArrangement
