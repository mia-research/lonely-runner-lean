import Fresh.NativeGroupEndpointRecovery

/-! At a computed group isolation, the current captured packet is disjoint
from the cleared group. Its supplied native prefix gives another exact
restart reduction; recovery at its endpoint rejoins the endpoint family.
This does not assert that successive packets shrink or stop. -/
open Classical
namespace Fresh.NativePacketRestartExchange
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeReturnHandoff
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery

noncomputable def captures (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) : Finset (Fin 8) :=
  (Finset.univ.erase k).filter (fun i=>InWay (reading v k i) R)

theorem captures_subset (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) :
    captures v k R ⊆ Finset.univ.erase k := Finset.filter_subset _ _

theorem captures_disjoint_group (v : Fin 8 → ℝ) (k : Fin 8)
    (I : Finset (Fin 8)) (R : ℝ) (hgroup : LonelyAt (part v k I) R) :
    Disjoint (captures v k R) I := by
  apply Finset.disjoint_left.mpr
  intro i hi
  exact endpoint_capture_outside I R hgroup i (Finset.mem_filter.mp hi).2

theorem captures_proper (v : Fin 8 → ℝ) (k : Fin 8)
    (I : Finset (Fin 8)) (R : ℝ) (hI : I ⊆ Finset.univ.erase k)
    (hne : I.Nonempty) (hgroup : LonelyAt (part v k I) R) :
    captures v k R≠Finset.univ.erase k := by
  obtain ⟨i,hi⟩ := hne
  intro he
  have hm : i∈captures v k R := he.symm ▸ hI hi
  exact Finset.disjoint_left.mp (captures_disjoint_group v k I R hgroup) hm hi

theorem captures_empty_iff (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) :
    captures v k R=∅ ↔ IsolatedAt v k R := by
  rw [isolatedAt_iff_lonelyAt]
  constructor
  · intro he d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    apply not_lt.mp
    intro hw
    have hm : i∈captures v k R := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩,hw⟩
    simpa [he] using hm
  · intro hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hm,hw⟩ := Finset.mem_filter.mp hi
    exact not_lt_of_ge (hc _ (mem_disparitySet.mpr ⟨i,(Finset.mem_erase.mp hm).1,rfl⟩)) hw

theorem packet_restart_future_iff {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (R : ℝ) (N : ℕ) :
    (∃ t,R≤t ∧ IsolatedAt v k t) ↔
      ∃ t,cascadeSeq (part v k (captures v k R)) R N≤t ∧ IsolatedAt v k t :=
  physical_restart_future_iff hv k _ (captures_subset v k R) R N

theorem successive_packets_disjoint (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (N : ℕ)
    (hc : LonelyAt (part v k (captures v k R)) (cascadeSeq (part v k (captures v k R)) R N)) :
    Disjoint (captures v k (cascadeSeq (part v k (captures v k R)) R N)) (captures v k R) :=
  captures_disjoint_group v k _ _ hc

-- STANDING: DEFINITION
noncomputable def ExchangeEndpointClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (I : Finset (Fin 8)) (C : ℝ) (A B : ℕ),
    I ⊆ Finset.univ.erase k ∧ I.Nonempty ∧ 0<C ∧
    let R := cascadeSeq (part v k I) C A
    let J := captures v k R
    LonelyAt (part v k I) R ∧ J.Nonempty ∧ 0<B ∧
    cascadeSeq (part v k J) R (B-1)<cascadeSeq (part v k J) R B ∧
    LonelyAt (part v k J) (cascadeSeq (part v k J) R B) ∧
    (∀ d∈outside v k J,¬InWay d (cascadeSeq (part v k J) R B))

theorem exchangeEndpoint_into_groupEndpoint {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ExchangeEndpointClass v k) : GroupEndpointClass v k := by
  obtain ⟨hv,I,C,A,B,hI,hne,hC,hgroup,hcap,hB,hstrict,hpacket,hout⟩ := h
  have hp := part_pos hv k I hI
  have hR : 0<cascadeSeq (part v k I) C A := lt_of_lt_of_le hC (by
    simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove (part v k I) C) A)
  exact ⟨hv,captures v k _,_,B,captures_subset v k _,
    captures_proper v k I _ hI hne hgroup,hR,hB,hstrict,hpacket,hout⟩

theorem exchangeEndpoint_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ExchangeEndpointClass v k) : Isolation v k :=
  groupEndpoint_isolation (exchangeEndpoint_into_groupEndpoint h)

-- Two computed prefixes preserve the future question even when neither
-- intermediate comparison belongs to the original full-cascade history.
theorem two_group_restart_future_iff {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k)
    (C : ℝ) (A B : ℕ) :
    (∃ t,C≤t ∧ IsolatedAt v k t) ↔
      ∃ t,cascadeSeq (part v k (captures v k (cascadeSeq (part v k I) C A)))
        (cascadeSeq (part v k I) C A) B≤t ∧ IsolatedAt v k t :=
  (physical_restart_future_iff hv k I hI C A).trans (packet_restart_future_iff hv k _ B)

#print axioms captures_subset
#print axioms captures_disjoint_group
#print axioms captures_proper
#print axioms captures_empty_iff
#print axioms packet_restart_future_iff
#print axioms successive_packets_disjoint
#print axioms exchangeEndpoint_into_groupEndpoint
#print axioms exchangeEndpoint_isolation
#print axioms two_group_restart_future_iff
end Fresh.NativePacketRestartExchange
