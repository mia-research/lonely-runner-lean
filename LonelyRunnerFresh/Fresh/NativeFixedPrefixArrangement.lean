import Fresh.NativeFixedPrefixTransport

/-! Proper physical subgroups with a supplied native cascade prefix. Whole
prefix opening faces retain recovered outsiders; a first closing guard or
a two-endpoint phase band discharges all such faces at once. The prefix
length is supplied and unbounded. No lower-order existence result is used. -/
open Classical
namespace Fresh.NativeFixedPrefixArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeFixedPrefixTransport Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention
  Fresh.NativeCanonicalReturn

noncomputable def part (v : Fin 8 → ℝ) (k : Fin 8) (I : Finset (Fin 8)) : Finset ℝ := I.image (reading v k)
noncomputable def outside (v : Fin 8 → ℝ) (k : Fin 8) (I : Finset (Fin 8)) : Finset ℝ :=
  ((Finset.univ.erase k)\I).image (reading v k)

theorem part_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (I : Finset (Fin 8))
    (hI : I ⊆ Finset.univ.erase k) : ∀ d∈part v k I,0<d := by
  intro d hd
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
  exact disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,(Finset.mem_erase.mp (hI hi)).1,rfl⟩)

theorem outside_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (I : Finset (Fin 8)) :
    ∀ d∈outside v k I,0<d := by
  intro d hd
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
  exact disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,
    (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1,rfl⟩)

theorem part_union_outside (v : Fin 8 → ℝ) (k : Fin 8) (I : Finset (Fin 8))
    (hI : I ⊆ Finset.univ.erase k) : part v k I∪outside v k I=disparitySet v k := by
  have hh := Finset.union_sdiff_of_subset hI
  dsimp [part,outside]
  rw [←Finset.image_union,hh]
  rfl

theorem prefix_endpoint_captures_outside {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (I : Finset (Fin 8)) (C : ℝ) (N : ℕ) (hI : I ⊆ Finset.univ.erase k)
    (hfaces : PrefixFaces (part v k I) (outside v k I) C N)
    (hfixed : LonelyAt (part v k I) (cascadeSeq (part v k I) C N))
    (i : Fin 8) (hcap : InWay (reading v k i) (cascadeSeq (disparitySet v k) C N)) : i∉I := by
  have he := (prefix_same_iff_faces (part_pos hv k I hI) (outside_pos hv k I) C N).2 hfaces N le_rfl
  rw [part_union_outside v k I hI] at he
  rw [he] at hcap
  intro hi
  exact not_lt_of_ge (hfixed _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)) hcap

theorem canonical_of_isolating_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U R : ℝ)
    (hU : 0<U) (hUR : U<R) (hm : IsMove (disparitySet v k) U R) (hclear : IsolatedAt v k R) :
    CanonicalReturnClass v k := by
  rcases hm with hf|⟨d,hd,hw,hR,hmax⟩
  · exact (ne_of_lt hUR hf.2.symm).elim
  · have hmOriginal : IsMove (disparitySet v k) U R := Or.inr ⟨d,hd,hw,hR,hmax⟩
    obtain ⟨g,hg,rfl⟩ := mem_disparitySet.mp hd
    have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
    have hgp : 0<reading v k g := hp
    have hcap := capture_at_label (reading v k g) U hw
    rw [next_at_label _ U hw] at hR
    have hO : opening (reading v k g) (label (reading v k g*U))=R := hR.symm
    have hid : reading v k g*R=(label (reading v k g*U) : ℝ)+1/8 := by
      have hh := (div_eq_iff hgp.ne').1 hO
      change (label (reading v k g*U) : ℝ)+1/8=R*reading v k g at hh
      nlinarith only [hh]
    refine ⟨hv,g,U,label (reading v k g*U),hg,hU,hcap.1,hcap.2,?_,?_⟩
    · change IsMove (disparitySet v k) U (opening (reading v k g) (label (reading v k g*U)))
      rw [hO]
      exact hmOriginal
    · intro i hi hret
      change reading v k g*((label (reading v k i*opening (reading v k g) (label (reading v k g*U))) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*U) : ℝ)+1/8)
      rw [hO]
      have hc : ¬InWay (reading v k i) R := not_lt.mpr
        ((isolatedAt_iff_lonelyAt v k R).1 hclear _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩))
      have hlo : (label (reading v k i*R) : ℝ)+1/8 ≤ reading v k i*R :=
        le_of_not_gt (fun hh=>hc ((inWay_iff_lower_not_passed _ _).2 hh))
      have hprod := mul_le_mul_of_nonneg_left hlo hgp.le
      have he := congrArg (fun x : ℝ=>reading v k i*x) hid
      nlinarith only [hprod,he]

-- STANDING: DEFINITION
noncomputable def PrefixRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (I : Finset (Fin 8)) (C : ℝ) (N : ℕ),
    I ⊆ Finset.univ.erase k ∧ I≠Finset.univ.erase k ∧ 0<C ∧ 0<N ∧
    cascadeSeq (part v k I) C (N-1)<cascadeSeq (part v k I) C N ∧
    PrefixFaces (part v k I) (outside v k I) C N ∧
    LonelyAt (part v k I) (cascadeSeq (part v k I) C N) ∧
    (∀ d∈outside v k I,¬InWay d (cascadeSeq (part v k I) C N))

theorem prefixRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : PrefixRecoveryClass v k) :
    CanonicalReturnClass v k := by
  obtain ⟨hv,I,C,N,hI,hproper,hC,hN,hstrict,hfaces,hfixed,houtside⟩ := h
  have hp := part_pos hv k I hI
  have ho := outside_pos hv k I
  have hlast : N-1+1=N := by omega
  have hm := cascadeSeq_isMove (part v k I) C (N-1)
  rw [hlast] at hm
  have hflast := hfaces (N-1) (by omega)
  rw [hlast] at hflast
  have hfull := (union_move_iff hp ho _ _ hm).2 hflast
  rw [part_union_outside v k I hI] at hfull
  have hstart := start_le_seq hp (cascadeSeq_isMove (part v k I) C) (N-1)
  have hU : 0<cascadeSeq (part v k I) C (N-1) := lt_of_lt_of_le hC (by simpa only [cascadeSeq_zero] using hstart)
  have hclear : LonelyAt (disparitySet v k) (cascadeSeq (part v k I) C N) := by
    rw [←part_union_outside v k I hI]
    intro d hd
    rcases Finset.mem_union.mp hd with hd|hd
    · exact hfixed d hd
    · exact not_lt.mp (houtside d hd)
  exact canonical_of_isolating_move hv k _ _ hU hstrict hfull ((isolatedAt_iff_lonelyAt v k _).2 hclear)

theorem prefixRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : PrefixRecoveryClass v k) : Isolation v k :=
  canonical_isolation (prefixRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ClosingGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (I : Finset (Fin 8)) (C : ℝ) (N : ℕ) (a : ℝ),
    I ⊆ Finset.univ.erase k ∧ I≠Finset.univ.erase k ∧ 0<C ∧ 0<N ∧
    cascadeSeq (part v k I) C (N-1)<cascadeSeq (part v k I) C N ∧
    LonelyAt (part v k I) (cascadeSeq (part v k I) C N) ∧ a∈outside v k I ∧
    (∀ s∈outside v k I,¬InWay s C) ∧ (∀ s∈outside v k I,closing a C ≤ closing s C) ∧
    cascadeSeq (part v k I) C N ≤ closing a C

theorem closingGuard_into_prefixRecovery {v : Fin 8 → ℝ} {k : Fin 8} (h : ClosingGuardClass v k) :
    PrefixRecoveryClass v k := by
  obtain ⟨hv,I,C,N,a,hI,hproper,hC,hN,hstrict,hfixed,ha,hclear,hfirst,hfit⟩ := h
  have hp := part_pos hv k I hI
  have ho := outside_pos hv k I
  have hb := earliest_closing_implies_band ho C N a ha hclear hfirst hfit
  exact ⟨hv,I,C,N,hI,hproper,hC,hN,hstrict,band_implies_faces hp ho C N hb,hfixed,
    fun d hd=>(band_keeps_supplied_states hp ho C N hb N le_rfl d hd).1⟩

theorem closingGuard_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ClosingGuardClass v k) : Isolation v k :=
  prefixRecovery_isolation (closingGuard_into_prefixRecovery h)

-- A continuum of physical replacements is retained across a supplied history.
-- STANDING: DEFINITION
noncomputable def TailIntervalClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a : Fin 8) (C lo hi : ℝ) (K : ℤ) (N : ℕ),
    a≠k ∧ 0<C ∧ 0<lo ∧ lo ≤ reading v k a ∧ reading v k a ≤ hi ∧ 0<N ∧
    cascadeSeq (others v k a) C (N-1)<cascadeSeq (others v k a) C N ∧
    LonelyAt (others v k a) (cascadeSeq (others v k a) C N) ∧
    (K : ℝ)+1/8 ≤ lo*C ∧ hi*cascadeSeq (others v k a) C N ≤ (K : ℝ)+7/8

theorem erased_outside (v : Fin 8 → ℝ) (k a : Fin 8) (ha : a≠k) :
    outside v k ((Finset.univ.erase k).erase a)={reading v k a} := by
  have hh : (Finset.univ.erase k)\((Finset.univ.erase k).erase a)={a} := by
    ext i
    by_cases he : i=a
    · subst i; simp [ha]
    · simp [he]
  dsimp [outside]
  rw [hh]
  simp

theorem tailInterval_into_prefixRecovery {v : Fin 8 → ℝ} {k : Fin 8} (h : TailIntervalClass v k) :
    PrefixRecoveryClass v k := by
  obtain ⟨hv,a,C,lo,hi,K,N,ha,hC,hlo,hls,hsh,hN,hstrict,hfixed,hlower,hupper⟩ := h
  let I := (Finset.univ.erase k).erase a
  have hI : I ⊆ Finset.univ.erase k := Finset.erase_subset _ _
  have hproper : I≠Finset.univ.erase k := by
    intro he
    have hm : a∈I := he.symm ▸ Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩
    exact (Finset.mem_erase.mp hm).1 rfl
  have hpart : part v k I=others v k a := rfl
  have hout : outside v k I={reading v k a} := erased_outside v k a ha
  have hp := others_pos hv k a
  have hs := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hstart : C ≤ cascadeSeq (others v k a) C N := by
    simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove (others v k a) C) N
  have hb := interval_singleton_band lo (reading v k a) hi C N K hlo hls hsh hC.le hlower hupper hstart
  have hsingle : ∀ d∈({reading v k a} : Finset ℝ),0<d := by simpa only [Finset.mem_singleton] using fun d (he : d=reading v k a)=>he ▸ hs
  refine ⟨hv,I,C,N,hI,hproper,hC,hN,?_,?_,?_,?_⟩
  · simpa only [hpart] using hstrict
  · simpa only [hpart,hout] using band_implies_faces hp hsingle C N hb
  · simpa only [hpart] using hfixed
  · simpa only [hpart,hout] using fun d hd=>(band_keeps_supplied_states hp hsingle C N hb N le_rfl d hd).1

theorem tailInterval_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : TailIntervalClass v k) : Isolation v k :=
  prefixRecovery_isolation (tailInterval_into_prefixRecovery h)

-- The changed reader may enter at the fixed prefix endpoint. Its own
-- following opening then fits the first remaining FIXED closing boundary.
-- STANDING: DEFINITION
noncomputable def TerminalIntervalClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a : Fin 8) (C lo hi : ℝ) (L : ℤ) (N : ℕ) (f : ℝ),
    a≠k ∧ 0<C ∧ 0<lo ∧ lo ≤ reading v k a ∧ reading v k a ≤ hi ∧ 0<N ∧
    cascadeSeq (others v k a) C (N-1)<cascadeSeq (others v k a) C N ∧
    LonelyAt (others v k a) (cascadeSeq (others v k a) C N) ∧
    PrefixFaces (others v k a) {lo} C N ∧
    (∀ j : ℕ,j<N → label (lo*cascadeSeq (others v k a) C j)=label (hi*cascadeSeq (others v k a) C j)) ∧
    label (lo*cascadeSeq (others v k a) C N)=L ∧ label (hi*cascadeSeq (others v k a) C N)=L ∧
    InWay hi (cascadeSeq (others v k a) C N) ∧ f∈others v k a ∧
    (∀ d∈others v k a,closing f (cascadeSeq (others v k a) C N) ≤ closing d (cascadeSeq (others v k a) C N)) ∧
    opening lo L ≤ closing f (cascadeSeq (others v k a) C N)

theorem terminalInterval_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : TerminalIntervalClass v k) :
    Fresh.NativeCapturedPartnerJoin.PartnerClass v k := by
  obtain ⟨hv,a,C,lo,hi,L,N,f,ha,hC,hlo,hls,hsh,hN,hstrict,hfixed,hfacesLo,hrecords,hlabelLo,hlabelHi,hwHi,hf,hfirst,hfit⟩ := h
  have hp := others_pos hv k a
  have hs : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hsingle : ∀ d∈({reading v k a} : Finset ℝ),0<d := by
    intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact hs
  have hfaces := interval_prefix_faces hp lo (reading v k a) hi C N hC.le hls hsh hrecords hfacesLo
  have hlast : N-1+1=N := by omega
  have hm := cascadeSeq_isMove (others v k a) C (N-1)
  rw [hlast] at hm
  have hflast := hfaces (N-1) (by omega)
  rw [hlast] at hflast
  have hfull := (union_move_iff hp hsingle _ _ hm).2 hflast
  rw [Finset.union_singleton,insert_others v k a ha] at hfull
  have hmono := native_seq_monotone hp C
  have hstart : C ≤ cascadeSeq (others v k a) C (N-1) := by
    simpa only [cascadeSeq_zero] using hmono (Nat.zero_le (N-1))
  have hR : 0<cascadeSeq (others v k a) C N :=
    lt_of_lt_of_le hC (by simpa only [cascadeSeq_zero] using hmono (Nat.zero_le N))
  have hw := speed_interval_capture lo (reading v k a) hi _ hls hsh hR.le (hlabelLo.trans hlabelHi.symm) hwHi
  have hlabel := (speed_interval_label lo (reading v k a) hi _ hls hsh hR.le (hlabelLo.trans hlabelHi.symm)).trans hlabelLo
  have hL0 := positive_entry_label lo _ hlo hR
  rw [hlabelLo] at hL0
  have hLR : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL0
  have hO : opening (reading v k a) L ≤ opening lo L :=
    div_le_div_of_nonneg_left (by linarith only [hLR]) hlo hls
  apply sole_capture_fits_partner hv k a _ _ (lt_of_lt_of_le hC hstart) ha hfull hw
  · intro i hik hia
    exact not_lt.mpr (hfixed _ (Finset.mem_image.mpr ⟨i,
      Finset.mem_erase.mpr ⟨hia,Finset.mem_erase.mpr ⟨hik,Finset.mem_univ _⟩⟩,rfl⟩))
  · intro i hik hia
    have hmem : reading v k i∈others v k a := Finset.mem_image.mpr ⟨i,
      Finset.mem_erase.mpr ⟨hia,Finset.mem_erase.mpr ⟨hik,Finset.mem_univ _⟩⟩,rfl⟩
    change opening (reading v k a) (label (reading v k a*cascadeSeq (others v k a) C N)) ≤ _
    rw [hlabel]
    exact le_trans hO (le_trans hfit (hfirst _ hmem))

theorem terminalInterval_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : TerminalIntervalClass v k) : Isolation v k :=
  Fresh.NativeCapturedPartnerJoin.partner_isolation (terminalInterval_into_partner h)

#print axioms part_pos
#print axioms outside_pos
#print axioms part_union_outside
#print axioms prefix_endpoint_captures_outside
#print axioms canonical_of_isolating_move
#print axioms prefixRecovery_into_canonical
#print axioms prefixRecovery_isolation
#print axioms closingGuard_into_prefixRecovery
#print axioms closingGuard_isolation
#print axioms erased_outside
#print axioms tailInterval_into_prefixRecovery
#print axioms tailInterval_isolation
#print axioms terminalInterval_into_partner
#print axioms terminalInterval_isolation
end Fresh.NativeFixedPrefixArrangement
