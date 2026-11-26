import Fresh.NativeWitnessPacketReentry
import Fresh.NativeOpeningRecovery
import Fresh.NativeFixedPrefixTransport

/-! Whole packet clearance from exact extreme-reader boundary faces.
A common input label needs one fastest upper face for retention. A supplied
terminal window needs only its slowest lower and fastest upper faces.
No endpoint clearance of every packet member is assumed. -/
namespace Fresh.NativePacketExtremeRecovery
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeCanonicalReturn
  Fresh.NativeOpeningRecovery Fresh.NativeFixedPrefixTransport
  Fresh.FastestCaptureRetention

theorem clear_labels_equal_of_close (s d T : ℝ)
    (hs : ¬InWay s T) (hd : ¬InWay d T) (hclose : |(s-d)*T| < 1/4) :
    label (s*T)=label (d*T) := by
  have hslo := le_of_not_gt (fun hh=>hs ((inWay_iff_lower_not_passed s T).2 hh))
  have hdlo := le_of_not_gt (fun hh=>hd ((inWay_iff_lower_not_passed d T).2 hh))
  have hsu := ((entry_interval s T _).1 (label_entry s T)).2
  have hdu := ((entry_interval d T _).1 (label_entry d T)).2
  have hc := abs_lt.mp hclose
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt|hgt
  · have hi : label (s*T)+1 ≤ label (d*T) := by omega
    have hr : (label (s*T) : ℝ)+1 ≤ (label (d*T) : ℝ) := by exact_mod_cast hi
    nlinarith only [hsu,hdlo,hr,hc.1]
  · have hi : label (d*T)+1 ≤ label (s*T) := by omega
    have hr : (label (d*T) : ℝ)+1 ≤ (label (s*T) : ℝ) := by exact_mod_cast hi
    nlinarith only [hdu,hslo,hr,hc.2]

theorem extreme_window (p s q T : ℝ) (J : ℤ) (hT : 0 ≤ T)
    (hps : p ≤ s) (hsq : s ≤ q)
    (hl : (J : ℝ)+1/8 ≤ p*T) (hu : q*T ≤ (J : ℝ)+7/8) :
    (J : ℝ)+1/8 ≤ s*T ∧ s*T ≤ (J : ℝ)+7/8 :=
  ⟨hl.trans (mul_le_mul_of_nonneg_right hps hT),
    (mul_le_mul_of_nonneg_right hsq hT).trans hu⟩

theorem clear_between_close_extremes (p s q T : ℝ) (hT : 0 ≤ T)
    (hps : p ≤ s) (hsq : s ≤ q) (hp : ¬InWay p T) (hq : ¬InWay q T)
    (hspread : |(p-q)*T| < 1/4) :
    ¬InWay s T ∧ label (s*T)=label (p*T) := by
  have he := clear_labels_equal_of_close p q T hp hq hspread
  have hlo := le_of_not_gt (fun hh=>hp ((inWay_iff_lower_not_passed p T).2 hh))
  have hu := ((entry_interval q T _).1 (label_entry q T)).2
  rw [←he] at hu
  have hw := extreme_window p s q T _ hT hps hsq hlo hu
  exact ⟨not_lt.mpr (clear_of_window _ hw.1 hw.2),(entry_iff_label s T _).1 (Or.inl hw)⟩

theorem packet_zero_iff_fastest {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (S T : ℝ) (I : Finset (Fin 8)) (f : Fin 8)
    (hI : I ⊆ Finset.univ.erase k) (hf : f∈I) (hS : 0 < S) (hST : S ≤ T)
    (hmax : ∀ i∈I, reading v k i ≤ reading v k f)
    (hl : ∀ i∈I, label (reading v k i*S)=label (reading v k f*S)) :
    (∀ i∈I, advance (reading v k i) S T=0) ↔
      reading v k f*T ≤ (label (reading v k f*S) : ℝ)+7/8 := by
  have hfk : f≠k := (Finset.mem_erase.mp (hI hf)).1
  have hfp : 0 < reading v k f := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨f,hfk,rfl⟩)
  constructor
  · intro hz
    exact (zero_iff_original_upper _ S T hfp.le hST).1 (hz f hf)
  · intro hu i hi
    apply (zero_iff_original_upper _ S T (abs_nonneg _) hST).2
    change reading v k i*T ≤ (label (reading v k i*S) : ℝ)+7/8
    rw [hl i hi]
    exact (mul_le_mul_of_nonneg_right (hmax i hi) (hS.le.trans hST)).trans hu

theorem fastest_retained_packet {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (S T : ℝ) (I : Finset (Fin 8)) (f : Fin 8)
    (hI : I ⊆ Finset.univ.erase k) (hf : f∈I) (hS : 0 < S)
    (hm : IsMove (disparitySet v k) S T)
    (hmax : ∀ i∈I, reading v k i ≤ reading v k f)
    (hl : ∀ i∈I, label (reading v k i*S)=label (reading v k f*S))
    (hu : reading v k f*T ≤ (label (reading v k f*S) : ℝ)+7/8) :
    ∀ i∈I, ¬InWay (reading v k i) T := by
  have hz := (packet_zero_iff_fastest hv k S T I f hI hf hS
    (le_of_isMove (disparitySet_pos hv k) hm) hmax hl).2 hu
  intro i hi
  exact not_lt.mpr (nonreturning_clear hv k S T hm i (Finset.mem_erase.mp (hI hi)).1 (hz i hi))

theorem extreme_opening_window (d p s q T : ℝ) (N J : ℤ)
    (hd : 0 < d) (hT : 0 ≤ T) (ho : d*T=(N : ℝ)+1/8)
    (hps : p ≤ s) (hsq : s ≤ q)
    (hl : d*((J : ℝ)+1/8) ≤ p*((N : ℝ)+1/8))
    (hu : q*((N : ℝ)+1/8) ≤ d*((J : ℝ)+7/8)) :
    ¬InWay s T ∧ label (s*T)=J := by
  have hp := opening_order_lower d p T N J hd ho hl
  have hq := opening_order_upper d q T N J hd ho hu
  have hw := extreme_window p s q T J hT hps hsq hp hq
  exact ⟨not_lt.mpr (clear_of_window J hw.1 hw.2),(entry_iff_label s T J).1 (Or.inl hw)⟩

-- STANDING: DEFINITION
noncomputable def ExtremeClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (S : ℝ) (a p q : Fin 8) (I : Finset (Fin 8)) (J : ℤ),
    0 < S ∧ a≠k ∧ InWay (reading v k a) S ∧
    IsMove (disparitySet v k) S (handoffOpening v k S a) ∧
    I ⊆ Finset.univ.erase k ∧ p∈I ∧ q∈I ∧
    (∀ i∈I, reading v k p ≤ reading v k i ∧ reading v k i ≤ reading v k q) ∧
    reading v k a*((J : ℝ)+1/8) ≤ reading v k p*((label (reading v k a*S) : ℝ)+1/8) ∧
    reading v k q*((label (reading v k a*S) : ℝ)+1/8) ≤ reading v k a*((J : ℝ)+7/8) ∧
    (∀ i : Fin 8, i≠k → i∉I → 0 < advance (reading v k i) S (handoffOpening v k S a) →
      reading v k a*((label (reading v k i*handoffOpening v k S a) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k a*S) : ℝ)+1/8))

theorem extreme_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ExtremeClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,S,a,p,q,I,J,hS,ha,hwa,hm,hI,hp,hq,hbounds,hl,hu,hout⟩ := h
  have hd : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hST := le_of_isMove (disparitySet_pos hv k) hm
  have hc := capture_at_label (reading v k a) S hwa
  refine ⟨hv,a,S,label (reading v k a*S),ha,hS,hc.1,hc.2,hm,?_⟩
  intro i hi hadv
  change reading v k a*((label (reading v k i*handoffOpening v k S a) : ℝ)+1/8) ≤
    reading v k i*((label (reading v k a*S) : ℝ)+1/8)
  by_cases him : i∈I
  · have hh := extreme_opening_window (reading v k a) (reading v k p) (reading v k i)
      (reading v k q) _ _ J hd (hS.le.trans hST) (handoff_identity hv k a S ha)
      (hbounds i him).1 (hbounds i him).2 hl hu
    have hlow : (label (reading v k i*handoffOpening v k S a) : ℝ)+1/8 ≤
        reading v k i*handoffOpening v k S a := by
      exact le_of_not_gt (fun hn=>hh.1 ((inWay_iff_lower_not_passed _ _).2 hn))
    have hscaled := mul_le_mul_of_nonneg_left hlow hd.le
    calc
      _ ≤ reading v k a*(reading v k i*handoffOpening v k S a) := hscaled
      _ = reading v k i*(reading v k a*handoffOpening v k S a) := by ring
      _ = _ := by rw [handoff_identity hv k a S ha]
  · exact hout i hi him hadv

theorem extreme_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ExtremeClass v k) : Isolation v k := canonical_isolation (extreme_into_canonical h)

#print axioms clear_labels_equal_of_close
#print axioms extreme_window
#print axioms clear_between_close_extremes
#print axioms packet_zero_iff_fastest
#print axioms fastest_retained_packet
#print axioms extreme_opening_window
#print axioms extreme_into_canonical
#print axioms extreme_isolation
end Fresh.NativePacketExtremeRecovery
