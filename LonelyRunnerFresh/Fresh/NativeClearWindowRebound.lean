import Fresh.NativeClearWindowWitness
import Fresh.NativeWatcherPacketReturn

/-! An old clear-window packet capture that returns after two selections
forces a strictly faster local handoff. No global speed descent or bound on
moves is inferred. The returned reader clears the previously selected core. -/
namespace Fresh.NativeClearWindowRebound
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeClearWindowWitness
  Fresh.NativeTwoSetterPacket Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.FastestCaptureRetention Fresh.NativeCoalescedCaptureRelay

-- Below one selected disparity, the positive clear-window ratio forces
-- the native two-setter face even at reference label one.
theorem below_selected_face (s g j : ℝ) (hg : 0 < g) (hj : 0 < j)
    (hrgj : 3*g ≤ 5*j) (hrjg : 3*j ≤ 5*g) (hs : s ≤ g ∨ s ≤ j) :
    s*(g+j) ≤ 3*g*j := by
  rcases hs with hs|hs
  · have hm := mul_le_mul_of_nonneg_right hs (add_pos hg hj).le
    have ht := mul_le_mul_of_nonneg_left (show g ≤ 2*j by linarith only [hrgj,hj]) hg.le
    nlinarith only [hm,ht]
  · have hm := mul_le_mul_of_nonneg_right hs (add_pos hg hj).le
    have ht := mul_le_mul_of_nonneg_left (show j ≤ 2*g by linarith only [hrjg,hg]) hj.le
    nlinarith only [hm,ht]

theorem old_two_phase_upper {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R)
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hwi : InWay (reading v k i) R) :
    reading v k i*handoffOpening v k (handoffOpening v k R g) j <
      (label (reading v k i*R) : ℝ)+23/24 := by
  have hgk := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have ht := captured_labelled_advance (reading v k g) R hgp hwg
  have hu := captured_labelled_advance (reading v k j) (handoffOpening v k R g) hjp hwj
  change 0 < handoffOpening v k R g-R ∧ reading v k g*(handoffOpening v k R g-R) < 1/4 at ht
  change 0 < handoffOpening v k (handoffOpening v k R g) j-handoffOpening v k R g ∧
    reading v k j*(handoffOpening v k (handoffOpening v k R g) j-handoffOpening v k R g) < 1/4 at hu
  have h1 := mul_le_mul_of_nonneg_right (pair_ratio h hi hg) ht.1.le
  have h2 := mul_le_mul_of_nonneg_right (pair_ratio h hi hj) hu.1.le
  have he := (capture_at_label (reading v k i) R hwi).2
  nlinarith only [h1,h2,ht.2,hu.2,he]

theorem old_return_capture {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (ha : 0 < advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j)) :
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) := by
  have hi0 := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hip : 0 ≤ reading v k i := (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi0,rfl⟩)).le
  have hRU := (le_of_isMove (disparitySet_pos hv k) hm1).trans (le_of_isMove (disparitySet_pos hv k) hm2)
  have hid := advance_identity (reading v k i) R _ hip hRU
  have hidR : (label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)=
      (label (reading v k i*R) : ℝ)+(advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) : ℝ) := by exact_mod_cast hid
  have har : (1 : ℝ) ≤ (advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) : ℝ) := by exact_mod_cast ha
  have hu := old_two_phase_upper hv k P R I N h g j i hg hj hi hwg hwj hwi
  apply (inWay_iff_lower_not_passed _ _).2
  rw [hidR]
  linarith only [hu,har]

theorem old_return_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R) :
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ↔
      0 < advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) := by
  constructor
  · intro hret
    have hik := (Finset.mem_erase.mp (h.2.1 hi)).1
    have ha := captured_implies_return hv k _ _ hm2 i hik hret
    change 0 < advance (reading v k i) (handoffOpening v k R g)
      (handoffOpening v k (handoffOpening v k R g) j) at ha
    have hz := member_zero hv k P R I N h g hg hwg hm1 i hi hwi
    have hadd := advance_add (reading v k i) R (handoffOpening v k R g) _
      (show 0 ≤ reading v k i from abs_nonneg _)
      (le_of_isMove (disparitySet_pos hv k) hm1) (le_of_isMove (disparitySet_pos hv k) hm2)
    omega
  · exact fun ha=>old_return_capture hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hwi ha

theorem old_return_one {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (ha : 0 < advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j)) :
    advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j)=1 := by
  have hu := old_two_phase_upper hv k P R I N h g j i hg hj hi hwg hwj hwi
  have hc := old_return_capture hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hwi ha
  have hl := (capture_at_label (reading v k i) _ hc).1
  have hi0 := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hp : 0 ≤ reading v k i := (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi0,rfl⟩)).le
  have hid := advance_identity (reading v k i) R _ hp
    ((le_of_isMove (disparitySet_pos hv k) hm1).trans (le_of_isMove (disparitySet_pos hv k) hm2))
  have hidR : (label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)=
      (label (reading v k i*R) : ℝ)+(advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) : ℝ) := by exact_mod_cast hid
  rw [hidR] at hl
  have hlt : advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) < 2 := by
    by_contra hn
    have hh : (2 : ℝ) ≤ (advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j) : ℝ) := by exact_mod_cast (le_of_not_gt hn)
    linarith only [hu,hl,hh]
  omega

theorem recapture_forces_largest {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    reading v k g < reading v k i ∧ reading v k j < reading v k i := by
  have hgk := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hik := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have no : ¬(reading v k i ≤ reading v k g ∨ reading v k i ≤ reading v k j) := by
    intro hs
    have hf := below_selected_face _ _ _ hgp hjp (pair_ratio h hg hj) (pair_ratio h hj hg) hs
    have hz := (two_setter_zero_split hv k R g j i hgk hjk hik hwg hm1 hwj hm2 hwi hf).2
    exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i hik hz) hret
  exact ⟨lt_of_not_ge (fun hh=>no (Or.inl hh)),lt_of_not_ge (fun hh=>no (Or.inr hh))⟩

theorem recapture_forces_outer_band {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    (3*reading v k g < 2*reading v k i ∧ 3*reading v k i ≤ 5*reading v k g) ∨
      (3*reading v k j < 2*reading v k i ∧ 3*reading v k i ≤ 5*reading v k j) := by
  have hgk := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hik := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hf : 3*reading v k g*reading v k j < reading v k i*(reading v k g+reading v k j) := by
    by_contra hn
    have hz := (two_setter_zero_split hv k R g j i hgk hjk hik hwg hm1 hwj hm2 hwi (le_of_not_gt hn)).2
    exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i hik hz) hret
  have hor : 3*reading v k g < 2*reading v k i ∨ 3*reading v k j < 2*reading v k i := by
    by_contra hn
    push Not at hn
    have h1 := mul_le_mul_of_nonneg_right hn.1 hjp.le
    have h2 := mul_le_mul_of_nonneg_right hn.2 hgp.le
    nlinarith only [hf,h1,h2]
  rcases hor with hh|hh
  · exact Or.inl ⟨hh,pair_ratio h hi hg⟩
  · exact Or.inr ⟨hh,pair_ratio h hi hj⟩

theorem recapture_forces_reference_one {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) : N=1 := by
  by_contra hn
  have hN : 2 ≤ N := by have hh := h.2.2.1; omega
  have hz := (two_zero hv k P R I N h hN g j i hg hj hi hwg hm1 hwj hm2 hwi).2
  exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i (Finset.mem_erase.mp (h.2.1 hi)).1 hz) hret

theorem next_capture_split {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    ¬InWay (reading v k i) (handoffOpening v k R g) ∧
      (¬InWay (reading v k i) R ∨
        (N=1 ∧ reading v k g < reading v k i ∧ reading v k j < reading v k i ∧
          advance (reading v k i) R (handoffOpening v k (handoffOpening v k R g) j)=1)) := by
  refine ⟨fun hw=>member_clear hv k P _ I N h j hj hwj hm2 i hi hw hret,?_⟩
  by_cases hold : InWay (reading v k i) R
  · have hb := recapture_forces_largest hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hold hret
    have ha := (old_return_iff hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hold).1 hret
    exact Or.inr ⟨recapture_forces_reference_one hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hold hret,
      hb.1,hb.2,old_return_one hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hold ha⟩
  · exact Or.inl hold

-- Every packet reader below the returned reader fits the following pair.
theorem rebound_packet_face {v : Fin 8 → ℝ} {k s j i : Fin 8} {P : ℝ}
    {I : Finset (Fin 8)} {N : ℤ} (h : Witness v k P I N)
    (hs : s∈I) (hj : j∈I) (hsp : 0 ≤ reading v k j) (hip : 0 ≤ reading v k i)
    (hsi : reading v k s ≤ reading v k i) :
    reading v k s*(reading v k j+reading v k i) ≤ 3*reading v k j*reading v k i := by
  have h1 := mul_le_mul_of_nonneg_right (pair_ratio h hs hj) hip
  have h2 := mul_le_mul_of_nonneg_right hsi hsp
  have hp := mul_nonneg hsp hip
  nlinarith only [h1,h2,hp]

-- The boundary kernel includes a reader at its own clear lower endpoint;
-- no false "captured at own opening" premise is introduced.
theorem own_two_window (d e s C : ℝ) (M : ℤ) (hd : 0 < d) (he : 0 < e) (hs : 0 < s)
    (ho : s*C=(M : ℝ)+1/8) (hw : InWay d C) (hret : InWay e (labelledOpening d C))
    (hfit : s*(d+e) ≤ 3*d*e) :
    (M : ℝ)+1/8 ≤ s*Fresh.NativeWatcherPacketReturn.returnOpening e d C ∧
      s*Fresh.NativeWatcherPacketReturn.returnOpening e d C < (M : ℝ)+7/8 := by
  have hl := Fresh.NativeCoalescedCaptureRelay.own_opening_labelled s C M hs ho
  have hlabel : label (s*C)=M := by
    have hh := (entry_iff_label s C M).1 (Or.inl ⟨ho.ge,by linarith only [ho]⟩)
    exact hh
  have hdelta := (captured_labelled_advance d C hd hw).2
  have h1 := mul_lt_mul_of_pos_left hdelta he
  have h2 := mul_lt_mul_of_pos_left h1 hs
  have hid := labelled_opening_identity d C hd
  have hface : Fresh.NativeWatcherPacketReturn.boundaryFace e d s C := by
    unfold Fresh.NativeWatcherPacketReturn.boundaryFace
    rw [hlabel]
    have hgap : (M : ℝ)+7/8-s*C=3/4 := by linarith only [ho]
    rw [hgap]
    have hx : (label (d*C) : ℝ)+1/8-d*C=d*(labelledOpening d C-C) := by nlinarith only [hid]
    rw [hx]
    nlinarith only [h2,hfit]
  have horder : labelledOpening s C ≤ labelledOpening d C := by
    rw [hl]
    exact le_of_lt (by have hh := (captured_labelled_advance d C hd hw).1; linarith only [hh])
  have hh := Fresh.NativeWatcherPacketReturn.boundary_packet_window e d s C he hd hs hw hret horder hface
  simpa only [hlabel] using hh

theorem returned_core_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    LonelyAt ({reading v k g,reading v k j,reading v k i} : Finset ℝ)
      (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i) := by
  have hgk := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hik := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩)
  have hbig := recapture_forces_largest hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hwi hret
  have hgown := handoff_identity hv k g R hgk
  have hjown := handoff_identity hv k j (handoffOpening v k R g) hjk
  have hiown := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hik
  have hgclear := own_two_window (reading v k j) (reading v k i) (reading v k g)
    (handoffOpening v k R g) (label (reading v k g*R)) hjp hip hgp hgown hwj hret
    (rebound_packet_face h hg hj hjp.le hip.le hbig.1.le)
  have hjclear := own_opening_retained (reading v k i) (reading v k j)
    (handoffOpening v k (handoffOpening v k R g) j)
    (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i)
    (label (reading v k i*handoffOpening v k (handoffOpening v k R g) j))
    (label (reading v k j*handoffOpening v k R g)) hip hjp.le
    (by linarith only [hbig.2,hip]) hjown hret hiown rfl
  intro d hdmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hdmem
  rcases hdmem with rfl|rfl|rfl
  · exact clear_of_window _ hgclear.1 hgclear.2.le
  · exact clear_of_window _ hjclear.1 hjclear.2.le
  · exact clear_of_window _ hiown.ge (by linarith only [hiown])

#print axioms old_two_phase_upper
#print axioms old_return_capture
#print axioms old_return_iff
#print axioms old_return_one
#print axioms below_selected_face
#print axioms recapture_forces_largest
#print axioms recapture_forces_outer_band
#print axioms recapture_forces_reference_one
#print axioms next_capture_split
#print axioms rebound_packet_face
#print axioms own_two_window
#print axioms returned_core_clear
end Fresh.NativeClearWindowRebound
