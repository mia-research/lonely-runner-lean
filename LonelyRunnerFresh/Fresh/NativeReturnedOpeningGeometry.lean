import Fresh.NativeClearWindowRebound

/-! Local returned-opening geometry. A coincident CURRENT opening is
stronger than an arbitrary later lower-boundary residue. No bound on the
number of returns or on a full cascade is asserted. -/
namespace Fresh.NativeReturnedOpeningGeometry
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeClearWindowWitness
  Fresh.NativeClearWindowRebound Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention

theorem return_tail (s U V : ℝ) (K : ℤ)
    (hu : s*U < (K : ℝ)+23/24) (ho : s*V=(K : ℝ)+1+1/8) :
    1/6 < s*(V-U) := by nlinarith only [hu,ho]

theorem coincident_capture_compact (s q U : ℝ) (hq : 0<q)
    (htail : 1/6 < s*(labelledOpening s U-U))
    (hw : InWay q U) (htie : labelledOpening q U=labelledOpening s U) :
    2*q < 3*s := by
  have hd := captured_labelled_advance q U hq hw
  rw [htie] at hd
  have h1 := mul_lt_mul_of_pos_left htail hq
  have h2 := mul_lt_mul_of_pos_left hd.2 (show 0<s by
    have hp := hd.1
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hp.le
    linarith only [hh,htail])
  nlinarith only [h1,h2]

theorem old_return_tail {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R)
    (hret : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    1/6 < reading v k i*(handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i-
      handoffOpening v k (handoffOpening v k R g) j) := by
  have hik := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hup := old_two_phase_upper hv k P R I N h g j i hg hj hi hwg hwj hwi
  have ha := (old_return_iff hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hwi).1 hret
  have hone := old_return_one hv k P R I N h g j i hg hj hi hwg hm1 hwj hm2 hwi ha
  have hid := advance_identity (reading v k i) R _ (show 0≤reading v k i from abs_nonneg _)
    ((le_of_isMove (disparitySet_pos hv k) hm1).trans (le_of_isMove (disparitySet_pos hv k) hm2))
  rw [hone] at hid
  have hl : (label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)=
      (label (reading v k i*R) : ℝ)+1 := by exact_mod_cast hid
  have ho := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hik
  rw [hl] at ho
  exact return_tail _ _ _ _ hup ho

#print axioms return_tail
#print axioms coincident_capture_compact
#print axioms old_return_tail
end Fresh.NativeReturnedOpeningGeometry
