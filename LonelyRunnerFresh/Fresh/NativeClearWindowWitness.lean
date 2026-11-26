import Fresh.NativeWitnessPacketReentry

/-! A common CLEAR integer window witnesses persistent packet ratios.
The first positive label clears a current capture in one selected opening;
labels at least two also force the existing two-opening packet face. Closed
window edges are included and future labels/advances remain independent. -/
namespace Fresh.NativeClearWindowWitness
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeCurrentLabelPacket Fresh.NativeCapturedPartnerJoin
  Fresh.NativeReturnClosingOrder Fresh.NativeTwoSetterPacket Fresh.FastestCaptureRetention
  Fresh.NativeReturnLevelClearance

theorem clear_window (d P : ℝ) (N : ℤ) (hw : ¬InWay d P) (hl : label (d*P)=N) :
    (N : ℝ)+1/8 ≤ d*P ∧ d*P ≤ (N : ℝ)+7/8 := by
  have hlo := le_of_not_gt (fun h=>hw ((inWay_iff_lower_not_passed d P).2 h))
  have hhi := ((entry_interval d P _).1 (label_entry d P)).2
  rw [hl] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem positive_clear_ratio (s d P : ℝ) (N : ℤ) (hP : 0 < P) (hN : 1 ≤ N)
    (hs : (N : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (N : ℝ)+7/8)
    (hd : (N : ℝ)+1/8 ≤ d*P ∧ d*P ≤ (N : ℝ)+7/8) : 3*s ≤ 5*d := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hb : 3*(s*P) ≤ 5*(d*P) := by nlinarith only [hs.2,hd.1,hn]
  by_contra hh
  have hp := mul_pos hP (show 0 < 3*s-5*d by linarith only [hh])
  nlinarith only [hp,hb]

theorem deep_clear_ratio (s d P : ℝ) (N : ℤ) (hP : 0 < P) (hN : 2 ≤ N)
    (hs : (N : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (N : ℝ)+7/8)
    (hd : (N : ℝ)+1/8 ≤ d*P ∧ d*P ≤ (N : ℝ)+7/8) : 17*s ≤ 23*d := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hb : 17*(s*P) ≤ 23*(d*P) := by nlinarith only [hs.2,hd.1,hn]
  by_contra hh
  have hp := mul_pos hP (show 0 < 17*s-23*d by linarith only [hh])
  nlinarith only [hp,hb]

-- STANDING: DEFINITION
noncomputable def Witness (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (I : Finset (Fin 8)) (N : ℤ) : Prop :=
  0 < P ∧ I ⊆ Finset.univ.erase k ∧ 1 ≤ N ∧
    ∀ i∈I, ¬InWay (reading v k i) P ∧ label (reading v k i*P)=N

theorem pair_ratio {v : Fin 8 → ℝ} {k i g : Fin 8} {P : ℝ} {I : Finset (Fin 8)} {N : ℤ}
    (h : Witness v k P I N) (hi : i∈I) (hg : g∈I) : 3*reading v k i ≤ 5*reading v k g := by
  obtain ⟨hp,hI,hN,hlabels⟩ := h
  exact positive_clear_ratio _ _ P N hp hN
    (clear_window _ P N (hlabels i hi).1 (hlabels i hi).2)
    (clear_window _ P N (hlabels g hg).1 (hlabels g hg).2)

theorem pair_deep_ratio {v : Fin 8 → ℝ} {k i g : Fin 8} {P : ℝ} {I : Finset (Fin 8)} {N : ℤ}
    (h : Witness v k P I N) (hN : 2 ≤ N) (hi : i∈I) (hg : g∈I) :
    17*reading v k i ≤ 23*reading v k g := by
  exact deep_clear_ratio _ _ P N h.1 hN
    (clear_window _ P N (h.2.2.2 i hi).1 (h.2.2.2 i hi).2)
    (clear_window _ P N (h.2.2.2 g hg).1 (h.2.2.2 g hg).2)

theorem member_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g : Fin 8) (hg : g∈I) (hwg : InWay (reading v k g) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i∈I) (hwi : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 := by
  have hik : i≠k := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hgk : g≠k := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  change 0 < reading v k g at hp
  have hr := pair_ratio h hi hg
  exact captured_ratio_zero hv k R i g hik hgk hwi hwg (by nlinarith only [hr,hp]) hm

theorem member_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N)
    (g : Fin 8) (hg : g∈I) (hwg : InWay (reading v k g) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i∈I) (hwi : InWay (reading v k i) R) :
    ¬InWay (reading v k i) (handoffOpening v k R g) := by
  exact not_lt.mpr (nonreturning_clear hv k R _ hm i (Finset.mem_erase.mp (h.2.1 hi)).1
    (member_zero hv k P R I N h g hg hwg hm i hi hwi))

theorem two_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N) (hN : 2 ≤ N)
    (i g j : Fin 8) (hi : i∈I) (hg : g∈I) (hj : j∈I) :
    reading v k i*(reading v k g+reading v k j) ≤ 3*reading v k g*reading v k j := by
  have hgk : g≠k := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk : j≠k := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hq := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  change 0 < reading v k g at hp
  change 0 < reading v k j at hq
  have h1 := mul_le_mul_of_nonneg_right (pair_deep_ratio h hN hi hg) hq.le
  have h2 := mul_le_mul_of_nonneg_right (pair_deep_ratio h hN hi hj) hp.le
  have hprod := mul_pos hp hq
  nlinarith only [h1,h2,hprod]

theorem two_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N) (hN : 2 ≤ N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 ∧
      advance (reading v k i) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j)=0 := by
  exact two_setter_zero_split hv k R g j i
    (Finset.mem_erase.mp (h.2.1 hg)).1 (Finset.mem_erase.mp (h.2.1 hj)).1
    (Finset.mem_erase.mp (h.2.1 hi)).1 hwg hm1 hwj hm2 hwi (two_face hv k P I N h hN i g j hi hg hj)

theorem two_capture_fresh {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (h : Witness v k P I N) (hN : 2 ≤ N)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R) (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hafter : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    ¬InWay (reading v k i) R ∧ ¬InWay (reading v k i) (handoffOpening v k R g) := by
  constructor
  · intro hw
    have hz := (two_zero hv k P R I N h hN g j i hg hj hi hwg hm1 hwj hm2 hw).2
    exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i (Finset.mem_erase.mp (h.2.1 hi)).1 hz) hafter
  · intro hw
    exact member_clear hv k P _ I N h j hj hwj hm2 i hi hw hafter

#print axioms clear_window
#print axioms positive_clear_ratio
#print axioms deep_clear_ratio
#print axioms pair_ratio
#print axioms pair_deep_ratio
#print axioms member_zero
#print axioms member_clear
#print axioms two_face
#print axioms two_zero
#print axioms two_capture_fresh
end Fresh.NativeClearWindowWitness
