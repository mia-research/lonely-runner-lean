import Fresh.NativeReturnGroupArrangement

/-! Crossing one remaining original closing face creates one forced new
returner, provided the displaced phase has not passed its next lower face.
This rejoins the single-return relay mechanism rather than assuming that
the old isolation at the closing face remains at its original location. -/
namespace Fresh.NativeReturnFaceHandoff
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnGroupRelay

noncomputable def FaceEntry (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c a : Fin 8) : Prop :=
  a≠k ∧ advance (reading v k a) P R=0 ∧
    (label (reading v k a*P) : ℝ)+7/8<reading v k a*handoffOpening v k R c ∧
    reading v k a*handoffOpening v k R c<(label (reading v k a*P) : ℝ)+9/8 ∧
    ∀ i : Fin 8, i≠k → i≠a → advance (reading v k i) P R=0 →
      handoffOpening v k R c≤closing (reading v k i) P

theorem crossed_face_label (s T : ℝ) (K : ℤ)
    (hlo : (K : ℝ)+7/8<s*T) (hhi : s*T<(K : ℝ)+9/8) : label (s*T)=K+1 ∧ InWay s T := by
  have he : Fresh.NativeReturnCapture.EntryWindow s T (K+1) := by
    apply (entry_interval _ _ _).2
    push_cast
    constructor <;> linarith only [hlo,hhi]
  refine ⟨(entry_iff_label _ _ _).1 he,?_⟩
  have hn : abs (s*T-((K+1 : ℤ) : ℝ))<1/8 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith only [hlo,hhi]
  exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hn

theorem crossed_face_next (s T : ℝ) (K : ℤ)
    (hlo : (K : ℝ)+7/8<s*T) (hhi : s*T<(K : ℝ)+9/8) :
    nextOpening s T=Fresh.FastestCaptureRetention.opening s (K+1) := by
  have hh := crossed_face_label s T K hlo hhi
  rw [next_at_label s T hh.2,hh.1]

theorem face_return_profile {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hr : Reset v k P R c)
    (hf : FaceEntry v k P R c a) :
    advance (reading v k a) R (handoffOpening v k R c)=1 ∧
      ∀ i : Fin 8, i≠k → i≠a → advance (reading v k i) R (handoffOpening v k R c)=0 := by
  have hPR := le_of_isMove (disparitySet_pos hv k) hm
  have hid := advance_identity (reading v k a) P R (abs_nonneg _) hPR
  simp only [hf.2.1,Nat.cast_zero,add_zero] at hid
  have hlabel := (crossed_face_label (reading v k a) _ (label (reading v k a*P)) hf.2.2.1 hf.2.2.2.1).1
  refine ⟨?_,?_⟩
  · simp only [advance,hlabel,hid]
    omega
  · intro i hi hia
    by_contra hn
    have hpos : 0 < advance (reading v k i) R (handoffOpening v k R c) := by omega
    have hh := (reset_return_iff hv k P R hm c hr i hi).1 hpos
    exact not_lt_of_ge (hf.2.2.2.2 i hi hia hh.1) hh.2

theorem face_into_single {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hr : Reset v k P R c)
    (hf : FaceEntry v k P R c a) :
    Fresh.NativeSingleReturnRelay.SingleReturn v k R (handoffOpening v k R c) a := by
  have hp := face_return_profile hv k P R hm c a hr hf
  refine ⟨hf.1,by omega,?_⟩
  intro i hi hpos
  by_cases he : i=a
  · rw [he]
  · have hz := hp.2 i hi he
    omega

theorem face_survivors {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hr : Reset v k P R c)
    (hf : FaceEntry v k P R c a) (i : Fin 8) :
    Survivor v k R (handoffOpening v k R c) i ↔ i=a := by
  have ht := reset_move hv k P R hm c hr
  have hcap := (crossed_face_label (reading v k a) _ (label (reading v k a*P)) hf.2.2.1 hf.2.2.2.1).2
  have hp := face_return_profile hv k P R hm c a hr hf
  constructor
  · intro hs
    by_contra hn
    have hz := hp.2 i hs.1 hn
    have ha := hs.2.1
    omega
  · intro he
    subst i
    exact (survivor_iff hv k R _ ht.2 a).2 ⟨hf.1,hcap⟩

theorem face_forces_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hr : Reset v k P R c)
    (hf : FaceEntry v k P R c a) :
    handoffOpening v k R c<handoffOpening v k (handoffOpening v k R c) a ∧
      IsMove (disparitySet v k) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) a) := by
  have ht := reset_move hv k P R hm c hr
  exact sole_survivor_handoff hv k R _ ht.2 a
    ((face_survivors hv k P R hm c a hr hf a).2 rfl)
    (fun i hi=>(face_survivors hv k P R hm c a hr hf i).1 hi)

theorem face_displaced_opening {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (c a : Fin 8)
    (hf : FaceEntry v k P R c a) :
    handoffOpening v k (handoffOpening v k R c) a=
      Fresh.FastestCaptureRetention.opening (reading v k a) (label (reading v k a*P)+1) := by
  exact congrArg (Fresh.FastestCaptureRetention.opening (reading v k a))
    (crossed_face_label (reading v k a) _ (label (reading v k a*P)) hf.2.2.1 hf.2.2.2.1).1

-- STANDING: DEFINITION
noncomputable def FaceRelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c a : Fin 8), HandoffEntry v k Q P j ∧
    Reset v k P (handoffOpening v k P j) c ∧ FaceEntry v k P (handoffOpening v k P j) c a ∧
      Fresh.NativeSingleReturnRelay.OriginalFits v k (handoffOpening v k P j)
        (handoffOpening v k (handoffOpening v k P j) c) a

theorem face_into_single_relay_class {v : Fin 8 → ℝ} {k : Fin 8} (h : FaceRelayClass v k) :
    Fresh.NativeSingleReturnArrangement.RelayClass v k := by
  obtain ⟨hv,Q,P,j,c,a,he,hr,hf,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hm2 := reset_move hv k P _ ht.2 c hr
  have hsingle := face_into_single hv k P _ ht.2 c a hr hf
  have hcap := (crossed_face_label (reading v k a) _ (label (reading v k a*P)) hf.2.2.1 hf.2.2.2.1).2
  have hP := lt_trans he.1 (predecessor_strict hv k Q P he.2.1 j he.2.2.1)
  exact ⟨hv,P,handoffOpening v k P j,c,a,⟨hP,ht.2,hr.1,hr.2.1⟩,
    (Fresh.NativeSingleReturnRelay.entry_iff_single hv k _ _ hm2.1.le a).2 hsingle,hcap,hfit⟩

theorem face_relay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FaceRelayClass v k) : Isolation v k :=
  Fresh.NativeSingleReturnArrangement.relay_isolation (face_into_single_relay_class h)

#print axioms crossed_face_label
#print axioms crossed_face_next
#print axioms face_return_profile
#print axioms face_into_single
#print axioms face_survivors
#print axioms face_forces_handoff
#print axioms face_displaced_opening
#print axioms face_into_single_relay_class
#print axioms face_relay_isolation
end Fresh.NativeReturnFaceHandoff
