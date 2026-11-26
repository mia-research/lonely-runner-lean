import Fresh.NativeFirstClosing

/-! Native original-window and independent-return capture families. One
first-closing boundary supplies every upper face; original retained or
captured entry bands supply zero-return lower faces. Positive returns keep
an explicit original passed-opening comparison, with no return bound. -/
namespace Fresh.NativeReturnCapture
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FastestCaptureRetention

noncomputable def EntryWindow (s Q : ℝ) (K : ℤ) : Prop :=
  ((K : ℝ)+1/8 ≤ s*Q ∧ s*Q ≤ (K : ℝ)+7/8) ∨
  ((K : ℝ)-1/8 < s*Q ∧ s*Q < (K : ℝ)+1/8)

def lifted (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) (i : Fin 8) : ℤ := L i+(A i : ℤ)

noncomputable def ReturnFrame (v : Fin 8 → ℝ) (k u c : Fin 8) (Q : ℝ) (N : ℤ)
    (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) : Prop :=
  u≠k ∧ c≠k ∧ L u=N ∧ A u=0 ∧ 0 < Q ∧
  (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
  IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
  (∀ i : Fin 8, i≠k → i≠u → EntryWindow |v i-v k| Q (L i) ∧
    (A i=0 ∨ |v u-v k| * ((lifted L A i : ℝ)+1/8) ≤ |v i-v k| * ((N : ℝ)+1/8))) ∧
  ∀ i : Fin 8, i≠k → |v i-v k| * ((lifted L A c : ℝ)+7/8) ≤
    |v c-v k| * ((lifted L A i : ℝ)+7/8)

noncomputable def SharpFace (v : Fin 8 → ℝ) (k u c : Fin 8) (Q : ℝ) (N : ℤ)
    (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) : Prop :=
  |v c-v k| * ((N : ℝ)+1/8-|v u-v k| * Q) ≤
    |v u-v k| * ((lifted L A c : ℝ)+7/8-|v c-v k| * Q)

noncomputable def QuarterFace (v : Fin 8 → ℝ) (k u c : Fin 8) (Q : ℝ)
    (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) : Prop :=
  |v c-v k|/4 ≤ |v u-v k| * ((lifted L A c : ℝ)+7/8-|v c-v k| * Q)

-- STANDING: DEFINITION
noncomputable def SharpReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u c : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ) (A : Fin 8 → ℕ),
    ReturnFrame v k u c Q N L A ∧ SharpFace v k u c Q N L A

-- STANDING: DEFINITION
noncomputable def QuarterReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u c : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ) (A : Fin 8 → ℕ),
    ReturnFrame v k u c Q N L A ∧ QuarterFace v k u c Q L A

-- STANDING: DEFINITION
noncomputable def ZeroReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u c : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    ReturnFrame v k u c Q N L (fun _=>0) ∧ SharpFace v k u c Q N L (fun _=>0)

theorem original_return_lower {ds : Finset ℝ} {d s Q P : ℝ} (N K : ℤ) (a : ℕ)
    (hd : 0 < d) (hs : 0 < s) (hmem : s ∈ ds) (hm : IsMove ds Q P) (hQP : Q ≤ P)
    (hopen : d*P=(N : ℝ)+1/8) (he : EntryWindow s Q K)
    (hreturn : a=0 ∨ d*(((K+(a : ℤ) : ℤ) : ℝ)+1/8) ≤ s*((N : ℝ)+1/8)) :
    ((K+(a : ℤ) : ℤ) : ℝ)+1/8 ≤ s*P := by
  rcases hreturn with ha|hpassed
  · subst a
    norm_num only [Nat.cast_zero,add_zero]
    rcases he with hret|hcap
    · have hinc := mul_nonneg hs.le (sub_nonneg.mpr hQP)
      nlinarith only [hinc,hret.1]
    · have hnear : |s*Q-(K : ℝ)| < 1/8 := by rw [abs_lt]; constructor <;> linarith only [hcap.1,hcap.2]
      have hw : InWay s Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ K) hnear
      have horder := Fresh.FastestCaptureRecovery.captured_order_of_move N K hm hmem hd hs hopen hcap.1 hcap.2
      exact Fresh.NativeOpeningRecovery.opening_order_lower d s P N K hd hopen horder
  · exact Fresh.NativeOpeningRecovery.opening_order_lower d s P N (K+(a : ℤ)) hd hopen hpassed

theorem terminal_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u c : Fin 8) (Q : ℝ) (N : ℤ)
    (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) (hf : ReturnFrame v k u c Q N L A)
    (hface : SharpFace v k u c Q N L A) :
    Q < opening |v u-v k| N ∧ IsolatedAt v k (opening |v u-v k| N) := by
  obtain ⟨hu,hc,hLu,hAu,hQ,hlo,hhi,hm,he,hfirst⟩ := hf
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun hh => hu (hv.2 hh)))
  have hcpos : 0 < |v c-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun hh => hc (hv.2 hh)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ N hd ho hlo hhi
  have hQP : Q < opening |v u-v k| N := by linarith only [ht.1]
  refine ⟨hQP,?_⟩
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul]
  by_cases hiu : i=u
  · subst i
    apply clear_of_window N
    · exact ho.ge
    · linarith only [ho]
  · have hmem : |v i-v k| ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
    apply clear_of_window (lifted L A i)
    · exact original_return_lower N (L i) (A i) hd (Fresh.Cascade.disparitySet_pos hv k _ hmem) hmem hm hQP.le ho (he i hi hiu).1 (he i hi hiu).2
    · exact Fresh.NativeFirstClosing.closing_at_opening _ _ _ Q _ N (lifted L A i) (lifted L A c) hd (abs_nonneg _) hcpos ho hface (hfirst i hi)

theorem sharp_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : SharpReturnClass v k) : Isolation v k := by
  obtain ⟨hv,u,c,Q,N,L,A,hf,hface⟩ := h
  have hQ := hf.2.2.2.2.1
  obtain ⟨ht,hclear⟩ := terminal_clear hv k u c Q N L A hf hface
  exact ⟨opening |v u-v k| N,lt_trans hQ ht,hclear⟩

theorem quarter_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterReturnClass v k) : SharpReturnClass v k := by
  obtain ⟨hv,u,c,Q,N,L,A,hf,hface⟩ := h
  refine ⟨hv,u,c,Q,N,L,A,hf,?_⟩
  exact Fresh.NativeFirstClosing.quarter_implies_deficit _ _ Q N (lifted L A c) (abs_nonneg _) hf.2.2.2.2.2.1 hface

theorem zero_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : ZeroReturnClass v k) : SharpReturnClass v k := by
  obtain ⟨hv,u,c,Q,N,L,hf,hface⟩ := h
  exact ⟨hv,u,c,Q,N,L,(fun _=>0),hf,hface⟩

theorem quarter_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterReturnClass v k) : Isolation v k :=
  sharp_isolation (quarter_into_sharp h)

theorem zero_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ZeroReturnClass v k) : Isolation v k :=
  sharp_isolation (zero_into_sharp h)

theorem return_roles {v : Fin 8 → ℝ} {k : Fin 8} (h : SharpReturnClass v k) :
    ∃ (u c : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) (R : Finset (Fin 8)),
      ReturnFrame v k u c Q N L A ∧ SharpFace v k u c Q N L A ∧
      u∉R ∧ k∉R ∧ ∀ i : Fin 8, i≠k → (i∈R ↔ 0 < A i) := by
  classical
  obtain ⟨hv,u,c,Q,N,L,A,hf,hface⟩ := h
  let R := (Finset.univ.erase k).filter (fun i=>0 < A i)
  refine ⟨u,c,Q,N,L,A,R,hf,hface,?_,?_,?_⟩
  · simp [R,hf.2.2.2.1]
  · simp [R]
  · intro i hi
    simp [R,hi]

theorem return_nonnegative (s Q P : ℝ) (K J : ℤ) (hs : 0 ≤ s) (hQP : Q ≤ P)
    (he : EntryWindow s Q K) (hupper : s*P ≤ (J : ℝ)+7/8) : K ≤ J := by
  have hlow : (K : ℝ)-1/8 < s*Q := by
    rcases he with hret|hcap
    · linarith only [hret.1]
    · exact hcap.1
  have htime := mul_le_mul_of_nonneg_left hQP hs
  by_contra hn
  have hz : J+1 ≤ K := by omega
  have hr : (J : ℝ)+1 ≤ (K : ℝ) := by exact_mod_cast hz
  linarith only [hlow,htime,hupper,hr]

theorem lifted_add (L : Fin 8 → ℤ) (A B : Fin 8 → ℕ) :
    lifted (lifted L A) B=lifted L (fun i=>A i+B i) := by
  funext i
  simp only [lifted,Nat.cast_add]
  ring

#print axioms return_nonnegative
#print axioms lifted_add
#print axioms original_return_lower
#print axioms terminal_clear
#print axioms sharp_isolation
#print axioms quarter_into_sharp
#print axioms zero_into_sharp
#print axioms quarter_isolation
#print axioms zero_isolation
#print axioms return_roles
end Fresh.NativeReturnCapture
