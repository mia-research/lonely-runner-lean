import Fresh.NativeReturnJoins

/-! Exact integer coordinates at GIVEN native states. The ceiling labels a
phase already supplied; it does not select an isolation time. Chronological
returns are nonnegative and additive, and a selected capture retains its
own label at its opening. -/
namespace Fresh.NativeEntryLabels
open Fresh Fresh.NativeReturnCapture

noncomputable def label (x : ℝ) : ℤ := ⌈x-7/8⌉

noncomputable def advance (s Q P : ℝ) : ℕ := (label (s*P)-label (s*Q)).toNat

theorem entry_interval (s Q : ℝ) (K : ℤ) :
    EntryWindow s Q K ↔ (K : ℝ)-1/8 < s*Q ∧ s*Q ≤ (K : ℝ)+7/8 := by
  constructor
  · intro he
    rcases he with hret|hcap
    all_goals constructor <;> linarith
  · intro he
    by_cases hl : (K : ℝ)+1/8 ≤ s*Q
    · exact Or.inl ⟨hl,he.2⟩
    · exact Or.inr ⟨he.1,lt_of_not_ge hl⟩

theorem entry_iff_label (s Q : ℝ) (K : ℤ) : EntryWindow s Q K ↔ label (s*Q)=K := by
  rw [entry_interval]
  unfold label
  rw [Int.ceil_eq_iff]
  constructor
  · intro he
    constructor <;> linarith only [he.1,he.2]
  · intro he
    constructor <;> linarith only [he.1,he.2]

theorem label_entry (s Q : ℝ) : EntryWindow s Q (label (s*Q)) :=
  (entry_iff_label s Q _).2 rfl

theorem entry_unique (s Q : ℝ) (K J : ℤ) (hK : EntryWindow s Q K) (hJ : EntryWindow s Q J) : K=J := by
  exact ((entry_iff_label s Q K).1 hK).symm.trans ((entry_iff_label s Q J).1 hJ)

theorem label_add_int (x : ℝ) (a : ℤ) : label (x+(a : ℝ))=label x+a := by
  unfold label
  have he : x+(a : ℝ)-7/8=(x-7/8)+(a : ℝ) := by ring
  rw [he,Int.ceil_add_intCast]

theorem label_monotone : Monotone label := by
  intro x y hxy
  exact Int.ceil_mono (sub_le_sub_right hxy _)

theorem advance_identity (s Q P : ℝ) (hs : 0 ≤ s) (hQP : Q ≤ P) :
    label (s*P)=label (s*Q)+(advance s Q P : ℤ) := by
  have hm := label_monotone (mul_le_mul_of_nonneg_left hQP hs)
  have ha := Int.toNat_of_nonneg (sub_nonneg.mpr hm)
  dsimp [advance]
  omega

theorem advance_add (s Q R P : ℝ) (hs : 0 ≤ s) (hQR : Q ≤ R) (hRP : R ≤ P) :
    advance s Q P=advance s Q R+advance s R P := by
  have h1 := advance_identity s Q R hs hQR
  have h2 := advance_identity s R P hs hRP
  have h3 := advance_identity s Q P hs (le_trans hQR hRP)
  omega

theorem selected_advance_zero (d Q P : ℝ) (N : ℤ)
    (hlo : (N : ℝ)-1/8 < d*Q) (hhi : d*Q < (N : ℝ)+1/8)
    (hopen : d*P=(N : ℝ)+1/8) : advance d Q P=0 := by
  have hQ : label (d*Q)=N := (entry_iff_label d Q N).1 (Or.inr ⟨hlo,hhi⟩)
  have hP : label (d*P)=N := (entry_iff_label d P N).1 (Or.inl (by constructor <;> linarith only [hopen]))
  simp [advance,hQ,hP]

theorem sharp_labels {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u c : Fin 8) (Q : ℝ) (N : ℤ)
    (L : Fin 8 → ℤ) (A : Fin 8 → ℕ) (hf : ReturnFrame v k u c Q N L A)
    (hface : SharpFace v k u c Q N L A) :
    ∀ i : Fin 8, i≠k → label (|v i-v k| * Q)=L i ∧
      label (|v i-v k| * Fresh.FastestCaptureRetention.opening |v u-v k| N)=lifted L A i ∧
      advance |v i-v k| Q (Fresh.FastestCaptureRetention.opening |v u-v k| N)=A i := by
  obtain ⟨hu,hc,hLu,hAu,hQ,hlo,hhi,hm,he,hfirst⟩ := hf
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun hh => hu (hv.2 hh)))
  have hcpos : 0 < |v c-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun hh => hc (hv.2 hh)))
  let P := Fresh.FastestCaptureRetention.opening |v u-v k| N
  have ho : |v u-v k| * P=(N : ℝ)+1/8 := by dsimp [P,Fresh.FastestCaptureRetention.opening]; field_simp
  have hQP := (Fresh.NativeOpeningRetention.capture_advance _ Q P N hd ho hlo hhi).1
  intro i hi
  have hmem : |v i-v k| ∈ disparitySet v k := Fresh.Localisation.mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have hs := Fresh.Cascade.disparitySet_pos hv k _ hmem
  have hentryQ : EntryWindow |v i-v k| Q (L i) := by
    by_cases hiu : i=u
    · subst i
      rw [hLu]
      exact Or.inr ⟨hlo,hhi⟩
    · exact (he i hi hiu).1
  have hentryP : EntryWindow |v i-v k| P (lifted L A i) := by
    apply Or.inl
    by_cases hiu : i=u
    · subst i
      simp only [lifted,hLu,hAu,Nat.cast_zero,add_zero]
      constructor <;> linarith only [ho]
    · constructor
      · exact original_return_lower N (L i) (A i) hd hs hmem hm (by linarith only [hQP]) ho (he i hi hiu).1 (he i hi hiu).2
      · exact Fresh.NativeFirstClosing.closing_at_opening _ _ _ Q P N (lifted L A i) (lifted L A c) hd hs.le hcpos ho hface (hfirst i hi)
  have hLQ := (entry_iff_label _ _ _).1 hentryQ
  have hLP := (entry_iff_label _ _ _).1 hentryP
  refine ⟨hLQ,hLP,?_⟩
  have ha := advance_identity |v i-v k| Q P hs.le (by linarith only [hQP])
  dsimp [P] at ha hLP
  dsimp [lifted] at hLP
  omega

theorem sharp_labels_unique {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u c b : Fin 8) (Q : ℝ) (N : ℤ)
    (L M : Fin 8 → ℤ) (A B : Fin 8 → ℕ)
    (hf : ReturnFrame v k u c Q N L A) (hg : ReturnFrame v k u b Q N M B)
    (hface : SharpFace v k u c Q N L A) (gface : SharpFace v k u b Q N M B) :
    ∀ i : Fin 8, i≠k → L i=M i ∧ A i=B i := by
  intro i hi
  have h1 := sharp_labels hv k u c Q N L A hf hface i hi
  have h2 := sharp_labels hv k u b Q N M B hg gface i hi
  exact ⟨h1.1.symm.trans h2.1,h1.2.2.symm.trans h2.2.2⟩

#print axioms sharp_labels
#print axioms sharp_labels_unique
#print axioms entry_interval
#print axioms entry_iff_label
#print axioms label_entry
#print axioms entry_unique
#print axioms label_add_int
#print axioms label_monotone
#print axioms advance_identity
#print axioms advance_add
#print axioms selected_advance_zero
end Fresh.NativeEntryLabels
