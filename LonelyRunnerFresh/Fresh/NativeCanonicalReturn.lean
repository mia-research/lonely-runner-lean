import Fresh.NativeReturnSurvivors

/-! Canonical native-return inputs eliminate freely supplied window/return
labels and closing witnesses. Only positive-return lower comparisons remain;
zero-return readings are unconditionally clear after the actual move. The
original first-closing family is an equivalent input representation. -/
namespace Fresh.NativeCanonicalReturn
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnCapture
  Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def CanonicalReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ), u≠k ∧ 0 < Q ∧
    (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
    IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
    ∀ i : Fin 8, i≠k → 0 < advance |v i-v k| Q (opening |v u-v k| N) →
      |v u-v k| * ((label (|v i-v k| * opening |v u-v k| N) : ℝ)+1/8) ≤
        |v i-v k| * ((N : ℝ)+1/8)

-- STANDING: DEFINITION
noncomputable def NoReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u : Fin 8) (Q : ℝ) (N : ℤ), u≠k ∧ 0 < Q ∧
    (N : ℝ)-1/8 < |v u-v k| * Q ∧ |v u-v k| * Q < (N : ℝ)+1/8 ∧
    IsMove (disparitySet v k) Q (opening |v u-v k| N) ∧
    ∀ i : Fin 8, i≠k → advance |v i-v k| Q (opening |v u-v k| N)=0

theorem returned_isolated {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u : Fin 8) (hu : u≠k)
    (Q P : ℝ) (N : ℤ) (hm : IsMove (disparitySet v k) Q P)
    (hopen : |v u-v k| * P=(N : ℝ)+1/8)
    (hpassed : ∀ i : Fin 8, i≠k → 0 < advance |v i-v k| Q P →
      |v u-v k| * ((label (|v i-v k| * P) : ℝ)+1/8) ≤ |v i-v k| * ((N : ℝ)+1/8)) :
    IsolatedAt v k P := by
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul]
  by_contra hn
  have hw : InWay |v i-v k| P := lt_of_not_ge hn
  have he := (Fresh.NativeReturnSurvivors.crossproduct_capture hv k u hu Q P N hm hopen i hi).1 hw
  have hp := hpassed i hi he.1
  linarith only [hp,he.2]

theorem canonical_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CanonicalReturnClass v k) : Isolation v k := by
  obtain ⟨hv,u,Q,N,hu,hQ,hlo,hhi,hm,hpassed⟩ := h
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he=>hu (hv.2 he)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ N hd ho hlo hhi
  exact ⟨opening |v u-v k| N,by linarith only [hQ,ht.1],returned_isolated hv k u hu Q _ N hm ho hpassed⟩

theorem noReturn_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : NoReturnClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,u,Q,N,hu,hQ,hlo,hhi,hm,hzero⟩ := h
  refine ⟨hv,u,Q,N,hu,hQ,hlo,hhi,hm,?_⟩
  intro i hi ha
  have hz := hzero i hi
  omega

theorem sharp_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : SharpReturnClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,u,c,Q,N,L,A,hf,hface⟩ := h
  have hlabels := sharp_labels hv k u c Q N L A hf hface
  obtain ⟨hu,hc,hLu,hAu,hQ,hlo,hhi,hm,he,hfirst⟩ := hf
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun hh=>hu (hv.2 hh)))
  have ho : |v u-v k| * opening |v u-v k| N=(N : ℝ)+1/8 := by dsimp [opening]; field_simp
  refine ⟨hv,u,Q,N,hu,hQ,hlo,hhi,hm,?_⟩
  intro i hi ha
  have hiu : i≠u := by
    intro hieq
    subst i
    have hz := selected_advance_zero _ Q _ N hlo hhi ho
    omega
  rcases (he i hi hiu).2 with hz|hpassed
  · have hh := (hlabels i hi).2.2
    omega
  · rw [(hlabels i hi).2.1]
    exact hpassed

theorem canonical_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : CanonicalReturnClass v k) : SharpReturnClass v k := by
  obtain ⟨hv,u,Q,N,hu,hQ,hlo,hhi,hm,hpassed⟩ := h
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he=>hu (hv.2 he)))
  let P := opening |v u-v k| N
  have ho : |v u-v k| * P=(N : ℝ)+1/8 := by dsimp [P,opening]; field_simp
  have hQP := le_of_isMove (disparitySet_pos hv k) hm
  let L : Fin 8 → ℤ := fun i=>label (|v i-v k| * Q)
  let A : Fin 8 → ℕ := fun i=>advance |v i-v k| Q P
  have htarg (i : Fin 8) : lifted L A i=label (|v i-v k| * P) := by
    exact (advance_identity |v i-v k| Q P (abs_nonneg _) hQP).symm
  obtain ⟨c,hc,hfirst⟩ := Fresh.NativeFirstClosing.exists_first_closing hv k (lifted L A)
  refine ⟨hv,u,c,Q,N,L,A,?_,?_⟩
  · refine ⟨hu,hc,?_,?_,hQ,hlo,hhi,hm,?_,hfirst⟩
    · exact (entry_iff_label _ Q N).1 (Or.inr ⟨hlo,hhi⟩)
    · exact selected_advance_zero _ Q P N hlo hhi ho
    · intro i hi hiu
      refine ⟨label_entry _ Q,?_⟩
      by_cases ha : A i=0
      · exact Or.inl ha
      · apply Or.inr
        rw [htarg]
        exact hpassed i hi (by change 0 < A i; omega)
  · have hup := ((entry_interval _ P _).1 (label_entry |v c-v k| P)).2
    rw [←htarg c] at hup
    exact (Fresh.NativeFirstClosing.deficit_iff_upper _ _ Q P N (lifted L A c) hd ho).2 hup

theorem canonical_iff_sharp {v : Fin 8 → ℝ} {k : Fin 8} : CanonicalReturnClass v k ↔ SharpReturnClass v k :=
  ⟨canonical_into_sharp,sharp_into_canonical⟩

theorem noReturn_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : NoReturnClass v k) : Isolation v k :=
  canonical_isolation (noReturn_into_canonical h)

#print axioms returned_isolated
#print axioms canonical_isolation
#print axioms noReturn_into_canonical
#print axioms sharp_into_canonical
#print axioms canonical_into_sharp
#print axioms canonical_iff_sharp
#print axioms noReturn_isolation
end Fresh.NativeCanonicalReturn
