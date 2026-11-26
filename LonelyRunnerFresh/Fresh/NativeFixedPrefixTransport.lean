import Fresh.NativeCoalescedCaptureArrangement

/-! Exact transport along a SUPPLIED native fixed-group prefix. Its length
is an arbitrary input, never a budget or a bound used to obtain isolation.
Per-step opening faces are necessary and sufficient, even for recovered
returns. A single original closing guard suffices when all outsiders retain
one clear band. No lower-order existence theorem supplies the endpoint. -/
open Classical
namespace Fresh.NativeFixedPrefixTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

noncomputable def PrefixFaces (ds added : Finset ℝ) (C : ℝ) (N : ℕ) : Prop :=
  ∀ j : ℕ,j<N → ∀ s∈added,(label (s*cascadeSeq ds C j) : ℝ)+1/8 ≤ s*cascadeSeq ds C (j+1)

noncomputable def PrefixSame (ds added : Finset ℝ) (C : ℝ) (N : ℕ) : Prop :=
  ∀ j : ℕ,j ≤ N → cascadeSeq (ds∪added) C j=cascadeSeq ds C j

theorem native_seq_monotone {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (C : ℝ) :
    Monotone (cascadeSeq ds C) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_of_isMove hpos (cascadeSeq_isMove ds C j)

theorem prefix_same_iff_faces {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) :
    PrefixSame ds added C N ↔ PrefixFaces ds added C N := by
  constructor
  · intro hs j hj
    have hh := cascadeSeq_isMove (ds∪added) C j
    rw [hs j (by omega),hs (j+1) (by omega)] at hh
    exact (union_move_iff hpos hadded _ _ (cascadeSeq_isMove ds C j)).1 hh
  · intro hf j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hh := cascadeSeq_isMove (ds∪added) C j
      rw [ih (by omega)] at hh
      have hn := (union_move_iff hpos hadded _ _ (cascadeSeq_isMove ds C j)).2 (hf j (by omega))
      exact isMove_unique hh hn

theorem clear_entry_insert_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U V : ℝ)
    (hs : 0<s) (hm : IsMove ds U V) (hclear : ¬InWay s U) : IsMove (insert s ds) U V := by
  have hh := insert_move hpos s U V hs hm
  rw [max_eq_left (le_trans (clear_opening_le s U hs hclear) (le_of_isMove hpos hm))] at hh
  exact hh

theorem band_at_point (s C U R : ℝ) (K : ℤ) (hs : 0 ≤ s) (hCU : C ≤ U) (hUR : U ≤ R)
    (hlo : (K : ℝ)+1/8 ≤ s*C) (hhi : s*R ≤ (K : ℝ)+7/8) :
    ¬InWay s U ∧ label (s*U)=K := by
  have hlow := le_trans hlo (mul_le_mul_of_nonneg_left hCU hs)
  have hupp := le_trans (mul_le_mul_of_nonneg_left hUR hs) hhi
  exact ⟨not_lt.mpr (clear_of_window K hlow hupp),(entry_iff_label s U K).1 (Or.inl ⟨hlow,hupp⟩)⟩

theorem interval_band_at_point (lo s hi C U R : ℝ) (K : ℤ) (hlo : 0<lo)
    (hls : lo ≤ s) (hsh : s ≤ hi) (hC : 0 ≤ C) (hCU : C ≤ U) (hUR : U ≤ R)
    (hlower : (K : ℝ)+1/8 ≤ lo*C) (hupper : hi*R ≤ (K : ℝ)+7/8) :
    ¬InWay s U ∧ label (s*U)=K := by
  have hs := lt_of_lt_of_le hlo hls
  have hR := le_trans hC (le_trans hCU hUR)
  apply band_at_point s C U R K hs.le hCU hUR
  · exact le_trans hlower (mul_le_mul_of_nonneg_right hls hC)
  · exact le_trans (mul_le_mul_of_nonneg_right hsh hR) hupper

noncomputable def PrefixBand (ds added : Finset ℝ) (C : ℝ) (N : ℕ) : Prop :=
  ∀ s∈added,¬InWay s C ∧ s*cascadeSeq ds C N ≤ (label (s*C) : ℝ)+7/8

theorem band_keeps_supplied_states {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) (hb : PrefixBand ds added C N) :
    ∀ j : ℕ,j ≤ N → ∀ s∈added,¬InWay s (cascadeSeq ds C j) ∧
      label (s*cascadeSeq ds C j)=label (s*C) := by
  intro j hj s hs
  have hmono := native_seq_monotone hpos C
  have hlo := le_of_not_gt (fun hh=>(hb s hs).1 ((inWay_iff_lower_not_passed s C).2 hh))
  exact band_at_point s C _ _ (label (s*C)) (hadded s hs).le
    (by simpa only [cascadeSeq_zero] using hmono (Nat.zero_le j)) (hmono hj) hlo (hb s hs).2

theorem band_implies_faces {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) (hb : PrefixBand ds added C N) :
    PrefixFaces ds added C N := by
  intro j hj s hs
  have hc := (band_keeps_supplied_states hpos hadded C N hb j (by omega) s hs).1
  have hm := clear_entry_insert_move hpos s _ _ (hadded s hs) (cascadeSeq_isMove ds C j) hc
  exact move_passes_entry_opening (by
    intro q hq
    rcases Finset.mem_insert.mp hq with he|hq
    · subst q
      exact hadded s hs
    · exact hpos q hq) _ _ s hm (Finset.mem_insert_self _ _)

theorem band_prefix_same {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) (hb : PrefixBand ds added C N) :
    PrefixSame ds added C N :=
  (prefix_same_iff_faces hpos hadded C N).2 (band_implies_faces hpos hadded C N hb)

theorem earliest_closing_implies_band {ds added : Finset ℝ} (hadded : ∀ s∈added,0<s)
    (C : ℝ) (N : ℕ) (a : ℝ) (_ha : a∈added)
    (hclear : ∀ s∈added,¬InWay s C)
    (hfirst : ∀ s∈added,closing a C ≤ closing s C)
    (hfit : cascadeSeq ds C N ≤ closing a C) : PrefixBand ds added C N := by
  intro s hs
  refine ⟨hclear s hs,?_⟩
  have hh := (le_div_iff₀ (hadded s hs)).1 (le_trans hfit (hfirst s hs))
  simpa only [closing,mul_comm] using hh

theorem exists_earliest_added (added : Finset ℝ) (C : ℝ) (hne : added.Nonempty) :
    ∃ a∈added,∀ s∈added,closing a C ≤ closing s C := by
  exact Finset.exists_min_image added (fun s=>closing s C) hne

theorem earliest_closing_prefix_same {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) (a : ℝ) (ha : a∈added)
    (hclear : ∀ s∈added,¬InWay s C) (hfirst : ∀ s∈added,closing a C ≤ closing s C)
    (hfit : cascadeSeq ds C N ≤ closing a C) : PrefixSame ds added C N := by
  exact band_prefix_same hpos hadded C N (earliest_closing_implies_band hadded C N a ha hclear hfirst hfit)

theorem prefix_recovered_endpoint {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (N : ℕ) (hf : PrefixFaces ds added C N)
    (hfixed : LonelyAt ds (cascadeSeq ds C N))
    (hclear : ∀ s∈added,¬InWay s (cascadeSeq ds C N)) :
    LonelyAt (ds∪added) (cascadeSeq (ds∪added) C N) := by
  rw [(prefix_same_iff_faces hpos hadded C N).2 hf N le_rfl]
  intro s hs
  rcases Finset.mem_union.mp hs with hs|hs
  · exact hfixed s hs
  · exact not_lt.mp (hclear s hs)

theorem interval_singleton_band {ds : Finset ℝ} (lo s hi C : ℝ) (N : ℕ) (K : ℤ)
    (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hC : 0 ≤ C)
    (hlower : (K : ℝ)+1/8 ≤ lo*C) (hupper : hi*cascadeSeq ds C N ≤ (K : ℝ)+7/8)
    (hCR : C ≤ cascadeSeq ds C N) : PrefixBand ds {s} C N := by
  intro q hq
  have he : q=s := Finset.mem_singleton.mp hq
  subst q
  have hh := interval_band_at_point lo s hi C C (cascadeSeq ds C N) K hlo hls hsh hC le_rfl hCR hlower hupper
  refine ⟨hh.1,?_⟩
  rw [hh.2]
  have hR := le_trans hC hCR
  exact le_trans (mul_le_mul_of_nonneg_right hsh hR) hupper

theorem first_failed_face_changes_next {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (C : ℝ) (j : ℕ) (s : ℝ) (hs : s∈added)
    (hf : PrefixFaces ds added C j)
    (hfail : s*cascadeSeq ds C (j+1)<(label (s*cascadeSeq ds C j) : ℝ)+1/8) :
    cascadeSeq (ds∪added) C j=cascadeSeq ds C j ∧
      cascadeSeq ds C (j+1)<cascadeSeq (ds∪added) C (j+1) := by
  have he := (prefix_same_iff_faces hpos hadded C j).2 hf j le_rfl
  have hp := hadded s hs
  have hinc := mul_le_mul_of_nonneg_left (le_of_isMove hpos (cascadeSeq_isMove ds C j)) hp.le
  have hw : InWay s (cascadeSeq ds C j) :=
    (inWay_iff_lower_not_passed _ _).2 (lt_of_le_of_lt hinc hfail)
  have hlt : cascadeSeq ds C (j+1)<nextOpening s (cascadeSeq ds C j) := by
    rw [captured_opening s _ hw]
    dsimp [labelledOpening,opening]
    apply (lt_div_iff₀ hp).2
    simpa only [mul_comm] using hfail
  have hm := cascadeSeq_isMove (ds∪added) C j
  rw [he] at hm
  refine ⟨he,?_⟩
  rcases hm with hfix|⟨d,hd,hwd,hR,hmax⟩
  · exact (hfix.1 s (Finset.mem_union_right _ hs) hw).elim
  · exact lt_of_lt_of_le hlt (hmax s (Finset.mem_union_right _ hs) hw)

theorem interval_prefix_faces {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (lo s hi C : ℝ) (N : ℕ) (hC : 0 ≤ C) (hls : lo ≤ s) (hsh : s ≤ hi)
    (hl : ∀ j : ℕ,j<N → label (lo*cascadeSeq ds C j)=label (hi*cascadeSeq ds C j))
    (hfaces : PrefixFaces ds {lo} C N) : PrefixFaces ds {s} C N := by
  intro j hj q hq
  have he : q=s := Finset.mem_singleton.mp hq
  subst q
  have hmono := native_seq_monotone hpos C
  have hstart : C ≤ cascadeSeq ds C j := by simpa only [cascadeSeq_zero] using hmono (Nat.zero_le j)
  have hnext : C ≤ cascadeSeq ds C (j+1) := by simpa only [cascadeSeq_zero] using hmono (Nat.zero_le (j+1))
  have hlabel := speed_interval_label lo s hi _ hls hsh (le_trans hC hstart) (hl j hj)
  rw [hlabel]
  exact le_trans (hfaces j hj lo (Finset.mem_singleton_self lo))
    (mul_le_mul_of_nonneg_right hls (le_trans hC hnext))

theorem nonfinal_interval_faces {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (lo s hi C : ℝ) (N : ℕ) (K : ℤ) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi)
    (hC : 0 ≤ C) (hN : 0<N) (hlower : (K : ℝ)+1/8 ≤ lo*C)
    (hupper : hi*cascadeSeq ds C (N-1) ≤ (K : ℝ)+7/8) : PrefixFaces ds {s} C N := by
  intro j hj q hq
  have he : q=s := Finset.mem_singleton.mp hq
  subst q
  have hp := lt_of_lt_of_le hlo hls
  have hmono := native_seq_monotone hpos C
  have hstart : C ≤ cascadeSeq ds C j := by simpa only [cascadeSeq_zero] using hmono (Nat.zero_le j)
  have hend := hmono (show j ≤ N-1 by omega)
  have hc := (interval_band_at_point lo s hi C _ _ K hlo hls hsh hC hstart hend hlower hupper).1
  have hm := clear_entry_insert_move hpos s _ _ hp (cascadeSeq_isMove ds C j) hc
  have hposs : ∀ d∈insert s ds,0<d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with he|hd
    · subst d; exact hp
    · exact hpos d hd
  exact move_passes_entry_opening hposs _ _ s hm (Finset.mem_insert_self _ _)

#print axioms native_seq_monotone
#print axioms prefix_same_iff_faces
#print axioms clear_entry_insert_move
#print axioms band_at_point
#print axioms interval_band_at_point
#print axioms band_keeps_supplied_states
#print axioms band_implies_faces
#print axioms band_prefix_same
#print axioms earliest_closing_implies_band
#print axioms exists_earliest_added
#print axioms earliest_closing_prefix_same
#print axioms prefix_recovered_endpoint
#print axioms interval_singleton_band
#print axioms first_failed_face_changes_next
#print axioms interval_prefix_faces
#print axioms nonfinal_interval_faces
end Fresh.NativeFixedPrefixTransport
