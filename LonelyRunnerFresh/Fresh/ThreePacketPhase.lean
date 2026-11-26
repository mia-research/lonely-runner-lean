import Fresh.APPhaseOpening

/-!
Rules:1–4,8–18. Four retained AP readings and a three-reading AP packet,
every real step b≥1,base x≥32b/3. Exact anchor phase bands join through
step-parameter overlaps. The selector retains the original core bands.
[PROVISIONAL: counting tool] named opening/cycle ceiling;
[PROVISIONAL: covering] finite step split in three_packet_all.
-/
open Classical
namespace Fresh.ThreePacketPhase
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.APPhaseOpening

theorem phase_opening (h : ℕ) {x b ε lo hi : ℝ}
    (hb : 1 ≤ b) (hx : (32/3 : ℝ)*b ≤ x)
    (hε : 0<ε) (hεmax : ε ≤ 3/32)
    (hfrac : b/(x+(h : ℝ)*b) ≤ ε)
    (hwidth : lo+ε ≤ hi) (hregionalLower : 32*(lo+ε) ≤ 7*b)
    (hregionalUpper : b ≤ 8*(hi-ε)) :
    ∃ T : ℝ, ∃ N : ℤ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      lo ≤ b*T ∧ b*T ≤ hi ∧ (x+(h : ℝ)*b)*T=(N : ℝ)+1/8 := by
  have hbpos : 0<b := by linarith
  have hhpos : 0≤(h : ℝ)*b := mul_nonneg (Nat.cast_nonneg _) hbpos.le
  have hX : 0<x+(h : ℝ)*b := by linarith
  let α : ℝ := max (b/8) lo
  have hαlo : lo ≤ α := le_max_right _ _
  have hαb : b/8 ≤ α := le_max_left _ _
  have hαhi : α+ε ≤ hi := by
    dsimp [α]
    rcases le_total (b/8) lo with hh | hh
    · rw [max_eq_right hh]; exact hwidth
    · rw [max_eq_left hh]; linarith
  have hαcore : 32*(α+ε) ≤ 7*b := by
    dsimp [α]
    rcases le_total (b/8) lo with hh | hh
    · rw [max_eq_right hh]; exact hregionalLower
    · rw [max_eq_left hh]; nlinarith
  obtain ⟨h1,h2,h3⟩ := openingAfter_spec (lo := α/b) hX
  have htlo : (1/8 : ℝ) ≤ openingAfter (x+(h : ℝ)*b) (α/b) := by
    have hh : (1/8 : ℝ) ≤ α/b := by rw [le_div_iff₀ hbpos]; linarith
    exact hh.trans h1
  have hp1 : α ≤ b*openingAfter (x+(h : ℝ)*b) (α/b) := by
    have := (div_le_iff₀ hbpos).mp h1
    nlinarith
  have hp2 : b*openingAfter (x+(h : ℝ)*b) (α/b) ≤ α+ε := by
    have hh := mul_le_mul_of_nonneg_left h2.le hbpos.le
    have he : b*(α/b+1/(x+(h : ℝ)*b))=α+b/(x+(h : ℝ)*b) := by field_simp
    rw [he] at hh
    linarith
  have htcore : openingAfter (x+(h : ℝ)*b) (α/b) ≤ (7/32 : ℝ) := by
    have hh : b*(32*openingAfter (x+(h : ℝ)*b) (α/b)) ≤ b*7 := by nlinarith
    have hh' := le_of_mul_le_mul_left hh hbpos
    linarith
  refine ⟨_,_,by linarith,?_,hαlo.trans hp1,hp2.trans hαhi,h3⟩
  intro j hj1 hj4
  have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hj4R : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
  have htpos : 0<openingAfter (x+(h : ℝ)*b) (α/b) := by linarith
  apply clear_of_window 0 <;> push_cast
  · have hh := mul_le_mul_of_nonneg_right hj1R htpos.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hj4R htpos.le
    nlinarith

theorem zero_chart (q : ℤ) {x b : ℝ} (hb : 1 ≤ b) (hx : (32/3 : ℝ)*b ≤ x)
    (hlo : (32*(q : ℝ)+3)/7 ≤ b) (hhi : b ≤ 8*(q : ℝ)+9/4) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 2 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  have hbpos : 0<b := by linarith
  have hX : 0<x+(0 : ℝ)*b := by linarith
  have hfrac : b/(x+(0 : ℝ)*b) ≤ (3/32 : ℝ) := by
    apply (div_le_iff₀ hX).2
    nlinarith
  obtain ⟨T,N,ht,hcore,hp1,hp2,hopen⟩ := phase_opening 0 hb hx
    (by norm_num : (0 : ℝ)<3/32) (by norm_num : (3/32 : ℝ)≤3/32) (by simpa using hfrac)
    (lo := (q : ℝ)) (hi := (q : ℝ)+3/8) (by linarith) (by linarith) (by linarith)
  refine ⟨T,ht,hcore,packet_phase_endpoints 2 0 (fun j => (j : ℤ)*q) N hp1 hp2 hopen ?_⟩
  intro j hj
  interval_cases j <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> push_cast <;> linarith

theorem one_chart (q : ℤ) {x b : ℝ} (hb : 1 ≤ b) (hx : (32/3 : ℝ)*b ≤ x)
    (hlo : (32/7 : ℝ)*((q : ℝ)+1/4+3/35) ≤ b)
    (hhi : b ≤ 8*(q : ℝ)+186/35) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 2 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  have hbpos : 0<b := by linarith
  have hX : 0<x+(1 : ℝ)*b := by linarith
  have hfrac : b/(x+(1 : ℝ)*b) ≤ (3/35 : ℝ) := by
    apply (div_le_iff₀ hX).2
    nlinarith
  obtain ⟨T,N,ht,hcore,hp1,hp2,hopen⟩ := phase_opening 1 hb hx
    (by norm_num : (0 : ℝ)<3/35) (by norm_num : (3/35 : ℝ)≤3/32) (by simpa using hfrac)
    (lo := (q : ℝ)+1/4) (hi := (q : ℝ)+3/4) (by linarith) (by linarith) (by linarith)
  refine ⟨T,ht,hcore,packet_phase_endpoints 2 1 (fun j => if j=0 then -q-1 else if j=1 then 0 else q) N hp1 hp2 hopen ?_⟩
  intro j hj
  interval_cases j <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> push_cast <;> linarith

theorem three_packet_all {x b : ℝ} (hb : 1 ≤ b) (hx : (32/3 : ℝ)*b ≤ x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 2 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  by_cases h0 : b ≤ 9/4
  · exact zero_chart 0 hb hx (by norm_num; linarith) (by norm_num; linarith)
  by_cases h1 : b ≤ 186/35
  · exact one_chart 0 hb hx (by norm_num; linarith) (by norm_num; linarith)
  by_cases h2 : b ≤ 41/4
  · exact zero_chart 1 hb hx (by norm_num; linarith) (by norm_num; linarith)
  by_cases h3 : b ≤ 466/35
  · exact one_chart 1 hb hx (by norm_num; linarith) (by norm_num; linarith)
  by_cases h4 : b ≤ 73/4
  · exact zero_chart 2 hb hx (by norm_num; linarith) (by norm_num; linarith)
  · let q : ℤ := ⌈b/8-1/4⌉
    have hq1 : b/8-1/4 ≤ (q : ℝ) := Int.le_ceil _
    have hq2 : (q : ℝ)<b/8-1/4+1 := Int.ceil_lt_add_one _
    exact one_chart q hb hx (by linarith) (by linarith)

#print axioms phase_opening
#print axioms zero_chart
#print axioms one_chart
#print axioms three_packet_all
end Fresh.ThreePacketPhase
