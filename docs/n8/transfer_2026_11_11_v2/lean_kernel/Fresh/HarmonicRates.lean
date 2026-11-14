import Fresh.HarmonicFrontierVerified
import Fresh.HarmonicSlow
import Fresh.HarmonicChecked

open Classical

namespace Fresh.Harmonic

private theorem no_five {p : Vector ℕ 5} (hp : ∀ i : Fin 5, 0 < p[i.val] ∧ p[i.val] ≤ 10)
    (hs : Monotone (fun i : Fin 5 => p[i.val])) (h : mixed p = true) :
    (replay p (fiveTimes p)).isEmpty = true :=
  List.all_eq_true.mp five_checked p (List.mem_filter.mpr ⟨mem_vectors hp hs,h⟩)

private theorem no_six {p : Vector ℕ 6} (hp : ∀ i : Fin 6, 0 < p[i.val] ∧ p[i.val] ≤ 5)
    (hs : Monotone (fun i : Fin 6 => p[i.val])) (h : mixed p = true) :
    (replay p [1,2,3,4,5]).isEmpty = true :=
  List.all_eq_true.mp six_checked p (List.mem_filter.mpr ⟨mem_vectors hp hs,h⟩)

private theorem times_valid {p : Vector ℕ 5} (m : ℕ) (hm : m ∈ fiveTimes p) :
    0 < m ∧ m ≤ 5 := by
  unfold fiveTimes at hm
  split at hm <;> simp at hm <;> omega

private theorem slow_for_pattern (p : Vector ℕ 5) {a : ℝ} (ha : 1 ≤ a) :
    ∃ t, SlowGood a t (fiveTimes p) := by
  unfold fiveTimes
  split
  · exact slow123 a ha
  · exact slow125 a ha

/-- All 1,849 mixed primitive five-reading profiles through harmonic 10. -/
theorem five_rates (p : Vector ℕ 5) (b : Fin 5 → ℝ) {a B frequency : ℝ}
    (hp : ∀ i : Fin 5, 0 < p[i.val] ∧ p[i.val] ≤ 10)
    (ordered : Monotone (fun i : Fin 5 => p[i.val])) (primitive_mixed : mixed p = true)
    (ha : 1 ≤ a) (hslow : 40*a ≤ frequency) (hfast : 100*B ≤ frequency)
    (hb : ∀ i, |b i| ≤ B) :
    ∃ s, InWindows s ∧ (1/8 : ℝ) ≤ distInt s ∧ (1/8 : ℝ) ≤ distInt (a*s) ∧
      ∀ i : Fin 5, (1/8 : ℝ) ≤ distInt (((↑(p.get i) : ℝ)*frequency+b i)*s) := by
  obtain ⟨t,ht⟩ := slow_for_pattern p ha
  obtain ⟨m,hm,φ,hφ⟩ := drift_of_replay b t (fun i => (hp i).1) ordered times_valid
    (no_five hp ordered primitive_mixed)
  obtain ⟨hw,hclear⟩ := ht m hm
  have hpos : 0 < frequency := by linarith
  obtain ⟨s,hs,hnear,slow,fast⟩ := lift (t := (m:ℝ)*t) ({1,a} : Finset ℝ)
    (e := 1/80) (B := B) (fun i : Fin 5 => p[i.val]) b hpos ha
    ((div_le_iff₀ (by positivity)).2 (by linarith))
    ((div_le_iff₀ (by positivity)).2 (by linarith)) hw
    (by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨by simpa using ha, by simpa using pinned_buffer hw⟩
      · exact ⟨by rw [abs_of_nonneg (by linarith)], by linarith⟩)
    hb (fun i => (hφ i).le)
  exact ⟨s,hs,by simpa using slow 1 (by simp),slow a (by simp),fast⟩

/-- All 200 mixed primitive six-reading profiles through harmonic 5. -/
theorem six_rates (p : Vector ℕ 6) (b : Fin 6 → ℝ) {B frequency : ℝ}
    (hp : ∀ i : Fin 6, 0 < p[i.val] ∧ p[i.val] ≤ 5)
    (ordered : Monotone (fun i : Fin 6 => p[i.val])) (primitive_mixed : mixed p = true)
    (hslow : 20 ≤ frequency) (hfast : 100*B ≤ frequency)
    (hb : ∀ i, |b i| ≤ B) :
    ∃ s, s ∈ Set.Icc (1/8 : ℝ) (7/8) ∧ (1/8 : ℝ) ≤ distInt s ∧
      ∀ i : Fin 6, (1/8 : ℝ) ≤ distInt (((↑(p.get i) : ℝ)*frequency+b i)*s) := by
  obtain ⟨m,hm,φ,hφ⟩ := drift_of_replay b (3/20)
    (fun i => (hp i).1)
    ordered (ms := [1,2,3,4,5]) (by intro k hk; simp at hk; omega)
    (no_six hp ordered primitive_mixed)
  have hw := slow12345 m hm
  have hpos : 0 < frequency := by linarith
  obtain ⟨s,hs,hnear,slow,fast⟩ := lift (t := (m:ℝ)*(3/20)) ({1} : Finset ℝ)
    (e := 1/40) (B := B) (fun i : Fin 6 => p[i.val]) b hpos (le_refl 1)
    ((div_le_iff₀ (by positivity)).2 (by linarith))
    ((div_le_iff₀ (by positivity)).2 (by linarith)) hw
    (by intro v hv; have he := Finset.mem_singleton.mp hv; subst v
        exact ⟨by norm_num, by simpa using pinned_buffer hw⟩)
    hb (fun i => (hφ i).le)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hnear
  have hbase : (m : ℝ)*(3/20) ∈ Set.Icc (3/20 : ℝ) (3/4) := by
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact ⟨s,⟨by linarith [hbase.1], by linarith [hbase.2]⟩,
    by simpa using slow 1 (by simp),fast⟩

#print axioms five_rates
#print axioms six_rates
end Fresh.Harmonic
