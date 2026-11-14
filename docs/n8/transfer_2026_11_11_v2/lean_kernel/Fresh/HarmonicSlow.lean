import Fresh.HarmonicLift

namespace Fresh.Harmonic

open Fresh.Cascade

private theorem phase_margin {x e : ℝ} (j : ℤ) (hl : (j : ℝ)+e ≤ x)
    (hu : x ≤ (j : ℝ)+1-e) : e ≤ distInt x := by
  change e ≤ |x-(round x : ℝ)|
  rcases le_or_gt (round x) j with h | h
  · have hh : ((round x : ℤ) : ℝ) ≤ j := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self _)
  · have hh : (j : ℝ)+1 ≤ (round x : ℝ) := by
      exact_mod_cast (show j+1 ≤ round x by omega)
    exact le_trans (by linarith) (neg_le_abs _)

private theorem intersect_scaled {a l u v w : ℝ} (ha : 0 < a)
    (hlu : l ≤ u) (hvw : v ≤ w) (hl : v ≤ a*u) (hu : a*l ≤ w) :
    ∃ t ∈ Set.Icc l u, a*t ∈ Set.Icc v w := by
  refine ⟨max l (v/a), ⟨le_max_left _ _, max_le hlu ((div_le_iff₀ ha).2 (by simpa [mul_comm] using hl))⟩, ?_⟩
  have hprod : a*(v/a) = v := by field_simp
  rw [mul_max_of_nonneg _ _ ha.le, hprod]
  exact ⟨le_max_right _ _, max_le hu hvw⟩

private theorem periodic_target {a l u : ℝ} (ha : 0 < a) (hlen : 1 ≤ a*(u-l)) :
    ∃ t ∈ Set.Icc l u, ∃ j : ℤ, a*t-(j : ℝ) = (l+u)/2 := by
  let c := (l+u)/2
  let j : ℤ := round (a*c-c)
  let t := ((j : ℝ)+c)/a
  have hr : |a*c-c-(j : ℝ)| ≤ 1/2 := abs_sub_round _
  have hh : a*t = (j : ℝ)+c := by dsimp [t]; field_simp
  have hb := abs_le.mp hr
  change -(1/2 : ℝ) ≤ a*c-c-(j : ℝ) ∧ a*c-c-(j : ℝ) ≤ 1/2 at hb
  have hc : a*c = (a*l+a*u)/2 := by dsimp [c]; ring
  have hwidth : 1 ≤ a*u-a*l := by linarith [mul_sub a u l]
  have h₁ : a*l ≤ a*t := by linarith [hb.1,hb.2]
  have h₂ : a*t ≤ a*u := by linarith [hb.1,hb.2]
  exact ⟨t, ⟨le_of_mul_le_mul_left h₁ ha, le_of_mul_le_mul_left h₂ ha⟩, j, by change a*t-(j:ℝ) = c; linarith⟩

def SlowGood (a t : ℝ) (ms : List ℕ) : Prop :=
  ∀ m ∈ ms, Buffered ((m : ℝ)*t) (1/80) ∧ 11/80 ≤ distInt (a*((m : ℝ)*t))

private theorem bufferI {t : ℝ} (h : t ∈ Set.Icc (11/80) (69/400)) :
    ∀ m : ℕ, m ∈ [1,2,5] → Buffered ((m : ℝ)*t) (1/80) := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl <;>
    exact Or.inl ⟨by norm_num; linarith [h.1], by norm_num; linarith [h.2]⟩

private theorem bufferJ {t : ℝ} (h : t ∈ Set.Icc (91/400) (149/400)) :
    ∀ m : ℕ, m ∈ [1,2,5] → Buffered ((m : ℝ)*t) (1/80) := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · exact Or.inl ⟨by norm_num; linarith [h.1], by norm_num; linarith [h.2]⟩
  · exact Or.inl ⟨by norm_num; linarith [h.1], by norm_num; linarith [h.2]⟩
  · exact Or.inr ⟨by norm_num; linarith [h.1], by norm_num; linarith [h.2]⟩

private theorem goodJ {x : ℝ} (h : x ∈ Set.Icc (91/400) (149/400)) :
    ∀ m : ℕ, m ∈ [1,2,5] → (11/80 : ℝ) ≤ distInt ((m : ℝ)*x) := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · exact phase_margin 0 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])
  · exact phase_margin 0 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])
  · exact phase_margin 1 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])

private theorem goodK {x : ℝ} (h : x ∈ Set.Icc (331/400) (69/80)) :
    ∀ m : ℕ, m ∈ [1,2,5] → (11/80 : ℝ) ≤ distInt ((m : ℝ)*x) := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · exact phase_margin 0 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])
  · exact phase_margin 1 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])
  · exact phase_margin 4 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])

private theorem mul_translate (m : ℕ) (j : ℤ) (x : ℝ) :
    distInt ((m : ℝ)*x) = distInt ((m : ℝ)*(x-j)) := by
  rw [show (m : ℝ)*x = (m : ℝ)*(x-j)+(((m : ℤ)*j : ℤ) : ℝ) by push_cast; ring]
  exact distInt_add_int _ _

theorem slow125 (a : ℝ) (ha : 1 ≤ a) : ∃ t, SlowGood a t [1,2,5] := by
  have hp : 0 < a := by linarith
  have rowJ {v w : ℝ} (hvw : v ≤ w) (hl : v ≤ a*(149/400))
      (hu : a*(91/400) ≤ w)
      (hgood : ∀ x ∈ Set.Icc v w, ∀ m : ℕ, m ∈ [1,2,5] →
        (11/80 : ℝ) ≤ distInt ((m : ℝ)*x)) : ∃ t, SlowGood a t [1,2,5] := by
    obtain ⟨t,ht,hx⟩ := intersect_scaled hp (by norm_num) hvw hl hu
    exact ⟨t, fun m hm => ⟨bufferJ ht m hm, by simpa [mul_left_comm] using hgood _ hx m hm⟩⟩
  have translated (j : ℤ) :
      ∀ x ∈ Set.Icc ((j : ℝ)+91/400) ((j : ℝ)+149/400),
        ∀ m : ℕ, m ∈ [1,2,5] → (11/80 : ℝ) ≤ distInt ((m : ℝ)*x) := by
    intro x hx m hm
    rw [mul_translate m j]
    exact goodJ ⟨by linarith [hx.1], by linarith [hx.2]⟩ m hm
  by_cases h1 : a ≤ 149/91
  · exact rowJ (by norm_num) (by linarith) (by linarith) (fun _ hx => goodJ hx)
  by_cases h2 : a ≤ 149/55
  · obtain ⟨t,ht,hx⟩ := intersect_scaled (l := 11/80) (u := 69/400)
      (v := 91/400) (w := 149/400) hp (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    exact ⟨t, fun m hm => ⟨bufferI ht m hm, by simpa [mul_left_comm] using goodJ hx m hm⟩⟩
  by_cases h3 : a ≤ 345/91
  · exact rowJ (by norm_num) (by linarith) (by linarith) (fun _ hx => goodK hx)
  by_cases h4 : a ≤ 549/91
  · exact rowJ (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (translated 1)
  by_cases h5 : a ≤ 7
  · exact rowJ (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (translated 2)
  obtain ⟨t,ht,j,hx⟩ := periodic_target (l := 91/400) (u := 149/400) hp
    (by norm_num; linarith)
  refine ⟨t, fun m hm => ⟨bufferJ ht m hm, ?_⟩⟩
  rw [mul_left_comm, mul_translate m j, hx]
  exact goodJ ⟨by norm_num, by norm_num⟩ m hm

private theorem goodU {x : ℝ} (h : x ∈ Set.Icc (11/80) (23/80)) :
    ∀ m : ℕ, m ∈ [1,2,3] → (11/80 : ℝ) ≤ distInt ((m : ℝ)*x) := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl <;>
    exact phase_margin 0 (by norm_num; linarith [h.1]) (by norm_num; linarith [h.2])

theorem slow123 (a : ℝ) (ha : 1 ≤ a) : ∃ t, SlowGood a t [1,2,3] := by
  have hp : 0 < a := by linarith
  have buf {t : ℝ} (h : t ∈ Set.Icc (11/80) (23/80)) :
      ∀ m : ℕ, m ∈ [1,2,3] → Buffered ((m : ℝ)*t) (1/80) := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl | rfl <;>
      exact Or.inl ⟨by norm_num; linarith [h.1], by norm_num; linarith [h.2]⟩
  have row {v w : ℝ} (hvw : v ≤ w) (hl : v ≤ a*(23/80)) (hu : a*(11/80) ≤ w)
      (hg : ∀ x ∈ Set.Icc v w, ∀ m : ℕ, m ∈ [1,2,3] →
        (11/80 : ℝ) ≤ distInt ((m : ℝ)*x)) : ∃ t, SlowGood a t [1,2,3] := by
    obtain ⟨t,ht,hx⟩ := intersect_scaled hp (by norm_num) hvw hl hu
    exact ⟨t, fun m hm => ⟨buf ht m hm, by simpa [mul_left_comm] using hg _ hx m hm⟩⟩
  by_cases h1 : a ≤ 23/11
  · exact row (by norm_num) (by linarith) (by linarith) (fun _ hx => goodU hx)
  by_cases h2 : a ≤ 149/33
  · apply row (v := 91/160) (w := 149/240) (by norm_num) (by linarith) (by linarith)
    intro x hx m hm
    simp at hm
    rcases hm with rfl | rfl | rfl
    · exact phase_margin 0 (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])
    · exact phase_margin 1 (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])
    · exact phase_margin 1 (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])
  by_cases h3 : a ≤ 7
  · apply row (v := 91/80) (w := 103/80) (by norm_num) (by linarith) (by linarith)
    intro x hx m hm
    rw [mul_translate m 1]
    exact goodU ⟨by norm_num; linarith [hx.1], by norm_num; linarith [hx.2]⟩ m hm
  obtain ⟨t,ht,j,hx⟩ := periodic_target (l := 11/80) (u := 23/80) hp
    (by norm_num; linarith)
  refine ⟨t, fun m hm => ⟨buf ht m hm, ?_⟩⟩
  rw [mul_left_comm, mul_translate m j, hx]
  exact goodU ⟨by norm_num, by norm_num⟩ m hm

theorem slow12345 (m : ℕ) (hm : m ∈ [1,2,3,4,5]) :
    Buffered ((m : ℝ)*(3/20)) (1/40) := by
  simp at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    exact Or.inl ⟨by norm_num, by norm_num⟩

theorem pinned_buffer {t e : ℝ} (h : Buffered t e) :
    1/8+e ≤ distInt t := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact phase_margin 0 (by norm_num; exact ha) (by norm_num; linarith)
  · exact phase_margin 1 (by norm_num; linarith) (by norm_num; linarith)

#print axioms slow125
#print axioms slow123
#print axioms slow12345
end Fresh.Harmonic
