import Mathlib

namespace LRC.ExactCellRestoration

def Restores (x u w : ℝ) : Prop :=
  ∃ t : ℝ, u ≤ t ∧ t ≤ w ∧ ∃ j : ℤ,
    (j : ℝ)+1/8 ≤ x*t ∧ x*t ≤ (j : ℝ)+7/8

theorem band_overlap_iff {x u w L U : ℝ} (hx : 0 < x)
    (huw : u ≤ w) (hLU : L ≤ U) :
    (∃ t : ℝ, u ≤ t ∧ t ≤ w ∧ L ≤ x*t ∧ x*t ≤ U) ↔
    (x*u ≤ U ∧ L ≤ x*w) := by
  constructor
  · rintro ⟨t, hut, htw, hLt, htU⟩
    constructor <;> nlinarith
  · rintro ⟨huU, hLw⟩
    by_cases h : u ≤ L/x
    · have he : x*(L/x)=L := by field_simp
      exact ⟨L/x, h, (div_le_iff₀ hx).mpr (by nlinarith), by rw [he], by rw [he]; exact hLU⟩
    · have ht : L/x ≤ u := le_of_not_ge h
      have hLu : L ≤ u*x := (div_le_iff₀ hx).mp ht
      exact ⟨u, le_rfl, huw, by nlinarith, huU⟩

/-- Complete failure characterization, including singleton cells and clear
endpoints. No hypothesis of future restoration is used. -/
theorem not_restores_iff {x u w : ℝ} (hx : 0 < x) (huw : u ≤ w) :
    ¬ Restores x u w ↔ ∃ ell : ℤ,
      (ell : ℝ)-1/8 < x*u ∧ x*w < (ell : ℝ)+1/8 := by
  constructor
  · intro hn
    let ell : ℤ := ⌊x*u+1/8⌋
    have hf : (ell : ℝ) ≤ x*u+1/8 := Int.floor_le _
    have hg : x*u+1/8 < (ell : ℝ)+1 := Int.lt_floor_add_one _
    have hmono : x*u ≤ x*w := by nlinarith
    have upper : x*w < (ell : ℝ)+1/8 := by
      by_contra h
      have hab := (band_overlap_iff hx huw (show (ell : ℝ)+1/8 ≤ (ell : ℝ)+7/8 by linarith)).mpr
        (And.intro (by linarith : x*u ≤ (ell : ℝ)+7/8) (le_of_not_gt h))
      obtain ⟨t, ht, hw, h1, h2⟩ := hab
      exact hn ⟨t, ht, hw, ell, h1, h2⟩
    refine ⟨ell, ?_, upper⟩
    by_contra h
    have he : x*u = (ell : ℝ)-1/8 := by linarith
    apply hn
    refine ⟨u, le_rfl, huw, ell-1, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨ell, hl, hu⟩ ⟨t, hut, htw, j, h1, h2⟩
    have hlo : (ell : ℝ)-1/8 < x*t := by nlinarith
    have hhi : x*t < (ell : ℝ)+1/8 := by nlinarith
    have hj : j < ell := by exact_mod_cast (show (j : ℝ)<ell by linarith)
    have he : ell < j+1 := by exact_mod_cast (show (ell : ℝ)<(j : ℝ)+1 by linarith)
    omega

/-- All-cell failure is a simultaneous integer-label assignment for ONE x. -/
theorem all_cells_fail_iff {α : Type*} (u w : α → ℝ) {x : ℝ}
    (hx : 0 < x) (huw : ∀ i, u i ≤ w i) :
    (¬ ∃ i, Restores x (u i) (w i)) ↔
    ∀ i, ∃ ell : ℤ, (ell : ℝ)-1/8 < x*u i ∧ x*w i < (ell : ℝ)+1/8 := by
  simp only [not_exists]
  exact forall_congr' (fun i => not_restores_iff hx (huw i))

/-- Exact open intervals in the incoming-reading parameter, not sampled times. -/
theorem not_restores_parameter_iff {x u w : ℝ} (hx : 0 < x)
    (hu : 0 < u) (hw : 0 < w) (huw : u ≤ w) :
    ¬ Restores x u w ↔ ∃ ell : ℤ,
      ((ell : ℝ)-1/8)/u < x ∧ x < ((ell : ℝ)+1/8)/w := by
  rw [not_restores_iff hx huw]
  simp only [div_lt_iff₀ hu, lt_div_iff₀ hw]

/-- The tail is discharged, rather than imposing a width requirement on all x. -/
theorem restores_of_width {x u w : ℝ} (hx : 0 < x) (huw : u ≤ w)
    (hwidth : 1/4 ≤ x*(w-u)) : Restores x u w := by
  by_contra hn
  obtain ⟨ell, hl, hr⟩ := (not_restores_iff hx huw).mp hn
  nlinarith

/-- Reflection couples failure labels. Integer x then forces ell+k=x. -/
theorem reflected_failure {x u w ell k : ℝ}
    (h1 : ell-1/8 < x*u) (h2 : x*w < ell+1/8)
    (h3 : k-1/8 < x*(1-w)) (h4 : x*(1-u) < k+1/8) :
    ell+k-1/4+x*(w-u) < x ∧ x < ell+k+1/4-x*(w-u) := by
  constructor <;> nlinarith

theorem reflected_integer_labels {x ell k : ℤ} {u w : ℝ}
    (hx : 0 < (x : ℝ)) (huw : u ≤ w)
    (h1 : (ell : ℝ)-1/8 < x*u) (h2 : x*w < (ell : ℝ)+1/8)
    (h3 : (k : ℝ)-1/8 < x*(1-w)) (h4 : x*(1-u) < (k : ℝ)+1/8) :
    ell+k=x := by
  obtain ⟨hl, hr⟩ := reflected_failure h1 h2 h3 h4
  have hnon : 0 ≤ (x : ℝ)*(w-u) := mul_nonneg hx.le (sub_nonneg.mpr huw)
  have hlo : ell+k-1 < x := by
    exact_mod_cast (show (ell : ℝ)+k-1 < (x : ℝ) by linarith)
  have hhi : x < ell+k+1 := by
    exact_mod_cast (show (x : ℝ) < (ell : ℝ)+k+1 by linarith)
  omega

/-- At integer x the reflected cell supplies equivalent, not independent,
obstruction information. Do not count it twice in a contradiction argument. -/
theorem not_restores_reflection_iff {x : ℤ} {u w : ℝ}
    (hx : 0 < (x : ℝ)) (huw : u ≤ w) :
    (¬ Restores x (1-w) (1-u)) ↔ ¬ Restores x u w := by
  rw [not_restores_iff hx (by linarith : 1-w ≤ 1-u), not_restores_iff hx huw]
  constructor
  · rintro ⟨ell, h1, h2⟩
    refine ⟨x-ell, ?_, ?_⟩ <;> push_cast <;> nlinarith
  · rintro ⟨ell, h1, h2⟩
    refine ⟨x-ell, ?_, ?_⟩ <;> push_cast <;> nlinarith

end LRC.ExactCellRestoration

#print axioms LRC.ExactCellRestoration.band_overlap_iff
#print axioms LRC.ExactCellRestoration.not_restores_iff
#print axioms LRC.ExactCellRestoration.all_cells_fail_iff
#print axioms LRC.ExactCellRestoration.reflected_failure
#print axioms LRC.ExactCellRestoration.not_restores_parameter_iff
#print axioms LRC.ExactCellRestoration.restores_of_width
#print axioms LRC.ExactCellRestoration.reflected_integer_labels
#print axioms LRC.ExactCellRestoration.not_restores_reflection_iff
