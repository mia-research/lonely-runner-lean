import Fresh.ThreeBlockNativePhysical

/-! Rules:1–4,8–18. Reflected original-label native bypass, subject6.
Both actual physical disparity sets are checked; label reversal is not an
assumption about the original full cascade's visited comparisons. -/
open Classical
namespace Fresh.ThreeBlockNativeMirror
open Fresh Fresh.Localisation Fresh.Cascade Fresh.ThreeBlockCarry
  Fresh.ThreeBlockGridResumption Fresh.ThreeBlockNativeBypass

theorem right_disparity_eq (c g h : ℝ) (hg : 0<g) (hh : 0<h) :
    disparitySet (speeds c g h) (6 : Fin 8)=leftReadings h g := by
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g h (0 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (0 : Fin 8)-speeds c g h (6 : Fin 8)=-(4+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (1 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (1 : Fin 8)-speeds c g h (6 : Fin 8)=-(3+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (2 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (2 : Fin 8)-speeds c g h (6 : Fin 8)=-(3+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (3 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (3 : Fin 8)-speeds c g h (6 : Fin 8)=-(2+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (4 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (4 : Fin 8)-speeds c g h (6 : Fin 8)=-(1+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (5 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (5 : Fin 8)-speeds c g h (6 : Fin 8)=-(h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg,abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · exact (hne rfl).elim
    · change |speeds c g h (7 : Fin 8)-speeds c g h (6 : Fin 8)| ∈ leftReadings h g
      have he : speeds c g h (7 : Fin 8)-speeds c g h (6 : Fin 8)=(1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [leftReadings]
  · intro hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with hd|hd|hd|hd|hd|hd|hd
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g h (5 : Fin 8)-speeds c g h (6 : Fin 8)=-(h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g h (7 : Fin 8)-speeds c g h (6 : Fin 8)=(1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g h (4 : Fin 8)-speeds c g h (6 : Fin 8)=-(1+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g h (3 : Fin 8)-speeds c g h (6 : Fin 8)=-(2+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g h (2 : Fin 8)-speeds c g h (6 : Fin 8)=-(3+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(1 : Fin 8),by decide,?_⟩
      have he : speeds c g h (1 : Fin 8)-speeds c g h (6 : Fin 8)=-(3+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g h (0 : Fin 8)-speeds c g h (6 : Fin 8)=-(4+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)

theorem physical_native_reflected_bypass (c g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*h)
    (hentry2 : (8*(m : ℝ)-1)*h < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3) :
    IsLeast (disparitySet (speeds c g h) (6 : Fin 8) : Set ℝ) h ∧
    InWay 1 (1/(8*h)) ∧
    IsMove (disparitySet (speeds c g h) (6 : Fin 8))
      (1/(8*h)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h) (6 : Fin 8)) ((m : ℝ)+1/8) := by
  rw [right_disparity_eq c g h hg hh]
  exact native_opposite_pair_bypass h g m n hm hh hg hentry1 hentry2
    (by simpa [add_comm] using hlo) (by simpa [add_comm] using hhi)

#print axioms right_disparity_eq
#print axioms physical_native_reflected_bypass
end Fresh.ThreeBlockNativeMirror
