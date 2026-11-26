import Fresh.FourAPPairsNative

/-! Rules:1–4,8–18. Original physical labels for both outer-gap native
four-pair bypasses. All seven disparities are derived in Lean, including
reflected roles and every independent gap. No stationary runner reduction. -/
open Classical
namespace Fresh.FourAPPairsNativePhysical
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourAPPairs Fresh.FourAPPairsNative

theorem left_disparity_eq (c g h j : ℝ) (hg : 0<g) (hh : 0<h) (hj : 0<j) :
    disparitySet (speeds c g h j) (1 : Fin 8)=leftReadings g h j := by
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g h j (0 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (0 : Fin 8)-speeds c g h j (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [leftReadings]
    · exact (hne rfl).elim
    · change |speeds c g h j (2 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (2 : Fin 8)-speeds c g h j (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (3 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (3 : Fin 8)-speeds c g h j (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (4 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (4 : Fin 8)-speeds c g h j (1 : Fin 8)=1+g+h := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (5 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (5 : Fin 8)-speeds c g h j (1 : Fin 8)=2+g+h := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (6 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (6 : Fin 8)-speeds c g h j (1 : Fin 8)=2+g+h+j := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (7 : Fin 8)-speeds c g h j (1 : Fin 8)| ∈ leftReadings g h j
      have he : speeds c g h j (7 : Fin 8)-speeds c g h j (1 : Fin 8)=3+g+h+j := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
  · intro hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with hd|hd|hd|hd|hd|hd|hd
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (2 : Fin 8)-speeds c g h j (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (0 : Fin 8)-speeds c g h j (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (3 : Fin 8)-speeds c g h j (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (4 : Fin 8)-speeds c g h j (1 : Fin 8)=1+g+h := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (5 : Fin 8)-speeds c g h j (1 : Fin 8)=2+g+h := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(6 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (6 : Fin 8)-speeds c g h j (1 : Fin 8)=2+g+h+j := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (7 : Fin 8)-speeds c g h j (1 : Fin 8)=3+g+h+j := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)

theorem right_disparity_eq (c g h j : ℝ) (hg : 0<g) (hh : 0<h) (hj : 0<j) :
    disparitySet (speeds c g h j) (6 : Fin 8)=leftReadings j h g := by
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g h j (0 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (0 : Fin 8)-speeds c g h j (6 : Fin 8)=-(3+j+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (1 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (1 : Fin 8)-speeds c g h j (6 : Fin 8)=-(2+j+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (2 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (2 : Fin 8)-speeds c g h j (6 : Fin 8)=-(2+j+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (3 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (3 : Fin 8)-speeds c g h j (6 : Fin 8)=-(1+j+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (4 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (4 : Fin 8)-speeds c g h j (6 : Fin 8)=-(1+j) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h j (5 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (5 : Fin 8)-speeds c g h j (6 : Fin 8)=-(j) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · exact (hne rfl).elim
    · change |speeds c g h j (7 : Fin 8)-speeds c g h j (6 : Fin 8)| ∈ leftReadings j h g
      have he : speeds c g h j (7 : Fin 8)-speeds c g h j (6 : Fin 8)=(1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [leftReadings]
  · intro hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with hd|hd|hd|hd|hd|hd|hd
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (5 : Fin 8)-speeds c g h j (6 : Fin 8)=-(j) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (7 : Fin 8)-speeds c g h j (6 : Fin 8)=(1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (4 : Fin 8)-speeds c g h j (6 : Fin 8)=-(1+j) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (3 : Fin 8)-speeds c g h j (6 : Fin 8)=-(1+j+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (2 : Fin 8)-speeds c g h j (6 : Fin 8)=-(2+j+h) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(1 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (1 : Fin 8)-speeds c g h j (6 : Fin 8)=-(2+j+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g h j (0 : Fin 8)-speeds c g h j (6 : Fin 8)=-(3+j+h+g) := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_neg]
      exact abs_of_nonneg (by linarith)

theorem physical_left_native_bypass (c g h j : ℝ) (m a b : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h) (hj : 0<j)
    (he1 : 1<(8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g<1)
    (hS1 : 8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hS2 : (8*(m : ℝ)+1)*(g+h) ≤ 8*(a : ℝ)+5)
    (hR1 : 8*(b : ℝ) ≤ (8*(m : ℝ)+1)*(g+h+j))
    (hR2 : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*(b : ℝ)+4) :
    IsLeast (disparitySet (speeds c g h j) (1 : Fin 8) : Set ℝ) g ∧ InWay 1 (1/(8*g)) ∧
    IsMove (disparitySet (speeds c g h j) (1 : Fin 8)) (1/(8*g)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h j) (1 : Fin 8)) ((m : ℝ)+1/8) := by
  rw [left_disparity_eq c g h j hg hh hj]
  exact native_full_bypass g h j m a b hm hg hh hj he1 he2 hS1 hS2 hR1 hR2

theorem physical_right_native_bypass (c g h j : ℝ) (m a b : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h) (hj : 0<j)
    (he1 : 1<(8*(m : ℝ)+1)*j) (he2 : (8*(m : ℝ)-1)*j<1)
    (hS1 : 8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(h+j))
    (hS2 : (8*(m : ℝ)+1)*(h+j) ≤ 8*(a : ℝ)+5)
    (hR1 : 8*(b : ℝ) ≤ (8*(m : ℝ)+1)*(g+h+j))
    (hR2 : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*(b : ℝ)+4) :
    IsLeast (disparitySet (speeds c g h j) (6 : Fin 8) : Set ℝ) j ∧ InWay 1 (1/(8*j)) ∧
    IsMove (disparitySet (speeds c g h j) (6 : Fin 8)) (1/(8*j)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h j) (6 : Fin 8)) ((m : ℝ)+1/8) := by
  rw [right_disparity_eq c g h j hg hh hj]
  exact native_full_bypass j h g m a b hm hj hh hg he1 he2
    (by simpa [add_comm] using hS1) (by simpa [add_comm] using hS2)
    (by simpa [add_comm,add_left_comm,add_assoc] using hR1)
    (by simpa [add_comm,add_left_comm,add_assoc] using hR2)

#print axioms left_disparity_eq
#print axioms right_disparity_eq
#print axioms physical_left_native_bypass
#print axioms physical_right_native_bypass
end Fresh.FourAPPairsNativePhysical
