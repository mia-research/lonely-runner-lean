import Fresh.ThreeBlockNativeBypass

/-! Rules:1–4,8–18. Original-label physical realization of the native
opposite-pair bypass. The seven readings are proved equal to the actual
subject disparity set; no runner is replaced by a stationary runner. -/
open Classical
namespace Fresh.ThreeBlockNativePhysical
open Fresh Fresh.Localisation Fresh.Cascade Fresh.ThreeBlockCarry
  Fresh.ThreeBlockGridResumption Fresh.ThreeBlockNativeBypass

theorem left_disparity_eq (c g h : ℝ) (hg : 0<g) (hh : 0<h) :
    disparitySet (speeds c g h) (1 : Fin 8)=leftReadings g h := by
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g h (0 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (0 : Fin 8)-speeds c g h (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [leftReadings]
    · exact (hne rfl).elim
    · change |speeds c g h (2 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (2 : Fin 8)-speeds c g h (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (3 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (3 : Fin 8)-speeds c g h (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (4 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (4 : Fin 8)-speeds c g h (1 : Fin 8)=2+g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (5 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (5 : Fin 8)-speeds c g h (1 : Fin 8)=3+g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (6 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (6 : Fin 8)-speeds c g h (1 : Fin 8)=3+g+h := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
    · change |speeds c g h (7 : Fin 8)-speeds c g h (1 : Fin 8)| ∈ leftReadings g h
      have he : speeds c g h (7 : Fin 8)-speeds c g h (1 : Fin 8)=4+g+h := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [leftReadings]
  · intro hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with hd|hd|hd|hd|hd|hd|hd
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g h (2 : Fin 8)-speeds c g h (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g h (0 : Fin 8)-speeds c g h (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g h (3 : Fin 8)-speeds c g h (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g h (4 : Fin 8)-speeds c g h (1 : Fin 8)=2+g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g h (5 : Fin 8)-speeds c g h (1 : Fin 8)=3+g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(6 : Fin 8),by decide,?_⟩
      have he : speeds c g h (6 : Fin 8)-speeds c g h (1 : Fin 8)=3+g+h := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g h (7 : Fin 8)-speeds c g h (1 : Fin 8)=4+g+h := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)

theorem physical_native_opposite_pair_bypass (c g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3) :
    IsLeast (disparitySet (speeds c g h) (1 : Fin 8) : Set ℝ) g ∧
    InWay 1 (1/(8*g)) ∧
    IsMove (disparitySet (speeds c g h) (1 : Fin 8))
      (1/(8*g)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h) (1 : Fin 8)) ((m : ℝ)+1/8) := by
  rw [left_disparity_eq c g h hg hh]
  exact native_opposite_pair_bypass g h m n hm hg hh hentry1 hentry2 hlo hhi

#print axioms left_disparity_eq
#print axioms physical_native_opposite_pair_bypass
end Fresh.ThreeBlockNativePhysical
