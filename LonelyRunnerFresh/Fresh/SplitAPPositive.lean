import Fresh.SplitAPBands
import Fresh.TranslatedSixPositive

/-! Rules1–4,8–18. Exact middle charts for two AP reading blocks.
[PROVISIONAL: covering] supports the finite PARAMETER splits only.
Small/tail integer opening selection inherits [PROVISIONAL: counting tool].
All seven named bands and closed equality edges are retained. -/

namespace Fresh.SplitAPBands
open Fresh Fresh.TranslatedSix

theorem splitTrain_eq_1 (a : ℝ) : splitTrain 1 a = {1, a, (a + 1), (a + 2), (a + 3), (a + 4), (a + 5)} := by
  ext d
  norm_num [splitTrain, Finset.range_add_one]
  all_goals tauto

theorem splitTrain_eq_2 (a : ℝ) : splitTrain 2 a = {1, 2, a, (a + 1), (a + 2), (a + 3), (a + 4)} := by
  ext d
  norm_num [splitTrain, Finset.range_add_one]
  all_goals tauto

theorem splitTrain_eq_3 (a : ℝ) : splitTrain 3 a = {1, 2, 3, a, (a + 1), (a + 2), (a + 3)} := by
  ext d
  norm_num [splitTrain, Finset.range_add_one]
  all_goals tauto

theorem splitTrain_eq_4 (a : ℝ) : splitTrain 4 a = {1, 2, 3, 4, a, (a + 1), (a + 2)} := by
  ext d
  norm_num [splitTrain, Finset.range_add_one]
  all_goals tauto

theorem splitTrain_eq_5 (a : ℝ) : splitTrain 5 a = {1, 2, 3, 4, 5, a, (a + 1)} := by
  ext d
  norm_num [splitTrain, Finset.range_add_one]
  all_goals tauto

theorem middle_r2_0 (a : ℝ) (ha : (1 / 4 : ℝ) ≤ a) (hb : a ≤ (2 / 5 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 3)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_0

theorem middle_r2_1 (a : ℝ) (ha : (3 / 8 : ℝ) ≤ a) (hb : a ≤ (3 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 3)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_1

theorem middle_r2_2 (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_2

theorem middle_r2_3 (a : ℝ) (ha : 3 ≤ a) (hb : a ≤ (46 / 13 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 4) := by linarith
  refine ⟨(49 : ℝ)/(8*(a + 4)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (5 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (6 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_3

theorem middle_r2_4 (a : ℝ) (ha : (27 / 8 : ℝ) ≤ a) (hb : a ≤ (11 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 3)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_4

theorem middle_r2_5 (a : ℝ) (ha : (11 / 3 : ℝ) ≤ a) (hb : a ≤ (13 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 2) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 2)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_5

theorem middle_r2_6 (a : ℝ) (ha : (51 / 8 : ℝ) ≤ a) (hb : a ≤ (19 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(25 : ℝ)/(8*(a + 3)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_6

theorem middle_r2_7 (a : ℝ) (ha : 9 ≤ a) (hb : a ≤ (29 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 2) := by linarith
  refine ⟨(33 : ℝ)/(8*(a + 2)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_7

theorem middle_r2_8 (a : ℝ) (ha : (34 / 3 : ℝ) ≤ a) (hb : a ≤ 16) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(17 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r2_8

theorem split_train_positive_r2 (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain 2 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  by_cases hs : a ≤ (2 : ℝ)/8
  · exact split_train_small 2 (by omega) (by omega) a ha hs
  by_cases h0 : a ≤ (2 / 5 : ℝ)
  · exact middle_r2_0 a (by linarith) h0
  by_cases h1 : a ≤ (3 / 2 : ℝ)
  · exact middle_r2_1 a (by linarith) h1
  by_cases h2 : a ≤ 3
  · exact middle_r2_2 a (by linarith) h2
  by_cases h3 : a ≤ (46 / 13 : ℝ)
  · exact middle_r2_3 a (by linarith) h3
  by_cases h4 : a ≤ (11 / 2 : ℝ)
  · exact middle_r2_4 a (by linarith) h4
  by_cases h5 : a ≤ (13 / 2 : ℝ)
  · exact middle_r2_5 a (by linarith) h5
  by_cases h6 : a ≤ (19 / 2 : ℝ)
  · exact middle_r2_6 a (by linarith) h6
  by_cases h7 : a ≤ (29 / 2 : ℝ)
  · exact middle_r2_7 a (by linarith) h7
  by_cases h8 : a ≤ 16
  · exact middle_r2_8 a (by linarith) h8
  exact split_train_tail 2 (by omega) (by omega) a ha (by norm_num; linarith) (by norm_num; linarith)

#print axioms split_train_positive_r2

theorem middle_r3_0 (a : ℝ) (ha : (3 / 8 : ℝ) ≤ a) (hb : a ≤ (1 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(49 : ℝ)/(8*(a + 3)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (5 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (6 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r3_0

theorem middle_r3_1 (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) (hb : a ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(1 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r3_1

theorem middle_r3_2 (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r3_2

theorem middle_r3_3 (a : ℝ) (ha : 4 ≤ a) (hb : a ≤ (41 / 9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < (a + 1) := by linarith
  refine ⟨(25 : ℝ)/(8*(a + 1)),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r3_3

theorem middle_r3_4 (a : ℝ) (ha : (9 / 2 : ℝ) ≤ a) (hb : a ≤ 8) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(9 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r3_4

theorem split_train_positive_r3 (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain 3 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  by_cases hs : a ≤ (3 : ℝ)/8
  · exact split_train_small 3 (by omega) (by omega) a ha hs
  by_cases h0 : a ≤ (1 / 2 : ℝ)
  · exact middle_r3_0 a (by linarith) h0
  by_cases h1 : a ≤ 1
  · exact middle_r3_1 a (by linarith) h1
  by_cases h2 : a ≤ 4
  · exact middle_r3_2 a (by linarith) h2
  by_cases h3 : a ≤ (41 / 9 : ℝ)
  · exact middle_r3_3 a (by linarith) h3
  by_cases h4 : a ≤ 8
  · exact middle_r3_4 a (by linarith) h4
  exact split_train_tail 3 (by omega) (by omega) a ha (by norm_num; linarith) (by norm_num; linarith)

#print axioms split_train_positive_r3

theorem middle_r4_0 (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) (hb : a ≤ (10 / 9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 4 := by linarith
  refine ⟨(9 : ℝ)/(8*4),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r4_0

theorem middle_r4_1 (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 5) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r4_1

theorem middle_r4_2 (a : ℝ) (ha : 5 ≤ a) (hb : a ≤ (50 / 9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(25 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (3 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (4 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r4_2

theorem middle_r4_3 (a : ℝ) (ha : (36 / 7 : ℝ) ≤ a) (hb : a ≤ 9) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(9 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r4_3

theorem middle_r4_4 (a : ℝ) (ha : 9 ≤ a) (hb : a ≤ (32 / 3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_4] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r4_4

theorem split_train_positive_r4 (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain 4 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  by_cases hs : a ≤ (4 : ℝ)/8
  · exact split_train_small 4 (by omega) (by omega) a ha hs
  by_cases h0 : a ≤ (10 / 9 : ℝ)
  · exact middle_r4_0 a (by linarith) h0
  by_cases h1 : a ≤ 5
  · exact middle_r4_1 a (by linarith) h1
  by_cases h2 : a ≤ (50 / 9 : ℝ)
  · exact middle_r4_2 a (by linarith) h2
  by_cases h3 : a ≤ 9
  · exact middle_r4_3 a (by linarith) h3
  by_cases h4 : a ≤ (32 / 3 : ℝ)
  · exact middle_r4_4 a (by linarith) h4
  exact split_train_tail 4 (by omega) (by omega) a ha (by norm_num; linarith) (by norm_num; linarith)

#print axioms split_train_positive_r4

theorem middle_r5_0 (a : ℝ) (ha : (5 / 8 : ℝ) ≤ a) (hb : a ≤ (4 / 3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 3 := by linarith
  refine ⟨(9 : ℝ)/(8*3),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_0

theorem middle_r5_1 (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_1

theorem middle_r5_2 (a : ℝ) (ha : (17 / 3 : ℝ) ≤ a) (hb : a ≤ (20 / 3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 3 := by linarith
  refine ⟨(9 : ℝ)/(8*3),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_2

theorem middle_r5_3 (a : ℝ) (ha : (45 / 7 : ℝ) ≤ a) (hb : a ≤ 9) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(9 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_3

theorem middle_r5_4 (a : ℝ) (ha : 9 ≤ a) (hb : a ≤ 14) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (1 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_4

theorem middle_r5_5 (a : ℝ) (ha : (85 / 7 : ℝ) ≤ a) (hb : a ≤ 17) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < a := by linarith
  refine ⟨(17 : ℝ)/(8*a),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_5

theorem middle_r5_6 (a : ℝ) (ha : 17 ≤ a) (hb : a ≤ 20) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ)/(8*1),by positivity,fun d hmem => ?_⟩
  rw [splitTrain_eq_5] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (0 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))
  · apply clear_ratio hd (2 : ℤ) <;> (first | (solve | norm_num) | (push_cast; nlinarith))

#print axioms middle_r5_6

theorem split_train_positive_r5 (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain 5 a, (1/8 : ℝ) ≤ distInt (d*t) := by
  by_cases hs : a ≤ (5 : ℝ)/8
  · exact split_train_small 5 (by omega) (by omega) a ha hs
  by_cases h0 : a ≤ (4 / 3 : ℝ)
  · exact middle_r5_0 a (by linarith) h0
  by_cases h1 : a ≤ 6
  · exact middle_r5_1 a (by linarith) h1
  by_cases h2 : a ≤ (20 / 3 : ℝ)
  · exact middle_r5_2 a (by linarith) h2
  by_cases h3 : a ≤ 9
  · exact middle_r5_3 a (by linarith) h3
  by_cases h4 : a ≤ 14
  · exact middle_r5_4 a (by linarith) h4
  by_cases h5 : a ≤ 17
  · exact middle_r5_5 a (by linarith) h5
  by_cases h6 : a ≤ 20
  · exact middle_r5_6 a (by linarith) h6
  exact split_train_tail 5 (by omega) (by omega) a ha (by norm_num; linarith) (by norm_num; linarith)

#print axioms split_train_positive_r5

theorem split_train_positive (r : ℕ) (hr1 : 1≤r) (hr5 : r≤5) (a : ℝ) (ha : 0<a) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r a, (1/8 : ℝ) ≤ distInt (d*t) := by
  interval_cases r
  · have he : splitTrain 1 a = train a := by
      rw [splitTrain_eq_1]
      rfl
    rw [he]
    exact translated_six_positive a ha
  · exact split_train_positive_r2 a ha
  · exact split_train_positive_r3 a ha
  · exact split_train_positive_r4 a ha
  · exact split_train_positive_r5 a ha

#print axioms split_train_positive
end Fresh.SplitAPBands
