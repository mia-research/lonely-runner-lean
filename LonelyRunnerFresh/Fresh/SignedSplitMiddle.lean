import Fresh.SplitAPPositive

/-! Rules1–4,8–18. Exact signed-block parameter charts.
Every signed original reading is retained through distInt_neg.
[PROVISIONAL: covering] supports only the finite PARAMETER strips. -/

namespace Fresh.SplitAPBands
open Fresh Fresh.Localisation Fresh.TranslatedSix

theorem signed_chart_0 (a : ℝ) (ha : (-39 / 8 : ℝ)≤a) (hb : a≤(-19 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(57 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((57 : ℝ)/(8*(-a))) = -((-a)*((57 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (7 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((57 : ℝ)/(8*(-a))) = -((-a - 1)*((57 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (5 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((57 : ℝ)/(8*(-a))) = -((-a - 2)*((57 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((57 : ℝ)/(8*(-a))) = -((-a - 3)*((57 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 4)*((57 : ℝ)/(8*(-a))) = -((-a - 4)*((57 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_0

theorem signed_chart_1 (a : ℝ) (ha : (-165 / 34 : ℝ)≤a) (hb : a≤(-33 / 7 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(33 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(-a))) = -((-a)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((33 : ℝ)/(8*(-a))) = -((-a - 1)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((33 : ℝ)/(8*(-a))) = -((-a - 2)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((33 : ℝ)/(8*(-a))) = -((-a - 3)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 4)*((33 : ℝ)/(8*(-a))) = -((-a - 4)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_1

theorem signed_chart_2 (a : ℝ) (ha : (-85 / 18 : ℝ)≤a) (hb : a≤(-17 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(-a))) = -((-a)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a))) = -((-a - 1)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a))) = -((-a - 2)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((17 : ℝ)/(8*(-a))) = -((-a - 3)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 4)*((17 : ℝ)/(8*(-a))) = -((-a - 4)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_2

theorem signed_chart_3 (a : ℝ) (ha : (-22 / 5 : ℝ)≤a) (hb : a≤(-67 / 16 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(-a - 1))) = -((-a)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 3)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 4)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 4)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_3

theorem signed_chart_4 (a : ℝ) (ha : (-245 / 58 : ℝ)≤a) (hb : a≤(-33 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(49 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((49 : ℝ)/(8*(-a))) = -((-a)*((49 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (6 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((49 : ℝ)/(8*(-a))) = -((-a - 1)*((49 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((49 : ℝ)/(8*(-a))) = -((-a - 2)*((49 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((49 : ℝ)/(8*(-a))) = -((-a - 3)*((49 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 4)*((49 : ℝ)/(8*(-a))) = -((-a - 4)*((49 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_4

theorem signed_chart_5 (a : ℝ) (ha : (-31 / 8 : ℝ)≤a) (hb : a≤(-15 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(33 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(-a - 1))) = -((-a)*((33 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (5 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((33 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((33 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((33 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((33 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((33 : ℝ)/(8*(-a - 1))) = -((-a - 3)*((33 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_5

theorem signed_chart_6 (a : ℝ) (ha : (-19 / 5 : ℝ)≤a) (hb : a≤(-59 / 16 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 2) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a - 2)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(-a - 2))) = -((-a)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 1)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 2)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 3)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_6

theorem signed_chart_7 (a : ℝ) (ha : (-37 / 10 : ℝ)≤a) (hb : a≤(-13 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(-a - 1))) = -((-a)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((9 : ℝ)/(8*(-a - 1))) = -((-a - 3)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_7

theorem signed_chart_8 (a : ℝ) (ha : (-85 / 26 : ℝ)≤a) (hb : a≤(-51 / 16 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(-a))) = -((-a)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a))) = -((-a - 1)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a))) = -((-a - 2)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((17 : ℝ)/(8*(-a))) = -((-a - 3)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_8

theorem signed_chart_9 (a : ℝ) (ha : (-109 / 34 : ℝ)≤a) (hb : a≤(-25 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(25 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((25 : ℝ)/(8*(-a - 1))) = -((-a)*((25 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((25 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((25 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((25 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((25 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 3)*((25 : ℝ)/(8*(-a - 1))) = -((-a - 3)*((25 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_9

theorem signed_chart_10 (a : ℝ) (ha : (-23 / 8 : ℝ)≤a) (hb : a≤(-165 / 58 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(25 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((25 : ℝ)/(8*(a + 5))) = -((-a)*((25 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((25 : ℝ)/(8*(a + 5))) = -((-a - 1)*((25 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((25 : ℝ)/(8*(a + 5))) = -((-a - 2)*((25 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_10

theorem signed_chart_11 (a : ℝ) (ha : (-165 / 58 : ℝ)≤a) (hb : a≤(-11 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(33 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(-a))) = -((-a)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((33 : ℝ)/(8*(-a))) = -((-a - 1)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((33 : ℝ)/(8*(-a))) = -((-a - 2)*((33 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_11

theorem signed_chart_12 (a : ℝ) (ha : (-11 / 4 : ℝ)≤a) (hb : a≤(-5 / 2 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(a + 5))) = -((-a)*((9 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(a + 5))) = -((-a - 1)*((9 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((9 : ℝ)/(8*(a + 5))) = -((-a - 2)*((9 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_12

theorem signed_chart_13 (a : ℝ) (ha : (-5 / 2 : ℝ)≤a) (hb : a≤(-9 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(-a))) = -((-a)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a))) = -((-a - 1)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a))) = -((-a - 2)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_13

theorem signed_chart_14 (a : ℝ) (ha : (-9 / 4 : ℝ)≤a) (hb : a≤(-125 / 58 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(33 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(a + 5))) = -((-a)*((33 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((33 : ℝ)/(8*(a + 5))) = -((-a - 1)*((33 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((33 : ℝ)/(8*(a + 5))) = -((-a - 2)*((33 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_14

theorem signed_chart_15 (a : ℝ) (ha : (-125 / 58 : ℝ)≤a) (hb : a≤(-17 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(25 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((25 : ℝ)/(8*(-a))) = -((-a)*((25 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((25 : ℝ)/(8*(-a))) = -((-a - 1)*((25 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 2)*((25 : ℝ)/(8*(-a))) = -((-a - 2)*((25 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_15

theorem signed_chart_16 (a : ℝ) (ha : (-15 / 8 : ℝ)≤a) (hb : a≤(-61 / 34 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(25 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((25 : ℝ)/(8*(a + 4))) = -((-a)*((25 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((25 : ℝ)/(8*(a + 4))) = -((-a - 1)*((25 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_16

theorem signed_chart_17 (a : ℝ) (ha : (-29 / 16 : ℝ)≤a) (hb : a≤(-45 / 26 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(a + 5))) = -((-a)*((17 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((17 : ℝ)/(8*(a + 5))) = -((-a - 1)*((17 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_17

theorem signed_chart_18 (a : ℝ) (ha : (-7 / 4 : ℝ)≤a) (hb : a≤(-13 / 10 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(a + 4))) = -((-a)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(a + 4))) = -((-a - 1)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_18

theorem signed_chart_19 (a : ℝ) (ha : (-21 / 16 : ℝ)≤a) (hb : a≤(-6 / 5 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 3) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 3)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((9 : ℝ)/(8*(a + 3))) = -((-a)*((9 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((9 : ℝ)/(8*(a + 3))) = -((-a - 1)*((9 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_19

theorem signed_chart_20 (a : ℝ) (ha : (-5 / 4 : ℝ)≤a) (hb : a≤(-9 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(33 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(a + 4))) = -((-a)*((33 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show (a + 1)*((33 : ℝ)/(8*(a + 4))) = -((-a - 1)*((33 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (5 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_20

theorem signed_chart_21 (a : ℝ) (ha : (-7 / 8 : ℝ)≤a) (hb : a≤(-45 / 58 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(49 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((49 : ℝ)/(8*(a + 5))) = -((-a)*((49 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (6 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_21

theorem signed_chart_22 (a : ℝ) (ha : (-13 / 16 : ℝ)≤a) (hb : a≤(-3 / 5 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(a + 4))) = -((-a)*((17 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_22

theorem signed_chart_23 (a : ℝ) (ha : (-3 / 4 : ℝ)≤a) (hb : a≤(-5 / 18 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((17 : ℝ)/(8*(a + 5))) = -((-a)*((17 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_23

theorem signed_chart_24 (a : ℝ) (ha : (-2 / 7 : ℝ)≤a) (hb : a≤(-5 / 34 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(33 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((33 : ℝ)/(8*(a + 5))) = -((-a)*((33 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_24

theorem signed_chart_25 (a : ℝ) (ha : (-1 / 4 : ℝ)≤a) (hb : a≤(-1 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 5) := by linarith
  refine ⟨(57 : ℝ)/(8*(a + 5)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_1] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    rw [show a*((57 : ℝ)/(8*(a + 5))) = -((-a)*((57 : ℝ)/(8*(a + 5)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (5 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (7 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_25

theorem signed_chart_26 (a : ℝ) (ha : (-15 / 4 : ℝ)≤a) (hb : a≤(-7 / 2 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 2) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a - 2)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(-a - 2))) = -((-a)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 1)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 2)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 3)*((9 : ℝ)/(8*(-a - 2))) = -((-a - 3)*((9 : ℝ)/(8*(-a - 2)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_26

theorem signed_chart_27 (a : ℝ) (ha : (-18 / 5 : ℝ)≤a) (hb : a≤(-27 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(-a))) = -((-a)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a))) = -((-a - 1)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a))) = -((-a - 2)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 3)*((9 : ℝ)/(8*(-a))) = -((-a - 3)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_27

theorem signed_chart_28 (a : ℝ) (ha : (-17 / 5 : ℝ)≤a) (hb : a≤(-13 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(-a))) = -((-a)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a))) = -((-a - 1)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a))) = -((-a - 2)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 3)*((17 : ℝ)/(8*(-a))) = -((-a - 3)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_28

theorem signed_chart_29 (a : ℝ) (ha : (-11 / 4 : ℝ)≤a) (hb : a≤(-43 / 16 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(-a - 1))) = -((-a)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((9 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((9 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_29

theorem signed_chart_30 (a : ℝ) (ha : (-27 / 10 : ℝ)≤a) (hb : a≤(-83 / 32 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a - 1) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a - 1)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(-a - 1))) = -((-a)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 1)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a - 1))) = -((-a - 2)*((17 : ℝ)/(8*(-a - 1)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_30

theorem signed_chart_31 (a : ℝ) (ha : (-34 / 13 : ℝ)≤a) (hb : a≤(-17 / 7 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(-a))) = -((-a)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a))) = -((-a - 1)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a))) = -((-a - 2)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_31

theorem signed_chart_32 (a : ℝ) (ha : (-23 / 9 : ℝ)≤a) (hb : a≤(-7 / 3 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<1 := by linarith
  refine ⟨(9 : ℝ)/(8*1),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*1)) = -((-a)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*1)) = -((-a - 1)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((9 : ℝ)/(8*1)) = -((-a - 2)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_32

theorem signed_chart_33 (a : ℝ) (ha : (-7 / 3 : ℝ)≤a) (hb : a≤(-66 / 29 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(25 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((25 : ℝ)/(8*(a + 4))) = -((-a)*((25 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((25 : ℝ)/(8*(a + 4))) = -((-a - 1)*((25 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((25 : ℝ)/(8*(a + 4))) = -((-a - 2)*((25 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_33

theorem signed_chart_34 (a : ℝ) (ha : (-37 / 16 : ℝ)≤a) (hb : a≤(-9 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(a + 4))) = -((-a)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(a + 4))) = -((-a - 1)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 2)*((9 : ℝ)/(8*(a + 4))) = -((-a - 2)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_34

theorem signed_chart_35 (a : ℝ) (ha : (-7 / 4 : ℝ)≤a) (hb : a≤(-27 / 16 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(9 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(-a))) = -((-a)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(-a))) = -((-a - 1)*((9 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_35

theorem signed_chart_36 (a : ℝ) (ha : (-50 / 29 : ℝ)≤a) (hb : a≤(-5 / 3 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(25 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((25 : ℝ)/(8*(-a))) = -((-a)*((25 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((25 : ℝ)/(8*(-a))) = -((-a - 1)*((25 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_36

theorem signed_chart_37 (a : ℝ) (ha : (-5 / 3 : ℝ)≤a) (hb : a≤(-13 / 9 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<1 := by linarith
  refine ⟨(9 : ℝ)/(8*1),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*1)) = -((-a)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*1)) = -((-a - 1)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_37

theorem signed_chart_38 (a : ℝ) (ha : (-11 / 7 : ℝ)≤a) (hb : a≤(-18 / 13 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(a + 4))) = -((-a)*((17 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((17 : ℝ)/(8*(a + 4))) = -((-a - 1)*((17 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_38

theorem signed_chart_39 (a : ℝ) (ha : (-45 / 32 : ℝ)≤a) (hb : a≤(-13 / 10 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 3) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 3)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(a + 3))) = -((-a)*((17 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((17 : ℝ)/(8*(a + 3))) = -((-a - 1)*((17 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_39

theorem signed_chart_40 (a : ℝ) (ha : (-21 / 16 : ℝ)≤a) (hb : a≤(-5 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 3) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 3)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(a + 3))) = -((-a)*((9 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show (a + 1)*((9 : ℝ)/(8*(a + 3))) = -((-a - 1)*((9 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_40

theorem signed_chart_41 (a : ℝ) (ha : (-3 / 4 : ℝ)≤a) (hb : a≤(-3 / 5 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((17 : ℝ)/(8*(a + 4))) = -((-a)*((17 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_41

theorem signed_chart_42 (a : ℝ) (ha : (-5 / 8 : ℝ)≤a) (hb : a≤(-2 / 5 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 4) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 4)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(a + 4))) = -((-a)*((9 : ℝ)/(8*(a + 4)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_42

theorem signed_chart_43 (a : ℝ) (ha : (-1 / 2 : ℝ)≤a) (hb : a≤(-1 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 2) := by linarith
  refine ⟨(9 : ℝ)/(8*(a + 2)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_2] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    rw [show a*((9 : ℝ)/(8*(a + 2))) = -((-a)*((9 : ℝ)/(8*(a + 2)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_43

theorem signed_chart_44 (a : ℝ) (ha : (-21 / 8 : ℝ)≤a) (hb : a≤(-17 / 7 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(-a) := by linarith
  refine ⟨(17 : ℝ)/(8*(-a)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show a*((17 : ℝ)/(8*(-a))) = -((-a)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 1)*((17 : ℝ)/(8*(-a))) = -((-a - 1)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 2)*((17 : ℝ)/(8*(-a))) = -((-a - 2)*((17 : ℝ)/(8*(-a)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_44

theorem signed_chart_45 (a : ℝ) (ha : (-23 / 9 : ℝ)≤a) (hb : a≤(-19 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<1 := by linarith
  refine ⟨(9 : ℝ)/(8*1),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show a*((9 : ℝ)/(8*1)) = -((-a)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 1)*((9 : ℝ)/(8*1)) = -((-a - 1)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    rw [show (a + 2)*((9 : ℝ)/(8*1)) = -((-a - 2)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_45

theorem signed_chart_46 (a : ℝ) (ha : (-13 / 8 : ℝ)≤a) (hb : a≤(-11 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<3 := by linarith
  refine ⟨(9 : ℝ)/(8*3),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show a*((9 : ℝ)/(8*3)) = -((-a)*((9 : ℝ)/(8*3))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    rw [show (a + 1)*((9 : ℝ)/(8*3)) = -((-a - 1)*((9 : ℝ)/(8*3))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_46

theorem signed_chart_47 (a : ℝ) (ha : (-5 / 8 : ℝ)≤a) (hb : a≤(-4 / 9 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<1 := by linarith
  refine ⟨(9 : ℝ)/(8*1),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show a*((9 : ℝ)/(8*1)) = -((-a)*((9 : ℝ)/(8*1))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_47

theorem signed_chart_48 (a : ℝ) (ha : (-4 / 7 : ℝ)≤a) (hb : a≤(-3 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  have hd : (0 : ℝ)<(a + 3) := by linarith
  refine ⟨(17 : ℝ)/(8*(a + 3)),by positivity,fun d hmem=>?_⟩
  rw [splitTrain_eq_3] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with hd0 | hd1 | hd2 | hd3 | hd4 | hd5 | hd6
  · rw [hd0]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd1]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd2]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd3]
    rw [show a*((17 : ℝ)/(8*(a + 3))) = -((-a)*((17 : ℝ)/(8*(a + 3)))) by ring,distInt_neg]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd4]
    apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd5]
    apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · rw [hd6]
    apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

#print axioms signed_chart_48

theorem signed_strip_r1_m5 (a : ℝ) (ha : (-39 / 8 : ℝ)≤a) (hb : a≤(-33 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-19 / 4 : ℝ)
  · exact signed_chart_0 a (by linarith) h0
  by_cases h1 : a≤(-33 / 7 : ℝ)
  · exact signed_chart_1 a (by linarith) h1
  by_cases h2 : a≤(-17 / 4 : ℝ)
  · exact signed_chart_2 a (by linarith) h2
  by_cases h3 : a≤(-67 / 16 : ℝ)
  · exact signed_chart_3 a (by linarith) h3
  exact signed_chart_4 a (by linarith) (by linarith)

#print axioms signed_strip_r1_m5

theorem signed_strip_r1_m4 (a : ℝ) (ha : (-31 / 8 : ℝ)≤a) (hb : a≤(-25 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-15 / 4 : ℝ)
  · exact signed_chart_5 a (by linarith) h0
  by_cases h1 : a≤(-59 / 16 : ℝ)
  · exact signed_chart_6 a (by linarith) h1
  by_cases h2 : a≤(-13 / 4 : ℝ)
  · exact signed_chart_7 a (by linarith) h2
  by_cases h3 : a≤(-51 / 16 : ℝ)
  · exact signed_chart_8 a (by linarith) h3
  exact signed_chart_9 a (by linarith) (by linarith)

#print axioms signed_strip_r1_m4

theorem signed_strip_r1_m3 (a : ℝ) (ha : (-23 / 8 : ℝ)≤a) (hb : a≤(-17 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-165 / 58 : ℝ)
  · exact signed_chart_10 a (by linarith) h0
  by_cases h1 : a≤(-11 / 4 : ℝ)
  · exact signed_chart_11 a (by linarith) h1
  by_cases h2 : a≤(-5 / 2 : ℝ)
  · exact signed_chart_12 a (by linarith) h2
  by_cases h3 : a≤(-9 / 4 : ℝ)
  · exact signed_chart_13 a (by linarith) h3
  by_cases h4 : a≤(-125 / 58 : ℝ)
  · exact signed_chart_14 a (by linarith) h4
  exact signed_chart_15 a (by linarith) (by linarith)

#print axioms signed_strip_r1_m3

theorem signed_strip_r1_m2 (a : ℝ) (ha : (-15 / 8 : ℝ)≤a) (hb : a≤(-9 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-61 / 34 : ℝ)
  · exact signed_chart_16 a (by linarith) h0
  by_cases h1 : a≤(-45 / 26 : ℝ)
  · exact signed_chart_17 a (by linarith) h1
  by_cases h2 : a≤(-13 / 10 : ℝ)
  · exact signed_chart_18 a (by linarith) h2
  by_cases h3 : a≤(-6 / 5 : ℝ)
  · exact signed_chart_19 a (by linarith) h3
  exact signed_chart_20 a (by linarith) (by linarith)

#print axioms signed_strip_r1_m2

theorem signed_strip_r1_m1 (a : ℝ) (ha : (-7 / 8 : ℝ)≤a) (hb : a≤(-1 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 1 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-45 / 58 : ℝ)
  · exact signed_chart_21 a (by linarith) h0
  by_cases h1 : a≤(-3 / 5 : ℝ)
  · exact signed_chart_22 a (by linarith) h1
  by_cases h2 : a≤(-5 / 18 : ℝ)
  · exact signed_chart_23 a (by linarith) h2
  by_cases h3 : a≤(-5 / 34 : ℝ)
  · exact signed_chart_24 a (by linarith) h3
  exact signed_chart_25 a (by linarith) (by linarith)

#print axioms signed_strip_r1_m1

theorem signed_strip_r2_m4 (a : ℝ) (ha : (-15 / 4 : ℝ)≤a) (hb : a≤(-13 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-7 / 2 : ℝ)
  · exact signed_chart_26 a (by linarith) h0
  by_cases h1 : a≤(-27 / 8 : ℝ)
  · exact signed_chart_27 a (by linarith) h1
  exact signed_chart_28 a (by linarith) (by linarith)

#print axioms signed_strip_r2_m4

theorem signed_strip_r2_m3 (a : ℝ) (ha : (-11 / 4 : ℝ)≤a) (hb : a≤(-9 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-43 / 16 : ℝ)
  · exact signed_chart_29 a (by linarith) h0
  by_cases h1 : a≤(-83 / 32 : ℝ)
  · exact signed_chart_30 a (by linarith) h1
  by_cases h2 : a≤(-17 / 7 : ℝ)
  · exact signed_chart_31 a (by linarith) h2
  by_cases h3 : a≤(-7 / 3 : ℝ)
  · exact signed_chart_32 a (by linarith) h3
  by_cases h4 : a≤(-66 / 29 : ℝ)
  · exact signed_chart_33 a (by linarith) h4
  exact signed_chart_34 a (by linarith) (by linarith)

#print axioms signed_strip_r2_m3

theorem signed_strip_r2_m2 (a : ℝ) (ha : (-7 / 4 : ℝ)≤a) (hb : a≤(-5 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-27 / 16 : ℝ)
  · exact signed_chart_35 a (by linarith) h0
  by_cases h1 : a≤(-5 / 3 : ℝ)
  · exact signed_chart_36 a (by linarith) h1
  by_cases h2 : a≤(-13 / 9 : ℝ)
  · exact signed_chart_37 a (by linarith) h2
  by_cases h3 : a≤(-18 / 13 : ℝ)
  · exact signed_chart_38 a (by linarith) h3
  by_cases h4 : a≤(-13 / 10 : ℝ)
  · exact signed_chart_39 a (by linarith) h4
  exact signed_chart_40 a (by linarith) (by linarith)

#print axioms signed_strip_r2_m2

theorem signed_strip_r2_m1 (a : ℝ) (ha : (-3 / 4 : ℝ)≤a) (hb : a≤(-1 / 4 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 2 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-3 / 5 : ℝ)
  · exact signed_chart_41 a (by linarith) h0
  by_cases h1 : a≤(-2 / 5 : ℝ)
  · exact signed_chart_42 a (by linarith) h1
  exact signed_chart_43 a (by linarith) (by linarith)

#print axioms signed_strip_r2_m1

theorem signed_strip_r3_m3 (a : ℝ) (ha : (-21 / 8 : ℝ)≤a) (hb : a≤(-19 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-17 / 7 : ℝ)
  · exact signed_chart_44 a (by linarith) h0
  exact signed_chart_45 a (by linarith) (by linarith)

#print axioms signed_strip_r3_m3

theorem signed_strip_r3_m2 (a : ℝ) (ha : (-13 / 8 : ℝ)≤a) (hb : a≤(-11 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  exact signed_chart_46 a (by linarith) (by linarith)

#print axioms signed_strip_r3_m2

theorem signed_strip_r3_m1 (a : ℝ) (ha : (-5 / 8 : ℝ)≤a) (hb : a≤(-3 / 8 : ℝ)) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain 3 a, (1/8 : ℝ)≤distInt (d*t) := by
  by_cases h0 : a≤(-4 / 9 : ℝ)
  · exact signed_chart_47 a (by linarith) h0
  exact signed_chart_48 a (by linarith) (by linarith)

#print axioms signed_strip_r3_m1

theorem signed_split_middle (r : ℕ) (hr1 : 1≤r) (hr3 : r≤3)
    (m : ℤ) (hmlo : (r : ℤ) - 6 ≤ m) (hmhi : m < 0)
    (a : ℝ) (ha : (m : ℝ)+(r : ℝ)/8≤a) (hb : a≤(m : ℝ)+1-(r : ℝ)/8) :
    ∃t : ℝ, 0<t ∧ ∀d∈splitTrain r a, (1/8 : ℝ)≤distInt (d*t) := by
  interval_cases r
  · have hm : (-5 : ℤ)≤ m := by simpa using hmlo
    interval_cases m
    · exact signed_strip_r1_m5 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r1_m4 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r1_m3 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r1_m2 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r1_m1 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
  · have hm : (-4 : ℤ)≤ m := by simpa using hmlo
    interval_cases m
    · exact signed_strip_r2_m4 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r2_m3 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r2_m2 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r2_m1 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
  · have hm : (-3 : ℤ)≤ m := by simpa using hmlo
    interval_cases m
    · exact signed_strip_r3_m3 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r3_m2 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)
    · exact signed_strip_r3_m1 a (by norm_num at ha ⊢; linarith) (by norm_num at hb ⊢; linarith)

#print axioms signed_split_middle
end Fresh.SplitAPBands
